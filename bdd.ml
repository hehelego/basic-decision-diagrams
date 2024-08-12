type var_id = int
type node_id = int
type node = False | True | Branch of var_id * node_id * node_id
type t = { index : (node, node_id) Hashtbl.t; store : node Dynarray.t }

let default_size = 1 lsl 20

let builder () =
  let index = Hashtbl.create default_size in
  let store = Dynarray.create () in
  Dynarray.add_last store False;
  Dynarray.add_last store True;
  Hashtbl.add index False 0;
  Hashtbl.add index True 1;
  { index; store }

let get_id { index; store } node =
  match Hashtbl.find_opt index node with
  | Some id -> id
  | None ->
      let id = Dynarray.length store in
      Dynarray.add_last store node;
      Hashtbl.add index node id;
      id

let get_node { index = _; store } id = Dynarray.get store id

let add_node builder node =
  let _ = get_id builder node in
  ()

(* helper function *)
let top_var = function True | False -> None | Branch (v, _, _) -> Some v

let min_opt = function
  | None, None -> None
  | None, Some y -> Some y
  | Some x, None -> Some x
  | Some x, Some y -> Some (min x y)

let split_top builder top node =
  let get_node = get_node builder in
  match node with
  | True | False -> (node, node)
  | Branch (v, low, high) ->
      if v = top then (get_node low, get_node high) else (node, node)

(* constructors *)

let leaf_true = True
let leaf_false = False

let var builder var =
  let node = Branch (var, 0, 1) in
  add_node builder node;
  node

let make_branch builder var low high =
  let valid_subbdd = function
    | True | False -> true
    | Branch (var', _, _) -> var < var'
  in
  assert (valid_subbdd low);
  assert (valid_subbdd high);
  let get_id = get_id builder in
  let low', high' = (get_id low, get_id high) in
  if low' = high' then low
  else
    let node = Branch (var, low', high') in
    add_node builder node;
    node

let terminal_value = function
  | True -> true
  | False -> false
  | Branch _ ->
      Invalid_argument "terminal_value is not applicable for an ITE node"
      |> raise

let value_node = function true -> True | false -> False

let rec apply binary_op builder lhs rhs =
  let ( @ ) = apply binary_op builder in
  let make_branch, split_top = (make_branch builder, split_top builder) in
  match min_opt (top_var lhs, top_var rhs) with
  | None ->
      (* two leaf nodes *)
      let x, y = (terminal_value lhs, terminal_value rhs) in
      binary_op x y |> value_node
  | Some var ->
      (* at least one of lhs/rhs is an internal node *)
      let lhs, rhs = (split_top var lhs, split_top var rhs) in
      let low, high = (fst lhs @ fst rhs, snd lhs @ snd rhs) in
      make_branch var low high

(* bdd manipulation functions *)

type binary_op = t -> node -> node -> node
type unary_op = t -> node -> node

let op_and = apply ( && )
let op_or = apply ( || )
let op_xor = apply (fun x y -> (x && not y) || (y && not x))
let op_nor = apply (fun x y -> not (x || y))
let op_nand = apply (fun x y -> not (x && y))
let op_imply = apply ( <= )
let op_equiv = apply ( = )
let op_not builder = op_xor builder True

(* other operators *)

type tenary_op = t -> node -> node -> node -> node

let if_then_else builder cond then_ else_ =
  let ( ! ), ( && ), ( || ) = (op_not builder, op_and builder, op_or builder) in
  let l = cond && then_ in
  let r = !cond && else_ in
  l || r

(* compute f[g/x] substitute the occurance of x with g *)
let rec subs builder f x g =
  let subs, ite, var, get_node =
    (subs builder, if_then_else builder, var builder, get_node builder)
  in
  match f with
  | True | False -> f
  | Branch (y, _, _) when x = y -> g
  | Branch (y, low, high) ->
      let low', high' = (get_node low, get_node high) in
      let low', high' = (subs low' x g, subs high' x g) in
      ite (var y) high' low'

(* quantifiers *)

(* \forall x \in {T,F} f \equiv f[T/x] \land f[F/x] *)
let forall builder x f =
  let ( && ), partial_eval = (op_and builder, subs builder f x) in
  partial_eval True && partial_eval False

(* \exists x \in {T,F} f \equiv f[T/x] \lor f[F/x] *)
let exists builder x f =
  let ( || ), partial_eval = (op_or builder, subs builder f x) in
  partial_eval True || partial_eval False

(* satisfiability *)
let unsat = ( = ) False
let sat f = unsat f |> not
