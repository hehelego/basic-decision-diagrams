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
  let get_node = get_node builder in
  let make_branch = make_branch builder in
  let ( @ ) = apply binary_op builder in
  match (lhs, rhs) with
  (* leaf nodes *)
  | False, False | False, True | True, False | True, True ->
      let x, y = (terminal_value lhs, terminal_value rhs) in
      binary_op x y |> value_node
  (* LHS is leaf *)
  | True, Branch (var, low, high) | False, Branch (var, low, high) ->
      let low, high = (get_node low, get_node high) in
      let low, high = (lhs @ low, lhs @ high) in
      make_branch var low high
  (* RHS is leaf *)
  | Branch (var, low, high), True | Branch (var, low, high), False ->
      let low, high = (get_node low, get_node high) in
      let low, high = (low @ rhs, high @ rhs) in
      make_branch var low high
  (* Non-terminal node on both sides *)
  | Branch (x, low_x, high_x), Branch (y, low_y, high_y) ->
      let low_x, high_x, low_y, high_y =
        (get_node low_x, get_node high_x, get_node low_y, get_node high_y)
      in
      let var, low, high =
        if x < y then (x, low_x @ rhs, high_x @ rhs)
        else if x > y then (y, lhs @ low_y, rhs @ high_y)
        else (x, low_x @ low_y, high_x @ high_y)
      in
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
  let op_not, op_and, op_or = (op_not builder, op_and builder, op_or builder) in
  let l = op_and cond then_ in
  let r = op_and (op_not cond) else_ in
  op_or l r

(* compute f[g/x] substitute the occurance of x with g *)
let subs builder f x g =
  let ite, var, get_node =
    (if_then_else builder, var builder, get_node builder)
  in
  match f with
  | True | False -> f
  | Branch (y, low, high) ->
      let low, high = (get_node low, get_node high) in
      let br = if x = y then g else var y in
      ite br high low

(* satisfiability *)
let unsat = ( = ) False
let sat f = unsat f |> not
