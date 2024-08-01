type var_id = int
type node_id = int
type node = Bottom | Top | Partition of var_id * node_id * node_id
type t = { index : (node, node_id) Hashtbl.t; store : node Dynarray.t }
type 'a base_case = { bottom_value : 'a; top_value : 'a }

let default_size = 1 lsl 20

let builder () =
  let index = Hashtbl.create default_size in
  let store = Dynarray.create () in
  Dynarray.add_last store Bottom;
  Dynarray.add_last store Top;
  Hashtbl.add index Bottom 0;
  Hashtbl.add index Top 1;
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

let empty = Bottom
let unit = Top

let singleton builder var =
  let node = Partition (var, 0, 1) in
  add_node builder node;
  node

let make_partition builder var low high =
  let valid_subbdd = function
    | Bottom | Top -> true
    | Partition (var', _, _) -> var < var'
  in
  assert (valid_subbdd low);
  assert (valid_subbdd high);
  let get_id = get_id builder in
  let low', high' = (get_id low, get_id high) in
  if high = Bottom then low
  else
    let node = Partition (var, low', high') in
    add_node builder node;
    node

let from_list builder vars =
  let vars = List.sort compare vars in
  let rec make = function
    | [] -> Bottom
    | x :: xs ->
        let rest = make xs in
        make_partition builder x rest Top
  in
  make vars

let filter1 builder x =
  let get_node, make_partition = (get_node builder, make_partition builder) in
  let rec filter = function
    | Top | Bottom -> Bottom (* leaf nodes = Partition (+inf, nil, nil) *)
    | Partition (y, low, high) ->
        if x < y then Bottom
        else if x > y then
          let low', high' = (get_node low, get_node high) in
          let low', high' = (filter low', filter high') in
          make_partition y low' high'
        else (* x=y *)
          get_node high
  in
  filter

let filter0 builder x =
  let get_node, make_partition = (get_node builder, make_partition builder) in
  let rec filter node =
    match node with
    | Top | Bottom -> node (* leaf nodes = Partition (+inf, nil, nil) *)
    | Partition (y, low, high) ->
        if x < y then node
        else if x > y then
          let low', high' = (get_node low, get_node high) in
          let low', high' = (filter low', filter high') in
          make_partition y low' high'
        else (* x=y *)
          get_node low
  in
  filter

type set_op = t -> node -> node -> node

let union builder =
  let get_node, make_partition = (get_node builder, make_partition builder) in
  let filter0, filter1 = (filter0 builder, filter1 builder) in
  let rec ( ++ ) lhs rhs =
    match (lhs, rhs) with
    (* base case *)
    | Bottom, r | r, Bottom -> r
    | Top, Top -> Top
    | l, r when l = r -> lhs
    | Top, Partition (x, low, high) | Partition (x, low, high), Top ->
        let low', high' = (get_node low, get_node high) in
        let low' = low' ++ Top in
        make_partition x low' high'
    | Partition (x, low_x, high_x), Partition (y, low_y, high_y) ->
        let low_x, high_x, low_y, high_y =
          (get_node low_x, get_node high_x, get_node low_y, get_node high_y)
        in
        let var, low, high =
          if x < y then (x, low_x ++ filter0 x rhs, high_x ++ filter1 x rhs)
          else if x > y then (y, filter0 y lhs ++ low_y, filter1 y rhs ++ high_y)
          else (x, low_x ++ low_y, high_x ++ high_y)
        in
        make_partition var low high
  in
  ( ++ )

let intersect builder =
  let get_node, make_partition = (get_node builder, make_partition builder) in
  let filter0, filter1 = (filter0 builder, filter1 builder) in
  let rec ( ** ) lhs rhs =
    match (lhs, rhs) with
    (* base case *)
    | Bottom, _ | _, Bottom -> Bottom
    | Top, Top -> Top
    | l, r when l = r -> lhs
    | Top, Partition (x, low, high) | Partition (x, low, high), Top ->
        let low', high' = (get_node low, get_node high) in
        let low' = low' ** Top in
        make_partition x low' high'
    | Partition (x, low_x, high_x), Partition (y, low_y, high_y) ->
        let low_x, high_x, low_y, high_y =
          (get_node low_x, get_node high_x, get_node low_y, get_node high_y)
        in
        let var, low, high =
          if x < y then (x, low_x ** filter0 x rhs, high_x ** filter1 x rhs)
          else if x > y then (y, filter0 y lhs ** low_y, filter1 y rhs ** high_y)
          else (x, low_x ** low_y, high_x ** high_y)
        in
        make_partition var low high
  in
  ( ** )

let diff builder =
  let get_node, make_partition = (get_node builder, make_partition builder) in
  let filter0, filter1 = (filter0 builder, filter1 builder) in
  let rec ( -- ) lhs rhs =
    match (lhs, rhs) with
    (* base case *)
    | Bottom, _ -> Bottom
    | l, Bottom -> l
    | Top, Top -> Top
    | l, r when l = r -> Bottom
    | Top, Partition (_, low, _) ->
        let low' = get_node low in
        Top -- low'
    | Partition (x, low, high), Top ->
        let low', high' = (get_node low, get_node high) in
        let low' = low' -- Top in
        make_partition x low' high'
    | Partition (x, low_x, high_x), Partition (y, low_y, high_y) ->
        let low_x, high_x, low_y, high_y =
          (get_node low_x, get_node high_x, get_node low_y, get_node high_y)
        in
        let var, low, high =
          if x < y then (x, low_x -- filter0 x rhs, high_x -- filter1 x rhs)
          else if x > y then (y, filter0 y lhs -- low_y, filter1 y rhs -- high_y)
          else (x, low_x -- low_y, high_x -- high_y)
        in
        make_partition var low high
  in
  ( -- )

let sym_diff builder lhs rhs =
  let ( -- ), ( ++ ) = (diff builder, union builder) in
  let lr, rl = (lhs -- rhs, rhs -- lhs) in
  lr ++ rl

let cached_recursion base_case combine builder =
  let cache = Array.make (Dynarray.length builder.store) None in
  let get_id, get_node = (get_id builder, get_node builder) in
  let rec f node =
    match node with
    | Bottom -> base_case.bottom_value
    | Top -> base_case.top_value
    | Partition (x, low, high) -> (
        let id = get_id node in
        match cache.(id) with
        | Some cached -> cached
        | None ->
            let low, high = (get_node low, get_node high) in
            let x0, x1 = (f low, f high) in
            let result = combine x x0 x1 in
            cache.(id) <- Some result;
            result)
  in
  f

let family =
  let combine x x0 x1 =
    List.(
      let x1' = map (cons x) x1 in
      x0 @ x1')
  in
  cached_recursion { bottom_value = []; top_value = [ [] ] } combine

let count =
  let combine _ = ( + ) in
  cached_recursion { bottom_value = 0; top_value = 1 } combine
