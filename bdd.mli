type var_id = int
type node_id = int
type node
type t

val builder : unit -> t
val apply : (bool -> bool -> bool) -> t -> node -> node -> node
val leaf_true : node
val leaf_false : node
val var : t -> var_id -> node

type tenary_op = t -> node -> node -> node -> node
type binary_op = t -> node -> node -> node
type unary_op = t -> node -> node

(* unary/binary/ternary operators *)

val op_and : binary_op
val op_or : binary_op
val op_xor : binary_op
val op_nor : binary_op
val op_nand : binary_op
val op_imply : binary_op
val op_equiv : binary_op
val op_not : unary_op
val if_then_else : tenary_op

(* variable substitution *)
val subs : t -> node -> var_id -> node -> node

(* quantifications over boolean variables *)
val forall : t -> var_id -> node -> node
val exists : t -> var_id -> node -> node

(* SAT solving *)
val unsat : node -> bool
val sat : node -> bool
