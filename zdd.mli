type var_id = int
type node_id = int
type node
type t

val builder : unit -> t

val empty : node
(** the set family {} *)

val unit : node
(** the set family { {} } *)

val singleton : t -> var_id -> node
(** the set family { {x} } *)

val from_list : t -> var_id list -> node
(** the set family { s } *)

val insert : t -> var_id -> node -> node
(** [insert x f] is the set family {s+{x}: s in f} *)

val remove : t -> var_id -> node -> node
(** [remove x f] is the set family {s-{x}: s in f} *)

(* set operations *)

val filter1 : t -> var_id -> node -> node
(** [filter1 x f] is the family {s-{x}: s in f, x in s} *)

val filter0 : t -> var_id -> node -> node
(** [filter0 x f] is the family {s: s in f, not (x in s)} *)

type set_op = t -> node -> node -> node

val union : set_op
(** [union f g] is the set family {{s: (s in f) or (s in g)}} *)

val intersect : set_op
(** [intersect f g] is the set family {s: (s in f) and (s in g)} *)

val diff : set_op
(** [diff f g] is the set family {s: (s in f) and (not (s in g))} *)

val sym_diff : set_op
(** [sym_diff f g] is the union of [diff f g] and [diff g f] *)

val family : t -> node -> var_id list list
(** [family f] evaluates the set family represented by a ZDD *)

val count : t -> node -> int
(** [count f] counts the number of subsets in the families corresponding to a ZDD.
    The result should be equivalent to [length (family f)] *)
