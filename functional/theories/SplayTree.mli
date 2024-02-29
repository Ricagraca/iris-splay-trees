
type __ = Obj.t

type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3

module type DecidableType =
 sig
  type t

  val eq_dec : t -> t -> sumbool
 end

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac :
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 sig
 end

module Nat :
 sig
  val compare : nat -> nat -> comparison

  val eq_dec : nat -> nat -> sumbool
 end

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

type 'x compare0 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> sumbool
 end

module Nat_as_OT :
 sig
  type t = nat

  val compare : nat -> nat -> nat compare0

  val eq_dec : nat -> nat -> sumbool
 end

module MakeRaw :
 functor (X:DecidableType) ->
 sig
  type elt = X.t

  type t = elt list

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val union : t -> t -> t

  val diff : t -> t -> t

  val inter : t -> t -> t

  val subset : t -> t -> bool

  val equal : t -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> (t, t) prod

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val isok : elt list -> bool
 end

module Make :
 functor (X:DecidableType) ->
 sig
  module Raw :
   sig
    type elt = X.t

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val subset : t -> t -> bool

    val equal : t -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> (t, t) prod

    val cardinal : t -> nat

    val elements : t -> elt list

    val choose : t -> elt option

    val isok : elt list -> bool
   end

  module E :
   sig
    type t = X.t

    val eq_dec : t -> t -> sumbool
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> (t, t) prod

  val eq_dec : t -> t -> sumbool
 end

module SplayTree :
 functor (Coq_o:OrderedType) ->
 sig
  module OrderedDecidableType :
   functor (Coq_o':OrderedType) ->
   sig
    module TO :
     sig
      type t = Coq_o'.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : Coq_o'.t -> Coq_o'.t -> sumbool

    val lt_dec : Coq_o'.t -> Coq_o'.t -> sumbool

    val eqb : Coq_o'.t -> Coq_o'.t -> bool

    type t = Coq_o'.t
   end

  module ODT :
   sig
    module TO :
     sig
      type t = Coq_o.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : Coq_o.t -> Coq_o.t -> sumbool

    val lt_dec : Coq_o.t -> Coq_o.t -> sumbool

    val eqb : Coq_o.t -> Coq_o.t -> bool

    type t = Coq_o.t
   end

  module XSet :
   sig
    module Raw :
     sig
      type elt = Coq_o.t

      type t = elt list

      val empty : t

      val is_empty : t -> bool

      val mem : elt -> t -> bool

      val add : elt -> t -> t

      val singleton : elt -> t

      val remove : elt -> t -> t

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val union : t -> t -> t

      val diff : t -> t -> t

      val inter : t -> t -> t

      val subset : t -> t -> bool

      val equal : t -> t -> bool

      val filter : (elt -> bool) -> t -> t

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val partition : (elt -> bool) -> t -> (t, t) prod

      val cardinal : t -> nat

      val elements : t -> elt list

      val choose : t -> elt option

      val isok : elt list -> bool
     end

    module E :
     sig
      type t = Coq_o.t

      val eq_dec : Coq_o.t -> Coq_o.t -> sumbool
     end

    type elt = Coq_o.t

    type t_ = Raw.t
      (* singleton inductive, whose constructor was Mkt *)

    val this : t_ -> Raw.t

    type t = t_

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val remove : elt -> t -> t

    val singleton : elt -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val empty : t

    val is_empty : t -> bool

    val elements : t -> elt list

    val choose : t -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val cardinal : t -> nat

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> (t, t) prod

    val eq_dec : t -> t -> sumbool
   end

  module TO :
   sig
    type t = Coq_o.t
   end

  module IsTO :
   sig
   end

  module OrderTac :
   sig
   end

  val eq_dec : Coq_o.t -> Coq_o.t -> sumbool

  val lt_dec : Coq_o.t -> Coq_o.t -> sumbool

  val eqb : Coq_o.t -> Coq_o.t -> bool

  type t = Coq_o.t

  val set_list : XSet.elt list -> XSet.t

  type tree =
  | L
  | T of tree * Coq_o.t * tree

  val tree_rect : 'a1 -> (tree -> 'a1 -> Coq_o.t -> tree -> 'a1 -> 'a1) -> tree -> 'a1

  val tree_rec : 'a1 -> (tree -> 'a1 -> Coq_o.t -> tree -> 'a1 -> 'a1) -> tree -> 'a1

  val ins_list : Coq_o.t -> Coq_o.t list -> Coq_o.t list

  val del_list : Coq_o.t -> Coq_o.t list -> Coq_o.t list

  val size : tree -> nat

  val in_order : tree -> Coq_o.t list

  val set_tree : tree -> XSet.t

  val splay : Coq_o.t -> tree -> tree

  val insert : Coq_o.t -> tree -> tree

  val splay_max : tree -> tree

  val delete : Coq_o.t -> tree -> tree

  type coq_R_splay =
  | R_splay_0 of tree
  | R_splay_1 of tree * tree * Coq_o.t * tree
  | R_splay_2 of tree * tree * Coq_o.t * tree
  | R_splay_3 of tree * tree * Coq_o.t * tree * tree * Coq_o.t * tree
  | R_splay_4 of tree * tree * Coq_o.t * tree * tree * Coq_o.t * tree * tree * coq_R_splay
  | R_splay_5 of tree * tree * Coq_o.t * tree * tree * Coq_o.t * tree * tree * coq_R_splay * 
     tree * Coq_o.t * tree
  | R_splay_6 of tree * tree * Coq_o.t * tree * tree * Coq_o.t * tree * tree * coq_R_splay
  | R_splay_7 of tree * tree * Coq_o.t * tree * tree * Coq_o.t * tree * tree * coq_R_splay * 
     tree * Coq_o.t * tree
  | R_splay_8 of tree * tree * Coq_o.t * tree
  | R_splay_9 of tree * tree * Coq_o.t * tree * tree * Coq_o.t * tree
  | R_splay_10 of tree * tree * Coq_o.t * tree * tree * Coq_o.t * tree * tree * coq_R_splay
  | R_splay_11 of tree * tree * Coq_o.t * tree * tree * Coq_o.t * tree * tree * coq_R_splay
     * tree * Coq_o.t * tree
  | R_splay_12 of tree * tree * Coq_o.t * tree * tree * Coq_o.t * tree * tree * coq_R_splay
  | R_splay_13 of tree * tree * Coq_o.t * tree * tree * Coq_o.t * tree * tree * coq_R_splay
     * tree * Coq_o.t * tree

  val coq_R_splay_rect :
    Coq_o.t -> (tree -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> 'a1)
    -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> __ -> 'a1) -> (tree ->
    tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __
    -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree ->
    Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> __ -> 'a1) ->
    (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree ->
    __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree -> Coq_o.t -> tree -> __ ->
    'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t ->
    tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree ->
    tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __
    -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree -> Coq_o.t -> tree -> __ -> 'a1) ->
    (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> __ -> 'a1) -> (tree -> tree
    -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __ -> __
    -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t
    -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree ->
    tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __
    -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree -> Coq_o.t -> tree -> __ -> 'a1) ->
    (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree ->
    __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree -> tree ->
    Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __ -> __ ->
    __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree -> Coq_o.t -> tree -> __ -> 'a1) -> tree ->
    tree -> coq_R_splay -> 'a1

  val coq_R_splay_rec :
    Coq_o.t -> (tree -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> 'a1)
    -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> __ -> 'a1) -> (tree ->
    tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __
    -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree ->
    Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> __ -> 'a1) ->
    (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree ->
    __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree -> Coq_o.t -> tree -> __ ->
    'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t ->
    tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree ->
    tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __
    -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree -> Coq_o.t -> tree -> __ -> 'a1) ->
    (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> __ -> 'a1) -> (tree -> tree
    -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __ -> __
    -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t
    -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree ->
    tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __
    -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree -> Coq_o.t -> tree -> __ -> 'a1) ->
    (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree ->
    __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree -> tree ->
    Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __ -> __ ->
    __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree -> Coq_o.t -> tree -> __ -> 'a1) -> tree ->
    tree -> coq_R_splay -> 'a1

  type coq_R_insert =
  | R_insert_0
  | R_insert_1 of tree * Coq_o.t * tree
  | R_insert_2 of tree * Coq_o.t * tree
  | R_insert_3 of tree * Coq_o.t * tree

  val coq_R_insert_rect :
    Coq_o.t -> tree -> (__ -> 'a1) -> (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> 'a1) -> (tree
    -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> 'a1) -> (tree -> Coq_o.t -> tree -> __ ->
    __ -> __ -> __ -> __ -> 'a1) -> tree -> coq_R_insert -> 'a1

  val coq_R_insert_rec :
    Coq_o.t -> tree -> (__ -> 'a1) -> (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> 'a1) -> (tree
    -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> 'a1) -> (tree -> Coq_o.t -> tree -> __ ->
    __ -> __ -> __ -> __ -> 'a1) -> tree -> coq_R_insert -> 'a1

  type coq_R_delete =
  | R_delete_0
  | R_delete_1 of tree * Coq_o.t * tree
  | R_delete_2 of tree * Coq_o.t * tree * tree * Coq_o.t * tree
  | R_delete_3 of tree * Coq_o.t * tree

  val coq_R_delete_rect :
    Coq_o.t -> tree -> (__ -> 'a1) -> (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> 'a1) ->
    (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> 'a1) -> (tree
    -> Coq_o.t -> tree -> __ -> __ -> __ -> 'a1) -> tree -> coq_R_delete -> 'a1

  val coq_R_delete_rec :
    Coq_o.t -> tree -> (__ -> 'a1) -> (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> 'a1) ->
    (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> 'a1) -> (tree
    -> Coq_o.t -> tree -> __ -> __ -> __ -> 'a1) -> tree -> coq_R_delete -> 'a1

  type coq_R_splay_max =
  | R_splay_max_0 of tree
  | R_splay_max_1 of tree * tree * Coq_o.t * tree
  | R_splay_max_2 of tree * tree * Coq_o.t * tree * tree * Coq_o.t * tree * tree * coq_R_splay_max
  | R_splay_max_3 of tree * tree * Coq_o.t * tree * tree * Coq_o.t * tree * tree
     * coq_R_splay_max * tree * Coq_o.t * tree

  val coq_R_splay_max_rect :
    (tree -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> 'a1) -> (tree -> tree
    -> Coq_o.t -> tree -> __ -> tree -> Coq_o.t -> tree -> __ -> tree -> coq_R_splay_max -> 'a1
    -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> tree -> Coq_o.t -> tree -> __ ->
    tree -> coq_R_splay_max -> 'a1 -> tree -> Coq_o.t -> tree -> __ -> 'a1) -> tree -> tree ->
    coq_R_splay_max -> 'a1

  val coq_R_splay_max_rec :
    (tree -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> 'a1) -> (tree -> tree
    -> Coq_o.t -> tree -> __ -> tree -> Coq_o.t -> tree -> __ -> tree -> coq_R_splay_max -> 'a1
    -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> tree -> Coq_o.t -> tree -> __ ->
    tree -> coq_R_splay_max -> 'a1 -> tree -> Coq_o.t -> tree -> __ -> 'a1) -> tree -> tree ->
    coq_R_splay_max -> 'a1
 end

module Nat_Tree :
 sig
  module OrderedDecidableType :
   functor (Coq_o':OrderedType) ->
   sig
    module TO :
     sig
      type t = Coq_o'.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : Coq_o'.t -> Coq_o'.t -> sumbool

    val lt_dec : Coq_o'.t -> Coq_o'.t -> sumbool

    val eqb : Coq_o'.t -> Coq_o'.t -> bool

    type t = Coq_o'.t
   end

  module ODT :
   sig
    module TO :
     sig
      type t = nat
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : nat -> nat -> sumbool

    val lt_dec : nat -> nat -> sumbool

    val eqb : nat -> nat -> bool

    type t = nat
   end

  module XSet :
   sig
    module Raw :
     sig
      type elt = nat

      type t = elt list

      val empty : t

      val is_empty : t -> bool

      val mem : elt -> t -> bool

      val add : elt -> t -> t

      val singleton : elt -> t

      val remove : elt -> t -> t

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val union : t -> t -> t

      val diff : t -> t -> t

      val inter : t -> t -> t

      val subset : t -> t -> bool

      val equal : t -> t -> bool

      val filter : (elt -> bool) -> t -> t

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val partition : (elt -> bool) -> t -> (t, t) prod

      val cardinal : t -> nat

      val elements : t -> elt list

      val choose : t -> elt option

      val isok : elt list -> bool
     end

    module E :
     sig
      type t = nat

      val eq_dec : nat -> nat -> sumbool
     end

    type elt = nat

    type t_ = Raw.t
      (* singleton inductive, whose constructor was Mkt *)

    val this : t_ -> Raw.t

    type t = t_

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val remove : elt -> t -> t

    val singleton : elt -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val empty : t

    val is_empty : t -> bool

    val elements : t -> elt list

    val choose : t -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val cardinal : t -> nat

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> (t, t) prod

    val eq_dec : t -> t -> sumbool
   end

  module TO :
   sig
    type t = nat
   end

  module IsTO :
   sig
   end

  module OrderTac :
   sig
   end

  val eq_dec : nat -> nat -> sumbool

  val lt_dec : nat -> nat -> sumbool

  val eqb : nat -> nat -> bool

  type t = nat

  val set_list : XSet.elt list -> XSet.t

  type tree =
  | L
  | T of tree * nat * tree

  val tree_rect : 'a1 -> (tree -> 'a1 -> nat -> tree -> 'a1 -> 'a1) -> tree -> 'a1

  val tree_rec : 'a1 -> (tree -> 'a1 -> nat -> tree -> 'a1 -> 'a1) -> tree -> 'a1

  val ins_list : nat -> nat list -> nat list

  val del_list : nat -> nat list -> nat list

  val size : tree -> nat

  val in_order : tree -> nat list

  val set_tree : tree -> XSet.t

  val splay : nat -> tree -> tree

  val insert : nat -> tree -> tree

  val splay_max : tree -> tree

  val delete : nat -> tree -> tree

  type coq_R_splay =
  | R_splay_0 of tree
  | R_splay_1 of tree * tree * nat * tree
  | R_splay_2 of tree * tree * nat * tree
  | R_splay_3 of tree * tree * nat * tree * tree * nat * tree
  | R_splay_4 of tree * tree * nat * tree * tree * nat * tree * tree * coq_R_splay
  | R_splay_5 of tree * tree * nat * tree * tree * nat * tree * tree * coq_R_splay * tree * 
     nat * tree
  | R_splay_6 of tree * tree * nat * tree * tree * nat * tree * tree * coq_R_splay
  | R_splay_7 of tree * tree * nat * tree * tree * nat * tree * tree * coq_R_splay * tree * 
     nat * tree
  | R_splay_8 of tree * tree * nat * tree
  | R_splay_9 of tree * tree * nat * tree * tree * nat * tree
  | R_splay_10 of tree * tree * nat * tree * tree * nat * tree * tree * coq_R_splay
  | R_splay_11 of tree * tree * nat * tree * tree * nat * tree * tree * coq_R_splay * tree * 
     nat * tree
  | R_splay_12 of tree * tree * nat * tree * tree * nat * tree * tree * coq_R_splay
  | R_splay_13 of tree * tree * nat * tree * tree * nat * tree * tree * coq_R_splay * tree * 
     nat * tree

  val coq_R_splay_rect :
    nat -> (tree -> __ -> 'a1) -> (tree -> tree -> nat -> tree -> __ -> __ -> __ -> 'a1) -> (tree
    -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> __ -> 'a1) -> (tree -> tree -> nat ->
    tree -> __ -> __ -> __ -> __ -> __ -> tree -> nat -> tree -> __ -> __ -> __ -> 'a1) -> (tree
    -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> nat -> tree -> __ -> __ -> __
    -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree -> tree -> nat -> tree -> __
    -> __ -> __ -> __ -> __ -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree ->
    coq_R_splay -> 'a1 -> tree -> nat -> tree -> __ -> 'a1) -> (tree -> tree -> nat -> tree -> __
    -> __ -> __ -> __ -> __ -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree ->
    coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree -> tree -> nat -> tree -> __ -> __ -> __ -> __ ->
    __ -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree
    -> nat -> tree -> __ -> 'a1) -> (tree -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ ->
    __ -> 'a1) -> (tree -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> nat ->
    tree -> __ -> __ -> __ -> 'a1) -> (tree -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __
    -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> __ ->
    'a1) -> (tree -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> nat -> tree ->
    __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree -> nat -> tree -> __ -> 'a1)
    -> (tree -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> nat -> tree -> __ ->
    __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree -> tree -> nat ->
    tree -> __ -> __ -> __ -> __ -> __ -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ ->
    tree -> coq_R_splay -> 'a1 -> tree -> nat -> tree -> __ -> 'a1) -> tree -> tree ->
    coq_R_splay -> 'a1

  val coq_R_splay_rec :
    nat -> (tree -> __ -> 'a1) -> (tree -> tree -> nat -> tree -> __ -> __ -> __ -> 'a1) -> (tree
    -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> __ -> 'a1) -> (tree -> tree -> nat ->
    tree -> __ -> __ -> __ -> __ -> __ -> tree -> nat -> tree -> __ -> __ -> __ -> 'a1) -> (tree
    -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> nat -> tree -> __ -> __ -> __
    -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree -> tree -> nat -> tree -> __
    -> __ -> __ -> __ -> __ -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree ->
    coq_R_splay -> 'a1 -> tree -> nat -> tree -> __ -> 'a1) -> (tree -> tree -> nat -> tree -> __
    -> __ -> __ -> __ -> __ -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree ->
    coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree -> tree -> nat -> tree -> __ -> __ -> __ -> __ ->
    __ -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree
    -> nat -> tree -> __ -> 'a1) -> (tree -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ ->
    __ -> 'a1) -> (tree -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> nat ->
    tree -> __ -> __ -> __ -> 'a1) -> (tree -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __
    -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> __ ->
    'a1) -> (tree -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> nat -> tree ->
    __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree -> nat -> tree -> __ -> 'a1)
    -> (tree -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> nat -> tree -> __ ->
    __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree -> tree -> nat ->
    tree -> __ -> __ -> __ -> __ -> __ -> tree -> nat -> tree -> __ -> __ -> __ -> __ -> __ ->
    tree -> coq_R_splay -> 'a1 -> tree -> nat -> tree -> __ -> 'a1) -> tree -> tree ->
    coq_R_splay -> 'a1

  type coq_R_insert =
  | R_insert_0
  | R_insert_1 of tree * nat * tree
  | R_insert_2 of tree * nat * tree
  | R_insert_3 of tree * nat * tree

  val coq_R_insert_rect :
    nat -> tree -> (__ -> 'a1) -> (tree -> nat -> tree -> __ -> __ -> __ -> 'a1) -> (tree -> nat
    -> tree -> __ -> __ -> __ -> __ -> __ -> 'a1) -> (tree -> nat -> tree -> __ -> __ -> __ -> __
    -> __ -> 'a1) -> tree -> coq_R_insert -> 'a1

  val coq_R_insert_rec :
    nat -> tree -> (__ -> 'a1) -> (tree -> nat -> tree -> __ -> __ -> __ -> 'a1) -> (tree -> nat
    -> tree -> __ -> __ -> __ -> __ -> __ -> 'a1) -> (tree -> nat -> tree -> __ -> __ -> __ -> __
    -> __ -> 'a1) -> tree -> coq_R_insert -> 'a1

  type coq_R_delete =
  | R_delete_0
  | R_delete_1 of tree * nat * tree
  | R_delete_2 of tree * nat * tree * tree * nat * tree
  | R_delete_3 of tree * nat * tree

  val coq_R_delete_rect :
    nat -> tree -> (__ -> 'a1) -> (tree -> nat -> tree -> __ -> __ -> __ -> __ -> 'a1) -> (tree
    -> nat -> tree -> __ -> __ -> __ -> tree -> nat -> tree -> __ -> 'a1) -> (tree -> nat -> tree
    -> __ -> __ -> __ -> 'a1) -> tree -> coq_R_delete -> 'a1

  val coq_R_delete_rec :
    nat -> tree -> (__ -> 'a1) -> (tree -> nat -> tree -> __ -> __ -> __ -> __ -> 'a1) -> (tree
    -> nat -> tree -> __ -> __ -> __ -> tree -> nat -> tree -> __ -> 'a1) -> (tree -> nat -> tree
    -> __ -> __ -> __ -> 'a1) -> tree -> coq_R_delete -> 'a1

  type coq_R_splay_max =
  | R_splay_max_0 of tree
  | R_splay_max_1 of tree * tree * nat * tree
  | R_splay_max_2 of tree * tree * nat * tree * tree * nat * tree * tree * coq_R_splay_max
  | R_splay_max_3 of tree * tree * nat * tree * tree * nat * tree * tree * coq_R_splay_max * 
     tree * nat * tree

  val coq_R_splay_max_rect :
    (tree -> __ -> 'a1) -> (tree -> tree -> nat -> tree -> __ -> __ -> 'a1) -> (tree -> tree ->
    nat -> tree -> __ -> tree -> nat -> tree -> __ -> tree -> coq_R_splay_max -> 'a1 -> __ ->
    'a1) -> (tree -> tree -> nat -> tree -> __ -> tree -> nat -> tree -> __ -> tree ->
    coq_R_splay_max -> 'a1 -> tree -> nat -> tree -> __ -> 'a1) -> tree -> tree ->
    coq_R_splay_max -> 'a1

  val coq_R_splay_max_rec :
    (tree -> __ -> 'a1) -> (tree -> tree -> nat -> tree -> __ -> __ -> 'a1) -> (tree -> tree ->
    nat -> tree -> __ -> tree -> nat -> tree -> __ -> tree -> coq_R_splay_max -> 'a1 -> __ ->
    'a1) -> (tree -> tree -> nat -> tree -> __ -> tree -> nat -> tree -> __ -> tree ->
    coq_R_splay_max -> 'a1 -> tree -> nat -> tree -> __ -> 'a1) -> tree -> tree ->
    coq_R_splay_max -> 'a1
 end
