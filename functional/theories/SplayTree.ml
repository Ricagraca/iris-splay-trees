
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type comparison =
| Eq
| Lt
| Gt

type sumbool =
| Left
| Right

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3 **)

let flip f x y =
  f y x

module type DecidableType =
 sig
  type t

  val eq_dec : t -> t -> sumbool
 end

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module Nat =
 struct
  (** val compare : nat -> nat -> comparison **)

  let rec compare n m =
    match n with
    | O -> (match m with
            | O -> Eq
            | S _ -> Lt)
    | S n' -> (match m with
               | O -> Gt
               | S m' -> compare n' m')

  (** val eq_dec : nat -> nat -> sumbool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> Left
            | S _ -> Right)
    | S n0 -> (match m with
               | O -> Right
               | S m0 -> eq_dec n0 m0)
 end

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | Nil -> a0
  | Cons (b, t0) -> fold_left f t0 (f a0 b)

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

module Nat_as_OT =
 struct
  type t = nat

  (** val compare : nat -> nat -> nat compare0 **)

  let compare x y =
    match Nat.compare x y with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT

  (** val eq_dec : nat -> nat -> sumbool **)

  let eq_dec =
    Nat.eq_dec
 end

module MakeRaw =
 functor (X:DecidableType) ->
 struct
  type elt = X.t

  type t = elt list

  (** val empty : t **)

  let empty =
    Nil

  (** val is_empty : t -> bool **)

  let is_empty = function
  | Nil -> True
  | Cons (_, _) -> False

  (** val mem : elt -> t -> bool **)

  let rec mem x = function
  | Nil -> False
  | Cons (y, l) -> (match X.eq_dec x y with
                    | Left -> True
                    | Right -> mem x l)

  (** val add : elt -> t -> t **)

  let rec add x s = match s with
  | Nil -> Cons (x, Nil)
  | Cons (y, l) -> (match X.eq_dec x y with
                    | Left -> s
                    | Right -> Cons (y, (add x l)))

  (** val singleton : elt -> t **)

  let singleton x =
    Cons (x, Nil)

  (** val remove : elt -> t -> t **)

  let rec remove x = function
  | Nil -> Nil
  | Cons (y, l) -> (match X.eq_dec x y with
                    | Left -> l
                    | Right -> Cons (y, (remove x l)))

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f =
    fold_left (flip f)

  (** val union : t -> t -> t **)

  let union s =
    fold add s

  (** val diff : t -> t -> t **)

  let diff s s' =
    fold remove s' s

  (** val inter : t -> t -> t **)

  let inter s s' =
    fold (fun x s0 -> match mem x s' with
                      | True -> add x s0
                      | False -> s0) s Nil

  (** val subset : t -> t -> bool **)

  let subset s s' =
    is_empty (diff s s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    match subset s s' with
    | True -> subset s' s
    | False -> False

  (** val filter : (elt -> bool) -> t -> t **)

  let rec filter f = function
  | Nil -> Nil
  | Cons (x, l) -> (match f x with
                    | True -> Cons (x, (filter f l))
                    | False -> filter f l)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let rec for_all f = function
  | Nil -> True
  | Cons (x, l) -> (match f x with
                    | True -> for_all f l
                    | False -> False)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let rec exists_ f = function
  | Nil -> False
  | Cons (x, l) -> (match f x with
                    | True -> True
                    | False -> exists_ f l)

  (** val partition : (elt -> bool) -> t -> (t, t) prod **)

  let rec partition f = function
  | Nil -> Pair (Nil, Nil)
  | Cons (x, l) ->
    let Pair (s1, s2) = partition f l in
    (match f x with
     | True -> Pair ((Cons (x, s1)), s2)
     | False -> Pair (s1, (Cons (x, s2))))

  (** val cardinal : t -> nat **)

  let cardinal =
    length

  (** val elements : t -> elt list **)

  let elements s =
    s

  (** val choose : t -> elt option **)

  let choose = function
  | Nil -> None
  | Cons (x, _) -> Some x

  (** val isok : elt list -> bool **)

  let rec isok = function
  | Nil -> True
  | Cons (a, l0) -> (match negb (mem a l0) with
                     | True -> isok l0
                     | False -> False)
 end

module Make =
 functor (X:DecidableType) ->
 struct
  module Raw = MakeRaw(X)

  module E =
   struct
    type t = X.t

    (** val eq_dec : t -> t -> sumbool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem x s =
    Raw.mem x (this s)

  (** val add : elt -> t -> t **)

  let add x s =
    Raw.add x (this s)

  (** val remove : elt -> t -> t **)

  let remove x s =
    Raw.remove x (this s)

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union s s' =
    Raw.union (this s) (this s')

  (** val inter : t -> t -> t **)

  let inter s s' =
    Raw.inter (this s) (this s')

  (** val diff : t -> t -> t **)

  let diff s s' =
    Raw.diff (this s) (this s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s =
    Raw.fold f (this s)

  (** val cardinal : t -> nat **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f s =
    Raw.filter f (this s)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f s =
    Raw.for_all f (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f s =
    Raw.exists_ f (this s)

  (** val partition : (elt -> bool) -> t -> (t, t) prod **)

  let partition f s =
    let p = Raw.partition f (this s) in Pair ((fst p), (snd p))

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in (match b with
                                 | True -> Left
                                 | False -> Right)
 end

module SplayTree =
 functor (Coq_o:OrderedType) ->
 struct
  module OrderedDecidableType =
   functor (Coq_o':OrderedType) ->
   struct
    module TO =
     struct
      type t = Coq_o'.t
     end

    module IsTO =
     struct
     end

    module OrderTac = MakeOrderTac(TO)(IsTO)

    (** val eq_dec : Coq_o'.t -> Coq_o'.t -> sumbool **)

    let eq_dec =
      Coq_o'.eq_dec

    (** val lt_dec : Coq_o'.t -> Coq_o'.t -> sumbool **)

    let lt_dec x y =
      match Coq_o'.compare x y with
      | LT -> Left
      | _ -> Right

    (** val eqb : Coq_o'.t -> Coq_o'.t -> bool **)

    let eqb x y =
      match eq_dec x y with
      | Left -> True
      | Right -> False

    type t = Coq_o'.t
   end

  module ODT =
   struct
    module TO =
     struct
      type t = Coq_o.t
     end

    module IsTO =
     struct
     end

    module OrderTac = MakeOrderTac(TO)(IsTO)

    (** val eq_dec : Coq_o.t -> Coq_o.t -> sumbool **)

    let eq_dec =
      Coq_o.eq_dec

    (** val lt_dec : Coq_o.t -> Coq_o.t -> sumbool **)

    let lt_dec x y =
      match Coq_o.compare x y with
      | LT -> Left
      | _ -> Right

    (** val eqb : Coq_o.t -> Coq_o.t -> bool **)

    let eqb x y =
      match eq_dec x y with
      | Left -> True
      | Right -> False

    type t = Coq_o.t
   end

  module XSet = Make(ODT)

  module TO = ODT.TO

  module IsTO = ODT.IsTO

  module OrderTac = ODT.OrderTac

  (** val eq_dec : Coq_o.t -> Coq_o.t -> sumbool **)

  let eq_dec =
    Coq_o.eq_dec

  (** val lt_dec : Coq_o.t -> Coq_o.t -> sumbool **)

  let lt_dec x y =
    match Coq_o.compare x y with
    | LT -> Left
    | _ -> Right

  (** val eqb : Coq_o.t -> Coq_o.t -> bool **)

  let eqb x y =
    match eq_dec x y with
    | Left -> True
    | Right -> False

  type t = Coq_o.t

  (** val set_list : XSet.elt list -> XSet.t **)

  let rec set_list = function
  | Nil -> XSet.empty
  | Cons (a, h) -> XSet.add a (set_list h)

  type tree =
  | L
  | T of tree * Coq_o.t * tree

  (** val tree_rect : 'a1 -> (tree -> 'a1 -> Coq_o.t -> tree -> 'a1 -> 'a1) -> tree -> 'a1 **)

  let rec tree_rect f f0 = function
  | L -> f
  | T (t1, n, t2) -> f0 t1 (tree_rect f f0 t1) n t2 (tree_rect f f0 t2)

  (** val tree_rec : 'a1 -> (tree -> 'a1 -> Coq_o.t -> tree -> 'a1 -> 'a1) -> tree -> 'a1 **)

  let rec tree_rec f f0 = function
  | L -> f
  | T (t1, n, t2) -> f0 t1 (tree_rec f f0 t1) n t2 (tree_rec f f0 t2)

  (** val ins_list : Coq_o.t -> Coq_o.t list -> Coq_o.t list **)

  let rec ins_list x l = match l with
  | Nil -> Cons (x, Nil)
  | Cons (a, h) ->
    (match eq_dec x a with
     | Left -> l
     | Right -> (match lt_dec x a with
                 | Left -> Cons (x, l)
                 | Right -> Cons (a, (ins_list x h))))

  (** val del_list : Coq_o.t -> Coq_o.t list -> Coq_o.t list **)

  let rec del_list x = function
  | Nil -> Nil
  | Cons (a, h) -> (match eq_dec x a with
                    | Left -> h
                    | Right -> Cons (a, (del_list x h)))

  (** val size : tree -> nat **)

  let rec size = function
  | L -> O
  | T (t1, _, t2) -> add (add (size t1) (size t2)) (S O)

  (** val in_order : tree -> Coq_o.t list **)

  let rec in_order = function
  | L -> Nil
  | T (t1, a, t2) -> app (in_order t1) (app (Cons (a, Nil)) (in_order t2))

  (** val set_tree : tree -> XSet.t **)

  let rec set_tree = function
  | L -> XSet.empty
  | T (l, a, r) -> XSet.union (XSet.singleton a) (XSet.union (set_tree l) (set_tree r))

  (** val splay : Coq_o.t -> tree -> tree **)

  let rec splay a = function
  | L -> L
  | T (cl, c, cr) ->
    (match eq_dec a c with
     | Left -> T (cl, c, cr)
     | Right ->
       (match lt_dec a c with
        | Left ->
          (match cl with
           | L -> T (cl, c, cr)
           | T (bl, b, br) ->
             (match eq_dec a b with
              | Left -> T (bl, b, (T (br, c, cr)))
              | Right ->
                (match lt_dec a b with
                 | Left ->
                   (match splay a bl with
                    | L -> T (bl, b, (T (br, c, cr)))
                    | T (al, a', ar) -> T (al, a', (T (ar, b, (T (br, c, cr))))))
                 | Right ->
                   (match splay a br with
                    | L -> T (bl, b, (T (br, c, cr)))
                    | T (al, a', ar) -> T ((T (bl, b, al)), a', (T (ar, c, cr)))))))
        | Right ->
          (match cr with
           | L -> T (cl, c, cr)
           | T (bl, b, br) ->
             (match eq_dec a b with
              | Left -> T ((T (cl, c, bl)), b, br)
              | Right ->
                (match lt_dec a b with
                 | Left ->
                   (match splay a bl with
                    | L -> T ((T (cl, c, bl)), b, br)
                    | T (al, a', ar) -> T ((T (cl, c, al)), a', (T (ar, b, br))))
                 | Right ->
                   (match splay a br with
                    | L -> T ((T (cl, c, bl)), b, br)
                    | T (al, a', ar) -> T ((T ((T (cl, c, bl)), b, al)), a', ar)))))))

  (** val insert : Coq_o.t -> tree -> tree **)

  let insert a t0 =
    match splay a t0 with
    | L -> T (L, a, L)
    | T (l, a', r) ->
      (match eq_dec a a' with
       | Left -> T (l, a, r)
       | Right ->
         (match lt_dec a a' with
          | Left -> T (l, a, (T (L, a', r)))
          | Right -> T ((T (l, a', L)), a, r)))

  (** val splay_max : tree -> tree **)

  let rec splay_max = function
  | L -> L
  | T (l, b, t2) ->
    (match t2 with
     | L -> T (l, b, L)
     | T (rl, c, rr) ->
       (match splay_max rr with
        | L -> T ((T (l, b, rl)), c, L)
        | T (rrl, x, xa) -> T ((T ((T (l, b, rl)), c, rrl)), x, xa)))

  (** val delete : Coq_o.t -> tree -> tree **)

  let delete a t0 =
    match splay a t0 with
    | L -> L
    | T (l, a', r) ->
      (match eq_dec a a' with
       | Left -> (match splay_max l with
                  | L -> r
                  | T (l', m, _) -> T (l', m, r))
       | Right -> T (l, a', r))

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

  (** val coq_R_splay_rect :
      Coq_o.t -> (tree -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ ->
      'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> __ -> 'a1) ->
      (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree
      -> __ -> __ -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __
      -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 ->
      __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree ->
      Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree ->
      Coq_o.t -> tree -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __
      -> __ -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay ->
      'a1 -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree
      -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree ->
      Coq_o.t -> tree -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __
      -> __ -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ ->
      tree -> Coq_o.t -> tree -> __ -> __ -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __
      -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree ->
      coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ ->
      __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay ->
      'a1 -> tree -> Coq_o.t -> tree -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ ->
      __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree ->
      coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ ->
      __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay ->
      'a1 -> tree -> Coq_o.t -> tree -> __ -> 'a1) -> tree -> tree -> coq_R_splay -> 'a1 **)

  let rec coq_R_splay_rect a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 _ _ = function
  | R_splay_0 t0 -> f t0 __
  | R_splay_1 (t0, cl, c, cr) -> f0 t0 cl c cr __ __ __
  | R_splay_2 (t0, cl, c, cr) -> f1 t0 cl c cr __ __ __ __ __ __
  | R_splay_3 (t0, cl, c, cr, bl, b, br) -> f2 t0 cl c cr __ __ __ __ __ bl b br __ __ __
  | R_splay_4 (t0, cl, c, cr, bl, b, br, _res, r0) ->
    f3 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rect a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 bl _res r0) __
  | R_splay_5 (t0, cl, c, cr, bl, b, br, _res, r0, al, a', ar) ->
    f4 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rect a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 bl _res r0) al a' ar __
  | R_splay_6 (t0, cl, c, cr, bl, b, br, _res, r0) ->
    f5 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rect a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 br _res r0) __
  | R_splay_7 (t0, cl, c, cr, bl, b, br, _res, r0, al, a', ar) ->
    f6 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rect a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 br _res r0) al a' ar __
  | R_splay_8 (t0, cl, c, cr) -> f7 t0 cl c cr __ __ __ __ __ __
  | R_splay_9 (t0, cl, c, cr, bl, b, br) -> f8 t0 cl c cr __ __ __ __ __ bl b br __ __ __
  | R_splay_10 (t0, cl, c, cr, bl, b, br, _res, r0) ->
    f9 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rect a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 bl _res r0) __
  | R_splay_11 (t0, cl, c, cr, bl, b, br, _res, r0, al, a', ar) ->
    f10 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rect a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 bl _res r0) al a' ar __
  | R_splay_12 (t0, cl, c, cr, bl, b, br, _res, r0) ->
    f11 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rect a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 br _res r0) __
  | R_splay_13 (t0, cl, c, cr, bl, b, br, _res, r0, al, a', ar) ->
    f12 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rect a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 br _res r0) al a' ar __

  (** val coq_R_splay_rec :
      Coq_o.t -> (tree -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ ->
      'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> __ -> 'a1) ->
      (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree
      -> __ -> __ -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __
      -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 ->
      __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree ->
      Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree ->
      Coq_o.t -> tree -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __
      -> __ -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay ->
      'a1 -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree
      -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay -> 'a1 -> tree ->
      Coq_o.t -> tree -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __
      -> __ -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ ->
      tree -> Coq_o.t -> tree -> __ -> __ -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __
      -> __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree ->
      coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ ->
      __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay ->
      'a1 -> tree -> Coq_o.t -> tree -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ ->
      __ -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree ->
      coq_R_splay -> 'a1 -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> __ ->
      __ -> __ -> tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> tree -> coq_R_splay ->
      'a1 -> tree -> Coq_o.t -> tree -> __ -> 'a1) -> tree -> tree -> coq_R_splay -> 'a1 **)

  let rec coq_R_splay_rec a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 _ _ = function
  | R_splay_0 t0 -> f t0 __
  | R_splay_1 (t0, cl, c, cr) -> f0 t0 cl c cr __ __ __
  | R_splay_2 (t0, cl, c, cr) -> f1 t0 cl c cr __ __ __ __ __ __
  | R_splay_3 (t0, cl, c, cr, bl, b, br) -> f2 t0 cl c cr __ __ __ __ __ bl b br __ __ __
  | R_splay_4 (t0, cl, c, cr, bl, b, br, _res, r0) ->
    f3 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rec a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 bl _res r0) __
  | R_splay_5 (t0, cl, c, cr, bl, b, br, _res, r0, al, a', ar) ->
    f4 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rec a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 bl _res r0) al a' ar __
  | R_splay_6 (t0, cl, c, cr, bl, b, br, _res, r0) ->
    f5 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rec a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 br _res r0) __
  | R_splay_7 (t0, cl, c, cr, bl, b, br, _res, r0, al, a', ar) ->
    f6 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rec a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 br _res r0) al a' ar __
  | R_splay_8 (t0, cl, c, cr) -> f7 t0 cl c cr __ __ __ __ __ __
  | R_splay_9 (t0, cl, c, cr, bl, b, br) -> f8 t0 cl c cr __ __ __ __ __ bl b br __ __ __
  | R_splay_10 (t0, cl, c, cr, bl, b, br, _res, r0) ->
    f9 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rec a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 bl _res r0) __
  | R_splay_11 (t0, cl, c, cr, bl, b, br, _res, r0, al, a', ar) ->
    f10 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rec a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 bl _res r0) al a' ar __
  | R_splay_12 (t0, cl, c, cr, bl, b, br, _res, r0) ->
    f11 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rec a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 br _res r0) __
  | R_splay_13 (t0, cl, c, cr, bl, b, br, _res, r0, al, a', ar) ->
    f12 t0 cl c cr __ __ __ __ __ bl b br __ __ __ __ __ _res r0
      (coq_R_splay_rec a f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 br _res r0) al a' ar __

  type coq_R_insert =
  | R_insert_0
  | R_insert_1 of tree * Coq_o.t * tree
  | R_insert_2 of tree * Coq_o.t * tree
  | R_insert_3 of tree * Coq_o.t * tree

  (** val coq_R_insert_rect :
      Coq_o.t -> tree -> (__ -> 'a1) -> (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> 'a1) ->
      (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> 'a1) -> (tree -> Coq_o.t -> tree
      -> __ -> __ -> __ -> __ -> __ -> 'a1) -> tree -> coq_R_insert -> 'a1 **)

  let coq_R_insert_rect _ _ f f0 f1 f2 _ = function
  | R_insert_0 -> f __
  | R_insert_1 (x, x0, x1) -> f0 x x0 x1 __ __ __
  | R_insert_2 (x, x0, x1) -> f1 x x0 x1 __ __ __ __ __
  | R_insert_3 (x, x0, x1) -> f2 x x0 x1 __ __ __ __ __

  (** val coq_R_insert_rec :
      Coq_o.t -> tree -> (__ -> 'a1) -> (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> 'a1) ->
      (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> __ -> 'a1) -> (tree -> Coq_o.t -> tree
      -> __ -> __ -> __ -> __ -> __ -> 'a1) -> tree -> coq_R_insert -> 'a1 **)

  let coq_R_insert_rec _ _ f f0 f1 f2 _ = function
  | R_insert_0 -> f __
  | R_insert_1 (x, x0, x1) -> f0 x x0 x1 __ __ __
  | R_insert_2 (x, x0, x1) -> f1 x x0 x1 __ __ __ __ __
  | R_insert_3 (x, x0, x1) -> f2 x x0 x1 __ __ __ __ __

  type coq_R_delete =
  | R_delete_0
  | R_delete_1 of tree * Coq_o.t * tree
  | R_delete_2 of tree * Coq_o.t * tree * tree * Coq_o.t * tree
  | R_delete_3 of tree * Coq_o.t * tree

  (** val coq_R_delete_rect :
      Coq_o.t -> tree -> (__ -> 'a1) -> (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> 'a1)
      -> (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> 'a1) ->
      (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> 'a1) -> tree -> coq_R_delete -> 'a1 **)

  let coq_R_delete_rect _ _ f f0 f1 f2 _ = function
  | R_delete_0 -> f __
  | R_delete_1 (x, x0, x1) -> f0 x x0 x1 __ __ __ __
  | R_delete_2 (x, x0, x1, x2, x3, x4) -> f1 x x0 x1 __ __ __ x2 x3 x4 __
  | R_delete_3 (x, x0, x1) -> f2 x x0 x1 __ __ __

  (** val coq_R_delete_rec :
      Coq_o.t -> tree -> (__ -> 'a1) -> (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> __ -> 'a1)
      -> (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> tree -> Coq_o.t -> tree -> __ -> 'a1) ->
      (tree -> Coq_o.t -> tree -> __ -> __ -> __ -> 'a1) -> tree -> coq_R_delete -> 'a1 **)

  let coq_R_delete_rec _ _ f f0 f1 f2 _ = function
  | R_delete_0 -> f __
  | R_delete_1 (x, x0, x1) -> f0 x x0 x1 __ __ __ __
  | R_delete_2 (x, x0, x1, x2, x3, x4) -> f1 x x0 x1 __ __ __ x2 x3 x4 __
  | R_delete_3 (x, x0, x1) -> f2 x x0 x1 __ __ __

  type coq_R_splay_max =
  | R_splay_max_0 of tree
  | R_splay_max_1 of tree * tree * Coq_o.t * tree
  | R_splay_max_2 of tree * tree * Coq_o.t * tree * tree * Coq_o.t * tree * tree * coq_R_splay_max
  | R_splay_max_3 of tree * tree * Coq_o.t * tree * tree * Coq_o.t * tree * tree
     * coq_R_splay_max * tree * Coq_o.t * tree

  (** val coq_R_splay_max_rect :
      (tree -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> 'a1) -> (tree ->
      tree -> Coq_o.t -> tree -> __ -> tree -> Coq_o.t -> tree -> __ -> tree -> coq_R_splay_max
      -> 'a1 -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> tree -> Coq_o.t -> tree
      -> __ -> tree -> coq_R_splay_max -> 'a1 -> tree -> Coq_o.t -> tree -> __ -> 'a1) -> tree ->
      tree -> coq_R_splay_max -> 'a1 **)

  let rec coq_R_splay_max_rect f f0 f1 f2 _ _ = function
  | R_splay_max_0 t0 -> f t0 __
  | R_splay_max_1 (t0, l, b, t2) -> f0 t0 l b t2 __ __
  | R_splay_max_2 (t0, l, b, t2, rl, c, rr, _res, r0) ->
    f1 t0 l b t2 __ rl c rr __ _res r0 (coq_R_splay_max_rect f f0 f1 f2 rr _res r0) __
  | R_splay_max_3 (t0, l, b, t2, rl, c, rr, _res, r0, rrl, x, xa) ->
    f2 t0 l b t2 __ rl c rr __ _res r0 (coq_R_splay_max_rect f f0 f1 f2 rr _res r0) rrl x xa __

  (** val coq_R_splay_max_rec :
      (tree -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> __ -> 'a1) -> (tree ->
      tree -> Coq_o.t -> tree -> __ -> tree -> Coq_o.t -> tree -> __ -> tree -> coq_R_splay_max
      -> 'a1 -> __ -> 'a1) -> (tree -> tree -> Coq_o.t -> tree -> __ -> tree -> Coq_o.t -> tree
      -> __ -> tree -> coq_R_splay_max -> 'a1 -> tree -> Coq_o.t -> tree -> __ -> 'a1) -> tree ->
      tree -> coq_R_splay_max -> 'a1 **)

  let rec coq_R_splay_max_rec f f0 f1 f2 _ _ = function
  | R_splay_max_0 t0 -> f t0 __
  | R_splay_max_1 (t0, l, b, t2) -> f0 t0 l b t2 __ __
  | R_splay_max_2 (t0, l, b, t2, rl, c, rr, _res, r0) ->
    f1 t0 l b t2 __ rl c rr __ _res r0 (coq_R_splay_max_rec f f0 f1 f2 rr _res r0) __
  | R_splay_max_3 (t0, l, b, t2, rl, c, rr, _res, r0, rrl, x, xa) ->
    f2 t0 l b t2 __ rl c rr __ _res r0 (coq_R_splay_max_rec f f0 f1 f2 rr _res r0) rrl x xa __
 end

module Nat_Tree = SplayTree(Nat_as_OT)
