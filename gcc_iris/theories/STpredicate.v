From ST Require Import STorientation.
From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual LibInt.
From stdpp Require Import gmap.
From iris.bi Require Import big_op.
From iris_time.heap_lang Require Import proofmode.
From iris_time Require Import Combined.
  
Section SplayTreePredicate.

  Context `{!tctrHeapG Σ} (nmax : nat).
  
  Notation elem := loc.
  Notation EdgeSet := (elem -> elem -> orientation -> Prop).
  
  Inductive content :=
  | NodeB : Z -> elem -> elem -> content
  | NodeL : Z -> elem -> content
  | NodeR : Z -> elem -> content
  | NodeN : Z -> content.

  Inductive path : EdgeSet -> elem -> elem -> Prop :=
    path_refl : forall F x, path F x x
  | path_single  : forall (F : EdgeSet) x y o, F x y o -> path F x y
  | path_trans : forall F x y z, path F x y -> path F y z -> path F x z.

  (* Graph structure *)
  Variable x y r : elem.
  Variable v : val.
  Variable R : elem.
  Variable D : LibSet.set elem.   (* domain *)
  Variable F : elem -> elem -> orientation -> Prop. (* edges *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* weight of node *)
  Variable M : gmap elem content. (* view of the memory *)

  (* Binary tree has at most two children:

                 x 
                / \
               y  z

     Meaning that y and z can't be the same 
     for different orientation

     *)
  
  Definition binarytree (F : EdgeSet) :=
    forall x y z l r,
      ~ (z = y) -> 
      F x y l -> F x z r ->
      ~ (r = l).


  (*

      There is an unique root:

             r1      r2
            /  \    /
           x   y   /
               \  /
                z 

      r1 and r2 anren't roots, since r1 /-> r2 nor r2 /-> r1

   *)

  Definition isroot (D : LibSet.set elem) (F : EdgeSet) r :=
    (forall x o, x \in D -> ~ (F x r o) /\ path F r x).
  
  (*

     If there is an edge from node x to node y:
     
               x -> y
               
     then both x and y are in the domain

   *)
  
  Definition confined (D : LibSet.set elem) (F : EdgeSet) :=
    forall x y o, F x y o -> x \in D /\ y \in D.

    (*

     For the moment, we are working with integers, 
     but this would work with any ordered type.

     It is a search tree, if we can be certain that 
     an element is or is not in the tree.

     Search for 3 in t:

               t            t
               |            |
               5            5  
              / \          / \
             3  7         2  7
 
            FOUND!      NOT FOUND!

   *)

  Definition searchtree (F : EdgeSet) (V : elem -> Z) :=
    (forall x y z, (F x y LEFT  /\ path F y z) -> (V x > V y)%Z /\ (V x > V z)%Z) /\
    (forall x y z, (F x y RIGHT /\ path F y z) -> (V x < V y)%Z /\ (V x < V z)%Z).

  (*

     Make sure that root R is belongs to domain.

   *)
  
  Definition rootisindomain (R : elem) (D : LibSet.set elem) := 
    R \in D.
  
  Definition positive_function (W : elem -> Z) := 
    forall e, (W e) > 0.

  (*

     The set R D F V is a binary search tree!

   *)
  
  Definition is_bst R D F V W :=
    (confined D F) /\
    (rootisindomain R D) /\ 
    (isroot D F R) /\
    (searchtree F V) /\
    (binarytree F) /\
    (finite D) /\
    (positive_function W).
  
  
  (*

     Create an invariant for the binary search tree, 
     * We can add other invariants here if needed.

   *)
  
  Record Inv R D F V W : Prop := {
    Inv_bst  : is_bst R D F V W
  }.

  (*
    
     If x belongs to the domain, then it will 
     map to a content, consequently, if x 
     has x1 and x2 has its childs, then the 
     content is a binary branch (NodeB) and 
     those nodes will also map to a content. 

                       x           
                       |
                   (NodeB kx x1 x2)
                             \   \
                             \ (NodeN kx2)
                             \
                       (NodeN kx1)
                        
   *)
  
  Definition Mem (D : LibSet.set elem)
             (F : elem -> elem -> orientation -> Prop)
             (V : elem -> Z) 
             (M : gmap elem content) : Prop :=
    forall x, x \in D ->
                    match M!!x with
                    | Some (NodeB v p1 p2) => F x p1 LEFT  /\ F x p2 RIGHT /\ V x = v
                    | Some (NodeL v p1) => F x p1 LEFT  /\ ¬(exists y, F x y RIGHT) /\ V x = v
                    | Some (NodeR v p2) => F x p2 RIGHT /\ ¬(exists y, F x y  LEFT) /\ V x = v
                    | Some (NodeN v) => ¬(exists y, F x y RIGHT) /\
                                        ¬(exists y, F x y  LEFT) /\ V x = v
                    | None => False
                    end.

  (*
    
     Val of content, maps a content type to a option physical 
     type (heap_lang value) content.

   *)
  
  Definition val_of_content (c : content) : option val :=
    match c with
    | NodeB k v1 v2 => Some (SOMEV(#k, (#v1,#v2)))
    | NodeL k v1 => Some (SOMEV(#k, (#v1,NONEV)))
    | NodeR k v2 => Some (SOMEV(#k, (NONEV,#v2)))
    | NodeN k => Some (SOMEV(#k, (NONEV,NONEV)))
    end.

  (*
    
     All physical content of each node belongs to a different
     part of the heap. 

          ____________________________________
         |   x1   |   x2   |   x3   |   x4   |    
         \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
           \          \          \          \
           \          \          \          \
         SOMEV   ∗  SOMEV   ∗  SOMEV   ∗  SOMEV

   *)

  Definition mapsto_M (M : gmap elem content) : iProp Σ :=
    ([∗ map] l ↦ c ∈ M, from_option (mapsto l 1) False (val_of_content c))%I.
  
  (*
    
     The splay tree (ST) predicate that we will 
     use in our proofs.

   *)
  
  Definition ST R D V W : iProp Σ :=
    (∃ F M,
        ⌜ Inv R D F V W ⌝ ∗
          ⌜ Mem D F V M ⌝ ∗
          mapsto_M M ).
  
  (*

     Hopefully, we will add here time credits and time receipts
     to prove the amortize time of the gcc splay tree algorithm!
    
   *)

End SplayTreePredicate.
