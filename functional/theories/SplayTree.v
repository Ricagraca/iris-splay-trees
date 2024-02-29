
(* Coq Libraries *)
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Orders.
Require Import FunInd.
Require Import Coq.Sorting.Sorted.
Require Import Coq.omega.Omega.
Import ListNotations.

(* My libraries *)
From ST Require Import XSet.
From ST Require Import ListTree.
From ST Require Import MyTactics.

Module SplayTree(o : OrderedType.OrderedType).

  Include XSet.OrderedSet(o).

  (** * Structural definition of tree with 
      ordered type elements.
  *)
  
  (* Structural definitions *)
  Inductive tree :=
  | L 
  | T (t1 : tree) (n : o.t) (t2 : tree).
  
  (* Add notation*)
  Include EqNotation(o).
  Include LtNotation(o).

  (* List functions : TODO not here *)
  Fixpoint ins_list (x : o.t) (l : list o.t) : list o.t := 
    match l with 
    | []   => [x]
    | a::h => if eq_dec x a then l
              else (if lt_dec x a then x :: l else a :: ins_list x h)
    end.

  Fixpoint del_list (x : o.t) (l : list o.t) : list o.t :=
    match l with
    | [] => []
    | a :: h => if eq_dec x a then h else a :: (del_list x h)
    end.                                    
  
  (** * Simple notation for trees. 
      - <| |> are leaves and 
      - <|t1 , n , t2 |> are nodes with value "n" and 
      with left "t1" and right "t2" child nodes.
  *)
  
  Notation " <| |> " := L.
  Notation " <| t1 , n , t2 |>  " := (T t1 n t2).

  (** * Functional implementation of the splay tree algorithm and other useful functions that will be used in following proofs.
   *)

  (** A size function that counts the number of nodes in tree 't' *)
  
  Fixpoint size (t : tree) : nat := 
    match t with 
    | <| |> => O
    | <| t1 , _, t2 |>  => size t1 + size t2 + 1
    end.

  (** An in order function that transforms tree 't' into a list. 
      If the tree is ordered, then it will produce an ordered list
   *)
  
  Fixpoint in_order (t : tree) : list o.t := 
    match t with 
    | <| |> => [ ] 
    | <| t1 , a, t2 |>  => (in_order t1) ++ [a] ++ (in_order t2)
    end.

  (** A set tree function that collects the elements of tree 't' into 
      a set.
   *)
  
  Fixpoint set_tree (t : tree)  : XSet.t := 
    match t with 
    | <| |> => XSet.empty
    | <| l, a, r |>   =>
      XSet.union
      (XSet.singleton a)
      (XSet.union (set_tree l) (set_tree r))
    end.

  (** The splay tree method, that given value 'a' and tree 't', 
      it produces a new tree with the value 'a' at its root,
      if 'a' was in tree 't'. Otherwise, 
      it produces a new tree with the closest 
      valued node to 'a' in its root.
   *)
  
  Fixpoint splay (a : o.t) (t : tree) : tree := 
    match t with 
    | <| |> => <| |>
    | <| cl , c, cr |> => 
      if eq_dec a c then <| cl , c, cr |>
      else if lt_dec a c 
           then match cl with 
                | <| |> => <| cl, c, cr |>
                | <| bl, b, br |> => 
                  if eq_dec a b then <| bl, b, <| br, c, cr |> |>
                  else if lt_dec a b 
                       then match splay a bl with 
                            | <| |> => <| bl, b, <| br, c, cr |> |>
                            | <| al, a', ar |> => <| al, a', <| ar, b, <| br, c, cr |> |> |>
                            end
                       else match splay a br with 
                            | <| |> =>  <| bl, b, <| br, c, cr |> |>
                            | <| al, a', ar |> => <| <| bl, b, al |> , a', <| ar, c, cr |> |>
                            end
                end
           else match cr with 
                | <| |> => <| cl, c, cr |>
                | <| bl, b, br |> => 
                  if eq_dec a b then <| <| cl, c, bl |>, b, br |>
                  else if lt_dec a b 
                       then match splay a bl with 
                            | <| |> => <| <| cl, c, bl |>, b, br |>
                            | <| al, a', ar |> => <| <| cl, c, al |>, a', <| ar, b, br |> |>
                            end
                       else match splay a br with 
                            | <| |> => <| <| cl, c, bl |>, b, br |>
                            | <| al, a', ar |> => <| <| <| cl, c, bl |>, b, al |> , a', ar |>
                            end
                end
    end.

  (** Is root predicate that is true whenever 
      element 'a' is in the root of tree 't'.
   *)
  
  Definition is_root (a : o.t) (t : tree) : Prop :=
    match t with
    | <| |> => False
    | <| l, a', r |>  => a' == a
    end.

  (** Is in predicate that is true whenever element 'a' is 
      in the tree. It applies the splay method to the tree in order
      to put it in its root.
   *)
  
  Definition isin (a : o.t) (t : tree) : Prop :=
    is_root a (splay a t).

  (** Simple empty predicate that tells when tree 't' is empty.
   *)
  
  Definition empty (t : tree) : Prop := 
    t = <| |>.

  (** The insert method, which creates a new tree
      with element 'a' at its root and the others as
      its descendants.
   *)
  
  Definition insert (a : o.t) (t : tree) : tree := 
    match splay a t with 
    |  <| |> => <| <| |>, a, <| |> |>
    |  <| l, a', r |>  => 
       if eq_dec a a' then <| l, a, r |> 
       else if lt_dec a a' then <| l, a, <| <|  |> , a', r |> |>
            else <| <| l , a', <|  |> |> , a, r |>
    end.

  (** The splay_max method splays the maximum element of tree 't'.
      We do not need to give any element, because we know which element 
      is the maximum, whenever the tree is ordered.
   *)

  Fixpoint splay_max (t : tree) : tree := 
    match t with 
    | <| |> => <| |>
    | <| l, b, <| |> |> => <| l, b, <| |> |>
    | <| l, b, <| rl, c, rr |> |> =>
      match splay_max rr with 
      | <| |> => <| <| l, b, rl |> , c, <| |> |>
      | <| rrl, x, xa |> => <| <| <| l, b, rl |> , c,  rrl |>, x , xa |>
      end
    end.

  (** The delete method, which produces a new tree 
      without element 'a' in it. If the tree doesn't
      have element 'a', it only applies the splay method
      without deleting anything.
   *)
  
  Definition delete (a : o.t) (t : tree) : tree := 
    match splay a t with 
    |  <| |> => <| |>
    |  <| l, a', r |>  => 
       if eq_dec a a' then 
         match splay_max l with 
         | <| |> => r
         | <| l', m, r' |>  => <| l', m, r |>
         end
       else
         <| l, a', r |>
  end.

  (** The binary search tree (bst) predicate.
      It gives True whenever tree 't' is ordered, i.e., 
      for a given node of a tree, its value must be higher
      than all of the descendant nodes to its left child and must be lower
      than all of the descendant nodes to its right.
   *)
  
  Fixpoint bst (t : tree) : Prop := 
    match t with 
    | <| |> => True
    | <| l, a, r |> => 
      let set_l := set_tree l in 
      let set_r := set_tree r in 
      (bst l) /\ (bst r) /\
      (XSet.For_all (fun n => n < a) (set_l) /\ XSet.For_all  (fun n => a < n) (set_r))
    end.

  (** The equal tree predicate, which is true whenever two 
      trees, 't1' and 't2' are the same semantically, i.e., 
      we have a1 == a2 for all nodes. NOTE that the sematical predicate (==) is not the 
      same as the syntatical predicate (=).
   *)
  
  Fixpoint eq_tree (t1 t2 : tree) : Prop := 
    match t1,t2 with 
    | <| |>, <| |> => True
    | <| l1, a1, r1 |>, <| l2, a2, r2 |> => 
      let eq_l := eq_tree l1 l2 in 
      let eq_r := eq_tree r1 r2 in 
      eq_l /\ eq_r /\ (a1 == a2)
    | _,_ => False
    end.
  
  Functional Scheme splay_ind := Induction for splay Sort Prop.
  Functional Scheme insert_ind := Induction for insert Sort Prop.
  Functional Scheme delete_ind := Induction for delete Sort Prop.
  Functional Scheme splay_max_ind := Induction for splay_max Sort Prop.

  (** * Lemmas and theorems for the splay tree implementation
   *)

  (** A singleton is a binary search tree.
   *)
  
  (* 1.0 My own theorems  *)
  Lemma bst_el : forall e,
      bst <| <| |> , e, <| |> |>.
  Proof.
    intros.
    simpl.
    repeat try (split || apply I || unfold XSet.For_all || intros || inversion H).
  Qed.

  (** If two elements "e" and "e'" are semantically equal, 
      and we trade "e" with "e'" in a binary search tree, 
      then the tree will remain ordered, i.e., it will still 
      be a binary search tree.
   *)

  Lemma bst_eq_root : forall l r e e',
      e == e' -> bst <| l , e , r |> ->
      bst <| l , e' , r |>.                                
  Proof.
    logical_reduction ; unfold XSet.For_all in * ; intros.
    - assert (x < e -> x < e'). order. apply H5.
      apply H2.  assumption.
    - assert (e < x -> e' < x). order. apply H5.
      apply H3.  assumption.
  Qed.

  (** Splaying value 'a' that it is in the root of 
      the tree produces the same tree.
   *)
  
  Lemma splay_of_root : forall l a r,
      splay a <| l , a, r |> = <| l , a, r |>.                      
  Proof.
    intros. 
    simpl ; destruct eq_dec ; [reflexivity|] ;
    unfold not in n ; exfalso ; apply n ; reflexivity.
  Qed.

  (** If value 'a' is in the root of the tree, 
      then 'a' belongs to the set of elements of the tree.
   *)
  
  Lemma set_el_in_root : forall a l r,
     XSet.In a (set_tree <| l, a, r |> ).
  Proof.
    intros ; simpl ;
    set_reduction ;
    left ; set_reduction.
  Qed.
  
  Lemma set_equal_in : forall a b l r t,  
      b == a -> 
      XSet.In a (set_tree <| l, a, r |> ) <-> XSet.In a (set_tree t) ->
      XSet.In b (set_tree t).
  Proof.
    intros a b l r t H H1 ; symmetry in H ;
    specialize (set_el_in_root a l r) as H' ;
    apply H1 in H' ;
    specialize (set_eq_in_spec a b (set_tree t) H) as H'' ;
    apply H'' in H' ; assumption.
  Qed.

  (** If "a" is in tree <| l , a' , r |> is equivalent to proposition P, then 
      we have 
      - if "a" is in "l" then P
      - if "a" is in "r" then P
      - if "a" is equal to "a'" then P
   *)

  Lemma set_tree_in_equiv_and : forall a a' l r P,
      XSet.In a (set_tree <| l, a', r |> ) <-> P ->
      (XSet.In a (set_tree l) -> P) /\ (XSet.In a (set_tree r) -> P) /\ (a == a' -> P).
  Proof.
    intros ;
    simpl in H ; repeat split ; intro H' ; apply H ; set_reduction ;
    repeat (left + right + set_reduction) ; assumption.
  Qed.

  (** Set of tree "t" is equal to the set of elements
      transformed into a list.
   *)

  Lemma equal_set_list_set_tree : forall t,
      XSet.Equal (set_list (in_order t)) (set_tree t).
  Proof.
    intro t.
    induction t ; split ; intro H ; simpl.
    + inversion H.
    + inversion H.
    + logical_reduction. apply set_in_app_or_spec in H.
      logical_reduction.
    - set_reduction. right. set_reduction. left. apply IHt1. assumption.
    - set_reduction. logical_reduction. left. set_reduction. assumption.
      right. set_reduction. right. apply IHt2. assumption.
      + logical_reduction. apply set_in_app_or_spec. set_reduction.
        logical_reduction. right. set_reduction. left.
        order. set_reduction. logical_reduction. left. apply IHt1.
        assumption. right. set_reduction. right. apply IHt2.
        assumption.
  Qed.

  
  (** Splaying a tree that has at least a node cannot 
      be equal to a leaf.
   *)
  
  (* 1.2 Functional Correctness Proofs I*)
  Lemma splay_node_not_nil : forall a t1 n t2,
      splay a <| t1, n, t2 |> <> <| |>.
  Proof.
    intros a t1 n t2 ; unfold not ; simpl ;
    destruct eq_dec ; intro ; inversion H ;
      destruct lt_dec ; destruct t1 ; destruct t2 ;
        try destruct eq_dec ; try inversion H ;
          try destruct lt_dec ; try destruct (splay a t1_1) ;
            try destruct (splay a t1_2) ;  try destruct (splay a t2_1) ;
               try destruct (splay a t2_2) ; try inversion H.
  Qed.

  (** Splaying a tree results in a leaf iff 
      the tree is a leaf itself.
   *)
  
  Theorem splay_leaf_iff : forall a t,
      splay a t = <| |> <-> t = <| |>.
  Proof.
    intros a t ;
    split ; intro H ; [| rewrite H ; reflexivity ] ;
    destruct t ; [reflexivity|] ;
    apply splay_node_not_nil in H ; contradiction.
  Qed.

  (** Using the splay_max on a tree results in a leaf iff
      the tree is a leaf itself.
   *)
  
  Theorem splay_max_leaf_iff : forall t,
      splay_max t = <| |> <-> (t = <| |>).
  Proof.
    intros t ;
    split ; intro H ; [| rewrite H ; reflexivity] ;
    destruct t ; [reflexivity|] ;
    simpl in H ; destruct t2 ; [inversion H|] ;
    destruct (splay_max t2_2) ; [inversion H|] ;
    inversion H.
  Qed.

  
  (** If "t1" and "t2" are semantically equal, 
      and "x" is in "t1" then "x" is also in "t2".
   *)
  
  Theorem eq_tree_in : forall t1 t2 x,
      eq_tree t1 t2 ->
      XSet.In x (set_tree t1) ->
      XSet.In x (set_tree t2).
  Proof.
    induction t1 ; intros ; simpl in *.
    + inversion H0.
    + destruct t2.
      - contradiction.
      - set_reduction. logical_reduction.
        * set_reduction. left. rewrite XSet.singleton_spec.
          order.
        * set_reduction. logical_reduction ; right ; set_reduction.
          { left. apply IHt1_1 ; auto. }
          { right. apply IHt1_2 ; auto. }
  Qed.

  
  (** If "t1" and "t2" are semantically equal, 
      they have the same set of elements.
   *)

  Theorem eq_tree_eq_set : forall t1 t2,
      eq_tree t1 t2 ->
      XSet.Equal (set_tree t1) (set_tree t2).       
  Proof.
    induction t1 ; unfold XSet.Equal ; intros ; simpl in *.
    + split ; destruct t2 ; simpl ; set_reduction ; logical_reduction.
    + split ; destruct t2 ; simpl ; logical_reduction ;
      apply IHt1_1 in H ; apply IHt1_2 in H1 ; 
      set_reduction ; logical_reduction ; set_reduction ;
        logical_reduction ; repeat (left + right) ;
          set_reduction ; try order ;
            repeat (left + right) ; try apply H ;
              try apply H1 ; assumption.
  Qed.

  (** The semantical predicate eq_tree is reflexive.
   *)

  Theorem eq_tree_refl : forall t,
      eq_tree t t.
  Proof.
    intros t. induction t.
    + reflexivity.
    + simpl. split ; try split ; try assumption. reflexivity.
  Qed.
  
  (** If two trees are syntatically the same, then they are 
      also semantically the same, because a = b -> a == b.
   *)
  
  Theorem tree_syntatic_semantic : forall t1 t2,
      t1 = t2 -> eq_tree t1 t2.
  Proof.
    intros.
    rewrite H. apply eq_tree_refl.
  Qed.
  
  (** The semantical predicate eq_tree is symmetric.
   *)
  
  Theorem eq_tree_symm : forall t1 t2,
      eq_tree t1 t2 -> eq_tree t2 t1.
  Proof.
    intros t1.
    induction t1.
    + simpl in *. destruct t2 ; auto.
    + intros ; simpl. destruct t2.
      - inversion H.
      - inversion H. unfold eq_tree in H. logical_reduction. order.
  Qed.
  
  (** The semantical predicate eq_tree is transitive.
   *)

  Theorem eq_tree_trans : forall t1 t2 t3,
      eq_tree t1 t2 -> eq_tree t2 t3 -> eq_tree t1 t3.
  Proof.
    intros t1.
    induction t1.
    + simpl in *. destruct t2 ; destruct t3 ; auto.
    + intros ; simpl. destruct t2 ; destruct t3 ; auto.
      - inversion H.
      - unfold eq_tree in H. logical_reduction. order.
  Qed.

  
  (** The size of a tree is the same as the 
      size of the tree after being splayed.
   *)
  
  (* 1.3 Functional Correctness Proofs II *)
  Lemma size_splay : forall t a,
      size (splay a t) = size t.                      
  Proof.
    intros t a ;
      functional induction (splay a t) using splay_ind ; simpl ;
        try (rewrite e5 in IHt0 ; rewrite <- IHt0) ; simpl ;
           try reflexivity ; omega.
  Qed.
  
  (** If "t1" and "t2" are semantically the same, then 
      their size is also the same.
   *)

  Lemma size_eq_tree : forall t1 t2,
      eq_tree t1 t2 -> size t1 = size t2.
  Proof.
    intros t1.
    induction t1.
    + intros. destruct t2. auto. inversion H.
    + intros. destruct t2 ; logical_reduction ; contradiction.
  Qed.  

  (** If splaying a tree "t" results in "<| l, u, r |>" then 
      the size of "t" (size t) is the same as the sum of the size of the splayed
      trees children "l" and "r" plus 1 ( size l + size r + 1 ).
   *)
  
  Lemma size_if_splay : forall a t l u r,
      eq_tree (splay a t) <| l, u, r |> -> size t = size l + size r + 1.
  Proof.
    intros a t.
    functional induction (splay a t) using splay_ind ; simpl ; intros ;
      logical_reduction ; try contradiction ; try destruct l ;
        try destruct r ; try destruct r2 ; try destruct l1 ; logical_reduction ;  
          try apply size_eq_tree in H ; try apply size_eq_tree in H0 ;
            try apply size_eq_tree in H2 ; try apply size_eq_tree in H4 ;
              logical_reduction ; try contradiction ;
                try (rewrite e5 in IHt0 ; specialize (eq_tree_refl (<| al, a', ar |> )) as refl ;
                  apply IHt0 in refl) ; try omega.
  Qed.

  (** If "t" is not a leaf, then there exists a node "<| l, x, r |>"
      that corresponds to "t" after being splayed.
   *)

  Lemma splay_not_leaf : forall (t:tree) a,
      t <> <| |> -> exists l x r, splay a t = <| l, x, r |>.
  Proof.
    intros t a.
    destruct t.
    + contradiction.
    + intros ; simpl ;
        destruct eq_dec ; try destruct lt_dec ;
          try destruct t1 ; try destruct t2 ;
            try destruct eq_dec ; try destruct lt_dec ;
              try destruct (splay a t1_1) ; try destruct (splay a t1_2) ;
                try destruct (splay a t2_1) ; try destruct (splay a t2_2) ;
                  eauto.      
  Qed.
  
  (** The set of elements of "t" are the same as the elements of the 
      tree afeter being splayed *)
  
  Lemma set_splay : forall a t,
      XSet.Equal (set_tree (splay a t)) (set_tree t).
  Proof.
    intros a t.
    functional induction (splay a t) using splay_ind ; simpl ; 
      logical_reduction ; set_reduction ; unfold XSet.Equal ;
        split ; intro H;
          repeat try ((set_reduction || logical_reduction || assumption)) ;
            unfold XSet.Equal in * ; 
              try (repeat (left + right + set_reduction) ;
                tryif reflexivity then idtac else assumption ) ;
                  try (rewrite e5 in IHt0 ;
                    try (apply IHt0 in H ; simpl in H) ;
                      repeat (set_reduction ; logical_reduction) ;
                        repeat (left + right + set_reduction +  apply IHt0) ;
                          tryif reflexivity then idtac else assumption).
  Qed.

  (** ** Tactic tree_reduction that simplifies some of the hypothesis 
        of the next theorems/lemmas *)
  
  (* Tree tactic reduction *)
  Ltac tree_reduction :=
    match goal with
    | h : _ |- 
      eq_tree ?t ?t => apply eq_tree_refl
    | h1 : ?e == ?e', h2 : bst <| ?l , ?e , ?r |> |- 
      bst <| ?l , ?e' , ?r |> =>
      apply (bst_eq_root l r e e' h1 h2)
    | h :_ |- bst <| <| |>, ?a, <| |> |> => apply bst_el 
    | h : splay ?a ?bl = <| |> |- _ =>
      apply splay_leaf_iff in h ; subst ; tree_reduction
    | h :  <| ?a, ?b, ?c|> = <| ?d, ?e, ?f |> |- _ =>
      inversion h ; subst                                                
    | h1 : splay ?a ?bl = <| ?al, ?a', ?ar |>, h2 : bst (splay ?a ?bl) |- _ =>
      rewrite h1 in h2 ; simpl in h2 ; tree_reduction                                
    | h : splay ?a ?bl = <| ?al, ?a', ?ar |> |- _ =>
      rewrite h in * ;
      try (specialize (set_splay a bl) as set_splay_reduct) ; tree_reduction
    | h : bst <| ?al, ?a', ?ar |> |- _ =>
      simpl in h ; tree_reduction
    | h : XSet.In ?a (set_tree <| ?al, ?a', ?ar |>) |- _ =>
      simpl in h ; tree_reduction                   
    | h : XSet.In ?a (set_tree <| |>) |- _ =>
      inversion h
    | h : splay_max ?t = <| |> |- _ =>
      rewrite splay_max_leaf_iff in h ; tree_reduction
    | h : splay_max ?t = <| |> |- _ =>
      rewrite splay_max_leaf_iff in h ; tree_reduction
    | h1 : eq_tree ?t1 ?t2, h2 : XSet.In ?x (set_tree ?t1) |-
      XSet.In ?x (set_tree ?t2) =>
      apply (eq_tree_in t1 t2 x h1 h2)
    | _ => idtac
    end.

  (** If "t" is a binary search tree and after splaying it with value "a" results in 
      <| l, e, r |>, then all values of elements of tree "l" 
      are lower than "a" *)

  Lemma splay_bstL : forall t a l e r x,
      bst t -> eq_tree (splay a t) <| l, e, r |> -> XSet.In x (set_tree l) -> x < a.
  Proof.
    intros t a.
    functional induction (splay a t) using splay_ind ; simpl ;
      try (apply splay_leaf_iff in e5) ; intros ; 
        logical_reduction.
    + apply eq_tree_symm in H0 as H0'. specialize (eq_tree_in l cl x H0' H1) as H'.
      apply H5 in H'. order.
    + destruct l ; try contradiction. inversion H1.
    + apply eq_tree_symm in H0 as H0'. specialize (eq_tree_in l bl x H0' H1) as H'.
      apply H8 in H'. order.
    + destruct l ; try contradiction. inversion H1.
    + rewrite e5 in IHt0. specialize (IHt0 al a' ar x H).
      apply IHt0 ; [apply eq_tree_refl|]. apply (eq_tree_eq_set al l) in H0.
      apply H0 in H1. assumption.
    + apply (eq_tree_eq_set bl l) in H0.
      apply H0 in H1. apply H5 in H1. order.
    + destruct l ; try contradiction. logical_reduction.
      set_reduction. logical_reduction ; set_reduction ; logical_reduction.
    - order.
    - apply (eq_tree_eq_set bl l1) in H0. apply H0 in H1.
      apply H8 in H1. order.
    - rewrite e5 in IHt0. specialize (IHt0 al a' ar x H7).
      apply IHt0 ; [apply eq_tree_refl|]. 
      apply (eq_tree_eq_set al l2) in H10. apply H10 in H1.
      assumption.
      + apply eq_tree_symm in H0 as H0'. specialize (eq_tree_in l cl x H0' H1) as H'.
        apply H4 in H'. order.
      + destruct l ; try contradiction. logical_reduction.
        set_reduction. logical_reduction ; set_reduction ; logical_reduction.
    - order.
    - apply (eq_tree_eq_set cl l1) in H0. apply H0 in H1.
      apply H5 in H1. order.
    - apply (eq_tree_eq_set bl l2) in H10. apply H10 in H1.
      apply H8 in H1. order.      
      + destruct l ; try contradiction. logical_reduction.
        set_reduction. logical_reduction ; set_reduction ; logical_reduction.
    - order.
    - apply (eq_tree_eq_set cl l1) in H0. apply H0 in H1.
      apply H3 in H1. order.
    - destruct l2 ; try contradiction.
      inversion H1.
      + destruct l ; try contradiction. logical_reduction.
        set_reduction. logical_reduction ; set_reduction ; logical_reduction.
    - order.
    - apply (eq_tree_eq_set cl l1) in H0. apply H0 in H1.
      apply H5 in H1. order.
    - rewrite e5 in IHt0. specialize (IHt0 al a' ar x H4).
      apply IHt0 ; [apply eq_tree_refl|].
      apply eq_tree_symm in H10 as H10'.
      apply (eq_tree_in l2 al x H10' H1).
      + destruct l ; try contradiction. logical_reduction.
        set_reduction. logical_reduction ; set_reduction ; logical_reduction.
    - order.
    - apply (eq_tree_eq_set cl l1) in H0. apply H0 in H1.
      apply H3 in H1. order.
    - apply (eq_tree_eq_set bl l2) in H9. apply H9 in H1.
      apply H5 in H1. order.
      + destruct l ; try contradiction. logical_reduction.
        destruct l1 ; try contradiction.
        set_reduction ; logical_reduction ;
          set_reduction ; logical_reduction ; set_reduction ; logical_reduction ;
            set_reduction ; logical_reduction ; try order.
    - apply eq_tree_symm in H0 as H0'.
      apply (eq_tree_eq_set cl l1_1) in H0. apply H0 in H1.
      apply H5 in H1. order.
    - apply eq_tree_symm in H12 as H12'.
      apply (eq_tree_eq_set bl l1_2) in H12. apply H12 in H1.
      apply H8 in H1. order.
    - apply eq_tree_symm in H2 as H2'.
      apply (eq_tree_eq_set al l2) in H10. apply H10 in H1.
      rewrite e5 in IHt0. specialize (IHt0 al a' ar x H7).
      apply IHt0 ; [apply eq_tree_refl|]. assumption.
  Qed.
  
  Lemma splay_bstL' : forall t a l e r x,
      bst t -> (splay a t) = <| l, e, r |> -> XSet.In x (set_tree l) -> x < a.
  Proof.
    intros.
    apply tree_syntatic_semantic in H0.
    apply (splay_bstL t0 a l e r x H H0 H1).
  Qed.
  
  (** If "t" is a binary search tree and after splaying it with value "a" results in 
      <| l, e, r |>, then all values of elements of tree "r" 
      are higher than "a" *)
  
  Lemma splay_bstR : forall t a l e r x,
      bst t -> eq_tree (splay a t) <| l, e, r |> -> XSet.In x (set_tree r) -> a < x.
  Proof.
    intros t a.
    functional induction (splay a t) using splay_ind ; simpl ;
      try (apply splay_leaf_iff in e5) ; intros ; 
        logical_reduction.
    + apply eq_tree_symm in H2 as H2'. specialize (eq_tree_in r cr x H2' H1) as H'.
      apply H6 in H'. order.
    + apply (eq_tree_eq_set cr r) in H2. apply H2 in H1.                                                       
      apply H5 in H1. order.
    + destruct r ; try contradiction. logical_reduction.
      set_reduction. logical_reduction ; set_reduction ; logical_reduction.
      - order.
      - apply (eq_tree_eq_set br r1) in H2. apply H2 in H1.
        apply H9 in H1. order.
      - apply (eq_tree_eq_set cr r2) in H10. apply H10 in H1.
        apply H6 in H1. order.
    + destruct r ; try contradiction. logical_reduction.
      set_reduction. logical_reduction ; set_reduction ; logical_reduction.
      - order.
      - apply (eq_tree_eq_set br r1) in H7. apply H7 in H1.
        apply H6 in H1. order.
      - apply (eq_tree_eq_set cr r2) in H9. apply H9 in H1.
        apply H4 in H1. order.
    + destruct r ; try contradiction. logical_reduction.
      set_reduction. logical_reduction ; set_reduction ; logical_reduction.
      - order.
      - apply (eq_tree_eq_set ar r1) in H2. apply H2 in H1.
        rewrite e5 in IHt0. specialize (IHt0 al a' ar x H).
        apply IHt0 ; [apply eq_tree_refl|]. assumption.
      - destruct r2 ; try contradiction. logical_reduction.
        set_reduction. logical_reduction ; set_reduction ; logical_reduction.
        * order.
        * apply eq_tree_eq_set in H10. apply H10 in H1. apply H9 in H1.
          order.
        * apply eq_tree_eq_set in H14. apply H14 in H1. apply H6 in H1.
          order.
    + destruct r ; try contradiction ; destruct r1 ; try contradiction ;
      logical_reduction ; set_reduction ; logical_reduction ; set_reduction ;
      logical_reduction.
      - order.
      - inversion H1.
      - apply eq_tree_eq_set in H7. apply H7 in H1.
        apply H4 in H1. order.
    + destruct r ; try contradiction. destruct l ; try contradiction ;
      logical_reduction ; set_reduction ; logical_reduction ; set_reduction ;
      logical_reduction.
      - order.
      - apply eq_tree_eq_set in H2. apply H2 in H1.
        rewrite e5 in IHt0. specialize (IHt0 al a' ar x H7).
        apply IHt0 ; [apply eq_tree_refl|]. assumption.
      - apply eq_tree_eq_set in H10. apply H10 in H1.
        apply H6 in H1. order.
    + destruct r ; try contradiction. inversion H1.
    + apply eq_tree_eq_set in H2. apply H2 in H1.
      apply H9 in H1. order.
    + destruct l ; try contradiction. destruct l2 ; try contradiction ; logical_reduction.
      apply eq_tree_eq_set in H7. apply H7 in H1. apply H6 in H1. order.
    + destruct r, l ; try contradiction. logical_reduction.
      set_reduction ; logical_reduction ; set_reduction ; logical_reduction.
      - order.
      - apply eq_tree_eq_set in H2. apply H2 in H1.
        rewrite e5 in IHt0.
        apply (IHt0 al a' ar x H4) ; [apply eq_tree_refl|assumption].
      - apply eq_tree_eq_set in H10. apply H10 in H1. apply H9 in H1.
        order.
    + destruct r ; try contradiction. inversion H1.
    + rewrite e5 in IHt0. apply eq_tree_eq_set in H2. apply H2 in H1. 
      apply (IHt0 al a' ar x H7) ; [apply eq_tree_refl|assumption].
  Qed.

  Lemma splay_bstR' : forall t a l e r x,
      bst t -> (splay a t) = <| l, e, r |> -> XSet.In x (set_tree r) -> a < x.
  Proof.
    intros.
    apply tree_syntatic_semantic in H0.
    apply (splay_bstR t0 a l e r x H H0 H1).
  Qed.

  (** If "t" is a binary search tree, then splaying it also results
      in a binary search tree. *)
  
  Theorem bst_splay : forall a t, 
      bst t -> bst (splay a t).
  Proof.
    intros a t ;
      functional induction (splay a t) using splay_ind ;
      intro ; simpl in H ; simpl ; auto ; unfold XSet.For_all ; intros ; tree_reduction ; 
        repeat try (order || logical_reduction || set_reduction || logical_reduction || set_create ).
  Qed.

  (** If "t" is a binary search tree and if "t'" is the result of splaying "t", 
      then "a" is in "t" iff exists "l" and "r" where "t'" is equal to "< | l , a , r | > "
      (where "a" is in the root of the splayed tree). *)

  Theorem splay_to_root : forall t a t',
      bst t -> eq_tree (splay a t) t' ->
      (XSet.In a (set_tree t) <->  (exists l r, eq_tree t' <| l, a, r |>)).
  Proof.
    intros t a ; functional induction (insert a t) using insert_ind ; tree_reduction ; simpl ; intros.
    + split ; intros.
      - logical_reduction. set_reduction.
      - logical_reduction. destruct t' ; [inversion H|contradiction].
    + destruct t' ; [contradiction|]. split ; intros.
      - exists l, r.
        logical_reduction ; apply eq_tree_symm in H0 ;
          apply eq_tree_symm in H2 ; try assumption ; order.
      - apply set_splay_reduct. do 2 destruct H1.
        logical_reduction. set_reduction. left.
        set_reduction. order.
    + split ; intros.
      - apply set_splay_reduct in H1. simpl in H1.
        set_reduction. logical_reduction.
        * set_reduction. order.
        * set_reduction. logical_reduction.
        { specialize (splay_bstL t a l a' r) as H'.
          specialize (H' a H). rewrite e in H'.
          assert (a < a). apply H' ; try assumption ;
          try apply eq_tree_refl. order.          
        }
        { specialize (splay_bstR t a l a' r) as H'.
          specialize (H' a H). rewrite e in H'.
          assert (a < a). apply H' ; try assumption ;
          try apply eq_tree_refl. order.   
        }
      - destruct t' ; try contradiction.
        logical_reduction. apply set_splay_reduct.
        set_reduction. left.      
        set_reduction. order.
  + destruct t' ; try contradiction ; logical_reduction. split ; intros.
    - apply set_splay_reduct in H3.
      set_reduction. logical_reduction ; set_reduction ; logical_reduction.
      * order. 
      * specialize (splay_bstL t a l a' r) as H'.
        specialize (H' a H). rewrite e in H'.
        assert (a < a). apply H' ; try assumption ;
                          try apply eq_tree_refl. order.
      * specialize (splay_bstR t a l a' r) as H'.
        specialize (H' a H). rewrite e in H'.
        assert (a < a). apply H' ; try assumption ;
                          try apply eq_tree_refl. order.
    - logical_reduction. logical_reduction.
      specialize (set_splay a t) as H'. rewrite e in H'.
      logical_reduction. apply H'.
      set_reduction. left. set_reduction. order. 
  Qed.

  (** If "t" is a binary search tree, "a" is in the root of "(splay a t)" iff 
   "a" is in tree "t" *)
  
  (* 1.3.1 Verification of is_in *)
  Lemma is_root_splay : forall t a,
      bst t -> 
      (is_root a (splay a t) <-> XSet.In a (set_tree t)).
  Proof.
    intros t a ; functional induction (insert a t) using insert_ind ; tree_reduction ;
      try order ; simpl ; intros ; try rewrite e in H' ; try order.
    + rewrite set_in_empty_false_spec. split ; auto.
    + subst. split ; intros ; try order.
      apply set_splay_reduct. simpl. set_reduction. left ; set_reduction.
      order.
    + split ; try order.
      intro. apply set_splay_reduct in H0. logical_reduction. set_reduction.
      logical_reduction ; set_reduction ; logical_reduction ; try order.
      - specialize (splay_bstL t a l a' r) as H'.
        specialize (H' a H). rewrite e in H'.
        assert ( a < a ). apply H' ; try apply eq_tree_refl ; auto.
        order.
      - specialize (splay_bstR t a l a' r) as H'.
        specialize (H' a H).
        rewrite e in H'. assert ( a < a ).
        apply H' ; try assumption ; try apply eq_tree_refl. order. 
    + split ; intros ; try order.
      apply set_splay_reduct in H0. simpl in H0.
      set_reduction.  logical_reduction ; set_reduction ; try order ;
      logical_reduction.
      - specialize (splay_bstL t a l a' r) as H'.
        specialize (H' a H).
        rewrite e in H'. assert ( a < a ).
        apply H' ; try assumption ; try apply eq_tree_refl. order.
      - specialize (splay_bstR t a l a' r) as H'.
        specialize (H' a H). rewrite e in H'. assert ( a < a ).
        apply H' ; try assumption ; try apply eq_tree_refl. order. 
  Qed.

  (** The set of elements of tree "t" after inserting element "a" is the 
      same as the union of the singleton element "a" with the set of elements of "t". *)  

  (* 1.3.2 Verification of insert *)
  Lemma set_insert : forall a t,
      XSet.Equal (set_tree (insert a t)) (XSet.union (XSet.singleton a) (set_tree t)). 
  Proof.  
    intros a t ; functional induction (insert a t) using insert_ind ; tree_reduction ;
      try order.
    + simpl. set_reduction. rewrite set_union_empty_spec. set_reduction.
    + logical_reduction. unfold XSet.Equal in *.
      intros.
      specialize (set_splay a t) as H'.
      rewrite e in H'. unfold XSet.Equal in *.
      split ; intros ; set_reduction ; logical_reduction.
    - right. apply H'. set_reduction. logical_reduction.
      * right. set_reduction. left. assumption.
      * right. set_reduction. right. assumption.
    - apply H' in H. set_reduction. logical_reduction.
      left. set_reduction. order.
    + logical_reduction. unfold XSet.Equal in *.
      intros.
      specialize (set_splay a t) as H'.
      rewrite e in H'. unfold XSet.Equal in *.
      split ; intros ; set_reduction ; logical_reduction.
    - right. apply H'. set_reduction. logical_reduction ; set_reduction ;
      logical_reduction ; set_reduction ; logical_reduction.      
      * right. set_reduction. left. assumption.
      * set_reduction. 
      * right. set_reduction. right. assumption.
    - right. set_reduction. apply H' in H.
      set_reduction. logical_reduction ; set_reduction ; logical_reduction.
      * right. set_reduction. left. set_reduction. order.
      * right. set_reduction. right. set_reduction. right. assumption.
    + logical_reduction. unfold XSet.Equal in *.
      intros.
      specialize (set_splay a t) as H'.
      rewrite e in H'. unfold XSet.Equal in *.
      split ; intros ; set_reduction ; logical_reduction.
    - right. apply H'. set_reduction. logical_reduction ; set_reduction ;
      logical_reduction ; set_reduction ; logical_reduction.      
      * right. set_reduction. left. assumption.
      * set_reduction. 
      * right. set_reduction. right. assumption.
    - right. set_reduction. apply H' in H.
      set_reduction. logical_reduction ; set_reduction ; logical_reduction.
      * left. set_reduction. left. set_reduction. order.
      * left. set_reduction. right. set_reduction. left. assumption.
  Qed.

  (** If "t" is a binary search tree, inserting "a" in tree "t" results in 
      a binary search tree as well.*)
  
  Lemma bst_insert : forall a t,
      bst t -> bst (insert a t).
  Proof.
    intros a t ; functional induction (insert a t) using insert_ind ; intro ; try order.
    + tree_reduction.
    + subst. apply (bst_splay a) in H.
      rewrite e in H. clear e0. symmetry in _x. tree_reduction. 
    + assert (H' := H).
      apply (bst_splay a) in H.
      rewrite e in H ; logical_reduction.
    - set_reduction.
    - specialize (splay_bstL t a l a' r) as H''.
      unfold XSet.For_all ; intros. rewrite e in *.
      specialize (H'' x H'). apply H'';
      [apply eq_tree_refl|assumption].
    - set_reduction. logical_reduction ; set_reduction.
      * assumption.
      * logical_reduction ; set_reduction ; set_create.
      + assert (H' := H).
        apply (bst_splay a) in H.
        rewrite e in H ; logical_reduction.
    - set_reduction.
    - set_reduction. logical_reduction ; set_reduction.
      * order.
      * logical_reduction ; set_reduction ; set_create.
        unfold XSet.For_all in *. intros. assert (x < a' -> x < a).
        order. apply H4. apply H1. assumption.
    - specialize (splay_bstR t a l a' r) as H''.
      unfold XSet.For_all ; intros.
      specialize (H'' x H'). rewrite e in H''.
      unfold XSet.For_all in *. apply H'' ;
      [apply eq_tree_refl|assumption].
  Qed.


  (** The size of tree "t" is the same as the size of tree "t" after 
      applying splay max in it.*)
  
  (* 1.3.3 Verification of splay-max *)
  Lemma size_splay_max : forall t,
      size (splay_max t) = size t.
  Proof.     
    intros t.
    functional induction (splay_max t) using splay_max_ind ; simpl ; try reflexivity.
    + apply (splay_max_leaf_iff rr) in e1. rewrite e1. simpl. omega.
    + rewrite e1 in IHt0. simpl in IHt0. rewrite <- IHt0. omega.
  Qed.

  (** If splay maxing "t" results in "<| l, u, r |>" then the
      size of "t" is equal to the sum of the size of "l" and "r" plus 1 
      (size of u).
   *)

  Lemma size_if_splay_max : forall t l u r,
      splay_max t = <| l, u, r |> -> size t = size l + size r + 1.
  Proof.
    intros t l u r H ; simpl. specialize (size_splay_max t).
    intro H'. rewrite H in H' ; simpl in H'.
    auto.
  Qed.  

  (** The set of elements of "t" is equal to the set of elements of "t"
      after splay maxing it.
   *)
  
  Lemma set_splay_max : forall t,
      XSet.Equal (set_tree (splay_max t)) (set_tree t).
  Proof.
    intros t.
    functional induction (splay_max t) using splay_max_ind ; simpl ; try order ; 
      logical_reduction ; set_reduction ; unfold XSet.Equal ; split ; intro H;
        repeat try (set_reduction || logical_reduction || assumption).
    - right. set_reduction. right. set_reduction. left ; set_reduction. order.
    - right. set_reduction. left. assumption.
    -  right. set_reduction. right. set_reduction. right. set_reduction. left ; assumption.
    - right. set_reduction ; left. set_reduction. left. set_reduction. order.
    - right. set_reduction. left. set_reduction. right. set_reduction. left. assumption.
    - right. set_reduction. left. set_reduction. right. set_reduction. right. assumption.
    - tree_reduction. subst. tree_reduction.
    - right. set_reduction. right. set_reduction. right. set_reduction. right.
      apply IHt0. rewrite e1. simpl. set_reduction. left ; set_reduction ; order.
    - right. set_reduction. right. set_reduction. left. set_reduction ; order.
    - right. set_reduction. left. assumption.
    - right. set_reduction. right. set_reduction. right. set_reduction.
      left ; assumption.
    - right. set_reduction. right. set_reduction. right. set_reduction.
      right. apply IHt0. rewrite e1 in *. logical_reduction. set_reduction. 
      right. set_reduction. left ; assumption.
    - right. set_reduction. right. set_reduction. right. set_reduction. right.
      apply IHt0. rewrite e1. simpl. set_reduction. right. set_reduction.
      right. assumption.
    - right. set_reduction. left. set_reduction. right. set_reduction. left.
      set_reduction. left. set_reduction ; order.
    - right. set_reduction. left. set_reduction. right. set_reduction.
      left. set_reduction. right. set_reduction. left ; assumption.
    - right. set_reduction. left. set_reduction. left ; set_reduction ; order.
    - right. set_reduction. left. set_reduction. right. set_reduction. left.
      set_reduction. right. set_reduction. right. assumption.
    - apply IHt0 in H. rewrite e1 in H.
      logical_reduction. set_reduction. logical_reduction. set_reduction. logical_reduction.
      + right. set_reduction. left. set_reduction. right. set_reduction. right.
        assumption.
      + set_reduction. right. set_reduction. right. assumption.
  Qed.

  (** If "t" is a binary search tree, then splay maxing it results in 
      a binary search tree as well. (invariant of bst).
   *)
  
  Lemma bst_splay_max : forall t,
      bst t -> bst (splay_max t).
  Proof.
    intros t.
    functional induction (splay_max t) using splay_max_ind.
    - auto.
    - intro ; assumption.
    - intros. logical_reduction ; set_reduction ; logical_reduction ; set_reduction. 
      + logical_reduction.
      + assumption.
      + logical_reduction. unfold XSet.For_all. intros.
        apply H1 in H8. order.
    - logical_reduction ; apply IHt0 in H3 ; rewrite e1 in H3 ; logical_reduction ;
        set_reduction ; logical_reduction ; set_reduction ;
          logical_reduction ; set_reduction ; set_create.
      + unfold XSet.For_all. intros. apply H1 in H11. order.
      + unfold XSet.For_all. intros.
        specialize (set_splay_max rr) as ssm.
        rewrite e1 in ssm. assert (XSet.In x0 (set_tree rr)).
        apply ssm. logical_reduction. set_reduction. right. set_reduction.
        left ; assumption. apply H5 in H12. order.
      + apply H5.
        specialize (set_splay_max rr) as ssm.
        rewrite e1 in ssm. apply ssm.
        logical_reduction. set_reduction.
        left. set_reduction. 
      + logical_reduction ; unfold XSet.For_all ; intros.
        * specialize (set_splay_max rr) as ssm.
          rewrite e1 in ssm. set_reduction.
          assert (XSet.In x (set_tree rr)).
          apply ssm. logical_reduction. set_reduction. 
          left ; set_reduction. apply H10 in H12. order.
        * specialize (set_splay_max rr) as ssm.
          rewrite e1 in ssm. set_reduction.
          assert (XSet.In x (set_tree rr)).
          apply ssm. logical_reduction. set_reduction. 
          left ; set_reduction. set_reduction ; left ; set_reduction. 
          logical_reduction.
          { apply H1 in H11. apply H5 in H12.  order. }
          { apply H4 in H11. apply H5 in H12.  order. }
  Qed.
  
  (** After splay maxing a tree "t", its right child is a leaf.
   *)
  
  Lemma splay_max_leaf : forall t l a r,
      splay_max t = <| l, a, r |> -> r = <| |>.
  Proof.
    intros t.
    functional induction (splay_max t) using splay_max_ind ; intros.
    - inversion H.
    - inversion H. reflexivity.
    - inversion H. reflexivity.
    - inversion H ; subst. apply (IHt0 rrl a r) ; assumption.
  Qed.
  
  (** If "t" is a binary search tree, and if all elements in "t" are 
      lower than "a" or equal to "a", then splay maxing t is the same
      as applying splay with element "a".
   *)

  Lemma splay_max_eq_splay : forall t a,
      bst t -> (forall x, XSet.In x (set_tree t) -> x < a \/ x == a) ->
      splay_max t = splay a t.
  Proof.
    intros t a.
    functional induction (splay_max t) using splay_max_ind ; intros.
    + reflexivity.
    + specialize (H0 b). assert (XSet.In b (set_tree <| l, b, <| |> |>)).
    - simpl. set_reduction. left. set_reduction.
    - apply H0 in H1. simpl. destruct eq_dec ; try reflexivity.
      destruct lt_dec ; try reflexivity.
      logical_reduction ; try order.
    + specialize (H0 b) as H'. assert (XSet.In b (set_tree <| l, b, <|rl,c,rr |> |>)).
      simpl. set_reduction. left. set_reduction.
      specialize (H0 c) as H''. assert (XSet.In c (set_tree <| l, b, <|rl,c,rr |> |>)).
      simpl. set_reduction. right. set_reduction. right.
      set_reduction. left. set_reduction.
      rewrite splay_max_leaf_iff in e1. subst.
      apply H0 in H2. apply H0 in H1. simpl.
      destruct eq_dec ; logical_reduction ;
        set_reduction ; logical_reduction ;
          set_reduction ; logical_reduction ;
            try destruct lt_dec ; try destruct eq_dec ;
              try destruct lt_dec ; try order ; try reflexivity.
    + specialize (H0 c) as H'. assert (c < a \/ c == a).
      apply H'. simpl. set_reduction. right. set_reduction.
      right. set_reduction. left. set_reduction.
      tree_reduction. apply splay_max_leaf in e1 as e2. simpl.
      destruct eq_dec ; logical_reduction ;
        set_reduction ; logical_reduction ;
          set_reduction ; logical_reduction ; try order ;
            try destruct lt_dec ; try destruct l ;
              try destruct eq_dec ; try destruct lt_dec ;
                try rewrite <- new ; try rewrite e1 ;
                  try reflexivity ; intros ;
                    try apply H0 ; set_reduction ; try right ;
                      set_reduction ; try right ;
                        set_reduction ; try right ;
                          set_reduction ; try right ;
                            try assumption ; try order.
    - specialize (set_splay_max rr) as H'.
      rewrite e1 in H'. specialize (H' x).
      assert (XSet.In x (set_tree rr)).
      apply H'. simpl. set_reduction. left. set_reduction.
      apply H7 in H13 as H7'. apply H12 in H13 as H12'.
      assert  (x < a \/ x == a).
      apply H0. set_reduction. right. set_reduction.
      right. set_reduction. right. set_reduction.
      right. assumption. logical_reduction ; order.
    - specialize (set_splay_max rr) as H'.
      rewrite e1 in H'. specialize (H' x).
      assert (XSet.In x (set_tree rr)).
      apply H'. simpl. set_reduction. left. set_reduction.
      apply H7 in H13 as H7'. apply H12 in H13 as H12'.
      assert  (x < a \/ x == a).
      apply H0. set_reduction. right. set_reduction.
      right. set_reduction. right. set_reduction.
      right. assumption. logical_reduction ; order.      
  Qed.

  Lemma splay_max_eq_splay' : forall t a,
      bst t -> (forall x, XSet.In x (set_tree t) -> x < a \/ x == a) ->
      eq_tree (splay_max t) (splay a t).
  Proof.
    intros.
    specialize (splay_max_eq_splay t0 a H H0) as H'.
    apply tree_syntatic_semantic in H'.
    assumption.
  Qed.
  
  (** If "t" is a binary search tree, and splay maxing t results in 
      "< | l , x , <| |> |>", then all elements of "t" are either lower
      than "x" or equal to "x".
   *)
     
  Lemma splay_max_root : forall t l x,
      bst t ->
      splay_max t = <| l, x, <| |> |> -> (forall y, XSet.In y (set_tree t) -> y < x \/ y == x).
  Proof.
    intros t l x.
    intros.
    apply  bst_splay_max in H.
    rewrite H0 in H.
    logical_reduction. specialize (set_splay_max t) as H'.
    rewrite H0 in H'. unfold XSet.Equal in H'.
    specialize (H' y). apply H' in H1.
    simpl in H1. set_reduction. logical_reduction.
    - set_reduction ; logical_reduction.
    - set_reduction. logical_reduction ; set_reduction.
  Qed.

  (** Given an element of the ordered type set, if "t" is 
      a binary search tree, then there exists a value "a"
      for which splay maxing "t" is equal to splaying "t" with 
      value "a".
   *)
  
  (* USER NEEDS TO PROVIDE AN ELEMENT*)
  Lemma splay_max_eq_splay_ex: forall t (e : o.t),
      bst t -> (exists a, eq_tree (splay_max t) (splay a t)).
  Proof.
    intros t.
    functional induction (splay_max t) using splay_max_ind ; intros e H.
    + exists e. reflexivity.
    + exists b. rewrite splay_of_root. apply eq_tree_refl. 
    + exists c. logical_reduction ; try assumption.
      destruct eq_dec eqn:E1 ; try assumption.
    - set_reduction. logical_reduction ; set_reduction ; order.
    - set_reduction. logical_reduction ; set_reduction ; logical_reduction ; try assumption.
      destruct lt_dec. destruct l ; order ; destruct eq_dec ; order ;
      destruct eq_dec ; order ; destruct lt_dec ; order ; destruct (splay c l2) ;
      order ; try assumption. destruct eq_dec ; try order. destruct eq_dec ; try order.
      rewrite splay_max_leaf_iff in e1 ; subst ; logical_reduction ; tree_reduction ;
      logical_reduction ; try reflexivity ; try assumption. 
    + specialize ( splay_max_leaf) as H'. assert (e2 := e1).
        apply H' in e2. subst. clear H'.
        exists x. logical_reduction ; try assumption.
        destruct eq_dec eqn:E1 ; try order ;
          set_reduction ; logical_reduction ; set_reduction ; try assumption.  
    - logical_reduction ; try assumption.
      specialize ( set_splay x0 rr) as ssxrr. rewrite e1 in *.
      apply eq_tree_eq_set in H7. 
      rewrite <- H7 in ssxrr. simpl in ssxrr.
      unfold XSet.Equal in ssxrr. specialize (ssxrr x).
      assert (XSet.In x (XSet.union (XSet.singleton x) (XSet.union (set_tree rrl) XSet.empty))).
      * set_reduction. left. set_reduction. 
      * apply ssxrr in H10. apply H8 in H10. order.
    - logical_reduction ; try assumption ; set_reduction. logical_reduction ;try assumption.
      specialize (set_splay_max rr) as ssxrr. rewrite e1 in *.
      simpl in ssxrr.
      unfold XSet.Equal in ssxrr. 
      assert (XSet.In x (XSet.union (XSet.singleton x) (XSet.union (set_tree rrl) XSet.empty))).
      * set_reduction. left. set_reduction. 
      * apply ssxrr in H11. apply H8 in H11.
        order.
    - destruct lt_dec ;
        logical_reduction ; set_reduction ; logical_reduction ;
          set_reduction ; logical_reduction ; try assumption.
      * specialize (set_splay_max rr) as ssxrr. rewrite e1 in *.
        simpl in ssxrr.
        unfold XSet.Equal in ssxrr. 
        assert (XSet.In x (set_tree rr)).
        apply ssxrr. set_reduction. left. set_reduction.
        apply H8 in H12 as H8'. apply H5 in H12 as H5'.
        order.
      * specialize (set_splay_max rr) as ssxrr. rewrite e1 in *.
        simpl in ssxrr.
        unfold XSet.Equal in ssxrr. 
        assert (XSet.In x (set_tree rr)).
        apply ssxrr. set_reduction. left. set_reduction.
        apply H8 in H12 as H8'. apply H5 in H12 as H5'.
        destruct eq_dec ; try order.
        destruct eq_dec ; try order.
        destruct lt_dec ; try order.
        specialize (splay_max_root rr rrl x H3 e1) as H''''.
        specialize (splay_max_eq_splay rr x H3) as H'''.
        apply H''' in H''''. rewrite <- H''''.
        rewrite e1. logical_reduction ; tree_reduction ;
        auto ; reflexivity.    
  Qed.
  
  (** If "t" is a binary sesarch tree, then using the delete method
      with value "a" on tree "t" results in the same set of elements 
      as removing "a" from the set of elements of "t".
   *)

  (* 1.3.4 Verification of delete *)
  Lemma set_delete : forall t a,
      bst t -> XSet.Equal (set_tree (delete a t)) (XSet.remove a (set_tree t)).
  Proof.
    intros t a.
    functional induction (delete a t) using delete_ind ; intros.
    + tree_reduction. logical_reduction. apply set_equal_comm_spec.
      apply set_remove_empty_spec.
    + tree_reduction. logical_reduction.
      unfold XSet.Equal. intros.
      split ; intros ;
        specialize (set_splay a t) ; intro H' ;
          rewrite e in H' ; simpl in H'.
    - apply XSet.remove_spec. logical_reduction.
      * apply H'. set_reduction. right.
        set_reduction. right. assumption.
      * specialize (splay_bstR t a (<||>) a' r) as H''.
        specialize (bst_splay a t H) as H'''.
        rewrite e in *. simpl in H'''.
        logical_reduction.
        assert (a < a0).
        apply H''; logical_reduction ; try reflexivity.
        apply eq_tree_refl.
        order.
    - specialize (splay_bstR t a (<||>) a' r) as H''.
      specialize (bst_splay a t H) as H'''.
      rewrite e in *. apply XSet.remove_spec in H0.
      logical_reduction. apply H' in H0.
      set_reduction. logical_reduction.
      set_reduction. order.
    + specialize (bst_splay a t H) as H'.
      specialize (set_splay a t) as H''.
      specialize (set_splay_max l) as H'''.
      rewrite e in *.
        unfold XSet.Equal. intros ;
          rewrite XSet.remove_spec in *.                       
        split ; intros.
    - split. 
      * simpl in H0. set_reduction.
        logical_reduction. set_reduction.
        rewrite e1 in *.
        apply H''. set_reduction. right.
        set_reduction. left. apply H'''.
        simpl. set_reduction. left.
        set_reduction ; assumption.
        apply H''. set_reduction. logical_reduction. right.
        set_reduction. left. apply H'''.
        rewrite e1. simpl. set_reduction. right.
        set_reduction. left ; assumption.
        set_reduction. right. set_reduction. right.
        assumption.
      * specialize (bst_splay_max l) as H''''.
        simpl in H'. logical_reduction.
        rewrite e1 in *.
        specialize (bst_splay a t H) as bst_splay_a_t.
        rewrite e in *.
        simpl in bst_splay_a_t.
        logical_reduction.
        specialize (set_splay_max l) as e2.
        assert (a0 < a' \/ a0 > a').
        set_reduction. logical_reduction ;
        set_reduction. left. apply H7.
        apply e2. rewrite e1.
        logical_reduction. set_reduction. left.
        set_reduction. order.
        logical_reduction. left. apply H7.
        apply e2. rewrite e1. logical_reduction.
        set_reduction. right. set_reduction.
        left. assumption.
        logical_reduction ; order.
    - apply (splay_max_leaf l) in e1 as e2.
      subst.
      logical_reduction.
      specialize (set_splay a t) as ssat.
      apply ssat in H0. rewrite e in H0.
      logical_reduction. set_reduction.
      logical_reduction ; set_reduction ;
      logical_reduction ; try order.
      specialize (set_splay_max l) as e2.
      apply e2 in H0. rewrite e1 in H0.
      logical_reduction. set_reduction.
      logical_reduction. set_reduction.
      logical_reduction. right. set_reduction. logical_reduction.
      inversion H0. right. set_reduction. right. logical_reduction.
    + unfold XSet.Equal ; split ; intros ;
      specialize (set_splay a t) as e1 ;
      rewrite e in e1. 
    - apply XSet.remove_spec. split.
      * apply e1 in H0. assumption.
      * apply tree_syntatic_semantic in e. logical_reduction.
        set_reduction. logical_reduction ; set_reduction ;
        logical_reduction ; try order.
        specialize (splay_bstL t a l a' r a0 H e H0) as e2.
        order.
        specialize (splay_bstR t a l a' r a0 H e H0) as e2.
        order.
    - apply XSet.remove_spec in H0. logical_reduction.
      apply e1. assumption.
  Qed.

  (** If "t" is a binary search tree, then deleting an element from the tree
      also results in a binary search tree.
   *)
  
  Lemma bst_delete : forall t a,
      bst t -> bst (delete a t).
  Proof.
    intros t a.
    functional induction (delete a t) using delete_ind ; intros n.
    + apply I.
    + specialize (bst_splay a t n) as n'. rewrite e in n'.
      logical_reduction.
    + specialize (bst_splay a t n) as n' ;
      rewrite e in n' ; logical_reduction ;
      specialize (bst_splay_max l H) as H' ;
      rewrite e1 in H' ; logical_reduction.
      unfold XSet.For_all. intros. apply H2 in H7.
      assert (m < a').
      apply H1. specialize (set_splay_max l). rewrite e1.
      intros. apply H8. simpl. set_reduction.
      left. set_reduction. order. 
    + specialize (bst_splay a t n) as H'. rewrite e in H'.
      auto.
  Qed.

  (** If we start with the empty tree, and 
      we insert a collection of elements that are ordered type, 
      then the tree will result in a binary search tree
   *)

  Fixpoint insert_star t l :=
    match l with
    | [] => t
    | hd :: tl => insert_star (insert hd t) tl
    end.

  Fixpoint delete_star t l :=
    match l with
    | [] => t
    | hd :: tl => delete_star (delete hd t) tl
    end.

  Fixpoint splay_star t l :=
    match l with
    | [] => t
    | hd :: tl => splay_star (splay hd t) tl
    end.

  Fixpoint splay_insert_delete_star t l :=
    match l with
    | [] => [t]
    | hd :: tl =>
      let insert_ := splay_insert_delete_star (insert hd t) tl in 
      let delete_ := splay_insert_delete_star (delete hd t) tl in 
      let splay_  := splay_insert_delete_star  (splay hd t) tl in
      insert_ ++ delete_ ++ splay_
    end.

  Search "forall".
  
  Definition all_tree_in_list_are_bst l :=
    Forall bst l.

  Functional Scheme splay_splay_insert_delete_star := Induction for splay_insert_delete_star Sort Prop.
  Functional Scheme splay_insert_star_ind := Induction for insert_star Sort Prop.
  
  Lemma bst_insert_star : forall t l,
      bst t -> bst (insert_star t l).
  Proof.
    intros t l.
    functional induction (insert_star t l) using splay_insert_star_ind.
    + auto.
    + intro H.
      apply (bst_insert hd) in H. apply IHt0 in H.
      auto.
  Qed.

  Lemma bst_insert_star_on_empty : forall l,
      bst (insert_star <||> l).
  Proof.
    intros.
    apply (bst_insert_star <||>). simpl ; auto.
  Qed.
  
  (** And the elements will be the same as the ones
      in the list.
   *)
  
  Lemma set_insert_star : forall t l,
      XSet.Equal (set_tree (insert_star t l)) (XSet.union (set_tree t) (set_list l)).
  Proof.
    intros t l.
    functional induction (insert_star t l) using splay_insert_star_ind.
    + simpl. set_reduction. unfold XSet.Equal.
      intros. split ; intro H.
      - apply XSet.union_spec. left. auto.
      - apply XSet.union_spec in H. destruct H ; auto.
        set_reduction.
    + unfold XSet.Equal in *. intros. split ; intro H.
      - apply IHt0 in H. set_reduction. logical_reduction.
        * apply set_insert in H. set_reduction. logical_reduction.
          right. set_reduction. left ; auto.
        * right. set_reduction. right ; auto.
      - apply IHt0. set_reduction. logical_reduction.
        * set_reduction. left. apply set_insert. set_reduction. right ; auto.
        * set_reduction. logical_reduction.
          left. apply set_insert. set_reduction. left. set_reduction. auto.
  Qed.
          
  Lemma set_insert_star_on_empty : forall l,
      XSet.Equal (set_tree (insert_star <||> l)) (set_list l).
  Proof.
    intros.
    apply (set_insert_star <||>).
  Qed.

  Lemma forall_append : forall A P (l1 l2 : list A),
      Forall P (l1 ++ l2) <-> (Forall P l1 /\ Forall P l2).
  Proof.
    intros. split ; intro H.
    + induction l1.
      - simpl in *. auto.
      - inversion H. apply IHl1 in H3.
        destruct H3. split ; auto.
    + induction l1.
      - simpl. destruct H.
        auto.
      - simpl. destruct H.
        inversion H. subst.
        apply Forall_cons.
        * auto.
        * apply IHl1. auto.
  Qed.
  
  Lemma bst_splay_insert_delete_star : forall t l,
      bst t -> all_tree_in_list_are_bst (splay_insert_delete_star t l).
  Proof.
    intros t l.
    functional induction (splay_insert_delete_star t l) using splay_splay_insert_delete_star.
    + intros. simpl. apply Forall_forall. intros. inversion H0 ; subst ; auto.
      inversion H1.
    + intro H.
      apply (bst_insert hd) in H as H1.
      apply (bst_delete _ hd) in H as H2.
      apply (bst_splay  hd) in H as H3.
      apply IHl0 in H1.
      apply IHl1 in H2.
      apply IHl2 in H3.
      unfold all_tree_in_list_are_bst in *.
      apply <- forall_append. split ; auto.
      apply <- forall_append. split ; auto.
  Qed.

  Lemma bst_splay_insert_delete_star_on_empty : forall l,
      all_tree_in_list_are_bst (splay_insert_delete_star <||> l).
  Proof.
    intros.
    apply (bst_splay_insert_delete_star <||>).
    simpl ; auto.
  Qed.
  
End SplayTree.
