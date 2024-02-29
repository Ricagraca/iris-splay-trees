From ST Require Import STorientation STpredicate.
From TLC Require Import LibTactics LibLogic LibProd LibContainer LibSet
     LibRelation LibPer.
From iris_time Require Import TLCBuffer.

Require Import Coq.Lists.List.
Import ListNotations.
From iris_time.heap_lang Require Import proofmode.
Require Import Coq.Logic.FunctionalExtensionality.

Notation elem := loc.
Notation EdgeSet := (elem -> elem -> orientation -> Prop).

Section DomainFunction.
  
  Definition descendants (F : EdgeSet) (r : elem) : set elem :=
    \set{ x | path F r x }.

End DomainFunction.
  
Section DomainProof.

  Inductive path_add : EdgeSet -> elem -> elem -> Prop :=
    path_a_refl : forall F x, path_add F x x
  | path_a_single : forall (F : EdgeSet) x y o, F x y o -> path_add F x y                         
  | path_a_add : forall (F : EdgeSet) x y z o, F y z o -> path_add F x y -> path_add F x z.

  Inductive path_add_memory : EdgeSet -> elem -> elem -> list elem -> Prop :=
    path_am_refl : forall F x, path_add_memory F x x ([])
  | path_am_single : forall (F : EdgeSet) x y o, F x y o -> path_add_memory F x y ([x])
  | path_am_add : forall (F : EdgeSet) x y z o l,
      F y z o -> path_add_memory F x y l -> path_add_memory F x z (l ++ [y]).

  Lemma path_add_memory_equiv_path_add : forall F x y,
      path_add F x y <-> exists l, path_add_memory F x y l.
  Proof.
    intros.
    split ; intros.
    + induction H.
      - eexists ([]). apply path_am_refl.
      - exists ([x]). apply path_am_single with o ; auto.
      - destruct IHpath_add. exists (x0++[y]).
        apply path_am_add with o ; auto.
    + destruct H. induction H.
      - apply path_a_refl.
      - apply path_a_single with o ; auto.
      - apply path_a_add with y o ; auto.
  Qed.    
      
  Lemma path_add_begin : forall (F : EdgeSet) x y z o ,
      F x y o ->
      path_add F y z ->
      path_add F x z.
  Proof.
    intros. induction H0.
    + apply path_a_single with o ; auto.
    + apply path_a_single in H.
      apply path_a_add with x0 o0 ; auto.
    + specialize (IHpath_add H).
      apply path_a_add with y o0 ; auto.
  Qed.
  
  Lemma path_add_memory_begin : forall (F : EdgeSet) x y z o l,
      F x y o ->
      path_add_memory F y z l ->
      path_add_memory F x z ([x] ++ l).
  Proof.
    intros.
    induction H0.
    + simpl. apply path_am_single with o ; auto.
    + apply path_am_add with o0 ; auto.
      apply path_am_single with o ; auto.
    + rewrite app_assoc. apply path_am_add with o0 ; auto.
  Qed.
    
  Lemma path_add_transitivity: forall F x y z,
      path_add F x y ->
      path_add F y z ->
      path_add F x z.    
  Proof.
    intros F x y z H1 H2.
    induction H1 ; auto.
    + apply path_add_begin with y o ; auto.
    + apply IHpath_add. apply path_add_begin with z0 o ; auto.
  Qed.

  Lemma path_add_memory_transitivity : forall F x y z l1 l2,
      path_add_memory F x y l1 ->
      path_add_memory F y z l2 ->
      path_add_memory F x z (l1 ++ l2).    
  Proof.
    intros F x y z l1 l2 H1.
    generalize l2.
    induction H1 ; auto ; intros.
    + apply (path_add_memory_begin F x y z o l0 H H0).
    + specialize (IHpath_add_memory ([y] ++ l0)).
      assert (path_add_memory F y z ([y] ++ l0)).
      pose proof (path_add_memory_begin F y z0 z o l0 H H0) ; auto.
      apply IHpath_add_memory in H2.
      replace (l ++ [y] ++ l0) with ((l++[y]) ++ l0) in H2 ; auto.
      rewrite app_assoc ; auto.
  Qed.
  
  Lemma path_implies_path_add : forall F x y,
      path F x y ->
      path_add F x y.
  Proof.
    intros F x y H.
    induction H.
    + apply path_a_refl.
    + apply path_a_single with o. auto.
    + apply path_add_transitivity with y ; auto.
  Qed.
   
  Lemma path_implies_path_add_memory : forall F x y,
      path F x y ->
      exists l, path_add_memory F x y l.
  Proof.
    intros F x y H.
    apply path_implies_path_add in H.
    apply path_add_memory_equiv_path_add in H. auto.
  Qed.

  Lemma path_add_implies_path : forall F x y,
      path_add F x y ->
      path F x y.
  Proof.
    intros F x y H.
    induction H.
    + apply path_refl.
    + apply path_single with o. auto.
    + apply path_trans with y ; auto.
      apply path_single with o. auto.
  Qed.

  Lemma path_add_equiv_path : forall F x y,
      path_add F x y <-> path F x y.
  Proof.
    intros. split.
    + apply path_add_implies_path.
    + apply path_implies_path_add.
  Qed.

  Lemma path_add_memory_implies_path : forall F x y l,
      path_add_memory F x y l -> path F x y.
  Proof.
    intros.
    apply path_add_equiv_path.
    apply path_add_memory_equiv_path_add.
    exists l ; auto.
  Qed.  

  Lemma exists_path_add_memory_implies_path : forall F x y,
      (exists l, path_add_memory F x y l) ->
      path F x y.
  Proof.
    intros F x y H. 
    apply path_add_memory_equiv_path_add in H.
    apply path_add_implies_path. auto.
  Qed.
  
End DomainProof.

Section DomainSplayTree.
  
  Variable p : elem.
  Variable D : LibSet.set elem. (* domain *)
  Variable V : elem -> Z. (* data stored in nodes *)
  Variable W : elem -> Z. (* weight nodes *)
  Variable M : gmap elem content. (* view of the memory *)
  
  Lemma path_domain_if_bst : forall F x, 
    Inv p D F V W -> 
    path F p x ->
    x \in D.
  Proof.
    intros F x Inv H.
    apply path_implies_path_add in H.
    induction H ; inversion Inv ; unfold is_bst in Inv_bst ; unpack ; subst.
    + auto.
    + apply H0 in H. unpack ; auto.
    + apply H1 in H. unpack ; auto.
  Qed.  

  Lemma in_domain_if_neq_if_bst : forall F x y, 
    Inv p D F V W -> 
    path F x y ->
    ~(x = y) ->
    x \in D /\ y \in D.
  Proof.
    intros F x y Inv H NEQ.
    apply path_implies_path_add in H.
    induction H ; inversion Inv ; unfold is_bst in Inv_bst ; unpack ; subst.
    + exfalso ; contradiction.
    + apply H0 in H. auto.
    + specialize (IHpath_add Inv). apply H1 in H as H'.
      unpack ; split ; auto.
      destruct (bool_decide (x = y)) eqn:XY ;
        [apply bool_decide_eq_true in XY;subst
        |apply bool_decide_eq_false in XY] ; auto.
      apply IHpath_add in XY. unpack ; auto.
  Qed.

  Lemma in_edge_then_in_domain_left_if_bst : forall F x y o,
      Inv p D F V W ->
      F x y o ->
      x \in D.
  Proof.
    intros.
    inversion H.
    unfold is_bst in Inv_bst.
    unpack. apply H1 in H0 ; unpack ; auto.
  Qed.
    
  Lemma in_edge_then_in_domain_right_if_bst : forall F x y o,
      Inv p D F V W ->
      F x y o ->
      y \in D.
  Proof.
    intros.
    inversion H.
    unfold is_bst in Inv_bst.
    unpack. apply H1 in H0 ; unpack ; auto.
  Qed.

  Lemma root_in_domain_if_bst : forall F,
      Inv p D F V W ->
      p \in D.
  Proof.
    intros.
    inversion H.
    unfold is_bst in Inv_bst.
    unpack. auto.
  Qed.
  
  Lemma if_node_in_domain_and_edge_then_end_also_in_domain_if_bst : forall F a x o x',
      Inv p D F V W ->      
      let D' := (descendants F x) in
      a \in D' ->
      F a x' o -> 
      x' \in D'.
  Proof.
    intros.
    rewrite in_set_st_eq.
    rewrite in_set_st_eq in H0.
    apply path_trans with a ; auto.
    apply path_single with o ; auto.
  Qed.
  
  Lemma descendants_incl_domain_if_bst : forall F x,
      Inv p D F V W ->
      x \in D ->
      let D' := descendants F x in
      D' \c D.
  Proof.
    intros F x Inv H. 
    unfold descendants.
    rewrite set_incl_in_eq. intros.
    rewrite in_set_st_eq in H0.
    pose proof (classic(x = x0)).
    destruct H1 ; subst ; auto.
    pose proof (in_domain_if_neq_if_bst F x x0 Inv H0 H1).
    unpack ; auto.
  Qed.
  
  Lemma descendants_finite_if_bst : forall F x,
      Inv p D F V W ->
      x \in D ->
      let D' := descendants F x in
      finite (D').
  Proof.
    intros F x Inv H.
    inversion Inv. 
    destruct Inv_bst as
        [confined [rootisindomain
                     [isroot [[searchleft searchright] [binarytree [finite positive]]]]]].
    pose proof (descendants_incl_domain_if_bst F x Inv H).
    pose proof (finite_incl H0 finite). auto.
  Qed.
  
  Lemma descendants_of_descendants_finite_if_bst : forall F x y o,
      finite (descendants F x) ->
      F x y o -> 
      finite (descendants F y).
  Proof.
    intros.
    pose proof (finite_incl).
    specialize (H1 elem (descendants F y) (descendants F x)).
    apply H1 ; auto. rewrite set_incl_in_eq.
    intros. rewrite in_set_st_eq in H2.
    rewrite in_set_st_eq. apply path_trans with y ; auto.
    apply path_single with o ; auto.
  Qed.
    
End DomainSplayTree.

Ltac stdomain_tac :=
  match goal with
  (* Edge domain *)
  | h1 : STpredicate.confined ?D ?F, h2 : ?F ?x ?y ?o |- ?x \in ?D =>
    apply h1 in h2 ; destruct h2 ; assumption
  | h1 : STpredicate.confined ?D ?F, h2 : ?F ?x ?y ?o |- ?y \in ?D =>
    apply h1 in h2 ; destruct h2 ; assumption
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?o |- ?y \in ?D =>
    apply (in_edge_then_in_domain_right_if_bst p D V W F x y o) ; auto
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?o |- ?x \in ?D =>
    apply (in_edge_then_in_domain_left_if_bst p D V W F x y o) ; auto
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?o |- ?x \in ?D =>
    apply (in_edge_then_in_domain_left_if_bst p D V W F x y o) ; auto
  | h1 : Inv ?p ?D ?F ?V ?W |- ?p \in ?D =>
    apply (root_in_domain_if_bst p D V W F h1)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : path ?F ?p ?x |- ?x \in ?D  =>
    apply (path_domain_if_bst p D V W F x h1 h2)
  | _ => idtac
  end.


Example ex1 : forall D (F : EdgeSet) x y o,
    STpredicate.confined D F -> F x y o -> x \in D.
Proof.
  intros. stdomain_tac.
Qed.

Example ex2 : forall D (F : EdgeSet) x y o,
    STpredicate.confined D F -> F x y o -> y \in D.
Proof.
  intros. stdomain_tac.
Qed.

Example ex3 : forall p D (F : EdgeSet) V W x y o,
    Inv p D F V W -> F x y o -> y \in D.
Proof.
  intros. stdomain_tac.
Qed.

Example ex4 : forall p D (F : EdgeSet) V W,
    Inv p D F V W -> p \in D.
Proof.
  intros. stdomain_tac.
Qed.

Example ex5 : forall p D (F : EdgeSet) V W x,
    Inv p D F V W -> path F p x -> x \in D.
Proof.
  intros. stdomain_tac.
Qed.
