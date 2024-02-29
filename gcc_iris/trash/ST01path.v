From iris_time.heap_lang Require Import proofmode.
Require Import stpredicate.
Require Import Coq.Lists.List.
Import ListNotations.

Section PathWithMemory.

  Notation elem := loc.
  Notation EdgeSet := (elem -> elem -> orientation -> Prop).
  
  Inductive path_memory : EdgeSet -> elem -> elem -> (list elem) -> Prop :=
    path_m_refl : forall F x,
      path_memory F x x []
  | path_m_single  : forall (F : EdgeSet) x y o,
      F x y o ->
      path_memory F x y [x]
  | path_m_add : forall (F : EdgeSet) x y z o l,
      F x y o ->
      path_memory F y z l ->
      path_memory F x z (x::l).

  Lemma path_app : forall F x y z x0 x1,
      path_memory F x y x0 ->
      path_memory F y z x1 ->
      path_memory F x z (x0 ++ x1).
  Proof.
    intros.
    induction H ; auto.
    + apply (path_m_add F x y z) with o ; auto.
    + apply IHpath_memory in H0. apply (path_m_add F x y z) with o ; auto.
  Qed.
  
  Lemma path_memory_implies_path : forall F x y l,
    (path_memory F x y l -> path F x y).
  Proof.
    intros.
    induction H.
    + apply path_refl.
    + apply path_single with o. auto.
    + apply path_trans with y ; auto.
      apply path_single with o. auto.
  Qed.

  Lemma path_add_end: forall (F : EdgeSet ) x y o z l,
      F y z o -> 
      path_memory F x y l ->
      path_memory F x z (l ++ [y]).
  Proof.
    intros.
    induction H0.
    + simpl. apply path_m_single with o ; auto.
    + simpl. apply path_m_add with y o0 ; auto.
      apply path_m_single with o ; auto.
    + specialize (IHpath_memory H).
      apply path_m_add with y o0 ; auto.
  Qed.

  Lemma path_exists_one : forall F x y,
      (path F x y -> exists l, path_memory F x y l).
  Proof.
    intros.
    induction H.
    + eexists. apply path_m_refl.
    + exists [x]. apply path_m_single with o ; auto.
    + destruct IHpath1, IHpath2. exists (x0 ++ x1).
      apply path_app with y ; auto.
  Qed.
  
End PathWithMemory.
  
Section PathWithMemorySplayTree.


  Lemma path_must_be_equal_if_bst : forall p D F V x y l1 l2,
    Inv p D F V ->
    path_memory F x y l1 ->
    path_memory F x y l2 ->
    l1 = l2.
  Proof.
    intros p D F V x y l1 l2 H H0.
    generalize l2.
    inversion H. unfold is_bst in Inv_bst . unpack.
    induction H0.
    + intros. inversion H0 ; subst ; auto.
    - pose proof (cant_point_to_itself_if_bst p D F V x o H H6).
      contradiction.
    - apply path__implies_path in H7.
      pose proof (no_cycles_if_bst p D F V x y o H H6 H7).
      contradiction.
      + intros. induction H6 ; subst ; auto.
    - pose proof (cant_point_to_itself_if_bst p D F V x o H H0).
      contradiction.
    - destruct (bool_decide (z = y)) eqn:E.
      * apply bool_decide_eq_true in E. subst.
        pose proof (unique_direction_if_bst p D F V x y o o0 H H6 H0).
        subst.
        inversion H7 ; subst ; auto.
        { pose proof (cant_point_to_itself_if_bst p D F V y o H H8).
          contradiction. }
        { apply path__implies_path in H9.
          pose proof (no_cycles_if_bst p D F V y y0 o H H8 H9).
          contradiction. }
      * apply bool_decide_eq_false in E.
        unfold binarytree in H5.
        specialize (H5 x y z o0 o E H6 H0).
        destruct o, o0 ; try exfalso ; apply H5 ; auto ;
        unfold searchtree in H4 ;unpack ;
        apply path__implies_path in H7.
        { 
          assert (F x y RIGHT /\ path F y z). split ; auto.
          apply H8 in H9. unpack.
          apply (edge_value_left_if_bst p D F V) in H0 ; auto.
          lia.
        }
        {
          assert (F x y LEFT /\ path F y z). split ; auto.
          apply H4 in H9. unpack.
          apply (edge_value_right_if_bst p D F V) in H0 ; auto.
          lia.
        }
  + specialize (IHpath_ H H1 H3 H4 H5).
    intros. destruct l0.
    - inversion H7 ; subst.
      apply path__implies_path in H6.
      pose proof (no_cycles_if_bst p D F V z y o H H0 H6).
      contradiction.
    - inversion H7 ; subst.
      * destruct (bool_decide (y = z)) eqn:E.
        {
          apply bool_decide_eq_true in E. subst.
          pose proof (unique_direction_if_bst p D F V l0 z o o0 H H12 H0).
          subst.
          assert (path_ F z z nil). apply path_o_refl.
          specialize (IHpath_ nil H8). subst. auto.
        }
        {
          apply bool_decide_eq_false in E.
          unfold binarytree in H5.
          specialize (H5 l0 z y o0 o E H12 H0).
          apply path__implies_path in H6.
          unfold searchtree in H4 ; unpack.
          destruct o, o0 ; try (exfalso ; contradiction).
          {
            assert (F l0 y LEFT /\ path F y z). split ; auto.
            apply H4 in H9. unpack.
            apply (edge_value_right_if_bst p D F V) in H12 ; auto.
            lia.
          }
          {
            assert (F l0 y RIGHT /\ path F y z). split ; auto.
            apply H8 in H9. unpack.
            apply (edge_value_left_if_bst p D F V) in H12 ; auto.
            lia.
          }
        }        
      * destruct (bool_decide (y0 = y)) eqn:E.
        {
          apply bool_decide_eq_true in E. subst.
          specialize (IHpath_ l1 H14). subst.
          pose proof (unique_direction_if_bst p D F V l0 y o o0 H H13 H0).
          subst. auto.
        }
        {
          apply bool_decide_eq_false in E.
          unfold binarytree in H5.
          specialize (H5 l0 y y0 o o0 E H0 H13).
          apply path__implies_path in H6.
          apply path__implies_path in H14.
          unfold searchtree in H4 ; unpack.
          destruct o, o0 ; try (exfalso ; contradiction).
          {
            assert (F l0 y LEFT /\ path F y z). split ; auto.
            apply H4 in H9. unpack.
            assert (F l0 y0 RIGHT /\ path F y0 z). split ; auto.
            apply H8 in H11. unpack.
            lia.
          }
          {
            assert (F l0 y RIGHT /\ path F y z). split ; auto.
            apply H8 in H9. unpack.
            assert (F l0 y0 LEFT /\ path F y0 z). split ; auto.
            apply H4 in H11. unpack.
            lia.
          }
        }        
Qed.






Lemma path_must_be_equal_if_bst : forall p D F V x y l1 l2,
   Inv p D F V ->
   path_ F x y l1 ->
   path_ F x y l2 ->
   l1 = l2.
Proof.
  intros p D F V x y l1 l2 H H0.
  generalize l2.
  inversion H. unfold is_bst in Inv_bst0. unpack.
  induction H0.
  + intros. inversion H0 ; subst ; auto.
    - pose proof (cant_point_to_itself_if_bst p D F V x o H H6).
      contradiction.
    - apply path__implies_path in H7.
      pose proof (no_cycles_if_bst p D F V x y o H H6 H7).
      contradiction.
  + intros. induction H6 ; subst ; auto.
    - pose proof (cant_point_to_itself_if_bst p D F V x o H H0).
      contradiction.
    - destruct (bool_decide (z = y)) eqn:E.
      * apply bool_decide_eq_true in E. subst.
        pose proof (unique_direction_if_bst p D F V x y o o0 H H6 H0).
        subst.
        inversion H7 ; subst ; auto.
        { pose proof (cant_point_to_itself_if_bst p D F V y o H H8).
          contradiction. }
        { apply path__implies_path in H9.
          pose proof (no_cycles_if_bst p D F V y y0 o H H8 H9).
          contradiction. }
      * apply bool_decide_eq_false in E.
        unfold binarytree in H5.
        specialize (H5 x y z o0 o E H6 H0).
        destruct o, o0 ; try exfalso ; apply H5 ; auto ;
        unfold searchtree in H4 ;unpack ;
        apply path__implies_path in H7.
        { 
          assert (F x y RIGHT /\ path F y z). split ; auto.
          apply H8 in H9. unpack.
          apply (edge_value_left_if_bst p D F V) in H0 ; auto.
          lia.
        }
        {
          assert (F x y LEFT /\ path F y z). split ; auto.
          apply H4 in H9. unpack.
          apply (edge_value_right_if_bst p D F V) in H0 ; auto.
          lia.
        }
  + specialize (IHpath_ H H1 H3 H4 H5).
    intros. destruct l0.
    - inversion H7 ; subst.
      apply path__implies_path in H6.
      pose proof (no_cycles_if_bst p D F V z y o H H0 H6).
      contradiction.
    - inversion H7 ; subst.
      * destruct (bool_decide (y = z)) eqn:E.
        {
          apply bool_decide_eq_true in E. subst.
          pose proof (unique_direction_if_bst p D F V l0 z o o0 H H12 H0).
          subst.
          assert (path_ F z z nil). apply path_o_refl.
          specialize (IHpath_ nil H8). subst. auto.
        }
        {
          apply bool_decide_eq_false in E.
          unfold binarytree in H5.
          specialize (H5 l0 z y o0 o E H12 H0).
          apply path__implies_path in H6.
          unfold searchtree in H4 ; unpack.
          destruct o, o0 ; try (exfalso ; contradiction).
          {
            assert (F l0 y LEFT /\ path F y z). split ; auto.
            apply H4 in H9. unpack.
            apply (edge_value_right_if_bst p D F V) in H12 ; auto.
            lia.
          }
          {
            assert (F l0 y RIGHT /\ path F y z). split ; auto.
            apply H8 in H9. unpack.
            apply (edge_value_left_if_bst p D F V) in H12 ; auto.
            lia.
          }
        }        
      * destruct (bool_decide (y0 = y)) eqn:E.
        {
          apply bool_decide_eq_true in E. subst.
          specialize (IHpath_ l1 H14). subst.
          pose proof (unique_direction_if_bst p D F V l0 y o o0 H H13 H0).
          subst. auto.
        }
        {
          apply bool_decide_eq_false in E.
          unfold binarytree in H5.
          specialize (H5 l0 y y0 o o0 E H0 H13).
          apply path__implies_path in H6.
          apply path__implies_path in H14.
          unfold searchtree in H4 ; unpack.
          destruct o, o0 ; try (exfalso ; contradiction).
          {
            assert (F l0 y LEFT /\ path F y z). split ; auto.
            apply H4 in H9. unpack.
            assert (F l0 y0 RIGHT /\ path F y0 z). split ; auto.
            apply H8 in H11. unpack.
            lia.
          }
          {
            assert (F l0 y RIGHT /\ path F y z). split ; auto.
            apply H8 in H9. unpack.
            assert (F l0 y0 LEFT /\ path F y0 z). split ; auto.
            apply H4 in H11. unpack.
            lia.
          }
        }        
Qed.
