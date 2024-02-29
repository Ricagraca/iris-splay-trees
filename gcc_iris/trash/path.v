Require Import predicate.


Inductive path_ : (elem -> elem -> orientation -> Prop) -> elem -> elem -> (list elem) -> Prop :=
  path_o_refl : forall F x, path_ F x x nil
| path_o_single  : forall (F : elem -> elem -> orientation -> Prop) x y o,
    F x y o ->
    path_ F x y (cons x nil)
| path_o_add : forall (F : elem -> elem -> orientation -> Prop) x y z o l,
    F x y o ->
    path_ F y z l ->
    path_ F x z (cons x l).

Lemma path__implies_path : forall F x y l,
    (path_ F x y l -> path F x y).
Proof.
  intros.
  induction H.
  + apply path_refl.
  + apply path_single with o. auto.
  + apply path_trans with y ; auto.
    apply path_single with o. auto.
Qed.

Lemma path_add_end: forall (F :  (elem -> elem -> orientation -> Prop) ) x y o z l,
   F y z o -> 
   path_ F x y l ->
   path_ F x z (l ++ (cons y nil)).
Proof.
  intros.
  induction H0.
  + simpl. apply path_o_single with o ; auto.
  + simpl. apply path_o_add with y o0 ; auto.
    apply path_o_single with o ; auto.
  + specialize (IHpath_ H).
    apply path_o_add with y o0 ; auto.
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

Lemma path__implies_only_path : forall p D F V x y l,
    Inv p D F V ->
    path_ F x y l ->
    exists! l', path_ F x y l'.
Proof.
  intros.
  exists l.
  split ; auto.
  intros. apply (path_must_be_equal_if_bst p D F V  x y l y0 H) in H0 ; auto.
Qed.

Lemma path_app : forall F x y z x0 x1,
    path_ F x y x0 ->
    path_ F y z x1 ->
    path_ F x z (x0 ++ x1).
Proof.
  intros.
  induction H ; auto.
  + apply (path_o_add F x y z) with o ; auto.
  + apply IHpath_ in H0. apply (path_o_add F x y z) with o ; auto.
Qed.

Lemma path_exists_one : forall p D F V x y,
    Inv p D F V -> 
    (path F x y -> exists l, path_ F x y l).
Proof.
  intros.
  induction H0.
  + eexists. apply path_o_refl.
  + exists (cons x nil). apply path_o_single with o ; auto.
  + specialize (IHpath1 H).
    specialize (IHpath2 H). destruct IHpath1, IHpath2.
    exists (x0 ++ x1).
    apply path_app with y ; auto.
Qed.

Lemma path_exists_only_one : forall p D F V x y,
    Inv p D F V -> 
    (path F x y -> exists! l, path_ F x y l).
Proof.
  intros.
  apply (path_exists_one p D F V) in H0 as H0' ; auto.
  destruct H0'. exists x0 ; split ; auto.
  intros. pose proof (path_must_be_equal_if_bst p D F V x y x0 y0 H H1 H2).
  auto.
Qed.

Lemma path_has_no_element_if_seen_before : forall p D F V x y o t l,
    Inv p D F V ->
    F x y o ->
    path_ F y t l ->
    Forall (fun e => ~(e = x)) l.
Proof.
  intros.
  induction H1 ; auto.
  + apply List.Forall_cons ; auto. admit.
  +
    
