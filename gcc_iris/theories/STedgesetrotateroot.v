From ST Require Import STorientation STpredicate STdomain STlink STpath STvaluefunction STedgeset.
From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual LibInt.
Require Import Coq.Logic.FunctionalExtensionality.

From iris_time.heap_lang Require Import proofmode.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

Notation elem := loc.
Notation EdgeSet := (elem -> elem -> orientation -> Prop).

Section SplayTreeRotateRootFunctional.
  
  Variable p : elem.
  Variable D : LibSet.set elem. (* domain *)
  Variable W : elem -> Z. (* weight nodes *)
  Variable V : elem -> Z. (* data stored in nodes *)
  
  (*confined*)

  Lemma rotate_confined_BB_if_bst : forall F x z o, 
    Inv p D F V W ->
    F p x o ->
    F x z (invert_orientation o)  ->
    let F' := (update_edge F p x z o) in
    let F'' := (update_edge F' x z p (invert_orientation o)) in
    confined D F''.
  Proof using.
    unfold update_edge in * ; intros F x z o Inv **.
    inversion Inv. unfold is_bst in *.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    unfold STpredicate.confined. intros.
    destruct H1 ; unpack ; subst.
    + destruct H3 ; unpack ; subst.
      - apply confined in H7 ; auto.
      - apply confined in H ; apply confined in H0. unpack ; split ; auto.
    + apply confined in H. unpack ; split ; auto.
  Qed.

  (*rootisindomain*)

  Lemma rotate_rootisindomain_if_bst : forall F x o, 
      Inv p D F V W ->
      F p x o ->
      rootisindomain x D.
  Proof using.
    unfold update_edge in * ; intros F x o Inv **.
    inversion Inv. unfold is_bst in Inv_bst ; unpack.
    apply H0 in H ; unpack ; auto.
  Qed. 

  (*isroot*)

  Lemma rotate_isroot_no_parent_BB_if_bst : forall F x z o,
      Inv p D F V W ->
      F p x o ->
      F x z (invert_orientation o) ->
      let F' := (update_edge F p x z o) in
      let F'' := (update_edge F' x z p (invert_orientation o)) in
      (∀ (x0 : elem) (o : orientation), x0 \in D → ¬ F'' x0 x o).
  Proof.
    intros F x z o Inv **.
    inversion Inv. unfold is_bst in *.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    intro.
    destruct H2 ; unpack ; subst ; stlink_tac.
    destruct H4 ; unpack ; subst ; stlink_tac.
    assert (p = x0). stpath_tac.
    subst. destruct H4 ; contradiction.
  Qed.

  Lemma rotate_is_root_path_to_all_BB_if_bst_aux : forall F x z o x0 a o0,
      Inv p D F V W ->
      F p x o ->
      F x z (invert_orientation o)  ->
      let F' := (update_edge F p x z o) in
      let F'' := (update_edge F' x z p (invert_orientation o)) in
      F a x0 o0 ->
      path F'' x a ->
      path F'' x x0.
  Proof.
    intros.
    destruct (bool_decide (x = a)) eqn:AX.
    + apply bool_decide_eq_true in AX. subst.
      destruct (classic (o0 = (invert_orientation o))) ; subst.
      - assert (z = x0). stlink_tac. subst.
        apply path_trans with p.
        * apply path_single with (invert_orientation o). right. auto.
        * apply path_single with o. left.
          assert (¬(p = a)). stlink_tac.
          repeat split ; auto. right ; auto.
      - apply invert_orientation_different_then_equal in H4. subst.
        apply path_single with o. left.
          repeat split ; [right;stlink_tac|right;stlink_tac|left]. 
          repeat split ; auto ; right ; stlink_tac.
    + destruct (bool_decide (p = a)) eqn:AP.
      - apply bool_decide_eq_true in AP. subst.
        apply bool_decide_eq_false in AX.
        destruct (classic (o0 = (invert_orientation o))) ; subst.
        * apply path_trans with a ; auto.
          apply path_single with (invert_orientation o). left.
          repeat split ; auto. left.
          repeat split ; auto ; right ; stlink_tac.
          intro. subst. apply AX. stpath_tac.
        * apply invert_orientation_different_then_equal in H4. subst.
          assert (x = x0). stlink_tac. subst.
          stpath_tac.
      - apply bool_decide_eq_false in AX.
        apply bool_decide_eq_false in AP.
        pose proof (update_edge_if_diff_inv F a x0 o0 p x z o H2 AP).
        pose proof (update_edge_if_diff_inv (update_edge F p x z o) a x0 o0 x z p
                                            (invert_orientation o) H4 AX).
        apply path_trans with a ; auto. apply path_single with o0. auto.
  Qed.

  Lemma rotate_isroot_path_to_all_BB_if_bst : forall F x z o,
      Inv p D F V W ->
      F p x o ->
      F x z (invert_orientation o)  ->
      let F' := (update_edge F p x z o) in
      let F'' := (update_edge F' x z p (invert_orientation o)) in
      ∀ (x0 : elem) (o : orientation), x0 \in D → path F'' x x0.
  Proof.
    intros F x z o Inv **.
    inversion Inv. unfold is_bst in *.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    apply isroot in H1 as Hpath ; auto.
    apply path_add_equiv_path in Hpath.
    apply path_add_memory_equiv_path_add in Hpath.
    destruct Hpath. assert (exists x1', x1 = rev x1').
    exists (rev x1). rewrite rev_involutive ; auto.
    destruct H3. rewrite -> H3 in H2. clear dependent x1. 
    generalize dependent x0.
    induction x2 ; intros. 
    + inversion H2 ; subst.
      - apply path_single with (invert_orientation o). unfold F''.
        right ; auto.
      - apply app_eq_nil in H3. unpack ; discriminate.
    + simpl in H2. inversion H2 ; subst.
      - symmetry in H7. apply app_eq_nil in H7 ; unpack ; discriminate.
      - symmetry in H3. apply app_eq_unit in H3 ; destruct H3 ; unpack ; try discriminate.
        inversion H4 ; subst.
        assert (path F x z). stpath_tac.
        assert (path F x0 x0). stpath_tac.
        assert (path F x x). stpath_tac.
        destruct (classic (o = o1)) ; subst.
        * assert (x = x0). stlink_tac. subst.
          stpath_tac.
        * apply path_trans with p.
          { apply path_single with (invert_orientation o). right. auto. }
          { apply path_single with o1. left.
            repeat split ; [left;stlink_tac |left;stlink_tac | left].
            apply different_orientation_then_equal_invert in H11. subst.
            assert (path F x0 x0). stpath_tac.
            assert (path F x z). stpath_tac.
            repeat split ; auto ; right ; stpath_tac ;
              destruct o1 ; simpl in * ; stpath_tac. }
      - apply app_inj_tail in H3. unpack ; subst.
        assert (a \in D). stdomain_tac.
        apply IHx2 in H3 ; auto.        
        pose proof (rotate_is_root_path_to_all_BB_if_bst_aux F x z o x0 a o1).
        apply H5 ; auto.
  Qed.

  Lemma rotate_isroot_BB_if_bst : forall F x z o, 
      Inv p D F V W ->
      F p x o ->
      F x z (invert_orientation o)  ->
      let F' := (update_edge F p x z o) in
      let F'' := (update_edge F' x z p (invert_orientation o)) in
      isroot D F'' x.
  Proof using.
    intros F x z o Inv **.
    inversion Inv. unfold is_bst in Inv_bst ; unpack.
    unfold isroot. intros. split.
    + apply rotate_isroot_no_parent_BB_if_bst ; auto.
    + apply rotate_isroot_path_to_all_BB_if_bst ; auto.
  Qed.

  (*searchtree*)

  Lemma rotate_searchtree_vx0_gt_vz0_BB_if_bst : forall F x z y o x0 z0,
      Inv p D F V W ->
      F p x o ->
      F x z (invert_orientation o) ->
      let F' := (update_edge F p x z o) in
      let F'' := (update_edge F' x z p (invert_orientation o)) in
      F x0 y (invert_orientation o) ->
      path F'' y z0 ->
      (orientation_op (invert_orientation o)) (V x0) (V z0).
  Proof.
    intros F x z y o x0 z0 Inv **.
    inversion Inv. unfold is_bst in *.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].    
    pose proof
      (update_edge_twice_if_no_path_inv p D W V F y z0 p x x z o z p (invert_orientation o)).
    pose proof (path_to_root_then_root_if_bst p D V W F y Inv).
    assert (¬(path F y p)). intro. apply H4 in H5 ; subst. stlink_tac.
    pose proof (edge_from_root_path_or_if_bst p D V W F x y o Inv H).
    assert (¬(path F y x)). intro. apply H6 in H7.
    destruct H7 ; subst ; auto ; destruct o ; simpl in * ; stlink_tac ; stpath_tac.
    assert (path F y z0). apply H3 ; auto.
    destruct o ; simpl in * ; stpath_tac.
  Qed.

  Lemma rotate_searchtree_path_rotation_BB_if_bst : forall F x z o z0,
      Inv p D F V W ->
      F p x o ->
      F x z (invert_orientation o) ->
      let F' := (update_edge F p x z o) in
      let F'' := (update_edge F' x z p (invert_orientation o)) in
      path F'' p z0 ->
      (p = z0) \/ (exists l, F p l (invert_orientation o) /\ path F l z0) \/ path F z z0.
  Proof.
    intros F x z o z0 Inv **.
    apply path_implies_path_add in H1.
    apply path_add_memory_equiv_path_add in H1.
    destruct H1. assert (exists x1, (x0 = rev x1)).
    exists (rev x0). rewrite rev_involutive. auto.
    destruct H2. rewrite H2 in H1. clear H2 x0.
    generalize dependent z0.
    induction x1 ; intros.
    + inversion H1 ; subst ; auto.
      apply app_eq_nil in H2 ; unpack. discriminate.
    + inversion H1 ; subst ; auto.
    - symmetry in H2. apply app_eq_unit in H2.
      destruct H2 ; unpack ; try discriminate.
      inversion H3. subst.
      destruct H6 ; unpack ; subst ; auto.
      destruct H6 ; unpack ; subst ; [|right ; right ; apply path_refl].
      destruct (classic (o0 = o)) ; subst ;
        [|apply different_orientation_then_equal_invert in H9 ;
          subst ;right;left;exists z0;split;auto using path_refl].
      destruct H6 ; try contradiction.
      pose proof (same_edge_for_same_orientation_if_bst p D V W F p x o z0 Inv H H8).
      contradiction.
    - apply app_inj_tail in H2 ; unpack ; subst.
      apply IHx1 in H7. destruct H7 ; subst ; auto.
      * destruct H3 ; unpack ; subst ; auto.
        destruct H4 ; unpack ; subst ; [|right;right;apply path_refl].
        {
          destruct H4,H5 ; try contradiction.
          destruct (classic (o0 = o)) ; subst.
          - right. right. 
            pose proof (same_edge_for_same_orientation_if_bst a D V W F a x o z0 Inv H H6).
            subst. exfalso ; apply H4 ; auto. 
          - right. left. exists z0 ; split ; auto using path_refl.
            apply different_orientation_then_equal_invert in H7.
            subst. auto.
        }
      * destruct H2.
        {
          destruct H2 ; unpack.
          right. left. exists x0. split ; auto.
          apply path_trans with a ; auto.
          destruct H3 ; unpack ; subst.
          + destruct H6 ; unpack ; subst.
            apply path_single with o0 ; auto.
            apply path_trans with x.
            apply path_single with o ; auto.
            apply path_single with (invert_orientation o) ; auto.
          + destruct o ; simpl in *.
            - pose proof ( different_nodes_on_bifurcation_if_bst p D V W F p x x0 x x).
              specialize (H3 Inv H2 H (path_refl F x) H4). exfalso ; apply H3 ; auto.
            - pose proof ( different_nodes_on_bifurcation_if_bst p D V W F p x0 x x x).
              specialize (H3 Inv H H2 H4 (path_refl F x)). exfalso ; apply H3 ; auto.
        }
        {
          right. right.
          destruct H3 ; unpack ; subst.
          + destruct H5 ; unpack ; subst ; auto using path_refl.
            apply path_trans with a ; auto.
            apply path_single with o0 ; auto.
          + apply path_single in H0 as H0'.
            destruct o ; simpl in * ; stpath_tac.
        }
  Qed.

  Lemma rotate_searchtree_vxvz0_BB_if_bst : forall F x z o z0,
      Inv p D F V W ->
      F p x o ->
      F x z (invert_orientation o) ->
      let F' := (update_edge F p x z o) in
      let F'' := (update_edge F' x z p (invert_orientation o)) in
      path F'' p z0 ->
      (orientation_op (invert_orientation o)) (V x) (V z0).
  Proof.
    intros F x z o z0 Inv **.
    inversion Inv. unfold is_bst in Inv_bst. 
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].  
    pose proof (rotate_searchtree_path_rotation_BB_if_bst F x z o z0 Inv H H0 H1).
    do 2 destruct H2 ; subst ; auto ; destruct o ; simpl in * ; stlink_tac ; stpath_tac.
    + destruct H2.
      assert (V x < V p). stlink_tac.
      unpack. assert (V p < V z0). stpath_tac. lia.
    + destruct H2.
      assert (V x > V p). stlink_tac.
      unpack. assert (V p > V z0). stpath_tac. lia.
  Qed.

  Lemma rotate_searchtree_vx0_lt_vz0_BB_if_bst : forall F x z y o x0 z0,
      Inv p D F V W ->
      F p x o ->
      F x z (invert_orientation o) ->
      x0 ≠ x ∨ y ≠ z ->
      x0 ≠ x ∨ y ≠ p ->
      x0 ≠ p ∨ y ≠ x ->
      x0 ≠ p ∨ y ≠ z ->
      let F' := (update_edge F p x z o) in
      let F'' := (update_edge F' x z p (invert_orientation o)) in
      F x0 y o ->
      path F'' y z0 ->
      (orientation_op o) (V x0) (V z0).
  Proof.
    intros F x z y o x0 z0 Inv **.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    pose proof (update_edge_twice_if_no_path_inv p D W V F y z0 p x x z o z p
                                                 (invert_orientation o)).
    pose proof (path_to_root_then_root_if_bst p D V W F y Inv).
    assert (¬(path F y p)). intro. apply H8 in H9 ; subst. stlink_tac.
    pose proof (edge_from_root_path_or_if_bst p D V W F x y o Inv H).
    pose proof (classic(path F y x)). destruct H11.
    + apply H10 in H11. destruct H11 ; subst ; stlink_tac.
      assert (x0 = p). stpath_tac.
      subst. destruct H3 ; contradiction.
    + assert (path F y z0). apply H7 ; auto.
      destruct o ; simpl in * ; stpath_tac.
  Qed.

  Lemma rotate_searchtree_vpvz0_BB_if_bst : forall F x z o z0,
      Inv p D F V W ->
      F p x o ->
      F x z (invert_orientation o) ->
      let F' := (update_edge F p x z o) in
      let F'' := (update_edge F' x z p (invert_orientation o)) in
      path F'' z z0 ->
      (orientation_op o) (V p) (V z0).
  Proof.
    intros F x z o z0 Inv **.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    pose proof (update_edge_twice_if_no_path_inv p D W V F z z0 p x x z o z p
                                                 (invert_orientation o)).
    pose proof (path_to_root_then_root_if_bst p D V W F z Inv).
    assert (¬(path F z p)). intro. apply H3 in H4 ; subst.
    stlink_tac.
    pose proof classic (path F z x).
    destruct H5.
    + apply path_single in H0 as H0'.
      pose proof (path_step_equal_if_bst p D V W F z x).
      assert (z = x). auto. subst. stlink_tac.
    + assert (path F z z0). apply H2 ; auto.
      assert (path F x z0). stpath_tac.
      destruct o ; simpl in * ; stpath_tac.
  Qed.

  Lemma rotate_searchtree_BB_if_bst : forall F x z o, 
      Inv p D F V W ->
      F p x o ->
      F x z (invert_orientation o) ->
      let F' := (update_edge F p x z o) in
      let F'' := (update_edge F' x z p (invert_orientation o)) in
      searchtree F'' V.
  Proof using.
    intros F x z o Inv **.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    split ; intros ; unpack.
    + destruct H1 ; unpack ; subst.
      - destruct H6 ; unpack ; subst ; simpl in *.
        * destruct o.
          { pose proof (rotate_searchtree_vx0_lt_vz0_BB_if_bst F x z y LEFT).
            simpl in H9. split ; stlink_tac. apply H9 ; auto. }
          { pose proof (rotate_searchtree_vx0_gt_vz0_BB_if_bst F x z y RIGHT x0 z0).
            simpl in *. split ; stlink_tac. apply H9 ; auto. }
        * pose proof (rotate_searchtree_vpvz0_BB_if_bst F x z LEFT z0).
          simpl in H6. split ; [|apply H6;auto].
          assert (path F x z). stpath_tac. stpath_tac.
      - destruct o ; simpl in * ; try discriminate. split ; [stlink_tac|].
        pose proof (rotate_searchtree_vxvz0_BB_if_bst F x z RIGHT z0).
        simpl in H1. auto.
    + destruct H1 ; unpack ; subst ; destruct o ; simpl in * ; try discriminate.
      - destruct H6 ; unpack ; subst ; try discriminate.
        pose proof (rotate_searchtree_vx0_gt_vz0_BB_if_bst F x z y LEFT x0 z0).
        simpl in H6. split ; stlink_tac. simpl in H9.
        apply H9 ; auto.
      - destruct H6 ; unpack ; subst.
        * pose proof (rotate_searchtree_vx0_lt_vz0_BB_if_bst F x z y RIGHT x0 z0).
          simpl in H6. split ; stlink_tac. simpl in H9.
          apply H9 ; auto.
        * pose proof (rotate_searchtree_vpvz0_BB_if_bst F x z RIGHT z0).
          simpl in H6. assert (path F x z). stpath_tac. split ; stpath_tac.
          apply H6 ; auto.
      - pose proof (rotate_searchtree_vxvz0_BB_if_bst F x z LEFT).
        simpl in H1. split ; stlink_tac. apply H1 ; auto.
  Qed.

  (*binarytree*)

  Lemma rotate_binarytree_BB_if_bst : forall F x z o, 
      Inv p D F V W ->
      F p x o ->
      F x z (invert_orientation o)  ->
      let F' := (update_edge F p x z o) in
      let F'' := (update_edge F' x z p (invert_orientation o)) in
      binarytree F''.
  Proof using.
    intros F x z o Inv **.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    unfold STpredicate.binarytree. intros.
    destruct H2, H3 ; unpack ; subst ; auto.
    + destruct H7, H5 ; unpack ; subst ; auto.
      - specialize (binarytree x0 y z0 l r). auto.
      - intro. subst. assert (x = y).
        stlink_tac. subst. destruct H7 ; contradiction.
      - intro. subst. assert (z0 = x). stlink_tac. subst.
        destruct H5 ; contradiction.
    + destruct H7 ; unpack ; subst ; auto ; [|destruct H2 ; auto]. 
      intro. subst. assert (z = y). stlink_tac.
      subst. destruct H2 ; contradiction.
    + destruct H5 ; unpack ; subst ; auto ; [|destruct H3 ; auto]. 
      intro. subst. assert (z0 = z). stlink_tac.
      subst. destruct H3 ; contradiction.
  Qed.  

  (*confined*)

  Lemma rotate_confined_BR_if_bst : forall F x o , 
      Inv p D F V W ->
      F p x o ->
      ¬(exists y, F x y (invert_orientation o)) ->
      let F' := (remove_edge F p x) in
      let F'' := (add_edge F' x p (invert_orientation o)) in
      confined D F''.
  Proof.
    intros F x o Inv E E'.
    unfold confined. intros.
    inversion Inv. unfold is_bst in * ; unpack.
    do 2destruct H ; unpack ; subst ;
      split ; stdomain_tac.
  Qed.

  (*isroot*)

  Lemma rotate_isroot_BR_if_bst : forall F x o, 
      Inv p D F V W ->
      F p x o ->
      let F' := (remove_edge F p x) in
      let F'' := (add_edge F' x p (invert_orientation o)) in
      isroot D F'' x.
  Proof.
    intros F x o Inv E **.
    unfold isroot. intros.
    inversion Inv. unfold is_bst in *.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    split.
    + intro. do 2 destruct H0 ; unpack ; subst.
      - assert (x0 = p). stpath_tac. subst.
        destruct H0 ; contradiction.
      - stlink_tac.
    + specialize (isroot x0 RIGHT H) as H2'. unpack.
      apply path_implies_path_add in H1.
      apply path_add_memory_equiv_path_add in H1.
      destruct H1. assert (exists x0, rev x0 = x1).
      exists (rev x1) ; rewrite rev_involutive ; auto.
      destruct H4. rewrite <- H4 in H1. clear dependent x1.
      generalize dependent x0.
      induction x2 ; intros.
      - inversion H1 ; subst.
        * apply path_single with (invert_orientation o). right. auto.
        * apply app_eq_nil in H4 ; unpack ; discriminate.
      - inversion H1 ; subst.
        * symmetry in H8. apply app_eq_nil in H8. unpack ; discriminate.
        * symmetry in H4. apply app_eq_unit in H4. destruct H4 ; unpack ; try discriminate.
          inversion H5. subst.
          destruct (classic (o = o1)) ; subst.
          {
            assert (x = x0). stlink_tac. subst. stpath_tac.
          }
          { apply different_orientation_then_equal_invert in H6.
            subst.
            apply path_trans with p.
            apply path_single with o1. right.
            rewrite involutive_invert. auto.
            apply path_single with (o1). left.
            split ; auto. rewrite <- not_and_eq.
            intro ; unpack ; subst. stlink_tac.
          }
        * apply app_inj_tail in H4. unpack ; subst.
          apply IHx2 in H9 ; auto ; stdomain_tac ; [|intro;stlink_tac].
          destruct (classic (o = o1)) ; subst.
          {
            destruct (classic ((a = p ∧ x0 = x))) ; unpack ; subst.
            + apply path_refl.
            + apply path_trans with a ; auto.
              apply path_single with o1.
              left. repeat split ; auto.
              rewrite <- not_and_eq. auto. 
          }
          {
            apply path_trans with a ; auto.
            apply path_single with o1.
            left. repeat split ; auto.
            rewrite <- not_and_eq. intro. unpack ; subst.
            pose proof (unique_direction_if_bst p D V W F p x o o1).
            assert (o = o1). auto. 
            contradiction.
          }
  Qed.

  (*searchtree*)

  Lemma rotate_searchtree_left_BR_if_bst : forall F x y o x0 z, 
      Inv p D F V W ->
      F p x o ->
      ¬(exists y, F x y (invert_orientation o)) ->
      let F' := (remove_edge F p x) in
      let F'' := (add_edge F' x p (invert_orientation o)) in
      F'' x0 y (invert_orientation o) ∧ path F'' y z ->
      (orientation_op (invert_orientation o)) (V x0) (V y) ∧
      (orientation_op (invert_orientation o)) (V x0) (V z).
  Proof.
    intros F x y o x0 z Inv **.
    inversion Inv. unfold is_bst in *.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    destruct (bool_decide (y = x)) eqn:YX ;
      destruct (bool_decide (y = p)) eqn:YP ;
      try apply bool_decide_eq_true in YX ; 
      try apply bool_decide_eq_true in YP ;
      try apply bool_decide_eq_false in YX ;
      try apply bool_decide_eq_false in YP ; unpack ; subst.
    - stlink_tac.
    - do 2destruct H1 ; unpack ; subst ; try contradiction.
      destruct H1 ; try contradiction.
      exfalso ; apply H1. stpath_tac. 
    - do 2destruct H1 ; unpack ; subst ; stlink_tac.
      apply adding_edge_to_beginning_of_path_inv in H4.
      destruct o ; simpl in *.
      + pose proof (remove_direction_edge_inv p D W V F p x z LEFT Inv H H4).
        destruct H1 ; subst ;
          [apply (edge_value_left_if_bst p D V W) in H ; auto ; lia|].
        destruct H1.
        apply (edge_value_left_if_bst p D V W) in H ; auto.
        split ; auto ; try lia.  simpl in H1.
        apply searchright in H1. lia.
      + pose proof (remove_direction_edge_inv p D W V F p x z RIGHT Inv H H4).
        destruct H1 ; subst ;
          [apply (edge_value_right_if_bst p D V W) in H ; auto ; lia|].
        destruct H1.
        apply (edge_value_right_if_bst p D V W) in H ; auto.
        split ; auto ; try lia. destruct H5. 
        apply searchleft in H1. lia.
    - do 2destruct H1 ; unpack ; subst ; try contradiction.
      destruct o.
      + assert (¬(path (remove_edge F p x) y x)).
        intro. apply remove_edge_inv in H6.
        pose proof (bottom_up_path_remove p D V W F p y x LEFT Inv H H6).
        destruct H7 ; subst ; try contradiction.
        destruct H7 ; subst ; try contradiction.
        pose proof (path_to_root_then_root_if_bst p D V W F y Inv H7).
        subst ; contradiction. simpl in *.
        pose proof (add_edge_if_no_path_inv (remove_edge F p x) x p RIGHT y z H6 H4).
        apply remove_edge_inv in H7. simpl in *. split ; [stlink_tac|stpath_tac].
      + assert (¬(path (remove_edge F p x) y x)).
        intro. apply remove_edge_inv in H6.
        pose proof (bottom_up_path_remove p D V W F p y x RIGHT Inv H H6).
        destruct H7 ; subst ; try contradiction.
        destruct H7 ; subst ; try contradiction.
        pose proof (path_to_root_then_root_if_bst p D V W F y Inv H7).
        subst ; contradiction.
        pose proof (add_edge_if_no_path_inv (remove_edge F p x) x p LEFT y z H6 H4).
        apply remove_edge_inv in H7. simpl in *. split ; [stlink_tac|stpath_tac].
  Qed.

  Lemma rotate_searchtree_right_BR_if_bst : forall F x y x0 z o, 
      Inv p D F V W ->
      F p x o ->
      ¬(exists y, F x y (invert_orientation o)) ->
      let F' := (remove_edge F p x) in
      let F'' := (add_edge F' x p (invert_orientation o)) in
      F'' x0 y o ∧ path F'' y z ->
      (orientation_op (o)) (V x0) (V y) ∧
      (orientation_op (o)) (V x0) (V z).
  Proof.
    intros F x y x0 z o Inv **.
    inversion Inv. unfold is_bst in *.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    destruct (bool_decide (y = x)) eqn:YX ;
      destruct (bool_decide (y = p)) eqn:YP ;
      try apply bool_decide_eq_true in YX ; 
      try apply bool_decide_eq_true in YP ;
      try apply bool_decide_eq_false in YX ;
      try apply bool_decide_eq_false in YP ; unpack ; subst.
    - stlink_tac.
    - do 2destruct H1 ; unpack ; subst ; try discriminate.
      destruct H1 ; try contradiction.
      assert (p = x0). stpath_tac. subst. contradiction.
      contradiction.
    - do 2destruct H1 ; unpack ; subst ; try discriminate.
      stlink_tac. destruct o ; simpl in * ; discriminate.
    - do 2destruct H1 ; unpack ; subst ; try contradiction.
      assert (¬(path (remove_edge F p x) y x)).
      intro. apply remove_edge_inv in H6.
      pose proof (bottom_up_path_remove p D V W F p y x o Inv H H6).
      destruct H7 ; subst ; try contradiction.
      destruct H7 ; subst ; try contradiction.
      pose proof (path_to_root_then_root_if_bst p D V W F y Inv H7).
      subst ; contradiction.
      pose proof (add_edge_if_no_path_inv (remove_edge F p x) x p (invert_orientation o)
                                          y z H6 H4).
      apply remove_edge_inv in H7.
      destruct o ; simpl in *. split ; [stlink_tac|stpath_tac].
      split ; [stlink_tac|stpath_tac].
  Qed.

  Lemma rotate_searchtree_BR_if_bst : forall F x o, 
      Inv p D F V W ->
      F p x o ->
      ¬(exists y, F x y (invert_orientation o)) ->
      let F' := (remove_edge F p x) in
      let F'' := (add_edge F' x p (invert_orientation o)) in
      searchtree F'' V.
  Proof.
    intros F x o Inv **.
    inversion Inv. unfold is_bst in * ; unpack.
    split ; intros.
    + destruct o.
      - pose proof (rotate_searchtree_right_BR_if_bst F x y x0 z LEFT).
        simpl in *. apply H9 ; auto.
      - pose proof (rotate_searchtree_left_BR_if_bst F x y RIGHT x0 z).
        simpl in *. apply H9 ; auto.
    + destruct o.
      - pose proof (rotate_searchtree_left_BR_if_bst F x y LEFT x0 z).
        simpl in *. apply H9 ; auto.
      - pose proof (rotate_searchtree_right_BR_if_bst F x y x0 z RIGHT).
        simpl in *. apply H9 ; auto.
  Qed.

  Lemma rotate_binarytree_BR_if_bst : forall F x o, 
      Inv p D F V W ->
      F p x o ->
      ¬(exists y, F x y (invert_orientation o)) ->
      let F' := (remove_edge F p x) in
      let F'' := (add_edge F' x p (invert_orientation o)) in
      binarytree F''.
  Proof.
    intros F x o Inv **.
    inversion Inv.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    unfold STpredicate.binarytree.
    intros. destruct H2, H3 ; unpack ; subst ; try contradiction.
    + destruct H2, H3. specialize (binarytree x0 y z l r).
      auto.
    + destruct H2. intro ; subst.
      apply H0. exists y. auto.
    + destruct H3. intro ; subst.
      apply H0. exists z. auto.
  Qed.  

End SplayTreeRotateRootFunctional.

(*

       p        x
        \      /
        x     p
       /      \
      z       z

 *)

Section SplayTreeRotateRightRootInv.

  Variable p : elem.
  Variable D : LibSet.set elem. (* domain *)
  Variable W : elem -> Z. (* weight nodes *)
  Variable V : elem -> Z. (* data stored in nodes *)

  (*
    
        Prove rotations that have an inner
        edge for the son of the root.
             
             p       p
            /         \
           x          x
           \          /
           z         z 

   *)
  
  Theorem rotate_XI_if_bst : forall F x z o, 
    Inv p D F V W ->
    F p x o ->
    F x z (invert_orientation o)  ->
    let F' := (update_edge F p x z o) in
    let F'' := (update_edge F' x z p (invert_orientation o)) in
    Inv x D F'' V W.
  Proof using.
    intros.
    constructor. unfold is_bst.
    split ; auto.
    (* confined *)
    apply (rotate_confined_BB_if_bst p D W V) ; auto.
    split ; auto.
    (*rootisindomain*)
    apply (rotate_rootisindomain_if_bst p D W V) with F o ; auto.
    split ; auto.
    (*isroot*)
    apply (rotate_isroot_BB_if_bst p D W V) ; auto.
    split ; auto.
    (*searchtree*)
    apply (rotate_searchtree_BB_if_bst p D W V) ; auto.    
    (*binarytree*)
    split ; auto.
    apply (rotate_binarytree_BB_if_bst p D W V) ; auto.
    inversion H. unfold is_bst in *. unpack ; auto.
  Qed.

  (*

       p        p         x
        \       \  ->    /
        x       x       p
      /\/      
      y       

   *)

  Theorem rotate_XE_if_bst : forall F x o, 
      Inv p D F V W ->
      F p x o ->
      ¬(exists y, F x y (invert_orientation o)) ->
      let F' := (remove_edge F p x) in
      let F'' := (add_edge F' x p (invert_orientation o)) in
      Inv x D F'' V W.
  Proof using.
    intros.
    constructor. unfold is_bst.
    split ; auto.
    (* confined *)
    apply (rotate_confined_BR_if_bst p D W V F x o) ; auto.
    split ; auto.
    (*rootisindomain*)
    apply (rotate_rootisindomain_if_bst p D W V F) with o ; auto.
    split ; auto.
    (*isroot*)
    apply (rotate_isroot_BR_if_bst p D W V) ; auto.
    split ; auto.
    (*searchtree*)
    apply (rotate_searchtree_BR_if_bst p D W V F x o) ; auto.
    (*binarytree*)
    split ; auto.
    apply (rotate_binarytree_BR_if_bst p D W V F) ; auto.
    inversion H. unfold is_bst in *. unpack ; auto.
  Qed.

End SplayTreeRotateRightRootInv.
