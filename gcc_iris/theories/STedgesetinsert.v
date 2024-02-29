From ST Require Import STorientation STpredicate STdomain STlink STpath STvaluefunction STedgeset.
From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual LibInt.
Require Import Coq.Logic.FunctionalExtensionality.

From iris_time.heap_lang Require Import proofmode.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

Notation elem := loc.
Notation EdgeSet := (elem -> elem -> orientation -> Prop).

Section SplayTreeInsertFunctional.
  
  Variable p : elem.
  Variable D : LibSet.set elem. (* domain *)
  Variable W : elem -> Z. (* weight nodes *)
  Variable V : elem -> Z. (* data stored in nodes *)
  
  Lemma insert_confined_if_bst : forall F x n u k,  
      Inv p D F V W ->
      n \notin D ->
      orientation_op u (V p) k ->
      F p x u -> 
      (forall y y' o, F p y o -> y' \in descendants F y -> (orientation_op o) k (V y')) ->
      confined (D \u '{n}) (remove_edge (add_edge (add_edge F n p (invert_orientation u)) n x u) p x).
  Proof.
    intros.
    unfold confined. intros.
    destruct H4. destruct H5 ; unpack ; subst.
    + destruct H5 ; unpack ; subst.
      - split ; rewrite set_in_union_eq ; left ;
          stdomain_tac.
      - split ; rewrite set_in_union_eq ; [right|left] ;
          stdomain_tac. rewrite in_single_eq. auto.
    + split ; rewrite set_in_union_eq ; [right|left] ;
          stdomain_tac. rewrite in_single_eq. auto.
  Qed.  

  Lemma insert_rootisindomain_if_bst : forall F x n u k,  
      Inv p D F V W ->
      n \notin D ->
      F p x u ->
      (forall y y' o, F p y o -> y' \in descendants F y -> (orientation_op o) k (V y')) ->
      rootisindomain n (D \u '{n}).
  Proof.
    intros.
    unfold rootisindomain.
    rewrite set_in_union_eq. right. rewrite in_single_eq. auto.
  Qed.
  
  Lemma insert_isroot_no_parent_if_bst : forall F x n u k x0 o,  
      Inv p D F V W ->
      n \notin D ->
      orientation_op u (V p) k ->
      F p x u -> 
      (forall y y' o, F p y o -> y' \in descendants F y -> (orientation_op o) k (V y')) ->
      x0 \in D \u '{n} ->
      ¬ (remove_edge (add_edge (add_edge F n p (invert_orientation u)) n x u) p x) x0 n o.
  Proof.
    intros. intro.
    destruct H4. destruct H5.
    + destruct H6 ; unpack ; subst.
      - destruct H6 ; unpack ; subst.
        * apply H0. stdomain_tac.
        * apply H0. auto.
      - apply H0. stdomain_tac.
    + destruct H5 ; unpack ; subst.
      - destruct H6 ; unpack ; subst.
        * destruct H6 ; unpack ; subst.
          { apply H0. stdomain_tac. }
          { apply H0. stdomain_tac. }
        * apply H0. stdomain_tac.
  Qed.

  Lemma insert_isroot_path_to_all_if_bst : forall F x n u k x0,  
      Inv p D F V W ->
      n \notin D ->
      orientation_op u (V p) k ->
      F p x u -> 
      (forall y y' o, F p y o -> y' \in descendants F y -> (orientation_op o) k (V y')) ->
      x0 \in D \u '{n} ->
      path (remove_edge (add_edge (add_edge F n p (invert_orientation u)) n x u) p x) n x0.
  Proof.
    intros.
    rewrite set_in_union_eq in H4.
    destruct H4.
    + assert (path F p x0). stpath_tac.
      apply path_implies_path_add_memory in H5.
      destruct H5.
      assert (exists l, rev l = x1). exists (rev x1). rewrite rev_involutive. auto.
      destruct H6. rewrite <- H6 in *. clear dependent x1.
      generalize dependent x0.
      induction x2 ; simpl in * ; intros.
      - inversion H5 ; subst.
        * apply path_single with (invert_orientation u). split.
          { right.  intro. subst. stlink_tac. }
          { left. right. auto. }
        * apply app_eq_nil in H6. unpack ; subst.
          discriminate.
      - inversion H5 ; unpack ; subst.
        * symmetry in H10. apply app_eq_nil in H10.
          unpack ; subst. discriminate.
        * symmetry in H6. apply app_eq_unit in H6.
          destruct H6 ; unpack ; subst ; try discriminate.
          inversion H6 ; subst.
          destruct (classic (o = u)) ; subst.
          { assert (x0 = x). stlink_tac. subst.
            apply path_single with u.
            split. rewrite <- not_and_eq. intro ; unpack ; subst.
            apply H0. stdomain_tac.
            right. auto.
          }
          {
            apply path_trans with p ; auto.
            { apply path_single with (invert_orientation u).
              split. rewrite <- not_and_eq. intro ; unpack ; subst.
              stlink_tac.
              left. right. auto.
            }
            {
              destruct (classic (o = u)) ; subst.
              + contradiction.
              + apply path_single with o.
                split. rewrite <- not_and_eq. intro ; unpack ; subst.
                apply H8. stlink_tac.
                left. left. auto.
            }
          }
        * apply app_inj_tail in H6 ; unpack ; subst.
          destruct (classic (p = a)) ; subst.
          { destruct (classic (o = u)) ; subst.
            + assert (x0 = x). stlink_tac. subst.
              apply path_single with u.
              split.
              left. intro ; subst a. apply H0. stdomain_tac.
              right. auto.
            + apply path_trans with a.
              - apply path_single with (invert_orientation u).
                split. left. intro ; subst. apply H0.
                stdomain_tac.
                left. right. auto.
              - apply path_single with o.
                split. right. intro ; subst.
                apply H6. stlink_tac.
                left. left. auto.
          }
          {
          specialize (IHx2 a).
          apply path_trans with a.
          { apply IHx2 ; auto. stdomain_tac. }
          { apply path_single with o. split. auto.
            left. left. auto. }
          }            
    + rewrite in_single_eq in H4. subst.
          stpath_tac.
  Qed.
  
  Lemma insert_isroot_if_bst : forall F x n u k,  
      Inv p D F V W ->
      n \notin D ->
      orientation_op u (V p) k ->
      F p x u -> 
      (forall y y' o, F p y o -> y' \in descendants F y -> (orientation_op o) k (V y')) ->
      isroot (D \u '{n}) (remove_edge (add_edge (add_edge F n p (invert_orientation u)) n x u) p x) n.
  Proof.
    unfold isroot.
    intros.
    split.
    + apply insert_isroot_no_parent_if_bst with k ; auto.
    + apply insert_isroot_path_to_all_if_bst with k ; auto.
  Qed.

  Lemma insert_searchtree_if_bst : forall F x n u k,  
      Inv p D F V W ->
      n \notin D ->
      orientation_op u (V p) k ->
      F p x u -> 
      (forall y y' o, F p y o -> y' \in descendants F y -> (orientation_op o) k (V y')) ->
      searchtree (remove_edge (add_edge (add_edge F n p (invert_orientation u)) n x u) p x)
                 (update_value V n k).
  Proof.
    unfold searchtree.
    intros.
    assert (¬(p = n)).
    intro. subst. apply H0. stdomain_tac.
    split ; intros ; unpack.
    + destruct H5.
      destruct H7 ; unpack ; subst.
      - destruct H7.
        * unfold update_value.
          destruct (bool_decide (x0 = n)) eqn:E1 ; subst ; simpl in * ;
            [apply bool_decide_eq_true_1 in E1 ; subst;exfalso;apply H0 ; stdomain_tac|].
          destruct (bool_decide (y = n)) eqn:E2 ; subst ; simpl in * ;
            [apply bool_decide_eq_true_1 in E2 ; subst;exfalso;apply H0 ; stdomain_tac|].
          destruct (bool_decide (z = n)) eqn:E3 ; subst ; simpl in *.
          {
            apply bool_decide_eq_true_1 in E3. subst.
            apply remove_edge_inv in H6.
            apply add_edge_if_no_path_inv in H6.
            apply add_edge_if_no_path_inv in H6.
            exfalso. apply H0.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F x0 y LEFT n H H7 H6).
            unpack ; auto.
            intro.
            apply H0.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F x0 y LEFT n H H7 H8).
            unpack ; auto.
            intro.
            apply H0.
            apply add_edge_if_no_path_inv in H8.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F x0 y LEFT n H H7 H8).
            unpack ; auto.
            intro.
            apply H0.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F x0 y LEFT n H H7 H9).
            unpack ; auto. 
          }
          {
            apply remove_edge_inv in H6.
            apply add_edge_if_no_path_inv in H6.
            apply add_edge_if_no_path_inv in H6.
            split ; try stlink_tac ; stpath_tac.
            intro. 
            apply H0.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F x0 y LEFT n H H7 H8).
            unpack ; auto.
            intro.
            apply add_edge_if_no_path_inv in H8.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F x0 y LEFT n H H7 H8).
            unpack ; auto.
            intro.
            apply H0.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F x0 y LEFT n H H7 H9).
            unpack ; auto.
          }
        * unpack ; subst.
          destruct u ; simpl ; try discriminate ; simpl in *.          
          unfold update_value.
          destruct (bool_decide (n = n)) eqn:E ; subst ; simpl in * ;      
            [|apply bool_decide_eq_false_1 in E ; contradiction].
          destruct (bool_decide (p = n)) eqn:E1 ; subst ; simpl in * ; 
            [apply bool_decide_eq_true_1 in E1 ; contradiction|].
          apply three_option_path_x_y in H6.
          destruct H6 as [H6 | [H6 | H6]] ; subst.
          { rewrite E1. lia. }
          { do 2destruct H6.
            destruct H6. destruct H8 ; unpack ; subst ; [|lia].
            destruct H8 ; unpack ; try discriminate.
            destruct (bool_decide (z = n)) eqn:E2 ; subst ; simpl in *.
            + apply bool_decide_eq_true_1 in E2 ; subst.
              apply remove_edge_inv in H7.
              apply add_edge_if_no_path_inv in H7.
              apply add_edge_if_no_path_inv in H7.
              assert (path F p n). stpath_tac. 
              exfalso ; apply H0. stdomain_tac.
              intro.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac.
              intro.
              apply add_edge_if_no_path_inv in H10.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac. intro.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac.
            + split ; [lia|]. destruct H6 ; try contradiction.
              exfalso ; apply H6. stlink_tac.
          }
          {
            do 2destruct H6.
            destruct H6. destruct H8 ; unpack ; subst ; [|lia].
            destruct H8 ; unpack ; subst ; [|exfalso ;apply H0 ; stdomain_tac].
            destruct (bool_decide (z = n)) eqn:E2 ; subst ; simpl in *.
            + apply bool_decide_eq_true_1 in E2 ; subst.
              apply remove_edge_inv in H7.
              apply add_edge_if_no_path_inv in H7.
              apply add_edge_if_no_path_inv in H7.
              assert (path F p n). stpath_tac. 
              exfalso ; apply H0. stdomain_tac.
              intro.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac.
              intro.
              apply add_edge_if_no_path_inv in H10.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac. intro.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac.
            + split ; [lia|]. 
              apply remove_edge_inv in H7.
              apply add_edge_if_no_path_inv in H7.
              apply add_edge_if_no_path_inv in H7.
              assert (V p > V z). stpath_tac. lia.
              intro. assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac.
              intro.
              apply add_edge_if_no_path_inv in H10.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac.
              intro.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac.
          }
      - unfold update_value.
        destruct (bool_decide (n = n)) eqn:E ; subst ; simpl in * ;      
          [|apply bool_decide_eq_false_1 in E ; contradiction].
        destruct (bool_decide (x = n)) eqn:E1 ; subst ; simpl in *.
        apply bool_decide_eq_true_1 in E1 ; subst. exfalso. apply H0.
        stdomain_tac.
        destruct (bool_decide (z = n)) eqn:E2 ; subst ; simpl in *.
        apply bool_decide_eq_true_1 in E2 ; subst.
        { apply remove_edge_inv in H6.
          apply add_edge_if_no_path_inv in H6.
          apply add_edge_if_no_path_inv in H6.
          assert (path F p n). stpath_tac.
          exfalso ; apply H0. stdomain_tac.
          intro. assert (path F p n). stpath_tac.
          apply H0. stdomain_tac.
          intro. apply add_edge_if_no_path_inv in H7.
          assert (path F p n). stpath_tac.
          apply H0. stdomain_tac.
          intro. assert (path F p n). stpath_tac.
          apply H0. stdomain_tac. }          
        { split.
        * specialize (H3 x x LEFT H2).
          apply H3. rewrite in_set_st_eq. stpath_tac.
        * apply remove_edge_inv in H6.
          apply add_edge_if_no_path_inv in H6.
          apply add_edge_if_no_path_inv in H6.
          { specialize (H3 x z LEFT H2).
            apply H3. rewrite in_set_st_eq. auto. }
          { intro.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F p x LEFT n).
            apply H8 in H7 ; auto ; unpack.
            apply H0. auto.
          }
          { intro.
            apply add_edge_if_no_path_inv in H7.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F p x LEFT n).
            apply H8 in H7 ; auto ; unpack.
            apply H0. auto.
            intro.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F p x LEFT n).
            apply H9 in H8 ; auto ; unpack.
            apply H0. auto.          
          }
        }        
    + destruct H5.
      destruct H7 ; unpack ; subst.
      - destruct H7.
        * unfold update_value.
          destruct (bool_decide (x0 = n)) eqn:E1 ; subst ; simpl in * ;
            [apply bool_decide_eq_true_1 in E1 ; subst;exfalso;apply H0 ; stdomain_tac|].
          destruct (bool_decide (y = n)) eqn:E2 ; subst ; simpl in * ;
            [apply bool_decide_eq_true_1 in E2 ; subst;exfalso;apply H0 ; stdomain_tac|].
          destruct (bool_decide (z = n)) eqn:E3 ; subst ; simpl in *.
          {
            apply bool_decide_eq_true_1 in E3. subst.
            apply remove_edge_inv in H6.
            apply add_edge_if_no_path_inv in H6.
            apply add_edge_if_no_path_inv in H6.
            exfalso. apply H0.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F x0 y RIGHT n H H7 H6).
            unpack ; auto.
            intro.
            apply H0.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F x0 y RIGHT n H H7 H8).
            unpack ; auto.
            intro.
            apply H0.
            apply add_edge_if_no_path_inv in H8.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F x0 y RIGHT n H H7 H8).
            unpack ; auto.
            intro.
            apply H0.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F x0 y RIGHT n H H7 H9).
            unpack ; auto. 
          }
          {
            apply remove_edge_inv in H6.
            apply add_edge_if_no_path_inv in H6.
            apply add_edge_if_no_path_inv in H6.
            split ; try stlink_tac ; stpath_tac.
            intro. 
            apply H0.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F x0 y RIGHT n H H7 H8).
            unpack ; auto.
            intro.
            apply add_edge_if_no_path_inv in H8.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F x0 y RIGHT n H H7 H8).
            unpack ; auto.
            intro.
            apply H0.
            pose proof (in_domain_if_edge_and_path_if_bst p D V W F x0 y RIGHT n H H7 H9).
            unpack ; auto.
          }
        * unpack ; subst.
          destruct u ; simpl ; try discriminate ; simpl in *.          
          unfold update_value.
          destruct (bool_decide (n = n)) eqn:E ; subst ; simpl in * ;      
            [|apply bool_decide_eq_false_1 in E ; contradiction].
          destruct (bool_decide (p = n)) eqn:E1 ; subst ; simpl in * ; 
            [apply bool_decide_eq_true_1 in E1 ; contradiction|].
          apply three_option_path_x_y in H6.
          destruct H6 as [H6 | [H6 | H6]] ; subst.
          { rewrite E1. lia. }
          {
            do 2destruct H6.
            destruct H6. destruct H8 ; unpack ; subst ; [|lia].
            destruct H8 ; unpack ; subst ; [|exfalso ;apply H0 ; stdomain_tac].
            destruct (bool_decide (z = n)) eqn:E2 ; subst ; simpl in *.
            + apply bool_decide_eq_true_1 in E2 ; subst.
              apply remove_edge_inv in H7.
              apply add_edge_if_no_path_inv in H7.
              apply add_edge_if_no_path_inv in H7.
              assert (path F p n). stpath_tac. 
              exfalso ; apply H0. stdomain_tac.
              intro.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac.
              intro.
              apply add_edge_if_no_path_inv in H10.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac. intro.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac.
            + split ; [lia|]. 
              apply remove_edge_inv in H7.
              apply add_edge_if_no_path_inv in H7.
              apply add_edge_if_no_path_inv in H7.
              assert (V p < V z). stpath_tac. lia.
              intro. assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac.
              intro.
              apply add_edge_if_no_path_inv in H10.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac.
              intro.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac.
          }
          { do 2destruct H6.
            destruct H6. destruct H8 ; unpack ; subst ; [|lia].
            destruct H8 ; unpack ; try discriminate.
            destruct (bool_decide (z = n)) eqn:E2 ; subst ; simpl in *.
            + apply bool_decide_eq_true_1 in E2 ; subst.
              apply remove_edge_inv in H7.
              apply add_edge_if_no_path_inv in H7.
              apply add_edge_if_no_path_inv in H7.
              assert (path F p n). stpath_tac. 
              exfalso ; apply H0. stdomain_tac.
              intro.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac.
              intro.
              apply add_edge_if_no_path_inv in H10.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac. intro.
              assert (path F p n). stpath_tac. 
              apply H0. stdomain_tac.
            + split ; [lia|]. destruct H6 ; try contradiction.
              exfalso ; apply H6. stlink_tac.
          }
      - unfold update_value.
        destruct (bool_decide (n = n)) eqn:E ; subst ; simpl in * ;      
          [|apply bool_decide_eq_false_1 in E ; contradiction].
        destruct (bool_decide (x = n)) eqn:E1 ; subst ; simpl in *.
        apply bool_decide_eq_true_1 in E1 ; subst. exfalso. apply H0.
        stdomain_tac.
        destruct (bool_decide (z = n)) eqn:E2 ; subst ; simpl in *.
        apply bool_decide_eq_true_1 in E2 ; subst.
        { apply remove_edge_inv in H6.
          apply add_edge_if_no_path_inv in H6.
          apply add_edge_if_no_path_inv in H6.
          assert (path F p n). stpath_tac.
          exfalso ; apply H0. stdomain_tac.
          intro. assert (path F p n). stpath_tac.
          apply H0. stdomain_tac.
          intro. apply add_edge_if_no_path_inv in H7.
          assert (path F p n). stpath_tac.
          apply H0. stdomain_tac.
          intro. assert (path F p n). stpath_tac.
          apply H0. stdomain_tac. }          
        { split.
          * specialize (H3 x x RIGHT H2).
            apply H3. rewrite in_set_st_eq. stpath_tac.
          * apply remove_edge_inv in H6.
            apply add_edge_if_no_path_inv in H6.
            apply add_edge_if_no_path_inv in H6.
            { specialize (H3 x z RIGHT H2).
              apply H3. rewrite in_set_st_eq. auto. }
            { intro.
              pose proof (in_domain_if_edge_and_path_if_bst p D V W F p x RIGHT n).
              apply H8 in H7 ; auto ; unpack.
              apply H0. auto.
            }
            { intro.
              apply add_edge_if_no_path_inv in H7.
              pose proof (in_domain_if_edge_and_path_if_bst p D V W F p x RIGHT n).
              apply H8 in H7 ; auto ; unpack.
              apply H0. auto.
              intro.
              pose proof (in_domain_if_edge_and_path_if_bst p D V W F p x RIGHT n).
              apply H9 in H8 ; auto ; unpack.
              apply H0. auto.          
            }
        }        
  Qed.

  Lemma insert_binarytree_if_bst : forall F x n u k,  
      Inv p D F V W ->
      n \notin D ->
      orientation_op u (V p) k ->
      F p x u -> 
      (forall y y' o, F p y o -> y' \in descendants F y -> (orientation_op o) k (V y')) ->
      binarytree (remove_edge (add_edge (add_edge F n p (invert_orientation u)) n x u) p x).
  Proof.
    intros.
    unfold binarytree.
    inversion H.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    intros.
    destruct H5, H6.
    destruct H7, H8 ; unpack ; subst.
    + destruct H7, H8 ; unpack ; subst.
      - apply (binarytree x0 y z l r) ; auto.
      - exfalso. apply H0. stdomain_tac.
      - exfalso. apply H0. stdomain_tac.
      - contradiction.
    + destruct H7.
      - exfalso ; apply H0. stdomain_tac.
      - unpack ; subst. intro. storientation_tac.
    + destruct H8 ; unpack ; subst.
      - exfalso ; apply H0. stdomain_tac.
      - intro. storientation_tac.
    + contradiction.
  Qed.

  Lemma insert_if_bst : forall F x n u k,  
      Inv p D F V W ->
      n \notin D ->
      orientation_op u (V p) k ->
      F p x u -> 
      (forall y y' o, F p y o -> y' \in descendants F y -> (orientation_op o) k (V y')) ->
      Inv n (D \u \{n}) (remove_edge (add_edge (add_edge F n p (invert_orientation u)) n x u) p x) (update_value V n k) W.
  Proof.
    intros.
    constructor. unfold is_bst.
    split ; auto.
    (* confined *)
    apply (insert_confined_if_bst F x n u k) ; auto.
    split ; auto.
    (*rootisindomain*)
    apply (insert_rootisindomain_if_bst F x n u k) ; auto.
    split ; auto.
    (*isroot*)
    apply (insert_isroot_if_bst F x n u k) ; auto.
    split ; auto.
    (*searchtree*)
    apply (insert_searchtree_if_bst F x n u k) ; auto.
    split ; auto.
    apply (insert_binarytree_if_bst F x n u k) ; auto.
    inversion H. unfold is_bst in Inv_bst.
    unpack. split ; auto.
    apply finite_union ; auto.
    apply finite_single.
  Qed.

  Lemma insert'_confined_if_bst : forall F n u k,  
      Inv p D F V W ->
      n \notin D ->
      orientation_op u (V p) k ->
      ¬(exists x, F p x u) -> 
      (forall y y' o, F p y o -> y' \in descendants F y -> (orientation_op o) k (V y')) ->
      confined (D \u '{n}) (add_edge F n p (invert_orientation u)).
  Proof.
    intros.
    unfold confined. intros.
    destruct H4. 
    + split ; rewrite set_in_union_eq ;
        left ; stdomain_tac.
    + unpack ; subst.
      split ; rewrite set_in_union_eq.
      right. rewrite in_single_eq. auto.
      left. stdomain_tac.
  Qed.  

  Lemma insert'_isroot_if_bst : forall F n u k,  
      Inv p D F V W ->
      n \notin D ->
      orientation_op u (V p) k ->
      ¬(exists x, F p x u) -> 
      (forall y y' o, F p y o -> y' \in descendants F y -> (orientation_op o) k (V y')) ->
      isroot (D \u '{n}) (add_edge F n p (invert_orientation u)) n.
  Proof.
    intros.
    split.
    + intro. destruct H5 ; unpack ; subst.
      - apply H0. stdomain_tac.
      - apply H0. stdomain_tac.
    + rewrite set_in_union_eq in H4.
      destruct H4.
      - assert (path F p x). stpath_tac.
        apply path_implies_path_add_memory in H5.
        destruct H5.
        assert (exists l, rev l = x0). exists (rev x0). rewrite rev_involutive. auto.
        destruct H6. rewrite <- H6 in *. subst.
        generalize dependent x.
        induction x1 ; intros.
        * inversion H5 ; subst.
          { apply path_single with (invert_orientation u).
            right. auto.
          }
          { apply app_eq_nil in H6.
            destruct H6 ; unpack ; discriminate.
          }
        * inversion H5 ; subst.
          { symmetry in H10.
            apply app_eq_nil in H10. unpack ; discriminate.
          }
          { symmetry in H6.
            apply app_eq_unit in H6. destruct H6 ; unpack ; try discriminate.
            inversion H7 ; subst.
            apply path_trans with p ; auto.
            - apply path_single with (invert_orientation u).
              right. auto.
            - apply path_single with o0.
              left. auto.
          }
          { apply app_inj_tail in H6.
            unpack ; subst. apply IHx1 in H11 ; stdomain_tac.
            apply path_trans with a ; auto.
            apply path_single with o0.
            left. auto.
          }
      - rewrite in_single_eq in H4. subst. stpath_tac.        
  Qed.

  Lemma insert'_binarytree_if_bst : forall F n u k,  
      Inv p D F V W ->
      n \notin D ->
      orientation_op u (V p) k ->
      ¬(exists x, F p x u) -> 
      (forall y y' o, F p y o -> y' \in descendants F y -> (orientation_op o) k (V y')) ->
      binarytree (add_edge F n p (invert_orientation u)).
  Proof.
    intros.
    inversion H.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    unfold STpredicate.binarytree in *.
    intros. destruct H5, H6 ; unpack ; subst.
    + specialize (binarytree x y z l r). auto.
    + exfalso. apply H0. stdomain_tac.
    + exfalso. apply H0. stdomain_tac.
    + contradiction.
  Qed.

  Lemma insert'_searchtree_if_bst : forall F n u k,  
      Inv p D F V W ->
      n \notin D ->
      orientation_op u (V p) k ->
      ¬(exists x, F p x u) -> 
      (forall y y' o, F p y o -> y' \in descendants F y -> (orientation_op o) k (V y')) ->
      searchtree (add_edge F n p (invert_orientation u)) (update_value V n k).
  Proof.
    intros.
    unfold searchtree.
    split ; intros ; unpack.
    + destruct H4.
      - unfold update_value.
        destruct (bool_decide (x = n)) eqn:E1 ; subst ; simpl in * ;
          [apply bool_decide_eq_true_1 in E1 ; subst;exfalso;apply H0 ; stdomain_tac|].
        destruct (bool_decide (y = n)) eqn:E2 ; subst ; simpl in * ;
          [apply bool_decide_eq_true_1 in E2 ; subst;exfalso;apply H0 ; stdomain_tac|].
        destruct (bool_decide (z = n)) eqn:E3 ; subst ; simpl in *.
        * apply bool_decide_eq_true_1 in E3. subst.
          apply add_edge_if_no_path_inv in H5.
          exfalso ; apply H0.
          pose proof (in_domain_if_edge_and_path_if_bst p D V W F x y LEFT n H H4 H5).
          unpack ; auto.
          intro. exfalso ; apply H0.
          pose proof (in_domain_if_edge_and_path_if_bst p D V W F x y LEFT n H H4 H6).
          unpack ; auto.
        * split ; stlink_tac.
          apply add_edge_if_no_path_inv in H5.
          stpath_tac.
          intro. 
          pose proof (in_domain_if_edge_and_path_if_bst p D V W F x y LEFT n H H4 H6).
          unpack ; auto.
      - unpack ; subst. destruct u ; simpl in * ; try discriminate.
        unfold update_value.
        destruct (bool_decide (n = n)) eqn:E1 ; subst ; simpl in * ;
          [|apply bool_decide_eq_false_1 in E1 ; subst;exfalso;contradiction]. 
        destruct (bool_decide (p = n)) eqn:E2 ; subst ; simpl in * ;
          [apply bool_decide_eq_true_1 in E2 ; subst;exfalso;apply H0 ; stdomain_tac|].
        destruct (bool_decide (z = n)) eqn:E3 ; subst ; simpl in *.
        * apply bool_decide_eq_true_1 in E3. subst.
          apply add_edge_if_no_path_inv in H5.
          exfalso ; apply H0. stdomain_tac.
          intro. exfalso ; apply H0. stdomain_tac.
        * split ; stlink_tac ; try lia.
          apply add_edge_if_no_path_inv in H5.
          { apply (three_option_path_x_y F) in H5.
            destruct H5 as [H5 | [H5 | H5]] ; subst ; try lia.
            + destruct H5 ; unpack. exfalso ; eauto.
            + destruct H5 ; unpack. assert (V p > V z).
              stpath_tac. lia.
          }
          { intro. apply H0. stdomain_tac. }
    + destruct H4.
      - unfold update_value.
        destruct (bool_decide (x = n)) eqn:E1 ; subst ; simpl in * ;
          [apply bool_decide_eq_true_1 in E1 ; subst;exfalso;apply H0 ; stdomain_tac|].
        destruct (bool_decide (y = n)) eqn:E2 ; subst ; simpl in * ;
          [apply bool_decide_eq_true_1 in E2 ; subst;exfalso;apply H0 ; stdomain_tac|].
        destruct (bool_decide (z = n)) eqn:E3 ; subst ; simpl in *.
        * apply bool_decide_eq_true_1 in E3. subst.
          apply add_edge_if_no_path_inv in H5.
          exfalso ; apply H0.
          pose proof (in_domain_if_edge_and_path_if_bst p D V W F x y RIGHT n H H4 H5).
          unpack ; auto.
          intro. exfalso ; apply H0.
          pose proof (in_domain_if_edge_and_path_if_bst p D V W F x y RIGHT n H H4 H6).
          unpack ; auto.
        * split ; stlink_tac.
          apply add_edge_if_no_path_inv in H5.
          stpath_tac.
          intro. 
          pose proof (in_domain_if_edge_and_path_if_bst p D V W F x y RIGHT n H H4 H6).
          unpack ; auto.
      - unpack ; subst. destruct u ; simpl in * ; try discriminate.
        unfold update_value.
        destruct (bool_decide (n = n)) eqn:E1 ; subst ; simpl in * ;
          [|apply bool_decide_eq_false_1 in E1 ; subst;exfalso;contradiction]. 
        destruct (bool_decide (p = n)) eqn:E2 ; subst ; simpl in * ;
          [apply bool_decide_eq_true_1 in E2 ; subst;exfalso;apply H0 ; stdomain_tac|].
        destruct (bool_decide (z = n)) eqn:E3 ; subst ; simpl in *.
        * apply bool_decide_eq_true_1 in E3. subst.
          apply add_edge_if_no_path_inv in H5.
          exfalso ; apply H0. stdomain_tac.
          intro. exfalso ; apply H0. stdomain_tac.
        * split ; stlink_tac ; try lia.
          apply add_edge_if_no_path_inv in H5.
          { apply (three_option_path_x_y F) in H5.
            destruct H5 as [H5 | [H5 | H5]] ; subst ; try lia.
            + destruct H5 ; unpack. assert (V p < V z).
              stpath_tac. lia.
            + destruct H5 ; unpack. exfalso ; eauto.
          }
          { intro. apply H0. stdomain_tac. }
  Qed.

  Lemma insert'_if_bst : forall F n u k,  
      Inv p D F V W ->
      n \notin D ->
      orientation_op u (V p) k ->
      ¬(exists x, F p x u) -> 
      (forall y y' o, F p y o -> y' \in descendants F y -> (orientation_op o) k (V y')) ->
      Inv n (D \u \{n}) (add_edge F n p (invert_orientation u)) (update_value V n k) W.
  Proof.
    intros.
    constructor. unfold is_bst.
    split ; auto.
    (* confined *)
    apply (insert'_confined_if_bst F n u k) ; auto.
    split ; auto.
    (*rootisindomain*)
    unfold rootisindomain. rewrite set_in_union_eq.
    rewrite in_single_eq. right. auto.
    split ; auto.
    (*isroot*)
    apply (insert'_isroot_if_bst F n u k) ; auto.
    split ; auto.
    (*searchtree*)
    apply (insert'_searchtree_if_bst F n u k) ; auto.
    split ; auto.
    apply (insert'_binarytree_if_bst F n u k) ; auto.
    inversion H. unfold is_bst in Inv_bst.
    unpack. split ; auto.
    apply finite_union ; auto.
    apply finite_single.
  Qed.  
  
End SplayTreeInsertFunctional.
