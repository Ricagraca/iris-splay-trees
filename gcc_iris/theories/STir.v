From ST Require Import STorientation STpredicate STlink STdomain STpath STedgeset
     STedgesetrotateroot STvaluefunction STpathcount.

From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual LibInt.
From stdpp Require Import gmap.
From iris.bi Require Import big_op.
From iris_time.heap_lang Require Import proofmode.
From iris_time Require Import Combined.
Require Import Coq.Lists.List.
Import ListNotations.

Section IterativeRotation.
  
  Variable p : elem.
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* weight of node *)
    
  Inductive bw_ir : EdgeSet -> (elem -> Z) -> elem -> elem -> Z -> nat ->
                     EdgeSet -> STpathcount.state -> Prop :=
    
    (*BASE CASES*)

    bw_ir_found_root : forall F V p, bw_ir F V p p (V p) O F ENDED

  (***)

  (*Trying to rotate left at root with no son*)
  | bw_ir_rl_fail : forall F V p z,
      z < V p ->
      ¬(exists y, F p y LEFT) ->
      bw_ir F V p p z O F ENDED

  (*Trying to rotate right at root with no son*)
  | bw_ir_rr_fail : forall F V p z,
      V p < z ->
      ¬(exists y, F p y RIGHT) ->
      bw_ir F V p p z O F ENDED

  (* Rotate left, found left child with no right grandchild *)
  | bw_ir_rl_root_nrgc_found : forall (F : EdgeSet) V p x z,
      z < V p -> 
      F p x LEFT -> 
      z = V x \/ V x < z \/ (z < V x /\ ¬(exists t, F x t LEFT)) -> 
      ¬(exists t, F x t RIGHT) -> 
      bw_ir F V p x z 1 (add_edge (remove_edge F p x) x p RIGHT) ENDED

  (* Rotate left, found left child with right grandchild *)
  | bw_ir_rl_root_rgc_found : forall (F : EdgeSet) V p x y z,
      z < V p -> 
      F p x LEFT -> 
      z = V x  \/ (z < V x /\ ¬(exists t, F x t LEFT)) -> 
      F x y RIGHT -> 
      bw_ir F V p x z 1 (update_edge (update_edge F x y p RIGHT) p x y LEFT) ENDED

  (* Rotate right, found right child with no left grandchild *)
  | bw_ir_rr_root_nlgc_found : forall (F : EdgeSet) V p x z,
      V p < z -> 
      F p x RIGHT -> 
      z = V x \/ z < V x \/ (V x < z /\ ¬(exists t, F x t RIGHT)) -> 
      ¬(exists t, F x t LEFT) -> 
      bw_ir F V p x z 1 (add_edge (remove_edge F p x) x p LEFT) ENDED

  (* Rotate right, found right child with left grandchild *)
  | bw_ir_rr_root_lgc_found : forall (F : EdgeSet) V p x y z,
      V p < z -> 
      F p x RIGHT -> 
      z = V x \/ (V x < z /\ ¬(exists t, F x t RIGHT)) -> 
      F x y LEFT -> 
      bw_ir F V p x z 1 (update_edge (update_edge F x y p LEFT) p x y RIGHT) ENDED

  (* Two rotates *)
            
  (* Rotate child then root without grand child*)
  | bw_ir_oo_child_nlgc : forall (F : EdgeSet) V p x y z o,
      (orientation_op o) (V p) z -> 
      F p x o ->
      (orientation_op o) (V x) z ->
      F x y o -> 
      ¬(exists t, F y t (invert_orientation o)) ->

      (* rotation on children *)
      let D' := (descendants F x) in
      let F' := (remove_edge_that_are_not_in_D F D') in 
      let FC' := (remove_edge_that_are_in_D F D') in
      let F'' := (remove_edge F' x y) in
      let F''' := (add_edge F'' y x (invert_orientation o)) in

      (*Edgeset after first rotation*)
      let Fafr := (add_edge (union_edge F''' FC') p y o) in 

      (* rotation on root *)
      let F1 := (update_edge Fafr p y x o) in 
      let F2 := (update_edge F1 y x p (invert_orientation o)) in 
      
      bw_ir F V p y z 2 F2 GOING
            
  | bw_ir_oo_child_lgc : forall (F : EdgeSet) V p x y z t o,
      (orientation_op o) (V p) z -> 
      F p x o -> 
      (orientation_op o) (V x) z -> 
      F x y o -> 
      F y t (invert_orientation o) ->

      (* rotation on children *)
      let D' := (descendants F x) in
      let F' := (remove_edge_that_are_not_in_D F D') in 
      let FC' := (remove_edge_that_are_in_D F D') in
      let F'' := (update_edge F' x y t o) in
      let F''' := (update_edge F'' y t x (invert_orientation o)) in
      

      (*Edgeset after first rotation*)
      let Fafr := (add_edge (union_edge F''' FC') p y o) in 

      (* rotation on root *)
      let F1 := (update_edge Fafr p y x o) in 
      let F2 := (update_edge F1 y x p (invert_orientation o)) in 
      
      bw_ir F V p y z 2 F2 GOING
            
  (* Rotate child then root right without grand child *)
  | bw_ir_oo'_child_nlgc : forall (F : EdgeSet) V p x y z o,
      (orientation_op o) (V p) z -> 
      F p x o ->
      (orientation_op (invert_orientation o)) (V x) z ->
      F x y (invert_orientation o) -> 
      ¬(exists t, F y t o) ->
      ¬(exists t, F y t (invert_orientation o)) ->

      (* rotation on children *)
      let D' := (descendants F x) in
      let F' := (remove_edge_that_are_not_in_D F D') in 
      let FC' := (remove_edge_that_are_in_D F D') in
      let F'' := (remove_edge F' x y) in
      let F''' := (add_edge F'' y x o) in

      (*Edgeset after first rotation*)
      let Fafr := (add_edge (union_edge F''' FC') p y o) in 

      (* rotation on root *)
      let F1 := (remove_edge Fafr p y) in 
      let F2 := (add_edge F1 y p (invert_orientation o)) in 
      
      bw_ir F V p y z 2 F2 GOING
            
  (* Rotate child then root right without grand child *)
  | bw_ir_oo'_child_lgc : forall (F : EdgeSet) V p x y t z o,
      (orientation_op o) (V p) z -> 
      F p x o ->
      (orientation_op (invert_orientation o)) (V x) z ->
      F x y (invert_orientation o) -> 
      ¬(exists t, F y t o) ->
      F y t (invert_orientation o) ->

      (* rotation on children *)
      let D' := (descendants F x) in
      let F' := (remove_edge_that_are_not_in_D F D') in 
      let FC' := (remove_edge_that_are_in_D F D') in
      let F'' := (remove_edge F' x y) in
      let F''' := (add_edge F'' y x o) in

      (*Edgeset after first rotation*)
      let Fafr := (add_edge (union_edge F''' FC') p y o) in 

      (* rotation on root *)
      let F1 := (update_edge Fafr p y t o) in 
      let F2 := (update_edge F1 y t p (invert_orientation o)) in 
      
      bw_ir F V p y z 2 F2 GOING
            
  (* Rotate child then root right without grand child *)
  | bw_ir_oo'_child_lgc_child : forall (F : EdgeSet) V p x y t z o,
      (orientation_op o) (V p) z -> 
      F p x o ->
      (orientation_op (invert_orientation o)) (V x) z ->
      F x y (invert_orientation o) -> 
      F y t o ->
      ¬(exists t, F y t (invert_orientation o)) ->

      (* rotation on children *)
      let D' := (descendants F x) in
      let F' := (remove_edge_that_are_not_in_D F D') in 
      let FC' := (remove_edge_that_are_in_D F D') in
      let F'' := (update_edge F' x y t (invert_orientation o)) in
      let F''' := (update_edge F'' y t x o) in

      (*Edgeset after first rotation*)
      let Fafr := (add_edge (union_edge F''' FC') p y o) in 

      (* rotation on root *)
      let F1 := (remove_edge Fafr p y) in 
      let F2 := (add_edge F1 y p (invert_orientation o)) in 
      
      bw_ir F V p y z 2 F2 GOING
            
  (* Rotate child then root right without grand child *)
  | bw_ir_oo'_child_gc_child : forall (F : EdgeSet) V p x y t1 t2 z o,
      (orientation_op o) (V p) z -> 
      F p x o ->
      (orientation_op (invert_orientation o)) (V x) z ->
      F x y (invert_orientation o) -> 
      F y t1 o ->
      F y t2 (invert_orientation o) ->

      (* rotation on children *)
      let D' := (descendants F x) in
      let F' := (remove_edge_that_are_not_in_D F D') in 
      let FC' := (remove_edge_that_are_in_D F D') in
      let F'' := (update_edge F' x y t1 (invert_orientation o)) in
      let F''' := (update_edge F'' y t1 x o) in

      (*Edgeset after first rotation*)
      let Fafr := (add_edge (union_edge F''' FC') p y o) in 

      (* rotation on root *)
      let F1 := (update_edge Fafr p y t2 o) in 
      let F2 := (update_edge F1 y t2 p (invert_orientation o)) in 
      
      bw_ir F V p y z 2 F2 GOING
            
  (***)
  
  (* INDUCTIVE CASES *)
            
  | bw_ir_ic_ind1 : forall (F F' F'' : EdgeSet) V p x y z n,
      bw_ir F V p x z 2 F' GOING ->
      bw_ir F' V x y z n F'' GOING ->
      bw_ir F V p y z (S (S n)) F'' GOING
            
  | bw_ir_ic_ind2 : forall (F F' F'' : EdgeSet) V p x y z n,
      bw_ir F V p x z 2 F' GOING ->
      bw_ir F' V x y z n F'' ENDED ->
      bw_ir F V p y z (S (S n)) F'' ENDED.
      
  Lemma bw_ir_inv : forall p F x n z F' s,
      Inv p D F V W ->
      bw_ir F V p x z n F' s ->
      Inv x D F' V W.
  Proof.
    intros.
    clear p. rename p0 into p.
    induction H0 ; subst ; auto.
    + pose proof (rotate_XE_if_bst p D W V F x LEFT).
      simpl in *. apply H4 ; auto.
    + pose proof (rotate_XI_if_bst p D W V F x y LEFT).
      simpl in *. apply update_comm_inv in H4 ; auto ; stlink_tac. 
    + pose proof (rotate_XE_if_bst p D W V F x RIGHT).
      simpl in *. apply H4 ; auto.
    + pose proof (rotate_XI_if_bst p D W V F x y RIGHT).
      simpl in *. apply update_comm_inv in H4 ; auto ; stlink_tac.
    + pose proof (child_if_inv p D W V F x o H H1).
      assert (F' x y o). repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (¬ (∃ y0 : elem, F' y y0 (invert_orientation o))).
      intro. destruct H7. apply H4. exists x0. destruct H7 ; unpack ; auto.
      pose proof (rotate_XE_if_bst x D' W V F' y o H5 H6 H7). simpl in H8.
      pose proof (join_if_inv p D W V F (add_edge (remove_edge F' x y) y x (invert_orientation o)) x y o).
      specialize (H9 H H1 H8).
      pose proof (rotate_XI_if_bst p D W V Fafr y x o H9).
      simpl in H10. apply H10 ; [right ; auto|left ; left ; right ; auto].
    + pose proof (child_if_inv p D W V F x o H H1).
      assert (F' x y o). repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' y t (invert_orientation o)). repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst x D' W V F' y t o H5 H6 H7).
      pose proof (join_if_inv p D W V F F''' x y o H H1 H8).
      pose proof (rotate_XI_if_bst p D W V Fafr y x o H9).
      simpl in H10. apply H10 ; [right ; auto|left ; left ; right ; auto].
    + pose proof (child_if_inv p D W V F x o H H1).
      assert (F' x y (invert_orientation o)). repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (¬ (∃ y0 : elem, F' y y0 o)). intro. apply H4. destruct H8.
      exists x0. destruct H8 ; unpack. auto.      
      pose proof (rotate_XE_if_bst x D' W V F' y (invert_orientation o) H6 H7 ).
      rewrite involutive_invert in H9. specialize (H9 H8).
      pose proof (join_if_inv p D W V F F''' x y o H H1 H9).
      pose proof (rotate_XE_if_bst p D W V Fafr y o H10).
      apply H11 ; [right ; auto|]. intro. destruct H12. apply H5.
      exists x0. destruct H12 ; unpack ; subst ; [|destruct o ; simpl in * ; discriminate].
      destruct H12 ; unpack ; subst ; [|destruct H12; auto].
      destruct H12 ; unpack ; subst ; [|destruct o ; simpl in * ; discriminate].
      destruct H12. destruct H13 ; unpack ; auto.
    + pose proof (child_if_inv p D W V F x o H H1).
      assert (F' x y (invert_orientation o)). repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (¬ (∃ y0 : elem, F' y y0 o)). intro. apply H4. destruct H8.
      exists x0. destruct H8 ; unpack. auto.      
      pose proof (rotate_XE_if_bst x D' W V F' y (invert_orientation o) H6 H7 ).
      rewrite involutive_invert in H9. specialize (H9 H8).
      pose proof (join_if_inv p D W V F F''' x y o H H1 H9).
      pose proof (rotate_XI_if_bst p D W V Fafr y t o H10).
      apply H11 ; [right ; auto|]. left. left. left.
      split ; [right ; stlink_tac|].
      split ; [rewrite in_set_st_eq ; stpath_tac|].
      split ; [rewrite in_set_st_eq ; stpath_tac|]. auto.
    + pose proof (child_if_inv p D W V F x o H H1).
      assert (F' x y (invert_orientation o)). repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' y t o). repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst x D' W V F' y t (invert_orientation o) H6 H7).
      rewrite involutive_invert in H9. specialize (H9 H8).
      pose proof (join_if_inv p D W V F F''' x y o H H1 H9).
      pose proof (rotate_XE_if_bst p D W V Fafr y o H10).
      apply H11 ; [right ; auto|]. intro. destruct H12. apply H5.
      exists x0. destruct H12 ; unpack ; subst ; [|destruct o ; simpl in * ; discriminate].
      destruct H12 ; unpack ; subst ; [|destruct H12; auto].
      destruct H12 ; unpack ; subst ; [|destruct o ; simpl in * ; discriminate].
      destruct H14 ; unpack ; subst ; [|destruct H12 ; contradiction].
      destruct H16 ; unpack ; subst ; auto.
    + pose proof (child_if_inv p D W V F x o H H1).
      assert (F' x y (invert_orientation o)). repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' y t1 o). repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst x D' W V F' y t1 (invert_orientation o) H6 H7).
      rewrite involutive_invert in H9. specialize (H9 H8).
      pose proof (join_if_inv p D W V F F''' x y o H H1 H9).
      pose proof (rotate_XI_if_bst p D W V Fafr y t2 o H10).
      apply H11 ; [right ; auto|]. left. left. left.
      split ; [right ; stlink_tac|].
      split ; [right ; stlink_tac|].  left.
      split ; [left;stlink_tac|].
      split ; [left;stlink_tac|].
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
  Qed.

  Lemma bw_add_end_state_going : forall F p x0 x z n F' F'', 
      bw_ir F V p  x0 z (2 * n) F' GOING ->
      bw_ir F' V x0 x z (2) F'' GOING ->
      bw_ir F V p x z (2*n + 2) F'' GOING .
  Proof.
    intros F p0 x0 x z n F' F''.
    generalize dependent F.
    generalize dependent F'.
    generalize dependent F''.
    generalize dependent x0.
    generalize dependent p0.
    induction n ; intros.
    + simpl in H. inversion H.
    + simpl in *.
      inversion H ; subst ; try (
                                destruct n ; simpl in * ; try lia ;
                                pose proof (bw_ir_ic_ind1 F F3 F'' V p0 x0 x z 2) ; auto
                              ).
      assert ((n0 = n + n)%nat). lia. subst.
      rewrite LibNat.plus_zero_r in IHn.
      clear H1. specialize (IHn x1 x0 F'' F' F'0 H8 H0).
      pose proof (bw_ir_ic_ind1 F  F'0 F'' V p0 x1 x z ((n+n)+2)).
      apply H1 ; auto.
  Qed.

  Lemma bw_add_end_state_end_0 : forall F p x0 x z n F' F'', 
      bw_ir F V p  x0 z (2 * n) F' GOING ->
      bw_ir F' V x0 x z (0) F'' ENDED ->
      bw_ir F V p x z (2*n) F'' ENDED .
  Proof.
    intros F p0 x0 x z n F' F''.
    generalize dependent F.
    generalize dependent F'.
    generalize dependent F''.
    generalize dependent x0.
    generalize dependent p0.
    induction n ; intros.
    + simpl in H. inversion H.
    + simpl in *.
      inversion H ; subst ;
        try (
            destruct n ; simpl in * ; try lia ;
            pose proof (bw_ir_ic_ind2 F F3 F'' V p0 x0 x z 0) ; auto
          ). 
      
      assert ((n0 = n + n)%nat). lia. subst.
      rewrite LibNat.plus_zero_r in IHn.
      clear H1. specialize (IHn x1 x0 F'' F' F'0 H8 H0).
      pose proof (bw_ir_ic_ind2 F  F'0 F'' V p0 x1 x z (n+n) H2 ).
      apply H1 ; auto.
  Qed.
  
  Lemma bw_add_end_state_end_1 : forall F p x0 x z n F' F'', 
      bw_ir F V p  x0 z (2 * n) F' GOING ->
      bw_ir F' V x0 x z (1) F'' ENDED ->
      bw_ir F V p x z (2*n + 1) F'' ENDED .
  Proof.
    intros F p0 x0 x z n F' F''.
    generalize dependent F.
    generalize dependent F'.
    generalize dependent F''.
    generalize dependent x0.
    generalize dependent p0.
    induction n ; intros.
    + simpl in H. inversion H.
    + simpl in *.
      inversion H ; subst ;
        try (
            destruct n ; simpl in * ; try lia ;
            pose proof (bw_ir_ic_ind2 F F3 F'' V p0 x0 x z 1) ; auto
          ). 
      
      assert ((n0 = n + n)%nat). lia. subst.
      rewrite LibNat.plus_zero_r in IHn.
      clear H1. specialize (IHn x1 x0 F'' F' F'0 H8 H0).
      pose proof (bw_ir_ic_ind2 F  F'0 F'' V p0 x1 x z (n+n + 1) H2 ).
      apply H1 ; auto.
  Qed.
  
  Lemma no_bw_ir_end_then_going : forall F z,
      ¬(exists F' x n, bw_ir F V p x z n F' ENDED) ->
      (forall n, (exists F' x, bw_ir F V p x z (2+2*n) F' GOING)).
  Proof.
    intros.
    induction n ; intros.
    + simpl.
      destruct (classic(exists x o, F p x o /\ (orientation_op o) (V p) z)).
    - do 2destruct H0 ; unpack.
      destruct (classic(exists y o, F x y o /\ (orientation_op o) (V x) z)).
      * do 2destruct H2. unpack.
        destruct (classic (x2 = x0)) ; subst.
        {
          destruct (classic(exists y, F x1 y (invert_orientation x0))).
          + destruct H4.
            pose proof (bw_ir_oo_child_lgc F V p x x1 z x2 x0 H1 H0 H3 H2 H4).
            eauto.
          + pose proof (bw_ir_oo_child_nlgc F V p x x1 z x0 H1 H0 H3 H2 H4).
            eauto.
        }
        {
          apply different_orientation_then_equal_invert in H4. subst.
          destruct (classic(exists y, F x1 y (x0))) ;
            destruct (classic(exists y, F x1 y (invert_orientation x0))).
          + destruct H4.
            destruct H5.
            pose proof (bw_ir_oo'_child_gc_child F V p x x1 x2 x3 z x0 H1 H0 H3 H2 H4 H5).
            eauto.
          + destruct H4.
            pose proof (bw_ir_oo'_child_lgc_child F V p x x1 x2 z x0 H1 H0 H3 H2 H4 H5).
            eauto.
          + destruct H5.
            pose proof (bw_ir_oo'_child_lgc F V p x x1 x2 z x0 H1 H0 H3 H2 H4 H5).
            eauto.
          + pose proof (bw_ir_oo'_child_nlgc F V p x x1 z x0 H1 H0 H3 H2 H4 H5).
            eauto.
        }
      * pose proof (Z.lt_trichotomy (z) (V x)).
        destruct H3 as [H3 | [H3 | H3]].
        { destruct (classic (exists x', F x x' (invert_orientation x0))) ;
            destruct x0 ; simpl in *.
          + destruct H4. 
            exfalso. apply H.
            exists ((update_edge (update_edge F x x0 p RIGHT) p x x0 LEFT)) x (S O).
            apply bw_ir_rl_root_rgc_found ; auto ; try lia.
            right. repeat split ; auto ; try lia. intro.
            apply H2. destruct H5. exists x1 LEFT. repeat split ; auto. simpl ; try lia.
          + destruct H4.
            exfalso. apply H2.
            exists (x0) LEFT. repeat split ; auto ; simpl ; try lia.
          + exfalso. apply H.
            exists (add_edge (remove_edge F p x) x p RIGHT) x (S O).
            apply bw_ir_rl_root_nrgc_found ; auto ; try lia.
            right. right. split ; auto.
            intro. apply H2. destruct H5. exists (x0) LEFT.
            split ; simpl ; auto ; lia.
          + destruct H4.
            exfalso. apply H.
            exists (add_edge (remove_edge F p x) x p LEFT) x (S O).
            apply bw_ir_rr_root_nlgc_found ; auto ; try lia.
            intro. apply H2. destruct H4. exists x0 LEFT.
            repeat split ; auto ; simpl ; try lia. 
        }
        { destruct (classic (exists x', F x x' (invert_orientation x0))) ;
            destruct x0 ; simpl in *.
          + destruct H4. 
            exfalso. apply H.
            exists ((update_edge (update_edge F x x0 p RIGHT) p x x0 LEFT)) x (S O).
            apply bw_ir_rl_root_rgc_found ; auto ; try lia.
          + destruct H4. 
            exfalso. apply H.
            exists ((update_edge (update_edge F x x0 p LEFT) p x x0 RIGHT)) x (S O).
            apply bw_ir_rr_root_lgc_found ; auto ; try lia.
          + exfalso. apply H.
            exists (add_edge (remove_edge F p x) x p RIGHT) x (S O).
            apply bw_ir_rl_root_nrgc_found ; auto ; try lia.
          + exfalso. apply H.
            exists (add_edge (remove_edge F p x) x p LEFT) x (S O).
            apply bw_ir_rr_root_nlgc_found ; auto ; try lia.
        }
        { destruct (classic (exists x', F x x' (invert_orientation x0))) ;
            destruct x0 ; simpl in *.
          + destruct H4. 
            exfalso. apply H2.
            exists (x0) RIGHT. repeat split ; auto.
          + destruct H4. 
            exfalso. apply H.
            exists ((update_edge (update_edge F x x0 p LEFT) p x x0 RIGHT)) x (S O).
            apply bw_ir_rr_root_lgc_found ; auto ; try lia.
            right. repeat split ; auto. intro.
            destruct H5. apply H2. exists x1 RIGHT.
            repeat split ; simpl ; auto.
          + exfalso. apply H.
            exists (add_edge (remove_edge F p x) x p RIGHT) x (S O).
            apply bw_ir_rl_root_nrgc_found ; auto ; try lia.
          + exfalso. apply H.
            exists (add_edge (remove_edge F p x) x p LEFT) x (S O).
            apply bw_ir_rr_root_nlgc_found ; auto ; try lia.
            right. right. repeat split ; simpl ; auto.
            intro. apply H2. destruct H5. exists x0 RIGHT.
            repeat split ; auto.
        }
    - exfalso. apply H. exists F p O.
      pose proof (Z.lt_trichotomy (z) (V p)).
      destruct H1 as [H1 | [H1 | H1]].
      * apply bw_ir_rl_fail ; auto.
        intro. apply H0. destruct H2.
        exists x LEFT. split ; auto. simpl. lia.
      * subst. apply bw_ir_found_root.
      * apply bw_ir_rr_fail ; auto.
        intro. apply H0. destruct H2.
        exists x RIGHT. split ; auto. 
      + destruct IHn. destruct H0.
        simpl. rename x into F'.
        destruct (classic(exists x o, F' x0 x o /\ (orientation_op o) (V x0) z)).
    - do 2destruct H1 ; unpack.
      destruct (classic(exists y o, F' x y o /\ (orientation_op o) (V x) z)).
      * do 2destruct H3. unpack.
        destruct (classic (x1 = x3)) ; subst.
        {
          destruct (classic(exists y, F' x2 y (invert_orientation x3))).
          + destruct H5.
            pose proof (bw_ir_oo_child_lgc F' V x0 x x2 z x1 x3 H2 H1 H4 H3 H5).
            replace (2 + 2*n)%nat with ((2 * S n))%nat in H0 ; try lia.
            apply (bw_add_end_state_going F p x0 x2 z (S n) F' ) in H6 ; auto.
            replace (S (S (S (n + S (n + 0)))))%nat with (2 * S n + 2)%nat ; try lia.              
            eauto.
          + pose proof (bw_ir_oo_child_nlgc F' V x0 x x2 z x3 H2 H1 H4 H3 H5).
            replace (2 + 2*n)%nat with ((2 * S n))%nat in H0 ; try lia.
            apply (bw_add_end_state_going F p x0 x2 z (S n) F' ) in H6 ; auto.
            replace (S (S (S (n + S (n + 0)))))%nat with (2 * S n + 2)%nat ; try lia.
            eauto.
        }
        {
          apply neq_sym in H5.
          apply different_orientation_then_equal_invert in H5. subst.
          destruct (classic(exists y, F' x2 y (x1))) ;
            destruct (classic(exists y, F' x2 y (invert_orientation x1))).
          + destruct H5.
            destruct H6.
            pose proof (bw_ir_oo'_child_gc_child F' V x0 x x2 x3 x4 z x1 H2 H1 H4 H3 H5 H6).
            replace (2 + 2*n)%nat with ((2 * S n))%nat in H0 ; try lia.
            apply (bw_add_end_state_going F p x0 x2 z (S n) F' ) in H7 ; auto.
            replace (S (S (S (n + S (n + 0)))))%nat with (2 * S n + 2)%nat ; try lia.              
            eauto.
          + destruct H5.
            pose proof (bw_ir_oo'_child_lgc_child F' V x0 x x2 x3 z x1 H2 H1 H4 H3 H5 H6).
            replace (2 + 2*n)%nat with ((2 * S n))%nat in H0 ; try lia.
            apply (bw_add_end_state_going F p x0 x2 z (S n) F' ) in H7 ; auto.
            replace (S (S (S (n + S (n + 0)))))%nat with (2 * S n + 2)%nat ; try lia.              
            eauto.       
          + destruct H6.
            pose proof (bw_ir_oo'_child_lgc F' V x0 x x2 x3 z x1 H2 H1 H4 H3 H5 H6).
            replace (2 + 2*n)%nat with ((2 * S n))%nat in H0 ; try lia.
            apply (bw_add_end_state_going F p x0 x2 z (S n) F' ) in H7 ; auto.
            replace (S (S (S (n + S (n + 0)))))%nat with (2 * S n + 2)%nat ; try lia.              
            eauto.   
          + pose proof (bw_ir_oo'_child_nlgc F' V x0 x x2 z x1 H2 H1 H4 H3 H5 H6).
            replace (2 + 2*n)%nat with ((2 * S n))%nat in H0 ; try lia.
            apply (bw_add_end_state_going F p x0 x2 z (S n) F' ) in H7 ; auto.
            replace (S (S (S (n + S (n + 0)))))%nat with (2 * S n + 2)%nat ; try lia.              
            eauto.
        }
      * pose proof (Z.lt_trichotomy (z) (V x)).
        destruct H4 as [H4 | [H4 | H4]].
        { destruct (classic (exists x', F' x x' (invert_orientation x1))) ;
            destruct x1 ; simpl in *.
          + destruct H5. 
            exfalso. apply H.
            exists (update_edge (update_edge F' x x1 x0 RIGHT) x0 x x1 LEFT) x (S(S (S (n + (n + 0))))).
            pose proof (bw_add_end_state_end_1 F p x0 x z (S n) F').
            replace (S (S (S (n + (n + 0)))))%nat with (2 * S n + 1)%nat ; try lia.
            replace ((S (S (n + (n + 0)))))%nat with (2 * S n)%nat in H0; try lia.
            apply H6 ; auto. 
            pose proof (bw_ir_rl_root_rgc_found F' V x0 x x1 z).
            apply H7 ; auto ; try lia. 
            right. repeat split ; auto ; try lia. intro. apply H3.
            destruct H8. exists x2 LEFT. repeat split ; auto. simpl ; try lia.
          + destruct H5.
            exfalso. apply H3.
            exists (x1) LEFT. repeat split ; auto ; simpl ; try lia.
          + exfalso. apply H.
            exists (add_edge (remove_edge F' x0 x) x x0 RIGHT) x (S(S (S (n + (n + 0))))).
            pose proof (bw_add_end_state_end_1 F p x0 x z (S n) F').
            replace (S (S (S (n + (n + 0)))))%nat with (2 * S n + 1)%nat ; try lia.
            replace ((S (S (n + (n + 0)))))%nat with (2 * S n)%nat in H0; try lia.
            apply H6 ; auto. 
            pose proof (bw_ir_rl_root_nrgc_found F' V x0 x z).
            apply H7 ; auto ; try lia. 
            right. right. repeat split ; auto ; try lia. intro. apply H3.
            destruct H8. exists x1 LEFT. repeat split ; auto. simpl ; try lia.
          + exfalso. apply H.
            pose proof (bw_add_end_state_end_1 F p x0 x z (S n) F').
            replace (S (S (S (n + (n + 0)))))%nat with (2 * S n + 1)%nat ; try lia.
            replace ((S (S (n + (n + 0)))))%nat with (2 * S n)%nat in H0; try lia.
            exists (add_edge (remove_edge F' x0 x) x x0 LEFT) x (2 * S n + 1)%nat.
            apply H6 ; auto.
            apply (bw_ir_rr_root_nlgc_found ) ; auto ; try lia.
        }
        { destruct (classic (exists x', F' x x' (invert_orientation x1))) ;
            destruct x1 ; simpl in *.
          + exfalso. apply H. destruct H5.
            pose proof (bw_add_end_state_end_1 F p x0 x z (S n) F').
            replace (S (S (S (n + (n + 0)))))%nat with (2 * S n + 1)%nat ; try lia.
            replace ((S (S (n + (n + 0)))))%nat with (2 * S n)%nat in H0; try lia.
            exists ((update_edge (update_edge F' x x1 x0 RIGHT) x0 x x1 LEFT)) x ((2 * S n + 1)%nat).
            apply H6 ; auto.
            apply bw_ir_rl_root_rgc_found ; auto ; try lia.
          + destruct H5.
            exfalso. apply H.
            pose proof (bw_add_end_state_end_1 F p x0 x z (S n) F').
            replace (S (S (S (n + (n + 0)))))%nat with (2 * S n + 1)%nat ; try lia.
            replace ((S (S (n + (n + 0)))))%nat with (2 * S n)%nat in H0; try lia.
            exists ((update_edge (update_edge F' x x1 x0 LEFT) x0 x x1 RIGHT)) x ((2 * S n + 1)%nat).
            apply H6 ; auto.
            apply bw_ir_rr_root_lgc_found; auto ; try lia.
          + exfalso. apply H.
            pose proof (bw_add_end_state_end_1 F p x0 x z (S n) F').
            replace (S (S (S (n + (n + 0)))))%nat with (2 * S n + 1)%nat ; try lia.
            replace ((S (S (n + (n + 0)))))%nat with (2 * S n)%nat in H0; try lia.
            exists ((add_edge (remove_edge F' x0 x) x x0 RIGHT)) x ((2 * S n + 1)%nat).
            apply H6 ; auto.
            apply bw_ir_rl_root_nrgc_found ; auto ; try lia.
          + exfalso. apply H.
            pose proof (bw_add_end_state_end_1 F p x0 x z (S n) F').
            replace (S (S (S (n + (n + 0)))))%nat with (2 * S n + 1)%nat ; try lia.
            replace ((S (S (n + (n + 0)))))%nat with (2 * S n)%nat in H0; try lia.
            exists ((add_edge (remove_edge F' x0 x) x x0 LEFT)) x ((2 * S n + 1)%nat).
            apply H6 ; auto.
            apply bw_ir_rr_root_nlgc_found ; auto ; try lia.
        }
        { destruct (classic (exists x', F' x x' (invert_orientation x1))) ;
            destruct x1 ; simpl in *.
          + destruct H5.
            exfalso. apply H3.
            exists (x1) RIGHT. repeat split ; auto.
          + destruct H5. 
            exfalso. apply H.
            pose proof (bw_add_end_state_end_1 F p x0 x z (S n) F').
            replace (S (S (S (n + (n + 0)))))%nat with (2 * S n + 1)%nat ; try lia.
            replace ((S (S (n + (n + 0)))))%nat with (2 * S n)%nat in H0; try lia.
            exists ((update_edge (update_edge F' x x1 x0 LEFT) x0 x x1 RIGHT)) x ((2 * S n + 1)%nat).
            apply H6 ; auto.
            apply bw_ir_rr_root_lgc_found ; auto ; try lia.
            right. repeat split ; auto. intro.
            destruct H7. apply H3. exists x2 RIGHT.
            repeat split ; simpl ; auto ; try lia.
          + exfalso. apply H.
            pose proof (bw_add_end_state_end_1 F p x0 x z (S n) F').
            replace (S (S (S (n + (n + 0)))))%nat with (2 * S n + 1)%nat ; try lia.
            replace ((S (S (n + (n + 0)))))%nat with (2 * S n)%nat in H0; try lia.
            exists (add_edge (remove_edge F' x0 x) x x0 RIGHT) x ((2 * S n + 1)%nat).
            apply H6 ; auto.
            apply bw_ir_rl_root_nrgc_found ; auto ; try lia.
          + exfalso. apply H.
            pose proof (bw_add_end_state_end_1 F p x0 x z (S n) F').
            replace (S (S (S (n + (n + 0)))))%nat with (2 * S n + 1)%nat ; try lia.
            replace ((S (S (n + (n + 0)))))%nat with (2 * S n)%nat in H0; try lia.
            exists (add_edge (remove_edge F' x0 x) x x0 LEFT) x ((2 * S n + 1)%nat).
            apply H6 ; auto.
            apply bw_ir_rr_root_nlgc_found ; auto ; try lia.
            right. right. repeat split ; simpl ; auto.
            intro. apply H3. destruct H7. exists x1 RIGHT.
            repeat split ; auto.
        }
    - exfalso.
      assert (bw_ir F V p x0 z (2 + 2 * n) F' ENDED).
      pose proof (bw_add_end_state_end_0 F p x0 x0 z (S n) F' F').
      assert (2 + 2 * n = 2 * S n)%nat. lia. rewrite H3.
      rewrite H3 in H0. apply H2 ; auto.
      pose proof (Z.lt_trichotomy (z) (V x0)).
      destruct H4 as [H4 | [H4 | H4]].
      * apply bw_ir_rl_fail ; auto.
        intro. apply H1. destruct H5.
        exists x LEFT. split ; auto. simpl. lia.
      * subst. apply bw_ir_found_root.
      * apply bw_ir_rr_fail ; auto.
        intro. apply H1. destruct H5.
        exists x RIGHT. split ; auto.
      * apply H. exists F' x0 (2 + 2 * n)%nat.
        auto.
  Qed.
  
  Lemma no_bw_ir_end_then_going_4 : forall F z,
      ¬(exists F' x n, bw_ir F V p x z n F' ENDED) ->
      (forall n, (exists F' x, bw_ir F V p x z (4+4*n) F' GOING)).
  Proof.
    intros.
    pose proof (no_bw_ir_end_then_going F z H (2*n + 1)).
    replace (2 + 2 * (2 * n + 1))%nat with (4 + 4 * n)%nat in H0 ; try lia.
    eauto.
  Qed.
  
  Lemma bw_ir_path_case_one : forall (F Ff : EdgeSet) p x y xf z o n x',
      Inv p D F V W ->
      
      path_find_count F V p xf z (4+n) ENDED ->
      
      (orientation_op o) (V p) z -> 
      F p x o ->
      (orientation_op o) (V x) z ->
      F x y o -> 
      ¬(exists t, F y t (invert_orientation o)) ->

      (* rotation on children *)
      let D' := (descendants F x) in
      let F' := (remove_edge_that_are_not_in_D F D') in 
      let FC' := (remove_edge_that_are_in_D F D') in
      let F'' := (remove_edge F' x y) in
      let F''' := (add_edge F'' y x (invert_orientation o)) in

      (*Edgeset after first rotation*)
      let Fafr := (add_edge (union_edge F''' FC') p y o) in 

      (* rotation on root *)
      let F1 := (update_edge Fafr p y x o) in 
      let F2 := (update_edge F1 y x p (invert_orientation o)) in 

      bw_ir F V p y z 2 F2 GOING ->
      bw_ir F2 V y x' z 2 Ff GOING ->
      (exists m y, (m < 4+n)%nat /\ path_find_count Ff V x' y z m ENDED).
  Proof.
    intros F Ff p0 x y xf z o n x' Inv path orientationp0 edgep0 orientationx edgex nedge **.
    apply bw_ir_inv in H as Invy ; auto.
    apply bw_ir_inv in H0 as Invx' ; auto.
    inversion path ; subst ; stpathcount_tac.
    inversion H1 ; subst ; stpathcount_tac.
    inversion H10 ; subst ; stpathcount_tac.
    inversion H12 ; subst ; stpathcount_tac.
    inversion H4 ; subst ; stpathcount_tac. rename H3 into Fp0.
    inversion H5 ; subst ; stpathcount_tac. rename H3 into Fy0.
    inversion H6 ; subst ; stpathcount_tac. rename H3 into Fy1.
    inversion H0 ; subst.

    (*
        CASE ONE 
     *)
    
    + pose proof (H11) as Hf2yx0.
      (* destruct F2yx0*)
      destruct Hf2yx0 as [[Hf2yx01 [Hf2yx02 Hf2yx03]] |] ; unpack ; subst ; storientation_tac.
      destruct Hf2yx03 as [[Hf2yx03 [Hf2yx04 Hf2yx05]] | ] ; unpack ; subst ; stlink_tac.
      destruct Hf2yx05 as [Hf2yx05 | ] ; unpack ; subst ; stlink_tac.
      destruct Hf2yx05 as [Hf2yx05 | Hf2yx05] ; unpack ; subst ; 
        [|destruct Hf2yx05 as [[Hf2yx05 Hf2yx06] Hf2yx07];
          unpack ; subst; exfalso ;apply Hf2yx05; rewrite in_set_st_eq;stpath_tac].
      destruct Hf2yx05 as [Hf2yx05 | ?]; unpack ; subst ; storientation_tac.
      destruct Hf2yx05 as [Hf2yx05 Hf2yx06] ; subst ; storientation_tac.
      destruct Hf2yx06 as [Hf2yx06 [Hf2yx07 Hf2yx08]] ; unpack ; subst ; storientation_tac.
      
      pose proof (H15) as Hf2x0x'.
      (* destruct F2yx0*)
      destruct Hf2x0x' as [[Hf2x0x'1 [Hf2x0x'2 Hf2x0x'3]] |] ; unpack ; subst ; stlink_tac.
      destruct Hf2x0x'3 as [[Hf2x0x'3 [Hf2x0x'4 Hf2x0x'5]] | ] ; unpack ; subst ; stlink_tac.
      destruct Hf2x0x'5 as [Hf2x0x'5 | ] ; unpack ; subst ; stlink_tac.
      destruct Hf2x0x'5 as [Hf2x0x'5 | Hf2x0x'5] ; unpack ; subst ; 
        [|destruct Hf2x0x'5 as [[Hf2x0x'5 Hf2x0x'6] Hf2x0x'7];
          unpack ; subst; exfalso ;apply Hf2x0x'5; rewrite in_set_st_eq;stpath_tac].
      destruct Hf2x0x'5 as [Hf2x0x'5 | ?]; unpack ; subst ; stlink_tac.
      destruct Hf2x0x'5 as [Hf2x0x'5 Hf2x0x'6] ; subst ; storientation_tac.
      destruct Hf2x0x'6 as [Hf2x0x'6 [Hf2x0x'7 Hf2x0x'8]] ; unpack ; subst ; storientation_tac.

      clear H1 H4 H10 H5 H12 H6.
      
      (* join orientation adn elem *)
      assert (o = o0) ; storientation_tac ; subst.
      assert (y0 = x) ; stlink_tac ; subst.
      assert (o1 = o0) ; storientation_tac ; subst.
      assert (y1 = y) ; stlink_tac ; subst.
      assert (o2 = o3) ; storientation_tac ; subst.
      assert (y2 = x0) ; stlink_tac ; subst.
      destruct (classic (invert_orientation o0 = o3)) ; subst ; [exfalso;eauto|].
      apply neq_sym in H1. apply invert_orientation_different_then_equal in H1. subst.

      inversion H14 ; subst.

    (* case for n = 0 *)
    - assert (o = o0) ; storientation_tac ; subst.
      assert (xf = x') ; stlink_tac ; subst.
      destruct (orientation_trichotomy o0 (V x') z) as [trix1 | [trix2 | trix3]] ; subst.
      * exists O x'. split ; [lia|]. inversion H2 ; subst.
        { apply path_fc_refl. }
        { assert (o = o0) ; storientation_tac ; subst.
          apply path_fc_stop with o0 ; auto.
          intro. destruct H6. 
          destruct H6 ; unpack ; subst ; storientation_tac.
          destruct H12 ; unpack ; subst ; [|lia].
          destruct H20 ; unpack ; subst ; [|lia]. 
          destruct H20 ; unpack ; subst ; 
            [|destruct H20 as [[a b] c] ; unpack ; apply a ; rewrite in_set_st_eq ; stpath_tac].
          destruct H20 ; unpack ; subst ; [|lia]. 
          destruct H20 ; unpack ; subst ; stlink_tac. 
          destruct H21 ; unpack ; subst ; stlink_tac. 
          destruct H23 ; unpack ; subst ; stlink_tac.   
          destruct H25 ; unpack ; subst ; stlink_tac.  
          destruct H27 ; unpack ; subst ; stlink_tac.  
          destruct H27 ; unpack ; subst ;
            [|destruct H27 as [[a b] c] ; unpack ; eauto].
          destruct H27 ; unpack ; subst ; stlink_tac.  
          destruct H27 ; unpack ; subst ; stlink_tac.  
          destruct H28 ; unpack ; subst ; stlink_tac.  
          eauto.
        }
        { inversion  H1. }
      * exists 2%nat x0. split ; [lia|].
        assert (F5 x' y (invert_orientation o0)).
        { right. auto. }
        assert (F5 y x0 o0).
        { left. repeat split ; [left ;intro ; subst|left;intro ; subst|] ; stlink_tac.
          right. auto.
        }
        apply path_fc_step_ended.
        { apply path_fc_step_going with y ;
            [apply path_fc with (invert_orientation o0) ; auto|apply path_fc with o0 ; auto].
        }
        {
          apply path_fc_stop with o0 ; auto.
          intro. destruct H6.
          destruct H6 ; unpack ; subst ; storientation_tac.
          destruct H12 ; unpack ; subst ; stlink_tac.
          destruct H19 ; unpack ; subst ; stlink_tac.
          destruct H19.
          + destruct H19 ; unpack ; subst ; storientation_tac.
            destruct H19 ; unpack ; subst ; storientation_tac. 
            destruct H20 ; unpack ; subst ; storientation_tac.
            assert (x1 = x') ; stlink_tac ; subst. lia.
          + destruct H19 ; unpack.
            assert (x1 = x') ; stlink_tac ; subst.
            apply H21. rewrite in_set_st_eq ; stpath_tac.
        }
      * exists O x'. split ; [lia|]. apply path_fc_refl.
        
    (* case for n inductive *)
    - inversion H4 ; subst ; stpathcount_tac.
      assert (o = o0) ; storientation_tac ; subst.
      assert (y0 = x') ; stlink_tac ; subst.
      destruct (orientation_trichotomy o0 (V x') z) as [trix1 | [trix2 | trix3]] ; subst.
      * exists n xf. split ; [lia|].
        apply path_fc_step_ended.
        { clear dependent H4 path H14 H2. generalize dependent xf.
          induction n ; intros.
          + inversion H18.
          + destruct n.
          - admit.
          - admit.
        }
        { inversion H2 ; subst ; stpathcount_tac.
          apply path_fc_stop with o ; auto.
          intro. destruct H12.
          destruct H12 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac. 
          destruct H19 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H22 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H22 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H22 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H22 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H23 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H25 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H27 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H29 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H29 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H29 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H29 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H30 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H29 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H22 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H23 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H26 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H28 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H28 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H28 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H28 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H29 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. 
          destruct H28 ; unpack ; subst ; stlink_tac ; stpath_tac ; storientation_tac ; eauto. }
      * exists 2%nat x0. split ; [lia|].
        assert (F5 x' y (invert_orientation o0)).
        { right. auto. }
        assert (F5 y x0 o0).
        { left. repeat split ; [left ;intro ; subst|left;intro ; subst|] ; stlink_tac.
          right. auto.
        }
        apply path_fc_step_ended.
        { apply path_fc_step_going with y ;
            [apply path_fc with (invert_orientation o0) ; auto|apply path_fc with o0 ; auto].
        }
        {
          apply path_fc_stop with o0 ; auto.
          intro. destruct H12.
          destruct H12 ; unpack ; subst ; storientation_tac.
          destruct H19 ; unpack ; subst ; stlink_tac.
          destruct H21 ; unpack ; subst ; stlink_tac.
          destruct H21.
          + destruct H21 ; unpack ; subst ; storientation_tac.
            destruct H21 ; unpack ; subst ; storientation_tac. 
            destruct H22 ; unpack ; subst ; storientation_tac.
            assert (x1 = x') ; stlink_tac ; subst. lia.
          + destruct H21 ; unpack.
            assert (x1 = x') ; stlink_tac ; subst.
            apply H21. rewrite in_set_st_eq ; stpath_tac.
        }
      * exists O x'. split ; [lia|]. apply path_fc_refl.

      (*
        CASE TWO
       *)
        
      + admit. 
      + admit. 
      + admit. 
      + admit. 
      + admit. 
      + inversion H19.
  Admitted.

  Lemma path_find_count_ir : forall p F F' x x' z n,
      Inv p D F V W -> 
      path_find_count F V p x z (4+n) ENDED ->
      bw_ir F V p x' z 4 F' GOING ->
      (exists m y, (m < 4+n)%nat /\ path_find_count F' V x' y z m ENDED).
  Proof.
    intros p0 F F' x x' z n Inv **.
    inversion H0 ; subst.
    inversion H2 ; subst.
    + pose proof (bw_ir_path_case_one F F' p0 x1 x0 x z o n x'). apply H7 ; auto.
    +
  Admitted.

  Lemma exxists_find_count_ir : forall p F x z n,
      path_find_count F V p x z (4+n) ENDED ->
      exists F' x', (bw_ir F V p x' z 4 F' GOING).
  Proof.
    intros.
    inversion H ; subst.
    inversion H0 ; subst.
    inversion H9 ; subst.
    inversion H11 ; subst.
    inversion H3 ; inversion H4 ; inversion H5 ; inversion H13 ; subst.
    + 
      
  Admitted.
  
  Lemma path_find_count_implies_bw_ir : forall p F x z n,
      Inv p D F V W ->
      path_find_count F V p x z n ENDED ->
      (exists F' x n, bw_ir F V p x z n F' ENDED).
  Proof.
    intros p0 F x z n Inv **.
    generalize dependent F.
    generalize dependent p0.
    generalize dependent x.
    induction_wf IH: Wf_nat.lt_wf n.
    intros.
    destruct x. admit.
    destruct x. admit.
    destruct x. admit.
    destruct x. admit.
    pose proof (exxists_find_count_ir p0 F x0 z x H0).
    do 2destruct H1.
    pose proof (path_find_count_ir p0 F x1 x0 x2 z x Inv H0 H1).
    do 2destruct H2. unpack.
    assert (STpredicate.Inv x2 D x1 V W).
    pose proof (bw_ir_inv p0 F x2 4 z x1 GOING).
    apply H4 ; auto.
    specialize (H x3 H2 x4 x2 x1 H4 H3).
    do 3destruct H. inversion H1 ; subst.
    exists (x5) x6 (4 + x7)%nat.
    pose proof (bw_ir_ic_ind2 F' x1 x5 V x8 x2 x6 z (x7) H12 H).
    pose proof (bw_ir_ic_ind2 F F' x5 V p0 x8 x6 z (S (S x7)) H6 H5).
    auto.
  Admitted.
  
  Lemma exists_bw_ir : forall p F z,
      Inv p D F V W ->
      (exists F' x n, bw_ir F V p x z n F' ENDED).
  Proof.
    intros p0 F z Inv **.
    pose proof (exists_find_count_path_if_inv D V W p0 F z Inv).
    do 2destruct H.
    apply path_find_count_implies_bw_ir in H ; auto.
  Qed.

  Lemma bw_ir_left_are_lower_key : forall p F x n z F',
      Inv p D F V W ->
      bw_ir F V p x z n F' ENDED ->
      (forall y y', F' x y LEFT -> y' \in descendants F' y -> z > V y').
  Proof.
    intros p0 F x n z F'.
    generalize dependent p0.
    generalize dependent F.
    generalize dependent x.
    generalize dependent z.
    generalize dependent F'. 
    induction_wf IH: Wf_nat.lt_wf n.
    intros.
    intros. pose proof (H1) as H0'.
    inversion H1 ; subst ;apply bw_ir_inv in H0' ; auto.
    + rewrite in_set_st_eq in H3. stpath_tac.
    + rewrite in_set_st_eq in H3. exfalso ; eauto.
    + rewrite in_set_st_eq in H3.
      assert (V x0 > V y'). stpath_tac. lia.
    + rewrite in_set_st_eq in H3.
      destruct H6 as [H6 | [H6 | H6] ] ; unpack ; subst.
    - stpath_tac.
    - assert (V x0 > V y'). stpath_tac. lia.
    - destruct H2 ; unpack ; subst ; try discriminate.
      destruct H2. exfalso ; eauto.
      + rewrite in_set_st_eq in H3.
        destruct H6 as [H6 | H6] ; unpack ; subst.
    - stpath_tac.
    - assert (V x0 > V y'). stpath_tac.
      destruct H2 ; unpack ; subst ; stlink_tac.
      destruct H11 ; unpack ; subst ; try discriminate.
      exfalso ; eauto.
      + rewrite in_set_st_eq in H3.
        destruct H6 as [H6 | [H6 | H6]] ; unpack ; subst.
    - stpath_tac.
    - assert (V x0 > V y'). stpath_tac.
      destruct H2 ; unpack ; subst.
      destruct H2. exfalso ; eauto.
      apply three_option_path_x_y in H3.
      destruct H3 as [H3 | [H3 | H3]] ; unpack ; subst.
      * lia.
      * destruct H3 ; unpack ; try discriminate.
        destruct H3. destruct H3 ; try contradiction.
        exfalso ; apply H3. stlink_tac.
      * destruct H3 ; unpack ; subst ; stlink_tac.
        destruct H3.
        apply add_edge_if_no_path_inv in H9.
        apply remove_edge_inv in H9.
        assert (V p0 > V y'). stpath_tac. lia.
        intro. apply remove_edge_inv in H12. stlink_tac.
    - destruct H2 ; unpack ; subst.
      destruct H2. exfalso ; eauto.
      apply three_option_path_x_y in H3.
      destruct H3 as [H3 | [H3 | H3] ] ; unpack ; subst.
      * lia.
      * destruct H3 ; unpack ; try discriminate.
        destruct H3. destruct H3 ; try contradiction.
        exfalso ; apply H3. stlink_tac.
      * destruct H3 ; unpack ; subst ; stlink_tac.
        destruct H3.
        apply add_edge_if_no_path_inv in H9.
        apply remove_edge_inv in H9.
        assert (V p0 > V y'). stpath_tac. lia.
        intro. apply remove_edge_inv in H12. stlink_tac.        
      + rewrite in_set_st_eq in H3.
        destruct H6 as [H6 | H6] ; unpack ; subst.
    - stpath_tac.
    - assert (V x0 > V y'). stpath_tac. lia.
      + specialize (H n). apply H with F' x0 F'0 x1 y ; auto.
        apply bw_ir_inv in H4 ; auto.
  Qed.

  Lemma bw_ir_right_are_lower_key : forall p F x n z F',
      Inv p D F V W ->
      bw_ir F V p x z n F' ENDED ->
      (forall y y', F' x y RIGHT -> y' \in descendants F' y -> z < V y').
  Proof.
    intros p0 F x n z F'.
    generalize dependent p0.
    generalize dependent F.
    generalize dependent x.
    generalize dependent z.
    generalize dependent F'. 
    induction_wf IH: Wf_nat.lt_wf n.
    intros.
    intros. pose proof (H1) as H0'.
    inversion H1 ; subst ;apply bw_ir_inv in H0' ; auto.
    + rewrite in_set_st_eq in H3. stpath_tac.
    + rewrite in_set_st_eq in H3. assert (V x0 < V y'). stpath_tac. lia.
    + rewrite in_set_st_eq in H3. exfalso ; eauto.
    + rewrite in_set_st_eq in H3.
      destruct H6 as [H6 | [H6 | H6] ] ; unpack ; subst.
    - stpath_tac.
    - destruct H2 ; unpack ; subst.
      destruct H2. exfalso ; eauto.
      apply three_option_path_x_y in H3.
      destruct H3 as [H3 | [H3 | H3]] ; unpack ; subst.
      * lia.
      * assert (V p0 < V y'). stpath_tac.
        destruct H3 ; unpack ; subst ; stlink_tac.
        destruct H3. destruct H3 ; try contradiction.
        lia.
      * destruct H3 ; unpack ; subst ; stlink_tac.
        destruct H3.
        assert (t = x0). stlink_tac. subst. lia.
    - destruct H2 ; unpack ; subst.
      destruct H2. exfalso ; eauto.
      apply three_option_path_x_y in H3.
      destruct H3 as [H3 | [H3 | H3]] ; unpack ; subst.
      * lia.
      * assert (V p0 < V y'). stpath_tac.
        destruct H3 ; unpack ; subst ; stlink_tac.
        destruct H3. destruct H3 ; try contradiction.
        lia.
      * destruct H3 ; unpack ; subst ; stlink_tac.
        destruct H3.
        assert (t = x0). stlink_tac. subst. lia.
      + rewrite in_set_st_eq in H3.
        destruct H6 as [H6 | H6] ; unpack ; subst.
    - stpath_tac.
    - assert (V x0 < V y'). stpath_tac. lia.
      + rewrite in_set_st_eq in H3.
        destruct H6 as [H6 | [H6 | H6] ] ; unpack ; subst.
    - stpath_tac.
    - assert (V x0 < V y'). stpath_tac.
      destruct H2 ; unpack ; subst ; try discriminate.
      destruct H2. lia.
    - destruct H2 ; unpack ; subst ; try discriminate.
      destruct H2. exfalso ; eauto.
      + rewrite in_set_st_eq in H3.
        destruct H6 as [H6 | H6] ; unpack ; subst.
    - stpath_tac.
    - assert (V x0 < V y'). stpath_tac.
      destruct H2 ; unpack ; subst ; stlink_tac.
      destruct H11 ; unpack ; subst ; try discriminate.
      exfalso ; eauto.
      + specialize (H n). apply H with F' x0 F'0 x1 y ; auto.
        apply bw_ir_inv in H4 ; auto.
  Qed.

  Lemma bw_ir_key_op : forall p F x n z F',
      Inv p D F V W ->
      bw_ir F V p x z n F' ENDED ->
      (forall y y' o, F' x y o -> y' \in descendants F' y -> (orientation_op o) z (V y')).
  Proof.
    intros.
    destruct o ; simpl.
    + apply bw_ir_left_are_lower_key with p0 F x n F' y ; auto.
    + apply bw_ir_right_are_lower_key with p0 F x n F' y ; auto.
  Qed.
    
  (*
  Lemma value_in_tree_then_splay_its_node : forall p F n1 n2,
      Inv p D F V W ->
      n1 \in D ->
      n2 \in D ->
      V n1 = V n2 ->
      n1 = n2.
  Proof.
    intros.
    assert (path F p0 n1). stpath_tac.
    assert (path F p0 n2). stpath_tac.
    apply path_implies_path_add_memory in H3.
    destruct H3.
    assert (exists l, rev l = x). exists (rev x).
    rewrite rev_involutive. auto.
    destruct H5. subst. rename x0 into x.
    generalize dependent n1.
    induction x ; intros.
    + inversion H3 ; subst.
      apply three_option_path_x_y in H4.
      destruct H4 as [H4 | [H4 | H4]] ; subst ; auto.
      - do 2destruct H4. assert (V n1 < V n2). stpath_tac. lia.
      - do 2destruct H4. assert (V n1 > V n2). stpath_tac. lia.
      - apply app_nil in H5. unpack ; discriminate.
    + inversion H3 ; subst.
      - symmetry in H9. apply app_nil in H9. unpack ; discriminate.
      - symmetry in H5. apply app_eq_unit in H5.
        destruct H5 ; unpack ; try discriminate.
        inversion H6 ; subst. 
        apply three_option_path_x_y in H4.
        destruct H4 as [H4 | [H4 | H4]] ; subst.
        { assert (orientation_op o (V n2) (V n1)). stlink_tac.
          destruct o ; simpl in * ; lia.
        }
        { do 2destruct H4.
          destruct o.
          + assert (V p0 > V n1). stlink_tac.
            assert (V p0 < V n2). stpath_tac.
            lia.
          + assert (n1 = x0). stlink_tac. subst x0.
            apply three_option_path_x_y in H7.
            destruct H7 as [H7 | [H7 | H7]] ; subst ; auto.
            - do 2destruct H7. assert (V n1 < V n2). stpath_tac.
              lia.
            - do 2destruct H7. assert (V n1 > V n2). stpath_tac.
              lia.            
        }
        {
          do 2destruct H4.
          destruct o.
          + assert (n1 = x0). stlink_tac. subst x0.
            apply three_option_path_x_y in H7.
            destruct H7 as [H7 | [H7 | H7]] ; subst ; auto.
            - do 2destruct H7. assert (V n1 < V n2). stpath_tac.
              lia.
            - do 2destruct H7. assert (V n1 > V n2). stpath_tac.
              lia. 
          + assert (V p0 < V n1). stlink_tac.
            assert (V p0 > V n2). stpath_tac.
            lia.
        }
      - apply app_inj_tail in H5. unpack ; subst.
        assert (a \in D). stdomain_tac.
        Admitted.
        
        
  Lemma bw_ir_value_in_tree_then_splay_its_node : forall p F x n node k F',
      Inv p D F V W ->
      node \in D ->
      V node = k ->
      bw_ir F V p x k n F' ENDED ->
      Inv node D F' V W.
  Proof.
    intros.
    induction H1 ; subst.
    +  

  Qed. *)
      
      
End IterativeRotation.
