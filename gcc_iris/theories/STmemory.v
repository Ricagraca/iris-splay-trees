From ST Require Import STorientation STpredicate STdomain STlink STpath STedgeset STvaluefunction.
From iris_time.heap_lang Require Import notation lib.assert.
From iris_time.heap_lang Require Export lang.
From iris_time.heap_lang Require Import proofmode.
From iris_time.heap_lang Require Import notation.
From iris_time Require Import Combined.
From stdpp Require Import gmap.


From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual
     LibInt.

  
Section MapstoMemory.

  Context `{!tctrHeapG Σ} (nmax : nat).

  Definition node_of_orientation (M : gmap elem content)
             (e : elem) (o : orientation) (x : elem) (F : EdgeSet) V :=
    match o with
    | LEFT  => exists v , V e = v /\ ((exists r, M !! e = Some (NodeB v x r) /\ F e r RIGHT)
                          \/ M !! e = Some (NodeL v x) /\ ¬(exists t, F e t RIGHT))
    | RIGHT => exists v , V e = v /\ ((exists l, M !! e = Some (NodeB v l x)  /\ F e l LEFT)
                          \/ M !! e = Some (NodeR v x) /\ ¬(exists t, F e t LEFT))
    end.
  
  Lemma mapsto_M_acc : forall M x c,
      M !! x = Some c ->
    mapsto_M M -∗
    ∃ v, ⌜val_of_content c = Some v⌝ ∗ x ↦ v ∗
    (∀ c' v', ⌜val_of_content c' = Some v'⌝ -∗
    x ↦ v' -∗ mapsto_M (<[x:=c']>M)).
  Proof.
    introv HM. iIntros "HM".
    rewrite -[in mapsto_M _](insert_id _ _ _ HM) -insert_delete /mapsto_M.
    rewrite big_sepM_insert ?lookup_delete //. iDestruct "HM" as "[Hc HM]".
    destruct (val_of_content c); [|done]. iExists _. iFrame. iSplit; [done|].
    iIntros (c' v' Hv') "?".
    rewrite -insert_delete big_sepM_insert ?lookup_delete // Hv'. iFrame.
  Qed.

  Lemma mapsto_M_acc_same : forall M x c,
      M !! x = Some c ->
      mapsto_M M -∗
               ∃ v, ⌜val_of_content c = Some v⌝ ∗ x ↦ v ∗ (x ↦ v -∗ mapsto_M M).
  Proof.
    introv HM. iIntros "HM".
    iDestruct (mapsto_M_acc with "HM") as (v Hv) "[Hv HM]"; [done|].
    iExists _. iFrame. iSplit; [done|].
    iSpecialize ("HM" $! _ _ Hv). by rewrite insert_id.
  Qed.

  Lemma mapsto_M_insert : forall M x c v,
      M !! x = None ->
      val_of_content c = Some v ->
      x ↦ v ∗ mapsto_M M ⊣⊢ mapsto_M (<[x:=c]>M).
  Proof.
    introv Mxc Hcv. by rewrite /mapsto_M big_sepM_insert // Hcv.
  Qed.

  Lemma M_inv_incl : forall D F V W M p x o,
      Inv p D F V W ->
      Mem D F V M ->
      F p x o -> 
      let D' := (descendants F x) in
      let F' := (remove_edge_that_are_not_in_D F D') in
      Mem D' F' V M.
  Proof.
    intros.
    intros x' H'.
    assert (x' \in D).
    apply incl_inv with D' ; auto.
    apply incl_prove. intros.
    rewrite in_set_st_eq in H2. assert (path F p x0).
    apply path_trans with x ; auto. apply path_single with o ; auto.
    stdomain_tac.
    apply H0 in H2. destruct (M !! x') ; auto.
    rewrite in_set_st_eq in H'.
    destruct c ; unpack ; auto ;
      repeat split ; auto ;
        try (rewrite in_set_st_eq ; stpath_tac) ;
        intro ; destruct H5.
    * apply H3. exists x0 ; destruct H5 ; unpack ; auto.
    * apply H3. exists x0 ; destruct H5 ; unpack ; auto.
    * apply H2. exists x0 ; destruct H5 ; unpack ; auto.
    * apply H3. exists x0 ; destruct H5 ; unpack ; auto.
  Qed.

  Lemma M_update_comm : forall D (F1 F2 : EdgeSet) V M,
      (forall a b c, F1 a b c <-> F2 a b c) -> 
      Mem D F1 V M ->
      Mem D F2 V M.
  Proof.
    intros.
    intros x Hx.
    apply H0 in Hx.
    destruct (M !! x) ; try contradiction.
    destruct c ; unpack ; repeat split ; auto ; try apply H ; auto ;
      intro ; destruct H4 ; apply H in H4 ; eauto.
  Qed.
    
  Lemma M_inv_add_union_edge_if_different : forall p D F F' V W M M' x z o,
      Mem D F V M ->
      Inv p D F V W -> 
      F p x o ->
      let D' := descendants F x in
      let FC' := remove_edge_that_are_in_D F D' in 
      Inv z D' F' V W ->
      Mem D' F' V M' ->
      let F'' := (add_edge (union_edge F' FC') p z o) in      
      (forall x, x \notin D' /\ x \in D /\ ¬(x = p) -> (M' !! x = M !! x)) ->
      node_of_orientation M' p o z FC' V -> 
      Mem D F'' V M'.
      Proof.
        intros.
        intros x' Hx.
        destruct (classic(x' \in D')).
        + apply H3 in H6 as Hx'.
          destruct (M' !! x') ; try contradiction.
          destruct c ; unpack.
          - repeat split ; auto ; left ; left ; auto.
          - repeat split ; auto ; [left ; left ; auto|].
            intro. destruct H10.
            destruct H10 ; unpack ; subst ;
            [|assert (p \in D') ; stdomain_tac ;
              rewrite in_set_st_eq in H6 ; stpath_tac].
            destruct H10 ; eauto. destruct H9 ; unpack.
            assert (x' \in D'). stdomain_tac. contradiction.
          - repeat split ; auto ; [left ; left ; auto|].
            intro. destruct H10.
            destruct H10 ; unpack ; subst ;
            [|assert (p \in D') ; stdomain_tac ;
              rewrite in_set_st_eq in H6 ; stpath_tac].
            destruct H10 ; eauto. destruct H9 ; unpack.
            assert (x' \in D'). stdomain_tac. contradiction.
          - repeat split ; auto.
            * intro. destruct H10.
              destruct H10 ; unpack ; subst ; [|rewrite in_set_st_eq in H6; stpath_tac].
              destruct H10 ; eauto.
              destruct H9 ; unpack. eauto.
            * intro. destruct H10.
              destruct H10 ; unpack ; subst ; [|rewrite in_set_st_eq in H6; stpath_tac].
              destruct H10 ; eauto.
              destruct H9 ; unpack. eauto.
        + destruct (classic (x' = p)) ; try subst x'.
          - unfold node_of_orientation in H5.
            destruct o.
            * destruct H5. destruct H5.
              { destruct H5. destruct H7.
                + destruct H5. unpack. rewrite H5.
                  repeat split ; auto ; [right; auto|].
                  left. right. auto.
                + destruct H5. rewrite H5.
                  repeat split ; auto ; [right; auto|].
                  intro. apply H7. destruct H8. exists x0.
                  destruct H8 ; unpack ; try discriminate.
                  destruct H8 ; auto. assert (p \in D'). stdomain_tac. contradiction.
              }
            * destruct H5. destruct H5.
              { destruct H5. destruct H7.
                + destruct H5. unpack. rewrite H5.
                  repeat split ; auto ; [|right; auto].
                  left. right. auto.
                + destruct H5. rewrite H5.
                  repeat split ; auto ; [right; auto|].
                  intro. apply H7. destruct H8. exists x0.
                  destruct H8 ; unpack ; try discriminate.
                  destruct H8 ; auto. assert (p \in D'). stdomain_tac. contradiction.
              }
          - specialize (H4 x' (conj H6 (conj Hx H7))).
            rewrite H4. 
            pose proof (conj Hx H5).
            apply H in Hx. destruct (M !! x') ; try contradiction.
            unpack.
            destruct c ; unpack.
            * destruct o.
              {
                repeat split ; auto.
                + left. right. repeat split ; auto.
                  pose proof
                   (if_node_not_in_domain_and_edge_then_end_also_not_in_domain_if_bst
                      p D V W F x' x LEFT l).
                  apply H13 ; auto. intro. subst. apply H7. stpath_tac.
                + left. right. repeat split ; auto.
                  pose proof
                   (if_node_not_in_domain_and_edge_then_end_also_not_in_domain_if_bst
                      p D V W F x' x RIGHT l0).
                  apply H13 ; auto. intro. subst. apply H7. stpath_tac.                
              }
              {
                repeat split ; auto.
                + left. right. repeat split ; auto.
                  pose proof
                   (if_node_not_in_domain_and_edge_then_end_also_not_in_domain_if_bst
                      p D V W F x' x LEFT l).
                  apply H13 ; auto. intro. subst. apply H7. stpath_tac.
                + left. right. repeat split ; auto.
                  pose proof
                   (if_node_not_in_domain_and_edge_then_end_also_not_in_domain_if_bst
                      p D V W F x' x RIGHT l0).
                  apply H13 ; auto. intro. subst. apply H7. stpath_tac.        
              }
            * destruct o.
              {
                repeat split ; auto.
                + left. right. repeat split ; auto.
                  pose proof
                   (if_node_not_in_domain_and_edge_then_end_also_not_in_domain_if_bst
                      p D V W F x' x LEFT l).
                  apply H13 ; auto. intro. subst. apply H7. stpath_tac.
                + intro. destruct H13. 
                  destruct H13 ; unpack ; subst ; try discriminate.
                  destruct H13.
                  assert (x' \in D'). stdomain_tac. contradiction.
                  apply H11. exists x0.
                  destruct H12. auto.
              }
              {
                repeat split ; auto.
                + left. right. repeat split ; auto.
                  pose proof
                   (if_node_not_in_domain_and_edge_then_end_also_not_in_domain_if_bst
                      p D V W F x' x LEFT l).
                  apply H13 ; auto. intro. subst. apply H7. stpath_tac.
                + intro. destruct H13. 
                  destruct H13 ; unpack ; subst ; eauto.
                  destruct H13.
                  assert (x' \in D'). stdomain_tac. contradiction.
                  apply H11. exists x0.
                  destruct H12. auto.
              }
            * destruct o.
              {
                repeat split ; auto.
                + left. right. repeat split ; auto.
                  pose proof
                   (if_node_not_in_domain_and_edge_then_end_also_not_in_domain_if_bst
                      p D V W F x' x RIGHT l).
                  apply H13 ; auto. intro. subst. apply H7. stpath_tac.
                + intro. destruct H13. 
                  destruct H13 ; unpack ; subst ; eauto. 
                  destruct H13.
                  assert (x' \in D'). stdomain_tac. contradiction.
                  apply H11. exists x0.
                  destruct H12. auto.
              }
              {
                repeat split ; auto.
                + left. right. repeat split ; auto.
                  pose proof
                   (if_node_not_in_domain_and_edge_then_end_also_not_in_domain_if_bst
                      p D V W F x' x RIGHT l).
                  apply H13 ; auto. intro. subst. apply H7. stpath_tac.
                + intro. destruct H13. 
                  destruct H13 ; unpack ; subst ; eauto.
                  destruct H13.
                  assert (x' \in D'). stdomain_tac. contradiction.
                  apply H11. exists x0.
                  destruct H12. auto.
              }
            * destruct o.
              {
                repeat split ; auto.
                + intro. destruct H13. 
                  destruct H13 ; unpack ; subst ; eauto. 
                  destruct H13.
                  assert (x' \in D'). stdomain_tac. contradiction.
                  apply H10. exists x0.
                  destruct H12. auto.
                + intro. destruct H13. 
                  destruct H13 ; unpack ; subst ; eauto. 
                  destruct H13.
                  assert (x' \in D'). stdomain_tac. contradiction.
                  apply H11. exists x0.
                  destruct H12. auto.
              }
              {
                repeat split ; auto.
                + intro. destruct H13. 
                  destruct H13 ; unpack ; subst ; eauto. 
                  destruct H13.
                  assert (x' \in D'). stdomain_tac. contradiction.
                  apply H10. exists x0.
                  destruct H12. auto.
                + intro. destruct H13. 
                  destruct H13 ; unpack ; subst ; eauto. 
                  destruct H13.
                  assert (x' \in D'). stdomain_tac. contradiction.
                  apply H11. exists x0.
                  destruct H12. auto.
              }
      Qed.

End MapstoMemory.

Section MemoryFunctionalRotateRight.
  
  (* Graph structure *)
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable M : gmap elem content. (* view of the memory *)

  (*
    
                p              l0
               / \            / \
              l  l0    ->    p  l2
                 /\         /\
               l1 l2       l l1

   *)

  (* WHERE ROOT IS BINARY *)
  
  Lemma Mem_rotate_right_BB : forall (F : EdgeSet) p l l0 l1 l2 vp vl0,
      Inv p D F V W ->
      M !! p  = Some (NodeB vp l l0) ->
      M !! l0 = Some (NodeB vl0 l1 l2) ->
      Mem D F V M ->
      Mem D (update_edge (update_edge F l0 l1 p LEFT) p l0 l1 RIGHT) V
          (<[p:=NodeB vp l l1]> (<[l0:=NodeB vl0 p l2]> M)).
  Proof.
    intros F p l l0 l1 l2 vp vl0 Inv **.
    unfold Mem. intros.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree [finite _]]]]]].
    apply H1 in rootisindomain as Ml. rewrite H in Ml. unpack.

    assert (l0 \in D). stdomain_tac.
    apply H1 in H6. rewrite H0 in H6. unpack.
    
    assert (path F l l). stpath_tac.
    assert (path F l0 l1). stpath_tac.
    assert (path F l0 l2). stpath_tac.
    destruct (bool_decide (x = p)) eqn:E.
    + apply bool_decide_eq_true in E. subst. rewrite lookup_insert.
      split.
      - left. repeat split ; [right| right|] ; stlink_tac ; stpath_tac.        
        repeat split ; auto. left.
        repeat split ; auto ; left ; stlink_tac ; stpath_tac.
      - split ; auto. right ; auto.
    + apply bool_decide_eq_false in E.
      rewrite lookup_insert_ne ; auto.
      destruct (bool_decide (x = l0)) eqn:E1 ;
        [apply bool_decide_eq_true in E1;subst|apply bool_decide_eq_false in E1].
      - rewrite lookup_insert.
        split.
        * left. repeat split ; auto. right. auto.
        * split ; auto. left. repeat split ; auto.
          left. repeat split ; auto ; right. stlink_tac.  stpath_tac.
      - rewrite lookup_insert_ne ; auto.
        apply H1 in H2. destruct (M !! x) ; auto.
        destruct c ; auto ; unpack ; subst.
        * repeat split ; auto ;
            left ; repeat split ; auto ; left ; repeat split ; auto. 
        * repeat split ; auto.
          left ; repeat split ; auto. left ; repeat split ; auto. 
          intro. destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H13 ; unpack ; [|subst ; discriminate].
          apply H12. exists x0 ; auto.
        * repeat split ; auto.
          left ; repeat split ; auto. left ; repeat split ; auto. 
          intro. destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H13 ; unpack ; [|subst ; contradiction]. 
          apply H12. exists x0 ; auto.
        * repeat split ; auto ; intro.
          { apply H2. destruct H5.
            destruct H5 ; unpack ; [|subst ; contradiction].
            destruct H13 ; unpack ; [|subst ; contradiction].
            exists x0 ; auto.
          }
          { apply H12. destruct H5.
            destruct H5 ; unpack ; [|subst ; contradiction].
            destruct H13 ; unpack ; [|subst ; contradiction].
            exists x0 ; auto.
          }
  Qed.

  Lemma Mem_rotate_right_BR : forall (F : EdgeSet) p p1 p2 p3 vp vp2,
      Inv p D F V W -> 
      M !! p  = Some (NodeB vp p1 p2) ->
      M !! p2 = Some (NodeR vp2 p3) ->
      Mem D F V M ->
      Mem D (add_edge (remove_edge F p p2) p2 p LEFT) V
          (<[p:=NodeL vp p1]> (<[p2:=NodeB vp2 p p3]> M)).
  Proof.
    intros F p l l0 l1 vp vl0 Inv **.
    unfold Mem. intros.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree [finite _]]]]]].
    apply H1 in rootisindomain as Ml. rewrite H in Ml. unpack.

    assert (l0 \in D). stdomain_tac.
    apply H1 in H6. rewrite H0 in H6. unpack.
    
    assert (path F l l). stpath_tac.
    assert (path F l0 l0). stpath_tac.
    assert (path F l0 l1). stpath_tac.
    destruct (bool_decide (x = p)) eqn:E.
    + apply bool_decide_eq_true in E. subst. rewrite lookup_insert.
      split.
      - left. repeat split ; auto. right ; stlink_tac.
      - split ; auto. intro.
        do 2destruct H5 ; unpack ; subst ; try discriminate.
        destruct H5. destruct H5 ; try contradiction.
        apply H5. stlink_tac.
    + apply bool_decide_eq_false in E.
      rewrite lookup_insert_ne ; auto.
      destruct (bool_decide (x = l0)) eqn:E1 ;
        [apply bool_decide_eq_true in E1;subst|apply bool_decide_eq_false in E1].
      - rewrite lookup_insert.
        split.
        * right. auto.
        * split ; auto. left. split ; auto.
      - rewrite lookup_insert_ne ; auto.
        apply H1 in H2. destruct (M !! x) ; auto.
        destruct c ; auto ; unpack ; subst.
        * repeat split ; auto ;
            left ; repeat split ; auto ; left ; repeat split ; auto. 
        * repeat split ; auto.
          left ; repeat split ; auto. 
          intro. destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H5.
          apply H12. exists x0 ; auto.
        * repeat split ; auto.
          left ; repeat split ; auto. 
          intro. destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H5.  apply H12 ; eauto.
        * repeat split ; auto ; intro.
          { apply H2. destruct H5.
            destruct H5 ; unpack ; [|subst ; contradiction].
            destruct H5. eauto.
          }
          { apply H12. destruct H5.
            destruct H5 ; unpack ; [|subst ; contradiction].
            destruct H5.
            exists x0 ; auto.
          }
  Qed.

  Lemma Mem_rotate_right_BL : forall (F : EdgeSet) p p1 p2 p3 vp vp2,
      Inv p D F V W ->
      M !! p  = Some (NodeB vp p1 p2) ->
      M !! p2 = Some (NodeL vp2 p3) ->
      Mem D F V M ->
      Mem D (update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT) V
           (<[p:=NodeB vp p1 p3]> (<[p2:=NodeL vp2 p]> M)).
  Proof.
    intros F p l l0 l1 vp vl0 Inv **.
    unfold Mem. intros.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree [finite _]]]]]].
    apply H1 in rootisindomain as Ml. rewrite H in Ml. unpack.

    assert (l0 \in D). stdomain_tac.
    apply H1 in H6. rewrite H0 in H6. unpack.
    
    assert (path F l l). stpath_tac.
    assert (path F l0 l0). stpath_tac.
    assert (path F l0 l1). stpath_tac.
    
    destruct (bool_decide (x = p)) eqn:E.
    + apply bool_decide_eq_true in E. subst. rewrite lookup_insert.
      split ; auto.
      - left. repeat split ; [right|right|] ; stlink_tac ; stpath_tac.
        left. repeat split ; [right|right|] ; stlink_tac ; stpath_tac ; auto.
      - repeat split ; auto. right. auto.
    + apply bool_decide_eq_false in E.
      rewrite lookup_insert_ne ; auto.
      destruct (bool_decide (x = l0)) eqn:E1 ;
        [apply bool_decide_eq_true in E1;subst|apply bool_decide_eq_false in E1].
      - rewrite lookup_insert.
        split.
        * left.
          repeat split ; [left|right|] ; stlink_tac.
          right ; auto.
        * split ; auto.
          intro.
          do 2destruct H5 ; unpack ; subst ; [|contradiction].
          destruct H12 ; unpack ; subst ; [|discriminate].
          apply H7. exists x ; auto.
      - rewrite lookup_insert_ne ; auto.
        apply H1 in H2. destruct (M !! x) ; auto.
        destruct c ; auto ; unpack ; subst.
        * repeat split ; auto.
          { left. repeat split ; auto. left. repeat split ; auto. }
          { left. repeat split ; auto. left. repeat split ; auto. }
        * repeat split ; auto.
          left ; repeat split ; auto.
          left ; repeat split ; auto.
          intro. destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H13 ; unpack ; try discriminate.
          apply H12. eauto.
        * repeat split ; auto.
          left ; repeat split ; auto.
          left ; repeat split ; auto.
          intro. destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H13 ; unpack ; subst ; try contradiction.
          apply H12. eauto.
        * repeat split ; auto ; intro.
          { apply H2. destruct H5.
            destruct H5 ; unpack ; [|subst ; contradiction].
            destruct H13 ; unpack ; eauto ; discriminate.
          }
          { apply H12. destruct H5.
            destruct H5 ; unpack ; [|subst ; contradiction].
            destruct H13 ; unpack ; subst ; eauto.
          }
  Qed.

  Lemma Mem_rotate_right_BN : forall (F : EdgeSet) p p1 p2 vp vp2,
      Inv p D F V W -> 
      M !! p  = Some (NodeB vp p1 p2) ->
      M !! p2 = Some (NodeN vp2) ->
      Mem D F V M ->
      Mem D (add_edge (remove_edge F p p2) p2 p LEFT) V
          (<[p:=NodeL vp p1]> (<[p2:=NodeL vp2 p]> M)).
  Proof.
    intros F p l l0 vp vl0 Inv **.
    unfold Mem. intros.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree [finite _]]]]]].
    apply H1 in rootisindomain as Ml. rewrite H in Ml. unpack.

    assert (l0 \in D). stdomain_tac.
    apply H1 in H6. rewrite H0 in H6. unpack.
    
    assert (path F l l). stpath_tac.
    assert (path F l0 l0). stpath_tac.
    
    destruct (bool_decide (x = p)) eqn:E.
    + apply bool_decide_eq_true in E. subst. rewrite lookup_insert.
      split ; auto.
      - left. 
        repeat split ; auto. right. stlink_tac.
      - repeat split ; auto. intro.
        do 2destruct H5 ; unpack ; subst ; try discriminate.
        destruct H5. destruct H5 ; try contradiction.
        apply H5. stlink_tac. 
    + apply bool_decide_eq_false in E.
      rewrite lookup_insert_ne ; auto.
      destruct (bool_decide (x = l0)) eqn:E1 ;
        [apply bool_decide_eq_true in E1;subst|apply bool_decide_eq_false in E1].
      - rewrite lookup_insert.
        split.
        * right. auto.
        * repeat split ; auto. intro.
          do 2destruct H5 ; unpack ; subst ; try discriminate.
          destruct H5. apply H6. eauto.
      - rewrite lookup_insert_ne ; auto.
        apply H1 in H2. destruct (M !! x) ; auto.
        destruct c ; auto ; unpack ; subst.
        * repeat split ; auto.
          { left. repeat split ; auto. }
          { left. repeat split ; auto. } 
        * repeat split ; auto.
          { left. repeat split ; auto. }
          { intro. do 2destruct H5 ; unpack ; subst ; try discriminate.
            destruct H5. apply H11. eauto. }
        * repeat split ; auto.
          { left. repeat split ; auto. }
          { intro. destruct H5.
            destruct H5 ;
              unpack ; subst ; try contradiction.
            destruct H5. apply H11. eauto.
          }
        * repeat split ; auto.
          { intro. do 2destruct H5 ;
            unpack ; subst ; try contradiction.
            destruct H5. apply H2. eauto. }
          { intro. destruct H5.
            destruct H5 ;
              unpack ; subst ; try contradiction.
            destruct H5. apply H11. eauto.
          }
  Qed.

  
  (* WHERE ROOT IS ONLY RIGHT *)

  Lemma Mem_rotate_right_RB : forall (F : EdgeSet) p p2 p3 p4 vp vp2,
      Inv p D F V W -> 
      M !! p  = Some (NodeR vp p2) ->
      M !! p2 = Some (NodeB vp2 p3 p4) ->
      Mem D F V M ->
      Mem D (update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT) V
          (<[p:=NodeR vp p3]> (<[p2:=NodeB vp2 p p4]> M)).
  Proof.
    intros F p l0 l1 l2 vp vl0 Inv **.
    unfold Mem. intros.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree [finite _]]]]]].
    apply H1 in rootisindomain as Ml. rewrite H in Ml. unpack.

    assert (l0 \in D). stdomain_tac.
    apply H1 in H6. rewrite H0 in H6. unpack.
    
    assert (path F l0 l1). stpath_tac.
    assert (path F l0 l2). stpath_tac.
    destruct (bool_decide (x = p)) eqn:E.
    + apply bool_decide_eq_true in E. subst. rewrite lookup_insert.
      split.
      - right.  auto. 
      - split ; auto. intro. destruct H5.
        destruct H5 ; unpack ; subst ; try discriminate.
        destruct H11 ; unpack ; subst ; [|destruct H5 ; contradiction].
        apply H4 ; eauto.
    + apply bool_decide_eq_false in E.
      rewrite lookup_insert_ne ; auto.
      destruct (bool_decide (x = l0)) eqn:E1 ;
        [apply bool_decide_eq_true in E1;subst|apply bool_decide_eq_false in E1].
      - rewrite lookup_insert.
        split.
        * left. repeat split ; auto. right. auto.
        * split ; auto. left. repeat split ; auto.
          left. repeat split ; auto ; right. stlink_tac.  stpath_tac.
      - rewrite lookup_insert_ne ; auto.
        apply H1 in H2. destruct (M !! x) ; auto.
        destruct c ; auto ; unpack ; subst.
        * repeat split ; auto ;
            left ; repeat split ; auto ; left ; repeat split ; auto. 
        * repeat split ; auto.
          left ; repeat split ; auto. left ; repeat split ; auto. 
          intro. destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H12 ; unpack ; [|subst ; discriminate].
          apply H11. exists x0 ; auto.
        * repeat split ; auto.
          left ; repeat split ; auto. left ; repeat split ; auto. 
          intro. destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H12 ; unpack ; [|subst ; contradiction]. 
          apply H11. exists x0 ; auto.
        * repeat split ; auto ; intro.
          { apply H2. destruct H5.
            destruct H5 ; unpack ; [|subst ; contradiction].
            destruct H12 ; unpack ; [|subst ; contradiction].
            exists x0 ; auto.
          }
          { apply H11. destruct H5.
            destruct H5 ; unpack ; [|subst ; contradiction].
            destruct H12 ; unpack ; [|subst ; contradiction].
            exists x0 ; auto.
          }
  Qed.
  
  Lemma Mem_rotate_right_RL : forall (F : EdgeSet) p p2 p3 vp vp2,
      Inv p D F V W -> 
      M !! p  = Some (NodeR vp p2) ->
      M !! p2 = Some (NodeL vp2 p3) ->
      Mem D F V M ->
      Mem D (update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT) V
          (<[p:=NodeR vp p3]> (<[p2:=NodeL vp2 p]> M)).
  Proof.
    intros F p p2 p3 vp vp2 Inv **.
    unfold Mem. intros.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree [finite _]]]]]].
    apply H1 in rootisindomain as Ml. rewrite H in Ml. unpack.

    assert (p2 \in D). stdomain_tac.
    apply H1 in H6. rewrite H0 in H6. unpack.
    
    destruct (bool_decide (x = p)) eqn:E.
    + apply bool_decide_eq_true in E. subst. rewrite lookup_insert.
      split.
      - right.  auto. 
      - split ; auto. intro. destruct H5.
        destruct H5 ; unpack ; subst ; try discriminate.
        destruct H9 ; unpack ; subst ; [|destruct H5 ; contradiction].
        apply H4 ; eauto.
    + apply bool_decide_eq_false in E.
      rewrite lookup_insert_ne ; auto.
      destruct (bool_decide (x = p2)) eqn:E1 ;
        [apply bool_decide_eq_true in E1;subst|apply bool_decide_eq_false in E1].
      - rewrite lookup_insert.
        split.
        * left. repeat split ; auto. right. auto.
        * split ; auto. intro.
          destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H9 ; unpack ; [|subst ; discriminate].
          apply H7 ; eauto.
      - rewrite lookup_insert_ne ; auto.
        apply H1 in H2. destruct (M !! x) ; auto.
        destruct c ; auto ; unpack ; subst.
        * repeat split ; auto ;
            left ; repeat split ; auto ; left ; repeat split ; auto. 
        * repeat split ; auto.
          left ; repeat split ; auto. left ; repeat split ; auto. 
          intro. destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H10 ; unpack ; [|subst ; discriminate].
          apply H9. exists x0 ; auto.
        * repeat split ; auto.
          left ; repeat split ; auto. left ; repeat split ; auto. 
          intro. destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H10 ; unpack ; [|subst ; contradiction]. 
          apply H9. eauto.
        * repeat split ; auto ; intro.
          { apply H2. destruct H5.
            destruct H5 ; unpack ; [|subst ; contradiction].
            destruct H10 ; unpack ; [|subst ; contradiction].
            exists x0 ; auto.
          }
          { apply H9. destruct H5.
            destruct H5 ; unpack ; [|subst ; contradiction].
            destruct H10 ; unpack ; [|subst ; contradiction].
            exists x0 ; auto.
          }
  Qed.
  
  Lemma Mem_rotate_right_RR : forall (F : EdgeSet) p p2 p3 vp vp2,
      Inv p D F V W -> 
      M !! p  = Some (NodeR vp p2) ->
      M !! p2 = Some (NodeR vp2 p3) ->
      Mem D F V M ->
      Mem D (add_edge (remove_edge F p p2) p2 p LEFT) V
          (<[p:=NodeN vp]> (<[p2:=NodeB vp2 p p3]> M)).
  Proof.
    intros F p p2 p3 vp vp2 Inv **.
    unfold Mem. intros.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree [finite _]]]]]].
    apply H1 in rootisindomain as Ml. rewrite H in Ml. unpack.

    assert (p2 \in D). stdomain_tac.
    apply H1 in H6. rewrite H0 in H6. unpack.
    
    destruct (bool_decide (x = p)) eqn:E.
    + apply bool_decide_eq_true in E. subst. rewrite lookup_insert.
      split.
      - intro.
        destruct H5.
        destruct H5 ; unpack ; subst ; [|discriminate].
        destruct H5. assert (x = p2). stlink_tac. subst.
        destruct H5 ; contradiction.
      - split ; auto. intro. destruct H5.
        destruct H5 ; unpack ; subst ; [|stlink_tac].
        destruct H5. apply H4. eauto.
    + apply bool_decide_eq_false in E.
      rewrite lookup_insert_ne ; auto.
      destruct (bool_decide (x = p2)) eqn:E1 ;
        [apply bool_decide_eq_true in E1;subst|apply bool_decide_eq_false in E1].
      - rewrite lookup_insert.
        split.
        * right. auto. 
        * split ; auto. left.
          split ; auto.
      - rewrite lookup_insert_ne ; auto.
        apply H1 in H2. destruct (M !! x) ; auto.
        destruct c ; auto ; unpack ; subst.
        * repeat split ; auto ;
            left ; repeat split ; auto ; left ; repeat split ; auto. 
        * repeat split ; auto.
          left ; repeat split ; auto. 
          intro. destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H5. apply H9. eauto.
        * repeat split ; auto.
          left ; repeat split ; auto. 
          intro. destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H5. apply H9. eauto.
        * repeat split ; auto ; intro.
          { apply H2. destruct H5.
            destruct H5 ; unpack ; [|subst ; contradiction].
            destruct H5. eauto.
          }
          { apply H9. destruct H5.
            destruct H5 ; unpack ; [|subst ; contradiction].
            destruct H5. eauto.
          }
  Qed.
  
  Lemma Mem_rotate_right_RN : forall (F : EdgeSet) p p2 vp vp2,
      Inv p D F V W -> 
      M !! p  = Some (NodeR vp p2) ->
      M !! p2 = Some (NodeN vp2) ->
      Mem D F V M ->
      Mem D (add_edge (remove_edge F p p2) p2 p LEFT) V
          (<[p:=NodeN vp]> (<[p2:=NodeL vp2 p]> M)).
  Proof.
    intros F p p2 vp vp2 Inv **.
    unfold Mem. intros.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree [finite _]]]]]].
    apply H1 in rootisindomain as Ml. rewrite H in Ml. unpack.

    assert (p2 \in D). stdomain_tac.
    apply H1 in H6. rewrite H0 in H6. unpack.
    
    destruct (bool_decide (x = p)) eqn:E.
    + apply bool_decide_eq_true in E. subst. rewrite lookup_insert.
      split.
      - intro.
        destruct H5.
        destruct H5 ; unpack ; subst ; [|discriminate].
        destruct H5. assert (x = p2). stlink_tac. subst.
        destruct H5 ; contradiction.
      - split ; auto. intro. destruct H5.
        destruct H5 ; unpack ; subst ; [|stlink_tac].
        destruct H5. apply H4. eauto.
    + apply bool_decide_eq_false in E.
      rewrite lookup_insert_ne ; auto.
      destruct (bool_decide (x = p2)) eqn:E1 ;
        [apply bool_decide_eq_true in E1;subst|apply bool_decide_eq_false in E1].
      - rewrite lookup_insert.
        split.
        * right. auto. 
        * split ; auto. intro.
          apply H6.
          destruct H5.
          destruct H5 ; unpack ; subst ; [|discriminate].
          destruct H5. eauto.
      - rewrite lookup_insert_ne ; auto.
        apply H1 in H2. destruct (M !! x) ; auto.
        destruct c ; auto ; unpack ; subst.
        * repeat split ; auto ;
            left ; repeat split ; auto ; left ; repeat split ; auto. 
        * repeat split ; auto.
          left ; repeat split ; auto. 
          intro. destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H5. apply H9. eauto.
        * repeat split ; auto.
          left ; repeat split ; auto. 
          intro. destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H5. apply H9. eauto.
        * repeat split ; auto ; intro.
          { apply H2. destruct H5.
            destruct H5 ; unpack ; [|subst ; contradiction].
            destruct H5. eauto.
          }
          { apply H9. destruct H5.
            destruct H5 ; unpack ; [|subst ; contradiction].
            destruct H5. eauto.
          }
  Qed.
  
End MemoryFunctionalRotateRight.


Section MemoryFunctionalRotateRight.
  
  (* Graph structure *)
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable M : gmap elem content. (* view of the memory *)

  (*
    
                p              l0
               / \            / \
              l  l0    ->    p  l2
                 /\         /\
               l1 l2       l l1

   *)

  (* WHERE ROOT IS BINARY *)
  
  Lemma Mem_rotate_left_BB : forall (F : EdgeSet) p p1 p2 p3 p4 vp vp1,
      Inv p D F V W ->
      let F'' :=  (update_edge (update_edge F p1 p4 p RIGHT) p p1 p4 LEFT) in
      let M' := (<[p:=NodeB vp p4 p2]> (<[p1:=NodeB vp1 p3 p]> M)) in 
      M !! p  = Some (NodeB vp p1 p2) ->
      M !! p1 = Some (NodeB vp1 p3 p4) ->
      Mem D F V M ->
      Mem D F'' V M'.
  Proof.
    intros F p p1 p2 p3 p4 vp vp1 Inv **.
    unfold Mem. intros.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree [finite _]]]]]].
    apply H1 in rootisindomain as Ml. rewrite H in Ml. unpack.

    assert (p1 \in D). stdomain_tac.
    apply H1 in H6. rewrite H0 in H6. unpack.
    
    assert (path F p2 p2). stpath_tac.
    assert (path F p3 p3). stpath_tac.
    assert (path F p4 p4). stpath_tac.
    assert (path F p1 p4). stpath_tac.
    assert (path F p1 p3). stpath_tac.
    
    destruct (bool_decide (x = p)) eqn:E.
    + apply bool_decide_eq_true in E. subst. rewrite lookup_insert.
      split.
      - right. auto.
      - split ; auto. left.
        repeat split ; auto ; [right|right|] ; stlink_tac ; stpath_tac.
        left. repeat split ; auto ; left ; stlink_tac.
    + apply bool_decide_eq_false in E.
      rewrite lookup_insert_ne ; auto.
      destruct (bool_decide (x = p1)) eqn:E1 ;
        [apply bool_decide_eq_true in E1;subst|apply bool_decide_eq_false in E1].
      - rewrite lookup_insert.
        split.
        * left. repeat split ; auto. left.
          repeat split ; auto ; right ; stpath_tac.
        * split ; auto. left. repeat split ; auto.
          right. auto.
      - rewrite lookup_insert_ne ; auto.
        apply H1 in H2. destruct (M !! x) ; auto.
        destruct c ; auto ; unpack ; subst.
        * repeat split ; auto ;
            left ; repeat split ; auto ; left ; repeat split ; auto. 
        * repeat split ; auto.
          left ; repeat split ; auto. left ; repeat split ; auto. 
          intro. destruct H5.
          destruct H5 ; unpack ; [|subst ; contradiction].
          destruct H15 ; unpack ; subst ; try contradiction.
          apply H14.  eauto. 
        * repeat split ; auto.
          { left. repeat split ; auto. left. repeat split ; auto. }
          { intro. do 2destruct H5 ; unpack ; subst ; try contradiction.
            destruct H15 ; unpack ; subst ; try eauto ; discriminate. }
        * repeat split ; auto ; intro.
          { apply H2. destruct H5.
            destruct H5 ; unpack ; [|subst ; contradiction].
            destruct H15 ; unpack ; subst ; try contradiction.
            eauto.
          }
          { 
            destruct H5 ; unpack ; subst.
            destruct H5 ; unpack ; subst ; try contradiction.
            destruct H15 ; unpack ; subst ; try contradiction.
            eauto.
          }
  Qed.

  Lemma Mem_rotate_left_BL : forall (F : EdgeSet) p p1 p2 p3 vp vp1,
      Inv p D F V W ->
      let F'' :=  (add_edge (remove_edge F p p1) p1 p RIGHT) in
      let M' := (<[p:=NodeR (V p) p2]> (<[p1:=NodeB vp1 p3 p]> M)) in 
      M !! p  = Some (NodeB vp p1 p2) ->
      M !! p1 = Some (NodeL vp1 p3) ->
      Mem D F V M ->
      Mem D F'' V M'.
  Proof.
  Admitted.

  Lemma Mem_rotate_left_BR : forall (F : EdgeSet) p p1 p2 p4 vp vp1,
      Inv p D F V W ->
      let F'' :=  (update_edge (update_edge F p1 p4 p RIGHT) p p1 p4 LEFT) in
      let M' := (<[p:=NodeB (V p) p4 p2]> (<[p1:=NodeR vp1 p]> M)) in 
      M !! p  = Some (NodeB vp p1 p2) ->
      M !! p1 = Some (NodeR vp1 p4) ->
      Mem D F V M ->
      Mem D F'' V M'.
  Proof.
  Admitted.

  Lemma Mem_rotate_left_BN : forall (F : EdgeSet) p p1 p2 vp vp1,
      Inv p D F V W ->
      let F'' :=  (add_edge (remove_edge F p p1) p1 p RIGHT) in
      let M' := (<[p:=NodeR (V p) p2]> (<[p1:=NodeR vp1 p]> M)) in 
      M !! p  = Some (NodeB vp p1 p2) ->
      M !! p1 = Some (NodeN vp1) ->
      Mem D F V M ->
      Mem D F'' V M'.
  Proof.
  Admitted.

  Lemma Mem_rotate_left_LB : forall (F : EdgeSet) p p1 p3 p4 vp vp1,
      Inv p D F V W ->
      let F'' :=  (update_edge (update_edge F p1 p4 p RIGHT) p p1 p4 LEFT) in
      let M' := (<[p:=NodeL (V p) p4]> (<[p1:=NodeB vp1 p3 p]> M)) in 
      M !! p  = Some (NodeL vp p1) ->
      M !! p1 = Some (NodeB vp1 p3 p4) ->
      Mem D F V M ->
      Mem D F'' V M'.
  Proof.
  Admitted.
  
  Lemma Mem_rotate_left_LL : forall (F : EdgeSet) p p1 p3 vp vp1,
      Inv p D F V W ->
      let F'' :=  (add_edge (remove_edge F p p1) p1 p RIGHT) in
      let M' := (<[p:=NodeN (V p)]> (<[p1:=NodeB vp1 p3 p]> M)) in 
      M !! p  = Some (NodeL vp p1) ->
      M !! p1 = Some (NodeL vp1 p3) ->
      Mem D F V M ->
      Mem D F'' V M'.
  Proof.
  Admitted.
  
  Lemma Mem_rotate_left_LR : forall (F : EdgeSet) p p1 p4 vp vp1,
      Inv p D F V W ->
      let F'' :=  (update_edge (update_edge F p1 p4 p RIGHT) p p1 p4 LEFT) in
      let M' := (<[p:=NodeL (V p) p4]> (<[p1:=NodeR vp1 p]> M)) in 
      M !! p  = Some (NodeL vp p1) ->
      M !! p1 = Some (NodeR vp1 p4) ->
      Mem D F V M ->
      Mem D F'' V M'.
  Proof.
  Admitted.
  
  Lemma Mem_rotate_left_LN : forall (F : EdgeSet) p p1 vp vp1,
      Inv p D F V W ->
      let F'' :=  (add_edge (remove_edge F p p1) p1 p RIGHT) in
      let M' := (<[p:=NodeN (V p)]> (<[p1:=NodeR vp1 p]> M)) in 
      M !! p  = Some (NodeL vp p1) ->
      M !! p1 = Some (NodeN vp1) ->
      Mem D F V M ->
      Mem D F'' V M'.
  Proof.
  Admitted.
    
End MemoryFunctionalRotateRight.
