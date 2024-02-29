From ST Require Import Code STorientation 
     STpredicate STpath STedgeset STedgesetrotateroot STlink STmemory STproof STdomain.
From iris_time.heap_lang Require Import notation lib.assert.
From iris_time.heap_lang Require Export lang.
From iris_time.heap_lang Require Import proofmode.
From iris_time Require Import Combined.

From iris.bi Require Import big_op.
From iris_time.heap_lang Require Import proofmode.
From iris_time Require Import Combined.

From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual
                        LibInt.

Notation elem := loc.

(*

        Proved:
                
                       p
                      / \
                    p1  p2

                rotate_right_BB_st
                rotate_right_BR_st
                rotate_right_BL_st
                rotate_right_BN_st
                rotate_right_RB_st
                rotate_right_RL_st
                rotate_right_RR_st
                rotate_right_RN_st

                       p
                      / \
                        p1

        Other theorems not needed:
              rotate_right_LX_st doesn't work
              rotate_right_N_st doesn't work

 *)

Section RotateRightRootSpecificationMemory.

  
  Context `{!tctrHeapG Σ} (nmax : nat).
  
  Variable v : val.
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable F : EdgeSet.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)
  
  Lemma rotate_right_BB_st' (pp p p1 p2 p3 p4 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeB vp2 p3 p4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
      {{{ RET #() ; pp ↦ #p2 ∗
          ⌜Inv p2 D (update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT) V W⌝ ∗
          ⌜Mem D (update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT) V
           (<[p:=NodeB (V p) p1 p3]> (<[p2:=NodeB vp2 p p4]> M))⌝ ∗
                       mapsto_M (<[p:=NodeB (V p) p1 p3]> (<[p2:=NodeB vp2 p p4]> M)) }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures. 

    (*get value of p2*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeB vp2 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (left_child %V #p2).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (right_child #p2).    
    iApply (right_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value #p2).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp2 p p4) = Some (InjRV (#vp2, (#p, #p4)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc (<[p2:=NodeB vp2 p p4]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    assert (¬(p2 = p)). stlink_tac.
    rewrite lookup_insert_ne ; auto.
    
    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.
    
    (* Get value of left child *)
    wp_bind (left_child #p).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj. wp_store.
    wp_seq. wp_store.
    
    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeB (V p) p1 p3) = Some (SOMEV (#(V p), (#p1, #p3))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
     
    iApply "H" ; iFrame. unfold ST.
    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p2 p3 RIGHT).
      apply update_comm_inv in H13 ; auto. stlink_tac.
    * pose proof (Mem_rotate_right_BB D V W M F p p1 p2 p3 p4 (V p) vp2).
      apply H13 ; auto.
  Qed.

  Lemma rotate_right_BL_st' (pp p p1 p2 p3 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeL vp2 p3) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
      {{{ RET #() ; pp ↦ #p2 ∗
          ⌜Inv p2 D (update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT) V W⌝ ∗
          ⌜Mem D (update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT) V
           (<[p:=NodeB (V p) p1 p3]> (<[p2:=NodeL vp2 p]> M))⌝ ∗
                       mapsto_M (<[p:=NodeB (V p) p1 p3]> (<[p2:=NodeL vp2 p]> M)) }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures.
    
    (*get value of p2*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeL vp2 p3) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (left_child %V #p2).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (right_child #p2).    
    iApply (right_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of node *)
    wp_bind (value #p2).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeL vp2 p) = Some (InjRV (#vp2, (#p, InjLV #())))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p2:=NodeL vp2 p]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    rewrite lookup_insert_ne ; auto ; stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (left_child #p).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj. wp_store.
    wp_seq. wp_store.

    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeB (V p) p1 p3) = Some (SOMEV (#(V p), (#p1, #p3))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
    
    iApply "H" ; iFrame. 
    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p2 p3 RIGHT).
      apply update_comm_inv in H13 ; auto ; stlink_tac.
    * pose proof (Mem_rotate_right_BL D V W M F p p1 p2 p3 (V p)).
      apply H13 ; auto.      
  Qed.  
      
  Lemma rotate_right_BR_st' (pp p p1 p2 p3 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeR vp2 p3) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
      {{{ RET #() ; pp ↦ #p2 ∗
          ⌜Inv p2 D ((add_edge (remove_edge F p p2) p2 p LEFT)) V W ⌝ ∗
             ⌜Mem D ((add_edge (remove_edge F p p2) p2 p LEFT)) V
             (<[p:=NodeL (V p) p1]> (<[p2:=NodeB vp2 p p3]> M))⌝ ∗
        mapsto_M (<[p:=NodeL (V p) p1]> (<[p2:=NodeB vp2 p p3]> M)) }}}.
  Proof.    
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".

    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures. 

    (*get value of p2*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeR vp2 p3) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (left_child %V #p2).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (right_child #p2).    
    iApply (right_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.     

    (* Get value of node *)
    wp_bind (value #p2).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.
    
    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp2 p p3) = Some (InjRV (#vp2, (#p, #p3)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'. rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p2:=NodeB vp2 p p3]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    rewrite lookup_insert_ne ; auto ; stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (left_child #p).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj. wp_store.
    wp_seq. wp_store.

    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeL (V p) p1) = Some (SOMEV (#(V p), (#p1, InjLV #()))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
    
    iApply "H" ; iFrame. iPureIntro.
    split ; auto.
    * pose proof (rotate_XE_if_bst p D W V F p2 RIGHT).
      auto.
    * pose proof (Mem_rotate_right_BR D V W M F p p1 p2 p3 (V p)).
      apply H13 ; auto.
  Qed.

  Lemma rotate_right_BN_st' `{!tctrHeapG Σ} (pp p p1 p2 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeN vp2) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
      {{{ RET #() ; pp ↦ #p2 ∗
          ⌜Inv p2 D ((add_edge (remove_edge F p p2) p2 p LEFT)) V W⌝ ∗
          ⌜Mem D ((add_edge (remove_edge F p p2) p2 p LEFT))V
           (<[p:=NodeL (V p) p1]> (<[p2:=NodeL vp2 p]> M))⌝ ∗
           mapsto_M (<[p:=NodeL (V p) p1]> (<[p2:=NodeL vp2 p]> M))}}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures. 

    (*get value of p2*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeN vp2) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (left_child %V #p2).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (right_child #p2).    
    iApply (right_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.     

    (* Get value of node *)
    wp_bind (value #p2).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeL vp2 p) = Some (InjRV (#vp2, (#p, NONEV)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p2:=NodeL vp2 p]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    rewrite lookup_insert_ne ; auto. intro ; subst. stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.
    
    (* Get value of left child *)
    wp_bind (left_child #p).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj. wp_store.
    wp_seq. wp_store.

    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeL (V p) p1) = Some (SOMEV (#(V p), (#p1, InjLV #()))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.

    iApply "H" ; iFrame. unfold ST.
    
    iSplit ; iPureIntro.
    * pose proof (rotate_XE_if_bst p D W V F p2 RIGHT H H2).
      apply H13 ; auto. 
    * rewrite <- H12.
      pose proof (Mem_rotate_right_BN D V W M F p p1 p2 (V p) (V p2)).
      apply H13  ; auto. rewrite H12. auto.
  Qed.

  Lemma rotate_right_RB_st' (pp p p2 p3 p4 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeB vp2 p3 p4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
      {{{ RET #() ; pp ↦ #p2 ∗
          ⌜Inv p2 D (update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT) V W⌝ ∗
          ⌜Mem D (update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT) V
           (<[p:=NodeR (V p) p3]> (<[p2:=NodeB vp2 p p4]> M))⌝ ∗
                       mapsto_M (<[p:=NodeR (V p) p3]> (<[p2:=NodeB vp2 p p4]> M)) }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures. 

    (*get value of p2*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeB vp2 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (left_child %V #p2).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (right_child #p2).    
    iApply (right_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value #p2).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp2 p p4) = Some (InjRV (#vp2, (#p, #p4)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc (<[p2:=NodeB vp2 p p4]> M) p (NodeR (V p) p2) with "M") as "M".
    assert (¬(p2 = p)). stlink_tac.
    rewrite lookup_insert_ne ; auto.
    
    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.
    
    (* Get value of left child *)
    wp_bind (left_child #p).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj. wp_store.
    wp_seq. wp_store.
    
    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeR (V p) p3) = Some (SOMEV (#(V p), (NONEV, #p3))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
     
    iApply "H" ; iFrame. unfold ST.
    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p2 p3 RIGHT H H3 H10).
      apply update_comm_inv in H13 ; auto. stlink_tac.
    * pose proof (Mem_rotate_right_RB D V W M F p p2 p3 p4 (V p) vp2).
      apply H13 ; auto.
  Qed.

  Lemma rotate_right_RL_st' (pp p p2 p3 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeL vp2 p3) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
      {{{ RET #() ; pp ↦ #p2 ∗
          ⌜Inv p2 D (update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT) V W⌝ ∗
          ⌜Mem D (update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT) V
           (<[p:=NodeR (V p) p3]> (<[p2:=NodeL vp2 p]> M))⌝ ∗
                       mapsto_M (<[p:=NodeR (V p) p3]> (<[p2:=NodeL vp2 p]> M)) }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures. 

    (*get value of p2*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeL vp2 p3) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (left_child %V #p2).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (right_child #p2).    
    iApply (right_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value #p2).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeL vp2 p) = Some (InjRV (#vp2, (#p, NONEV)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc (<[p2:=NodeL vp2 p]> M) p (NodeR (V p) p2) with "M") as "M".
    assert (¬(p2 = p)). stlink_tac.
    rewrite lookup_insert_ne ; auto.
    
    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.
    
    (* Get value of left child *)
    wp_bind (left_child #p).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj. wp_store.
    wp_seq. wp_store.
    
    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeR (V p) p3) = Some (SOMEV (#(V p), (NONEV, #p3))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
     
    iApply "H" ; iFrame.
    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p2 p3 RIGHT H H3 H10).
      apply update_comm_inv in H13 ; auto. stlink_tac.
    * pose proof (Mem_rotate_right_RL D V W M F p p2 p3 (V p) vp2).
      apply H13 ; auto.
  Qed.

  Lemma rotate_right_RR_st' (pp p p2 p3 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeR vp2 p3) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
      {{{ RET #() ; pp ↦ #p2 ∗
      ⌜Inv p2 D ((add_edge (remove_edge F p p2) p2 p LEFT)) V W⌝ ∗
        ⌜Mem D ((add_edge (remove_edge F p p2) p2 p LEFT)) V
            (<[p:=NodeN (V p)]> (<[p2:=NodeB vp2 p p3]> M))⌝ ∗
        mapsto_M (<[p:=NodeN (V p)]> (<[p2:=NodeB vp2 p p3]> M)) }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures. 

    (*get value of p2*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeR vp2 p3) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (left_child %V #p2).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (right_child #p2).    
    iApply (right_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value #p2).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp2 p p3) = Some (InjRV (#vp2, (#p, #p3)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc (<[p2:=NodeB vp2 p p3]> M) p (NodeR (V p) p2) with "M") as "M".
    assert (¬(p2 = p)). stlink_tac.
    rewrite lookup_insert_ne ; auto.
    
    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.
    
    (* Get value of left child *)
    wp_bind (left_child #p).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj. wp_store.
    wp_seq. wp_store.
    
    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeN (V p)) = Some (SOMEV (#(V p), (NONEV, NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
     
    iApply "H" ; iFrame.
    iSplit ; iPureIntro.
    * pose proof (rotate_XE_if_bst p D W V F p2 RIGHT H H3 H11).
      auto.
    * pose proof (Mem_rotate_right_RR D V W M F p p2 p3 (V p) vp2).
      apply H13 ; auto.
  Qed.

  Lemma rotate_right_RN_st' `{!tctrHeapG Σ} (pp p p2 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeN vp2) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
      {{{ RET #() ; pp ↦ #p2 ∗
          ⌜Inv p2 D ((add_edge (remove_edge F p p2) p2 p LEFT)) V W⌝ ∗
          ⌜Mem D ((add_edge (remove_edge F p p2) p2 p LEFT))V
           (<[p:=NodeN (V p)]> (<[p2:=NodeL vp2 p]> M))⌝ ∗
           mapsto_M (<[p:=NodeN (V p)]> (<[p2:=NodeL vp2 p]> M))}}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures. 

    (*get value of p2*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeN vp2) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (left_child %V #p2).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (right_child #p2).    
    iApply (right_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.     

    (* Get value of node *)
    wp_bind (value #p2).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeL vp2 p) = Some (InjRV (#vp2, (#p, NONEV)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p2:=NodeL vp2 p]> M) p (NodeR (V p) p2) with "M") as "M".
    rewrite lookup_insert_ne ; auto. intro ; subst. stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.
    
    (* Get value of left child *)
    wp_bind (left_child #p).
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj. wp_store.
    wp_seq. wp_store.

    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeN (V p)) = Some (SOMEV (#(V p), (NONEV, NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.

    iApply "H" ; iFrame. 
    
    iSplit ; iPureIntro.
    * pose proof (rotate_XE_if_bst p D W V F p2 RIGHT H H3 H11).
      apply H13 ; auto. 
    * rewrite <- H12.
      pose proof (Mem_rotate_right_RN D V W M F p p2 (V p) (V p2)).
      apply H13  ; auto. rewrite H12. auto.
  Qed.
  
End RotateRightRootSpecificationMemory.

Section RotateRightRootSpecificationWithTimeCredits.

  Context `{!tctrHeapG Σ} (nmax : nat).
  
  Variable v : val.
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable F : EdgeSet.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)

  Lemma rotate_right_RN_st_tc `{!tctrHeapG Σ} (pp p p2 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeN vp2) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_right #pp #p #p2 »
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros "#TC_inv" (Φ) "!# [R [% [% [M TC]]]] H".
    inversion H. unfold is_bst in Inv_bst.
    
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_tick. wp_rec. wp_pures. wp_tick. wp_tick.
    wp_pures. wp_tick. wp_pures. 
    wp_tick. wp_pures. wp_tick.

    (*get value of p2*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeN vp2) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p2).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« right_child »%V #p2).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto. 
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p2).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj.
    wp_tick_store. wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeL vp2 p) = Some (InjRV (#vp2, (#p, NONEV)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p2:=NodeL vp2 p]> M) p (NodeR (V p) p2) with "M") as "M".
    rewrite lookup_insert_ne ; auto. intro ; subst. stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.

    (* Get value of node *)
    wp_bind (« value »%V #p).    
    iPoseProof (TC_plus 17 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj. wp_tick_store.
    wp_tick_seq. wp_tick_store.

    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeN (V p)) = Some (SOMEV (#(V p), (NONEV,NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.

    iApply "H" ; iFrame. unfold ST.
     iExists
        ((add_edge (remove_edge F p p2) p2 p LEFT)),
     (<[p:=NodeN (V p)]> (<[p2:=NodeL vp2 p]> M)) ; iFrame.
     iSplit ; iPureIntro.
    * pose proof (rotate_XE_if_bst p D W V F p2 RIGHT H H3 H11).
      auto.
    * rewrite <- H12.
      pose proof (Mem_rotate_right_RN D V W M F p).      
      apply H13 ; auto. rewrite H12 ; auto.
  Qed.

  (*
                p
               / \
                 p2
                / \ 
                  p3
   *)
        
  Lemma rotate_right_RR_st_tc `{!tctrHeapG Σ} (pp p p2 p3 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeR vp2 p3) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_right #pp #p #p2 »
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros "#TC_inv" (Φ) "!# [R [% [% [M TC]]]] H".
    inversion H. unfold is_bst in Inv_bst.
    
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_tick. wp_rec. wp_pures. wp_tick. wp_tick.
    wp_pures. wp_tick. wp_pures. 
    wp_tick. wp_pures. wp_tick.

    (*get value of p2*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeR vp2 p3) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p2).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« right_child »%V #p2).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto. 
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p2).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj.
    wp_tick_store. wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp2 p p3) = Some (InjRV (#vp2, (#p, #p3)))).
    auto. apply H3.

    (*get value of p*)    
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p2:=NodeB vp2 p p3]> M) p (NodeR (V p) p2) with "M") as "M".
    rewrite lookup_insert_ne ; auto ; stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.

    (* Get value of node *)
    wp_bind (« value »%V #p).    
    iPoseProof (TC_plus 17 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj. wp_tick_store.
    wp_tick_seq. wp_tick_store.

    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeN (V p)) = Some (SOMEV (#(V p), (NONEV, NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.
    
    iApply "H" ; iFrame. unfold ST.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
    
    iExists
      ((add_edge (remove_edge F p p2) p2 p LEFT)),
    (<[p:=NodeN (V p)]> (<[p2:=NodeB vp2 p p3]> M)) ; iFrame.
    iSplit ; iPureIntro.
    * pose proof (rotate_XE_if_bst p D W V F p2 RIGHT H H1 H11).
      auto.
    * pose proof (Mem_rotate_right_RR D V W M F p p2 p3 (V p) vp2).
      apply H13 ; auto.
  Qed.
        
  (*
                p
               / \
                 p2
                / \ 
               p3  
   *)
  
  Lemma rotate_right_RL_st_tc `{!tctrHeapG Σ} (pp p p2 p3 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeL vp2 p3) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_right #pp #p #p2 »
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros "#TC_inv" (Φ) "!# [R [% [% [M TC]]]] H".
    inversion H. unfold is_bst in Inv_bst. 
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_tick. wp_rec. wp_pures. wp_tick. wp_tick.
    wp_pures. wp_tick. wp_pures. 
    wp_tick. wp_pures. wp_tick.

    (*get value of p2*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeL vp2 p3) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p2).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« right_child »%V #p2).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto. 
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p2).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj.
    wp_tick_store. wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeL vp2 p) = Some (InjRV (#vp2, (#p, NONEV)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p2:=NodeL vp2 p]> M) p (NodeR (V p) p2) with "M") as "M".
    rewrite lookup_insert_ne ; auto. intro ; subst. stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.

    (* Get value of node *)
    wp_bind (« value »%V #p).    
    iPoseProof (TC_plus 17 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj. wp_tick_store.
    wp_tick_seq. wp_tick_store.

    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeR (V p) p3) = Some (SOMEV (#(V p), (InjLV #(), #p3))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame. unfold ST.
    iExists
      ((update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT)),
    (<[p:=NodeR (V p) p3]> (<[p2:=NodeL vp2 p]> M)) ; iFrame.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.

    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p2 p3 RIGHT H H3 H10).
      apply update_comm_inv in H13 ; auto ; stlink_tac.
    * rewrite <- H12.
      pose proof ( Mem_rotate_right_RL D V W M F p p2 p3 (V p) (V p2)).      
      apply H13 ; auto. rewrite H12. auto.
  Qed.
    
  (*
                p
               / \
                 p2
                /  \
               p3  p4
   *)
  
  Lemma rotate_right_RB_st_tc `{!tctrHeapG Σ} (pp p p2 p3 p4 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeB vp2 p3 p4) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_right #pp #p #p2 »
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros "#TC_inv" (Φ) "!# [R [% [% [M TC]]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_tick. wp_rec. wp_pures. wp_tick. wp_tick.
    wp_pures. wp_tick. wp_pures. 
    wp_tick. wp_pures. wp_tick.

    (*get value of p2*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeB vp2 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p2).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« right_child »%V #p2).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto. 
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p2).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj.
    wp_tick_store. wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp2 p p4) = Some (InjRV (#vp2, (#p, #p4)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p2:=NodeB vp2 p p4]> M) p (NodeR (V p) p2) with "M") as "M".
    rewrite lookup_insert_ne ; auto. intro ; subst. stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.

    (* Get value of node *)
    wp_bind (« value »%V #p).    
    iPoseProof (TC_plus 17 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj. wp_tick_store.
    wp_tick_seq. wp_tick_store.

    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeR (V p) p3) = Some (SOMEV (#(V p), (InjLV #(), #p3))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
    
    iApply "H" ; iFrame. 
    iExists
      ((update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT)),
    (<[p:=NodeR (V p) p3]> (<[p2:=NodeB vp2 p p4]> M)) ; iFrame.

    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p2 p3 RIGHT H H3 H10).
      apply update_comm_inv in H13 ; auto ; stlink_tac.
    * pose proof ( Mem_rotate_right_RB D V W M F p p2 p3 p4 (V p) vp2).      
      apply H13 ; auto. 
  Qed.
  
  (*

                p
               / \
             p1  p2
                 
   *)  
                      
  Lemma rotate_right_BN_st_tc `{!tctrHeapG Σ} (pp p p1 p2 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeN vp2) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_right #pp #p #p2 »
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros "#TC_inv" (Φ) "!# [R [% [% [M TC]]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].

    wp_tick. wp_rec. wp_pures. wp_tick. wp_tick.
    wp_pures. wp_tick. wp_pures. 
    wp_tick. wp_pures. wp_tick.

    (*get value of p2*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeN vp2) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p2).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« right_child »%V #p2).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto. 
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p2).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj.
    wp_tick_store. wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeL vp2 p) = Some (InjRV (#vp2, (#p, NONEV)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p2:=NodeL vp2 p]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    rewrite lookup_insert_ne ; auto. intro ; subst. stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.

    (* Get value of node *)
    wp_bind (« value »%V #p).    
    iPoseProof (TC_plus 17 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj. wp_tick_store.
    wp_tick_seq. wp_tick_store.

    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeL (V p) p1) = Some (SOMEV (#(V p), (#p1, InjLV #()))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame. unfold ST.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
    
    iExists
      ((add_edge (remove_edge F p p2) p2 p LEFT)),
    (<[p:=NodeL (V p) p1]> (<[p2:=NodeL vp2 p]> M)) ; iFrame.

    iSplit ; iPureIntro.
    * pose proof (rotate_XE_if_bst p D W V F p2 RIGHT H H7 H11). auto.
    * pose proof (Mem_rotate_right_BN D V W M F p p1 p2).
      apply H13 ; auto.
  Qed.

  (*

                p
               / \
             p1  p2
                  \
                  p3
                 
   *)
  
  Lemma rotate_right_BR_st_tc `{!tctrHeapG Σ} (pp p p1 p2 p3 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeR vp2 p3) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_right #pp #p #p2 »
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros "#TC_inv" (Φ) "!# [R [% [% [M TC]]]] H".
    inversion H. unfold is_bst in Inv_bst.
    
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_tick. wp_rec. wp_pures. wp_tick. wp_tick.
    wp_pures. wp_tick. wp_pures. 
    wp_tick. wp_pures. wp_tick.

    (*get value of p2*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeR vp2 p3) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p2).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« right_child »%V #p2).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto. 
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p2).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj.
    wp_tick_store. wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp2 p p3) = Some (InjRV (#vp2, (#p, #p3)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. 
    iPoseProof (mapsto_M_acc (<[p2:=NodeB vp2 p p3]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    rewrite lookup_insert_ne ; auto ; stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H3 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.

    (* Get value of node *)
    wp_bind (« value »%V #p).    
    iPoseProof (TC_plus 17 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj. wp_tick_store.
    wp_tick_seq. wp_tick_store.

    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeL (V p) p1) = Some (SOMEV (#(V p), (#p1, InjLV #()))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. unpack.
    
    iApply "H" ; iFrame. 
    iExists
      ((add_edge (remove_edge F p p2) p2 p LEFT)),
    (<[p:=NodeL (V p) p1]> (<[p2:=NodeB vp2 p p3]> M)) ; iFrame.

    unpack.
    iSplit ; iPureIntro.
    * pose proof (rotate_XE_if_bst p D W V F p2 RIGHT H ).
      auto.
    * pose proof (Mem_rotate_right_BR D V W M F p p1 p2 p3 (V p)).
      apply H13 ; auto.
  Qed.

  (*

                p
               / \
             p1  p2
                 /
                p3

   *)
  
  Lemma rotate_right_BL_st_tc `{!tctrHeapG Σ} (pp p p1 p2 p3 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeL vp2 p3) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_right #pp #p #p2 »
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros "#TC_inv" (Φ) "!# [R [% [% [M TC]]]] H".
    inversion H. unfold is_bst in Inv_bst. 
    
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_tick. wp_rec. wp_pures. wp_tick. wp_tick.
    wp_pures. wp_tick. wp_pures. 
    wp_tick. wp_pures. wp_tick.

    (*get value of p2*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeL vp2 p3) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p2).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« right_child »%V #p2).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto. 
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p2).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj.
    wp_tick_store. wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeL vp2 p) = Some (InjRV (#vp2, (#p, InjLV #())))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p2:=NodeL vp2 p]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    pose proof (different_pointers_if_bst p D V W F p p2 RIGHT H H7).
    rewrite lookup_insert_ne ; auto.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.

    (* Get value of node *)
    wp_bind (« value »%V #p).    
    iPoseProof (TC_plus 17 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj. wp_tick_store.
    wp_tick_seq. wp_tick_store.

    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeB (V p) p1 p3) = Some (SOMEV (#(V p), (#p1, #p3))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
    
    iApply "H" ; iFrame. unfold ST.
    iExists
      ((update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT)),
    (<[p:=NodeB (V p) p1 p3]> (<[p2:=NodeL vp2 p]> M)) ; iFrame.

    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p2 p3 RIGHT).
      apply update_comm_inv in H13 ; auto ; stlink_tac.
    * pose proof (Mem_rotate_right_BL D V W M F p p1 p2 p3 (V p)).
      apply H13 ; auto.    
  Qed.  
  

  (*

                p
               / \
             p1  p2
                 /\
               p3 p4

   *)
  
  Lemma rotate_right_BB_st_tc `{!tctrHeapG Σ} (pp p p1 p2 p3 p4 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeB vp2 p3 p4) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_right #pp #p #p2 »
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros "#TC_inv" (Φ) "!# [R [% [% [M TC]]]] H".
    inversion H. unfold is_bst in Inv_bst.
    
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_tick. wp_rec. wp_pures. wp_tick. wp_tick.
    wp_pures. wp_tick. wp_pures. 
    wp_tick. wp_pures. wp_tick.

    (*get value of p2*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc M p2 (NodeB vp2 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p2).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« right_child »%V #p2).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p2).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".
    
    wp_tick_pair. wp_tick_inj. wp_tick_store.
    wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp2 p p4) = Some (InjRV (#vp2, (#p, #p4)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p2:=NodeB vp2 p p4]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    rewrite lookup_insert_ne ; auto ; stlink_tac.
    
    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (« left_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.

    (* Get value of node *)
    wp_bind (« value »%V #p).    
    iPoseProof (TC_plus 17 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj. wp_tick_store.
    wp_tick_seq. wp_tick_store.

    (*save in memory*)
    iAssert
    (bi_pure (val_of_content (NodeB (V p) p1 p3) = Some (SOMEV (#(V p), (#p1, #p3))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p2 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
    
    iApply "H" ; iFrame. unfold ST.
    iExists
      ((update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT)),
    (<[p:=NodeB (V p) p1 p3]> (<[p2:=NodeB vp2 p p4]> M)) ; iFrame.

    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p2 p3 RIGHT).
      apply update_comm_inv in H13 ; auto ; stlink_tac.
    * pose proof (Mem_rotate_right_BB D V W M F p p1 p2 p3 p4 (V p) (V p2)).
      rewrite H12 in H13.
      apply H13 ; auto.
  Qed.

End RotateRightRootSpecificationWithTimeCredits.

Section RotateRightRootSpecification.

  Context `{!tctrHeapG Σ} (nmax : nat).
  
  Variable v : val.
  Variable D : LibSet.set elem.   (* domain *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable F : EdgeSet.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)

  Lemma rotate_right_RN_st (pp p p2 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeN vp2) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_right_RN_st' D V W F M pp p p2 vp vp2 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% [% M]]]". iApply "H". iFrame.
    unfold ST.
    iExists (add_edge (remove_edge F p p2) p2 p LEFT) ,
    (<[p:=NodeN (V p)]> (<[p2:=NodeL vp2 p]> M)).
    iSplit ; auto.
  Qed.

  (*
                p
               / \
                 p2
                / \ 
                  p3
   *)
        
  Lemma rotate_right_RR_st (pp p p2 p3 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeR vp2 p3) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_right_RR_st' D V W F M pp p p2 p3 vp vp2 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% M]]". iApply "H". iFrame.
    unfold ST.
    iExists (add_edge (remove_edge F p p2) p2 p LEFT) ,
    (<[p:=NodeN (V p)]> (<[p2:=NodeB vp2 p p3]> M)). iFrame.
    auto.
  Qed.
        
  (*
                p
               / \
                 p2
                / \ 
               p3  
   *)
  
  Lemma rotate_right_RL_st `{!tctrHeapG Σ} (pp p p2 p3 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeL vp2 p3) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_right_RL_st' D V W F M pp p p2 p3 vp vp2 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% M]]". iApply "H". iFrame.
    unfold ST.
    iExists (update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT) ,
    (<[p:=NodeR (V p) p3]> (<[p2:=NodeL vp2 p]> M)). iFrame.
    auto.
  Qed.
    
  (*
                p
               / \
                 p2
                /  \
               p3  p4
   *)
  
  Lemma rotate_right_RB_st (pp p p2 p3 p4 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeB vp2 p3 p4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_right_RB_st' D V W F M pp p p2 p3 p4 vp vp2 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% M]]". iApply "H". iFrame.
    unfold ST.
    iExists (update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT),
    (<[p:=NodeR (V p) p3]> (<[p2:=NodeB vp2 p p4]> M)). iFrame.
    auto.
  Qed.
  
  (*

                p
               / \
             p1  p2
                 
   *)  
                      
  Lemma rotate_right_BN_st `{!tctrHeapG Σ} (pp p p1 p2 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeN vp2) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_right_BN_st' D V W F M pp p p1 p2 vp vp2 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% M]]". iApply "H". iFrame.
    unfold ST.
    iExists (add_edge (remove_edge F p p2) p2 p LEFT),
    (<[p:=NodeL (V p) p1]> (<[p2:=NodeL vp2 p]> M)). iFrame.
    auto.
  Qed.

  (*

                p
               / \
             p1  p2
                  \
                  p3
                 
   *)
  
  Lemma rotate_right_BR_st (pp p p1 p2 p3 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeR vp2 p3) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_right_BR_st' D V W F M pp p p1 p2 p3 vp vp2 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% M]]". iApply "H". iFrame.
    unfold ST.
    iExists (add_edge (remove_edge F p p2) p2 p LEFT),
    (<[p:=NodeL (V p) p1]> (<[p2:=NodeB vp2 p p3]> M)). iFrame.
    auto.
  Qed.

  (*

                p
               / \
             p1  p2
                 /
                p3

   *)
  
  Lemma rotate_right_BL_st (pp p p1 p2 p3 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeL vp2 p3) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_right_BL_st' D V W F M pp p p1 p2 p3 vp vp2 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% [% M]]]". iApply "H". iFrame.
    unfold ST.
    iExists (update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT),
    (<[p:=NodeB (V p) p1 p3]> (<[p2:=NodeL vp2 p]> M)). iFrame. auto.
  Qed.  
  

  (*

                p
               / \
             p1  p2
                 /\
               p3 p4

   *)
  
  Lemma rotate_right_BB_st (pp p p1 p2 p3 p4 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeB vp2 p3 p4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_right #pp #p #p2
    {{{ RET #() ; pp ↦ #p2 ∗ ST p2 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_right_BB_st' D V W F M pp p p1 p2 p3 p4 vp vp2 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% [% M]]]". iApply "H". iFrame.
    unfold ST.
    iExists (update_edge (update_edge F p2 p3 p LEFT) p p2 p3 RIGHT),
    (<[p:=NodeB (V p) p1 p3]> (<[p2:=NodeB vp2 p p4]> M)). iFrame.
    auto.
  Qed.
  
End RotateRightRootSpecification.
