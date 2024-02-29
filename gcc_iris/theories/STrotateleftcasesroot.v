From ST Require Import Code
     STorientation STpredicate STpath STedgeset
     STedgesetrotateroot STlink STmemory STproof STdomain.
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

                rotate_left_BB_st
                rotate_left_BR_st
                rotate_left_BL_st
                rotate_left_BN_st
                rotate_left_RB_st
                rotate_left_RL_st
                rotate_left_RR_st
                rotate_left_RN_st

                       p
                      / \
                        p1

        Other theorems not needed:
              rotate_right_LX_st doesn't work
              rotate_right_N_st doesn't work

 *)

Section RotateLeftRootSpecificationMemory.

  
  Context `{!tctrHeapG Σ} (nmax : nat).
  
  Variable v : val.
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable F : EdgeSet.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)
  
  Lemma rotate_left_BB_st' (pp p p1 p2 p3 p4 : loc) (vp vp1 : Z) :
    let F'' :=  (update_edge (update_edge F p1 p4 p RIGHT) p p1 p4 LEFT) in
    let M' := (<[p:=NodeB (V p) p4 p2]> (<[p1:=NodeB vp1 p3 p]> M)) in 
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeB vp1 p3 p4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures. 

    (*get value of p2*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc M p1 (NodeB vp1 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (right_child %V #p1).
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (left_child #p1).    
    iApply (left_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value #p1).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp1 p3 p) = Some (InjRV (#vp1, (#p3, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeB vp1 p3 p]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    assert (¬(p1 = p)). stlink_tac.
    rewrite lookup_insert_ne ; auto.
    
    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.
    
    (* Get value of left child *)
    wp_bind (right_child #p).
    iApply (right_child_specification with "[Hp]") ; auto.
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
    (bi_pure (val_of_content (NodeB (V p) p4 p2) = Some (SOMEV (#(V p), (#p4, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
     
    iApply "H" ; iFrame. 
    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p1 p4 LEFT H).
      apply update_comm_inv in H13 ; auto ; stlink_tac. 
    * pose proof (Mem_rotate_left_BB D V W M F p p1 p2 p3 p4 (V p) vp1).
      apply H13 ; auto.
  Qed.

  Lemma rotate_left_BL_st' (pp p p1 p2 p3 : loc) (vp vp1 : Z) :
    let F'' :=  (add_edge (remove_edge F p p1) p1 p RIGHT) in
    let M' := (<[p:=NodeR (V p) p2]> (<[p1:=NodeB vp1 p3 p]> M)) in 
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeL vp1 p3) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures.
    
    (*get value of p2*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc M p1 (NodeL vp1 p3) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (right_child %V #p1).
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (left_child #p1).    
    iApply (left_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value #p1).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp1 p3 p) = Some (InjRV (#vp1, (#p3, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeB vp1 p3 p]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    assert (¬(p1 = p)). stlink_tac.
    rewrite lookup_insert_ne ; auto.
    
    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.
    
    (* Get value of left child *)
    wp_bind (right_child #p).
    iApply (right_child_specification with "[Hp]") ; auto.
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
    (bi_pure (val_of_content (NodeR (V p) p2) = Some (SOMEV (#(V p), (NONEV, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
    
    iApply "H" ; iFrame. 
    iSplit ; iPureIntro.
    * pose proof (rotate_XE_if_bst p D W V F p1 LEFT).
      simpl in H13. auto.
    * pose proof (Mem_rotate_left_BL D V W M F p p1 p2 p3 (V p) vp1).
      apply H13 ; auto.
  Qed.
      
  Lemma rotate_left_BR_st' (pp p p1 p2 p4 : loc) (vp vp1 : Z) :
    let F'' :=  (update_edge (update_edge F p1 p4 p RIGHT) p p1 p4 LEFT) in
    let M' := (<[p:=NodeB (V p) p4 p2]> (<[p1:=NodeR vp1 p]> M)) in 
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeR vp1 p4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures.
    
    (*get value of p2*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc M p1 (NodeR vp1 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (right_child %V #p1).
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (left_child #p1).    
    iApply (left_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value #p1).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeR vp1 p) = Some (InjRV (#vp1, (NONEV, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeR vp1 p]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    assert (¬(p1 = p)). stlink_tac.
    rewrite lookup_insert_ne ; auto.
    
    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.
    
    (* Get value of left child *)
    wp_bind (right_child #p).
    iApply (right_child_specification with "[Hp]") ; auto.
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
    (bi_pure (val_of_content (NodeB (V p) p4 p2) = Some (SOMEV (#(V p), (#p4, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
    
    iApply "H" ; iFrame. 
    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p1 p4 LEFT).
      simpl in H13. apply update_comm_inv in H13 ; auto ; stlink_tac.  
    * pose proof (Mem_rotate_left_BR D V W M F p p1 p2 p4 (V p) vp1).
      apply H13 ; auto.
  Qed.

  Lemma rotate_left_BN_st' `{!tctrHeapG Σ} (pp p p1 p2 : loc) (vp vp1 : Z) :
    let F'' :=  (add_edge (remove_edge F p p1) p1 p RIGHT) in
    let M' := (<[p:=NodeR (V p) p2]> (<[p1:=NodeR vp1 p]> M)) in 
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeN vp1) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures.
    
    (*get value of p2*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc M p1 (NodeN vp1) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (right_child %V #p1).
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (left_child #p1).    
    iApply (left_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value #p1).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeR vp1 p) = Some (InjRV (#vp1, (NONEV, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeR vp1 p]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    assert (¬(p1 = p)). stlink_tac.
    rewrite lookup_insert_ne ; auto.
    
    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.
    
    (* Get value of left child *)
    wp_bind (right_child #p).
    iApply (right_child_specification with "[Hp]") ; auto.
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
      (bi_pure (val_of_content (NodeR (V p) p2) = Some (SOMEV (#(V p), (NONEV, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
    
    iApply "H" ; iFrame. 
    iSplit ; iPureIntro.
    * pose proof (rotate_XE_if_bst p D W V F p1 LEFT).
      simpl in H13. auto.
    * pose proof (Mem_rotate_left_BN D V W M F p p1 p2 (V p) vp1).
      apply H13 ; auto.
  Qed.

  Lemma rotate_left_LB_st' (pp p p1 p3 p4 : loc) (vp vp1 : Z) :
    let F'' :=  (update_edge (update_edge F p1 p4 p RIGHT) p p1 p4 LEFT) in
    let M' := (<[p:=NodeL (V p) p4]> (<[p1:=NodeB vp1 p3 p]> M)) in 
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeB vp1 p3 p4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures. 

    (*get value of p2*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc M p1 (NodeB vp1 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (right_child %V #p1).
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (left_child #p1).    
    iApply (left_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value #p1).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp1 p3 p) = Some (InjRV (#vp1, (#p3, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeB vp1 p3 p]> M) p (NodeL (V p) p1) with "M") as "M".
    assert (¬(p1 = p)). stlink_tac.
    rewrite lookup_insert_ne ; auto.
    
    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.
    
    (* Get value of left child *)
    wp_bind (right_child #p).
    iApply (right_child_specification with "[Hp]") ; auto.
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
    (bi_pure (val_of_content (NodeL (V p) p4) = Some (SOMEV (#(V p), (#p4, NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
     
    iApply "H" ; iFrame. 
    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p1 p4 LEFT H).
      apply update_comm_inv in H13 ; auto ; stlink_tac. 
    * pose proof (Mem_rotate_left_LB D V W M F p p1 p3 p4 (V p)).
      apply H13 ; auto.
  Qed.

  Lemma rotate_left_LL_st' (pp p p1 p3 : loc) (vp vp1 : Z) :
    let F'' :=  (add_edge (remove_edge F p p1) p1 p RIGHT) in
    let M' := (<[p:=NodeN (V p)]> (<[p1:=NodeB vp1 p3 p]> M)) in 
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeL vp1 p3) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures.
    
    (*get value of p2*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc M p1 (NodeL vp1 p3) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (right_child %V #p1).
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (left_child #p1).    
    iApply (left_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value #p1).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp1 p3 p) = Some (InjRV (#vp1, (#p3, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeB vp1 p3 p]> M) p (NodeL (V p) p1) with "M") as "M".
    assert (¬(p1 = p)). stlink_tac.
    rewrite lookup_insert_ne ; auto.
    
    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.
    
    (* Get value of left child *)
    wp_bind (right_child #p).
    iApply (right_child_specification with "[Hp]") ; auto.
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

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
    
    iApply "H" ; iFrame. 
    iSplit ; iPureIntro.
    * pose proof (rotate_XE_if_bst p D W V F p1 LEFT).
      simpl in H13. auto.
    * pose proof (Mem_rotate_left_LL D V W M F p p1 p3 (V p)).
      apply H13 ; auto.
  Qed.
      
  Lemma rotate_left_LR_st' (pp p p1 p4 : loc) (vp vp1 : Z) :
    let F'' :=  (update_edge (update_edge F p1 p4 p RIGHT) p p1 p4 LEFT) in
    let M' := (<[p:=NodeL (V p) p4]> (<[p1:=NodeR vp1 p]> M)) in 
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeR vp1 p4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures.
    
    (*get value of p2*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc M p1 (NodeR vp1 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (right_child %V #p1).
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (left_child #p1).    
    iApply (left_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value #p1).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeR vp1 p) = Some (InjRV (#vp1, (NONEV, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeR vp1 p]> M) p (NodeL (V p) p1) with "M") as "M".
    assert (¬(p1 = p)). stlink_tac.
    rewrite lookup_insert_ne ; auto.
    
    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.
    
    (* Get value of left child *)
    wp_bind (right_child #p).
    iApply (right_child_specification with "[Hp]") ; auto.
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
    (bi_pure (val_of_content (NodeL (V p) p4) = Some (SOMEV (#(V p), (#p4, NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
    
    iApply "H" ; iFrame. 
    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p1 p4 LEFT).
      simpl in H13. apply update_comm_inv in H13 ; auto ; stlink_tac.  
    * pose proof (Mem_rotate_left_LR D V W M F p p1 p4 (V p) vp1).
      apply H13 ; auto. 
  Qed.

  Lemma rotate_left_LN_st' `{!tctrHeapG Σ} (pp p p1 : loc) (vp vp1 : Z) :
    let F'' :=  (add_edge (remove_edge F p p1) p1 p RIGHT) in
    let M' := (<[p:=NodeN (V p)]> (<[p1:=NodeR vp1 p]> M)) in 
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeN vp1) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    wp_rec. wp_pures. 
    wp_pures. wp_pures. 
    wp_pures.
    
    (*get value of p2*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc M p1 (NodeN vp1) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (right_child %V #p1).
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_let.
    
    (* Get value of right child *)
    wp_bind (left_child #p1).    
    iApply (left_child_specification with "[Hp]") ; auto. 
    iModIntro. iIntros "Hp".

    wp_pair.

    (* Get value of node *)
    wp_bind (value #p1).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair. wp_inj.
    wp_store. wp_seq.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeR vp1 p) = Some (InjRV (#vp1, (NONEV, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as H2'. rewrite E1 in H2'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeR vp1 p]> M) p (NodeL (V p) p1) with "M") as "M".
    assert (¬(p1 = p)). stlink_tac.
    rewrite lookup_insert_ne ; auto.
    
    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.
    
    (* Get value of left child *)
    wp_bind (right_child #p).
    iApply (right_child_specification with "[Hp]") ; auto.
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

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.
    
    iApply "H" ; iFrame. 
    iSplit ; iPureIntro.
    * pose proof (rotate_XE_if_bst p D W V F p1 LEFT).
      simpl in H13. auto.
    * pose proof (Mem_rotate_left_LN D V W M F p p1 (V p)).
      apply H13 ; auto.
  Qed.
  
End RotateLeftRootSpecificationMemory.


Section RotateLeftRootSpecificationWithTimeCredits.
  

  Context `{!tctrHeapG Σ} (nmax : nat).
  
  Variable v : val.
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable F : EdgeSet.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)

  Lemma rotate_left_LN_st_tc `{!tctrHeapG Σ} (pp p p1 : loc) (vp vp1 : Z) :
    let F'' :=  (add_edge (remove_edge F p p1) p1 p RIGHT) in
    let M' := (<[p:=NodeN (V p)]> (<[p1:=NodeR vp1 p]> M)) in 
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeN vp1) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗ ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_left #pp #p #p1»
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
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
    iPoseProof (mapsto_M_acc M p1 (NodeN vp1) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p1).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« left_child »%V #p1).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto. 
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p1).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj.
    wp_tick_store. wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeR vp1 p) = Some (InjRV (#vp1, (NONEV, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeR vp1 p]> M) p (NodeL (V p) p1) with "M") as "M".
    rewrite lookup_insert_ne ; auto. intro ; subst. stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
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

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.

    iApply "H" ; iFrame. iSplit ; iPureIntro.
    * pose proof (rotate_XE_if_bst p D W V F p1 LEFT).
      auto.
    * pose proof (Mem_rotate_left_LN D V W M F p p1 (V p)).
      apply H13 ; auto.
  Qed.

  (*
                p
               / \
                 p2
                / \ 
                  p3
   *)
        
  Lemma rotate_left_LR_st_tc `{!tctrHeapG Σ} (pp p p1 p4 : loc) (vp vp1 : Z) :
    let F'' :=  (update_edge (update_edge F p1 p4 p RIGHT) p p1 p4 LEFT) in
    let M' := (<[p:=NodeL (V p) p4]> (<[p1:=NodeR vp1 p]> M)) in 
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeR vp1 p4) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_left #pp #p #p1»
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
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
    iPoseProof (mapsto_M_acc M p1 (NodeR vp1 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p1).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« left_child »%V #p1).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto. 
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p1).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj.
    wp_tick_store. wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeR vp1 p) = Some (InjRV (#vp1, (NONEV, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeR vp1 p]> M) p (NodeL (V p) p1) with "M") as "M".
    rewrite lookup_insert_ne ; auto. intro ; subst. stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
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
    (bi_pure (val_of_content (NodeL (V p) p4) = Some (SOMEV (#(V p), (#p4,NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p1 p4 LEFT).
      simpl in H13. apply update_comm_inv in H13 ; auto ; stlink_tac.  
    * pose proof (Mem_rotate_left_LR D V W M F p p1 p4 (V p) vp1).
      apply H13 ; auto. 
  Qed.
        
  (*
                p
               / \
                 p2
                / \ 
               p3  
   *)
  
  Lemma rotate_left_LL_st_tc `{!tctrHeapG Σ} (pp p p1 p3 : loc) (vp vp1 : Z) :
    let F'' :=  (add_edge (remove_edge F p p1) p1 p RIGHT) in
    let M' := (<[p:=NodeN (V p)]> (<[p1:=NodeB vp1 p3 p]> M)) in 
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeL vp1 p3) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_left #pp #p #p1»
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
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
    iPoseProof (mapsto_M_acc M p1 (NodeL vp1 p3) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p1).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« left_child »%V #p1).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto. 
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p1).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj.
    wp_tick_store. wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp1 p3 p) = Some (InjRV (#vp1, (#p3, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeB vp1 p3 p]> M) p (NodeL (V p) p1) with "M") as "M".
    rewrite lookup_insert_ne ; auto. intro ; subst. stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
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

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro.
    * pose proof (rotate_XE_if_bst p D W V F p1 LEFT).
      simpl in H13. auto.
    * pose proof (Mem_rotate_left_LL D V W M F p p1 p3 (V p)).
      apply H13 ; auto.
  Qed.
    
  (*
                p
               / \
                 p2
                /  \
               p3  p4
   *)
  
  Lemma rotate_left_LB_st_tc `{!tctrHeapG Σ} (pp p p1 p3 p4 : loc) (vp vp1 : Z) :
    let F'' :=  (update_edge (update_edge F p1 p4 p RIGHT) p p1 p4 LEFT) in
    let M' := (<[p:=NodeL (V p) p4]> (<[p1:=NodeB vp1 p3 p]> M)) in 
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeB vp1 p3 p4) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_left #pp #p #p1»
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
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
    iPoseProof (mapsto_M_acc M p1 (NodeB vp1 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p1).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« left_child »%V #p1).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto. 
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p1).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj.
    wp_tick_store. wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp1 p3 p) = Some (InjRV (#vp1, (#p3, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeB vp1 p3 p]> M) p (NodeL (V p) p1) with "M") as "M".
    rewrite lookup_insert_ne ; auto. intro ; subst. stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
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
    (bi_pure (val_of_content (NodeL (V p) p4) = Some (SOMEV (#(V p), (#p4,NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p1 p4 LEFT H).
      apply update_comm_inv in H13 ; auto ; stlink_tac. 
    * pose proof (Mem_rotate_left_LB D V W M F p p1 p3 p4 (V p)).
      apply H13 ; auto.
  Qed.
  
  (*

                p
               / \
             p1  p2
                 
   *)  
                      
  Lemma rotate_left_BN_st_tc `{!tctrHeapG Σ} (pp p p1 p2 : loc) (vp vp1 : Z) :
    let F'' :=  (add_edge (remove_edge F p p1) p1 p RIGHT) in
    let M' := (<[p:=NodeR (V p) p2]> (<[p1:=NodeR vp1 p]> M)) in 
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeN vp1) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_left #pp #p #p1»
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
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
    iPoseProof (mapsto_M_acc M p1 (NodeN vp1) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p1).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« left_child »%V #p1).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto. 
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p1).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj.
    wp_tick_store. wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeR vp1 p) = Some (InjRV (#vp1, (NONEV, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeR vp1 p]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    rewrite lookup_insert_ne ; auto. intro ; subst. stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
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
    (bi_pure (val_of_content (NodeR (V p) p2) = Some (SOMEV (#(V p), (NONEV, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro.
    * pose proof (rotate_XE_if_bst p D W V F p1 LEFT).
      simpl in H13. auto.
    * pose proof (Mem_rotate_left_BN D V W M F p p1 p2 (V p) vp1).
      apply H13 ; auto.
  Qed.

  (*

                p
               / \
             p1  p2
                  \
                  p3
                 
   *)
  
  Lemma rotate_left_BR_st_tc `{!tctrHeapG Σ} (pp p p1 p2 p4 : loc) (vp vp1 : Z) :
    let F'' :=  (update_edge (update_edge F p1 p4 p RIGHT) p p1 p4 LEFT) in
    let M' := (<[p:=NodeB (V p) p4 p2]> (<[p1:=NodeR vp1 p]> M)) in 
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeR vp1 p4) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_left #pp #p #p1»
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
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
    iPoseProof (mapsto_M_acc M p1 (NodeR vp1 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p1).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« left_child »%V #p1).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto. 
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p1).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj.
    wp_tick_store. wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeR vp1 p) = Some (InjRV (#vp1, (NONEV, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeR vp1 p]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    rewrite lookup_insert_ne ; auto. intro ; subst. stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
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
    (bi_pure (val_of_content (NodeB (V p) p4 p2) = Some (SOMEV (#(V p), (#p4, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p1 p4 LEFT).
      simpl in H13. apply update_comm_inv in H13 ; auto ; stlink_tac.  
    * pose proof (Mem_rotate_left_BR D V W M F p p1 p2 p4 (V p) vp1).
      apply H13 ; auto.
  Qed.

  (*

                p
               / \
             p1  p2
                 /
                p3

   *)
  
  Lemma rotate_left_BL_st_tc `{!tctrHeapG Σ} (pp p p1 p2 p3 : loc) (vp vp1 : Z) :
    let F'' :=  (add_edge (remove_edge F p p1) p1 p RIGHT) in
    let M' := (<[p:=NodeR (V p) p2]> (<[p1:=NodeB vp1 p3 p]> M)) in 
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeL vp1 p3) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_left #pp #p #p1»
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
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
    iPoseProof (mapsto_M_acc M p1 (NodeL vp1 p3) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p1).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« left_child »%V #p1).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto. 
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p1).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj.
    wp_tick_store. wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp1 p3 p) = Some (InjRV (#vp1, (#p3, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeB vp1 p3 p]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    rewrite lookup_insert_ne ; auto. intro ; subst. stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
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
    (bi_pure (val_of_content (NodeR (V p) p2) = Some (SOMEV (#(V p), (NONEV, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro.
    * pose proof (rotate_XE_if_bst p D W V F p1 LEFT).
      simpl in H13. auto.
    * pose proof (Mem_rotate_left_BL D V W M F p p1 p2 p3 (V p) vp1).
      apply H13 ; auto.
  Qed.  
  

  (*

                p
               / \
             p1  p2
                 /\
               p3 p4

   *)
  
  Lemma rotate_right_BB_st_tc `{!tctrHeapG Σ} (pp p p1 p2 p3 p4 : loc) (vp vp1 : Z) :
    let F'' :=  (update_edge (update_edge F p1 p4 p RIGHT) p p1 p4 LEFT) in
    let M' := (<[p:=NodeB (V p) p4 p2]> (<[p1:=NodeB vp1 p3 p]> M)) in 
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeB vp1 p3 p4) ->
    TCTR_invariant nmax -∗
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M ∗ TC (64) }}}
      «rotate_left #pp #p #p1»
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
  Proof.
    intros F'' M' E1 E2.
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
    iPoseProof (mapsto_M_acc M p1 (NodeB vp1 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
    simpl in H6. inversion H6 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p1).
    iPoseProof (TC_plus 52 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_let. wp_tick.
    
    (* Get value of right child *)
    wp_bind (« left_child »%V #p1).    
    iPoseProof (TC_plus 43 6) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (left_child_specification_tc with "[TC_inv] [P]") ; auto. 
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick.    

    (* Get value of node *)
    wp_bind (« value »%V #p1).    
    iPoseProof (TC_plus 36 5) as "TCSum". 
    iDestruct ("TCSum" with "TC") as "[TC TC5]".
    iCombine "Hp" "TC5" as "P".    
    iApply (value_specification_tc with "[TC_inv] [P]") ; auto.
    iClear "TCSum". iModIntro. iIntros "Hp".

    wp_tick_pair. wp_tick_inj.
    wp_tick_store. wp_tick_seq. wp_tick.

    (*save in memory*)
    iDestruct ("M" with "[] [Hp]") as "M" ; auto.
    iPureIntro. assert (val_of_content (NodeB vp1 p3 p) = Some (InjRV (#vp1, (#p3, #p)))).
    auto. apply H3.

    (*get value of p*)
    apply H0 in rootisindomain as rootisindomain'.
    rewrite E1 in rootisindomain'. unpack.
    iPoseProof (mapsto_M_acc (<[p1:=NodeB vp1 p3 p]> M) p (NodeB (V p) p1 p2) with "M") as "M".
    rewrite lookup_insert_ne ; auto. intro ; subst. stlink_tac.

    iDestruct "M" as (v') "[% [Hp M]]".
    inversion H9 ; subst.

    (* Get value of left child *)
    wp_bind (« right_child »%V #p).
    iPoseProof (TC_plus 24 6) as "TCSum".
    iDestruct ("TCSum" with "TC") as "[TC TC6]".
    iCombine "Hp" "TC6" as "P".    
    iApply (right_child_specification_tc with "[TC_inv] [P]") ; auto.
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
    (bi_pure (val_of_content (NodeB (V p) p4 p2) = Some (SOMEV (#(V p), (#p4, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    assert (p1 \in D). stdomain_tac.
    apply H0 in H10. rewrite E2 in H10. unpack.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro.
    * pose proof (rotate_XI_if_bst p D W V F p1 p4 LEFT H).
      apply update_comm_inv in H13 ; auto ; stlink_tac. 
    * pose proof (Mem_rotate_left_BB D V W M F p p1 p2 p3 p4 (V p) vp1).
      apply H13 ; auto.
  Qed.

End RotateLeftRootSpecificationWithTimeCredits.

Section RotateLeftRootSpecification.

  Context `{!tctrHeapG Σ} (nmax : nat).
  
  Variable v : val.
  Variable D : LibSet.set elem.   (* domain *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable F : EdgeSet.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)

  Lemma rotate_left_LN_st (pp p p1 p2 : loc) (vp vp1 : Z) :
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeN vp1) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ST p1 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_left_LN_st' D V W F M pp p p1 vp vp1 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% [% M]]]". iApply "H". iFrame.
    iExists (add_edge (remove_edge F p p1) p1 p RIGHT) ,
    (<[p:=NodeN (V p)]> (<[p1:=NodeR vp1 p]> M)).
    iSplit ; auto.
  Qed.
        
  Lemma rotate_left_LR_st (pp p p1 p2 : loc) (vp vp1 : Z) :
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeR vp1 p2) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ST p1 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_left_LR_st' D V W F M pp p p1 p2 vp vp1 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% [% M]]]". iApply "H". iFrame.
    iExists (update_edge (update_edge F p1 p2 p RIGHT) p p1 p2 LEFT),
    (<[p:=NodeL (V p) p2]> (<[p1:=NodeR vp1 p]> M)).
    iSplit ; auto.
  Qed.
        
  (*
                p
               / \
                 p2
                / \ 
               p3  
   *)
  
  Lemma rotate_left_LL_st `{!tctrHeapG Σ} (pp p p1 p3 : loc) (vp vp1 : Z) :
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeL vp1 p3) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ST p1 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_left_LL_st' D V W F M pp p p1 p3 vp vp1 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% M]]". iApply "H". iFrame.
    unfold ST.
    iExists (add_edge (remove_edge F p p1) p1 p RIGHT),
    (<[p:=NodeN (V p)]> (<[p1:=NodeB vp1 p3 p]> M)). iFrame.
    auto.
  Qed.
    
  (*
                p
               / \
                 p2
                /  \
               p3  p4
   *)
  
  Lemma rotate_left_LB_st (pp p p1 p3 p4 : loc) (vp vp2 : Z) :
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeB vp2 p3 p4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ST p1 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_left_LB_st' D V W F M pp p p1 p3 p4 vp vp2 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% M]]". iApply "H". iFrame.
    unfold ST.
    iExists (update_edge (update_edge F p1 p4 p RIGHT) p p1 p4 LEFT),
    (<[p:=NodeL (V p) p4]> (<[p1:=NodeB vp2 p3 p]> M)). iFrame.
    auto.
  Qed.
  
  (*

                p
               / \
             p1  p2
                 
   *)  
                      
  Lemma rotate_left_BN_st `{!tctrHeapG Σ} (pp p p1 p2 : loc) (vp vp1 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeN vp1) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ST p1 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_left_BN_st' D V W F M pp p p1 p2 vp vp1 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% M]]". iApply "H". iFrame.
    unfold ST.
    iExists (add_edge (remove_edge F p p1) p1 p RIGHT),
    (<[p:=NodeR (V p) p2]> (<[p1:=NodeR vp1 p]> M)). iFrame.
    auto.
  Qed.

  (*

                p
               / \
             p1  p2
                  \
                  p3
                 
   *)
  
  Lemma rotate_left_BR_st (pp p p1 p2 p3 : loc) (vp vp1 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeR vp1 p3) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ST p1 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_left_BR_st' D V W F M pp p p1 p2 p3 vp vp1 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% M]]". iApply "H". iFrame.
    unfold ST.
    iExists (update_edge (update_edge F p1 p3 p RIGHT) p p1 p3 LEFT),
    (<[p:=NodeB (V p) p3 p2]> (<[p1:=NodeR vp1 p]> M)). iFrame.
    auto.
  Qed.

  (*

                p
               / \
             p1  p2
                 /
                p3

   *)
  
  Lemma rotate_left_BL_st (pp p p1 p2 p3 : loc) (vp vp1 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeL vp1 p3) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ST p1 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_left_BL_st' D V W F M pp p p1 p2 p3 vp vp1 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% [% M]]]". iApply "H". iFrame.
    unfold ST.
    iExists (add_edge (remove_edge F p p1) p1 p RIGHT),
    (<[p:=NodeR (V p) p2]> (<[p1:=NodeB vp1 p3 p]> M)). iFrame.
    iSplit ; auto.
  Qed.  
  

  (*

                p
               / \
             p1  p2
                 /\
               p3 p4

   *)
  
  Lemma rotate_left_BB_st (pp p p1 p2 p3 p4 : loc) (vp vp1 : Z) :
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeB vp1 p3 p4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ST p1 D V W }}}.
  Proof.
    intros E1 E2.
    iIntros (Φ) "[R [% [% M]]] H".
    iApply (rotate_left_BB_st' D V W F M pp p p1 p2 p3 p4 vp vp1 with "[R M]") ; auto ;
      iFrame ; [iSplit ; auto|].
    iModIntro. 
    iIntros "[R [% [% M]]]". iApply "H". iFrame.
    iExists (update_edge (update_edge F p1 p4 p RIGHT) p p1 p4 LEFT),
    (<[p:=NodeB (V p) p4 p2]> (<[p1:=NodeB vp1 p3 p]> M)). iFrame.
    iSplit ; auto.
  Qed.
  
End RotateLeftRootSpecification.
