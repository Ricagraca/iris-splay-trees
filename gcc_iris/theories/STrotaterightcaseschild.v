From ST Require Import Code STdomain 
     STedgesetrotateroot STrotaterightcasesroot
     STpredicate STpath STedgeset STlink STmemory STproof.
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
     Fully proved:

           rotate_right_child_BBB_r_st
           rotate_right_child_BBL_r_st
           rotate_right_child_BBR_r_st
           rotate_right_child_BBN_r_st

           rotate_right_child_RBB_r_st
           rotate_right_child_RBL_r_st
           rotate_right_child_RBR_r_st
           rotate_right_child_RBN_r_st

           rotate_right_child_BRB_r_st
           rotate_right_child_BRL_r_st
           rotate_right_child_BRR_r_st
           rotate_right_child_BRN_r_st

           rotate_right_child_RRB_r_st
           rotate_right_child_RRL_r_st
           rotate_right_child_RRR_r_st
           rotate_right_child_RRN_r_st

*)


(*
     Structure of a tree in the gcc implementation 
             pp
             |
             p   
             |              forall p, exist pp, pp -> p ; &p
        (vp,(p1,p2))
             /   \    
               (vp2,(p3,p4))
                     /   \
         (vp3,(p5,p6))  (vp4,(p7,p8))

*)


(*
     Structure of a tree in the gcc implementation 
             pp
             |
             p  
             |            p2' <-> &p2
        (vp,(p1',p2'))
             /    \
            p1    p2        
            /      \    
                 (vp2,(p3,p4))
                       /   \
    
 *)

Section RotateRightRightChildSpecification.

  Context `{!tctrHeapG Σ} (nmax : nat).
  
  Variable v : val.
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable F : EdgeSet.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)

  (*
                  p                        p
                 /\                       / \
               p1 p2                     p1 p4
                 / \          ->           / \ 
               p3  p4                     p2 p6
                  / \                    / \
                 p5 p6                  p3 p5

   *)
  
  Lemma rotate_right_child_BBB_r_st (pp p p1 p2 p3 p4 p5 p6 : loc) (vp vp2 vp4 : Z) :    
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (update_edge F' p4 p5 p2 STorientation.LEFT) in
    let F''' := (update_edge F'' p2 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeB (V p) p1 p4]> (<[p2:=NodeB (V p2) p3 p5]> (<[p4:=NodeB (V p4) p2 p6]> M))) in 
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeB vp2 p3 p4) ->
    M !! p4 = Some (NodeB vp4 p5 p6) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeB vp2 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_BB_st' D' V W F' M tmp p2 p3 p4 p5 p6 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H H3). 
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                  (<[p2:=NodeB (V p2) p3 p5]> (<[p4:=NodeB (V p4) p2 p6]> M))
                  p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p1 p4) = Some (SOMEV (#(V p), (#p1, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H3).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 STorientation.LEFT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst p2 D' W V F' p4 p5 STorientation.RIGHT H13 H14 H15).
      apply update_comm_inv in H16 ; auto ; stlink_tac.
      pose proof (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H H3 H16).
      auto.
    + pose proof (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H H3 H4 ).
      assert (Mem D' F''' V M').
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      assert ((∀ x : elem, x \notin descendants F p2 ∧ x \in D ∧ x ≠ p → M' !! x = M !! x)).
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      assert (node_of_orientation M' p STorientation.RIGHT p4 (remove_edge_that_are_in_D F (descendants F p2)) V).
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p1.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H16 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H17 ; auto. subst. stlink_tac.
      }
      specialize (H13 H14 H15 H16). auto.
  Qed.

  (*
                  p                        p
                 /\                       / \
               p1 p2                     p1 p4
                 / \          ->           /  
               p3  p4                     p2 
                  /                      / \
                 p5                     p3 p5

   *)
  
  Lemma rotate_right_child_BBL_r_st (pp p p1 p2 p3 p4 p5 : loc) (vp vp2 vp4 : Z) :    
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (update_edge F' p4 p5 p2 STorientation.LEFT) in
    let F''' := (update_edge F'' p2 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeB (V p) p1 p4]> (<[p2:=NodeB (V p2) p3 p5]> (<[p4:=NodeL (V p4) p2]> M))) in
    
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeB vp2 p3 p4) ->
    M !! p4 = Some (NodeL vp4 p5) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeB vp2 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_BL_st' D' V W F' M tmp p2 p3 p4 p5 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H H3). 
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                  (<[p2:=NodeB (V p2) p3 p5]> (<[p4:=NodeL (V p4) p2]> M))
                  p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p1 p4) = Some (SOMEV (#(V p), (#p1, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H3).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 STorientation.LEFT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst p2 D' W V F' p4 p5 STorientation.RIGHT H13 H14 H15).
      apply update_comm_inv in H16 ; auto ; stlink_tac.
      pose proof (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H H3 H16).
      auto.
    + pose proof (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H H3 H4 ).
      assert (Mem D' F''' V M').
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      assert ((∀ x : elem, x \notin descendants F p2 ∧ x \in D ∧ x ≠ p → M' !! x = M !! x)).
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      assert (node_of_orientation M' p STorientation.RIGHT p4 (remove_edge_that_are_in_D F (descendants F p2)) V).
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p1.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H16 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H17 ; auto. subst. stlink_tac.
      }
      specialize (H13 H14 H15 H16). auto.
  Qed.

  (*
                  p                        p
                 /\                       / \
               p1 p2                     p1 p4
                 / \          ->           / \  
               p3  p4                     p2 p5
                    \                    / 
                    p5                  p3 

   *)
  
  
  Lemma rotate_right_child_BBR_r_st (pp p p1 p2 p3 p4 p5 : loc) (vp vp2 vp4 : Z) :
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (remove_edge F' p2 p4) in
    let F''' := (add_edge F'' p4 p2 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeB (V p) p1 p4]>
              (<[p2:=NodeL (V p2) p3]> (<[p4:=NodeB (V p4) p2 p5]> M))) in
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeB vp2 p3 p4) ->
    M !! p4 = Some (NodeR vp4 p5) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeB vp2 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_BR_st' D' V W F' M tmp p2 p3 p4 p5 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H H3). 
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                   (<[p2:=NodeL (V p2) p3]> (<[p4:=NodeB (V p4) p2 p5]> M))
                  p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p1 p4) = Some (SOMEV (#(V p), (#p1, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H3).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert ( ¬ (exists y,
                     F' p4 y (STorientation.invert_orientation STorientation.RIGHT))).
      intro. destruct H15. simpl in H15. destruct H15. unpack. eauto. 
      pose proof (rotate_XE_if_bst p2 D' W V F' p4 STorientation.RIGHT H13 H14 H15).
      pose proof (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H H3 ).
      apply H17. auto.
    + pose proof (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H H3 H4 ).
      assert (Mem D' F''' V M').
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      assert ((∀ x : elem, x \notin descendants F p2 ∧ x \in D ∧ x ≠ p → M' !! x = M !! x)).
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      assert (node_of_orientation M' p STorientation.RIGHT p4 (remove_edge_that_are_in_D F (descendants F p2)) V).
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p1.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H16 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H17 ; auto. subst. stlink_tac.
      }
      specialize (H13 H14 H15 H16). auto.
  Qed.  

  (*
                  p                        p
                 /\                       / \
               p1 p2                     p1 p4
                 / \          ->           /  
               p3  p4                     p2 
                                         / 
                                        p3

   *)  

  Lemma rotate_right_child_BBN_r_st (pp p p1 p2 p3 p4 : loc) (vp vp2 vp4 : Z) :
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (remove_edge F' p2 p4) in
    let F''' := (add_edge F'' p4 p2 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeB (V p) p1 p4]>
               (<[p2:=NodeL (V p2) p3]> (<[p4:=NodeL (V p4) p2]> M))) in
    
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeB vp2 p3 p4) ->
    M !! p4 = Some (NodeN vp4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeB vp2 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_BN_st' D' V W F' M tmp p2 p3 p4 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H H3). 
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                   (<[p2:=NodeL (V p2) p3]> (<[p4:=NodeL (V p4) p2]> M))
                  p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p1 p4) = Some (SOMEV (#(V p), (#p1, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H3).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert ( ¬ (exists y,
                     F' p4 y (STorientation.invert_orientation STorientation.RIGHT))).
      intro. destruct H15. simpl in H15. destruct H15. unpack. eauto. 
      pose proof (rotate_XE_if_bst p2 D' W V F' p4 STorientation.RIGHT H13 H14 H15).
      pose proof (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H H3 ).
      apply H17. auto.
    + pose proof (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H H3 H4 ).
      assert (Mem D' F''' V M').
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      assert ((∀ x : elem, x \notin descendants F p2 ∧ x \in D ∧ x ≠ p → M' !! x = M !! x)).
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      assert (node_of_orientation M' p STorientation.RIGHT p4 (remove_edge_that_are_in_D F (descendants F p2)) V).
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p1.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H16 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H17 ; auto. subst. stlink_tac.
      }
      specialize (H13 H14 H15 H16). auto.
  Qed.
  
  Lemma rotate_right_child_RBB_r_st (pp p p2 p3 p4 p5 p6 : loc) (vp vp2 vp4 : Z) :
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (update_edge F' p4 p5 p2 STorientation.LEFT) in
    let F''' := (update_edge F'' p2 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeR (V p) p4]>
              (<[p2:=NodeB (V p2) p3 p5]> (<[p4:=NodeB (V p4) p2 p6]> M))) in
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeB vp2 p3 p4) ->
    M !! p4 = Some (NodeB vp4 p5 p6) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeB vp2 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_BB_st' D' V W F' M tmp p2 p3 p4 p5 p6 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H H2). 
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                  (<[p2:=NodeB (V p2) p3 p5]> (<[p4:=NodeB (V p4) p2 p6]> M))
                  p (NodeR (V p) p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeR (V p) p4) = Some (SOMEV (#(V p), (NONEV, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H2).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 (STorientation.LEFT)).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst p2 D' W V F' p4 p5 STorientation.RIGHT H13 H14).
      simpl in H16. specialize (H16 H15).
      apply update_comm_inv in H16 ; auto ; stlink_tac.
      pose proof (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H H2 H16).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H ) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right. 
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack.
          eauto.
      }
  Qed.
  
  Lemma rotate_right_child_RBR_r_st (pp p p2 p3 p4 p6 : loc) (vp vp2 vp4 : Z) :
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (remove_edge F' p2 p4) in
    let F''' := (add_edge F'' p4 p2 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeR (V p) p4]>
              (<[p2:=NodeL (V p2) p3]> (<[p4:=NodeB (V p4) p2 p6]> M))) in
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeB vp2 p3 p4) ->
    M !! p4 = Some (NodeR vp4 p6) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeB vp2 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_BR_st' D' V W F' M tmp p2 p3 p4 p6 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H) ; auto.
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                   (<[p2:=NodeL (V p2) p3]> (<[p4:=NodeB (V p4) p2 p6]> M))
                   p (NodeR (V p) p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeR (V p) p4) = Some (SOMEV (#(V p), (NONEV, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H2).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert ( ¬ (exists y,
                     F' p4 y (STorientation.invert_orientation STorientation.RIGHT))).
      intro. destruct H15. simpl in H15. destruct H15. unpack. eauto. 
      pose proof (rotate_XE_if_bst p2 D' W V F' p4 STorientation.RIGHT H13 H14 H15).
      apply (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H) ; auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right. 
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack. eauto.
      }
  Qed.

  Lemma rotate_right_child_RBL_r_st (pp p p2 p3 p4 p5 : loc) (vp vp2 vp4 : Z) :
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (update_edge F' p4 p5 p2 STorientation.LEFT) in
    let F''' := (update_edge F'' p2 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeR (V p) p4]>
              (<[p2:=NodeB (V p2) p3 p5]> (<[p4:=NodeL (V p4) p2]> M))) in
    
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeB vp2 p3 p4) ->
    M !! p4 = Some (NodeL vp4 p5) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeB vp2 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_BL_st' D' V W F' M tmp p2 p3 p4 p5 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H H2). 
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                  (<[p2:=NodeB (V p2) p3 p5]> (<[p4:=NodeL (V p4) p2]> M))
                  p (NodeR (V p) p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeR (V p) p4) = Some (SOMEV (#(V p), (NONEV, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H2).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 (STorientation.LEFT)).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst p2 D' W V F' p4 p5 STorientation.RIGHT H13 H14).
      simpl in H16. specialize (H16 H15).
      apply update_comm_inv in H16 ; auto ; stlink_tac.
      apply (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H H2).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H ) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right. 
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack.
          eauto.
      }
  Qed.

  Lemma rotate_right_child_RBN_r_st (pp p p2 p3 p4 : loc) (vp vp2 vp4 : Z) :
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (remove_edge F' p2 p4) in
    let F''' := (add_edge F'' p4 p2 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeR (V p) p4]>
               (<[p2:=NodeL (V p2) p3]> (<[p4:=NodeL (V p4) p2]> M))) in
    
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeB vp2 p3 p4) ->
    M !! p4 = Some (NodeN vp4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeB vp2 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_BN_st' D' V W F' M tmp p2 p3 p4 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H H2). 
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                  (<[p2:=NodeL (V p2) p3]> (<[p4:=NodeL (V p4) p2]> M))
                  p (NodeR (V p) p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeR (V p) p4) = Some (SOMEV (#(V p), (NONEV, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H2).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XE_if_bst p2 D' W V F' p4 STorientation.RIGHT H13 H14).
      apply (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H H2).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H ) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right. 
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack.
          eauto.
      }
  Qed.
    
  Lemma rotate_right_child_BRB_r_st (pp p p1 p2 p4 p5 p6 : loc) (vp vp2 vp4 : Z) :    
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (update_edge F' p4 p5 p2 STorientation.LEFT) in
    let F''' := (update_edge F'' p2 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeB (V p) p1 p4]>
               (<[p2:=NodeR (V p2) p5]> (<[p4:=NodeB (V p4) p2 p6]> M))) in 
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeR vp2 p4) ->
    M !! p4 = Some (NodeB vp4 p5 p6) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeR vp2 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_RB_st' D' V W F' M tmp p2 p4 p5 p6 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H H3). 
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                  (<[p2:=NodeR (V p2) p5]> (<[p4:=NodeB (V p4) p2 p6]> M))
                  p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p1 p4) = Some (SOMEV (#(V p), (#p1, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H3).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 STorientation.LEFT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst p2 D' W V F' p4 p5 STorientation.RIGHT H13 H14 H15).
      apply update_comm_inv in H16 ; auto ; stlink_tac.
      pose proof (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H H3 H16).
      auto.
    + pose proof (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H H3 H4 ).
      assert (Mem D' F''' V M').
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      assert ((∀ x : elem, x \notin descendants F p2 ∧ x \in D ∧ x ≠ p → M' !! x = M !! x)).
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      assert (node_of_orientation M' p STorientation.RIGHT p4 (remove_edge_that_are_in_D F (descendants F p2)) V).
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p1.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H16 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H17 ; auto. subst. stlink_tac.
      }
      specialize (H13 H14 H15 H16). auto.
  Qed.

  (*
                  p                        p
                 /\                       / \
               p1 p2                     p1 p4
                 / \          ->           /  
               p3  p4                     p2 
                  /                      / \
                 p5                     p3 p5

   *)
  
  Lemma rotate_right_child_BRL_r_st (pp p p1 p2 p4 p5 : loc) (vp vp2 vp4 : Z) :    
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (update_edge F' p4 p5 p2 STorientation.LEFT) in
    let F''' := (update_edge F'' p2 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeB (V p) p1 p4]>
               (<[p2:=NodeR (V p2) p5]> (<[p4:=NodeL (V p4) p2]> M))) in
    
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeR vp2 p4) ->
    M !! p4 = Some (NodeL vp4 p5) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeR vp2 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_RL_st' D' V W F' M tmp p2 p4 p5 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H H3). 
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                  (<[p2:=NodeR (V p2) p5]> (<[p4:=NodeL (V p4) p2]> M))
                  p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p1 p4) = Some (SOMEV (#(V p), (#p1, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H3).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 STorientation.LEFT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst p2 D' W V F' p4 p5 STorientation.RIGHT H13 H14 H15).
      apply update_comm_inv in H16 ; auto ; stlink_tac.
      pose proof (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H H3 H16).
      auto.
    + pose proof (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H H3 H4 ).
      assert (Mem D' F''' V M').
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      assert ((∀ x : elem, x \notin descendants F p2 ∧ x \in D ∧ x ≠ p → M' !! x = M !! x)).
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      assert (node_of_orientation M' p STorientation.RIGHT p4 (remove_edge_that_are_in_D F (descendants F p2)) V).
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p1.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H16 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H17 ; auto. subst. stlink_tac.
      }
      specialize (H13 H14 H15 H16). auto.
  Qed.

  (*
                  p                        p
                 /\                       / \
               p1 p2                     p1 p4
                 / \          ->           / \  
               p3  p4                     p2 p5
                    \                    / 
                    p5                  p3 

   *)
  
  
  Lemma rotate_right_child_BRR_r_st (pp p p1 p2 p4 p5 : loc) (vp vp2 vp4 : Z) :
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (remove_edge F' p2 p4) in
    let F''' := (add_edge F'' p4 p2 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeB (V p) p1 p4]>
               (<[p2:=NodeN (V p2)]> (<[p4:=NodeB (V p4) p2 p5]> M))) in
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeR vp2 p4) ->
    M !! p4 = Some (NodeR vp4 p5) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeR vp2 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_RR_st' D' V W F' M tmp p2 p4 p5 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H H3). 
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                   (<[p2:=NodeN (V p2)]> (<[p4:=NodeB (V p4) p2 p5]> M))
                   p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p1 p4) = Some (SOMEV (#(V p), (#p1, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H3).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert ( ¬ (exists y,
                     F' p4 y (STorientation.invert_orientation STorientation.RIGHT))).
      intro. destruct H15. simpl in H15. destruct H15. unpack. eauto. 
      pose proof (rotate_XE_if_bst p2 D' W V F' p4 STorientation.RIGHT H13 H14 H15).
      pose proof (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H H3 ).
      apply H17. auto.
    + pose proof (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H H3 H4 ).
      assert (Mem D' F''' V M').
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      assert ((∀ x : elem, x \notin descendants F p2 ∧ x \in D ∧ x ≠ p → M' !! x = M !! x)).
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      assert (node_of_orientation M' p STorientation.RIGHT p4 (remove_edge_that_are_in_D F (descendants F p2)) V).
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p1.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H16 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H17 ; auto. subst. stlink_tac.
      }
      specialize (H13 H14 H15 H16). auto.
  Qed.  

  (*
                  p                        p
                 /\                       / \
               p1 p2                     p1 p4
                 / \          ->           /  
               p3  p4                     p2 
                                         / 
                                        p3

   *)  

  Lemma rotate_right_child_BRN_r_st (pp p p1 p2 p4 : loc) (vp vp2 vp4 : Z) :
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (remove_edge F' p2 p4) in
    let F''' := (add_edge F'' p4 p2 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeB (V p) p1 p4]>
               (<[p2:=NodeN (V p2)]> (<[p4:=NodeL (V p4) p2]> M))) in
    
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p2 = Some (NodeR vp2 p4) ->
    M !! p4 = Some (NodeN vp4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeR vp2 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_RN_st' D' V W F' M tmp p2 p4 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H H3). 
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                   (<[p2:=NodeN (V p2)]> (<[p4:=NodeL (V p4) p2]> M))
                   p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p1 p4) = Some (SOMEV (#(V p), (#p1, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H3).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert ( ¬ (exists y,
                     F' p4 y (STorientation.invert_orientation STorientation.RIGHT))).
      intro. destruct H15. simpl in H15. destruct H15. unpack. eauto. 
      pose proof (rotate_XE_if_bst p2 D' W V F' p4 STorientation.RIGHT H13 H14 H15).
      pose proof (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H H3 ).
      apply H17. auto.
    + pose proof (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H H3 H4 ).
      assert (Mem D' F''' V M').
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      assert ((∀ x : elem, x \notin descendants F p2 ∧ x \in D ∧ x ≠ p → M' !! x = M !! x)).
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H15. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      assert (node_of_orientation M' p STorientation.RIGHT p4 (remove_edge_that_are_in_D F (descendants F p2)) V).
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p1.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H16 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H17 ; auto. subst. stlink_tac.
      }
      specialize (H13 H14 H15 H16). auto.
  Qed.

    
  Lemma rotate_right_child_RRB_r_st (pp p p2 p4 p5 p6 : loc) (vp vp2 vp4 : Z) :
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (update_edge F' p4 p5 p2 STorientation.LEFT) in
    let F''' := (update_edge F'' p2 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeR (V p) p4]>
               (<[p2:=NodeR (V p2) p5]> (<[p4:=NodeB (V p4) p2 p6]> M))) in 
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeR vp2 p4) ->
    M !! p4 = Some (NodeB vp4 p5 p6) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeR vp2 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_RB_st' D' V W F' M tmp p2 p4 p5 p6 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H H2). 
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                  (<[p2:=NodeR (V p2) p5]> (<[p4:=NodeB (V p4) p2 p6]> M))
                  p (NodeR (V p) p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeR (V p) p4) = Some (SOMEV (#(V p), (NONEV, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H2).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 (STorientation.LEFT)).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst p2 D' W V F' p4 p5 STorientation.RIGHT H13 H14).
      simpl in H16. specialize (H16 H15).
      apply update_comm_inv in H16 ; auto ; stlink_tac.
      pose proof (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H H2 H16).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H ) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right. 
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack.
          eauto.
      }
  Qed.
  
  Lemma rotate_right_child_RRR_r_st (pp p p2 p4 p6 : loc) (vp vp2 vp4 : Z) :
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (remove_edge F' p2 p4) in
    let F''' := (add_edge F'' p4 p2 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeR (V p) p4]>
               (<[p2:=NodeN (V p2)]> (<[p4:=NodeB (V p4) p2 p6]> M))) in
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeR vp2 p4) ->
    M !! p4 = Some (NodeR vp4 p6) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeR vp2 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_RR_st' D' V W F' M tmp p2 p4 p6 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H) ; auto.
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                   (<[p2:=NodeN (V p2)]> (<[p4:=NodeB (V p4) p2 p6]> M))
                   p (NodeR (V p) p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeR (V p) p4) = Some (SOMEV (#(V p), (NONEV, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H2).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert ( ¬ (exists y,
                     F' p4 y (STorientation.invert_orientation STorientation.RIGHT))).
      intro. destruct H15. simpl in H15. destruct H15. unpack. eauto. 
      pose proof (rotate_XE_if_bst p2 D' W V F' p4 STorientation.RIGHT H13 H14 H15).
      apply (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H) ; auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right. 
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack. eauto.
      }
  Qed.

  Lemma rotate_right_child_RRL_r_st (pp p p2 p4 p5 : loc) (vp vp2 vp4 : Z) :
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (update_edge F' p4 p5 p2 STorientation.LEFT) in
    let F''' := (update_edge F'' p2 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeR (V p) p4]>
              (<[p2:=NodeR (V p2) p5]> (<[p4:=NodeL (V p4) p2]> M))) in
    
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeR vp2 p4) ->
    M !! p4 = Some (NodeL vp4 p5) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeR vp2 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_RL_st' D' V W F' M tmp p2 p4 p5 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H H2). 
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                  (<[p2:=NodeR (V p2) p5]> (<[p4:=NodeL (V p4) p2]> M))
                  p (NodeR (V p) p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeR (V p) p4) = Some (SOMEV (#(V p), (NONEV, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H2).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 (STorientation.LEFT)).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst p2 D' W V F' p4 p5 STorientation.RIGHT H13 H14).
      simpl in H16. specialize (H16 H15).
      apply update_comm_inv in H16 ; auto ; stlink_tac.
      apply (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H H2).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H ) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right. 
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack.
          eauto.
      }
  Qed.

  Lemma rotate_right_child_RRN_r_st (pp p p2 p4 : loc) (vp vp2 vp4 : Z) :
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (remove_edge F' p2 p4) in
    let F''' := (add_edge F'' p4 p2 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.RIGHT) in 
    
    let M' := (<[p:=NodeR (V p) p4]>
               (<[p2:=NodeN (V p2)]> (<[p4:=NodeL (V p4) p2]> M))) in
    
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeR vp2 p4) ->
    M !! p4 = Some (NodeN vp4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_right ("tmp") #p2 (right_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p2 (NodeR vp2 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p2 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p2). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p2 #p4).
    iPoseProof (rotate_right_RN_st' D' V W F' M tmp p2 p4 (V p2) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p2 STorientation.RIGHT H H2). 
    apply (M_inv_incl D F V W M p p2 STorientation.RIGHT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.

    wp_load. 
    
    iPoseProof (mapsto_M_acc
                  (<[p2:=NodeN (V p2)]> (<[p4:=NodeL (V p4) p2]> M))
                  p (NodeR (V p) p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (left_child%V #p).    
    iApply (left_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeR (V p) p4) = Some (SOMEV (#(V p), (NONEV, #p4))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p2 STorientation.RIGHT H H2).
      assert (F' p2 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XE_if_bst p2 D' W V F' p4 STorientation.RIGHT H13 H14).
      apply (join_if_inv p D W V F F''' p2 p4 STorientation.RIGHT H H2).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p2 p4 STorientation.RIGHT H0 H ) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right. 
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack.
          eauto.
      }
  Qed.
  
End RotateRightRightChildSpecification.


(*
     Fully proved:

           rotate_right_child_BBB_l_st
           rotate_right_child_BBL_l_st
           rotate_right_child_BBR_l_st
           rotate_right_child_BBN_l_st

           rotate_right_child_LBB_l_st
           rotate_right_child_LBL_l_st
           rotate_right_child_LBR_l_st
           rotate_right_child_LBN_l_st

           rotate_right_child_BRB_l_st
           rotate_right_child_BRL_l_st
           rotate_right_child_BRR_l_st
           rotate_right_child_BRN_l_st

           rotate_right_child_LRB_l_st
           rotate_right_child_LRL_l_st
           rotate_right_child_LRR_l_st
           rotate_right_child_LRN_l_st

*)


Section RotateRightLeftChildSpecification.

  Context `{!tctrHeapG Σ} (nmax : nat).
  
  Variable v : val.
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable F : EdgeSet.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)
  
  Lemma rotate_right_child_BBB_l_st (pp p p1 p2 p3 p4 p5 p6 : loc) (vp vp1 vp4 : Z) :    
    let D' := descendants F p1 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (update_edge F' p4 p5 p1 STorientation.LEFT) in
    let F''' := (update_edge F'' p1 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in 
    
    let M' := (<[p:=NodeB (V p) p4 p2]>
             (<[p1:=NodeB (V p1) p3 p5]> (<[p4:=NodeB (V p4) p1 p6]> M))) in 
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeB vp1 p3 p4) ->
    M !! p4 = Some (NodeB vp4 p5 p6) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeB vp1 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_BB_st' D' V W F' M tmp p1 p3 p4 p5 p6 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2). auto.
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                  (<[p1:=NodeB (V p1) p3 p5]> (<[p4:=NodeB (V p4) p1 p6]> M))
                  p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load. 
    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p4 p2) = Some (SOMEV (#(V p), (#p4, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 STorientation.LEFT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst p1 D' W V F' p4 p5 STorientation.RIGHT). simpl in H16.
      apply update_comm_inv in H16 ; auto ; stlink_tac.
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT H0 H) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p2.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H13 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H14 ; auto. stlink_tac. subst. stlink_tac.
      }
  Qed.

  (*
                  p                        p
                 /\                       / \
               p1 p2                     p1 p4
                 / \          ->           /  
               p3  p4                     p2 
                  /                      / \
                 p5                     p3 p5

   *)
  
  Lemma rotate_right_child_BBL_l_st (pp p p1 p2 p3 p4 p5 : loc) (vp vp1 vp4 : Z) :  
    let D' := descendants F p1 in
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in
    let F'' := (update_edge F' p4 p5 p1 STorientation.LEFT) in
    let F''' := (update_edge F'' p1 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in
    
    let M' := (<[p:=NodeB (V p) p4 p2]>
             (<[p1:=NodeB (V p1) p3 p5]> (<[p4:=NodeL (V p4) p1]> M))) in
    
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeB vp1 p3 p4) ->
    M !! p4 = Some (NodeL vp4 p5) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeB vp1 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_BL_st' D' V W F' M tmp p1 p3 p4 p5 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2). auto.
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                  (<[p1:=NodeB (V p1) p3 p5]> (<[p4:=NodeL (V p4) p1]> M))
                  p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load. 
    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p4 p2) = Some (SOMEV (#(V p), (#p4, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 STorientation.LEFT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst p1 D' W V F' p4 p5 STorientation.RIGHT). simpl in H16.
      apply update_comm_inv in H16 ; auto ; stlink_tac.
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT H0 H) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p2.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H13 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H14 ; auto. stlink_tac. subst. stlink_tac.
      }
  Qed.
  
  Lemma rotate_right_child_BBR_l_st (pp p p1 p2 p3 p4 p5 : loc) (vp vp1 vp4 : Z) :
    let D' := descendants F p1 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (remove_edge F' p1 p4) in
    let F''' := (add_edge F'' p4 p1 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in 
    
    let M' := (<[p:=NodeB (V p) p4 p2]>
               (<[p1:=NodeL (V p1) p3]> (<[p4:=NodeB (V p4) p1 p5]> M))) in
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeB vp1 p3 p4) ->
    M !! p4 = Some (NodeR vp4 p5) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeB vp1 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_BR_st' D' V W F' M tmp p1 p3 p4 p5 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2). auto.
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                  (<[p1:=NodeL (V p1) p3]> (<[p4:=NodeB (V p4) p1 p5]> M))
                  p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load. 
    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p4 p2) = Some (SOMEV (#(V p), (#p4, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XE_if_bst p1 D' W V F' p4 STorientation.RIGHT). simpl in H16.
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT H0 H) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p2.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H13 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H14 ; auto. stlink_tac. subst. stlink_tac.
      }
  Qed.  

  (*
                  p                        p
                 /\                       / \
               p1 p2                     p1 p4
                 / \          ->           /  
               p3  p4                     p2 
                                         / 
                                        p3

   *)  

  Lemma rotate_right_child_BBN_l_st (pp p p1 p2 p3 p4 : loc) (vp vp1 vp4 : Z) :
    let D' := descendants F p1 in
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in
    let F'' := (remove_edge F' p1 p4) in
    let F''' := (add_edge F'' p4 p1 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in
    
    let M' := (<[p:=NodeB (V p) p4 p2]>
               (<[p1:=NodeL (V p1) p3]> (<[p4:=NodeL (V p4) p1]> M))) in
    
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeB vp1 p3 p4) ->
    M !! p4 = Some (NodeN vp4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeB vp1 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_BN_st' D' V W F' M tmp p1 p3 p4 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p1 STorientation.LEFT H) ; auto.
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                  (<[p1:=NodeL (V p1) p3]> (<[p4:=NodeL (V p4) p1]> M))
                  p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load.

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p4 p2) = Some (SOMEV (#(V p), (#p4, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XE_if_bst p1 D' W V F' p4 STorientation.RIGHT). 
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT H0 H) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p2.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H13 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H14 ; auto. stlink_tac. subst. stlink_tac.
      }
  Qed.
  
  Lemma rotate_right_child_LBB_l_st (pp p p1 p3 p4 p5 p6 : loc) (vp vp1 vp4 : Z) :
    let D' := descendants F p1 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (update_edge F' p4 p5 p1 STorientation.LEFT) in
    let F''' := (update_edge F'' p1 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in 
    
    let M' := (<[p:=NodeL (V p) p4]>
               (<[p1:=NodeB (V p1) p3 p5]> (<[p4:=NodeB (V p4) p1 p6]> M))) in
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeB vp1 p3 p4) ->
    M !! p4 = Some (NodeB vp4 p5 p6) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeB vp1 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_BB_st' D' V W F' M tmp p1 p3 p4 p5 p6 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p1 STorientation.LEFT H) ; auto. 
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                  (<[p1:=NodeB (V p1) p3 p5]> (<[p4:=NodeB (V p4) p1 p6]> M))
                  p (NodeL (V p) p1) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load.
    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeL (V p) p4) = Some (SOMEV (#(V p), (#p4,NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      pose proof (rotate_XI_if_bst p1 D' W V F' p4 p5 STorientation.RIGHT H13).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 STorientation.LEFT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      simpl in H14. specialize (H14 H15 H16).
      apply update_comm_inv in H14 ; auto ; stlink_tac.
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT H).
      apply H17 ; auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT H0 H ) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right. 
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack.
          eauto.
      }
  Qed.
  
  Lemma rotate_right_child_LBR_l_st (pp p p1 p3 p4 p6 : loc) (vp vp1 vp4 : Z) :
    let D' := descendants F p1 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (remove_edge F' p1 p4) in
    let F''' := (add_edge F'' p4 p1 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in 
    
    let M' := (<[p:=NodeL (V p) p4]>
               (<[p1:=NodeL (V p1) p3]> (<[p4:=NodeB (V p4) p1 p6]> M))) in
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeB vp1 p3 p4) ->
    M !! p4 = Some (NodeR vp4 p6) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeB vp1 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_BR_st' D' V W F' M tmp p1 p3 p4 p6 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p1 STorientation.LEFT H) ; auto.
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                   (<[p1:=NodeL (V p1) p3]> (<[p4:=NodeB (V p4) p1 p6]> M))
                   p (NodeL (V p) p1) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load.
    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeL (V p) p4) = Some (SOMEV (#(V p), (#p4,NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert ( ¬ (exists y,
                     F' p4 y (STorientation.invert_orientation STorientation.RIGHT))).
      intro. destruct H15. simpl in H15. destruct H15. unpack. eauto. 
      pose proof (rotate_XE_if_bst p1 D' W V F' p4 STorientation.RIGHT H13 H14 H15).
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT).
      apply H17 ; auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack. eauto.
      }
  Qed.

  Lemma rotate_right_child_LBL_l_st (pp p p1 p3 p4 p5 : loc) (vp vp1 vp4 : Z) :
    let D' := descendants F p1 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (update_edge F' p4 p5 p1 STorientation.LEFT) in
    let F''' := (update_edge F'' p1 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in 
    
    let M' := (<[p:=NodeL (V p) p4]>
               (<[p1:=NodeB (V p1) p3 p5]> (<[p4:=NodeL (V p4) p1]> M))) in
    
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeB vp1 p3 p4) ->
    M !! p4 = Some (NodeL vp4 p5) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeB vp1 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_BL_st' D' V W F' M tmp p1 p3 p4 p5 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p1 STorientation.LEFT H) ; auto.
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                  (<[p1:=NodeB (V p1) p3 p5]> (<[p4:=NodeL (V p4) p1]> M))
                  p (NodeL (V p) p1) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load.
    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeL (V p) p4) = Some (SOMEV (#(V p), (#p4, NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 STorientation.LEFT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst p1 D' W V F' p4 p5 STorientation.RIGHT H13 H14).
      simpl in H16. specialize (H16 H15).
      apply update_comm_inv in H16 ; auto ; stlink_tac.
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT ) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right. 
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack.
          eauto.
      }
  Qed.

  Lemma rotate_right_child_LBN_l_st (pp p p1 p3 p4 : loc) (vp vp1 vp4 : Z) :
    let D' := descendants F p1 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (remove_edge F' p1 p4) in
    let F''' := (add_edge F'' p4 p1 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in 
    
    let M' := (<[p:=NodeL (V p) p4]>
               (<[p1:=NodeL (V p1) p3]> (<[p4:=NodeL (V p4) p1]> M))) in
    
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeB vp1 p3 p4) ->
    M !! p4 = Some (NodeN vp4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeB vp1 p3 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_BN_st' D' V W F' M tmp p1 p3 p4 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p1 STorientation.LEFT H) ; auto.
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                  (<[p1:=NodeL (V p1) p3]> (<[p4:=NodeL (V p4) p1]> M))
                  p (NodeL (V p) p1) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load.
    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeL (V p) p4) = Some (SOMEV (#(V p), (#p4, NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert ( ¬ (exists y,
                     F' p4 y (STorientation.invert_orientation STorientation.RIGHT))).
      intro. destruct H15. simpl in H15. destruct H15. unpack. eauto. 
      pose proof (rotate_XE_if_bst p1 D' W V F' p4 STorientation.RIGHT H13 H14 H15).
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT).
      apply H17 ; auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack. eauto.
      }
  Qed.

  Lemma rotate_right_child_BRB_l_st (pp p p1 p2 p4 p5 p6 : loc) (vp vp1 vp4 : Z) :    
    let D' := descendants F p1 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (update_edge F' p4 p5 p1 STorientation.LEFT) in
    let F''' := (update_edge F'' p1 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in 
    
    let M' := (<[p:=NodeB (V p) p4 p2]>
               (<[p1:=NodeR (V p1) p5]> (<[p4:=NodeB (V p4) p1 p6]> M))) in 
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeR vp1 p4) ->
    M !! p4 = Some (NodeB vp4 p5 p6) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeR vp1 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_RB_st' D' V W F' M tmp p1 p4 p5 p6 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2). auto.
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                  (<[p1:=NodeR (V p1) p5]> (<[p4:=NodeB (V p4) p1 p6]> M))
                  p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load. 
    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p4 p2) = Some (SOMEV (#(V p), (#p4, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 STorientation.LEFT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst p1 D' W V F' p4 p5 STorientation.RIGHT). simpl in H16.
      apply update_comm_inv in H16 ; auto ; stlink_tac.
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT H0 H) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p2.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H13 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H14 ; auto. stlink_tac. subst. stlink_tac.
      }
  Qed.
  
  Lemma rotate_right_child_BRL_l_st (pp p p1 p2 p4 p5 : loc) (vp vp1 vp4 : Z) :  
    let D' := descendants F p1 in
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in
    let F'' := (update_edge F' p4 p5 p1 STorientation.LEFT) in
    let F''' := (update_edge F'' p1 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in
    
    let M' := (<[p:=NodeB (V p) p4 p2]>
               (<[p1:=NodeR (V p1) p5]> (<[p4:=NodeL (V p4) p1]> M))) in
    
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeR vp1 p4) ->
    M !! p4 = Some (NodeL vp4 p5) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeR vp1 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_RL_st' D' V W F' M tmp p1 p4 p5 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2). auto.
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                  (<[p1:=NodeR (V p1) p5]> (<[p4:=NodeL (V p4) p1]> M))
                  p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load. 
    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p4 p2) = Some (SOMEV (#(V p), (#p4, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 STorientation.LEFT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst p1 D' W V F' p4 p5 STorientation.RIGHT). simpl in H16.
      apply update_comm_inv in H16 ; auto ; stlink_tac.
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT H0 H) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p2.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H13 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H14 ; auto. stlink_tac. subst. stlink_tac.
      }
  Qed.
  
  Lemma rotate_right_child_BRR_l_st (pp p p1 p2 p4 p5 : loc) (vp vp1 vp4 : Z) :
    let D' := descendants F p1 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (remove_edge F' p1 p4) in
    let F''' := (add_edge F'' p4 p1 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in 
    
    let M' := (<[p:=NodeB (V p) p4 p2]>
               (<[p1:=NodeN (V p1)]> (<[p4:=NodeB (V p4) p1 p5]> M))) in
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeR vp1 p4) ->
    M !! p4 = Some (NodeR vp4 p5) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeR vp1 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_RR_st' D' V W F' M tmp p1 p4 p5 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2). auto.
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                  (<[p1:=NodeN (V p1)]> (<[p4:=NodeB (V p4) p1 p5]> M))
                  p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load. 
    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p4 p2) = Some (SOMEV (#(V p), (#p4, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XE_if_bst p1 D' W V F' p4 STorientation.RIGHT). simpl in H16.
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT H0 H) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p2.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H13 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H14 ; auto. stlink_tac. subst. stlink_tac.
      }
  Qed.  

  (*
                  p                        p
                 /\                       / \
               p1 p2                     p1 p4
                 / \          ->           /  
               p3  p4                     p2 
                                         / 
                                        p3

   *)  

  Lemma rotate_right_child_BRN_l_st (pp p p1 p2 p4 : loc) (vp vp1 vp4 : Z) :
    let D' := descendants F p1 in
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in
    let F'' := (remove_edge F' p1 p4) in
    let F''' := (add_edge F'' p4 p1 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in
    
    let M' := (<[p:=NodeB (V p) p4 p2]>
               (<[p1:=NodeN (V p1)]> (<[p4:=NodeL (V p4) p1]> M))) in
    
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeR vp1 p4) ->
    M !! p4 = Some (NodeN vp4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeR vp1 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_RN_st' D' V W F' M tmp p1 p4 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p1 STorientation.LEFT H) ; auto.
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                  (<[p1:=NodeN (V p1)]> (<[p4:=NodeL (V p4) p1]> M))
                  p (NodeB (V p) p1 p2) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load.

    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeB (V p) p4 p2) = Some (SOMEV (#(V p), (#p4, #p2))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XE_if_bst p1 D' W V F' p4 STorientation.RIGHT). 
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT H0 H) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. left. exists p2.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          repeat split ; auto ; intro ; rewrite in_set_st_eq in H13 ; stpath_tac.
          pose proof (path_only_if_child_equal p D V W F p p2 p1 STorientation.RIGHT STorientation.LEFT).
          assert (p2 = p1). apply H14 ; auto. stlink_tac. subst. stlink_tac.
      }
  Qed.

  Lemma rotate_right_child_LRB_l_st (pp p p1 p4 p5 p6 : loc) (vp vp1 vp4 : Z) :
    let D' := descendants F p1 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (update_edge F' p4 p5 p1 STorientation.LEFT) in
    let F''' := (update_edge F'' p1 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in 
    
    let M' := (<[p:=NodeL (V p) p4]>
               (<[p1:=NodeR (V p1) p5]> (<[p4:=NodeB (V p4) p1 p6]> M))) in
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeR vp1 p4) ->
    M !! p4 = Some (NodeB vp4 p5 p6) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeR vp1 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_RB_st' D' V W F' M tmp p1 p4 p5 p6 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p1 STorientation.LEFT H) ; auto. 
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                  (<[p1:=NodeR (V p1) p5]> (<[p4:=NodeB (V p4) p1 p6]> M))
                  p (NodeL (V p) p1) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load.
    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeL (V p) p4) = Some (SOMEV (#(V p), (#p4,NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      pose proof (rotate_XI_if_bst p1 D' W V F' p4 p5 STorientation.RIGHT H13).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 STorientation.LEFT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      simpl in H14. specialize (H14 H15 H16).
      apply update_comm_inv in H14 ; auto ; stlink_tac.
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT H).
      apply H17 ; auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT H0 H ) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right. 
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack.
          eauto.
      }
  Qed.
  
  Lemma rotate_right_child_LRR_l_st (pp p p1 p4 p6 : loc) (vp vp1 vp4 : Z) :
    let D' := descendants F p1 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (remove_edge F' p1 p4) in
    let F''' := (add_edge F'' p4 p1 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in 
    
    let M' := (<[p:=NodeL (V p) p4]>
               (<[p1:=NodeN (V p1)]> (<[p4:=NodeB (V p4) p1 p6]> M))) in
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeR vp1 p4) ->
    M !! p4 = Some (NodeR vp4 p6) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeR vp1 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_RR_st' D' V W F' M tmp p1 p4 p6 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p1 STorientation.LEFT H) ; auto.
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                   (<[p1:=NodeN (V p1)]> (<[p4:=NodeB (V p4) p1 p6]> M))
                   p (NodeL (V p) p1) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load.
    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeL (V p) p4) = Some (SOMEV (#(V p), (#p4,NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert ( ¬ (exists y,
                     F' p4 y (STorientation.invert_orientation STorientation.RIGHT))).
      intro. destruct H15. simpl in H15. destruct H15. unpack. eauto. 
      pose proof (rotate_XE_if_bst p1 D' W V F' p4 STorientation.RIGHT H13 H14 H15).
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT).
      apply H17 ; auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack. eauto.
      }
  Qed.

  Lemma rotate_right_child_LRL_l_st (pp p p1 p4 p5 : loc) (vp vp1 vp4 : Z) :
    let D' := descendants F p1 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (update_edge F' p4 p5 p1 STorientation.LEFT) in
    let F''' := (update_edge F'' p1 p4 p5 STorientation.RIGHT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in 
    
    let M' := (<[p:=NodeL (V p) p4]>
               (<[p1:=NodeR (V p1) p5]> (<[p4:=NodeL (V p4) p1]> M))) in
    
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeR vp1 p4) ->
    M !! p4 = Some (NodeL vp4 p5) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeR vp1 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_RL_st' D' V W F' M tmp p1 p4 p5 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p1 STorientation.LEFT H) ; auto.
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                  (<[p1:=NodeR (V p1) p5]> (<[p4:=NodeL (V p4) p1]> M))
                  p (NodeL (V p) p1) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load.
    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeL (V p) p4) = Some (SOMEV (#(V p), (#p4, NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (F' p4 p5 STorientation.LEFT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      pose proof (rotate_XI_if_bst p1 D' W V F' p4 p5 STorientation.RIGHT H13 H14).
      simpl in H16. specialize (H16 H15).
      apply update_comm_inv in H16 ; auto ; stlink_tac.
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT).
      auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT ) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right. 
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack.
          eauto.
      }
  Qed.

  Lemma rotate_right_child_LRN_l_st (pp p p1 p4 : loc) (vp vp1 vp4 : Z) :
    let D' := descendants F p1 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (remove_edge F' p1 p4) in
    let F''' := (add_edge F'' p4 p1 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p4 STorientation.LEFT) in 
    
    let M' := (<[p:=NodeL (V p) p4]>
               (<[p1:=NodeN (V p1)]> (<[p4:=NodeL (V p4) p1]> M))) in
    
    M !! p  = Some (NodeL vp p1) ->
    M !! p1 = Some (NodeR vp1 p4) ->
    M !! p4 = Some (NodeN vp4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p1 in 
      rotate_right ("tmp") #p1 (right_child #p1) ;;
      #p <- SOME (value #p, (!"tmp", right_child #p))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros D' FC' F' F'' F''' F'''' M' E1 E2 E3.
    iIntros (Φ) "[R [% [% M]]] H".
    inversion H. unfold is_bst in Inv_bst. 

    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    
    iPoseProof (mapsto_M_acc_same M p1 (NodeR vp1 p4) E2 with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]". 
    simpl in H1. inversion H1 ; subst.

    wp_alloc tmp as "Htmp".
    wp_let.

    apply H0 in rootisindomain. rewrite E1 in rootisindomain.
    unpack. assert (p1 \in D). stdomain_tac.
    apply H0 in H7. rewrite E2 in H7. 
    unpack. assert (p4 \in D). stdomain_tac.
    apply H0 in H10. rewrite E3 in H10. unpack. subst.

    (* Get value of right child *)
    wp_bind (right_child %V #p1). 
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".
    
    iDestruct ("M" with "Hp") as "M".

    wp_bind (rotate_right #tmp #p1 #p4).
    iPoseProof (rotate_right_RN_st' D' V W F' M tmp p1 p4 (V p1) (V p4) E2 E3 with "[Htmp M]") as "Hr".
    iFrame. iPureIntro.
    split.
    apply (child_if_inv p D W V F p1 STorientation.LEFT H) ; auto.
    apply (M_inv_incl D F V W M p p1 STorientation.LEFT) ; auto.
    iApply "Hr". iModIntro. iIntros "[H1 [% [% M]]]".
    wp_seq.
    
    iPoseProof (mapsto_M_acc
                  (<[p1:=NodeN (V p1)]> (<[p4:=NodeL (V p4) p1]> M))
                  p (NodeL (V p) p1) with "M")
      as "M".

    do 2 (rewrite lookup_insert_ne ; stlink_tac ; auto).
    
    iDestruct "M" as (v') "[% [Hp M]]". 
    inversion H12 ; subst.
    
    (* Get left child of p *)
    wp_bind (right_child%V #p).    
    iApply (right_child_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_load.
    wp_pair.
    
    (* Get value of p *)
    wp_bind (value%V #p).    
    iApply (value_specification with "[Hp]") ; auto.
    iModIntro. iIntros "Hp".

    wp_store.

    (*save in memory*)
    iAssert
      (bi_pure (val_of_content (NodeL (V p) p4) = Some (SOMEV (#(V p), (#p4, NONEV))))) as "H'".
    iPureIntro. auto.
    iDestruct ("M" with "[H'] [Hp]") as "M" ; auto.

    iApply "H" ; iFrame.
    iSplit ; iPureIntro ; auto.
    + pose proof (child_if_inv p D W V F p1 STorientation.LEFT H H2).
      assert (F' p1 p4 STorientation.RIGHT).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert ( ¬ (exists y,
                     F' p4 y (STorientation.invert_orientation STorientation.RIGHT))).
      intro. destruct H15. simpl in H15. destruct H15. unpack. eauto. 
      pose proof (rotate_XE_if_bst p1 D' W V F' p4 STorientation.RIGHT H13 H14 H15).
      pose proof (join_if_inv p D W V F F''' p1 p4 STorientation.LEFT).
      apply H17 ; auto.
    + apply (M_inv_add_union_edge_if_different p D F F''' V W M M' p1 p4 STorientation.LEFT) ; auto.
      { intros x H'. unfold M'.
        rewrite lookup_insert_ne. apply H9 ; auto. intro. subst x.
        rewrite in_set_st_eq in H'. stpath_tac.
      }
      { 
        intros. unpack.
        rewrite lookup_insert_ne. rewrite lookup_insert_ne. rewrite lookup_insert_ne. auto.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. apply H13. rewrite in_set_st_eq. stpath_tac.
        intro. subst. contradiction.
      }
      {
        unfold node_of_orientation. exists (V p) ; split ; auto. right.
        split.
        - rewrite lookup_insert ; auto.
        - unfold remove_edge_that_are_in_D.
          intro. destruct H13. unpack. eauto.
      }
  Qed.
  
End RotateRightLeftChildSpecification.
