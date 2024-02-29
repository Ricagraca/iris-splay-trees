From ST Require Import Code STorientation 
     STpredicate STpath STedgeset STedgesetrotateroot
     STrotaterightcasesroot STrotateleftcasesroot STlink STmemory STproof STdomain STpathcount     .
From iris_time.heap_lang Require Import notation lib.assert.
From iris_time.heap_lang Require Export lang.
From iris_time.heap_lang Require Import proofmode.
From iris_time Require Import Combined.

From iris.bi Require Import big_op.
From iris_time.heap_lang Require Import proofmode.
From iris_time Require Import Combined.

From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual
     LibInt.

Section SplaySubCasesRightGCRotation.

  Context `{!tctrHeapG Σ} (nmax : nat).

  Variable v : val.
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)

  Lemma splay_root_rotate_right_gc_eq_st F (pp p p' y : loc) (z : Z) (n : nat) :
    Inv p D F V W ->
    Mem D F V M ->
    V p < z -> 
    F p p' RIGHT ->
    z = V p' -> 
    F p' y LEFT ->
    let F' := (update_edge F p' y p LEFT) in
    let F'' := (update_edge F' p p' y RIGHT) in
    {{{ pp ↦ #p ∗ mapsto_M M }}}
      splay_tree_while_loop #pp #z
      {{{ M', RET #() ; pp ↦ #p' ∗ ⌜Inv p' D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗ mapsto_M M'}}}.
  Proof. 
    intros.
    iIntros "[R M] H".
    inversion H. subst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].

    apply H0 in rootisindomain.
    destruct (M !! p) eqn:E ; try contradiction.

    unfold splay_tree_while_loop. wp_lam.
    wp_load. wp_let.

    iPoseProof (mapsto_M_acc_same M p c E with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]" ; 
      
      destruct c ; unpack ; subst ; inversion H3 ; subst ;
        wp_bind (value #p) ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;
            
            wp_bind (splay_compare #(V p') #(V p)) ;
            iApply (splay_compare_specification_gt) ; auto ;
              iModIntro ; iIntros ;

                wp_pures ;
                
                wp_bind (right_child #p) ;
                iApply (right_child_specification with "[Hp]") ; auto ;
                  iModIntro ; iIntros "Hp" ;
                  [ |exfalso;eauto | | exfalso;eauto] ;

                    wp_pures.
    + assert (p' = l0). stlink_tac. subst l0.
      assert (p' \in D) ; stdomain_tac ;
        apply H0 in H10 ;
        
        wp_pures ; destruct (M !! p') eqn:E1 ; try contradiction ;
          iDestruct ("M" with "Hp") as "M" ;
          
          iPoseProof (mapsto_M_acc_same M p' c E1 with "M") as "M" ;
          iDestruct "M" as (v') "[% [Hp M]]".
      
      destruct c ; unpack ; subst ; inversion H11 ; subst ;
        
        wp_bind (value #p') ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;

              iDestruct ("M" with "Hp") as "M" ;
              
              wp_bind (splay_compare #(V p') #(V p')) ;
              iApply (splay_compare_specification_eq) ; auto ;
                iModIntro ; iIntros ; wp_pures ;
                  [ | | exfalso;eauto | exfalso; eauto ].
    - assert (y = l0). stlink_tac. subst.
      iPoseProof
        (rotate_right_BB_st' D V W F M pp p l p' l0 l1 (V p) (V p') with "[R M]")
        as "HF" ; auto.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros "[HPP [% [% M]]]". wp_seq.
      iApply "H" ; iFrame.  auto.
    - assert (y = l0). stlink_tac. subst.
      iPoseProof
        (rotate_right_BL_st' D V W F M pp p l p' l0 (V p) (V p') with "[R M]")
        as "HF" ; auto.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros "[HPP [% [% M]]]". wp_seq.
      iApply "H" ; iFrame. iSplit ; iPureIntro ; auto.
    + assert (p' = l). stlink_tac. subst l.
      assert (p' \in D) ; stdomain_tac ;
        apply H0 in H10 ;
        
        wp_pures ; destruct (M !! p') eqn:E1 ; try contradiction ;
          iDestruct ("M" with "Hp") as "M" ;
          
          iPoseProof (mapsto_M_acc_same M p' c E1 with "M") as "M" ;
          iDestruct "M" as (v') "[% [Hp M]]".
      
      destruct c ; unpack ; subst ; inversion H11 ; subst ;
        
        wp_bind (value #p') ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;

              iDestruct ("M" with "Hp") as "M" ;
              
              wp_bind (splay_compare #(V p') #(V p')) ;
              iApply (splay_compare_specification_eq) ; auto ;
                iModIntro ; iIntros ; wp_pures ;
                  [ | | exfalso;eauto | exfalso; eauto ].
    - iPoseProof
        (rotate_right_RB_st' D V W F M pp p p' l l0 (V p) (V p') with "[R M]")
        as "HF" ; auto.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros "[HPP [% [% M]]]". wp_seq.
      assert (l = y). stlink_tac. subst.
      iApply "H" ; iFrame. iSplit ; iPureIntro ; auto. 
    - assert (y = l). stlink_tac. subst.
      iPoseProof
        (rotate_right_RL_st' D V W F M pp p p' l (V p) (V p') with "[R M]")
        as "HF" ; auto.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros "[HPP [% [% M]]]". wp_seq.
      iApply "H" ; iFrame. iSplit ; iPureIntro ; auto.
  Qed.

  Lemma splay_root_rotate_right_gc_gt_ne_st F (pp p p' y : loc) (z : Z) (n : nat) :
    Inv p D F V W ->
    Mem D F V M ->
    V p < z -> 
    F p p' RIGHT ->
    (V p' < z)%Z ∧ ¬ (exists t, F p' t RIGHT) ->
    F p' y LEFT ->
    let F' := (update_edge F p' y p LEFT ) in
    let F'' := (update_edge F' p p' y RIGHT) in
    {{{ pp ↦ #p ∗ mapsto_M M }}}
      splay_tree_while_loop #pp #z
      {{{ M', RET #() ; pp ↦ #p' ∗ ⌜Inv p' D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros.
    iIntros "[R M] H".
    inversion H. subst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].

    apply H0 in rootisindomain.
    destruct (M !! p) eqn:E ; try contradiction.

    unfold splay_tree_while_loop. wp_lam.
    wp_load. wp_let.

    iPoseProof (mapsto_M_acc_same M p c E with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
      
      destruct c ; unpack ; subst ; inversion H5 ; subst ;
        wp_bind (value #p) ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;
            
            wp_bind (splay_compare #z #(V p)) ;
            iApply (splay_compare_specification_gt) ; auto ;
              iModIntro ; iIntros ;

                wp_pures ;
                
                wp_bind (right_child #p) ;
                iApply (right_child_specification with "[Hp]") ; auto ;
                  iModIntro ; iIntros "Hp" ;
                  [ |exfalso;eauto | | exfalso;eauto] ;

                    wp_pures.
    + assert (p' = l0). stlink_tac. subst l0.
      assert (p' \in D) ; stdomain_tac ;
        apply H0 in H12 ;
        
        wp_pures ; destruct (M !! p') eqn:E1 ; try contradiction ;
          iDestruct ("M" with "Hp") as "M" ;
          
          iPoseProof (mapsto_M_acc_same M p' c E1 with "M") as "M" ;
          iDestruct "M" as (v') "[% [Hp M]]".
      
      destruct c eqn:Ec ; unpack ; subst ; inversion H13 ; subst ;
        
        wp_bind (value #p') ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;

              
              wp_bind (splay_compare #z #(V p')) ;
              (iApply (splay_compare_specification_gt) ;
                [iPureIntro; rewrite gt_zarith ; lia|]) ;
                iModIntro ; iIntros ; wp_pures ;
                  [ exfalso;eauto | | exfalso; eauto | exfalso; eauto ] ;
      
      
                wp_bind (right_child #p') ;
                iApply (right_child_specification with "[Hp]") ; auto ;
                  iModIntro ; iIntros "Hp" ;
                    
              iDestruct ("M" with "Hp") as "M" ; wp_pures.                    
    - assert (y = l0). stlink_tac. subst.
      iPoseProof
        (rotate_right_BL_st' D V W F M pp p l p' l0 (V p) (V p') with "[R M]")
        as "HF" ; auto.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros "[HPP [% [% M]]]". wp_seq.
      iApply "H" ; iFrame. iSplit ; iPureIntro ; auto.
    + assert (p' = l). stlink_tac. subst l.
      assert (p' \in D) ; stdomain_tac ;
        apply H0 in H12 ;
        
        wp_pures ; destruct (M !! p') eqn:E1 ; try contradiction ;
          iDestruct ("M" with "Hp") as "M" ;
          
          iPoseProof (mapsto_M_acc_same M p' c E1 with "M") as "M" ;
          iDestruct "M" as (v') "[% [Hp M]]".
      
      destruct c eqn:Ec ; unpack ; subst ; inversion H13 ; subst ;
        
        wp_bind (value #p') ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;

              
              wp_bind (splay_compare #z #(V p')) ;
              (iApply (splay_compare_specification_gt) ;
                [iPureIntro; rewrite gt_zarith ; lia|]) ;
                iModIntro ; iIntros ; wp_pures ;
                  [ exfalso;eauto | | exfalso; eauto | exfalso; eauto ] ;
      
      
                wp_bind (right_child #p') ;
                iApply (right_child_specification with "[Hp]") ; auto ;
                  iModIntro ; iIntros "Hp" ;
                    
              iDestruct ("M" with "Hp") as "M" ; wp_pures.                    
    - assert (y = l). stlink_tac. subst.
      iPoseProof
        (rotate_right_RL_st' D V W F M pp p p' l (V p) (V p') with "[R M]")
        as "HF" ; auto.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros "[HPP [% [% M]]]". wp_seq.
      iApply "H" ; iFrame. iSplit ; iPureIntro ; auto.
  Qed.
  
  Lemma splay_root_rotate_right_gc_st F (pp p p' y : loc) (z : Z) (n : nat) :
    Inv p D F V W ->
    Mem D F V M ->
    V p < z -> 
    F p p' RIGHT ->
    (z = V p') \/ (V p' < z)%Z ∧ ¬ (exists t, F p' t RIGHT) ->
    F p' y LEFT ->
    let F' := (update_edge F p' y p LEFT ) in
    let F'' := (update_edge F' p p' y RIGHT) in
    {{{ pp ↦ #p ∗ mapsto_M M }}}
      splay_tree_while_loop #pp #z
      {{{ M', RET #() ; pp ↦ #p' ∗ ⌜Inv p' D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros.
    destruct H3.
    - apply splay_root_rotate_right_gc_eq_st ; auto.
    - apply splay_root_rotate_right_gc_gt_ne_st ; auto.
  Qed.
    
End SplaySubCasesRightGCRotation.
