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

Section SplaySubCasesRightRotation.

  Context `{!tctrHeapG Σ} (nmax : nat).

  Variable v : val.
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)

  Lemma splay_root_rotate_right_eq_st F (pp p p' : loc) (z : Z) (n : nat) :
    Inv p D F V W ->
    Mem D F V M ->
    V p < z -> 
    F p p' RIGHT ->
    z = V p' -> 
    ¬ (exists t, F p' t LEFT) ->
    let F' := (remove_edge F p p') in
    let F'' := (add_edge F' p' p LEFT) in
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
      [ |exfalso;eauto | | exfalso;eauto] ; wp_pures.
    + assert (l0 \in D) ; stdomain_tac ;
        apply H0 in H10 ;
        
        wp_pures ; destruct (M !! l0) eqn:E1 ; try contradiction ;
          iDestruct ("M" with "Hp") as "M" ;
          
          iPoseProof (mapsto_M_acc_same M l0 c E1 with "M") as "M" ;
          iDestruct "M" as (v') "[% [Hp M]]".
      
      destruct c ; unpack ; subst ; inversion H11 ; subst ;
        
        wp_bind (value #l0) ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;

            assert (l0 = p') ; stlink_tac ; subst ;
              iDestruct ("M" with "Hp") as "M" ;
              
              wp_bind (splay_compare #(V p') #(V p')) ;
              iApply (splay_compare_specification_eq) ; auto ;
                iModIntro ; iIntros ; wp_pures ;
      [exfalso;eauto|exfalso; eauto| |].
    - iPoseProof
        (rotate_right_BR_st' D V W F M pp p l p' l1 (V p) (V p') with "[R M]") as "HF" ; auto.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros "[HPP [%  M]]". wp_seq.
      iApply "H" ; iFrame. iPureIntro. auto.
    - iPoseProof
        (rotate_right_BN_st' D V W F M pp p l p' (V p) (V p') with "[R M]") as "HF" ; auto.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros "[HPP [%  M]]". wp_seq.
      iApply "H" ; iFrame. iPureIntro. auto.
    + assert (l \in D) ; stdomain_tac ;
        apply H0 in H10 ;
        
        wp_pures ; destruct (M !! l) eqn:E1 ; try contradiction ;
          iDestruct ("M" with "Hp") as "M" ;
          
          iPoseProof (mapsto_M_acc_same M l c E1 with "M") as "M" ;
          iDestruct "M" as (v') "[% [Hp M]]".
      
      destruct c ; unpack ; subst ; inversion H11 ; subst ;
        
        wp_bind (value #l) ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;

            assert (l = p') ; stlink_tac ; subst ;
              iDestruct ("M" with "Hp") as "M" ;
              
              wp_bind (splay_compare #(V p') #(V p')) ;
              iApply (splay_compare_specification_eq) ; auto ;
                iModIntro ; iIntros ; wp_pures ;
      [exfalso;eauto|exfalso; eauto| |].
    - iPoseProof
        (rotate_right_RR_st' D V W F M pp p p' l0 (V p) (V p') with "[R M]") as "HF" ; auto.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros "[HPP [%  M]]". wp_seq.
      iApply "H" ; iFrame. iPureIntro. auto.
    - iPoseProof
        (rotate_right_RN_st' D V W F M pp p p' (V p) (V p') with "[R M]") as "HF" ; auto.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros "[HPP [%  M]]". wp_seq.
      iApply "H" ; iFrame. iPureIntro. auto.
  Qed.

  Lemma splay_root_rotate_right_lt_st F (pp p p' x y : loc) (z : Z) (n : nat) :
    Inv p D F V W ->
    Mem D F V M ->
    V p < z -> 
    F p p' RIGHT ->
    z < V p' -> 
    ¬ (exists t, F p' t LEFT) ->
    let F' := (remove_edge F p p') in
    let F'' := (add_edge F' p' p LEFT) in
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
                iModIntro ; iIntros "Hp" ; [ |exfalso;eauto | | exfalso;eauto] ;
                  
                  wp_pures.
    + assert (l0 \in D) ; stdomain_tac ;
        apply H0 in H11 ;
        
        wp_pures ; destruct (M !! l0) eqn:E1 ; try contradiction ;
          iDestruct ("M" with "Hp") as "M" ;
          
          iPoseProof (mapsto_M_acc_same M l0 c E1 with "M") as "M" ;
          iDestruct "M" as (v') "[% [Hp M]]".
          
          destruct c eqn:Ec ; pose (Ec) as Ec' ; unpack ; subst ;inversion H12 ; subst ;
            
            wp_bind (value #l0) ;
            iApply (value_specification with "[Hp]") ; auto ;
              iModIntro ; iIntros "Hp" ;

                assert (l0 = p') ; stlink_tac ; subst ;
                  iDestruct ("M" with "Hp") as "M" ;
                  
                  wp_bind (splay_compare #z #(V p')) ;
                  iApply (splay_compare_specification_lt) ; auto ;
                    iModIntro ; iIntros ; wp_pures ;
                      [exfalso;eauto |exfalso; eauto| | ] ;
                      
                      (iPoseProof (mapsto_M_acc_same M with "M") as "M" ; [apply E1|]) ;
                      iDestruct "M" as (v') "[% [Hp M]]" ; inversion H15 ; subst ;
                        
                        wp_bind (left_child #p') ;
                        iApply (left_child_specification with "[Hp]") ; auto ;
                          iModIntro ; iIntros "Hp" ; 
                            iDestruct ("M" with "Hp") as "M" ; wp_pures.
    - iPoseProof
        (rotate_right_BR_st' D V W F M pp p l p' l1 (V p) (V p') with "[R M]") as "HF" ; auto.
      iFrame.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros "[HPP [% M]]". unpack. wp_seq.
      iApply "H" ; iFrame. auto.
    - iPoseProof
        (rotate_right_BN_st' D V W F M pp p l p' (V p) (V p') with "[R M]") as "HF" ; auto.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros. wp_seq.
      iApply "H" ; iFrame.
    + assert (l \in D) ; stdomain_tac ;
        apply H0 in H11 ;
        
        wp_pures ; destruct (M !! l) eqn:E1 ; try contradiction ;
          iDestruct ("M" with "Hp") as "M" ;
          
          iPoseProof (mapsto_M_acc_same M l c E1 with "M") as "M" ;
          iDestruct "M" as (v') "[% [Hp M]]".
          
          destruct c eqn:Ec ; pose (Ec) as Ec' ; unpack ; subst ;inversion H12 ; subst ;
            
            wp_bind (value #l) ;
            iApply (value_specification with "[Hp]") ; auto ;
              iModIntro ; iIntros "Hp" ;

                assert (l = p') ; stlink_tac ; subst ;
                  iDestruct ("M" with "Hp") as "M" ;
                  
                  wp_bind (splay_compare #z #(V p')) ;
                  iApply (splay_compare_specification_lt) ; auto ;
                    iModIntro ; iIntros ; wp_pures ;
                      [exfalso;eauto |exfalso; eauto| | ] ;
                      
                      (iPoseProof (mapsto_M_acc_same M with "M") as "M" ; [apply E1|]) ;
                      iDestruct "M" as (v') "[% [Hp M]]" ; inversion H15 ; subst ;
                        
                        wp_bind (left_child #p') ;
                        iApply (left_child_specification with "[Hp]") ; auto ;
                          iModIntro ; iIntros "Hp" ; 
                            iDestruct ("M" with "Hp") as "M" ; wp_pures.
    - iPoseProof
        (rotate_right_RR_st' D V W F M pp p p' l0 (V p) (V p') with "[R M]") as "HF" ; auto.
      iFrame.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros "[HPP [% M]]". unpack. wp_seq.
      iApply "H" ; iFrame. auto.
    - iPoseProof
        (rotate_right_RN_st' D V W F M pp p p' (V p) (V p') with "[R M]") as "HF" ; auto.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros. wp_seq.
      iApply "H" ; iFrame.
  Qed.

  Lemma splay_root_rotate_right_gt_ne_st F (pp p p' x y : loc) (z : Z) (n : nat) :
    Inv p D F V W ->
    Mem D F V M ->
    V p < z -> 
    F p p' RIGHT ->
    (V p' < z)%Z ∧ ¬ (exists t, F p' t RIGHT) ->
    ¬ (exists t, F p' t LEFT) ->
    let F' := (remove_edge F p p') in
    let F'' := (add_edge F' p' p LEFT) in
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
                iModIntro ; iIntros "Hp" ; [ |exfalso;eauto | | exfalso;eauto] ;
                  
                  wp_pures.
    + assert (l0 = p'). stlink_tac. subst.
      assert (p' \in D) ; stdomain_tac.
        apply H0 in H12.
        
        wp_pures ; destruct (M !! p') eqn:E1 ; try contradiction ;
          iDestruct ("M" with "Hp") as "M" ;
          
          iPoseProof (mapsto_M_acc_same M p' c E1 with "M") as "M" ;
          iDestruct "M" as (v') "[% [Hp M]]".
          
          destruct c eqn:Ec ; pose (Ec) as Ec' ; unpack ; subst ;inversion H13 ; subst ;
            
            wp_bind (value #p') ;
            iApply (value_specification with "[Hp]") ; auto ;
              iModIntro ; iIntros "Hp" ;

                  iDestruct ("M" with "Hp") as "M" ;
                  
                  wp_bind (splay_compare #z #(V p')) ;
                  (iApply (splay_compare_specification_gt) ;
                   [iPureIntro;rewrite gt_zarith;lia|]) ;
                  iModIntro ; iIntros ; wp_pures ;
                      [exfalso;eauto |exfalso; eauto|exfalso;eauto| ].
                      
                      (iPoseProof (mapsto_M_acc_same M with "M") as "M" ; [apply E1|]).
                      iDestruct "M" as (v') "[% [Hp M]]" ; inversion H16 ; subst.
                        
                        wp_bind (right_child #p') ;
                        iApply (right_child_specification with "[Hp]") ; auto.
                          iModIntro ; iIntros "Hp" ; 
                            iDestruct ("M" with "Hp") as "M" ; wp_pures.
    - iPoseProof
        (rotate_right_BN_st' D V W F M pp p l p' (V p) (V p') with "[R M]") as "HF" ; auto.
      iFrame.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros "[HPP [% M]]". unpack. wp_seq.
      iApply "H" ; iFrame. iPureIntro ; auto.
    + assert (l = p'). stlink_tac. subst.
      assert (p' \in D) ; stdomain_tac.
        apply H0 in H12.
        
        wp_pures ; destruct (M !! p') eqn:E1 ; try contradiction ;
          iDestruct ("M" with "Hp") as "M" ;
          
          iPoseProof (mapsto_M_acc_same M p' c E1 with "M") as "M" ;
          iDestruct "M" as (v') "[% [Hp M]]".
          
          destruct c eqn:Ec ; pose (Ec) as Ec' ; unpack ; subst ;inversion H13 ; subst ;
            
            wp_bind (value #p') ;
            iApply (value_specification with "[Hp]") ; auto ;
              iModIntro ; iIntros "Hp" ;

                  iDestruct ("M" with "Hp") as "M" ;
                  
                  wp_bind (splay_compare #z #(V p')) ;
                  (iApply (splay_compare_specification_gt) ;
                   [iPureIntro;rewrite gt_zarith;lia|]) ;
                  iModIntro ; iIntros ; wp_pures ;
                      [exfalso;eauto |exfalso; eauto|exfalso;eauto| ].
                      
                      (iPoseProof (mapsto_M_acc_same M with "M") as "M" ; [apply E1|]).
                      iDestruct "M" as (v') "[% [Hp M]]" ; inversion H16 ; subst.
                        
                        wp_bind (right_child #p') ;
                        iApply (right_child_specification with "[Hp]") ; auto.
                          iModIntro ; iIntros "Hp" ; 
                            iDestruct ("M" with "Hp") as "M" ; wp_pures.
    - iPoseProof
        (rotate_right_RN_st' D V W F M pp p p' (V p) (V p') with "[R M]") as "HF" ; auto.
      iFrame.
      iFrame ; iSplit ; iPureIntro ; auto.
      wp_bind (rotate_right #pp #p #p').
      iApply "HF". iModIntro. iIntros "[HPP [% M]]". unpack. wp_seq.
      iApply "H" ; iFrame. iPureIntro ; auto.
  Qed.

  Lemma splay_root_rotate_right_st F (pp p p' : loc) (z : Z) (n : nat) :
    Inv p D F V W ->
    Mem D F V M ->
    V p < z -> 
    F p p' RIGHT ->
    z = V p' \/ z < V p' \/ (V p' < z)%Z ∧ ¬ (exists t, F p' t RIGHT) ->
    ¬ (exists t, F p' t LEFT) ->
    let F' := (remove_edge F p p') in
    let F'' := (add_edge F' p' p LEFT) in
    {{{ pp ↦ #p ∗ mapsto_M M }}}
      splay_tree_while_loop #pp #z
      {{{ M', RET #() ; pp ↦ #p' ∗ ⌜Inv p' D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros.
    destruct H3 ; [|destruct H3].
    - apply splay_root_rotate_right_eq_st ; auto.
    - apply splay_root_rotate_right_lt_st ; auto.
    - apply splay_root_rotate_right_gt_ne_st ; auto.
  Qed.
  
End SplaySubCasesRightRotation.
