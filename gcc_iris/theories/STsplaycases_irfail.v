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

Section SplaySubCasesFail.
  
  Context `{!tctrHeapG Σ} (nmax : nat).

  Variable v : val.
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)

  Lemma splay_root_fail_left_child_st F (pp p : loc) (k : Z) (n : nat) :
    Inv p D F V W ->
    Mem D F V M ->
    k < V p ->
    ¬ (exists y, F p y LEFT) ->
    {{{ pp ↦ #p ∗ mapsto_M M }}}
      splay_tree_while_loop #pp #k
      {{{ M', RET #() ; pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗ ⌜Mem D F V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros.
    iIntros "[R M] H".
    inversion H.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].

    apply H0 in rootisindomain.
    destruct (M !! p) eqn:E ; try contradiction.

    unfold splay_tree_while_loop. wp_lam.
    wp_load. wp_let.

    iPoseProof (mapsto_M_acc_same M p c E with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".    
    
    destruct c ; unpack ; subst ; simpl in H3 ; inversion H3 ; subst ;
      [exfalso; apply H2 ; eauto|exfalso; apply H2 ; eauto| | ] ;

      wp_bind (value #p) ;
      iApply (value_specification with "[Hp]") ; auto ;
        iModIntro ; iIntros "Hp" ;
          
          wp_bind (splay_compare #k #(V p)) ;
          iApply (splay_compare_specification_lt) ; auto ;
            iModIntro ; iIntros ;
              wp_pures ;
              
              wp_bind (left_child #p) ;
              iApply (left_child_specification with "[Hp]") ; auto ;
                iModIntro ; iIntros "Hp" ;

                  wp_pures ;
                  
                  iApply "H" ; iFrame ;
                    iDestruct ("M" with "Hp") as "M" ;
                    iFrame ; iSplit ; auto.
  Qed.

  Lemma splay_root_fail_right_child_st F (pp p : loc) (k : Z) (n : nat) :
    Inv p D F V W ->
    Mem D F V M ->
    V p < k ->
    ¬ (exists y, F p y RIGHT) ->
    {{{ pp ↦ #p ∗ mapsto_M M }}}
      splay_tree_while_loop #pp #k
      {{{ M', RET #() ; pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗ ⌜Mem D F V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros.
    iIntros "[R M] H".
    inversion H.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].

    apply H0 in rootisindomain.
    destruct (M !! p) eqn:E ; try contradiction.

    unfold splay_tree_while_loop. wp_lam.
    wp_load. wp_let.

    iPoseProof (mapsto_M_acc_same M p c E with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".    
    
    destruct c ; unpack ; subst ; simpl in H3 ; inversion H3 ; subst ;
      [exfalso; apply H2 ; eauto| | exfalso; apply H2 ; eauto| ] ;

      wp_bind (value #p) ;
      iApply (value_specification with "[Hp]") ; auto ;
        iModIntro ; iIntros "Hp" ;
          
          wp_bind (splay_compare #k #(V p)) ;
          iApply (splay_compare_specification_gt) ; auto ;
            iModIntro ; iIntros ;
              wp_pures ;
              
              wp_bind (right_child #p) ;
              iApply (right_child_specification with "[Hp]") ; auto ;
                iModIntro ; iIntros "Hp" ;

                  wp_pures ;
                  
                  iApply "H" ; iFrame ;
                    iDestruct ("M" with "Hp") as "M" ;
                    iFrame ; iSplit ; auto.
    
  Qed.  

  Lemma splay_root_rotate_right_found_child_st F (pp p x y : loc) (z : Z) (n : nat) :
    Inv p D F V W ->
    Mem D F V M ->
    V p < z -> 
    F p x RIGHT ->
    z = V x ->     
    F x y LEFT ->
    let F' :=  (update_edge F x y p LEFT) in
    let F'' :=  (update_edge F' p x y RIGHT) in
    {{{ pp ↦ #p ∗ mapsto_M M }}}
      splay_tree_splay #pp #z
      {{{ M', RET #() ; pp ↦ #x ∗ ⌜Inv x D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros.
    iIntros "[R M] H".
    inversion H. subst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].

    apply H0 in rootisindomain.
    destruct (M !! p) eqn:E ; try contradiction.

    wp_rec. wp_pures. 
    wp_load. wp_pures.
    unfold splay_tree_while_loop. wp_lam.
    wp_load. wp_let.

    iPoseProof (mapsto_M_acc_same M p c E with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]" ; 
      
      destruct c ; unpack ; subst ; inversion H3 ; subst ;
        wp_bind (value #p) ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;
            
            wp_bind (splay_compare #(V x) #(V p)) ;
            iApply (splay_compare_specification_gt) ; auto ;
              iModIntro ; iIntros ;

                wp_pures ;
                
                wp_bind (right_child #p) ;
                iApply (right_child_specification with "[Hp]") ; auto ;
                  iModIntro ; iIntros "Hp" ; [ |exfalso;eauto | |exfalso;eauto] ;

                    wp_pures.
    + assert (l0 \in D) ; stdomain_tac ;
        apply H0 in H10.
      
      wp_pures ; destruct (M !! l0) eqn:E1 ; try contradiction ;
        iDestruct ("M" with "Hp") as "M" ;
        
        iPoseProof (mapsto_M_acc_same M l0 c E1 with "M") as "M" ;
        iDestruct "M" as (v') "[% [Hp M]]".
      
      destruct c ; unpack ; subst ; inversion H11 ; subst ;
        
        wp_bind (value #l0) ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;

            assert (l0 = x) ; stlink_tac ; subst ;
              iDestruct ("M" with "Hp") as "M" ;
              
              wp_bind (splay_compare #(V x) #(V x)) ;
              iApply (splay_compare_specification_eq) ; auto ;
                iModIntro ; iIntros ; wp_pures ; [ | | exfalso;eauto| exfalso;eauto ] ;
                  try (assert (l1 = y) ; stlink_tac ; subst) ;
                  [iPoseProof
                     (rotate_right_BB_st' D V W F M pp p l x y l2 (V p) (V x) with "[R M]") as "HF" ;
                   auto ; iFrame ; [iSplit ; iPureIntro ; auto|]
                  |iPoseProof
                     (rotate_right_BL_st' D V W F M pp p l x y (V p) (V x) with "[R M]") as "HF" ;
                   auto ; iFrame ; [iSplit ; iPureIntro ; auto|]] ;
                  wp_bind (rotate_right #pp #p #x) ;
                  iApply "HF" ; iModIntro ; iIntros "[Hpp [Inv [Mem M]]]" ;

                    wp_pures ; iApply "H" ; iFrame.
    + assert (l \in D) ; stdomain_tac ;
        apply H0 in H10.
      
      wp_pures ; destruct (M !! l) eqn:E1 ; try contradiction ;
        iDestruct ("M" with "Hp") as "M" ;
        
        iPoseProof (mapsto_M_acc_same M l c E1 with "M") as "M" ;
        iDestruct "M" as (v') "[% [Hp M]]".
      
      destruct c ; unpack ; subst ; inversion H11 ; subst ;
        
        wp_bind (value #l) ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;

            assert (l = x) ; stlink_tac ; subst ;
              iDestruct ("M" with "Hp") as "M" ;
              
              wp_bind (splay_compare #(V x) #(V x)) ;
              iApply (splay_compare_specification_eq) ; auto ;
                iModIntro ; iIntros ; wp_pures ; [ | | exfalso;eauto |exfalso;eauto ] ;
                  try (assert (l0 = y) ; stlink_tac ; subst) ;
                  [iPoseProof
                     (rotate_right_RB_st' D V W F M pp p x y l1 (V p) (V x) with "[R M]") as "HF" ;
                   auto ; iFrame ; [iSplit ; iPureIntro ; auto|]
                  |iPoseProof
                     (rotate_right_RL_st' D V W F M pp p x y (V p) (V x) with "[R M]") as "HF" ;
                   auto ; iFrame ; [iSplit ; iPureIntro ; auto|]] ;
                  wp_bind (rotate_right #pp #p #x) ;
                  iApply "HF" ; iModIntro ; iIntros "[Hpp [Inv [Mem M]]]" ;

                    wp_pures ; iApply "H" ; iFrame.
  Qed.
  
End SplaySubCasesFail.
