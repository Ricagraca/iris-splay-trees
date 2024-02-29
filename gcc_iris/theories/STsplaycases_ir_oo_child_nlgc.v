From ST Require Import Code STorientation 
     STpredicate STpath STedgeset STedgesetrotateroot
     STrotaterightcasesroot STrotateleftcasesroot
     STlink STmemory STproof STdomain STpathcount
     STrotaterightcaseschild STrotateleftcaseschild.

From iris_time.heap_lang Require Import lib.assert.
From iris_time.heap_lang Require Export lang.
From iris_time.heap_lang Require Import proofmode.
From iris_time.heap_lang Require Import notation.
From iris_time Require Import Combined.

From iris.bi Require Import big_op.
From iris_time.heap_lang Require Import proofmode.
From iris_time Require Import Combined.

From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual
     LibInt.

Section SplaySubCasesRightRightRotation.

  Context `{!tctrHeapG Σ} (nmax : nat).

  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)
  
  Lemma splay_root_rotate_right_right_ngc_st F FF (pp p p' y x : loc) (z : Z) :
    Inv p D F V W ->
    Mem D F V M ->
    
    ((V p) < z)%Z -> 
    F p x RIGHT ->
    ((V x) < z)%Z ->
    F x y RIGHT -> 
    ¬(exists t, F y t LEFT) ->

    (* rotation on children *)
    let D' := (descendants F x) in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let FC' := (remove_edge_that_are_in_D F D') in
    let F'' := (remove_edge F' x y) in
    let F''' := (add_edge F'' y x LEFT) in

    (*Edgeset after first rotation*)
    let Fafr := (add_edge (union_edge F''' FC') p y RIGHT) in 

    (* rotation on root *)
    let F1 := (update_edge Fafr p y x RIGHT) in 
    let F2 := (update_edge F1 y x p LEFT) in
    
    ({{{ pp ↦ #y ∗ (∃ M', mapsto_M M' ∗ ⌜Mem D F2 V M'⌝ ∗ ⌜Inv y D F2 V W⌝ ) }}} 
       splay_tree_while_loop #pp #z
    {{{ M', RET #() ; pp ↦ #p' ∗ ⌜Inv p' D FF V W⌝ ∗ ⌜Mem D FF V M'⌝ ∗ mapsto_M M'}}}) -∗
    
    {{{ pp ↦ #p ∗ mapsto_M M }}} 
      splay_tree_while_loop #pp #z
    {{{ M', RET #() ; pp ↦ #p' ∗ ⌜Inv p' D FF V W⌝ ∗ ⌜Mem D FF V M'⌝ ∗ mapsto_M M'}}}.
  Proof.    
    intros. iIntros "#Hind". iModIntro.
    iIntros (Φ) "[R M] H".
    inversion H. subst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].

    apply H0 in rootisindomain.
    destruct (M !! p) eqn:E ; try contradiction.

    unfold splay_tree_while_loop. wp_lam.
    wp_load. wp_let.

    iPoseProof (mapsto_M_acc_same M p c E with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
      
    destruct c ; unpack ; subst ; inversion H6 ; subst ;
      [ |exfalso;eauto | | exfalso;eauto] ;
      
        wp_bind (value #p) ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;
            
            wp_bind (splay_compare #z #(V p)) ;
      (iApply (splay_compare_specification_gt) ; [rewrite gt_zarith ;iPureIntro; lia|]) ;
                                                  
              iModIntro ; iIntros ;

                wp_pures ;
                
                wp_bind (right_child #p) ;
                iApply (right_child_specification with "[Hp]") ; auto ;
                  iModIntro ; iIntros "Hp" ;

                    wp_pures ; [|rename l into l0] ;
                      (assert (l0 = x) ; stlink_tac ; subst) ;
    iDestruct ("M" with "Hp") as "M" ;

    (assert (x \in D) ; stdomain_tac ; apply H0 in H12) ;
    destruct (M !! x) eqn:E1 ; try contradiction ;
    
    iPoseProof (mapsto_M_acc_same M x c E1 with "M") as "M" ;
    iDestruct "M" as (v') "[% [Hp M]]" ;

    (destruct c ; unpack ; subst ; inversion H13 ; subst ;
     [ |exfalso;eauto | | exfalso;eauto]) ;

      wp_bind (value #x) ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;            
    wp_bind (splay_compare #z #(V x)) ;
      (iApply (splay_compare_specification_gt) ; [rewrite gt_zarith ;iPureIntro; lia|]) ;
      iModIntro ; iIntros ;
        wp_pures ;
    wp_bind (right_child #x) ;
      iApply (right_child_specification with "[Hp]") ; auto ;
        iModIntro ; iIntros "Hp" ;
          wp_pures ;
            [|rename l0 into l1|rename l0 into l1|rename l into l1] ;
            (assert (l1 = y) ; stlink_tac ; subst) ;
            (assert (y \in D); stdomain_tac ;
             apply H0 in H16) ;
            iDestruct ("M" with "Hp") as "M" ; wp_bind(Rec BAnon "tmp" _ (Alloc (LitV x))).
    + destruct (M !! y) eqn:E2 ; try contradiction.
      destruct c ; unpack ; subst ; [exfalso;eauto|exfalso;eauto| | ].
      - iPoseProof (rotate_right_child_BBR_r_st D V W F M pp p l x l0 y l1
                                                (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeB (V p) l y]> (<[x:=NodeL (V x) l0]> (<[y:=NodeB (V y) x l1]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeB (V p) l y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeB (V y) x l1)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_right_BB_st' D V W Fafr Mp' pp p l y x l1 (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_right #pp #p (right_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeB (V p) l y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (right_child #p) ;
          iApply (right_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists ((<[p:=NodeB (V p) l x]>
                  (<[y:=NodeB (V y) p l1]>
                   (<[p:=NodeB (V p) l y]> (<[x:=NodeL (V x) l0]> (<[y:=NodeB (V y) x l1]> M)))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1. apply M_update_comm with ( (update_edge
             (update_edge
                (add_edge
                   (union_edge
                      (add_edge
                         (remove_edge (remove_edge_that_are_not_in_D F (descendants F x)) x y) y
                         x LEFT) (remove_edge_that_are_in_D F (descendants F x))) p y RIGHT) y x
                p LEFT) p y x RIGHT)) ; auto. intros. apply update_edge_comm. stlink_tac.
      - iPoseProof (rotate_right_child_BBN_r_st D V W F M pp p l x l0 y 
                                                (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeB (V p) l y]> (<[x:=NodeL (V x) l0]> (<[y:=NodeL (V y) x]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeB (V p) l y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeL (V y) x)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_right_BL_st' D V W Fafr Mp' pp p l y x (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_right #pp #p (right_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeB (V p) l y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (right_child #p) ;
          iApply (right_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeB (V p) l x]>
                 (<[y:=NodeL (V y) p]>
                  (<[p:=NodeB (V p) l y]> (<[x:=NodeL (V x) l0]> (<[y:=NodeL (V y) x]> M))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1. apply M_update_comm with ( (update_edge
             (update_edge
                (add_edge
                   (union_edge
                      (add_edge
                         (remove_edge (remove_edge_that_are_not_in_D F (descendants F x)) x y) y
                         x LEFT) (remove_edge_that_are_in_D F (descendants F x))) p y RIGHT) y x
                p LEFT) p y x RIGHT)) ; auto. intros. apply update_edge_comm. stlink_tac.
    + destruct (M !! y) eqn:E2 ; try contradiction.
      destruct c ; unpack ; subst ; [exfalso;eauto|exfalso;eauto| | ].
      - iPoseProof (rotate_right_child_BRR_r_st D V W F M pp p l x y l0
                                                (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeB (V p) l y]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) x l0]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeB (V p) l y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeB (V y) x l0)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_right_BB_st' D V W Fafr Mp' pp p l y x l0 (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_right #pp #p (right_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeB (V p) l y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (right_child #p) ;
          iApply (right_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeB (V p) l x]>
                 (<[y:=NodeB (V y) p l0]>
                  (<[p:=NodeB (V p) l y]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) x l0]> M))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1. apply M_update_comm with ( (update_edge
             (update_edge
                (add_edge
                   (union_edge
                      (add_edge
                         (remove_edge (remove_edge_that_are_not_in_D F (descendants F x)) x y) y
                         x LEFT) (remove_edge_that_are_in_D F (descendants F x))) p y RIGHT) y x
                p LEFT) p y x RIGHT)) ; auto. intros. apply update_edge_comm. stlink_tac.
      - iPoseProof (rotate_right_child_BRN_r_st D V W F M pp p l x y 
                                                (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeB (V p) l y]> (<[x:=NodeN (V x)]> (<[y:=NodeL (V y) x]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeB (V p) l y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeL (V y) x)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_right_BL_st' D V W Fafr Mp' pp p l y x (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_right #pp #p (right_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeB (V p) l y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (right_child #p) ;
          iApply (right_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeB (V p) l x]>
                 (<[y:=NodeL (V y) p]>
                  (<[p:=NodeB (V p) l y]> (<[x:=NodeN (V x)]> (<[y:=NodeL (V y) x]> M))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1. apply M_update_comm with ( (update_edge
             (update_edge
                (add_edge
                   (union_edge
                      (add_edge
                         (remove_edge (remove_edge_that_are_not_in_D F (descendants F x)) x y) y
                         x LEFT) (remove_edge_that_are_in_D F (descendants F x))) p y RIGHT) y x
                p LEFT) p y x RIGHT)) ; auto. intros. apply update_edge_comm. stlink_tac.
    + destruct (M !! y) eqn:E2 ; try contradiction.
      destruct c ; unpack ; subst ; [exfalso;eauto|exfalso;eauto| | ].
      - iPoseProof (rotate_right_child_RBR_r_st D V W F M pp p x l y l0
                                                (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeR (V p) y]> (<[x:=NodeL (V x) l]> (<[y:=NodeB (V y) x l0]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeR (V p) y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeB (V y) x l0)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_right_RB_st' D V W Fafr Mp' pp p y x l0 (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_right #pp #p (right_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeR (V p) y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (right_child #p) ;
          iApply (right_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame. 
        iExists (<[p:=NodeR (V p) x]>
                 (<[y:=NodeB (V y) p l0]>
                  (<[p:=NodeR (V p) y]> (<[x:=NodeL (V x) l]> (<[y:=NodeB (V y) x l0]> M))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1. apply M_update_comm with ( (update_edge
             (update_edge
                (add_edge
                   (union_edge
                      (add_edge
                         (remove_edge (remove_edge_that_are_not_in_D F (descendants F x)) x y) y
                         x LEFT) (remove_edge_that_are_in_D F (descendants F x))) p y RIGHT) y x
                p LEFT) p y x RIGHT)) ; auto. intros. apply update_edge_comm. stlink_tac.
      - iPoseProof (rotate_right_child_RBN_r_st D V W F M pp p x l y
                                                (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeR (V p) y]> (<[x:=NodeL (V x) l]> (<[y:=NodeL (V y) x]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeR (V p) y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeL (V y) x)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_right_RL_st' D V W Fafr Mp' pp p y x (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_right #pp #p (right_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeR (V p) y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (right_child #p) ;
          iApply (right_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame. 
        iExists (<[p:=NodeR (V p) x]>
                 (<[y:=NodeL (V y) p]>
                  (<[p:=NodeR (V p) y]> (<[x:=NodeL (V x) l]> (<[y:=NodeL (V y) x]> M))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1. apply M_update_comm with ( (update_edge
             (update_edge
                (add_edge
                   (union_edge
                      (add_edge
                         (remove_edge (remove_edge_that_are_not_in_D F (descendants F x)) x y) y
                         x LEFT) (remove_edge_that_are_in_D F (descendants F x))) p y RIGHT) y x
                p LEFT) p y x RIGHT)) ; auto. intros. apply update_edge_comm. stlink_tac.
    + destruct (M !! y) eqn:E2 ; try contradiction.
      destruct c ; unpack ; subst ; [exfalso;eauto|exfalso;eauto| | ].
      - iPoseProof (rotate_right_child_RRR_r_st D V W F M pp p x y l
                                                (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeR (V p) y]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) x l]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeR (V p) y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeB (V y) x l)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_right_RB_st' D V W Fafr Mp' pp p y x l (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_right #pp #p (right_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeR (V p) y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (right_child #p) ;
          iApply (right_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame. 
        iExists (<[p:=NodeR (V p) x]>
                 (<[y:=NodeB (V y) p l]>
                  (<[p:=NodeR (V p) y]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) x l]> M))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1. apply M_update_comm with ( (update_edge
             (update_edge
                (add_edge
                   (union_edge
                      (add_edge
                         (remove_edge (remove_edge_that_are_not_in_D F (descendants F x)) x y) y
                         x LEFT) (remove_edge_that_are_in_D F (descendants F x))) p y RIGHT) y x
                p LEFT) p y x RIGHT)) ; auto. intros. apply update_edge_comm. stlink_tac.
      - iPoseProof (rotate_right_child_RRN_r_st D V W F M pp p x y
                                                (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeR (V p) y]> (<[x:=NodeN (V x)]> (<[y:=NodeL (V y) x]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeR (V p) y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeL (V y) x)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_right_RL_st' D V W Fafr Mp' pp p y x (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_right #pp #p (right_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeR (V p) y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (right_child #p) ;
          iApply (right_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame. 
        iExists (<[p:=NodeR (V p) x]>
                 (<[y:=NodeL (V y) p]>
                  (<[p:=NodeR (V p) y]> (<[x:=NodeN (V x)]> (<[y:=NodeL (V y) x]> M))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1. apply M_update_comm with ( (update_edge
             (update_edge
                (add_edge
                   (union_edge
                      (add_edge
                         (remove_edge (remove_edge_that_are_not_in_D F (descendants F x)) x y) y
                         x LEFT) (remove_edge_that_are_in_D F (descendants F x))) p y RIGHT) y x
                p LEFT) p y x RIGHT)) ; auto. intros. apply update_edge_comm. stlink_tac.        
  Qed.
    
End SplaySubCasesRightRightRotation.


Section SplaySubCasesLeftLeftRotation.

  Context `{!tctrHeapG Σ} (nmax : nat).

  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)
  
  Lemma splay_root_rotate_left_left_ngc_st F FF (pp p p' y x : loc) (z : Z) :
    Inv p D F V W ->
    Mem D F V M ->
    
    ((V p) > z)%Z -> 
    F p x LEFT ->
    ((V x) > z)%Z ->
    F x y LEFT -> 
    ¬(exists t, F y t RIGHT) ->

    (* rotation on children *)
    let D' := (descendants F x) in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let FC' := (remove_edge_that_are_in_D F D') in
    let F'' := (remove_edge F' x y) in
    let F''' := (add_edge F'' y x RIGHT) in

    (*Edgeset after first rotation*)
    let Fafr := (add_edge (union_edge F''' FC') p y LEFT) in 

    (* rotation on root *)
    let F1 := (update_edge Fafr p y x LEFT) in 
    let F2 := (update_edge F1 y x p RIGHT) in
    
    ({{{ pp ↦ #y ∗ (∃ M', mapsto_M M' ∗ ⌜Mem D F2 V M'⌝ ∗ ⌜Inv y D F2 V W⌝ ) }}} 
       splay_tree_while_loop #pp #z
    {{{ M', RET #() ; pp ↦ #p' ∗ ⌜Inv p' D FF V W⌝ ∗ ⌜Mem D FF V M'⌝ ∗ mapsto_M M'}}}) -∗
    
    {{{ pp ↦ #p ∗ mapsto_M M }}} 
      splay_tree_while_loop #pp #z
    {{{ M', RET #() ; pp ↦ #p' ∗ ⌜Inv p' D FF V W⌝ ∗ ⌜Mem D FF V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros. iIntros "#Hind". iModIntro.
    iIntros (Φ) "[R M] H".
    inversion H. subst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].

    apply H0 in rootisindomain.
    destruct (M !! p) eqn:E ; try contradiction.

    unfold splay_tree_while_loop. wp_lam.
    wp_load. wp_let.

    iPoseProof (mapsto_M_acc_same M p c E with "M") as "M".
    iDestruct "M" as (v') "[% [Hp M]]".
      
    destruct c ; unpack ; subst ; inversion H6 ; subst ;
      [ | |exfalso;eauto | exfalso;eauto] ;
      
        wp_bind (value #p) ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;
            
            wp_bind (splay_compare #z #(V p)) ;
      (iApply (splay_compare_specification_lt) ; [rewrite lt_zarith ;iPureIntro; lia|]) ;
                                                  
              iModIntro ; iIntros ;

                wp_pures ;
                
                wp_bind (left_child #p) ;
                iApply (left_child_specification with "[Hp]") ; auto ;
                  iModIntro ; iIntros "Hp" ;

                    wp_pures ;
                      (assert (l = x) ; stlink_tac ; subst) ;
    iDestruct ("M" with "Hp") as "M" ;

    (assert (x \in D) ; stdomain_tac ; apply H0 in H12) ;
    destruct (M !! x) eqn:E1 ; try contradiction ;
    
    iPoseProof (mapsto_M_acc_same M x c E1 with "M") as "M" ;
    iDestruct "M" as (v') "[% [Hp M]]" ;

    (destruct c ; unpack ; subst ; inversion H13 ; subst ;
     [ | |exfalso;eauto | exfalso;eauto]) ;

      wp_bind (value #x) ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;            
    wp_bind (splay_compare #z #(V x)) ;
      (iApply (splay_compare_specification_lt) ; [rewrite lt_zarith ;iPureIntro; lia|]) ;
      iModIntro ; iIntros ;
        wp_pures ;
    wp_bind (left_child #x) ;
      iApply (left_child_specification with "[Hp]") ; auto ;
        iModIntro ; iIntros "Hp" ;
          wp_pures ;
            (assert (l = y) ; stlink_tac ; subst) ;
            (assert (y \in D); stdomain_tac ;
             apply H0 in H16) ;
            iDestruct ("M" with "Hp") as "M" ; wp_bind(Rec BAnon "tmp" _ (Alloc (LitV x))).
    + destruct (M !! y) eqn:E2 ; try contradiction.
      destruct c ; unpack ; subst ; [exfalso;eauto| |exfalso;eauto| ].
      - iPoseProof (rotate_left_child_BBL_l_st D V W F M pp p x l0 y l1 l
                                                (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeB (V p) y l0]> (<[x:=NodeR (V x) l1]> (<[y:=NodeB (V y) l x]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeB (V p) y l0)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeB (V y) l x)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_left_BB_st' D V W Fafr Mp' pp p y l0 l x (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_left #pp #p (left_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeB (V p) y l0)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (left_child #p) ;
          iApply (left_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeB (V p) x l0]>
                 (<[y:=NodeB (V y) l p]>
                  (<[p:=NodeB (V p) y l0]> (<[x:=NodeR (V x) l1]> (<[y:=NodeB (V y) l x]> M))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1.
        apply M_update_comm with (update_edge (update_edge Fafr y x p RIGHT) p y x LEFT). intros.
        apply update_edge_comm. stlink_tac. auto.
      - iPoseProof (rotate_left_child_BBN_l_st D V W F M pp p x l0 y l1
                                                (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeB (V p) y l0]> (<[x:=NodeR (V x) l1]> (<[y:=NodeR (V y) x]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeB (V p) y l0)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeR (V y) x)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_left_BR_st' D V W Fafr Mp' pp p y l0 x (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_left #pp #p (left_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeB (V p) y l0)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (left_child #p) ;
          iApply (left_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeB (V p) x l0]>
                 (<[y:=NodeR (V y) p]>
                  (<[p:=NodeB (V p) y l0]> (<[x:=NodeR (V x) l1]> (<[y:=NodeR (V y) x]> M))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1.
        apply M_update_comm with (update_edge (update_edge Fafr y x p RIGHT) p y x LEFT). intros.
        apply update_edge_comm. stlink_tac. auto.
    + destruct (M !! y) eqn:E2 ; try contradiction.
      destruct c ; unpack ; subst ; [exfalso;eauto| |exfalso;eauto| ].
      - iPoseProof (rotate_left_child_BLL_l_st D V W F M pp p x l0 y l
                                                (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember  (<[p:=NodeB (V p) y l0]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) l x]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeB (V p) y l0)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeB (V y) l x)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_left_BB_st' D V W Fafr Mp' pp p y l0 l x (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_left #pp #p (left_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeB (V p) y l0)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (left_child #p) ;
          iApply (left_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeB (V p) x l0]>
                 (<[y:=NodeB (V y) l p]>
                  (<[p:=NodeB (V p) y l0]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) l x]> M))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1.
        apply M_update_comm with (update_edge (update_edge Fafr y x p RIGHT) p y x LEFT). intros.
        apply update_edge_comm. stlink_tac. auto.
      - iPoseProof (rotate_left_child_BLN_l_st D V W F M pp p x l0 y
                                                (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeB (V p) y l0]> (<[x:=NodeN (V x)]> (<[y:=NodeR (V y) x]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeB (V p) y l0)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeR (V y) x)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_left_BR_st' D V W Fafr Mp' pp p y l0 x (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_left #pp #p (left_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeB (V p) y l0)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (left_child #p) ;
          iApply (left_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeB (V p) x l0]>
                 (<[y:=NodeR (V y) p]>
                  (<[p:=NodeB (V p) y l0]> (<[x:=NodeN (V x)]> (<[y:=NodeR (V y) x]> M))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1.
        apply M_update_comm with (update_edge (update_edge Fafr y x p RIGHT) p y x LEFT). intros.
        apply update_edge_comm. stlink_tac. auto.
    + destruct (M !! y) eqn:E2 ; try contradiction.
      destruct c ; unpack ; subst ; [exfalso;eauto| |exfalso;eauto| ].
      - iPoseProof (rotate_left_child_LBL_l_st D V W F M pp p x y l0 l
                                               (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeL (V p) y]> (<[x:=NodeR (V x) l0]> (<[y:=NodeB (V y) l x]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeL (V p) y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeB (V y) l x)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_left_LB_st' D V W Fafr Mp' pp p y l x (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_left #pp #p (left_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeL (V p) y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (left_child #p) ;
          iApply (left_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeL (V p) x]>
                 (<[y:=NodeB (V y) l p]>
                  (<[p:=NodeL (V p) y]> (<[x:=NodeR (V x) l0]> (<[y:=NodeB (V y) l x]> M))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1.
        apply M_update_comm with (update_edge (update_edge Fafr y x p RIGHT) p y x LEFT). intros.
        apply update_edge_comm. stlink_tac. auto.
      - iPoseProof (rotate_left_child_LBN_l_st D V W F M pp p x y l0
                                               (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeL (V p) y]> (<[x:=NodeR (V x) l0]> (<[y:=NodeR (V y) x]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeL (V p) y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeR (V y) x)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_left_LR_st' D V W Fafr Mp' pp p y x (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_left #pp #p (left_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeL (V p) y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (left_child #p) ;
          iApply (left_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeL (V p) x]>
                 (<[y:=NodeR (V y) p]>
                  (<[p:=NodeL (V p) y]> (<[x:=NodeR (V x) l0]> (<[y:=NodeR (V y) x]> M))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1.
        apply M_update_comm with (update_edge (update_edge Fafr y x p RIGHT) p y x LEFT). intros.
        apply update_edge_comm. stlink_tac. auto.
    + destruct (M !! y) eqn:E2 ; try contradiction.
      destruct c ; unpack ; subst ; [exfalso;eauto| |exfalso;eauto| ].
      - iPoseProof (rotate_left_child_LLL_l_st D V W F M pp p x y l
                                               (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeL (V p) y]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) l x]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeL (V p) y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeB (V y) l x)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_left_LB_st' D V W Fafr Mp' pp p y l x (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_left #pp #p (left_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeL (V p) y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (left_child #p) ;
          iApply (left_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeL (V p) x]>
                 (<[y:=NodeB (V y) l p]>
                  (<[p:=NodeL (V p) y]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) l x]> M))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1.
        apply M_update_comm with (update_edge (update_edge Fafr y x p RIGHT) p y x LEFT). intros.
        apply update_edge_comm. stlink_tac. auto.
      - iPoseProof (rotate_left_child_LLN_l_st D V W F M pp p x y
                                               (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeL (V p) y]> (<[x:=NodeN (V x)]> (<[y:=NodeR (V y) x]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeL (V p) y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeR (V y) x)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_left_LR_st' D V W Fafr Mp' pp p y x (V p) (V y)) as "Hf" ; auto.

        wp_bind (rotate_left #pp #p (left_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeL (V p) y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H22 ; subst.
        wp_bind (left_child #p) ;
          iApply (left_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".        
        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeL (V p) x]>
                 (<[y:=NodeR (V y) p]>
                  (<[p:=NodeL (V p) y]> (<[x:=NodeN (V x)]> (<[y:=NodeR (V y) x]> M))))). iFrame.
        iSplit ; iPureIntro ; apply update_comm_inv in H23 ; stlink_tac ; auto.
        unfold F2, F1.
        apply M_update_comm with (update_edge (update_edge Fafr y x p RIGHT) p y x LEFT). intros.
        apply update_edge_comm. stlink_tac. auto.
  Qed.

End SplaySubCasesLeftLeftRotation.

Section SplaySubCasesOORotation.

  Context `{!tctrHeapG Σ} (nmax : nat).

  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable M : gmap elem content.  (* data stored in nodes *)
  
  Lemma splay_root_rotate_o_o_ngc_st F FF (pp p p' y x : loc) (z : Z) o :
    Inv p D F V W ->
    Mem D F V M ->

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
    
    ({{{ pp ↦ #y ∗ (∃ M', mapsto_M M' ∗ ⌜Mem D F2 V M'⌝ ∗ ⌜Inv y D F2 V W⌝ ) }}} 
       splay_tree_while_loop #pp #z
    {{{ M', RET #() ; pp ↦ #p' ∗ ⌜Inv p' D FF V W⌝ ∗ ⌜Mem D FF V M'⌝ ∗ mapsto_M M'}}}) -∗
    
    {{{ pp ↦ #p ∗ mapsto_M M }}} 
      splay_tree_while_loop #pp #z
    {{{ M', RET #() ; pp ↦ #p' ∗ ⌜Inv p' D FF V W⌝ ∗ ⌜Mem D FF V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    destruct o.
    + apply splay_root_rotate_left_left_ngc_st ; auto.
    + apply splay_root_rotate_right_right_ngc_st ; auto.
  Qed.
    
End SplaySubCasesOORotation.

