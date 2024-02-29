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

Section SplaySubCasesRightLeftRotation.

  Context `{!tctrHeapG Σ} (nmax : nat).

  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)
  
  Lemma splay_root_rotate_right_left_gcrighti_st F FF (pp p p' y x t : loc) (z : Z) :
    Inv p D F V W ->
    Mem D F V M ->

    ((V p) < z)%Z ->
    F p x RIGHT ->
    ((V x) > z)%Z ->
    F x y LEFT ->
    ¬ (exists t', F y t' RIGHT) ->
    F y t LEFT ->
    
    (* rotation on children *)
    let D' := (descendants F x) in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let FC' := (remove_edge_that_are_in_D F D') in
    let F'' := (remove_edge F' x y) in
    let F''' := (add_edge F'' y x RIGHT) in

    let Fafr := add_edge (union_edge F''' FC') p y RIGHT in 
    let F1 := update_edge Fafr p y t RIGHT in 
    let F2 := update_edge F1 y t p LEFT in 
                                                    
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
      
      destruct c ; unpack ; subst ; inversion H7 ; subst ;
        [ | exfalso;eauto | | exfalso;eauto] ;
        
        wp_bind (value #p) ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;
            wp_bind (splay_compare #z #(V p)) ;
            (iApply (splay_compare_specification_gt) ; [rewrite gt_zarith; iPureIntro; lia|]) ;
            
            iModIntro ; iIntros ;

              wp_pures ;
                
                wp_bind (right_child #p) ;
                iApply (right_child_specification with "[Hp]") ; auto ;
                  iModIntro ; iIntros "Hp" ; [|rename l into l0] ;
                    wp_pures ; (assert (l0 = x) ; stlink_tac ; subst l0) ;
                      iDestruct ("M" with "Hp") as "M" ;

                      (assert (x \in D) ; stdomain_tac ; apply H0 in H13) ;
                      destruct (M !! x) eqn:E1 ; try contradiction ;
                        
                        iPoseProof (mapsto_M_acc_same M x c E1 with "M") as "M" ;
                        iDestruct "M" as (v') "[% [Hp M]]" ;

                        (destruct c ; unpack ; subst ; inversion H14 ; subst ;
                         [| |exfalso;eauto | exfalso;eauto]) ;

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
                                  [rename l0 into e|rename l0 into e|rename l into e|rename l into e] ;
                                  (assert (e = y) ; stlink_tac ; subst e) ;
                                  (assert (y \in D); stdomain_tac ;
                                   apply H0 in H17) ;
                                  iDestruct ("M" with "Hp") as "M" ; wp_bind(Rec BAnon "tmp" _ (Alloc (LitV x))) ;
                                    (destruct (M !! y) eqn:E2 ; try contradiction) ;
                                    (destruct c ; unpack ; subst ; [exfalso;eauto| |exfalso;eauto |exfalso;eauto]).
      + assert (l0 = t). stlink_tac. subst.
        iPoseProof (rotate_left_child_BBL_r_st D V W F M pp p l x y l1 t
                                               (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeB (V p) l y]> (<[x:=NodeR (V x) l1]> (<[y:=NodeB (V y) t x]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeB (V p) l y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeB (V y) t x)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_right_BB_st' D V W Fafr Mp' pp p l y t x (V p) (V y)) as "Hf" ; auto.
        
        wp_bind (rotate_right #pp #p (right_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeB (V p) l y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H23 ; subst.
        wp_bind (right_child #p) ;
          iApply (right_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".

        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeB (V p) l t]>
                 (<[y:=NodeB (V y) p x]>
                  (<[p:=NodeB (V p) l y]> (<[x:=NodeR (V x) l1]> (<[y:=NodeB (V y) t x]> M))))). iFrame.
        iSplit ; iPureIntro ; auto.
        apply M_update_comm with (update_edge (update_edge Fafr y t p LEFT) p y t RIGHT) ; auto.
        intros. apply update_edge_comm ; stlink_tac.
        apply update_comm_inv in H24 ; stlink_tac ; auto.
      + assert (l0 = t). stlink_tac. subst.
        iPoseProof (rotate_left_child_BLL_r_st D V W F M pp p l x y t
                                               (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeB (V p) l y]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) t x]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeB (V p) l y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeB (V y) t x)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_right_BB_st' D V W Fafr Mp' pp p l y t x (V p) (V y)) as "Hf" ; auto.
        
        wp_bind (rotate_right #pp #p (right_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeB (V p) l y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H23 ; subst.
        wp_bind (right_child #p) ;
          iApply (right_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".

        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeB (V p) l t]>
                 (<[y:=NodeB (V y) p x]>
                  (<[p:=NodeB (V p) l y]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) t x]> M))))). iFrame.
        iSplit ; iPureIntro ; auto.
        apply M_update_comm with (update_edge (update_edge Fafr y t p LEFT) p y t RIGHT) ; auto.
        intros. apply update_edge_comm ; stlink_tac.
        apply update_comm_inv in H24 ; stlink_tac ; auto.
     + assert (l = t). stlink_tac. subst.
       iPoseProof (rotate_left_child_RBL_r_st D V W F M pp p x y l0 t
                                              (V p) (V x) (V y)) as "Hf" ; auto.
       iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
       iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
       remember (<[p:=NodeR (V p) y]> (<[x:=NodeR (V x) l0]> (<[y:=NodeB (V y) t x]> M))) as Mp'.
       assert (Mp' !! p = Some (NodeR (V p) y)).
       { rewrite HeqMp'. rewrite lookup_insert. auto. }
       assert (Mp' !! y = Some (NodeB (V y) t x)).
       { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
       iPoseProof (rotate_right_RB_st' D V W Fafr Mp' pp p y t x (V p) (V y)) as "Hf" ; auto.
       
       wp_bind (rotate_right #pp #p (right_child #p)).
       iPoseProof (mapsto_M_acc_same Mp' p ((NodeR (V p) y)) with "M") as "M" ; auto.
       iDestruct "M" as (v') "[% [Hp M]]". inversion H23 ; subst.
       wp_bind (right_child #p) ;
         iApply (right_child_specification with "[Hp]") ; auto ;
           iModIntro ; iIntros "Hp".

       iDestruct ("M" with "Hp") as "M".
       iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
       iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
       iApply ("Hind" with "[Hpp M]") ; iFrame.
       iExists (<[p:=NodeR (V p) t]>
                (<[y:=NodeB (V y) p x]>
                 (<[p:=NodeR (V p) y]> (<[x:=NodeR (V x) l0]> (<[y:=NodeB (V y) t x]> M))))). iFrame.
       iSplit ; iPureIntro ; auto.
       apply M_update_comm with (update_edge (update_edge Fafr y t p LEFT) p y t RIGHT) ; auto.
       intros. apply update_edge_comm ; stlink_tac.
       apply update_comm_inv in H24 ; stlink_tac ; auto.
     + assert (l = t). stlink_tac. subst.
       iPoseProof (rotate_left_child_RLL_r_st D V W F M pp p x y t
                                              (V p) (V x) (V y)) as "Hf" ; auto.
       iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
       iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
       remember (<[p:=NodeR (V p) y]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) t x]> M))) as Mp'.
       assert (Mp' !! p = Some (NodeR (V p) y)).
       { rewrite HeqMp'. rewrite lookup_insert. auto. }
       assert (Mp' !! y = Some (NodeB (V y) t x)).
       { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
       iPoseProof (rotate_right_RB_st' D V W Fafr Mp' pp p y t x (V p) (V y)) as "Hf" ; auto.
       
       wp_bind (rotate_right #pp #p (right_child #p)).
       iPoseProof (mapsto_M_acc_same Mp' p ((NodeR (V p) y)) with "M") as "M" ; auto.
       iDestruct "M" as (v') "[% [Hp M]]". inversion H23 ; subst.
       wp_bind (right_child #p) ;
         iApply (right_child_specification with "[Hp]") ; auto ;
           iModIntro ; iIntros "Hp".

       iDestruct ("M" with "Hp") as "M".
       iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
       iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
       iApply ("Hind" with "[Hpp M]") ; iFrame.
       iExists (<[p:=NodeR (V p) t]>
                (<[y:=NodeB (V y) p x]>
                 (<[p:=NodeR (V p) y]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) t x]> M))))). iFrame.
       iSplit ; iPureIntro ; auto.
       apply M_update_comm with (update_edge (update_edge Fafr y t p LEFT) p y t RIGHT) ; auto.
       intros. apply update_edge_comm ; stlink_tac.
       apply update_comm_inv in H24 ; stlink_tac ; auto.
  Qed.
  
End SplaySubCasesRightLeftRotation.

Section SplaySubCasesLeftRightRotation.

  Context `{!tctrHeapG Σ} (nmax : nat).

  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)
 
  Lemma splay_root_rotate_left_right_gclefti_st F FF (pp p p' y x t : loc) (z : Z) :
    Inv p D F V W ->
    Mem D F V M ->

    ((V p) > z)%Z ->
    F p x LEFT ->
    ((V x) < z)%Z ->
    F x y RIGHT ->
    ¬ (exists t', F y t' LEFT) ->
    F y t RIGHT ->
    
    (* rotation on children *)
    let D' := (descendants F x) in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let FC' := (remove_edge_that_are_in_D F D') in
    let F'' := (remove_edge F' x y) in
    let F''' := (add_edge F'' y x LEFT) in

    let Fafr := add_edge (union_edge F''' FC') p y LEFT in 
    let F1 := update_edge Fafr p y t LEFT in 
    let F2 := update_edge F1 y t p RIGHT in 
                                                    
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
      
      destruct c ; unpack ; subst ; inversion H7 ; subst ;
        [ | | exfalso;eauto | exfalso;eauto] ;
        
        wp_bind (value #p) ;
        iApply (value_specification with "[Hp]") ; auto ;
          iModIntro ; iIntros "Hp" ;
            wp_bind (splay_compare #z #(V p)) ;
            (iApply (splay_compare_specification_lt) ; [rewrite lt_zarith; iPureIntro; lia|]) ;
            
            iModIntro ; iIntros ;

              wp_pures ;
                
                wp_bind (left_child #p) ;
                iApply (left_child_specification with "[Hp]") ; auto ;
                  iModIntro ; iIntros "Hp" ;
                    wp_pures ; (assert (l = x) ; stlink_tac ; subst l) ;
                      iDestruct ("M" with "Hp") as "M" ;

                      (assert (x \in D) ; stdomain_tac ; apply H0 in H13) ;
                      destruct (M !! x) eqn:E1 ; try contradiction ;
                        
                        iPoseProof (mapsto_M_acc_same M x c E1 with "M") as "M" ;
                        iDestruct "M" as (v') "[% [Hp M]]" ;

                        (destruct c ; unpack ; subst ; inversion H14 ; subst ;
                         [| exfalso;eauto | | exfalso;eauto]) ;

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
                                  [rename l1 into e|rename l into e|rename l0 into e|rename l into e] ;
                                  (assert (e = y) ; stlink_tac ; subst e) ;
                                  (assert (y \in D); stdomain_tac ;
                                   apply H0 in H17) ;
                                  iDestruct ("M" with "Hp") as "M" ; wp_bind(Rec BAnon "tmp" _ (Alloc (LitV x))) ;
                                    (destruct (M !! y) eqn:E2 ; try contradiction) ;
                                    (destruct c ; unpack ; subst ; [exfalso;eauto| exfalso;eauto | |exfalso;eauto]).
      + assert (l1 = t). stlink_tac. subst.
        iPoseProof (rotate_right_child_BBR_l_st D V W F M pp p x l0 l y t
                                               (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeB (V p) y l0]> (<[x:=NodeL (V x) l]> (<[y:=NodeB (V y) x t]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeB (V p) y l0)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeB (V y) x t)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_left_BB_st' D V W Fafr Mp' pp p y l0 x t (V p) (V y)) as "Hf" ; auto.
        
        wp_bind (rotate_left #pp #p (left_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeB (V p) y l0)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H23 ; subst.
        wp_bind (left_child #p) ;
          iApply (left_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".

        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeB (V p) t l0]>
                 (<[y:=NodeB (V y) x p]>
                  (<[p:=NodeB (V p) y l0]> (<[x:=NodeL (V x) l]> (<[y:=NodeB (V y) x t]> M))))). iFrame.
        iSplit ; iPureIntro ; auto.
        apply M_update_comm with (update_edge (update_edge Fafr y t p RIGHT) p y t LEFT) ; auto.
        intros. apply update_edge_comm ; stlink_tac.
        apply update_comm_inv in H24 ; stlink_tac ; auto.
      + assert (l = t). stlink_tac. subst.
        iPoseProof (rotate_right_child_BRR_l_st D V W F M pp p x l0 y t
                                               (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeB (V p) y l0]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) x t]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeB (V p) y l0)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeB (V y) x t)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_left_BB_st' D V W Fafr Mp' pp p y l0 x t (V p) (V y)) as "Hf" ; auto.
        
        wp_bind (rotate_left #pp #p (left_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeB (V p) y l0)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H23 ; subst.
        wp_bind (left_child #p) ;
          iApply (left_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".

        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeB (V p) t l0]>
                 (<[y:=NodeB (V y) x p]>
                  (<[p:=NodeB (V p) y l0]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) x t]> M))))). iFrame.
        iSplit ; iPureIntro ; auto.
        apply M_update_comm with (update_edge (update_edge Fafr y t p RIGHT) p y t LEFT) ; auto.
        intros. apply update_edge_comm ; stlink_tac.
        apply update_comm_inv in H24 ; stlink_tac ; auto.
      + assert (l0 = t). stlink_tac. subst.
        iPoseProof (rotate_right_child_LBR_l_st D V W F M pp p x l y t
                                               (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeL (V p) y]> (<[x:=NodeL (V x) l]> (<[y:=NodeB (V y) x t]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeL (V p) y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeB (V y) x t)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_left_LB_st' D V W Fafr Mp' pp p y x t (V p) (V y)) as "Hf" ; auto.
        
        wp_bind (rotate_left #pp #p (left_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeL (V p) y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H23 ; subst.
        wp_bind (left_child #p) ;
          iApply (left_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".

        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeL (V p) t]>
                 (<[y:=NodeB (V y) x p]>
                  (<[p:=NodeL (V p) y]> (<[x:=NodeL (V x) l]> (<[y:=NodeB (V y) x t]> M))))). iFrame.
        iSplit ; iPureIntro ; auto.
        apply M_update_comm with (update_edge (update_edge Fafr y t p RIGHT) p y t LEFT) ; auto.
        intros. apply update_edge_comm ; stlink_tac.
        apply update_comm_inv in H24 ; stlink_tac ; auto.
      + assert (l = t). stlink_tac. subst.
        iPoseProof (rotate_right_child_LRR_l_st D V W F M pp p x y t
                                               (V p) (V x) (V y)) as "Hf" ; auto.
        iApply ("Hf" with "[R M]") ; iFrame ; auto. iClear "Hf".
        iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        remember (<[p:=NodeL (V p) y]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) x t]> M))) as Mp'.
        assert (Mp' !! p = Some (NodeL (V p) y)).
        { rewrite HeqMp'. rewrite lookup_insert. auto. }
        assert (Mp' !! y = Some (NodeB (V y) x t)).
        { rewrite HeqMp'. do 2(rewrite lookup_insert_ne ; stlink_tac). rewrite lookup_insert. auto. }
        iPoseProof (rotate_left_LB_st' D V W Fafr Mp' pp p y x t (V p) (V y)) as "Hf" ; auto.
        
        wp_bind (rotate_left #pp #p (left_child #p)).
        iPoseProof (mapsto_M_acc_same Mp' p ((NodeL (V p) y)) with "M") as "M" ; auto.
        iDestruct "M" as (v') "[% [Hp M]]". inversion H23 ; subst.
        wp_bind (left_child #p) ;
          iApply (left_child_specification with "[Hp]") ; auto ;
            iModIntro ; iIntros "Hp".

        iDestruct ("M" with "Hp") as "M".
        iApply ("Hf" with "[Hpp M]") ; iFrame ; try (iSplit ; iPureIntro ; auto).
        iClear "Hf". iModIntro. iIntros "[Hpp [% [% M]]]". wp_seq.
        iApply ("Hind" with "[Hpp M]") ; iFrame.
        iExists (<[p:=NodeL (V p) t]>
                 (<[y:=NodeB (V y) x p]>
                  (<[p:=NodeL (V p) y]> (<[x:=NodeN (V x)]> (<[y:=NodeB (V y) x t]> M))))). iFrame.
        iSplit ; iPureIntro ; auto.
        apply M_update_comm with (update_edge (update_edge Fafr y t p RIGHT) p y t LEFT) ; auto.
        intros. apply update_edge_comm ; stlink_tac.
        apply update_comm_inv in H24 ; stlink_tac ; auto.
  Qed.
  
End SplaySubCasesLeftRightRotation.

Section SplaySubCasesOO'Rotation.

  Context `{!tctrHeapG Σ} (nmax : nat).

  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable M : gmap elem content.  (* data stored in nodes *)
  
  Lemma splay_root_rotate_o_o'_gcoi_st F FF (pp p p' y x t : loc) (z : Z) o :
    Inv p D F V W ->
    Mem D F V M ->

    orientation_op o (V p) z ->
    F p x o ->
    orientation_op (invert_orientation o) (V x) z ->
    F x y (invert_orientation o) ->
    ¬ (exists t', F y t' o) ->
    F y t (invert_orientation o) ->
    
    (* rotation on children *)
    let D' := (descendants F x) in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let FC' := (remove_edge_that_are_in_D F D') in
    let F'' := (remove_edge F' x y) in
    let F''' := (add_edge F'' y x o) in

    let Fafr := add_edge (union_edge F''' FC') p y o in 
    let F1 := update_edge Fafr p y t o in 
    let F2 := update_edge F1 y t p (invert_orientation o) in 
                                                    
    ({{{ pp ↦ #y ∗ (∃ M', mapsto_M M' ∗ ⌜Mem D F2 V M'⌝ ∗ ⌜Inv y D F2 V W⌝ ) }}} 
      splay_tree_while_loop #pp #z
    {{{ M', RET #() ; pp ↦ #p' ∗ ⌜Inv p' D FF V W⌝ ∗ ⌜Mem D FF V M'⌝ ∗ mapsto_M M'}}}) -∗
    
    {{{ pp ↦ #p ∗ mapsto_M M }}} 
      splay_tree_while_loop #pp #z
    {{{ M', RET #() ; pp ↦ #p' ∗ ⌜Inv p' D FF V W⌝ ∗ ⌜Mem D FF V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    destruct o.
    + simpl. apply splay_root_rotate_left_right_gclefti_st ; auto.
    + apply splay_root_rotate_right_left_gcrighti_st ; auto.
  Qed.
    
End SplaySubCasesOO'Rotation.

