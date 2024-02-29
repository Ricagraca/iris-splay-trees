From iris_time.heap_lang Require Import notation lib.assert.
From iris_time.heap_lang Require Export lang.
From iris_time.heap_lang Require Import proofmode.
From iris_time Require Import Combined.

From iris.bi Require Import big_op.

From ST Require Import Code STorientation 
     STpredicate STpath STedgeset STedgesetrotateroot
     STrotaterightcasesroot STrotateleftcasesroot STlink STmemory STproof STdomain
     STpathcount STsplaycases_irfail STsplaycases_ironeleftrotation
     STsplaycases_ironeleftrotationgrandchild 
     STsplaycases_ironerightrotation
     STsplaycases_ironerightrotationgrandchild
     STsplaycases_ir_oo_child_nlgc
     STsplaycases_ir_oo_child_lgc
     STsplaycases_ir_ooi_child_nlgc
     STsplaycases_ir_ooi_child_gco
     STsplaycases_ir_ooi_child_gcoi
     STsplaycases_ir_ooi_child_gcooi
     STsplaycases_ir STir.

From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual
     LibInt.

Section SplaySpecification.

  Context `{!tctrHeapG Σ} (nmax : nat).
  
  Lemma bw_ir_splay_loop_st : forall n p D (F:EdgeSet) V W pp p' k F' M,
    bw_ir F V p p' k n F' ENDED ->
    Inv p D F V W ->
    Mem D F V M -> 
    {{{ pp ↦ #p ∗ mapsto_M M }}}
      splay_tree_while_loop #pp #k
    {{{ M', RET #() ; pp ↦ #p' ∗ ⌜Inv p' D F' V W⌝ ∗ ⌜Mem D F' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intro n. 
    induction_wf IH: Wf_nat.lt_wf n.
    intros.
    iIntros "[R M] H".
    rename H2 into Mem.
    rename H1 into Inv.
    inversion H0 ; subst ; intros.
    + iApply (splay_root_st with "[R M]") ; auto. auto. apply Mem.
      auto. iFrame.
    + iApply (splay_root_fail_left_child_st with "[R M]") ; auto.
      auto. apply Mem. rewrite lt_zarith. lia. auto. iFrame.
    + iApply (splay_root_fail_right_child_st with "[R M]") ; auto.
      auto. apply Mem. rewrite lt_zarith. lia. auto. iFrame.
    + iApply (splay_root_rotate_left_st with "[R M]"). auto.
      apply Inv. apply Mem. rewrite lt_zarith. lia.
      apply H2. destruct H3 ; auto. rewrite lt_zarith.
      auto. auto. iFrame. auto.
    + iApply (splay_root_rotate_left_gc_st with "[R M]"). auto.
      apply Inv. apply Mem. rewrite lt_zarith. lia. apply H2.
      auto. apply H4. iFrame. auto.
    + iApply (splay_root_rotate_right_st with "[R M]"). auto.
      apply Inv. apply Mem. rewrite lt_zarith. lia. apply H2.
      rewrite lt_zarith. auto. apply H4. iFrame. auto. 
    + iApply (splay_root_rotate_right_gc_st with "[R M]"). auto.
      apply Inv. apply Mem. rewrite lt_zarith. lia. apply H2.
      auto. apply H4. iFrame. auto. 
    + assert ((n < (S (S n)))%nat). lia.
      inversion H1 ; subst.
      - iApply (splay_root_rotate_o_o_ngc_st D V W M F F' pp p p' x0 x k o with "[] [R M]") ; auto ; iFrame.
        iModIntro. iIntros (Φ') "[Hpp M]". 
        iDestruct "M" as (M') "[M [% %]]". 
        specialize (H n H3 x0 D F3 V W pp p' k F' M' H2 H10 H9 Φ').
        iApply (H with "[Hpp M]") ; iFrame.
      - iApply (splay_root_rotate_o_o_gc_st D V W M F F' pp p p' x0 x t k o with "[] [R M]") ; auto ; try iFrame.
        iModIntro. iIntros (Φ') "[Hpp M]". 
        iDestruct "M" as (M') "[M [% %]]". 
        specialize (H n H3 x0 D F3 V W pp p' k F' M' H2 H10 H9 Φ').
        iApply (H with "[Hpp M]") ; iFrame.
      - iApply (splay_root_rotate_o_o'_ngc_st D V W M F F' pp p p' x0 x k o with "[] [R M]") ; auto ; iFrame.
        iModIntro. iIntros (Φ') "[Hpp M]". 
        iDestruct "M" as (M') "[M [% %]]". 
        specialize (H n H3 x0 D F3 V W pp p' k F' M' H2 H11 H10).
        iApply (H with "[Hpp M]") ; iFrame.
      - iApply (splay_root_rotate_o_o'_gcoi_st D V W M F F' pp p p' x0 x t k o with "[] [R M]") ; auto ; iFrame.
        iModIntro. iIntros (Φ') "[Hpp M]". 
        iDestruct "M" as (M') "[M [% %]]". 
        specialize (H n H3 x0 D F3 V W pp p' k F' M' H2 H11 H10).
        iApply (H with "[Hpp M]") ; iFrame.
      - iApply (splay_root_rotate_o_o'_gco_st D V W M F F' pp p p' x0 x t k o with "[] [R M]") ; auto ; iFrame.
        iModIntro. iIntros (Φ') "[Hpp M]". 
        iDestruct "M" as (M') "[M [% %]]". 
        specialize (H n H3 x0 D F3 V W pp p' k F' M' H2 H11 H10).
        iApply (H with "[Hpp M]") ; iFrame.
      - iApply (splay_root_rotate_o_o'_gcooi_st D V W M F F' pp p p' x0 x t1 t2 k o with "[] [R M]") ; auto ; iFrame.
        iModIntro. iIntros (Φ') "[Hpp M]". 
        iDestruct "M" as (M') "[M [% %]]". 
        specialize (H n H3 x0 D F3 V W pp p' k F' M' H2 H11 H10).
        iApply (H with "[Hpp M]") ; iFrame.
      - inversion H11.
  Qed.
  
  Lemma bw_ir_splay_st : forall n p D (F:EdgeSet) V W pp p' k F' M,
    bw_ir F V p p' k n F' ENDED ->
    Inv p D F V W ->
    Mem D F V M -> 
    {{{ pp ↦ #p ∗ mapsto_M M }}}
      splay_tree_splay #pp #k
    {{{ M', RET #() ; pp ↦ #p' ∗ ⌜Inv p' D F' V W⌝ ∗ ⌜Mem D F' V M'⌝ ∗ mapsto_M M'}}}.
  Proof.
    intros.
    iIntros "[Hpp M] Hf". wp_rec. wp_pures. wp_load.
    wp_pures. iApply (bw_ir_splay_loop_st n p D (F:EdgeSet) V W pp p' k F' M with "[Hpp M] [Hf]") ; auto ; iFrame.
  Qed.

  Lemma splay_st (p pp : elem) (D : set elem) (V W : elem -> Z) (k : Z) :
    {{{ pp ↦ #p ∗ ST p D V W }}}
      splay_tree_splay #pp #k 
    {{{ (p' : elem) ,  RET #() ; pp ↦ #p' ∗ ST p' D V W }}}.
  Proof.
    intros.
    iIntros "[Hp ST]".
    unfold ST. 
    iDestruct "ST" as (F M) "[% [% M]]".
    pose proof (exists_bw_ir p D V W p F k H).
    do 3destruct H1.
    pose proof (bw_ir_splay_st x1 p D F V W pp x0 k x M). iIntros "Hf".
    wp_apply (H2 with "[Hp M]") ; auto ; try iFrame.
    iIntros (M') "[Hpp [% [% M]]]". iApply "Hf" ; iFrame.
    iExists (x), (M'). auto.    
  Qed.

  Lemma bw_ir_splay_loop_st' : forall n p D (F:EdgeSet) V W pp p' k F' M,
    bw_ir F V p p' k n F' ENDED ->
    Inv p D F V W ->
    Mem D F V M -> 
    {{{ pp ↦ #p ∗ mapsto_M M }}}
      splay_tree_while_loop #pp #k
    {{{ M', RET #() ;
        pp ↦ #p' ∗
           ⌜Inv p' D F' V W⌝ ∗
           ⌜Mem D F' V M'⌝   ∗
           mapsto_M M'       ∗
           ⌜ (forall y y' o, F' p' y o -> y' \in descendants F' y -> (orientation_op o) k (V y')) ⌝
      }}}.
  Proof.
    intros. iIntros "[iH1 iH2] Hf".
    pose proof (bw_ir_splay_loop_st n p D F V W pp p' k F' M H H0 H1).
    wp_apply (H2 with "[iH1 iH2]"). iFrame.
    iIntros (M') "[iH3 [% [% M]]]". iApply "Hf". iFrame.
    iPureIntro. split ; auto. split ; auto. intros.
    pose proof (bw_ir_key_op D V W p F p' n k F' H0 H y y' o).
    apply H7 ; auto.
  Qed.  
 
  Lemma splay_st' : forall p D (F:EdgeSet) V W pp k M,
    Inv p D F V W ->
    Mem D F V M -> 
    {{{ pp ↦ #p ∗ mapsto_M M }}}
      splay_tree_splay #pp #k
    {{{ M' F' (p' : loc) , RET #() ;
        pp ↦ #p' ∗
           ⌜Inv p' D F' V W⌝ ∗
           ⌜Mem D F' V M'⌝ ∗
            mapsto_M M' ∗
           ⌜ (forall y y' o, F' p' y o -> y' \in descendants F' y -> (orientation_op o) k (V y')) ⌝
      }}}.
  Proof.
    intros. iIntros "[iH1 iH2] Hf".
    wp_rec. wp_pures. wp_load. wp_pures.
    pose proof (exists_bw_ir p D V W p F k H).
    do 3destruct H1.
    wp_apply (bw_ir_splay_loop_st' with "[iH1 iH2]").
    apply H1. apply H. apply H0. iFrame.
    iIntros (M') "[Hpp [% [% [M %]]]]".
    iApply "Hf". iFrame. iPureIntro. split. apply H2.
    split ; auto. 
  Qed.

 Lemma splay_on_empty : forall (pp p : loc) k,
    {{{ pp ↦ NONEV }}}
      splay_tree_splay #pp #k
    {{{ RET #() ; pp ↦ NONEV }}}.
  Proof.
    intros. iIntros "Hpp Hf".
    wp_rec. wp_pures. wp_load. wp_pures.
    iApply "Hf". iFrame.
  Qed.
  
End SplaySpecification.
