From ST Require Import Code STpredicate STpath STedgeset STlink STmemory.
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

Section Proof.

  Context `{!tctrHeapG Σ} (nmax : nat).
  Lemma value_specification `{!tctrHeapG Σ} (p : loc) (e : val) (v : Z) :    
    {{{ p ↦ InjRV (#v, e)}}}
      value #p
    {{{ RET #(v) ; p ↦ InjRV (#v, e) }}}.
  Proof.
    iIntros (Φ) "P H".
    wp_rec. wp_load.
    wp_match. wp_proj.
    iApply "H". done.
  Qed.  

  Lemma left_child_specification `{!tctrHeapG Σ} (p : loc) (e1 e2 : val) (v : Z) : 
    {{{ p ↦ InjRV (#v, (e1,e2))}}}
      left_child #p
    {{{ RET (e1) ; p ↦ InjRV (#v, (e1,e2)) }}}.
  Proof.
    iIntros (Φ) "P H".
    wp_rec. wp_load.
    wp_match. wp_proj. wp_proj.
    iApply "H". done.
  Qed.

  Lemma right_child_specification `{!tctrHeapG Σ} (p : loc) (e1 e2 : val) (v : Z) : 
    {{{ p ↦ InjRV (#v, (e1,e2))}}}
      right_child #p
    {{{ RET (e2) ;  p ↦ InjRV (#v, (e1,e2)) }}}.
  Proof.
    iIntros (Φ) "P H".
    wp_rec. wp_load.
    wp_match. wp_proj. wp_proj.
    iApply "H". done.
  Qed.
  
  Lemma value_specification_tc `{!tctrHeapG Σ} (p : loc) (e : val) (v : Z) :    
    TCTR_invariant nmax -∗
    {{{ p ↦ InjRV (#v, e) ∗ TC (5)}}}
      « value »%V #p
    {{{ RET #(v) ; p ↦ InjRV (#v, e) }}}.
  Proof.
    intros.
    iIntros "#TC_inv".
    iIntros (Φ) "!# [P TC] H".
    wp_rec. wp_tick_load.
    wp_tick_match. wp_tick_proj.
    iApply "H". done.
  Qed.  

  Lemma left_child_specification_tc `{!tctrHeapG Σ} (p : loc) (e1 e2 : val) (v : Z) :    
    TCTR_invariant nmax -∗
    {{{ p ↦ InjRV (#v, (e1,e2)) ∗ TC (6)}}}
      « left_child »%V #p
    {{{ RET (e1) ; p ↦ InjRV (#v, (e1,e2)) }}}.
  Proof.
    intros.
    iIntros "#TC_inv".
    iIntros (Φ) "!# [P TC] H".
    wp_rec. wp_tick_load.
    wp_tick_match. wp_tick_proj. wp_tick_proj.
    iApply "H". done.
  Qed.

  Lemma right_child_specification_tc `{!tctrHeapG Σ} (p : loc) (e1 e2 : val) (v : Z) :    
    TCTR_invariant nmax -∗
    {{{ p ↦ InjRV (#v, (e1,e2)) ∗ TC (6)}}}
      « right_child »%V #p
    {{{ RET (e2) ;  p ↦ InjRV (#v, (e1,e2)) }}}.
  Proof.
    intros.
    iIntros "#TC_inv".
    iIntros (Φ) "!# [P TC] H".
    wp_rec. wp_tick_load.
    wp_tick_match. wp_tick_proj. wp_tick_proj.
    iApply "H". done.
  Qed.

  Lemma splay_compare_specification_eq `{!tctrHeapG Σ} (l1 l2 : Z) :    
    {{{ ⌜l1 = l2⌝ }}}
      splay_compare #l1 #l2
    {{{ RET #(0) ; True }}}.
  Proof.
    iIntros (Φ) "% H".
    wp_rec. wp_pures.
    destruct (bool_decide (#l1 = #l2)) eqn:E ; wp_pures.
    + iApply "H". auto.
    + apply bool_decide_eq_false in E.
      destruct (bool_decide (l1 < l2)%Z).
      - exfalso. apply E.
        subst ; auto.
      - wp_pures. subst.
        exfalso. apply E ; auto.
  Qed.
  
  Lemma splay_compare_specification_lt `{!tctrHeapG Σ} (l1 l2 : Z) :    
    {{{ ⌜l1 < l2⌝ }}}
      splay_compare #l1 #l2
    {{{ RET #(-1) ; True }}}.
  Proof.
    iIntros (Φ) "% H".
    wp_rec. wp_pures.
    destruct (bool_decide (#l1 = #l2)) eqn:E ; wp_pures.
    + apply bool_decide_eq_true in E.
      inversion E. subst. rewrite lt_zarith in H.
      lia.
    + apply bool_decide_eq_false in E.
      destruct (bool_decide (l1 < l2)%Z) eqn:E' ; wp_pures.
      - iApply "H". auto.
      - rewrite lt_zarith in H.
        apply bool_decide_eq_false in E'.
        lia.
  Qed.
  
  Lemma splay_compare_specification_gt `{!tctrHeapG Σ} (l1 l2 : Z) :    
    {{{ ⌜l1 > l2⌝ }}}
      splay_compare #l1 #l2
    {{{ RET #(1) ; True }}}.
  Proof.
    iIntros (Φ) "% H".
    wp_rec. wp_pures.
    destruct (bool_decide (#l1 = #l2)) eqn:E ; wp_pures.
    + apply bool_decide_eq_true in E.
      inversion E. subst. rewrite gt_zarith in H.
      lia.
    + apply bool_decide_eq_false in E.
      destruct (bool_decide (l1 < l2)%Z) eqn:E' ; wp_pures.
      - apply bool_decide_eq_true in E'. 
        rewrite gt_zarith in H. lia.
      - iApply "H". auto.
  Qed.

  Lemma splay_to_loop `{!tctrHeapG Σ} (pp x: loc) (z : Z) P K :    
    ({{{ pp ↦ #x ∗ K }}} 
      splay_tree_while_loop #pp #z
      {{{ RET #() ; P }}}) -∗
    ({{{ pp ↦ #x ∗ K}}} 
      splay_tree_splay #pp #z
      {{{ RET #() ; P }}}).
  Proof.
    intros.
    iIntros "#H".
    iModIntro.
    iIntros (Φ) "[Hpp K] Hf".
    unfold splay_tree_splay.
    wp_lam. wp_let. wp_load. wp_pures.
    iApply ("H" with "[Hpp K]") ; iFrame.
  Qed.
  
End Proof.
