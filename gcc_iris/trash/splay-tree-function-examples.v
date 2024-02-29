
Require Import code.
From iris.heap_lang Require Import notation lib.assert.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.

Lemma ex12 `{!heapG Σ} (pp p p1 p2 p3 : loc) (pv : val) :
  {{{ pp ↦ #p ∗
         p ↦ (SOMEV (#4, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#2, (#p3, NONEV))) ∗
         p2 ↦ (SOMEV (#6, (NONEV, NONEV))) ∗
         p3 ↦ (SOMEV (#1, (NONEV, NONEV))) }}}
    splay_tree_foreach #pp (λ: "x", #2 * "x")
    {{{ RET #() ;
        pp ↦ #p ∗
         p ↦ (SOMEV (#8, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#4, (#p3, NONEV))) ∗
         p2 ↦ (SOMEV (#12, (NONEV, NONEV))) ∗
         p3 ↦ (SOMEV (#2, (NONEV, NONEV))) 
    }}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 [Hp2 Hp3]]]] H".
  repeat (wp_load || wp_rec || wp_pures || wp_match || wp_proj || wp_store).
  iApply "H". iFrame.  
Qed.

Lemma ex2 `{!heapG Σ} (pp p p1 p2 p3 : loc) (pv : val) :
  {{{ pp ↦ #p ∗
         p ↦ (SOMEV (#4, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#2, (#p3, NONEV))) ∗
         p2 ↦ (SOMEV (#6, (NONEV, NONEV))) ∗
         p3 ↦ (SOMEV (#1, (NONEV, NONEV))) }}}
    splay_tree_splay #pp #0
    {{{ RET #() ;
        pp ↦ #p3 ∗
           p ↦ (SOMEV (#4, (#p1, #p2))) ∗
           p1 ↦ (SOMEV (#2, (NONEV, NONEV))) ∗
                     p2 ↦ (SOMEV (#6, (NONEV, NONEV))) ∗
                     p3 ↦ (SOMEV (#1, (NONEV, #p)))
    }}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 [Hp2 Hp3]]]] H".
  wp_rec. wp_let.
  wp_load. wp_op. wp_if. wp_pures.

  wp_load.
  wp_let. 
  unfold value. wp_load. wp_match.
  wp_proj. unfold splay_compare.
  wp_pures. wp_lam. wp_load. wp_match. do 2 wp_proj.
  wp_load. wp_match. wp_proj.
  wp_lam. wp_let. wp_op ; wp_if. wp_op ; wp_if.
  wp_let. wp_op ; wp_if. wp_op ; wp_if.

  wp_pures. wp_rec. wp_load.
  wp_match. do 2 wp_proj. wp_op ; wp_if.
  wp_op ; wp_if. wp_if. wp_op ; wp_if. wp_op ; wp_if. wp_lam.

  wp_pures. wp_load. wp_match. do 2wp_proj.
  wp_let. wp_rec. wp_load ; wp_match ; do 2wp_proj.
  
  wp_alloc adf as "Hpp1".
  wp_rec.
  wp_let. wp_let. wp_rec. wp_load ; wp_match.
  do 2wp_proj. wp_let. wp_rec. wp_load ; wp_match.
  do 2wp_proj. wp_pures. wp_rec. wp_load ; wp_match.
  wp_proj. wp_store. wp_rec. wp_load.
  wp_pures. wp_rec. wp_load. wp_match.
  wp_proj. wp_store. wp_store.
  wp_rec. wp_load. wp_match.
  do 2wp_proj. wp_pures.
  wp_load. wp_match. wp_proj. wp_store.

  wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_rec. wp_pures. wp_rec. 
  wp_load ; wp_match ; do 2wp_proj.
  wp_pures.
  wp_rec.
  wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_rec.

  wp_load ; wp_match ; wp_proj.
  wp_store. wp_rec.
  wp_load ; wp_match ; do 2wp_proj.

  wp_pures.
  wp_rec.
  wp_load ; wp_match ; wp_proj.
  wp_store. wp_store.

  wp_rec. wp_pures. wp_load.
  wp_pures. wp_load.
  wp_match ; wp_proj.
  wp_pures. wp_rec.
  wp_load ; wp_match ; do 2wp_proj.
  wp_pures.

  iApply "H". iFrame.
  
  
Qed.

Lemma ex11 `{!heapG Σ} (pp p p1 p2 p3 p4 : loc) (pv : val) :
  {{{    pp ↦ #p ∗
         p ↦ (SOMEV (#4, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#2, (#p3, NONEV))) ∗
         p2 ↦ (SOMEV (#6, (NONEV, NONEV))) ∗
         p3 ↦ (SOMEV (#1, (NONEV, NONEV)))
  }}}
    splay_tree_lookup #pp #0
    {{{ RET (NONEV) ;
         pp ↦ #p3 ∗
           p ↦ (SOMEV (#4, (#p1, #p2))) ∗
           p1 ↦ (SOMEV (#2, (NONEV, NONEV))) ∗
                     p2 ↦ (SOMEV (#6, (NONEV, NONEV))) ∗
                     p3 ↦ (SOMEV (#1, (NONEV, #p)))
    }}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 [Hp2 Hp3]]]] H".
  wp_rec. wp_pures. 
  iCombine "Hpp Hp Hp1 Hp2 Hp3" as "All".
  wp_apply (ex2 with "All") ; auto.
  iIntros "[Hpp [Hp [Hp1 [Hp2 Hp3]]]]". wp_seq.
  wp_load. wp_pures. wp_load. wp_rec.
  wp_load ; wp_match ; wp_proj.
  wp_rec. wp_pures. iApply "H". iFrame.
Qed.

Lemma ex4 `{!heapG Σ} (pp p p1 p2 p3 : loc) (pv : val) :
  {{{ pp ↦ #p ∗
         p ↦ (SOMEV (#4, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#2, (NONEV, NONEV))) ∗
         p2 ↦ (SOMEV (#6, (NONEV, #p3))) ∗
         p3 ↦ (SOMEV (#10, (NONEV, NONEV))) }}}
    splay_tree_splay #pp #10
    {{{ RET #(NONE) ;
        pp ↦ #p3 ∗
           p ↦ (SOMEV (#4, (#p1, #p2))) ∗
           p1 ↦ (SOMEV (#2, (NONEV, NONEV))) ∗
                     p2 ↦ (SOMEV (#6, (NONEV, NONEV))) ∗
                     p3 ↦ (SOMEV (#1, (NONEV, #p)))
    }}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 [Hp2 Hp3]]]] H".
  wp_rec. wp_let.
  wp_load. wp_op. wp_if. wp_pures.

  wp_load.
  wp_let. 
  unfold value. wp_load. wp_match.
  wp_proj. unfold splay_compare.
  wp_pures. wp_lam. wp_load. wp_match. do 2 wp_proj.
  wp_load. wp_match. wp_proj.
  wp_lam. wp_let. wp_op ; wp_if. wp_op ; wp_if.
  wp_let. wp_op ; wp_if. wp_op ; wp_if.

  wp_pures. wp_rec. wp_load.
  wp_match. do 2 wp_proj. wp_op ; wp_if.
  wp_op ; wp_if. wp_if. wp_op ; wp_if. wp_op ; wp_if. wp_lam.

  wp_pures. wp_load. wp_match. do 2wp_proj.
  wp_pures. wp_rec.
  wp_load ; wp_match ; do 2wp_proj.
  
  wp_alloc adf as "Hpp1".
  wp_rec.
  wp_let. wp_let. wp_rec. wp_load ; wp_match.
  do 2wp_proj. wp_let. wp_rec. wp_load ; wp_match.
  do 2wp_proj. wp_pures. wp_rec. wp_load ; wp_match.
  wp_proj. wp_store. wp_rec. wp_load.
  wp_pures. wp_rec. wp_load. wp_match.
  wp_proj. wp_store. wp_store.
  wp_rec. wp_load. wp_match.
  do 2wp_proj. wp_pures.
  wp_load. wp_match. wp_proj. wp_store.
  
  wp_rec. wp_load. wp_match. do 2wp_proj.
  wp_rec. wp_pures. wp_rec.
  wp_load ; wp_match ; wp_proj.
  wp_pures.

  wp_rec. wp_load ; wp_match ; wp_proj.
  wp_pures. wp_rec. wp_load ; wp_match ; wp_proj.
  wp_store. wp_rec. wp_load ; wp_match ; wp_proj.

  wp_pures. wp_rec. wp_load ; wp_match ; wp_proj.
  wp_store. wp_store. wp_rec. wp_pures. wp_load.
  wp_pures.
  wp_load ; wp_match ; repeat wp_proj.
  wp_pures. 
  
  iApply "H". iFrame.
  
Qed.


Lemma ex11 `{!heapG Σ} (pp p p1 p2 p3 p4 : loc) (pv : val) :
  {{{ pp ↦ #p ∗
         p ↦ (SOMEV (#4, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#2, (NONEV, NONEV))) ∗
         p2 ↦ (SOMEV (#6, (NONEV, #p3))) ∗
         p3 ↦ (SOMEV (#10, (NONEV, NONEV)))
  }}}
    splay_tree_lookup #pp #10
    {{{ RET #(10) ;
        pp ↦ #p3 ∗
           p ↦ (SOMEV (#4, (#p1, #p2))) ∗
           p1 ↦ (SOMEV (#2, (NONEV, NONEV))) ∗
                     p2 ↦ (SOMEV (#6, (NONEV, NONEV))) ∗
                     p3 ↦ (SOMEV (#10, (#p, NONEV)))
    }}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 [Hp2 Hp3]]]] H".
  wp_rec. wp_pures. 
  iCombine "Hpp Hp Hp1 Hp2 Hp3" as "All".
  wp_apply (ex4 with "All") ; auto.
  iIntros "[Hpp [Hp [Hp1 [Hp2 Hp3]]]]". wp_seq.
  wp_load. wp_pures. wp_load. wp_rec.
  wp_load ; wp_match ; wp_proj.
  wp_rec. wp_pures. iApply "H". iFrame.
Qed.
  
Lemma ex10 `{!heapG Σ} (pp p p1 p2 p3 : loc) (pv : val) :
  {{{ pp ↦ #p ∗
         p ↦ (SOMEV (#4, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#2, (#p3, NONEV))) ∗
         p2 ↦ (SOMEV (#6, (NONEV, NONEV))) ∗
         p3 ↦ (SOMEV (#1, (NONEV, NONEV))) }}}
    splay_tree_remove #pp #4
    {{{ RET #() ;
        pp ↦ #p1 ∗
           p ↦ (SOMEV (#4, (#p1, #p2))) ∗
           p1 ↦ (SOMEV (#2, (#p3, #p2))) ∗
                     p2 ↦ (SOMEV (#6, (NONEV, NONEV))) ∗
                     p3 ↦ (SOMEV (#1, (NONEV, NONEV)))
    }}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 [Hp2 Hp3]]]] H".
  wp_rec. wp_pures. wp_rec.
  wp_pures. wp_load ; wp_pures.
  wp_load ; wp_pures.
  wp_rec ; wp_pures.
  wp_load ; wp_match ; wp_proj.
  wp_rec. wp_pures.
  wp_load ; wp_pures.
  wp_load ; wp_rec ; wp_pures.
  wp_load ; wp_match ; wp_proj.
  wp_rec ; wp_pures.
  wp_load ; wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_pures.
  wp_alloc a as "Ha". wp_pures.
  wp_load ; wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_alloc b as "Hb". wp_pures. wp_load.
  wp_pures. wp_load.
  wp_store. wp_pures. wp_load. wp_pures.
  (*Entra no while loop*) wp_pures. wp_load. wp_rec.
  wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_load. wp_load.
  wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_load. wp_rec. wp_load ; wp_match ; wp_proj.
  wp_load. wp_store. iApply "H" ; iFrame.
Qed.

Lemma ex11 `{!heapG Σ} (pp p p1 p2 p3 p4 : loc) (pv : val) :
  {{{ pp ↦ #p ∗
         p ↦ (SOMEV (#4, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#2, (#p3, #p4))) ∗
         p2 ↦ (SOMEV (#6, (NONEV, NONEV))) ∗
         p3 ↦ (SOMEV (#1, (NONEV, NONEV))) ∗
         p4 ↦ (SOMEV (#3, (NONEV, NONEV))) }}}
    splay_tree_remove #pp #4
    {{{ RET #() ;
        pp ↦ #p1 ∗
           p ↦ (SOMEV (#4, (#p1, #p2))) ∗
           p1 ↦ (SOMEV (#2, (#p3, #p4))) ∗
           p2 ↦ (SOMEV (#6, (NONEV, NONEV))) ∗
           p4 ↦ (SOMEV (#3, (NONEV, #p2))) ∗
                     p3 ↦ (SOMEV (#1, (NONEV, NONEV)))
    }}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 [Hp2 [Hp3 Hp4]]]]] H".
  wp_rec. wp_pures. wp_rec.
  wp_pures. wp_load ; wp_pures.
  wp_load ; wp_pures.
  wp_rec ; wp_pures.
  wp_load ; wp_match ; wp_proj.
  wp_rec. wp_pures.
  wp_load ; wp_pures.
  wp_load ; wp_rec ; wp_pures.
  wp_load ; wp_match ; wp_proj.
  wp_rec ; wp_pures.
  wp_load ; wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_pures.
  wp_alloc a as "Ha". wp_pures.
  wp_load ; wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_alloc b as "Hb". wp_pures. wp_load.
  wp_pures. 
  wp_load. wp_store.
  wp_load. wp_pures. wp_load. wp_rec.
  wp_load. wp_load. wp_rec. wp_load. wp_match.
  do 2wp_proj. wp_store.
  (*Entra no while loop*) wp_pures. wp_load. wp_rec.
  wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_load. wp_load. wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_load. wp_rec.
  wp_load ; wp_match ; wp_proj.
  wp_pures. wp_load. wp_store.
  iApply "H". iFrame.
Qed.
  
Lemma ex2 `{!heapG Σ} (pp p p1 p2 p3 : loc) (pv : val) :
  {{{ pp ↦ #p ∗
         p ↦ (SOMEV (#4, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#2, (#p3, NONEV))) ∗
         p2 ↦ (SOMEV (#6, (NONEV, NONEV))) ∗
         p3 ↦ (SOMEV (#1, (NONEV, NONEV))) }}}
    splay_tree_splay #pp #0
    {{{ RET #() ;
        pp ↦ #p3 ∗
           p ↦ (SOMEV (#4, (#p1, #p2))) ∗
           p1 ↦ (SOMEV (#2, (NONEV, NONEV))) ∗
                     p2 ↦ (SOMEV (#6, (NONEV, NONEV))) ∗
                     p3 ↦ (SOMEV (#1, (NONEV, #p)))
    }}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 [Hp2 Hp3]]]] H".
  wp_rec. wp_let.
  wp_load. wp_op. wp_if. wp_pures.

  wp_load.
  wp_let. 
  unfold value. wp_load. wp_match.
  wp_proj. unfold splay_compare.
  wp_pures. wp_lam. wp_load. wp_match. do 2 wp_proj.
  wp_load. wp_match. wp_proj.
  wp_lam. wp_let. wp_op ; wp_if. wp_op ; wp_if.
  wp_let. wp_op ; wp_if. wp_op ; wp_if.

  wp_pures. wp_rec. wp_load.
  wp_match. do 2 wp_proj. wp_op ; wp_if.
  wp_op ; wp_if. wp_if. wp_op ; wp_if. wp_op ; wp_if. wp_lam.

  wp_pures. wp_load. wp_match. do 2wp_proj.
  wp_let. wp_rec. wp_load ; wp_match ; do 2wp_proj.
  
  wp_alloc adf as "Hpp1".
  wp_rec.
  wp_let. wp_let. wp_rec. wp_load ; wp_match.
  do 2wp_proj. wp_let. wp_rec. wp_load ; wp_match.
  do 2wp_proj. wp_pures. wp_rec. wp_load ; wp_match.
  wp_proj. wp_store. wp_rec. wp_load.
  wp_pures. wp_rec. wp_load. wp_match.
  wp_proj. wp_store. wp_store.
  wp_rec. wp_load. wp_match.
  do 2wp_proj. wp_pures.
  wp_load. wp_match. wp_proj. wp_store.

  wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_rec. wp_pures. wp_rec. 
  wp_load ; wp_match ; do 2wp_proj.
  wp_pures.
  wp_rec.
  wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_rec.

  wp_load ; wp_match ; wp_proj.
  wp_store. wp_rec.
  wp_load ; wp_match ; do 2wp_proj.

  wp_pures.
  wp_rec.
  wp_load ; wp_match ; wp_proj.
  wp_store. wp_store.

  wp_rec. wp_pures. wp_load.
  wp_pures. wp_load.
  wp_match ; wp_proj.
  wp_pures. wp_rec.
  wp_load ; wp_match ; do 2wp_proj.
  wp_pures.

  iApply "H". iFrame.
  
  
Qed.


Lemma ex6 `{!heapG Σ} (pp p p1 p2 p3 p4 : loc) (pv : val) :
  {{{ pp ↦ #p ∗ p ↦ (SOMEV (#4, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#2, (#p3, NONEV))) ∗
         p2 ↦ (SOMEV (#6, (NONEV, NONEV))) ∗
         p3 ↦ (SOMEV (#1, (NONEV, NONEV))) ∗
         p4 ↦ (SOMEV (#0, (NONEV, NONEV)))
  }}}
    splay_tree_insert #pp #p4
    {{{ RET #() ;
        pp ↦ #p4 ∗
           p ↦ (SOMEV (#4, (#p1, #p2))) ∗
           p1 ↦ (SOMEV (#2, (NONEV, NONEV))) ∗
           p2 ↦ (SOMEV (#6, (NONEV, NONEV))) ∗
           p3 ↦ (SOMEV (#1, (NONEV, #p))) ∗
           p4 ↦ (SOMEV (#0, (NONEV, #p3)))
    }}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 [Hp2 [Hp3 Hp4]]]]] H".
  wp_rec. wp_let.
  wp_rec. wp_load ; wp_match ; wp_proj.
  wp_bind (splay_tree_splay #pp #0).
  iCombine "Hpp Hp Hp1 Hp2 Hp3" as "All".
  wp_apply (ex2 with "All") ; auto.
  iIntros "[Hpp [Hp [Hp1 [Hp2 Hp3]]]]". wp_seq.
  wp_load. wp_pures. wp_rec. wp_load.
  wp_load. wp_rec. wp_load. wp_match. wp_proj.
  wp_rec. wp_pures. wp_load. wp_op.
  wp_op. wp_if. wp_op ; wp_if. wp_load.
  wp_op. wp_if. wp_op. wp_if.
  wp_pures. wp_load. wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_rec. wp_load ; wp_match ; wp_proj.
  wp_store. wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_rec. wp_load ; wp_match ; do 2wp_proj. 
  wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_rec. 
  wp_load ; wp_match ; wp_proj.
  wp_store.
  wp_rec. wp_load. wp_match.
  do 2wp_proj. wp_rec.

  wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_rec. 
  wp_load ; wp_match ; do 2wp_proj.
  wp_rec. 
  wp_load ; wp_match ; wp_proj.
  wp_pures. wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_store. wp_store. iApply "H".
  iFrame.  
Qed.


Lemma ex0 `{!heapG Σ} (pp p  p1 p2 : loc) (pv : val) :
  {{{ pp ↦ #p ∗
         p ↦ (SOMEV (#3, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#1, (NONEV, NONEV))) ∗
         p2 ↦ (SOMEV (#5, (NONEV, NONEV))) }}}
    splay_tree_splay #pp #1
    {{{ RET #() ; pp ↦ #p1 ∗ p1 ↦ (SOMEV (#1, (NONEV, #p))) ∗ p ↦ (SOMEV (#3, (NONEV, #p2)))
                   ∗ p2 ↦ (SOMEV (#5, (NONEV, NONEV)))}}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 [Hp2 Hpn]]]] H".
  wp_rec. wp_let.
  wp_load. wp_op. wp_if. wp_pures.
  unfold create_node. wp_load.
  wp_let. 
  unfold value. wp_load. wp_match.
  wp_proj. unfold splay_compare.
  wp_pures. wp_lam. wp_load. wp_match. do 2 wp_proj.
  wp_load. wp_pures.
  wp_lam. wp_pures. wp_rec. wp_load. wp_match.
  do 2wp_proj. wp_let. wp_rec. wp_load ; wp_match ; wp_proj.
  wp_pures. wp_rec. wp_load ; wp_match ; wp_proj.
  wp_store. wp_rec. wp_load. wp_match ; do 2wp_proj.
  wp_pures. wp_rec. wp_load. wp_match. wp_proj.
  wp_store. wp_store. iApply "H". iFrame.
Qed.

Lemma ex8 `{!heapG Σ} (pp p  p1 p2 : loc) (pv : val) :
  {{{ pp ↦ #p ∗
         p ↦ (SOMEV (#3, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#1, (NONEV, NONEV))) ∗
         p2 ↦ (SOMEV (#5, (NONEV, NONEV))) }}}
    splay_tree_remove #pp #1
    {{{ RET #() ; pp ↦ #p ∗ p1 ↦ (SOMEV (#1, (NONEV, #p))) ∗ p ↦ (SOMEV (#3, (NONEV, #p2)))
                   ∗ p2 ↦ (SOMEV (#5, (NONEV, NONEV)))}}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 Hp2]]] H".
  wp_rec. wp_let.
  wp_bind (splay_tree_splay #pp #1).
  iCombine "Hpp Hp Hp1 Hp2" as "All".
  wp_apply (ex0 with "All") ; auto.
  iIntros "[Hpp [Hp [Hp1 Hp2]]]". wp_seq.
  wp_load. wp_op. wp_pures. wp_load.
  wp_rec. wp_load ; wp_match ; wp_proj.
  wp_rec. wp_pures. wp_load. wp_rec.
  wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_load. wp_rec.
  wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_store.
  iApply "H".
  iFrame.
Qed.

Lemma ex7 `{!heapG Σ} (pp p p1 p2 p3 p4 : loc) (pv : val) :
  {{{ pp ↦ #p ∗
         p ↦ (SOMEV (#3, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#1, (NONEV, NONEV))) ∗
         p2 ↦ (SOMEV (#5, (NONEV, NONEV))) ∗
         p3 ↦ (SOMEV (#1, (NONEV, NONEV)))
  }}}
    splay_tree_insert #pp #p3
    {{{ RET #() ; pp ↦ #p1 ∗ p1 ↦ (SOMEV (#1, (NONEV, #p))) ∗ p ↦ (SOMEV (#3, (NONEV, #p2)))
                   ∗ p2 ↦ (SOMEV (#5, (NONEV, NONEV)))∗
         p3 ↦ (SOMEV (#1, (NONEV, NONEV)))
  }}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 [Hp2 Hp3]]]] H".
  wp_rec. wp_let.
  wp_rec. wp_load ; wp_match ; wp_proj.
  wp_bind (splay_tree_splay #pp #1).
  iCombine "Hpp Hp Hp1 Hp2" as "All".
  wp_apply (ex0 with "All") ; auto.
  iIntros "[Hpp [Hp [Hp1 Hp2]]]". wp_seq.
  wp_load. wp_pures. wp_rec. wp_load.
  wp_load. wp_rec. wp_load. wp_match. wp_proj.
  wp_rec. wp_pures. wp_load. wp_op.
  wp_op. wp_if. wp_op ; wp_if. 
  iApply "H".
  iFrame.  
Qed.

Lemma ex5 `{!heapG Σ} (pp p p1 p2 p3 : loc) (pv : val) :
  {{{ pp ↦ #p ∗
         p ↦ (SOMEV (#4, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#2, (NONEV, NONEV))) ∗
         p2 ↦ (SOMEV (#6, (NONEV, #p3))) ∗
         p3 ↦ (SOMEV (#10, (NONEV, NONEV))) }}}
    splay_tree_splay #pp #7
    {{{ RET #() ;
        pp ↦ #p3 ∗
           p ↦ (SOMEV (#4, (#p1, NONEV))) ∗
           p1 ↦ (SOMEV (#2, (NONEV, NONEV))) ∗
                     p2 ↦ (SOMEV (#6, (#p, NONEV))) ∗
                     p3 ↦ (SOMEV (#10, (#p2, NONEV)))
    }}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 [Hp2 Hp3]]]] H".
  wp_rec. wp_let.
  wp_load. wp_op. wp_if. wp_pures.

  wp_load.
  wp_let. 
  unfold value. wp_load. wp_match.
  wp_proj. unfold splay_compare.
  wp_pures. wp_lam. wp_load. wp_match. do 2 wp_proj.
  wp_load. wp_match. wp_proj.
  wp_lam. wp_let. wp_op ; wp_if. wp_op ; wp_if.
  wp_let. wp_op ; wp_if. wp_op ; wp_if.

  wp_pures. wp_rec. wp_load.
  wp_match. do 2 wp_proj. wp_op ; wp_if.
  wp_op ; wp_if. wp_if. wp_op ; wp_if. wp_op ; wp_if. wp_lam.

  wp_pures. wp_load. wp_match. do 2wp_proj.
  wp_pures. wp_rec.
  wp_load ; wp_match ; do 2wp_proj.
  
  wp_alloc adf as "Hpp1".
  wp_rec.
  wp_let. wp_let. wp_rec. wp_load ; wp_match.
  do 2wp_proj. wp_let. wp_rec. wp_load ; wp_match.
  do 2wp_proj. wp_pures. wp_rec. wp_load ; wp_match.
  wp_proj. wp_store. wp_rec. wp_load.
  wp_pures. wp_rec. wp_load. wp_match.
  wp_proj. wp_store. wp_store.
  wp_rec. wp_load. wp_match.
  do 2wp_proj. wp_pures.
  wp_load. wp_match. wp_proj. wp_store.
  
  wp_rec. wp_load. wp_match. do 2wp_proj.
  wp_rec. wp_pures. wp_rec.
  wp_load ; wp_match ; wp_proj.
  wp_pures.

  wp_rec. wp_load ; wp_match ; wp_proj.
  wp_pures. wp_rec. wp_load ; wp_match ; wp_proj.
  wp_store. wp_rec. wp_load ; wp_match ; wp_proj.

  wp_pures. wp_rec. wp_load ; wp_match ; wp_proj.
  wp_store. wp_store.

  wp_rec. wp_let. 

  wp_load.
  wp_let. 
  unfold value. wp_load. wp_match.
  wp_proj. unfold splay_compare.
  wp_pures. wp_lam. wp_load. wp_match. do 2 wp_proj.
  wp_load. wp_match. wp_proj.
  wp_lam. wp_let. wp_op ; wp_if. wp_op ; wp_if.
  wp_let. wp_op ; wp_if. wp_op ; wp_if.

  wp_pures. wp_rec. wp_load.
  wp_match. do 2 wp_proj. wp_op ; wp_if.
  wp_op ; wp_if. wp_op. wp_if. wp_op ; wp_if. wp_if.
  wp_op ; wp_if. wp_op ; wp_if.
  wp_lam.

  wp_pures. wp_load. wp_match. do 2wp_proj.
  wp_pures. wp_rec.

  wp_load ; wp_match ; repeat wp_proj.
  wp_alloc sdf as "Hpp2".
  wp_rec.
  wp_let. wp_let. wp_rec. wp_load ; wp_match.
  do 2wp_proj. wp_let. wp_rec. wp_load ; wp_match.
  do 2wp_proj. wp_pures. wp_rec. wp_load ; wp_match.
  wp_proj. wp_store. wp_rec. wp_load.
  wp_pures. wp_rec. wp_load. wp_match.
  wp_proj. wp_store. wp_store.
  wp_rec. wp_load. wp_match.
  do 2wp_proj. wp_pures.
  wp_load. wp_match. wp_proj. wp_store.
  
  wp_rec. wp_load. wp_match. do 2wp_proj.
  wp_rec. wp_pures. wp_rec.
  wp_load ; wp_match ; wp_proj.
  wp_pures.

  wp_rec. wp_load ; wp_match ; wp_proj.
  wp_pures. wp_rec. wp_load ; wp_match ; wp_proj.
  wp_store. wp_rec. wp_load ; wp_match ; wp_proj.
  wp_pures. wp_rec. wp_load ; wp_match ; wp_proj.

  wp_store. wp_store.

  wp_rec. wp_pures.
  wp_load ; wp_pures.
  wp_load ; wp_match ; wp_proj.
  wp_pures.

  wp_rec. wp_load ; wp_match ; wp_proj.
  wp_proj ; wp_pures.
  wp_load ; wp_match ; wp_proj.
  wp_pures.

  wp_rec ; wp_load ; wp_match ; wp_proj.
  wp_proj ; wp_pures.
  wp_rec ; wp_pures. wp_rec.
  wp_load ; wp_match ; repeat wp_proj.
  wp_pures.

  wp_rec ; wp_pures. 
  wp_load ; wp_match ; repeat wp_proj.

  wp_pures.  wp_rec.
  wp_load ; wp_match ; repeat wp_proj.
  wp_store.
  
  wp_pures.  wp_rec.
  wp_load ; wp_match ; repeat wp_proj.

  wp_pures ; wp_rec ; wp_pures. 
  wp_load ; wp_match ; repeat wp_proj.

  wp_store. wp_store.

  iApply "H". iFrame.
  
Qed.


Lemma ex6 `{!heapG Σ} (pp p p1 p2 p3 p4 : loc) (pv : val) :
  {{{ pp ↦ #p ∗
         p ↦ (SOMEV (#4, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#2, (NONEV, NONEV))) ∗
         p2 ↦ (SOMEV (#6, (NONEV, #p3))) ∗
         p3 ↦ (SOMEV (#10, (NONEV, NONEV))) ∗
         p4 ↦ (SOMEV (#7, (NONEV, NONEV)))
  }}}
    splay_tree_insert #pp #p4
    {{{ RET #() ;
        pp ↦ #p4 ∗
           p ↦ (SOMEV (#4, (#p1, NONEV))) ∗
           p1 ↦ (SOMEV (#2, (NONEV, NONEV))) ∗
                     p2 ↦ (SOMEV (#6, (#p, NONEV))) ∗
                     p3 ↦ (SOMEV (#10, (NONEV, NONEV))) ∗
                     p4 ↦ (SOMEV (#7, (#p2, #p3)))
    }}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 [Hp2 [Hp3 Hp4]]]]] H".
  wp_rec. wp_let.
  wp_rec. wp_load ; wp_match ; wp_proj.
  wp_bind (splay_tree_splay #pp #7).
  iCombine "Hpp Hp Hp1 Hp2 Hp3" as "All".
  wp_apply (ex5 with "All") ; auto.
  iIntros "[Hpp [Hp [Hp1 [Hp2 Hp3]]]]". wp_seq.
  wp_load. wp_pures. wp_rec. wp_load.
  wp_load. wp_rec. wp_load. wp_match. wp_proj.
  wp_rec. wp_pures. wp_load. wp_op.
  wp_op. wp_if. wp_op ; wp_if. wp_load.
  wp_op. wp_if. wp_op. wp_if.
  wp_pures. wp_load. wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_rec. wp_load ; wp_match ; wp_proj.
  wp_store. wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_rec. wp_load ; wp_match ; do 2wp_proj. 
  wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_rec. 
  wp_load ; wp_match ; wp_proj.
  wp_store.
  wp_rec. wp_load. wp_match.
  do 2wp_proj. wp_rec.

  wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_rec. 
  wp_load ; wp_match ; do 2wp_proj.
  wp_rec. 
  wp_load ; wp_match ; wp_proj.
  wp_pures. wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_store. wp_store. iApply "H".
  iFrame.  
Qed.

Lemma ex3 `{!heapG Σ} (pp p  p1 p2 : loc) :
  {{{ pp ↦ #p ∗
         p ↦ (SOMEV (#3, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#1, (NONEV, NONEV))) ∗
         p2 ↦ (SOMEV (#5, (NONEV, NONEV)))  }}}
    splay_tree_splay #pp #6
    {{{ RET #() ; pp ↦ #p2 ∗ p1 ↦ (SOMEV (#1, (NONEV, NONEV))) ∗ p ↦ (SOMEV (#3, (#p1, NONEV)))
                   ∗ p2 ↦ (SOMEV (#5, (#p, NONEV)))}}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 Hp2]]] H".
  wp_rec. wp_let.
  wp_load. wp_op. wp_if. wp_pures.
  wp_load.
  wp_let. 
  unfold value. wp_load. wp_match.
  wp_proj. unfold splay_compare.
  wp_pures. wp_lam. wp_load. wp_match. do 2 wp_proj.
  wp_load. wp_pures.
  wp_lam. wp_pures. wp_load.
  wp_match. do 2wp_proj.
  wp_op ; wp_if. wp_op ; wp_if.
  wp_rec. wp_pures. wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_rec. wp_load ; wp_match ; wp_proj.
  wp_store. wp_rec. wp_load ; wp_match ; do 2wp_proj.
  wp_pures. wp_rec. wp_load ; wp_match ; wp_proj.
  wp_store. wp_store. iApply "H". iFrame.
Qed.

Lemma ex3 `{!heapG Σ} (pp p  p1 p2 : loc) :
  {{{ pp ↦ #p ∗
         p ↦ (SOMEV (#3, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#1, (NONEV, NONEV))) ∗
         p2 ↦ (SOMEV (#5, (NONEV, NONEV)))  }}}
    splay_tree_splay #pp #5
    {{{ RET #() ; pp ↦ #p2 ∗ p1 ↦ (SOMEV (#1, (NONEV, NONEV))) ∗ p ↦ (SOMEV (#3, (#p1, NONEV)))
                   ∗ p2 ↦ (SOMEV (#5, (#p, NONEV)))}}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 Hp2]]] H".
  wp_rec. wp_let.
  wp_load. wp_op. wp_if. wp_pures.
  wp_load.
  wp_let. 
  unfold value. wp_load. wp_match.
  wp_proj. unfold splay_compare.
  wp_pures. wp_lam. wp_load. wp_match. do 2 wp_proj.
  wp_load. wp_pures.
  wp_lam. wp_pures. wp_rec. wp_load. wp_match.
  do 2wp_proj. wp_let. wp_rec. wp_load ; wp_match ; wp_proj.
  wp_pures. wp_rec. wp_load ; wp_match ; wp_proj. wp_pures.
  wp_store. wp_rec. wp_load. wp_match ; do 2wp_proj.
  wp_pures. wp_rec. wp_load. wp_match. wp_proj.
  wp_store. wp_store. iApply "H". iFrame.
Qed.

Lemma ex1 `{!heapG Σ} (pp p p1 p2 : loc) (pv : val) :
  {{{ pp ↦ #p ∗ p ↦ (SOMEV (#3, (#p1, #p2))) ∗
         p ↦ (SOMEV (#3, (#p1, #p2))) ∗
         p1 ↦ (SOMEV (#1, (NONEV, NONEV))) ∗
         p2 ↦ (SOMEV (#5, (NONEV, NONEV))) }}}
    splay_tree_splay #pp #0
    {{{ RET #() ; pp ↦ #p1 ∗ p1 ↦ (SOMEV (#1, (NONEV, #p))) ∗ p ↦ (SOMEV (#3, (NONEV, #p2)))
                   ∗ p2 ↦ (SOMEV (#5, (NONEV, NONEV))) }}}.
Proof.
  iIntros (Φ) "[Hpp [Hp [Hp1 [Hp2 Hpn]]]] H".
  wp_rec. wp_let.
  wp_load. wp_op. wp_if. wp_pures.

  wp_load.
  wp_let. 
  unfold value. wp_load. wp_match.
  wp_proj. unfold splay_compare.
  wp_pures. wp_lam. wp_load. wp_match. do 2 wp_proj. wp_pures.
  wp_load. wp_match. wp_proj.
  wp_lam. wp_let. wp_op ; wp_if. wp_op ; wp_if.
  wp_let. wp_op ; wp_if. wp_op ; wp_if.

  wp_pures. wp_rec. wp_load.
  wp_match. do 2 wp_proj. wp_op ; wp_if.
  wp_if. wp_op ; wp_if. wp_lam.
  wp_let. wp_let. wp_rec. wp_load ; wp_match.
  do 2wp_proj. wp_let. wp_rec.
  wp_load ; wp_match ; repeat wp_proj.
  wp_pures. wp_rec. 
  wp_load ; wp_match ; repeat wp_proj.
  wp_store.
  wp_pures. wp_rec.
  wp_load ; wp_match ; repeat wp_proj.
  wp_pures. wp_rec.
  wp_load ; wp_match ; repeat wp_proj.
  wp_store. wp_store. iApply "H". iFrame.
Qed.

