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

Section SplaySubCasesRoot.

  Context `{!tctrHeapG Σ} (nmax : nat).

  Variable v : val.
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* data stored in nodes *)
  Variable M : gmap elem content.       (* data stored in nodes *)

  Lemma splay_root_st F (pp p : loc) (k : Z) (n : nat) :
    Inv p D F V W ->
    Mem D F V M -> 
    {{{ pp ↦ #p ∗ mapsto_M M }}}
      splay_tree_while_loop #pp #(V p)
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
    
    destruct c ; unpack ; subst ; simpl in H1 ; inversion H1 ; subst ;

      wp_bind (value #p) ;
      iApply (value_specification with "[Hp]") ; auto ;
        iModIntro ; iIntros "Hp" ;
          
          wp_bind (splay_compare #(V p) #(V p)) ;
          iApply (splay_compare_specification_eq) ; auto ;
            iModIntro ; iIntros ;
              wp_pures ;

              iApply "H" ; iFrame ;
                iDestruct ("M" with "Hp") as "M" ;
                iFrame ; iSplit ; auto.              
  Qed.
  
End SplaySubCasesRoot.
