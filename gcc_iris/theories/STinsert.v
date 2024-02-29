From iris.bi Require Import big_op.
From iris_time.heap_lang Require Import proofmode.
From iris_time Require Import Combined.

From ST Require Import Code STorientation 
     STpredicate STpath STedgeset STedgesetrotateroot STvaluefunction
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
     STsplaycases_ir STir STsplay STedgesetinsert.

From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual
     LibInt.

Section InsertSpecification.

  Context `{!tctrHeapG Σ} (nmax : nat).
    
  Lemma insert_st : forall n (p :elem) D V W pp (v : Z),
      {{{ pp ↦ #p ∗ n ↦ SOMEV (#v,(NONEV, NONEV)) ∗ ST p D V W
             ∗ ⌜n \notin D⌝
             ∗ ⌜¬(exists n', n' \in D /\ V n' = v)⌝ }}}
      splay_tree_insert #pp #n
    {{{ RET #() ; pp ↦ #n ∗ ST n (D \u \{n}) (update_value V n v) W }}}.
  Proof.
    intros.
    iIntros "[Hpp [N [ST %]]] Hf". destruct H as [H Hnexists].
    rename H into HnNotInD.
    unfold ST. iDestruct "ST" as (F M) "[% [% M]]".
    wp_rec. wp_pures.

    wp_bind (value #n).
    iApply (value_specification n (NONEV, NONEV) v with "[N]"). iApply "N".
    iModIntro. iIntros "Hn".

    wp_bind (splay_tree_splay #pp #v).    
    iPoseProof (splay_st' 0 p D F V W pp v M) as "SSt" ; auto.
    iApply ("SSt" with "[Hpp M]"). 
    unfold ST ; iFrame. iModIntro.
    iIntros (M' F' p') "[Hpp [% [% [M %]]]]".

    wp_pures.
    wp_load. wp_pures.

    wp_bind (value #n).
    iApply (value_specification n (NONEV, NONEV) v with "[Hn]") ; iFrame.
    iModIntro. iIntros "Hn".

    wp_load.
    assert (p' \in D). stdomain_tac.

    apply H2 in H4.
    destruct (M' !! p') eqn:E2 ; try contradiction.

    destruct c ; unpack.
    + iPoseProof (mapsto_M_acc M' p' (NodeB z l l0) E2 with "M") as "M".
      iDestruct "M" as (v') "[% [Hp M]]".
      simpl in H6. inversion H7 ; subst.

      (* Get value of node *)
      wp_bind (value #p').    
      iApply (value_specification with "[Hp]") ; auto.
      iModIntro. iIntros "Hp".
      pose proof (Z.lt_trichotomy (V p') v).
      destruct H6 as [H6 | [H6 | H6]].
      (* 1 . 1 *)
      - wp_bind (splay_compare #(V p') #v).
        iApply (splay_compare_specification_lt) ; auto.
        iPureIntro. rewrite lt_zarith. auto. 
        iModIntro ; iIntros ; wp_pures.

        wp_load. wp_pures. wp_load. wp_pures.

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". wp_load.

        (* Get value of node *) wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (right_child #p').    
        iApply (right_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp".
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".

        wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (left_child #p').    
        iApply (left_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp". wp_pures.
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".
        
        wp_bind (value #p').    
        iApply (value_specification with "[Hp]") ; auto.
        iModIntro. iIntros "Hp".

        wp_pures.
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".

        wp_store. wp_pures. wp_store.
        iApply "Hf". 
        iFrame.

        (*save in memory*)
        iAssert
          (bi_pure (val_of_content (NodeL (V p') l) = Some (InjRV (#(V p'), (#l, InjLV #())))))
            as "H1". iPureIntro. auto. 
        iDestruct ("M" with "[H1] [Hp]") as "M" ; auto.
        iExists (remove_edge (add_edge (add_edge F' n p' LEFT) n l0 RIGHT) p' l0),
        ((<[n:=NodeB v p' l0]> (<[p':=NodeL (V p') l]>M'))).
        iSplit. iPureIntro.
        pose proof (insert_if_bst p' D W V F' l0 n RIGHT v).
        simpl in H9. apply H9 ; auto.
        iSplit. iPureIntro.
        unfold Mem. intros. apply in_union_inv in H9.        
        destruct H9.
        * rewrite lookup_insert_ne.
          destruct (classic (p' = x)) ; subst.
          { rewrite lookup_insert.
            split.
            + split. right. intro. subst. stlink_tac.
              left. left. auto.
            + split.
              - intro. destruct H10. destruct H10.
                destruct H11 ; unpack ; subst.
                { destruct H11 ; unpack ; subst ; try discriminate.
                  destruct H10 ; try contradiction.
                  apply H10. stlink_tac.
                }
                contradiction.
              - unfold update_value.
                destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                apply bool_decide_eq_true_1 in E. subst. contradiction.
          }
          { rewrite lookup_insert_ne.
            pose proof H9 as HxInDomain.
            apply H2 in H9.
            destruct (M' !! x) ; try contradiction ; auto.
            destruct c ; unpack ; subst ; try auto.
            + split.
              - split. left. intro. subst. contradiction.
                left. left. auto.
              - split.
                * split. left. intro ; subst. contradiction.
                  left. left. auto.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - split. left. intro. subst. contradiction.
                left. left. auto.
              - split.
                * intro. do 3destruct H12.
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; try discriminate.
                    eauto.
                  }
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; try discriminate.
                    eauto.
                  }                  
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - split. left. intro. subst. contradiction.
                left. left. auto.
              - split.
                * intro. do 3destruct H12.
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    eauto.
                  }
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    eauto.
                  }                  
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              * intro. do 3destruct H12.
                { destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                  destruct H13 ; unpack ; subst ; try discriminate. 
                  eauto.
                }
                { destruct H13 ; unpack ; subst ; try contradiction.
                  destruct H13 ; unpack ; subst ; try discriminate.
                  eauto.
                }                  
              * split.
                { intro. do 3destruct H12.
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                    eauto.
                  }
                  { destruct H13 ; unpack ; subst ; try contradiction.
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                    eauto.
                  }
                }
                {
                  unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. auto.
                }
            + auto.
          }
          { intro. subst. auto. }
         * rewrite set_in_single_eq in H9. subst.
          rewrite lookup_insert. repeat split ; auto.
          { left. intro. subst. apply HnNotInD. stdomain_tac. }
          { left. right. auto. }
          { left. intro. subst. apply HnNotInD. stdomain_tac. }
          { right. auto. }
          { unfold update_value. destruct (bool_decide (n = n)) eqn:E ; auto.
            apply bool_decide_eq_false_1 in E. contradiction. }
         * iAssert (bi_pure ((<[p':=NodeL (V p') l]> M') !! n = None%I)) as %Mx.
           { case HMx: ((<[p':=NodeL (V p') l]> M')!!n)=>//.
             iDestruct (big_sepM_lookup with "M") as "Hx'"=>//.
             destruct val_of_content; try done.             
             destruct val_of_content; try done.             
             destruct val_of_content; try done.             
               by iDestruct (mapsto_valid_2 with "Hn Hx'") as %[]. 
               destruct val_of_content; try done.             
                 by iDestruct (mapsto_valid_2 with "Hn Hx'") as %[]. }                    
           iApply mapsto_M_insert; [| |by iFrame] ; auto.
      (* 1 . 2 *)
      - subst. exfalso ; apply Hnexists. exists p'.
        split ; stdomain_tac ; auto.
      (* 1 . 3 *)
      - wp_bind (splay_compare #(V p') #v).
        iApply (splay_compare_specification_gt) ; auto.
        iPureIntro. rewrite gt_zarith. lia.
        iModIntro ; iIntros ; wp_pures.

        wp_load. wp_pures. wp_load. wp_pures.
        wp_load.
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        (* Get value of node *) wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".
        
        wp_bind (left_child #p').    
        iApply (left_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp".

        wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (right_child #p').    
        iApply (right_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp". wp_pures.
        
        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".
        
        wp_bind (value #p').    
        iApply (value_specification with "[Hp]") ; auto.
        iModIntro. iIntros "Hp".

        wp_pures.
        
        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".

        wp_store. wp_pures. wp_store.
        iApply "Hf". 
        iFrame.

        (*save in memory*)
        iAssert
          (bi_pure (val_of_content (NodeR (V p') l0) = Some (InjRV (#(V p'), (InjLV #(), #l0)))))
            as "H1". iPureIntro. auto. 
        iDestruct ("M" with "[H1] [Hp]") as "M" ; auto.
        iExists (remove_edge (add_edge (add_edge F' n p' RIGHT) n l LEFT) p' l),
        ((<[n:=NodeB v l p']> (<[p':=NodeR (V p') l0]> M'))).
        iSplit. iPureIntro.
        pose proof (insert_if_bst p' D W V F' l n LEFT v).
        simpl in H9. apply H9 ; auto. lia. 
        iSplit. iPureIntro.
        unfold Mem. intros. apply in_union_inv in H9.        
        destruct H9.
        * rewrite lookup_insert_ne.
          destruct (classic (p' = x)) ; subst.
          { rewrite lookup_insert.
            split.
            + split. right. intro. subst. stlink_tac.
              left. left. auto.
            + split.
              - intro. destruct H10. destruct H10.
                destruct H11 ; unpack ; subst.
                { destruct H11 ; unpack ; subst ; try discriminate.
                  destruct H10 ; try contradiction.
                  apply H10. stlink_tac.
                }
                contradiction.
              - unfold update_value.
                destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                apply bool_decide_eq_true_1 in E. subst. contradiction.
          }
          { rewrite lookup_insert_ne ; auto.
            pose proof H9 as HxInDomain.
            apply H2 in H9.
            destruct (M' !! x) ; try contradiction ; auto.
            destruct c ; unpack ; subst ; try auto.
            + split.
              - split. left. intro. subst. contradiction.
                left. left. auto.
              - split.
                * split. left. intro ; subst. contradiction.
                  left. left. auto.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - split. left. intro. subst. contradiction.
                left. left. auto.
              - split.
                * intro. do 3destruct H12.
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    eauto.
                  }
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    eauto.
                  }                  
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - split. left. intro. subst. contradiction.
                left. left. auto.
              - split.
                * intro. do 3destruct H12.
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    eauto.
                  }
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    eauto.
                  }                  
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              * intro. do 3destruct H12.
                { destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                  destruct H13 ; unpack ; subst ; try contradiction. 
                  eauto.
                }
                { destruct H13 ; unpack ; subst ; try contradiction.
                  destruct H13 ; unpack ; subst ; try contradiction.
                  eauto.
                }                  
              * split.
                { intro. do 3destruct H12.
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                    eauto.
                  }
                  { destruct H13 ; unpack ; subst ; try contradiction.
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                    eauto.
                  }
                }
                {
                  unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. auto.
                }
          }
          { intro. subst. auto. }
         * rewrite set_in_single_eq in H9. subst.
          rewrite lookup_insert. repeat split ; auto.
          { left. intro. subst. apply HnNotInD. stdomain_tac. }
          { right. auto. }
          { left. intro. subst. apply HnNotInD. stdomain_tac. }
          { left. right. auto. }
          { unfold update_value. destruct (bool_decide (n = n)) eqn:E ; auto.
            apply bool_decide_eq_false_1 in E. contradiction. }
         * iAssert (bi_pure ((<[p':=NodeR (V p') l0]> M') !! n = None%I)) as %Mx.
           { case HMx: ((<[p':=NodeR (V p') l0]> M')!!n)=>//.
             iDestruct (big_sepM_lookup with "M") as "Hx'"=>//.
             destruct val_of_content; try done.             
             destruct val_of_content; try done.             
             destruct val_of_content; try done.             
               by iDestruct (mapsto_valid_2 with "Hn Hx'") as %[]. 
               destruct val_of_content; try done.             
                 by iDestruct (mapsto_valid_2 with "Hn Hx'") as %[]. }                    
           iApply mapsto_M_insert; [| |by iFrame] ; auto.
    + iPoseProof (mapsto_M_acc M' p' (NodeL z l) E2 with "M") as "M".
      iDestruct "M" as (v') "[% [Hp M]]".
      simpl in H6. inversion H7 ; subst.

      (* Get value of node *)
      wp_bind (value #p').    
      iApply (value_specification with "[Hp]") ; auto.
      iModIntro. iIntros "Hp".
      pose proof (Z.lt_trichotomy (V p') v).
      destruct H6 as [H6 | [H6 | H6]].
      (* 1 . 1 *)
      - wp_bind (splay_compare #(V p') #v).
        iApply (splay_compare_specification_lt) ; auto.
        iPureIntro. rewrite lt_zarith. auto. 
        iModIntro ; iIntros ; wp_pures.

        wp_load. wp_pures. wp_load. wp_pures.

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". wp_load.

        (* Get value of node *) wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (right_child #p').    
        iApply (right_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp".
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".

        wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (left_child #p').    
        iApply (left_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp". wp_pures.
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".
        
        wp_bind (value #p').    
        iApply (value_specification with "[Hp]") ; auto.
        iModIntro. iIntros "Hp".

        wp_pures.
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".

        wp_store. wp_pures. wp_store.
        iApply "Hf". 
        iFrame.

        (*save in memory*)
        iAssert
          (bi_pure (val_of_content (NodeL (V p') l) = Some (InjRV (#(V p'), (#l, InjLV #())))))
            as "H1". iPureIntro. auto. 
        iDestruct ("M" with "[H1] [Hp]") as "M" ; auto.
        iExists (add_edge F' n p' LEFT),
        ((<[n:=NodeL v p']> (<[p':=NodeL (V p') l]> M'))).
        iSplit. iPureIntro.
        pose proof (insert'_if_bst p' D W V F' n RIGHT v).
        simpl in H9. apply H9 ; auto.
        iSplit. iPureIntro.
        unfold Mem. intros. apply in_union_inv in H9.        
        destruct H9.
        * rewrite lookup_insert_ne.
          destruct (classic (p' = x)) ; subst.
          { rewrite lookup_insert.
            split.
            + left. auto.
            + split.
              - intro. destruct H10. destruct H10 ; unpack ; try discriminate.
                eauto.
              - unfold update_value.
                destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                apply bool_decide_eq_true_1 in E. subst. contradiction.
          }
          { rewrite lookup_insert_ne.
            pose proof H9 as HxInDomain.
            apply H2 in H9.
            destruct (M' !! x) ; try contradiction ; auto.
            destruct c ; unpack ; subst ; try auto.
            + split.
              - left. auto.
              - split.
                * left. auto.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - left. auto.
              - split.
                * intro. do 2destruct H12 ; eauto.
                  unpack ; discriminate.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - left. auto.
              - split.
                * intro. do 2destruct H12 ; eauto.
                  unpack ; subst. apply HnNotInD. eauto.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              * intro. do 2destruct H12 ; eauto.
                unpack ; discriminate.
              * split.
                { intro. do 2destruct H12 ; eauto.
                  unpack ; subst. apply HnNotInD. eauto.
                }
                {
                  unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. auto.
                }
            + auto.
          }
          { intro. subst. auto. }
         * rewrite set_in_single_eq in H9. subst.
          rewrite lookup_insert. repeat split ; auto.
          { right. auto. }
          { intro. destruct H9. destruct H9 ; unpack ; subst ; try discriminate.
            apply HnNotInD. stdomain_tac. }
          { unfold update_value. destruct (bool_decide (n = n)) eqn:E ; auto.
            apply bool_decide_eq_false_1 in E. contradiction. }
         * iAssert (bi_pure ((<[p':=NodeL (V p') l]> M') !! n = None%I)) as %Mx.
           { case HMx: ((<[p':=NodeL (V p') l]> M')!!n)=>//.
             iDestruct (big_sepM_lookup with "M") as "Hx'"=>//.
             destruct val_of_content; try done.             
             destruct val_of_content; try done.             
               by iDestruct (mapsto_valid_2 with "Hn Hx'") as %[].  }                    
           iApply mapsto_M_insert; [| |by iFrame] ; auto.
      (* 1 . 2 *)
      - subst. exfalso ; apply Hnexists. exists p'.
        split ; stdomain_tac ; auto.
      (* 1 . 3 *)
      - wp_bind (splay_compare #(V p') #v).
        iApply (splay_compare_specification_gt) ; auto.
        iPureIntro. rewrite gt_zarith. lia.
        iModIntro ; iIntros ; wp_pures.

        wp_load. wp_pures. wp_load. wp_pures.
        wp_load.
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        (* Get value of node *) wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".
        
        wp_bind (left_child #p').    
        iApply (left_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp".

        wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (right_child #p').    
        iApply (right_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp". wp_pures.
        
        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".
        
        wp_bind (value #p').    
        iApply (value_specification with "[Hp]") ; auto.
        iModIntro. iIntros "Hp".

        wp_pures.
        
        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".

        wp_store. wp_pures. wp_store.
        iApply "Hf". 
        iFrame.

        (*save in memory*)
        iAssert
          (bi_pure (val_of_content (NodeN (V p')) = Some (InjRV (#(V p'), (InjLV #(), InjLV #())))))
            as "H1". iPureIntro. auto. 
        iDestruct ("M" with "[H1] [Hp]") as "M" ; auto.
        iExists (remove_edge (add_edge (add_edge F' n p' RIGHT) n l LEFT) p' l),
        ((<[n:=NodeB v l p']> (<[p':=NodeN (V p')]> M'))).
        iSplit. iPureIntro.
        pose proof (insert_if_bst p' D W V F' l n LEFT v).
        simpl in H9. apply H9 ; auto. lia. 
        iSplit. iPureIntro.
        unfold Mem. intros. apply in_union_inv in H9.        
        destruct H9.
        * rewrite lookup_insert_ne.
          destruct (classic (p' = x)) ; subst.
          { rewrite lookup_insert.
            split.
            + intro. destruct H10. destruct H10.
              destruct H11 ; unpack ; subst.
              { destruct H11 ; unpack ; subst ; try discriminate. eauto.
                destruct H10 ; try contradiction.
              }
              contradiction.
            + split.
              - intro. destruct H10. destruct H10.
                destruct H11 ; unpack ; subst.
                { destruct H11 ; unpack ; subst ; try discriminate.
                  destruct H10 ; try contradiction.
                  apply H10. stlink_tac.
                }
                contradiction.
              - unfold update_value.
                destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                apply bool_decide_eq_true_1 in E. subst. contradiction.
          }
          { rewrite lookup_insert_ne.
            pose proof H9 as HxInDomain.
            apply H2 in H9.
            destruct (M' !! x) ; try contradiction ; auto.
            destruct c ; unpack ; subst ; try auto.
            + split.
              - split. left. intro. subst. contradiction.
                left. left. auto.
              - split.
                * split. left. intro ; subst. contradiction.
                  left. left. auto.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - split. left. intro. subst. contradiction.
                left. left. auto.
              - split.
                * intro. do 3destruct H12.
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    eauto.
                  }
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    eauto.
                  }                  
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - split. left. intro. subst. contradiction.
                left. left. auto.
              - split.
                * intro. do 3destruct H12.
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    eauto.
                  }
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    eauto.
                  }                  
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              * intro. do 3destruct H12.
                { destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                  destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                  eauto.
                }
                { destruct H13 ; unpack ; subst ; try contradiction.
                  destruct H13 ; unpack ; subst ; eauto.
                }                  
              * split.
                { intro. do 3destruct H12.
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                    eauto.
                  }
                  { destruct H13 ; unpack ; subst ; try contradiction.
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                    eauto.
                  }
                }
                {
                  unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. auto.
                }
            + auto.
          }
          { intro. subst. auto. }
         * rewrite set_in_single_eq in H9. subst.
          rewrite lookup_insert. repeat split ; auto.
          { left. intro. subst. apply HnNotInD. stdomain_tac. }
          { right. auto. }
          { left. intro. subst. apply HnNotInD. stdomain_tac. }
          { left. right. auto. }
          { unfold update_value. destruct (bool_decide (n = n)) eqn:E ; auto.
            apply bool_decide_eq_false_1 in E. contradiction. }
         * iAssert (bi_pure ((<[p':=NodeN (V p')]> M') !! n = None%I)) as %Mx.
           { case HMx: ((<[p':=NodeN (V p')]> M')!!n)=>//.
             iDestruct (big_sepM_lookup with "M") as "Hx'"=>//.
             destruct val_of_content; try done.             
             destruct val_of_content; try done.             
             destruct val_of_content; try done.             
               by iDestruct (mapsto_valid_2 with "Hn Hx'") as %[]. 
               destruct val_of_content; try done.             
                 by iDestruct (mapsto_valid_2 with "Hn Hx'") as %[]. }                    
           iApply mapsto_M_insert; [| |by iFrame] ; auto.
     + iPoseProof (mapsto_M_acc M' p' (NodeR z l) E2 with "M") as "M".
       iDestruct "M" as (v') "[% [Hp M]]".
       simpl in H6. inversion H7 ; subst.

       (* Get value of node *)
       wp_bind (value #p').    
       iApply (value_specification with "[Hp]") ; auto.
       iModIntro. iIntros "Hp".
       pose proof (Z.lt_trichotomy (V p') v).
       destruct H6 as [H6 | [H6 | H6]].
      (* 1 . 1 *)
      - wp_bind (splay_compare #(V p') #v).
        iApply (splay_compare_specification_lt) ; auto.
        iPureIntro. rewrite lt_zarith. auto. 
        iModIntro ; iIntros ; wp_pures.

        wp_load. wp_pures. wp_load. wp_pures.

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". wp_load.

        (* Get value of node *) wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (right_child #p').    
        iApply (right_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp".
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".

        wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (left_child #p').    
        iApply (left_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp". wp_pures.
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".
        
        wp_bind (value #p').    
        iApply (value_specification with "[Hp]") ; auto.
        iModIntro. iIntros "Hp".

        wp_pures.
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".

        wp_store. wp_pures. wp_store.
        iApply "Hf". 
        iFrame.

        (*save in memory*)
        iAssert
          (bi_pure (val_of_content (NodeN (V p')) = Some (InjRV (#(V p'), (InjLV #(), InjLV #())))))
          as "H1". iPureIntro. auto. 
        iDestruct ("M" with "[H1] [Hp]") as "M" ; auto.
        iExists (remove_edge (add_edge (add_edge F' n p' LEFT) n l RIGHT) p' l),
        ((<[n:=NodeB v p' l]> (<[p':=NodeN (V p')]> M'))).
        iSplit. iPureIntro.
        pose proof (insert_if_bst p' D W V F' l n RIGHT v).
        simpl in H9. apply H9 ; auto. 
        iSplit. iPureIntro.
        unfold Mem. intros. apply in_union_inv in H9.        
        destruct H9.
        * rewrite lookup_insert_ne.
          destruct (classic (p' = x)) ; subst.
          { rewrite lookup_insert.
            split.
            + intro. destruct H10. destruct H10 ; unpack ; try discriminate.
              destruct H11 ; unpack ; subst ; [|lia].
              destruct H11 ; unpack ; subst ; try discriminate.
              destruct H10 ; apply H10 ; stlink_tac ; auto.
            + split.
              - intro. destruct H10. destruct H10 ; unpack ; try discriminate.
                destruct H11 ; unpack ; subst ; [|lia].
                destruct H11 ; unpack ; subst ; try contradiction.
                destruct H10 ; try contradiction. eauto.
              - unfold update_value.
                destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                apply bool_decide_eq_true_1 in E. subst. contradiction.
          }
          { rewrite lookup_insert_ne.
            pose proof H9 as HxInDomain.
            apply H2 in H9.
            destruct (M' !! x) ; try contradiction ; auto.
            destruct c ; unpack ; subst ; try auto.
            + split.
              - split. left. intro. subst. contradiction.
                left. left. auto.
              - split.
                * split. left. intro ; subst. contradiction.
                  left. left. auto.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - split. left. intro. subst. contradiction.
                left. left. auto.
              - split.
                * intro. do 3destruct H12.
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; try discriminate.
                    eauto.
                  }
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; try discriminate.
                    eauto.
                  }                  
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - split. left. intro. subst. contradiction.
                left. left. auto.
              - split.
                * intro. do 3destruct H12.
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    eauto.
                  }
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ; stdomain_tac].
                    eauto.
                  }                  
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              * intro. do 3destruct H12.
                { destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                  destruct H13 ; unpack ; subst ; try discriminate. 
                  eauto.
                }
                { destruct H13 ; unpack ; subst ; try contradiction.
                  destruct H13 ; unpack ; subst ; try discriminate.
                  eauto.
                }                  
              * split.
                { intro. do 3destruct H12.
                  { destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                    eauto.
                  }
                  { destruct H13 ; unpack ; subst ; try contradiction.
                    destruct H13 ; unpack ; subst ; [|apply HnNotInD ;auto].
                    eauto.
                  }
                }
                {
                  unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. auto.
                }
            + auto.
          }
          { intro. subst. auto. }
         * rewrite set_in_single_eq in H9. subst.
          rewrite lookup_insert. repeat split ; auto.
          { left. intro. subst. apply HnNotInD. stdomain_tac. }
          { left. right. auto. }
          { left. intro. subst. apply HnNotInD. stdomain_tac. }
          { right. auto. }
          { unfold update_value. destruct (bool_decide (n = n)) eqn:E ; auto.
            apply bool_decide_eq_false_1 in E. contradiction. }
         * iAssert (bi_pure ((<[p':=NodeN (V p')]> M') !! n = None%I)) as %Mx.
           { case HMx: ((<[p':=NodeN (V p')]> M')!!n)=>//.
             iDestruct (big_sepM_lookup with "M") as "Hx'"=>//.
             destruct val_of_content; try done.             
             destruct val_of_content; try done.             
             destruct val_of_content; try done.             
               by iDestruct (mapsto_valid_2 with "Hn Hx'") as %[]. 
               destruct val_of_content; try done.             
                 by iDestruct (mapsto_valid_2 with "Hn Hx'") as %[]. }                    
           iApply mapsto_M_insert; [| |by iFrame] ; auto.
      (* 1 . 2 *)
      - subst. exfalso ; apply Hnexists. exists p'.
        split ; stdomain_tac ; auto.
      (* 1 . 3 *)
      - wp_bind (splay_compare #(V p') #v).
        iApply (splay_compare_specification_gt) ; auto.
        iPureIntro. rewrite gt_zarith. lia.
        iModIntro ; iIntros ; wp_pures.

        wp_load. wp_pures. wp_load. wp_pures.
        wp_load.
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        (* Get value of node *) wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".
        
        wp_bind (left_child #p').    
        iApply (left_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp".

        wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (right_child #p').    
        iApply (right_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp". wp_pures.
        
        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".
        
        wp_bind (value #p').    
        iApply (value_specification with "[Hp]") ; auto.
        iModIntro. iIntros "Hp".

        wp_pures.
        
        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".

        wp_store. wp_pures. wp_store.
        iApply "Hf". 
        iFrame.

        (*save in memory*)
        iAssert
          (bi_pure (val_of_content (NodeR (V p') l) = Some (InjRV (#(V p'), (InjLV #(), #l)))))
          as "H1". iPureIntro. auto. 
        iDestruct ("M" with "[H1] [Hp]") as "M" ; auto.
        iExists (add_edge F' n p' RIGHT),
        ((<[n:=NodeR v p']> (<[p':=NodeR (V p') l]> M'))).
        iSplit. iPureIntro.
        pose proof (insert'_if_bst p' D W V F' n LEFT v).
        simpl in H9. apply H9 ; auto. lia.
        iSplit. iPureIntro.
        unfold Mem. intros. apply in_union_inv in H9.        
        destruct H9.
        * rewrite lookup_insert_ne.
          destruct (classic (p' = x)) ; subst.
          { rewrite lookup_insert.
            split.
            + left. auto.
            + split.
              - intro. destruct H10. destruct H10 ; unpack ; try discriminate.
                eauto.
              - unfold update_value.
                destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                apply bool_decide_eq_true_1 in E. subst. contradiction.
          }
          { rewrite lookup_insert_ne.
            pose proof H9 as HxInDomain.
            apply H2 in H9.
            destruct (M' !! x) ; try contradiction ; auto.
            destruct c ; unpack ; subst ; try auto.
            + split.
              - left. auto.
              - split.
                * left. auto.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - left. auto.
              - split.
                * intro. do 2destruct H12 ; eauto. unpack ; subst. eauto.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - left. auto.
              - split.
                * intro. do 2destruct H12 ; eauto.
                  unpack ; subst. apply HnNotInD. eauto.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              * intro. do 2destruct H12 ; eauto. unpack ; subst. eauto.
              * split.
                { intro. do 2destruct H12 ; eauto.
                  unpack ; subst. apply HnNotInD. eauto.
                }
                {
                  unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. auto.
                }
            + auto.
          }
          { intro. subst. auto. }
         * rewrite set_in_single_eq in H9. subst.
          rewrite lookup_insert. repeat split ; auto.
          { right. auto. }
          { intro. destruct H9. destruct H9 ; unpack ; subst ; try discriminate.
            apply HnNotInD. stdomain_tac. }
          { unfold update_value. destruct (bool_decide (n = n)) eqn:E ; auto.
            apply bool_decide_eq_false_1 in E. contradiction. }
         * iAssert (bi_pure ((<[p':=NodeR (V p') l]> M') !! n = None%I)) as %Mx.
           { case HMx: ((<[p':=NodeR (V p') l]> M')!!n)=>//.
             iDestruct (big_sepM_lookup with "M") as "Hx'"=>//.
             destruct val_of_content; try done.             
             destruct val_of_content; try done.             
               by iDestruct (mapsto_valid_2 with "Hn Hx'") as %[].  }                    
           iApply mapsto_M_insert; [| |by iFrame] ; auto.
     + iPoseProof (mapsto_M_acc M' p' (NodeN z) E2 with "M") as "M".
       iDestruct "M" as (v') "[% [Hp M]]".
       simpl in H6. inversion H7 ; subst.

       (* Get value of node *)
       wp_bind (value #p').    
       iApply (value_specification with "[Hp]") ; auto.
       iModIntro. iIntros "Hp".
       pose proof (Z.lt_trichotomy (V p') v).
       destruct H6 as [H6 | [H6 | H6]].
      (* 1 . 1 *)
      - wp_bind (splay_compare #(V p') #v).
        iApply (splay_compare_specification_lt) ; auto.
        iPureIntro. rewrite lt_zarith. auto. 
        iModIntro ; iIntros ; wp_pures.

        wp_load. wp_pures. wp_load. wp_pures.

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". wp_load.

        (* Get value of node *) wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (right_child #p').    
        iApply (right_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp".
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".

        wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (left_child #p').    
        iApply (left_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp". wp_pures.
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".
        
        wp_bind (value #p').    
        iApply (value_specification with "[Hp]") ; auto.
        iModIntro. iIntros "Hp".

        wp_pures.
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".

        wp_store. wp_pures. wp_store.
        iApply "Hf". 
        iFrame.

        (*save in memory*)
        iAssert
          (bi_pure (val_of_content (NodeN (V p')) = Some (InjRV (#(V p'), (InjLV #(), InjLV #())))))
          as "H1". iPureIntro. auto. 
        iDestruct ("M" with "[H1] [Hp]") as "M" ; auto.
        iExists (add_edge F' n p' LEFT),
        ((<[n:=NodeL v p']> (<[p':=NodeN (V p')]> M'))).
        iSplit. iPureIntro.
        pose proof (insert'_if_bst p' D W V F' n RIGHT v).
        simpl in H9. apply H9 ; auto. 
        iSplit. iPureIntro.
        unfold Mem. intros. apply in_union_inv in H9.        
        destruct H9.
        * rewrite lookup_insert_ne.
          destruct (classic (p' = x)) ; subst.
          { rewrite lookup_insert.
            split.
            + intro. destruct H10. destruct H10 ; unpack ; try discriminate.
              eauto.
            + split.
              - intro. destruct H10. destruct H10 ; unpack ; subst ; try contradiction.
                eauto.
              - unfold update_value.
                destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                apply bool_decide_eq_true_1 in E. subst. contradiction.
          }
          { rewrite lookup_insert_ne.
            pose proof H9 as HxInDomain.
            apply H2 in H9.
            destruct (M' !! x) ; try contradiction ; auto.
            destruct c ; unpack ; subst ; try auto.
            + split.
              - left. auto.
              - split.
                * left. auto.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - left. auto.
              - split.
                * intro. do 2destruct H12 ; eauto. unpack ; subst. eauto.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - left. auto.
              - split.
                * intro. do 2destruct H12 ; eauto.
                  unpack ; subst. apply HnNotInD. eauto.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              * intro. do 2destruct H12 ; eauto. unpack ; subst. eauto.
              * split.
                { intro. do 2destruct H12 ; eauto.
                  unpack ; subst. apply HnNotInD. eauto.
                }
                {
                  unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. auto.
                }
            + auto.
          }
          { intro. subst. auto. }
         * rewrite set_in_single_eq in H9. subst.
          rewrite lookup_insert. repeat split ; auto.
          { right. auto. }
          { intro. destruct H9. destruct H9 ; unpack ; subst ; try discriminate.
            apply HnNotInD. stdomain_tac. }
          { unfold update_value. destruct (bool_decide (n = n)) eqn:E ; auto.
            apply bool_decide_eq_false_1 in E. contradiction. }
         * iAssert (bi_pure ((<[p':=NodeN (V p')]> M') !! n = None%I)) as %Mx.
           { case HMx: ((<[p':=NodeN (V p')]> M')!!n)=>//.
             iDestruct (big_sepM_lookup with "M") as "Hx'"=>//.
             destruct val_of_content; try done.             
             destruct val_of_content; try done.             
               by iDestruct (mapsto_valid_2 with "Hn Hx'") as %[].  }                    
           iApply mapsto_M_insert; [| |by iFrame] ; auto.
      (* 1 . 2 *)
      - subst. exfalso ; apply Hnexists. exists p'.
        split ; stdomain_tac ; auto.
      (* 1 . 3 *)
      - wp_bind (splay_compare #(V p') #v).
        iApply (splay_compare_specification_gt) ; auto.
        iPureIntro. rewrite gt_zarith. lia.
        iModIntro ; iIntros ; wp_pures.

        wp_load. wp_pures. wp_load. wp_pures.
        wp_load.
        
        wp_bind (left_child #n).    
        iApply (left_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        (* Get value of node *) wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".
        
        wp_bind (left_child #p').    
        iApply (left_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp".

        wp_pures.
        wp_bind (value #n).    
        iApply (value_specification with "[Hn]") ; auto.
        iModIntro. iIntros "Hn".
        wp_store. wp_pures.

        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn". 

        wp_bind (right_child #p').    
        iApply (right_child_specification with "[Hp]") ; auto. 
        iModIntro. iIntros "Hp". wp_pures.
        
        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".
        
        wp_bind (value #p').    
        iApply (value_specification with "[Hp]") ; auto.
        iModIntro. iIntros "Hp".

        wp_pures.
        
        wp_bind (right_child #n).    
        iApply (right_child_specification with "[Hn]") ; auto. 
        iModIntro. iIntros "Hn".

        wp_store. wp_pures. wp_store.
        iApply "Hf". 
        iFrame.

        (*save in memory*)
        iAssert
          (bi_pure (val_of_content (NodeN (V p')) = Some (InjRV (#(V p'), (InjLV #(), InjLV #())))))
          as "H1". iPureIntro. auto. 
        iDestruct ("M" with "[H1] [Hp]") as "M" ; auto.
        iExists (add_edge F' n p' RIGHT),
        ((<[n:=NodeR v p']> (<[p':=NodeN (V p')]> M'))).
        iSplit. iPureIntro.
        pose proof (insert'_if_bst p' D W V F' n LEFT v).
        simpl in H9. apply H9 ; auto. lia.
        iSplit. iPureIntro.
        unfold Mem. intros. apply in_union_inv in H9.        
        destruct H9.
        * rewrite lookup_insert_ne.
          destruct (classic (p' = x)) ; subst.
          { rewrite lookup_insert.
            split.
            + intro. destruct H10. destruct H10 ; unpack ; subst ; try contradiction. 
              eauto.
            + split.
              - intro. destruct H10. destruct H10 ; unpack ; try discriminate.
                eauto.
              - unfold update_value.
                destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                apply bool_decide_eq_true_1 in E. subst. contradiction.
          }
          { rewrite lookup_insert_ne.
            pose proof H9 as HxInDomain.
            apply H2 in H9.
            destruct (M' !! x) ; try contradiction ; auto.
            destruct c ; unpack ; subst ; try auto.
            + split.
              - left. auto.
              - split.
                * left. auto.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - left. auto.
              - split.
                * intro. do 2destruct H12 ; eauto. unpack ; subst. eauto.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              - left. auto.
              - split.
                * intro. do 2destruct H12 ; eauto.
                  unpack ; subst. apply HnNotInD. eauto.
                * unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. stdomain_tac.
            + split.
              * intro. do 2destruct H12 ; eauto. unpack ; subst. eauto.
              * split.
                { intro. do 2destruct H12 ; eauto.
                  unpack ; subst. apply HnNotInD. eauto.
                }
                {
                  unfold update_value. destruct (bool_decide (x = n)) eqn:E ; subst ; auto.
                  apply bool_decide_eq_true_1 in E. subst. exfalso. apply HnNotInD. auto.
                }
            + auto.
          }
          { intro. subst. auto. }
         * rewrite set_in_single_eq in H9. subst.
          rewrite lookup_insert. repeat split ; auto.
          { right. auto. }
          { intro. destruct H9. destruct H9 ; unpack ; subst ; try discriminate.
            apply HnNotInD. stdomain_tac. }
          { unfold update_value. destruct (bool_decide (n = n)) eqn:E ; auto.
            apply bool_decide_eq_false_1 in E. contradiction. }
         * iAssert (bi_pure ((<[p':=NodeN (V p')]> M') !! n = None%I)) as %Mx.
           { case HMx: ((<[p':=NodeN (V p')]> M')!!n)=>//.
             iDestruct (big_sepM_lookup with "M") as "Hx'"=>//.
             destruct val_of_content; try done.             
             destruct val_of_content; try done.             
               by iDestruct (mapsto_valid_2 with "Hn Hx'") as %[].  }                    
           iApply mapsto_M_insert; [| |by iFrame] ; auto.
  Qed.
    
  Lemma insert'_st : forall n (p :elem) D V W pp (v : Z),
      {{{ pp ↦ #p ∗ ST p D V W ∗ ⌜n \in D⌝}}}
        splay_tree_insert #pp #n
      {{{ RET #() ; pp ↦ #n ∗ ST n D V W }}}.
  Proof.
    
    
    
End InsertSpecification.
