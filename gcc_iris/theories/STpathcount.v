From ST Require Import STorientation STpredicate STlink STdomain STpath STedgeset
                       STedgesetrotateroot STvaluefunction.

From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual LibInt.
From stdpp Require Import gmap.
From iris.bi Require Import big_op.
From iris_time.heap_lang Require Import proofmode.
From iris_time Require Import Combined.
Require Import Coq.Lists.List.
Import ListNotations.

Section PathCount.

  Notation elem := loc.
  Notation EdgeSet := (elem -> elem -> orientation -> Prop).

  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* weight of node *)
  
  Inductive path_count : EdgeSet -> elem -> elem -> nat -> Prop :=
    path_c_refl : forall F x, path_count F x x 0
  | path_c_step : forall (F : EdgeSet) x y o, F x y o -> path_count F x y 1
  | path_c_trans : forall (F : EdgeSet) x y z o n,
      path_count F x y n ->
      F y z o ->
      path_count F x z (S n).
  
  Inductive path_memory_count : EdgeSet -> elem -> elem -> nat -> list elem -> Prop :=
    path_mc_refl : forall F x, path_memory_count F x x 0 ([])
  | path_mc_step : forall (F : EdgeSet) x y o, F x y o -> path_memory_count F x y 1 ([x])
  | path_mc_trans : forall (F : EdgeSet) x y z o n l,
      path_memory_count  F x y n l ->
      F y z o ->
      path_memory_count  F x z (S n) (l ++ [y]).

  
  Lemma path_memory_count_implies_path_memory : forall F x y c l,
      path_memory_count F x y c l ->
      path_memory F x y l.
  Proof.
    intros.
    induction H.
    + apply path_m_refl. 
    + apply path_m_single with o ; auto.
    + apply path_memory_add_end with o ; auto.
  Qed.
  
  Lemma path_memory_count_implies_path_count : forall F x y n l, 
      path_memory_count F x y n l -> 
      path_count F x y n.
  Proof.
    intros.
    induction H.
    + apply path_c_refl.
    + apply path_c_step with o ; auto.
    + apply ( path_c_trans ) with y o ; auto.
  Qed.
  
  Lemma path_count_implies_path : forall F x y n, 
      path_count F x y n -> 
      path F x y.
  Proof.
    intros.
    induction H.
    + apply path_refl.
    + apply path_single with o ; auto.
    + apply path_trans with y ; auto.
      apply path_single with o ; auto.
  Qed.
  
  Lemma path_memory_count_implies_path_memory_count : forall F x y n, 
      path_count F x y n ->
      (exists l, path_memory_count F x y n l).
  Proof.
    intros.
    induction H.
    + eexists ([]). apply path_mc_refl.
    + exists ([x]). apply path_mc_step with o ; auto.
    + destruct IHpath_count.
      exists (x0 ++ [y]).
      apply path_mc_trans with o ; auto.
  Qed.
  
  Lemma path_memory_count_implies_path : forall F x y n l, 
      path_memory_count F x y n l ->
      path F x y.
  Proof.
    intros.
    induction H.
    + apply path_refl.
    + apply path_single with o ; auto.
    + apply path_trans with y ; auto.
      apply path_single with o ; auto.
  Qed.
  
  Lemma exists_n_path : forall p (F : EdgeSet) x,
      Inv p D F V W ->
      x \in D ->
      exists c, path_count F p x c.
  Proof.
    intros p F x Inv xindomain.    
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree [finite positive]]]]]].
    pose proof (isroot x RIGHT xindomain). unpack.
    clear confined rootisindomain isroot searchleft searchright binarytree finite positive H.
    apply path_implies_path_add in H0.
    induction H0.
    + exists O. apply path_c_refl.
    + exists (S O). apply path_c_step with o ; auto.
    + assert (y \in D) as yindomain. stdomain_tac.
      specialize (IHpath_add Inv yindomain).
      destruct IHpath_add. exists ((1 + x0)%nat).
      pose proof (path_c_trans F x y z o x0).
      apply H2 ; auto. 
  Qed.

  Lemma path_length_equals_counter_if_bst: forall p (F : EdgeSet) x y c l,
      Inv p D F V W ->
      path_memory_count F x y c l ->
      length l = c.
  Proof.
    intros p F x y c l Inv P.
    assert (exists l', rev l' = l).
    exists (rev l). rewrite rev_involutive. auto.
    destruct H. rewrite <- H in *.
    clear dependent l.
    generalize dependent y.
    generalize dependent c.
    induction x0 ; simpl ; intros.
    + inversion P ; subst ; auto.
      apply app_eq_nil in H. unpack ; discriminate.
    + inversion P ; subst ; auto.
      apply app_inj_tail in H. unpack ; subst.
      apply IHx0 in H0. rewrite app_length.
      simpl. rewrite H0. lia.      
  Qed.

  Lemma if_path_to_itself_then_no_step : forall p (F : EdgeSet) x c l,
      Inv p D F V W ->
      path_memory_count F x x c l ->
      c = O /\ l = [].
  Proof.
    intros p F x c l Inv ** .
    assert (exists l', rev l' = l).
    exists (rev l). rewrite rev_involutive. auto.
    destruct H0. rewrite <- H0 in *. clear dependent l.
    rename x0 into l.
    generalize dependent x.
    induction l ; intros.
    + inversion H ; subst ; auto.
      apply app_eq_nil in H0 ; unpack ; discriminate.
    + inversion H ; subst ; auto ; [stlink_tac|].
      apply path_memory_count_implies_path_count in H1.
      apply path_count_implies_path in H1.
      assert (x = y) as XY. stpath_tac. subst.
      stlink_tac.
  Qed.

  Lemma if_path_count_to_itself_then_no_step : forall p (F : EdgeSet) x c,
      Inv p D F V W ->
      path_count F x x c ->
      c = O.
  Proof.
    intros p F x c Inv ** .
    inversion H ; subst ; auto.
    + stlink_tac.
    + destruct o.
      - apply path_count_implies_path in H0. stpath_tac.
      - apply path_count_implies_path in H0. stpath_tac.
  Qed.

  Lemma if_e_in_memory_then_path_from_begin_and_to_end_if_bst :
    forall p F x y e n l,
      Inv p D F V W -> 
      path_memory_count F x y n l ->
      In e l ->
      path F x e /\ path F e y.
  Proof.
    intros.
    assert (exists l', rev l' = l).
    exists (rev l). rewrite rev_involutive. auto.
    destruct H2. rewrite <- H2 in *.
    generalize dependent y.
    generalize dependent n.
    clear dependent l.
    induction x0 ; intros ; auto.
    + inversion H1. 
    + inversion H0.
      - symmetry in H7. apply app_eq_nil in H7 ; unpack ; discriminate.
      - symmetry in H2. apply app_eq_unit in H2 ; destruct H2 ;  unpack ; try discriminate.
        inversion H8 ; subst.
        destruct x0 ; [|simpl in H2; apply app_eq_nil in H2 ; unpack ; discriminate].
        inversion H1 ; subst ; [|inversion H3]. 
        split ; stpath_tac.
      - apply app_inj_tail in H2. unpack ; subst.
        apply in_rev in H1.
        inversion H1 ; subst.
        * apply  path_memory_count_implies_path in H3.
          split ; [|apply path_single with o] ; auto.
        * apply in_rev in H2. apply IHx0 in H3 ; auto. 
          unpack ; split ; auto. apply path_trans with a ; auto.
          apply path_single with o ; auto.
  Qed.
  
  Lemma if_e_in_memory_then_path_from_e_to_end_if_bst :
    forall F x y e n l,
      path_memory_count F x y n l ->
      In e l ->
      (exists n', ((n' > O)%nat /\ path_count F e y n')).
  Proof.
    intros.
    assert (exists l', rev l' = l).
    exists (rev l). rewrite rev_involutive. auto.
    destruct H1. rewrite <- H1 in *.
    generalize dependent y.
    generalize dependent n.
    clear dependent l.
    induction x0 ; intros ; auto.
    + inversion H0. 
    + inversion H ; subst.
      - symmetry in H6. apply app_eq_nil in H6 ; unpack ; discriminate.
      - symmetry in H1. apply app_eq_unit in H1 ; destruct H1 ;  unpack ; try discriminate.
        inversion H2 ; subst.
        destruct x0 ; [|simpl in H1; apply app_eq_nil in H1 ; unpack ; discriminate].
        inversion H0 ; subst ; [|inversion H3]. 
        exists (S O). split ; auto. apply path_c_step with o ; auto.
      - apply app_inj_tail in H1. unpack ; subst.
        apply in_rev in H0.
        inversion H0 ; subst.
        * exists (S O). split ; try lia.
          apply path_c_step with o ; auto.
        * apply in_rev in H1. apply IHx0 in H2 ; auto. 
          destruct H2. exists (S x1). split ; try lia.
          unpack.
          pose proof (path_c_trans F e a y o x1 H3 H7).
          auto.
  Qed.
  
  Lemma if_path_x_to_y_then_y_not_in_memory :
    forall p F x y n l,
      Inv p D F V W -> 
      path_memory_count F x y n l ->
      ¬(In y l).
  Proof.
    intros. intro.
    pose proof (if_e_in_memory_then_path_from_e_to_end_if_bst F x y y n l H0 H1).
    destruct H2. unpack. inversion H3 ; subst.
    + lia.
    + stlink_tac.
    +apply path_count_implies_path in H4. stpath_tac.
  Qed.
    
  Lemma no_duplicates_in_path_list : forall p (F : EdgeSet) x y c l,
      Inv p D F V W ->
      path_memory_count F x y c l ->
      NoDup l.
  Proof.
    intros p F x y c l Inv **.
    generalize dependent y.
    generalize dependent c.
    assert (exists l', rev l' = l).
    exists (rev l). rewrite rev_involutive. auto.
    destruct H. rewrite <- H in *.
    clear dependent l. rename x0 into l.
    induction l ; intros.
    + apply NoDup_nil. 
    + apply NoDup_rev. simpl in *. inversion H ; subst.
      - symmetry in H5. apply app_eq_nil in H5.
        unpack ; discriminate. 
      - symmetry in H0. apply app_eq_unit in H0.
        destruct H0 ; unpack ; try discriminate.
        inversion H1 ; subst. destruct l ; [|apply app_eq_nil in H0 ; unpack ; discriminate].
        apply NoDup_cons ; auto.
        apply NoDup_nil.
      - apply app_inj_tail in H0. unpack ; subst.
        apply IHl in H1 as H1'.
        apply NoDup_cons ; auto.
        pose proof (if_path_x_to_y_then_y_not_in_memory p F x a n (rev l) Inv H1).
        intro. apply H0. rewrite <- in_rev ; auto.
        rewrite <- rev_involutive. apply NoDup_rev. auto.
  Qed.

  (* In e l -> LibList.mem x l *)
  Lemma liblistmem_implies_in : forall {A : Type} (l : list A) e,
      LibList.mem e l -> In e l.
  Proof.
    intros.
    induction l.
    + inversion H.
    + inversion H ; subst.
      - simpl. left ; auto.
      - apply IHl in H1. apply in_cons. auto.
  Qed.
      
  (* NoDup -> LibList.noduplicates *)
  Lemma nodup_implies_liblistnoduplicated : forall {A : Type} (l : list A),
      NoDup l -> LibList.noduplicates l.
  Proof.
    intros.
    induction l.
    + apply LibList.noduplicates_nil.
    + inversion H ; subst. apply LibList.noduplicates_cons ; auto.
      intro. apply H2. apply liblistmem_implies_in. auto.
  Qed.
  
  Lemma all_elements_in_memory_are_in_domain_if_bst : forall p (F : EdgeSet) x y c l,
      Inv p D F V W ->
      path_memory_count F x y c l ->
      Forall (fun e => e \in D) l.
  Proof.
    intros.
    induction H0.
    + auto.
    + apply Forall_cons ; auto.
      stdomain_tac.
    + apply Forall_app_2 ; auto.
      apply Forall_cons ; auto.
      stdomain_tac.
  Qed.

  Lemma Forall_implies_liblistmem : forall P l, 
      Forall P l ->
      (∀ x0 : elem, LibList.mem x0 l → P x0).
  Proof.
    intros.
    induction l.
    + inversion H0.
    + inversion H. subst.
      inversion H0 ; subst ; auto.
  Qed.
      
  Lemma length_of_path_le_card_of_domain_if_bst : forall p (F : EdgeSet) x y c l,
      Inv p D F V W ->
      path_memory_count F x y c l ->
      LibList.length l <= card D.
  Proof.
    intros p F x y c l Inv **.
    inversion Inv.
    destruct Inv_bst as
        [_ [_ [_ [[_ _] [_ [finite _]]]]]].
    assert (LibList.noduplicates l). apply nodup_implies_liblistnoduplicated.
    apply (no_duplicates_in_path_list p) in H ; auto.
    assert (forall x, LibList.mem x l -> x \in D). apply Forall_implies_liblistmem.
    apply (all_elements_in_memory_are_in_domain_if_bst p F x y c l) ; auto.
    pose proof (finite_inv_list_covers_and_card finite).
    destruct H2. unpack. rewrite H3. clear H3.
    unfold list_covers in H2.
    assert (∀ x : elem, LibList.mem x l -> LibList.mem x x0).
    intros. apply H1 in H3. apply H2 in H3. auto.
    pose proof (LibList.noduplicates_length_le).
    specialize (H4 elem l x0 H0 H3).
    rewrite le_peano in H4. apply inj_le. auto.
  Qed.

  Lemma length_equals_liblistlength : forall {A : Type} (l : list A),
      length l = LibList.length l.
  Proof.
    intros.
    induction l ; auto.
    simpl.     rewrite IHl.
    rewrite LibList.length_cons. auto.
  Qed.
    
  Lemma if_path_count_then_count_less_than_card_D : forall p (F : EdgeSet) x y c,
      Inv p D F V W ->
      path_count F x y c ->
      c <= card D.
  Proof.
    intros p F x y c Inv P.
    apply path_memory_count_implies_path_memory_count in P. destruct P.
    pose proof (length_of_path_le_card_of_domain_if_bst p F x y c x0 Inv H).
    apply (path_length_equals_counter_if_bst p) in H as C ; auto.
    rewrite <- C. rewrite length_equals_liblistlength. auto.
  Qed.

  Lemma path_count_begin : forall (F : EdgeSet) x y o z c,
      F x y o ->
      path_count F y z c ->
      path_count F x z (S c).
  Proof.
    intros.
    induction H0 ; simpl ; auto.
    + apply path_c_step in H ; auto.
    + apply path_c_step in H ; auto.
      pose proof ( path_c_trans F x x0 y o0 1 H H0). auto.      
    + apply IHpath_count in H.
      pose proof ( path_c_trans F x y z o0 (S n) H H1).
      auto.
  Qed.
      
  Lemma path_memory_count_begin : forall (F : EdgeSet) x y o z c l,
      F x y o ->
      path_memory_count F y z c l ->
      path_memory_count F x z (S c) (x::l).
  Proof.
    intros.
    induction H0 ; simpl ; auto.
    + apply path_mc_step in H ; auto.
    + apply path_mc_step in H ; auto.
      pose proof path_mc_trans F x x0 y o0 1 ([x]).
      apply H1 ; auto.
    + pose proof path_mc_trans F x y z o0 (S n) (x::l).
      apply H2 ; auto.
  Qed.
  
  Lemma path_count_transitivity : forall F x y z c1 c2,
      path_count F x y c1 ->
      path_count F y z c2 ->
      path_count F x z (c1 + c2).
  Proof.
    intros.
    generalize dependent c2.
    induction H ; simpl ; auto ; intros.
    + pose proof (path_count_begin F x y o z c2 H H0). auto.
    + pose proof (path_count_begin F y z0 o z c2 H0 H1).
      specialize (IHpath_count (S c2) H2).
      rewrite plus_succ in IHpath_count.
      auto.
  Qed.    

  
  Lemma path_memory_implies_path_memory_count : forall F x y l,
      path_memory F x y l ->
      path_memory_count F x y (LibList.length l) l.
  Proof.
    intros.
    induction H.
    + apply path_mc_refl. 
    + apply path_mc_step with o ; auto.
    + pose proof (path_memory_count_begin F x y o z (LibList.length l) l).
      simpl. rewrite <- length_equals_liblistlength.
      simpl. rewrite length_equals_liblistlength.
      apply H1 ; auto.      
  Qed.
  
  Lemma path_memory_size_le_card_domain : forall p (F : EdgeSet) x y l,
      Inv p D F V W ->
      path_memory F x y l ->
      LibList.length l <= card D.
  Proof.
    intros.
    apply  path_memory_implies_path_memory_count in H0.
    apply (length_of_path_le_card_of_domain_if_bst) with p F x y (LibList.length l) ; auto.
  Qed.  
    
  Lemma path_count_memory_refl_nil : forall p F x c l,
      Inv p D F V W -> 
      path_memory_count F x x c l ->
      l = [] /\ c = O.
  Proof.
    intros.
    apply path_memory_count_implies_path_memory in H0 as H0'.
    apply (path_refl_implies_unique p D V W F) in H0' ; auto.
    subst. inversion H0 ; subst ; auto.
    apply app_eq_nil in H1. unpack ; discriminate.
  Qed.
  
  Lemma length_of_path_lt_card_of_domain_if_bst : forall p (F : EdgeSet) x y c l,
      Inv p D F V W ->
      path_memory_count F x y c l ->
      LibOrder.le (LibList.length l) (card D - 1)%nat.
  Proof.
    intros p F x y c l Inv **.
    inversion Inv.
    destruct Inv_bst as
        [_ [rootisindomain [_ [[_ _] [_ [finite _]]]]]].
    destruct c.
    + inversion H ; subst. pose proof ( path_count_memory_refl_nil p F).
      apply H0 in H ; auto. unpack.
      rewrite <- length_equals_liblistlength. simpl.
      pose proof (card_ge_one).
      specialize (H2 elem D p rootisindomain finite). 
      rewrite le_peano in H2.
      rewrite le_peano. lia.
    + inversion H ; subst.
      - Search card. rewrite <- length_equals_liblistlength. simpl.
        pose proof card_diff_single.
        specialize (H0 elem D p finite rootisindomain).
        rewrite <- H0.
        pose proof (card_ge_one).
        specialize (H1 elem (D \-- p) y). apply H1.
        * rewrite set_in_remove_eq. split ; stdomain_tac.
          intro. rewrite set_in_single_eq in H2. subst.
          stlink_tac.
        * apply finite_remove ; auto.
      - assert (¬(LibList.mem y (l0 ++ [y0]))). admit.
        assert (LibList.noduplicates (l0 ++ [y0])). apply nodup_implies_liblistnoduplicated.
        apply (no_duplicates_in_path_list p) in H ; auto.
        assert (forall x, LibList.mem x (l0 ++ [y0]) -> x \in (D \-- y)).
        apply Forall_implies_liblistmem. admit.
        assert (LibSet.finite (D \-- y)). apply finite_remove ; auto.
        pose proof (finite_inv_list_covers_and_card H4).
        destruct H6. unpack.
        pose proof card_diff_single.
        assert (y \in D) as yindomain ; stdomain_tac.
        specialize (H8 elem D y finite yindomain). rewrite <- H8.
        rewrite H7. 
        unfold list_covers in H6.
        assert (∀ x : elem, LibList.mem x (l0 ++ [y0]) -> LibList.mem x x0).
        intros. apply H6. apply H3. auto. auto.
        pose proof (LibList.noduplicates_length_le).
        specialize (H10 elem (l0 ++ [y0]) x0 H2 H9). auto.        
  Admitted.
  
  Lemma path_count_memory_refl_unit : forall p F x y o c l,
      Inv p D F V W -> 
      path_memory_count F x y c l ->
      F x y o ->
      l = [x] /\ c = (S O).
  Proof.
    intros.
    apply path_memory_count_implies_path_memory in H0 as H0'.
    apply (path_single_implies_unique p D V W F x y o) in H0' ; auto.
    subst. 
    inversion H0 ; subst ; auto.
    apply app_eq_unit in H2.
    destruct H2 ; unpack ; try discriminate.
    inversion H4 ; subst.
    apply (path_count_memory_refl_nil p) in H3 ; auto ; unpack ; subst.
    auto.
  Qed.    
  
  Lemma path_memory_count_exists : forall F x y c l,
      path_memory_count F x y (S c) l ->
      (exists o t l', F x t o /\ path_memory_count F t y c l' /\ l = [x] ++ l').
  Proof.
    intros F x y c l **.
    assert (exists l', rev l' = l).
    exists (rev l). rewrite rev_involutive. auto.
    destruct H0. rewrite <- H0 in *. clear dependent l.
    generalize dependent y.
    generalize dependent c.
    induction x0 ; intros ; subst ; auto.
    + inversion H ; subst.
      apply app_eq_nil in H1. unpack ; discriminate.
    + inversion H ; subst.
      - exists o y. eexists ([]).
        repeat split ; auto. apply path_mc_refl.
      - apply app_inj_tail in H1. unpack ; subst.
        destruct c.
        * inversion H5 ; subst.
          simpl in *. rewrite <- H3 in *. simpl in *.
          exists o y. eexists ([]).
          repeat split ; auto using path_mc_refl.
        * apply IHx0 in H5.
          destruct H5 ; subst.
          { inversion H ; subst. apply app_inj_tail in H2 ; unpack ; subst.
            exists x1 t. eexists (l' ++ [a]). repeat split ; simpl ; auto.
            apply path_mc_trans with o ; auto.
            rewrite H4. auto.
          }
  Qed.    

  Lemma no_duplicates_in_path_m_list : forall p (F : EdgeSet) x y l,
      Inv p D F V W ->
      path_memory F x y l ->
      NoDup l.
  Proof.
    intros.
    apply path_memory_implies_path_memory_count in H0.
    apply (no_duplicates_in_path_list p) in H0 ; auto.
  Qed.
  
  
End PathCount.

Section PathFindCount.

  (*
    
        With EdgeSet F and value function V, 
        
        path_count F V x y n s
        means that whenever we use find on F 
        starting in x, then we find y, 
   *)

  Inductive state :=
  | ENDED
  | GOING
  .

  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* weight of node *)

  Inductive path_find_count :
    EdgeSet -> (elem -> Z) -> elem -> elem -> Z -> nat -> state -> Prop :=
    path_fc_refl : forall F V x,
      path_find_count F V x x (V x) 0 ENDED
  | path_fc_stop :  forall F V x z o,
      ¬(exists y, F x y o)  ->
      (orientation_op o) (V x) z ->
      path_find_count F V x x z 0 ENDED
  | path_fc : forall (F :EdgeSet) V x y z o,
      F x y o ->
      (orientation_op o) (V x) z ->
      path_find_count F V x y z 1 GOING
  | path_fc_step_going : forall (F : EdgeSet) V x t y z n1,
      path_find_count F V x y z 1       GOING ->
      path_find_count F V y t z n1      GOING ->
      path_find_count F V x t z (S n1)  GOING
  | path_fc_step_ended : forall (F : EdgeSet) V x y z n1,
      path_find_count F V x y z n1    GOING ->
      path_find_count F V y y z 0     ENDED ->
      path_find_count F V x y z (n1)  ENDED.

  
  Lemma path_find_count_0_going_false : forall F V x y z, 
      ¬(path_find_count F V x y z 0 GOING).
  Proof.
    intros. intro.
    inversion H.
  Qed.
  
  Lemma path_find_count_add_end : forall F x y t z n s,
      path_find_count F V x y z n GOING ->
      path_find_count F V y t z 1 s ->
      path_find_count F V x t z (S n) s.
  Proof.
    intros.
    generalize dependent x.
    generalize dependent y.
    generalize dependent t.
    generalize dependent s.
    induction n ; intros.
    + inversion H ; subst ; auto.
    + inversion H ; subst.
      - inversion H0; subst.
        * apply path_fc_step_going with y ; auto.
        * inversion H10.
        * apply path_fc_step_ended ; auto.
          apply path_fc_step_going with y ; auto.
      - specialize (IHn s t y H0 y0 H8).
        destruct s.
        * inversion IHn ; subst. apply path_fc_step_ended ; auto.
          pose proof (path_fc_step_going F V x t y0 z (S n)).
          apply H4 ; auto.
        * pose proof (path_fc_step_going F V x t y0 z (S n)).
          apply H1 ; auto.
  Qed.
      
  Lemma path_find_count_implies_path : forall F x y z n s,
      path_find_count F V x y z n s ->
      path F x y.
  Proof.
    intros.
    induction H ; stpath_tac.
  Qed.
  
  Lemma path_find_count_implies_path_count : forall F x y z n s,
      path_find_count F V x y z n s ->
      path_count F x y n.
  Proof.
    intros.
    induction H ; try apply path_c_refl.
    + apply path_c_step in H. auto.
    + pose proof ( path_count_transitivity F x y t 1 n1 IHpath_find_count1 IHpath_find_count2).
      auto.
    + pose proof ( path_count_transitivity F x y y n1 0 ).
      rewrite Nat.add_0_r in H1.
      apply H1 ; auto.
  Qed.  

  Lemma path_find_count_smaller_than_n : forall p F x z n s,
      Inv p D F V W -> 
      path_find_count F V p x z n s ->
      n <= card D.
  Proof.
    intros.
    apply path_find_count_implies_path_count in H0.
    pose proof (if_path_count_then_count_less_than_card_D D V W p F p x ).
    auto.
  Qed.

  Lemma no_ending_path_then_exists_a_path_with_different_size : forall p F z,
      ¬(exists x n, path_find_count F V p x z n ENDED) ->
      forall n, (exists x, path_find_count F V p x z (S n) GOING).
  Proof.
    intros.
    induction n.
    + destruct (classic(exists x o, F p x o /\ (orientation_op o) (V p) z)).
      - do 2 destruct H0. unpack. destruct x0 ; simpl in *.
        * exists x. apply path_fc with LEFT ; auto ; try lia.
        * exists x. apply path_fc with RIGHT ; auto ; try lia.
      - exfalso. apply H. exists p O.
        pose proof ((Z.lt_trichotomy (z) (V p))).
        destruct H1 as [H1 |[H1 | H1]].
        * apply path_fc_stop with LEFT ; try lia ; simpl ; auto ; try lia.
          intro. apply H0. destruct H2. exists x LEFT.          
          split ; auto ; simpl ; try lia.
        * subst. apply path_fc_refl.
        * apply path_fc_stop with RIGHT ; try lia ; simpl ; auto ; try lia.
          intro. apply H0. destruct H2. exists x RIGHT.          
          split ; auto ; simpl ; try lia.
    + destruct IHn.
      destruct (classic(exists y o, F x y o /\ (orientation_op o) (V x) z)).
      - do 2destruct H1 ; unpack.
        exists x0.
        pose proof (path_find_count_add_end F p x x0 z ).
        replace (S n + 1)%nat with (S (S n))%nat in H3 ; try lia.
        apply H3 ; auto ; try lia.
        destruct x1.
        * apply path_fc with LEFT ; simpl in * ; try lia ; auto.
        * apply path_fc with RIGHT ; simpl in * ; try lia ; auto.
      - exfalso.
        assert (path_find_count F V p x z (S n) ENDED).
        pose proof (path_fc_step_ended F V p x z (S n)).
        replace (S n + 0)%nat with (S n)%nat in H2 ; try lia.
        apply H2 ; auto ; try lia. 
        pose proof ((Z.lt_trichotomy (z) (V x))).
        destruct H3 as [H3 |[H3 | H3]].
        * apply path_fc_stop with LEFT ; simpl ; try lia.
          intro. apply H1. destruct H4. exists x0 LEFT.
          split ; auto ; simpl ; try lia.
        * subst. apply path_fc_refl.
        * apply path_fc_stop with RIGHT ; simpl ; try lia.
          intro. apply H1. destruct H4. exists x0 RIGHT.
          split ; auto ; simpl ; try lia.
        * eauto.
  Qed.

  Theorem exists_find_count_path_if_inv : forall p F z,
      Inv p D F V W -> 
      (exists x n, path_find_count F V p x z n ENDED).
  Proof.
    intros.
    destruct (classic (∃ (x : elem) (n : nat), path_find_count F V p x z n ENDED)) ; auto.
    pose proof (no_ending_path_then_exists_a_path_with_different_size p F z H0 (card D)).
    exfalso. destruct H1. pose proof (path_find_count_smaller_than_n p F x z (S (card D)) GOING).
    apply H2 in H1 ; auto.
    rewrite <- Nat2Z.inj_le in H1. lia.
  Qed.

  Inductive path_find_count_memory :
    EdgeSet -> (elem -> Z) -> elem -> elem -> Z -> nat -> list elem -> state -> Prop :=
    path_fcm_refl : forall F V x,
      path_find_count_memory F V x x (V x) 0 ([]) ENDED
  | path_fcm_stop :  forall F V x z o,
      ¬(exists y, F x y o)  ->
      (orientation_op o) (V x) z ->
      path_find_count_memory F V x x z 0 ([]) ENDED
  | path_fcm : forall (F :EdgeSet) V x y z o,
      F x y o ->
      (orientation_op o) (V x) z ->
      path_find_count_memory F V x y z 1 ([x]) GOING
  | path_fcm_step_going : forall (F : EdgeSet) V x t y z n1 l,
      path_find_count_memory F V x y z 1 ([x]) GOING ->
      path_find_count_memory F V y t z n1 l    GOING ->
      path_find_count_memory F V x t z (S n1) ([x] ++ l)  GOING
  | path_fcm_step_ended : forall (F : EdgeSet) V x y z n1 l,
      path_find_count_memory F V x y z n1 l   GOING ->
      path_find_count_memory F V y y z 0 ([]) ENDED ->
      path_find_count_memory F V x y z (n1) l ENDED.
    
  Lemma path_find_count_memory_implies_path_find_count : forall F x y z n l s,
      path_find_count_memory F V x y z n l s ->
      path_find_count F V x y z n s.
  Proof.
    intros.
    induction H.
    + apply path_fc_refl.
    + apply path_fc_stop with o ; auto.
    + apply path_fc with o ; auto.
    + apply path_fc_step_going with y ; auto.
    + apply path_fc_step_ended ; auto.
  Qed.
  
  Lemma path_find_count_memory_add_end : forall F x y t z n l,
      path_find_count_memory F V x y z n l GOING ->
      path_find_count_memory F V y t z 1 ([y]) GOING ->
      path_find_count_memory F V x t z (S n) (l ++ [y]) GOING.
  Proof.
    intros.
    generalize dependent x.
    generalize dependent y.
    generalize dependent t.
    generalize dependent l.    
    induction n ; intros.
    + inversion H.
    + inversion H ; subst.
      - pose proof (path_fcm_step_going F V x t y z 1).
        apply H1 ; auto.
      - specialize (IHn l0 t y H0 y0 H8).
        pose proof (path_fcm_step_going F V x t y0 z (S n) (l0 ++ [y])).
        eauto.
  Qed.
  
  Lemma no_ending_path_memory_then_exists_a_path_with_different_size : forall p F z,
      ¬(exists x n l, path_find_count_memory F V p x z n l ENDED) ->
      forall n, (exists x l, path_find_count_memory F V p x z (S n) l GOING).
  Proof.
    intros.
    induction n.
    + destruct (classic(exists x o, F p x o /\ (orientation_op o) (V p) z)).
      - do 2 destruct H0. unpack. destruct x0 ; simpl in *.
        * exists x ([p]). apply path_fcm with LEFT ; auto.
        * exists x ([p]). apply path_fcm with RIGHT ; auto ; try lia.
      - exfalso. apply H. exists p O. eexists ([]).
        pose proof ((Z.lt_trichotomy (z) (V p))).
        destruct H1 as [H1 |[H1 | H1]].
        * apply path_fcm_stop with LEFT ; try lia ; simpl ; auto ; try lia.
          intro. apply H0. destruct H2. exists x LEFT.          
          split ; auto ; simpl ; try lia.
        * subst. apply path_fcm_refl.
        * apply path_fcm_stop with RIGHT ; try lia ; simpl ; auto ; try lia.
          intro. apply H0. destruct H2. exists x RIGHT.          
          split ; auto ; simpl ; try lia.
    + destruct IHn.
      destruct (classic(exists y o, F x y o /\ (orientation_op o) (V x) z)).
      - do 2destruct H1 ; unpack.
        exists x0.
        pose proof (path_find_count_memory_add_end F p x x0 z (S n) l).
        exists (l ++ [x]).
        apply H3 ; auto ; try lia.
        destruct x1.
        * apply path_fcm with LEFT ; simpl in * ; try lia ; auto.
        * apply path_fcm with RIGHT ; simpl in * ; try lia ; auto.
      - exfalso.
        destruct H0.
        assert (path_find_count_memory F V p x z (S n) x0 ENDED).
        pose proof (path_fcm_step_ended F V p x z (S n)).
        apply H2 ; auto ; try lia. 
        pose proof ((Z.lt_trichotomy (z) (V x))).
        destruct H3 as [H3 |[H3 | H3]].
        * apply path_fcm_stop with LEFT ; simpl ; try lia.
          intro. apply H1. destruct H4. exists x1 LEFT.
          split ; auto ; simpl ; try lia.
        * subst. apply path_fcm_refl.
        * apply path_fcm_stop with RIGHT ; simpl ; try lia.
          intro. apply H1. destruct H4. exists x1 RIGHT.
          split ; auto ; simpl ; try lia.
        * eauto.
  Qed.
  
  Theorem exists_find_count_memory_path_if_inv : forall p F z,
      Inv p D F V W -> 
      (exists x n l, path_find_count_memory F V p x z n l ENDED).
  Proof.
    intros.
    destruct (classic (∃ (x : elem) (n : nat) (l : list elem), path_find_count_memory F V p x z n l ENDED)) ; auto.
    pose proof (no_ending_path_memory_then_exists_a_path_with_different_size p F z H0 (card D)).
    exfalso. do 2destruct H1.
    apply path_find_count_memory_implies_path_find_count in H1.
    pose proof (path_find_count_smaller_than_n p F x z (S (card D)) GOING).
    apply H2 in H1 ; auto.
    rewrite <- Nat2Z.inj_le in H1. lia.
  Qed.

  Lemma base_case_path_find_count_exists : forall F x y z s,
    path_find_count F V x y z 2 s -> 
    exists t,
      path_find_count F V x t z 1 GOING /\
      path_find_count F V t y z 1 s.
  Proof.
    intros.
    inversion H ; subst.
    + inversion H7 ; subst ; [|inversion H9].
      exists y0. repeat split ; auto.
    + inversion H0 ; subst.
      inversion H9 ; subst ; [|inversion H11].
      exists y0. repeat split ; auto.
      apply path_fc_step_ended ; auto.
  Qed.
                    
  Lemma path_find_count_exists_end : forall F x y z n s,
      path_find_count F V x y z (S (S n)) s ->
      exists t,
        path_find_count F V x t z (S n) GOING /\
        path_find_count F V t y z 1 s.
  Proof.
    intros.
    generalize dependent x.
    generalize dependent y.
    induction n ; intros.
    + apply base_case_path_find_count_exists ; auto.
    + inversion H ; subst.
      * specialize (IHn y y0 H7).
        destruct IHn as [t H'].
        destruct H' as [H1' H2'].
        exists t. repeat split ; auto.
        apply path_fc_step_going with y0 ; auto.
      * inversion H0 ; subst.
        assert (path_find_count F V y0 y z (S (S n)) ENDED).
        apply path_fc_step_ended ; auto.
        specialize (IHn y y0 H2).
        destruct IHn as [t H'].
        destruct H' as [H1' H2'].
        exists t. repeat split ; auto.
        apply path_fc_step_going with y0 ; auto.
  Qed.
  
  Theorem find_count_path_on_descendent_if_inv : forall p F x y z n s,
      Inv p D F V W -> 
      path_find_count F V x y z n s ->
      path_find_count (remove_edge_that_are_not_in_D F (descendants F x)) V x y z n s.
  Proof.
    intros.
    generalize dependent s.
    generalize dependent x.
    generalize dependent y.
    induction n ; intros.
    + inversion H0 ; subst.
      - apply path_fc_refl.
      - apply path_fc_stop with o ; auto.
        intro. apply H1. destruct H3. exists x.
        destruct H3. unpack ; auto.
      - inversion H1.
    + destruct n.
      - inversion H0 ; subst.
        * apply path_fc with o ; auto.
          repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
        * inversion H8.
        * inversion H1 ; subst ; [|inversion H10].
          inversion H2 ; subst.
          { apply path_fc_step_ended ; auto.
            + apply path_fc with o ; auto. repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
            + apply path_fc_refl. }
          { apply (path_fc_step_ended).
            + apply path_fc with o ; auto. repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
            + apply path_fc_stop with o0 ; auto. intro. destruct H7. destruct H7 ; unpack.
              eauto. }
          { inversion H5. }
      - apply path_find_count_exists_end in H0 as H0'.
        destruct H0' as [t H'].
        destruct H' as [H1' H3'].
        specialize (IHn t x GOING H1').
        assert (path_find_count (remove_edge_that_are_not_in_D F (descendants F x)) V x y z (S (S n)) s) ; auto.
        { pose proof (path_find_count_add_end
                        (remove_edge_that_are_not_in_D F (descendants F x)) x t y z (S n)).
          apply H1 ; auto.
          inversion H3' ; subst.
          * apply path_fc with o ; auto.
            repeat split ; auto ; rewrite in_set_st_eq.
            { pose proof (path_find_count_implies_path F x t z (S n) GOING).
              apply H4 ; auto. }
            { pose proof (path_find_count_implies_path F x y z (S (S n)) GOING).
              apply H4 ; auto. }
          * inversion H9.
          * inversion H2 ; subst ; [|inversion H11].
            apply path_fc_step_ended ; auto.
            { apply path_fc with o ; auto.
              repeat split ; auto ; rewrite in_set_st_eq.
              { pose proof (path_find_count_implies_path F x t z (S n) GOING).
                apply H6 ; auto. }
              { pose proof (path_find_count_implies_path F x y z (S (S n)) ENDED).
                apply H6 ; auto. }
            }
            inversion H3 ; subst.
            {
              apply path_fc_refl.
            }
            {
              apply path_fc_stop with o0 ; auto.
              intro. apply H6. destruct H8. exists x0. destruct H8 ; unpack ; auto.
            }
            { inversion H6. }
        }
  Qed.
  
  Lemma find_count_path_equiv : forall x y F1 F2 z n s,
      (forall a b c, F1 a b c <-> F2 a b c) -> 
      path_find_count F1 V x y z n s ->
      path_find_count F2 V x y z n s.
  Proof.
    intros.
    induction H0.
    + apply path_fc_refl.
    + apply path_fc_stop with o ; auto. intro.
      apply H0. destruct H2. exists x0. apply H ; auto.
    + apply path_fc with o ; auto. apply H. auto.
    + apply path_fc_step_going with y ; auto.
    + apply path_fc_step_ended ; auto.
  Qed.

  Lemma path_find_count_memory_eliminate_subtree_not_in_path_case : forall F p x n o z,
      Inv p D F V W -> 
      orientation_op o (V p) z ->
      path_find_count F V p x z (S n) GOING ->
      orientation_op o (V p) (V x).
  Proof.
    intros.
    inversion H1 ; subst. 
    + assert (o = o0). storientation_tac. subst ; auto ; stlink_tac.
    + inversion H3 ; subst ; [|inversion H11]. assert (o = o0) ; storientation_tac ; subst.
      apply path_find_count_implies_path in H9. stpath_tac.
  Qed.
      
  Lemma path_find_count_memory_eliminate_subtree_not_in_path : forall F p x y o z n s,
      Inv p D F V W -> 
      orientation_op o (V p) z -> 
      orientation_op (invert_orientation o) (V p) (V y) -> 
      path_find_count (remove_edge_that_are_in_D F (descendants F y)) V p x z n s->
      path_find_count F V p x z n s.
  Proof.
    intros.
    generalize dependent x.
    generalize dependent s.
    induction n ; intros.
    + inversion H2 ; subst.
      - apply path_fc_refl.
      - assert (o = o0) ; storientation_tac ; subst o0.
        apply path_fc_stop with o ; auto. intro.
        destruct H5. apply H3. exists x0.
        repeat split ; auto ; rewrite in_set_st_eq ; intro.
        * assert (x = y) ; stpath_tac ; subst ; storientation_tac.
        * assert (orientation_op (o) (V x) (V x0)). stlink_tac.          
          destruct (classic (y = x0)) ; subst ; storientation_tac.
          pose proof (path_right_left_step_end_if_bst F y x0 H6 H8).
          destruct H9. unpack. destruct H9 ; assert (x1 = x) ; stpath_tac ; subst.
          { assert (o = RIGHT) ; stlink_tac ; subst. simpl in *.
            assert (y = x) ; stpath_tac ; subst. lia. }
          { assert (o = LEFT) ; stlink_tac ; subst. simpl in *.
            assert (y = x) ; stpath_tac ; subst. lia. }
      - inversion H3.
    + destruct n.
      - inversion H2 ; subst.
        * apply path_fc with o0 ; auto. destruct H3 ; auto.
        * inversion H10.
        * apply path_fc_step_ended ; auto.
          { inversion H3 ; subst ; [|inversion H12]. apply path_fc with o0 ; auto. destruct H5 ; auto. }
          { inversion H4 ; subst.
            + apply path_fc_refl.
            + apply path_fc_stop with o0 ; auto.
              intro. apply H5. destruct H7. exists x0.
              repeat split ; auto ; rewrite in_set_st_eq ; intro.
              - apply H5. exists x0. repeat split ; auto ; rewrite in_set_st_eq ; intro.
                * inversion H3 ; subst ; [|inversion H18].
                  destruct H11 ; unpack. assert (o = o1) ; storientation_tac ; subst o1.
                  apply path_right_left_step_end_if_bst in H8 ; 
                    [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                  destruct H8. unpack.
                  destruct H8 ; assert (x1 = p) ; stpath_tac ; subst.
                  { apply path_right_left_step_end_if_bst in H9 ; 
                    [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                    destruct H9 ; unpack. destruct H9 ; assert (x1 = p) ; stpath_tac ; subst.
                    assert (y = p) ; stpath_tac ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac.
                  }
                  { apply path_right_left_step_end_if_bst in H9 ; 
                    [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                    destruct H9 ; unpack. destruct H9 ; assert (x1 = p) ; stpath_tac ; subst.
                    assert (y = p) ; stpath_tac ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac.
                  }
                * inversion H3 ; subst ; [|inversion H18].
                  destruct H11 ; unpack. assert (o = o1) ; storientation_tac ; subst o1.
                  apply path_right_left_step_end_if_bst in H8 ; 
                    [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                  destruct H8. unpack.
                  destruct H8 ; assert (x1 = p) ; stpath_tac ; subst.
                  { apply path_right_left_step_end_if_bst in H9 ; 
                    [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                    destruct H9 ; unpack. destruct H9 ; assert (x1 = x) ; stpath_tac ; subst.
                    - apply path_right_left_step_end_if_bst in H16 ;
                        [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                      destruct H16 ; unpack. destruct H16 ; assert (x1 = p) ; stpath_tac ; subst.
                      assert (y=p) ; stpath_tac ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac.
                    - apply path_right_left_step_end_if_bst in H16 ;
                        [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                      destruct H16 ; unpack. destruct H16 ; assert (x1 = p) ; stpath_tac ; subst.
                      assert (y=p) ; stpath_tac ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac.
                  }
                  { apply path_right_left_step_end_if_bst in H9 ; 
                    [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                    destruct H9 ; unpack. destruct H9 ; assert (x1 = x) ; stpath_tac ; subst.
                    - apply path_right_left_step_end_if_bst in H16 ;
                        [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                      destruct H16 ; unpack. destruct H16 ; assert (x1 = p) ; stpath_tac ; subst.
                      assert (y=p) ; stpath_tac ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac.
                    - apply path_right_left_step_end_if_bst in H16 ;
                        [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                      destruct H16 ; unpack. destruct H16 ; assert (x1 = p) ; stpath_tac ; subst.
                      assert (y=p) ; stpath_tac ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac.
                  }
              - apply H5. exists x0. repeat split ; auto ; rewrite in_set_st_eq ; intro.
                * inversion H3 ; subst ; [|inversion H18].
                  destruct H11 ; unpack. assert (o = o1) ; storientation_tac ; subst o1.
                  apply path_right_left_step_end_if_bst in H8 ; 
                    [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                  destruct H8. unpack.
                  destruct H8 ; assert (x1 = x) ; stpath_tac ; subst.
                  { apply path_right_left_step_end_if_bst in H9 ; 
                    [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                    destruct H9 ; unpack. destruct H9 ; assert (x1 = p) ; stpath_tac ; subst ;
                    assert (y = p) ; stpath_tac ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac.
                  }
                  { apply path_right_left_step_end_if_bst in H9 ; 
                    [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                    destruct H9 ; unpack. destruct H9 ; assert (x1 = p) ; stpath_tac ; subst ;
                    assert (y = p) ; stpath_tac ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac.
                  }
                * inversion H3 ; subst ; [|inversion H18].
                  destruct H11 ; unpack. assert (o = o1) ; storientation_tac ; subst o1.
                  apply path_right_left_step_end_if_bst in H8 ;
                  [|intro ; subst ;
                   assert ( orientation_op o (V p) (V x0)) ; assert (path F x x0) ; stpath_tac ; stpath_tac ;
                   storientation_tac].
                  destruct H8. unpack.
                  destruct H8 ; assert (x1 = x) ; stpath_tac ; subst.
                  { apply path_right_left_step_end_if_bst in H9 ; 
                    [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                    destruct H9 ; unpack. destruct H9 ; assert (x1 = x) ; stpath_tac ; subst.
                    apply path_right_left_step_end_if_bst in H16 ;
                      [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                    destruct H16 ; unpack. destruct H16 ; assert (x1 = p) ; stpath_tac ; subst ;
                      assert (y=p) ; stpath_tac ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac.
                  }
                  { apply path_right_left_step_end_if_bst in H9 ; 
                    [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                    destruct H9 ; unpack. destruct H9 ; assert (x1 = x) ; stpath_tac ; subst.
                    apply path_right_left_step_end_if_bst in H16 ;
                      [|intro ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac].
                    destruct H16 ; unpack. destruct H16 ; assert (x1 = p) ; stpath_tac ; subst ;
                    assert (y=p) ; stpath_tac ; subst ; apply H14 ; rewrite in_set_st_eq ; stpath_tac.
                  }
            + inversion H5.
          }
      - apply path_find_count_exists_end in H2. destruct H2 ; unpack.
        apply IHn in H2.
        assert (path_find_count F V x0 x z 1 s).
        * inversion H3 ; subst.
          { apply path_fc with o0 ; auto. destruct H4 ; unpack ; auto. }
          { inversion H11. }
          { apply path_fc_step_ended ; auto.
            + inversion H4 ; subst ; [|inversion H13].
              apply path_fc with o0 ; auto. destruct H6 ; unpack ; auto.
            + inversion H5 ; subst.
              - apply path_fc_refl.
              - inversion H4 ; subst ; [|inversion H16].
                destruct H8 ; unpack. apply path_fc_stop with o0 ; auto.
                intro. destruct H13. apply H6. exists x1. repeat split ; auto.
                rewrite in_set_st_eq. intro.
                apply path_right_left_step_end_if_bst in H14.
                * destruct H14 ; unpack. destruct H14 ; assert (x2 = x) ; stpath_tac ; subst.
                  { apply H12. auto. }
                  { apply H12. auto. }                  
                * intro. subst.
                  inversion H2 ; subst.
                  { assert (o2 = o). storientation_tac. subst.
                    assert (path F x0 x1). 
                    apply path_trans with x ; stpath_tac.
                    assert (orientation_op (o) (V p) (V x1)). stpath_tac. storientation_tac.
                  }
                  { inversion H16 ; subst ; [|inversion H24].
                    assert (path F y x1). apply path_find_count_implies_path in H22.
                    apply path_trans with x ; stpath_tac.
                    assert (o2 = o). storientation_tac. subst.
                    assert (orientation_op (o) (V p) (V x1)). stpath_tac. storientation_tac.
                  }
              - inversion H6.
          }
        * apply path_find_count_add_end with x0 ; auto.
  Qed.
  
End PathFindCount.

Ltac stpathcount_tac :=
  match goal with
  | h1 : path_find_count ?F ?V ?x ?y ?z 0 GOING  |- _  =>
    inversion h1
  | |- path_find_count ?F ?V ?x ?x (?V ?x) 0 ENDED =>
    apply path_fc_refl
  | _ => idtac
  end.
