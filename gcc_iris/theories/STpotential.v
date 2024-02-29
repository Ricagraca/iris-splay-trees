From ST Require Import STorientation STpredicate STlink STdomain STpath STedgeset
                       STedgesetrotateroot.

From iris_time Require Import TLCBuffer.
From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual LibInt LibSet.
From stdpp Require Import gmap.
From iris.bi Require Import big_op.
From iris_time.heap_lang Require Import proofmode.
From iris_time Require Import Combined.
Require Import Coq.Lists.List.
Import ListNotations.

Section PotentialFunction.

  Search finite.
  
  Variable v : val.
  Variable p : elem.
  Variable D : LibSet.set elem.   (* domain *)
  Variable F : elem -> elem -> orientation -> Prop. (* edges *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* weight of node *)
  Variable M : gmap elem content. (* view of the memory *)
  
  Fixpoint sum_list_Z (l : list Z) :=
    match l with
    | [] => 0
    | hd :: tl => hd + (sum_list_Z tl)
    end.

  Definition s (l : list elem) :=
    sum_list_Z (map (fun x => W x) l).

  Definition r (l : list elem) :=
    Z.log2 (s (l)).

  Lemma sum_always_positive :
    Inv p D F V W -> 
    forall l, 0 <= s(l) .
  Proof.
    intros.
    induction l.
    + unfold s. simpl. lia.
    + unfold s. simpl. inversion H.
      destruct Inv_bst as [_ [_ [_ [_ [_ [_ P]]]]]].
      unfold positive_function in P. assert (W a > 0). apply (P a).
      unfold s in IHl. lia.
  Qed.
  
  Lemma sum_append :
    forall l1 l2, s (l1 ++ l2) = s(l1) + s(l2).
  Proof.
    intros.
    generalize dependent l2.
    induction l1 ; intros.
    + unfold s. simpl. auto.
    + simpl. unfold s in *.
      simpl. rewrite IHl1. lia.
  Qed.

  Lemma if_mem_x_l_then_two_list : forall {X} (x : X) (l :list X),
    (LibList.mem x l) ->
    (exists l' l'', l = l' ++ [x] ++ l'').
  Proof.
    intros.
    induction l.
    + inversion H.
    + destruct (classic (a = x)) ; subst.
      - eexists ([]). exists l. auto.
      - inversion H ; subst ; try contradiction.
        apply IHl in H2. destruct H2.
        destruct H1. subst. exists (a :: x0) x1. auto.
  Qed.
    
  Lemma rank_le_if_contained :
    forall l1 l2,
      Inv p D F V W ->
      LibList.noduplicates l1 ->
      LibList.noduplicates l2 ->
      (forall x, LibList.mem x l1 -> LibList.mem x l2) ->
      (s (l1)) <= (s (l2)).
  Proof.
    intros.
    generalize dependent l2.
    induction l1 ; intros.
    + unfold s. simpl. apply sum_always_positive ; auto.
    + inversion H ; subst.
      assert (LibList.mem a l2) ; [apply H2 ; apply LibList.mem_cons_l|].
      apply if_mem_x_l_then_two_list in H3. do 2destruct H3.
      subst. assert (s(l1) ≤ s (x ++ x0)). inversion H0 ; subst.
      apply IHl1 ; auto. 
      intros. 
      * pose proof (LibList.noduplicates_remove).
        specialize (H3 elem a (x ++ [a] ++ x0) H1).
        Search LibList.remove. admit.
      * intros. admit.
      * replace (a :: l1) with ([a] ++ l1) ; [|auto].
        repeat rewrite sum_append ; auto. 
        rewrite sum_append in H3. lia.
  Admitted.
  
      
  Lemma child_lower_rank_than_father :
    forall x o l1 l2, 
      Inv p D F V W ->
      F p x o ->
      let Dp  := descendants F  p in 
      let Dx  := descendants F  x in
      list_repr Dp  l1 ->
      list_repr Dx  l2 ->
      let rp  := r (l1) in 
      let rx  := r (l2) in 
      rx <= rp. 
  Proof.
    intros.
    unfold rp, rx.
    unfold r. apply Z.log2_le_mono.
    unfold list_repr in *.
    unpack. 
    assert (forall x, LibList.mem x l2 -> LibList.mem x l1).
    { intros. apply H3 in H5. apply H4. rewrite in_set_st_eq in H5.
      rewrite in_set_st_eq. apply path_trans with x ; auto ; stpath_tac. }
    apply rank_le_if_contained ; auto.
  Qed.

  Lemma one_rotation_with_no_inner_child_done_case_1 :
    forall x y o l1 l2 l3 l4, 
      Inv y D F V W ->
      F y x o ->
      ¬(exists z, F x z ( invert_orientation o )) ->
      let F' := (add_edge (remove_edge F y x) x y ( invert_orientation o ))in
      let Dx' := descendants F' x in 
      let Dy' := descendants F' y in 
      let Dx  := descendants F  x in 
      let Dy  := descendants F  y in
      list_repr Dx  l1 ->
      list_repr Dy  l2 ->
      list_repr Dx' l3 ->
      list_repr Dy' l4 ->
      let rx  := r (l1) in 
      let ry  := r (l2) in 
      let rx' := r (l3) in 
      let ry' := r (l4) in
      1 + (rx' + ry') - (rx + ry) <= 1 + 3*(rx' - rx). 
  Proof.
  Admitted.
  
End PotentialFunction.
