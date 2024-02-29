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

Section EdgeFiniteList.

  Notation elem := loc.
  Notation EdgeSet := (elem -> elem -> orientation -> Prop).

  Variable p : elem.
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* weight of node *)
  Variable M : gmap elem content. (* view of the memory *)
  
  Definition edge_set (F : EdgeSet) : set (elem * (elem * orientation)) :=
    (set_st (fun x => (F (fst x) (fst (snd x)) (snd (snd x)) ))).

  Lemma if_domain_finite_then_cartesian_as_well_if_bst :
    forall (X Y : Type) (D1 : set X) (D2 : set Y),
      finite D1 ->
      finite D2 -> 
      finite (set_st (fun (x : prod X Y) => fst x \in D1 /\ snd x \in D2)).      
  Proof.
    intros.
    rewrite finite_eq_in_iff_mem_to_list.
    intros. split ; intros.
    + admit.
    + destruct x. rewrite in_set_st_eq.
      simpl. pose proof  LibList.Forall_mem_inv.
      specialize (H2 (prod X Y) (fun x => x.1 \in D1 ∧ x.2 \in D2)).
      apply H2 in H1 ; auto.
      rewrite LibList.Forall_eq_forall_mem.
      intros. 

  Admitted.
    
  Lemma edge_set_finite_if_bst : forall F,
      Inv p D F V W ->
      finite (edge_set F).
  Proof.
    intros.
    inversion H. 
    destruct Inv_bst as
        [confined [_ [_ [_ [_ [finite _]]]]]]. 
    pose proof (if_domain_finite_then_cartesian_as_well_if_bst
                  elem orientation D (\{RIGHT} \u \{LEFT})).
    assert (LibSet.finite  ('{RIGHT} \u '{LEFT})).
    * apply finite_union ; apply finite_single.  
    * specialize (H0 finite H1).
      pose proof (if_domain_finite_then_cartesian_as_well_if_bst
                    elem (elem * orientation)).
      remember \set{ x : elem * orientation | x.1 \in D ∧ x.2 \in '{RIGHT} \u '{LEFT}} as D2.
      specialize (H2 D D2 finite H0). unfold edge_set.
      pose proof (finite_incl).
      specialize (H3 (prod elem (prod elem orientation))
                     (\set{ x : elem * (elem * orientation) | F x.1 x.2.1 x.2.2})
                     (\set{ x : elem * (elem * orientation) | x.1 \in D ∧ x.2 \in D2})).
      apply H3 ; auto.
      apply incl_prove. intros.
      rewrite in_set_st_eq in H4.
      rewrite in_set_st_eq. apply confined in H4. unpack ; split ; auto.
      rewrite HeqD2. 
      rewrite in_set_st_eq. split ; auto. destruct x.2.2.
      apply in_union_r. rewrite set_in_single_eq. auto.
      apply in_union_l. rewrite set_in_single_eq. auto.
  Qed.

  Lemma exists_list_for_edge_set_if_bst : forall F,
      Inv p D F V W ->
      (exists l, (forall x y o, LibList.mem (x,(y,o)) l <-> F x y o)).
  Proof.
    intros.
    pose proof (edge_set_finite_if_bst F H) as H'.
    pose proof (finite_eq_in_iff_mem_to_list).
    specialize (H0 (prod elem (prod elem orientation)) (edge_set F)).
    rewrite H0 in H'.
    exists (to_list (edge_set F)).
    split ; intro.
    + apply H' in H1. rewrite in_set_st_eq in H1.
      auto.
    + apply H'. rewrite in_set_st_eq .
      auto.
  Qed.

End EdgeFiniteList.
