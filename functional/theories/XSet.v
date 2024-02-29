Require Import MSets.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Omega.
Require Import Coq.Lists.List.
Require Import Compare_dec.
Require Import Coq.Structures.Orders.
Import ListNotations.
 

Module OrderedSet(Import o : OrderedType.OrderedType).

  Module OrderedDecidableType(o' : OrderedType.OrderedType) <: DecidableType.
    Include OrderedType.OrderedTypeFacts(o').
    Definition t := o'.t.
    Definition eq := o'.eq.
  End OrderedDecidableType.
  
  Module ODT  := OrderedDecidableType(o).
  Module XSet := MSetWeakList.Make(ODT).
  Include ODT.
  
  (*
    Module X_facts := OrderedTypeFacts (o).
   *)
  
  Fixpoint set_list (t : list XSet.elt ) : XSet.t := 
    match t with 
    | []   => XSet.empty
    | a::h => XSet.add a (set_list h)
    end.
  
  Lemma set_forall_empty_spec : forall p,
      XSet.For_all p XSet.empty.
  Proof.
    intros.
    unfold XSet.For_all. intros.
    inversion H.
  Qed.

  Lemma set_equal_refl_spec : forall s,
      XSet.Equal s s.
  Proof.
    intros.
    unfold XSet.Equal ; split ; auto.
  Qed.

  Lemma set_equal_comm_spec : forall s1 s2,
      XSet.Equal s1 s2 <-> XSet.Equal s2 s1.
  Proof.
    intros. split ; unfold XSet.For_all, XSet.Equal in * ;
    intro ; split ; intro ; apply H ; apply H0.
  Qed.

  Lemma set_equal_forall_spec : forall p s1 s2,
      XSet.Equal s1 s2 ->
      XSet.For_all p s1 ->
      XSet.For_all p s2.
  Proof.
    intros.
    unfold XSet.For_all, XSet.Equal in *.
    intros. apply H in H1. apply H0 in H1. apply H1.
  Qed.
  
  Theorem set_in_list_in_set_spec : forall a l,
      In a l -> XSet.In a (set_list l).
  Proof.
    intros a l ; induction l ; intro H.
    - inversion H.
    - simpl in H ; destruct H ; simpl ; subst ;
      apply XSet.add_spec ;
      [left;reflexivity|right;apply IHl ;assumption].
  Qed.

  Theorem set_in_app_or_spec : forall a l1 l2,
      (XSet.In a (set_list (l1 ++ l2))) <->
      (XSet.In a (set_list l1) \/ XSet.In a (set_list l2)).
  Proof.
    intros ; split ; induction l1 ; intro H ; simpl in * ;
      try apply XSet.add_spec in H ; auto ; destruct H ;
        repeat rewrite XSet.add_spec ; auto ;
          try (apply IHl1 in H ; destruct H ; auto) ;
            inversion H ; try (rewrite XSet.add_spec in H ; destruct H ; auto).
  Qed.

  Theorem set_union_comm_spec : forall s1 s2,
      XSet.Equal (XSet.union s1 s2) (XSet.union s2 s1).
  Proof.
    unfold XSet.Equal ; split ; do 2 rewrite XSet.union_spec ;
    intro H ; destruct H ; auto.
  Qed.

  Theorem set_union_assoc_spec : forall s1 s2 s3,
      XSet.Equal (XSet.union s1 (XSet.union s2 s3))
                 (XSet.union (XSet.union s1 s2) s3).
  Proof.
    unfold XSet.Equal ; split ; do 4 rewrite XSet.union_spec ;
    intro H ; do 2 (destruct H ; auto).
  Qed.

  Lemma set_union_reduct_intro_spec : forall s1 s2 s3,
      XSet.Equal s2 s3 ->
      XSet.Equal (XSet.union s1 s2) (XSet.union s1 s3).
  Proof.
    intros s1 s2 s3 ; unfold XSet.Equal ; split ; intro H' ;
    apply XSet.union_spec ; apply XSet.union_spec in H'    ;
    destruct H' ; try apply H in H0 ; auto.
  Qed.

  Theorem set_union_empty_spec :
    XSet.Equal (XSet.union XSet.empty XSet.empty) XSet.empty.
  Proof.
    unfold XSet.Equal ; intros ; split ; intro.
    + apply XSet.union_spec in H. destruct H ; assumption.
    + apply XSet.union_spec. left ; assumption.
  Qed.

  Theorem set_in_empty_false_spec : forall a,
      XSet.In a XSet.empty <-> False.
  Proof.
    intros.
    split ; intros ; [inversion H| contradiction].
  Qed.
  
  Theorem set_remove_empty_spec : forall a,
      XSet.Equal (XSet.remove a XSet.empty) XSet.empty.
  Proof.
    unfold XSet.Equal ; intros ;
    split ; intro.
    + apply XSet.remove_spec in H ; destruct H ; assumption.
    + apply XSet.remove_spec ;
      split ; try assumption ; inversion H.
  Qed.

  Theorem set_different_remove_spec : forall a a' s,
      ~eq a a' ->
      XSet.In a s ->
      XSet.In a (XSet.remove a' s).
  Proof.
    intros ;
    apply XSet.remove_spec ; split ; assumption.
  Qed.
  
  Theorem set_union_spec : forall p s1 s2,
      XSet.For_all p (XSet.union s1 s2) <->
      XSet.For_all p s1 /\ XSet.For_all p s2.
  Proof.
    intros.
    split ; intro H ; unfold XSet.For_all in *.
    - split ; intros ; apply H ; apply XSet.union_spec ; auto.
    - destruct H as [H1 H2] ;  intros.
      apply XSet.union_spec in H.
      destruct H ; [apply H1 | apply H2] ; auto.
  Qed.

  Theorem set_predicate_spec : forall (p1 p2 : XSet.elt -> Prop) s,
      (forall el, p1 el -> p2 el) ->
      XSet.For_all p1 s ->
      XSet.For_all p2 s.
  Proof.
    intros. unfold XSet.For_all in *.
    intros. apply H. apply H0. apply H1.
  Qed.

  Lemma set_forall_lt_l_spec : forall b c s,
      lt b c ->
      XSet.For_all (fun n : XSet.elt => lt c n) s ->
      XSet.For_all (fun n : XSet.elt => lt b n) s.
  Proof.
    unfold XSet.For_all ; intros.
    apply (H0 x) in H1.
    order.
  Qed.

  Lemma set_forall_lt_r_spec : forall b c s,
      lt c b ->
      XSet.For_all (fun n : XSet.elt => lt n c) s ->
      XSet.For_all (fun n : XSet.elt => lt n b) s.
  Proof.
    unfold XSet.For_all ; intros.
    apply (H0 x) in H1.
    order.
  Qed.

  Lemma set_equal_union_singleton_l_spec : forall a s1 s2,
      XSet.Equal (XSet.union (XSet.singleton a) (s1)) (s2) ->
      XSet.In a s2.
  Proof.
    intros. unfold XSet.Equal in H. specialize (H a).
    apply H. rewrite XSet.union_spec. left.
    rewrite XSet.singleton_spec. reflexivity.
  Qed.

  Lemma set_equal_union_singleton_r_spec : forall a s1 s2,
      XSet.Equal (s1) (XSet.union (XSet.singleton a) (s2)) ->
      XSet.In a s1.
  Proof.
    intros. unfold XSet.Equal in H. specialize (H a).
    apply H. rewrite XSet.union_spec. left.
    rewrite XSet.singleton_spec. reflexivity.
  Qed.
    
  Lemma set_forall_singleton_predicate_intro_spec : forall p n,
      XSet.For_all p (XSet.singleton n) -> p n.
  Proof.
    intros.
    unfold XSet.For_all in H.
    apply H. apply XSet.singleton_spec ; reflexivity.
  Qed.

  Lemma set_equal_in_parent_spec : forall x s1 s2 s3 s4,
      XSet.Equal (s1) (XSet.union (s2) (XSet.union (s3) (s4))) ->
      XSet.In x (s2) ->
      XSet.In x (s1).
  Proof.
    intros.
    unfold XSet.Equal in H. specialize (H x).
    assert (XSet.In x (XSet.union s2 (XSet.union s3 s4))).
    rewrite XSet.union_spec. left ; assumption.
    apply H in H1. assumption.
  Qed.

  Lemma set_equal_in_l_child_spec : forall x s1 s2 s3 s4,
      XSet.Equal (s1) (XSet.union (s2) (XSet.union (s3) (s4))) ->
      XSet.In x (s3) ->
      XSet.In x (s1).
  Proof.
    intros.
    unfold XSet.Equal in H. specialize (H x).
    assert (XSet.In x (XSet.union s2 (XSet.union s3 s4))).
    rewrite XSet.union_spec. right.
    rewrite XSet.union_spec ; left ; assumption.
    apply H in H1. assumption.
  Qed.

  Lemma set_equal_in_r_child_spec : forall x s1 s2 s3 s4,
      XSet.Equal (s1) (XSet.union (s2) (XSet.union (s3) (s4))) ->
      XSet.In x (s4) ->
      XSet.In x (s1).
  Proof.
    intros.
    unfold XSet.Equal in H. specialize (H x).
    assert (XSet.In x (XSet.union s2 (XSet.union s3 s4))).
    rewrite XSet.union_spec. right.
    rewrite XSet.union_spec ; right ; assumption.
    apply H in H1. assumption.
  Qed.
 
  Lemma set_forall_singleton_lt_r_spec : forall e n,
      lt n e -> XSet.For_all (fun x => lt x e) (XSet.singleton n).
  Proof.
    intros. 
    unfold XSet.For_all. intros.
    apply XSet.singleton_spec in H0.
    specialize (eq_lt) as H'.
    apply (H' x n e H0 H).
  Qed.

  Lemma set_forall_singleton_lt_l_spec : forall e n,
      lt e n -> XSet.For_all (fun x => lt e x) (XSet.singleton n).
  Proof.
    intros. 
    unfold XSet.For_all. intros.
    apply XSet.singleton_spec in H0.
    Print OrderedType.OrderedTypeFacts. 
    specialize (lt_eq) as H'. symmetry in H0. 
    apply (H' e n x H H0).
  Qed.
  
  Theorem set_in_singleton_equal : forall a c,
      XSet.In a (XSet.singleton c) <->
      eq a c.
  Proof.
    intros ; split ; intro H.
    + inversion H ; [assumption | inversion H1].
    + rewrite H ; apply XSet.singleton_spec ; reflexivity.
  Qed.

  Theorem set_in_add_empty_singleton : forall a b, 
      XSet.In a (XSet.add b XSet.empty) <->
      XSet.In a (XSet.singleton b).
  Proof.
    intros ; split ; intro H ; rewrite XSet.add_spec in * ;
      rewrite XSet.singleton_spec in * ; auto ; destruct H ; auto ;
        inversion H.
  Qed.
  
  Theorem set_eq_in_spec : forall a b s,
      eq a b ->
      XSet.In a s ->
      XSet.In b s.
  Proof.
    intros ;
    rewrite <- XSet.elements_spec1 in H0 ;
    rewrite <- XSet.elements_spec1 ;
    specialize (InA_eqA eq_equiv) as H' ;
    apply (H' (XSet.elements s) a b H H0). 
  Qed.      
    
  Lemma set_el_not_in_empty : forall a,
      ~ (XSet.In a XSet.empty).
  Proof.
    intros ; unfold not ;
    intro ; inversion H.
  Qed.

  Lemma set_el_in_set_with_pred : forall p s a,
      XSet.For_all p s ->
      XSet.In a s ->
      p a.
  Proof.
    intros ; unfold XSet.For_all in H ;
    apply (H a) ; assumption.
  Qed.

  Lemma set_in_ina : forall x l,
      XSet.In x (set_list l) ->
      InA o.eq x l.
  Proof.
    intros.
    induction l ; try inversion H ; simpl in * ;
    rewrite XSet.add_spec in H ;
    destruct H ; apply InA_cons ; auto ;
    try (right ; apply IHl) ; assumption.
  Qed.        
  
  Lemma set_hdrel_in_spec : forall a x l,
      Sorted lt l ->
      HdRel lt a l ->
      XSet.In x (set_list l) ->
      lt a x.
  Proof.
    intros ;
    specialize ODT.Inf_alt as H' ;
    specialize (H' l a H) ;
    rewrite H' in H0 ;
    specialize (H0 x) ; apply H0 ;
    apply (set_in_ina x l H1).
  Qed.

  Lemma set_in_forall_l_child_spec : forall b x s1 s2 s3 s4,
      XSet.For_all (fun n : XSet.elt => lt n b) s4 ->
      XSet.Equal (XSet.union s1 (XSet.union s2 s3)) (s4) ->
      XSet.In x s2 ->
      lt x b.
  Proof.
    intros. 
    rewrite set_equal_comm_spec in H0.
    specialize (set_equal_in_l_child_spec x s4 s1 s2 s3) as H'.
    specialize (H' H0 H1). apply H in H'. assumption.
  Qed.
  
  Lemma set_in_forall_r_child_spec : forall b x s1 s2 s3 s4,
      XSet.For_all (fun n : XSet.elt => lt n b) s4 ->
      XSet.Equal (XSet.union s1 (XSet.union s2 s3)) (s4) ->
      XSet.In x s3 ->
      lt x b.
  Proof.
    intros. 
    rewrite set_equal_comm_spec in H0.
    specialize (set_equal_in_r_child_spec x s4 s1 s2 s3) as H'.
    specialize (H' H0 H1). apply H in H'. assumption.
  Qed.
  
  Lemma set_in_forall_l_child_1_spec : forall b x s1 s2 s3 s4,
      XSet.For_all (fun n : XSet.elt => lt b n) s4 ->
      XSet.Equal (XSet.union s1 (XSet.union s2 s3)) (s4) ->
      XSet.In x s2 ->
      lt b x.
  Proof.
    intros. 
    rewrite set_equal_comm_spec in H0.
    specialize (set_equal_in_l_child_spec x s4 s1 s2 s3) as H'.
    specialize (H' H0 H1). apply H in H'. assumption.
  Qed.

  Lemma set_in_forall_r_child_1_spec : forall b x s1 s2 s3 s4,
      XSet.For_all (fun n : XSet.elt => lt b n) s4 ->
      XSet.Equal (XSet.union s1 (XSet.union s2 s3)) (s4) ->
      XSet.In x s3 ->
      lt b x.
  Proof.
    intros. 
    rewrite set_equal_comm_spec in H0.
    specialize (set_equal_in_r_child_spec x s4 s1 s2 s3) as H'.
    specialize (H' H0 H1). apply H in H'. assumption.
  Qed.
  
  Lemma set_in_forall_parent_spec : forall b x s1 s2 s3 s4,
      XSet.For_all (fun n : XSet.elt => lt n b) s4 ->
      XSet.Equal (XSet.union s1 (XSet.union s2 s3)) (s4) ->
      XSet.In x s1 ->
      lt x b.
  Proof.
    intros. 
    rewrite set_equal_comm_spec in H0.
    specialize (set_equal_in_parent_spec x s4 s1 s2 s3) as H'.
    specialize (H' H0 H1). apply H in H'. assumption.
  Qed.

  Lemma set_equal_singleton_in_lt_spec : forall a c s1 s2,
      XSet.Equal (XSet.union (XSet.singleton a) s1) s2 ->
      XSet.For_all (fun n : XSet.elt => lt n c) s2 ->
      lt a c.
  Proof.
    intros.
    apply H0. apply H. apply XSet.union_spec. left.
    rewrite XSet.singleton_spec. reflexivity.
  Qed.

  Lemma set_equal_singleton_in_lt_eq_r_spec : forall a c x s1 s2,
      XSet.Equal (XSet.union (XSet.singleton a) s1) s2 ->
      XSet.For_all (fun n : XSet.elt => lt n c) s2 ->
      eq x c ->
      lt a x.
  Proof.
    intros.
    specialize (set_equal_singleton_in_lt_spec a c s1 s2 H H0) as H'.
    order.
  Qed.

  Lemma set_equal_singleton_in_lt_eq_l_spec : forall a c x s1 s2,
      XSet.Equal (XSet.union (XSet.singleton a) s1) s2 ->
      XSet.For_all (fun n : XSet.elt => lt n c) s2 ->
      eq c x ->
      lt a x.
  Proof.
    intros.
    specialize (set_equal_singleton_in_lt_spec a c s1 s2 H H0) as H'.
    order.
  Qed.
  
  Lemma set_equal_singleton_in_lt_lt_r_spec : forall a c x s1 s2,
      XSet.Equal (XSet.union (XSet.singleton a) s1) s2 ->
      XSet.For_all (fun n : XSet.elt => lt n c) s2 ->
      lt c x ->
      lt a x.
  Proof.
    intros.
    specialize (set_equal_singleton_in_lt_spec a c s1 s2 H H0) as H'.
    order.
  Qed.

  Lemma set_equal_singleton_in_lt_lt_l_spec : forall a c x s1 s2,
      XSet.Equal (XSet.union (XSet.singleton a) s1) s2 ->
      XSet.For_all (fun n : XSet.elt => lt n c) s2 ->
      lt x a ->
      lt x c.
  Proof.
    intros.
    specialize (set_equal_singleton_in_lt_spec a c s1 s2 H H0) as H'.
    order.
  Qed.

  Lemma set_in_union_implies_or_spec : forall x s1 s2 (P : Prop),
      (XSet.In x (XSet.union s1 s2) -> P) ->
      (((XSet.In x s1) -> P) /\ ((XSet.In x s2) -> P)).
  Proof.
    intros.
    rewrite XSet.union_spec in H.
    split ; intros ; apply H ; auto.
  Qed.
       
  Ltac set_reduction :=
    match goal with
    | h : XSet.Equal ?s ?s |- _ =>  
      clear h ; set_reduction
    | h : _ |-  XSet.Equal ?s ?s =>
      apply set_equal_refl_spec ; set_reduction
    | h : (XSet.In ?x (XSet.union ?s1 ?s2) -> ?P) |- _ =>
      apply set_in_union_implies_or_spec in h ; set_reduction                                               
    | h : XSet.For_all _ (XSet.union (_) (_)) |- _ =>
      apply set_union_spec in h ; set_reduction        
    | h : _ |- XSet.In ?x (XSet.union _ _ ) =>
      apply XSet.union_spec ; set_reduction                          
    | h : _ |- XSet.For_all _ (XSet.union _ _) =>
      apply set_union_spec ; set_reduction
    | h : XSet.For_all _ (XSet.singleton _) |- _ =>
      apply set_forall_singleton_predicate_intro_spec in h ; set_reduction
    | h : XSet.In ?a (XSet.singleton ?c) |- _ =>
      apply set_in_singleton_equal in h ; set_reduction
    | h : _ |- XSet.In ?a (XSet.singleton ?a) =>
      apply set_in_singleton_equal ; reflexivity                                     
    | h : _ |- XSet.In ?a (XSet.singleton ?c) =>
      apply set_in_singleton_equal ; set_reduction                             
    | h : XSet.In ?a XSet.empty |- _ =>
      apply set_el_not_in_empty in h ; contradiction
    | h : XSet.In ?a (XSet.union _ _) |- _ =>
      apply XSet.union_spec in h ; set_reduction
    | h : _ |- XSet.For_all ?p XSet.empty =>
      apply set_forall_empty_spec ; set_reduction
    | h : _ |- XSet.Equal (XSet.union ?s1 ?s2) (XSet.union ?s1 ?s3) =>
      apply set_union_reduct_intro_spec ; set_reduction
    | h : _ |- XSet.In ?x (set_list (?l1 ++ ?l2)) =>
      apply set_in_app_or_spec ; set_reduction
    | h : XSet.In ?a (XSet.add ?b XSet.empty) |- _ =>
      apply set_in_add_empty_singleton in h  ; set_reduction
    | h : _ |- XSet.In ?x (XSet.add ?c XSet.empty) =>
      apply set_in_add_empty_singleton ; set_reduction
    | h :  XSet.In ?x (XSet.add ?a (set_list (?l))) |- _ =>
      apply XSet.add_spec in h ; set_reduction
    | h : _ |- XSet.In ?x (XSet.add ?y _) =>
      rewrite XSet.add_spec ; set_reduction
    | h : _ |- XSet.For_all (fun x => lt x ?e) (XSet.singleton ?n) =>
      apply set_forall_singleton_lt_r_spec ; set_reduction
    | h : _ |- XSet.For_all (fun x => lt ?e x) (XSet.singleton ?n) =>
      apply set_forall_singleton_lt_l_spec ; set_reduction
    | h : lt ?b ?c , h1 : XSet.For_all (fun n : XSet.elt => lt n ?b) ?s |-
      XSet.For_all (fun n : XSet.elt => lt n ?c) ?s => 
      apply (set_forall_lt_r_spec b c s h h1)                         
    | h : lt ?b ?c , h1 : XSet.For_all (fun n : XSet.elt => lt ?c n) ?s |-
      XSet.For_all (fun n : XSet.elt => lt ?b n) ?s => 
      apply (set_forall_lt_l_spec b c s h h1)
    | h1 : XSet.Equal (?s1) (XSet.union (?s2) (XSet.union (?s3) (?s4))),
           h2 : XSet.In ?x (?s2) |- XSet.In ?x (?s1) =>
      apply (set_equal_in_parent_spec x s1 s2 s3 s4 h1 h2)
    | h1 : XSet.Equal (?s1) (XSet.union (?s2) (XSet.union (?s3) (?s4))),
           h2 : XSet.In ?x (?s3) |- XSet.In ?x (?s1) =>
      apply (set_equal_in_l_child_spec x s1 s2 s3 s4 h1 h2)
    | h1 : XSet.Equal (?s1) (XSet.union (?s2) (XSet.union (?s3) (?s4))),
           h2 : XSet.In ?x (?s4) |- XSet.In ?x (?s1) =>
      apply (set_equal_in_r_child_spec x s1 s2 s3 s4 h1 h2)
    | h1 : XSet.For_all (fun n : XSet.elt => lt n ?b) ?s4,
      h2 : XSet.Equal (XSet.union ?s1 (XSet.union ?s2 ?s3)) (?s4),
      h3 : XSet.In ?x ?s1 |- 
      lt ?x ?b => apply (set_in_forall_parent_spec b x s1 s2 s3 s4 h1 h2 h3)
    | h1 : XSet.For_all (fun n : XSet.elt => lt n ?b) ?s4,
      h2 : XSet.Equal (XSet.union ?s1 (XSet.union ?s2 ?s3)) (?s4),
      h3 : XSet.In ?x ?s2 |- 
      lt ?x ?b => apply (set_in_forall_l_child_spec b x s1 s2 s3 s4 h1 h2 h3)
    | h1 : XSet.For_all (fun n : XSet.elt => lt n ?b) ?s4,
      h2 : XSet.Equal (XSet.union ?s1 (XSet.union ?s2 ?s3)) (?s4),
      h3 : XSet.In ?x ?s3 |- 
      lt ?x ?b => apply (set_in_forall_r_child_spec b x s1 s2 s3 s4 h1 h2 h3)
    | h1 : XSet.For_all (fun n : XSet.elt => lt ?b n) ?s4,
      h2 : XSet.Equal (XSet.union ?s1 (XSet.union ?s2 ?s3)) (?s4),
      h3 : XSet.In ?x ?s2 |- 
      lt ?b ?x => apply (set_in_forall_l_child_1_spec b x s1 s2 s3 s4 h1 h2 h3)
    | h1 : XSet.For_all (fun n : XSet.elt => lt ?b n) ?s4,
      h2 : XSet.Equal (XSet.union ?s1 (XSet.union ?s2 ?s3)) (?s4),
      h3 : XSet.In ?x ?s3 |- 
      lt ?b ?x => apply (set_in_forall_r_child_1_spec b x s1 s2 s3 s4 h1 h2 h3)
    | h1 : XSet.Equal (XSet.union (XSet.singleton ?a) ?s1) ?s2,
      h2 : XSet.For_all (fun n : XSet.elt => lt n ?c) ?s2 |-
      lt ?a ?c => apply (set_equal_singleton_in_lt_spec a c s1 s2 h1 h2)
    | h1 : XSet.Equal (XSet.union (XSet.singleton ?a) ?s1) ?s2,
      h2 : XSet.For_all (fun n : XSet.elt => lt n ?c) ?s2,
      h3 : eq ?c ?x |-
      lt ?a ?x => apply (set_equal_singleton_in_lt_eq_l_spec a c x s1 s2 h1 h2)
    | h1 : XSet.Equal (XSet.union (XSet.singleton ?a) ?s1) ?s2,
      h2 : XSet.For_all (fun n : XSet.elt => lt n ?c) ?s2,
      h3 : eq ?x ?c |-
      lt ?a ?x => apply (set_equal_singleton_in_lt_eq_r_spec a c x s1 s2 h1 h2)           
    | h1 : XSet.Equal (XSet.union (XSet.singleton ?a) ?s1) ?s2,
      h2 : XSet.For_all (fun n : XSet.elt => lt n ?c) ?s2,
      h3 : lt ?c ?x |-
      lt ?a ?x => apply (set_equal_singleton_in_lt_lt_r_spec a c x s1 s2 h1 h2 h3)
    | h1 : XSet.Equal (XSet.union (XSet.singleton ?a) ?s1) ?s2,
      h2 : XSet.For_all (fun n : XSet.elt => lt n ?c) ?s2,
      h3 : lt ?x ?a |-
      lt ?x ?c => apply (set_equal_singleton_in_lt_lt_l_spec a c x s1 s2 h1 h2 h3)
    | _ => idtac
    end.

  Ltac set_create :=
    match goal with
    | h1 : XSet.Equal ?s1 ?s2,
           h2 : XSet.For_all ?p ?s1 |- _ =>
      apply (set_equal_forall_spec p s1 s2 h1) in h2
    | h : XSet.Equal ?s1 (XSet.union (XSet.singleton ?a) ?s2) |- _ =>
      apply set_equal_union_singleton_r_spec in h              
    | h : XSet.Equal (XSet.union (XSet.singleton ?a) ?s1) ?s2 |- _ =>
      apply set_equal_union_singleton_l_spec in h     
    | h : XSet.For_all ?p1 ?t |- XSet.For_all ?p2 ?t =>
      apply ( set_predicate_spec p1) ; [intros ; omega | assumption]
    | h1 : XSet.For_all ?p1 ?s,
           h2 : XSet.In ?a ?s |- _ =>
      specialize (set_el_in_set_with_pred _ _ a h1 h2) ; simpl in * ; intro ; clear h1
    | h : XSet.Equal (_) (_) |- _ =>
      assert (com' := h) ; 
      apply set_equal_comm_spec in com'                   
    | _ => idtac
    end.

End OrderedSet.
