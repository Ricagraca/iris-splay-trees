Include Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Lemma hdrel_app : forall X (lt : X -> X -> Prop) a l1 l2,
    HdRel lt a (l1 ++ l2) ->
    HdRel lt a l1.
Proof.
  intros.
  destruct l1.
  + apply HdRel_nil.
  + apply HdRel_cons.
    replace ((x :: l1) ++ l2) with (x :: (l1 ++ l2)) in H ; auto.
    apply HdRel_inv in H. assumption.
Qed.

Lemma sorted_app : forall X (lt : X -> X -> Prop) l1 l2,
    Sorted lt (l1 ++ l2) ->
    Sorted lt l1 /\ Sorted lt l2.
Proof.
  intros X lt l1.
  induction l1.
  + simpl in *. split ; [apply Sorted_nil|assumption].
  + intros. inversion H ; subst. apply IHl1 in H2.
    destruct H2 ; split ; auto. apply hdrel_app in H3.
    apply Sorted_cons ; auto.
Qed.
    
    
