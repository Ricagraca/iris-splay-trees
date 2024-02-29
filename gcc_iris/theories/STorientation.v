From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual LibInt.
From stdpp Require Import gmap.
From iris.bi Require Import big_op.
From iris_time.heap_lang Require Import proofmode.
From iris_time Require Import Combined.

Section orientation.

  Inductive orientation :=
  |LEFT
  |RIGHT.

  Definition invert_orientation (o : orientation) :=
    match o with
    | LEFT => RIGHT
    | RIGHT => LEFT
    end.

  Definition orientation_op (o : orientation) :=
    match o with
    | LEFT => Z.gt
    | RIGHT => Z.lt
    end.
  
  Definition orientation_eq (o1 o2 : orientation) :=
    match o1 with
    | LEFT =>
      match o2 with
      | LEFT => true
      | RIGHT => false
      end
    | RIGHT =>
      match o2 with
      | LEFT => false
      | RIGHT => true
      end
    end.

  Lemma invert_orientation_different_then_equal : forall o o',
      ¬(o = invert_orientation o') -> o = o'.
  Proof.
    intros.
    destruct o, o' ; simpl in H ; auto ; exfalso ; apply H ; auto.
  Qed.

  Lemma different_orientation_then_equal_invert : forall o o',
      ¬(o = o') -> o = (invert_orientation o').
  Proof.
    intros.
    destruct o, o' ; simpl in H ; auto ; exfalso ; apply H ; auto.
  Qed.

  Lemma involutive_invert : forall o,
      invert_orientation (invert_orientation o) = o.
  Proof.
    intros.
    destruct o ; simpl ; auto.
  Qed.
  
  Lemma o_diff_o' : forall o,
      ¬((invert_orientation o) = o).
  Proof.
    intros.
    destruct o ; simpl ; auto.
  Qed.
  
  Lemma o_op_a_b_b_a_false : forall o a b P,
      orientation_op o b a ->
      orientation_op o a b ->
      P.
  Proof.
    intros.
    destruct o ; simpl ; auto ; simpl in * ; try lia.
  Qed.
  
  Lemma o_must_be_equal : forall o1 o2 a b,
      orientation_op o1 a b ->
      orientation_op o2 a b ->
      o1 = o2.
  Proof.
    intros o1 o2.
    destruct o1, o2 ; auto ; simpl in * ; lia.
  Qed.
  
  Lemma orientation_op_transitivity : forall o a b c,
      orientation_op o a b ->
      orientation_op o b c ->
      orientation_op o a c.
  Proof.
    intros.
    destruct o ; auto ; simpl in * ; lia.
  Qed.

  Lemma orientation_trichotomy : forall o a b,
      orientation_op o a b \/ orientation_op (invert_orientation o) a b \/ a = b.
  Proof.
    intros.
    destruct o ; auto ; simpl in * ; lia.
  Qed.

  Lemma invert_orientation_diff : forall o a b P,
      orientation_op o a b ->
      orientation_op (invert_orientation o) a b ->
      P.
  Proof.
    intros.
    destruct o ; auto ; simpl in * ; lia.
  Qed.
  
End orientation.

Ltac storientation_tac :=
  match goal with
  (* same_edge_for_same_orientation_if_bst *)
  | h1 : ((invert_orientation ?o) = ?o) |- _ =>
    apply o_diff_o' in h1 ; contradiction
  | h1 : (?o = (invert_orientation ?o)) |- _ =>
    symmetry in h1 ; 
    apply o_diff_o' in h1 ; contradiction
  | h1 : (orientation_op ?o ?b ?a), h2 : (orientation_op ?o ?a ?b) |- ?P =>
    apply (o_op_a_b_b_a_false o a b P) ; auto
  | h1 : (orientation_op ?o1 ?a ?b), h2 : (orientation_op ?o2 ?a ?b) |- (?o1 = ?o2) =>
    apply (o_must_be_equal o1 o2 a b) ; auto
  | h1 : (orientation_op ?o ?a ?b), h2 : (orientation_op ?o ?b ?c) |- (orientation_op ?o ?a ?c) =>
    apply (orientation_op_transitivity o a b c) ; auto
  | h1 : (orientation_op ?o ?a ?a) |- _ =>
    destruct o ; simpl in * ; lia
  | h1 : (orientation_op ?o ?a ?b), h2 : (orientation_op (invert_orientation ?o) ?a ?b) |- _ =>
    destruct o ; auto ; simpl in * ; lia
  | _ => idtac
  end.

Lemma ex1 : forall o,
    ¬((invert_orientation o) = o).
Proof.
  intros. intro. storientation_tac.
Qed.
  
Lemma ex2 : forall o,
    ¬(o = (invert_orientation o)).
Proof.
  intros. intro. storientation_tac.
Qed.

Lemma ex3 : forall o a b P,
    orientation_op o b a ->
    orientation_op o a b ->
    P.
Proof.
  intros.
  storientation_tac.
Qed.

Lemma ex4 : forall o1 o2 a b,
    orientation_op o1 a b ->
    orientation_op o2 a b ->
    o1 = o2.
Proof.
  intros.
  storientation_tac.
Qed.

Lemma ex5 : forall o a b c,
    orientation_op o a b ->
    orientation_op o b c ->
    orientation_op o a c.
Proof.
  intros.
  storientation_tac.
Qed.
