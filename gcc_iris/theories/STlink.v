From ST Require Import STorientation STpredicate.
From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual LibInt.
From iris_time.union_find.math Require Import TLCBuffer.
From stdpp Require Import gmap.
From iris.bi Require Import big_op.
From iris_time.heap_lang Require Import proofmode.
From iris_time Require Import Combined.

Section STInvProofLink.
  
  Notation elem := loc.
  
  (* Graph structure *)
  Variable p : elem.
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z.       (* weight nodes *)
  Variable M : gmap elem content. (* view of the memory *)
  
  (* 

                 x                 x
               o/ \o      -->    o/ \o
               y  z             (z  z)

   *)
 
  Lemma same_edge_for_same_orientation_if_bst : forall F x y o z,
    Inv p D F V W ->    
    F x y o ->
    F x z o ->
    z = y.
  Proof.
    intros.
    inversion H. unfold is_bst in *.
    unfold searchtree in *. unpack.
    unfold binarytree in H7.
    destruct (bool_decide (z = y)) eqn:E.
    - apply bool_decide_eq_true in E. auto.
    - apply bool_decide_eq_false in E.
      specialize (H6 x y z o o E H0 H1).
      exfalso ; apply H6 ; auto.
  Qed.

  (*
  
  If F x y LEFT then V x > V y:

                       x 
                      /  
                     y


  If F x y RIGHT then V x < V y:

                       x 
                        \  
                         y

   *)

  Lemma edge_value_left_if_bst : forall F x y,
      Inv p D F V W ->    
      (F x y LEFT -> V x > V y). 
  Proof.
    intros F x y Inv H.
    inversion Inv. unfold is_bst in *.
    destruct Inv_bst as [confined [rootisindomain [isroot [searchtree [binarytree finite]]]]].
    assert (F x y LEFT /\ path F y y) as FPxyl. split ; auto using path_refl.
    destruct searchtree as [searchtreeleft searchtreeright].
    apply searchtreeleft in FPxyl. destruct FPxyl. auto.
  Qed.

  Lemma edge_value_right_if_bst : forall F x y,
      Inv p D F V W ->    
      (F x y RIGHT -> V x < V y).
  Proof.
    intros F x y Inv H.
    inversion Inv. unfold is_bst in *.
    destruct Inv_bst as [confined [rootisindomain [isroot [searchtree [binarytree finite]]]]].
    assert (F x y RIGHT /\ path F y y) as FPxyr. split ; auto using path_refl.
    destruct searchtree as [searchtreeleft searchtreeright].
    apply searchtreeright in FPxyr. destruct FPxyr. auto.
  Qed.

  (*

  If F x y o and F x y u then o = u:

                       x    x
                       | u  | o
                       y    y 

   *)

  Lemma unique_direction_if_bst : forall F x y u o,
      Inv p D F V W ->    
      F x y o ->
      F x y u ->
      u = o.
  Proof.
    intros F x y u o Inv E1 E2.
    destruct u, o ; auto.
    - pose proof (edge_value_left_if_bst F x y Inv E2).
      pose proof (edge_value_right_if_bst F x y Inv E1).
      lia.
    - pose proof (edge_value_left_if_bst F x y Inv E1).
      pose proof (edge_value_right_if_bst F x y Inv E2).
      lia.
  Qed.

  (*
  A splay tree cannot have a node pointing to itself:

                       x <-
                      / \ /
                     y   ^
                    / \
                   zl zr

   *)

  Lemma cant_point_to_itself_if_bst : forall F p' o, 
      Inv p D F V W ->
      ~ (F p' p' o).
  Proof.
    intros F p' o Inv. intro N.
    inversion Inv. unfold is_bst in *.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    destruct o.
    + assert (F p' p' LEFT /\ path F p' p') as FPp'l.
      split ; auto using path_refl.
      apply searchleft in FPp'l. lia.
    + assert (F p' p' RIGHT /\ path F p' p') as FPp'r.
      split ; auto using path_refl.
      apply searchright in FPp'r. lia.
  Qed.
  
  
  (*

                       x 
                      / \
                     y   
              
   then x different from y if bst

   *)

  Lemma different_pointers_if_bst : forall F x y o, 
      Inv p D F V W -> F x y o -> ¬(x = y).
  Proof.
    intros F x y o Inv H.
    intro. subst. apply (cant_point_to_itself_if_bst F y o Inv H).
  Qed.

  Lemma different_pointers_split_if_bst : forall F x y z, 
      Inv p D F V W ->
      F x y  LEFT ->
      F x z RIGHT -> ¬(y = z).
  Proof.
    intros F x y z Inv E1 E2.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    intro. subst.
    pose proof (edge_value_left_if_bst F x z Inv E1).
    pose proof (edge_value_right_if_bst F x z Inv E2).
    lia.
  Qed.

  Lemma no_single_step_cycles_if_bst : forall F x y o u, 
      Inv p D F V W ->
      ¬ (F x y o /\ F y x u).
  Proof.
    intros F x y o u Inv [E1 E2].
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    destruct o.
    + specialize (searchleft x y x).
      assert (F x y LEFT /\ path F y x) as FPxxl.
      split ; auto. apply path_single with u ; auto.
      apply searchleft in FPxxl. lia.
    + specialize (searchright x y x).
      assert (F x y RIGHT /\ path F y x) as FPxxr.
      split ; auto. apply path_single with u ; auto.
      apply searchright in FPxxr. lia.
  Qed.

  Lemma no_pointer_to_root_if_bst : forall F x o, 
      Inv p D F V W ->
      ¬(F x p o).
  Proof.
    intros F x o Inv E.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    apply confined in E as Dxp.
    destruct Dxp as [xindomain pindomain].
    apply (isroot x o) in xindomain.
    destruct xindomain as [NExp Ppx].
    contradiction.
  Qed.

  Lemma different_orientation_false_if_bst : forall F x y, 
      Inv p D F V W ->
      F x y LEFT ->
      F x y RIGHT ->
      False.
  Proof.
    intros F x y Inv H1 H2.
    pose proof (unique_direction_if_bst F x y LEFT RIGHT).
    assert (LEFT = RIGHT).
    apply H ; auto. discriminate.
  Qed.

  Lemma different_pointer_chain_2_edge : forall F x y z o u,
      Inv p D F V W ->
      F x y o ->
      F y z u ->
      ¬(x = z).
  Proof.
    intros.
    intro. subst.
    pose proof (no_single_step_cycles_if_bst F z y o u H).
    apply H2. split ; auto.
  Qed.  
    
  Lemma different_pointer_chain_3_edge : forall F x y z t o u d,
      Inv p D F V W ->
      F x y o ->
      F y z u ->
      F z t d ->
      ¬(x = t).
  Proof.
    intros.
    intro. subst.
    inversion H. unfold is_bst in *.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    destruct o.
    + assert (F t y LEFT /\ path F y t) as FPttl.
      split ; auto. apply path_trans with z.
      apply path_single with u ; auto.
      apply path_single with d ; auto.
      apply searchleft in FPttl ; lia.
    + assert (F t y RIGHT /\ path F y t) as FPttr.
      split ; auto. apply path_trans with z.
      apply path_single with u ; auto.
      apply path_single with d ; auto.
      apply searchright in FPttr. lia.
  Qed.  
  
  Lemma no_path_right_join_from_edge_bifurcation_if_inv :
    forall F x y z,
      Inv p D F V W ->
      F x y RIGHT ->
      F x z LEFT ->
      path F y z ->
      False.
  Proof.
    intros F x y z Inv E1 E2 Pyz.
    inversion Inv.
    unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    assert (F x y RIGHT /\ path F y z) as FPxzr. split ; auto.
    assert (F x z LEFT /\ path F z z) as FPxzl. split ; auto using path_refl.
    apply searchright in FPxzr.
    apply searchleft in FPxzl.
    lia.
  Qed.
  
  Lemma no_path_left_join_from_edge_bifurcation_if_inv :
    forall F x y z,
      Inv p D F V W ->
      F x y RIGHT ->
      F x z LEFT ->
      path F z y ->
      False.
  Proof.
    intros F x y z Inv E1 E2 Pzy.
    inversion Inv.
    unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    assert (F x y RIGHT /\ path F y y) as FPxyr. split ; auto using path_refl.
    assert (F x z LEFT /\ path F z y) as FPxyl. split ; auto.
    apply searchright in FPxyr.
    apply searchleft in FPxyl.
    lia.
  Qed.

  Lemma no_inverted_orientation_for_same_edge_if_bst :
    forall F x y o,
      Inv p D F V W ->
      F x y o -> 
      F x y (invert_orientation o) ->
      False.
  Proof.
    intros.
    pose proof (unique_direction_if_bst F x y o (invert_orientation o) H H1 H0).
    destruct o ; simpl in H2 ; discriminate.
  Qed.

  Lemma different_orientation_different_end_if_bst :
    forall F x y z o,
      Inv p D F V W ->
      F x y o -> 
      F x z (invert_orientation o) ->
      ¬(z = y).
  Proof.
    intros.
    destruct o ;
    pose proof (different_pointers_split_if_bst F x y z) ;
    intro ; subst ; apply H2 ; auto.
  Qed.

  Lemma orientation_edge_value :
    forall F x y o,
      Inv p D F V W ->
      F x y o ->
      orientation_op o (V x) (V y).
  Proof.
    intros F x y o Inv **.
    destruct o ; simpl.
    + apply edge_value_left_if_bst in H ; auto.
    + apply edge_value_right_if_bst in H ; auto.
  Qed.
  
End STInvProofLink.


Ltac stlink_tac :=
  match goal with
  (* same_edge_for_same_orientation_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W , h2 : ?F ?x ?y ?o, h3 : ?F ?x ?z ?o |- (?y = ?z) =>
    apply (same_edge_for_same_orientation_if_bst p D V W F x z o y h1 h3 h2)
  (* edge_value_left_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y LEFT |- ?V ?x > ?V ?y =>
    apply (edge_value_left_if_bst p D V W F x y h1) in h2 ; lia
  (* edge_value_left_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y LEFT |- ?V ?y < ?V ?x =>
    apply (edge_value_left_if_bst p D V W F x y h1) in h2 ; lia
  (* edge_value_right_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y RIGHT |- ?V ?x < ?V ?y =>
    apply (edge_value_right_if_bst p D V W F x y h1) in h2 ; lia
  (* edge_value_right_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y RIGHT |- ?V ?y > ?V ?x =>
    apply (edge_value_right_if_bst p D V W F x y h1) in h2 ; lia
  (* unique_direction_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?o, h3 : ?F ?x ?y ?u |- ?u = ?o =>
    apply (unique_direction_if_bst p D V W F x y u o h1 h2 h3)
  (* cant_point_to_itself_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?x ?o |- _ =>
    exfalso ; apply (cant_point_to_itself_if_bst p D V W F x o h1 h2)
  (* different_pointers_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?p1 ?p2 ?o |- ¬(?p1 = ?p2) =>
    apply (different_pointers_if_bst p D V W F p1 p2 o h1) in h2 ; lia
  (* different_pointers_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?p1 ?p2 ?o |- ¬(?p2 = ?p1) =>
    apply (different_pointers_if_bst p D V W F p1 p2 o h1) in h2 ; lia

  (* different_pointers_split_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?p1 ?p2 LEFT, h3 : ?F ?p1 ?p3 RIGHT |- ¬(?p2 = ?p3) =>
    apply (different_pointers_split_if_bst p D V W F p1 p2 p3 h1 h2 h3)
          
  (* different_pointers_split_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?p1 ?p2 LEFT, h3 : ?F ?p1 ?p3 RIGHT |- ¬(?p3 = ?p2) =>
    apply (different_pointers_split_if_bst p D V W F p1 p2 p3 h1 h2) in h3 ; lia
          
  (* no_pointer_to_root_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?p ?o |- _ =>
    exfalso ; apply (no_pointer_to_root_if_bst p D V W F x o h1 h2)        
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y LEFT, h3 : ?F ?x ?y RIGHT |- _ =>
    exfalso ; apply (different_orientation_false_if_bst p D V W F x y h1 h2 h3)    
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?o, h3 : ?F ?y ?z ?u |- ¬(?x = ?z) =>
    apply (different_pointer_chain_2_edge p D V W F x y z o u h1 h2 h3)    
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?o, h3 : ?F ?y ?z ?u |- ¬(?z = ?x) =>
    apply (different_pointer_chain_2_edge p D V W F x y z o u h1 h2) in h3 ; lia    
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?o, h3 : ?F ?y ?z ?u, h4 : ?F ?z ?t ?d  |-
    ¬(?t = ?x) =>
    apply (different_pointer_chain_3_edge p D V W F x y z t o u d h1 h2 h3) in h4 ; lia 
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?o, h3 : ?F ?y ?z ?u, h4 : ?F ?z ?t ?d  |-
    ¬(?x = ?t) =>
    apply (different_pointer_chain_3_edge p D V W F x y z t o u d h1 h2 h3) in h4 ; lia 
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y RIGHT, h3 : ?F ?x ?z LEFT, h4 : path ?F ?y ?z |- _ =>
    exfalso ; apply (no_path_right_join_from_edge_bifurcation_if_inv p D V W F x y z h1 h2 h3 h4)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y RIGHT, h3 : ?F ?x ?z LEFT, h4 : path ?F ?z ?y |- _ =>
    exfalso ; apply (no_path_left_join_from_edge_bifurcation_if_inv p D V W F x y z h1 h2 h3 h4)
                    
  | h1 : Inv ?p ?D ?F ?V ?W,
         h2 : ?F ?x ?y ?o,
              h3 : ?F ?x ?y (invert_orientation ?o) |- _ =>
    exfalso ; apply (no_inverted_orientation_for_same_edge_if_bst p D V W F x y o h1 h2 h3)
                    
  | h1 : Inv ?p ?D ?F ?V ?W,
         h2 : ?F ?x ?y ?o,
              h3 : ?F ?x ?z (invert_orientation ?o) |- ¬(?y = ?z) =>
    apply (different_orientation_different_end_if_bst p D V W F x y z o h1 h2) in h3 ;
    lia

  | h1 : Inv ?p ?D ?F ?V ?W,
         h2 : ?F ?x ?y ?o,
              h3 : ?F ?x ?z (invert_orientation ?o) |- ¬(?z = ?y) =>
    apply (different_orientation_different_end_if_bst p D V W F x y z o h1 h2) in h3 ;
    lia
      
  | h1 : Inv ?p ?D ?F ?V ?W,
    h2 : ?F ?x ?y ?o |- orientation_op ?o (?V ?x) (?V ?y) =>
    apply (orientation_edge_value p D V W F x y o h1 h2) ; auto
                    
  | _ => idtac
  end.

Example ex1 : forall p D V F W x y o z,
    Inv p D F V W ->    
    F x y o ->
    F x z o ->
    z = y.
Proof.
  intros. stlink_tac.
Qed.

Example ex2 : forall p D V F W x y,
    Inv p D F V W ->    
    F x y LEFT ->
    V y < V x.
Proof.
  intros. stlink_tac.
Qed.

Example ex3 : forall p D V F W x y,
    Inv p D F V W ->    
    F x y RIGHT ->
    V x < V y.
Proof.
  intros. stlink_tac.
Qed.

Example ex4 : forall p D V F W x y o u,
    Inv p D F V W ->    
    F x y o ->
    F x y u ->
    o = u.
Proof.
  intros. stlink_tac.
Qed.

Example ex5 : forall p D V F W x o P,
    Inv p D F V W ->    
    F x x o ->
    P.
Proof.
  intros. stlink_tac.
Qed.

Example ex6 : forall p D V F W x y o, 
    Inv p D F V W ->
    F x y o ->
    ¬(x = y).
Proof.
  intros. stlink_tac.
Qed.

Example ex7 : forall p D V F W x y z, 
    Inv p D F V W ->
    F x y  LEFT ->
    F x z RIGHT -> ¬(y = z).
Proof.
  intros. stlink_tac.
Qed.

Example ex8 : forall p D V F W x o, 
    Inv p D F V W ->
    ¬(F x p o).
Proof.
  intros. intro. stlink_tac.
Qed.

Example ex9 : forall p D V F W x y P,
    Inv p D F V W ->    
    F x y LEFT ->
    F x y RIGHT ->
    P.
Proof.
  intros. stlink_tac.
Qed.

Example ex10 : forall p D V F W x y z o u,
    Inv p D F V W ->    
    F x y o ->
    F y z u ->
    ¬(z = x).
Proof.
  intros. stlink_tac.
Qed.

Example ex11 : forall p D V F W x y z t o u d,
    Inv p D F V W ->    
    F x y o ->
    F y z u ->
    F z t d ->
    ¬(t = x).
Proof.
  intros. stlink_tac.
Qed.

Example ex12 : forall p D V F W x y z P,
    Inv p D F V W ->    
    F x y LEFT ->
    F x z RIGHT ->
    path F y z ->
    P.
Proof.
  intros. stlink_tac.
Qed.

Example ex13 : forall p D V F W x y z P,
    Inv p D F V W ->    
    F x y LEFT ->
    F x z RIGHT ->
    path F z y ->
    P.
Proof.
  intros. stlink_tac.
Qed.

Example ex14 : forall p D V F W x y o P,
    Inv p D F V W ->    
    F x y o ->
    F x y (invert_orientation o) ->
    P.
Proof.
  intros. stlink_tac.
Qed.

Example ex15 : forall p D V F W x y z o,
    Inv p D F V W ->    
    F x y o ->
    F x z (invert_orientation o) ->
    ¬(z = y).
Proof.
  intros. stlink_tac.
Qed.

Example ex16 : forall p D V F W x y z o,
    Inv p D F V W ->    
    F x y o ->
    F x z (invert_orientation o) ->
    ¬(y = z).
Proof.
  intros. stlink_tac.
Qed.

Example ex17 : forall p D V F W x y o,
    Inv p D F V W ->    
    F x y o ->
    orientation_op o (V x) (V y) .
Proof.
  intros. stlink_tac.
Qed.
