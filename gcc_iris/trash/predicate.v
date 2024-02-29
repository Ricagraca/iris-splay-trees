From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual
                        LibInt.
From iris_time.union_find.math Require Import TLCBuffer.

From stdpp Require Import gmap.

From iris.bi Require Import big_op.
From iris_time.heap_lang Require Import proofmode.
From iris_time Require Import Combined.
Require Import Coq.Logic.FunctionalExtensionality.

(* An object in the Union Find data structure is represented by an
   heap_lang location. *)
Notation elem := loc.

(* The logical type of the content of a vertex. *)
Inductive content :=
| NodeB : Z -> elem -> elem -> content
| NodeL : Z -> elem -> content
| NodeR : Z -> elem -> content
| NodeN : Z -> content.

Definition val_of_content (c : content) : option val :=
  match c with
  | NodeB k v1 v2 => Some (SOMEV(#k, (#v1,#v2)))
  | NodeL k v1 => Some (SOMEV(#k, (#v1,NONEV)))
  | NodeR k v2 => Some (SOMEV(#k, (NONEV,#v2)))
  | NodeN k => Some (SOMEV(#k, (NONEV,NONEV)))
  end.

(**
F x y /\ F x z -> é possivel y =/= z

                    F x y LEFT /\ F x z RIGHT
                    
                     x
                    / \
                   y   z
**)   
                 
Section SplayTree.
  
(* Add orientation to edge *)
Inductive orientation :=
|LEFT
|RIGHT.   

Inductive path : (elem -> elem -> orientation -> Prop) -> elem -> elem -> Prop :=
  path_refl : forall F x, path F x x
| path_single  : forall (F : elem -> elem -> orientation -> Prop) x y o, F x y o -> path F x y
| path_trans : forall F x y z, path F x y -> path F y z -> path F x z.
  
Variable x y r : elem.
Variable v : val.
Variable R : elem.
Variable D : LibSet.set elem.   (* domain *)
Variable F : elem -> elem -> orientation -> Prop. (* edges *)
Variable V : elem -> Z.       (* data stored in nodes *)
Variable M : gmap elem content. (* view of the memory *)

Definition binarytree (F : elem -> elem -> orientation -> Prop) :=
  forall x y z l r,
    ~ (z = y) -> 
    F x y l -> F x z r ->
    ~ (r = l).


(*

      r1      r2
     /  \    /
    x   y   /
        \  /
         z 

*)

Definition isroot (F :  elem -> elem -> orientation -> Prop) r :=
  (forall x o, ~ (F x r o) /\ path F r x).

Definition confined' (D : LibSet.set elem) (F :  elem -> elem -> orientation -> Prop) :=
  forall x y o, F x y o -> x \in D /\ y \in D.

Definition searchtree (F :  elem -> elem -> orientation -> Prop) (V : elem -> Z) :=
  (forall x y z, (F x y LEFT  /\ path F y z) -> (V x > V y)%Z /\ (V x > V z)%Z) /\
  (forall x y z, (F x y RIGHT /\ path F y z) -> (V x < V y)%Z /\ (V x < V z)%Z).

Definition rootisindomain (R : elem) (D : LibSet.set elem) := 
  R \in D.
  
Definition is_bst :=
  (confined' D F) /\
  (rootisindomain R D) /\ 
  (isroot F R) /\
  (searchtree F V) /\
  (binarytree F).

Definition descendants F r :=
   \set{ y | path F r y}.

Definition Mem (D : LibSet.set elem)
           (F : elem -> elem -> orientation -> Prop)
           (V : elem -> Z) 
           (M : gmap elem content) : Prop :=
  forall x, x \in D ->
    match M!!x with
    | Some (NodeB v p1 p2) => F x p1 LEFT  /\ F x p2 RIGHT /\ V x = v
    | Some (NodeL v p1) => F x p1 LEFT  /\ V x = v
    | Some (NodeR v p2) => F x p2 RIGHT /\ V x = v
    | Some (NodeN v) => V x = v
    | None => False
    end.

End SplayTree.

Lemma val_of_content_Some :
  forall c v,
    val_of_content c = Some v ->
    (∃ (k : Z) (e1 e2 : elem), v = SOMEV(#k,(#e1,#e2)) /\ c = NodeB k e1 e2) \/
    (∃ (k : Z) (e1 : elem), v = SOMEV(#k,(#e1,NONEV)) /\ c = NodeL k e1) \/
    (∃ (k : Z) (e2 : elem), v = SOMEV(#k,(NONEV,#e2)) /\ c = NodeR k e2) \/
    (∃ (k : Z), v = SOMEV(#k,(NONEV,NONEV)) /\ c = NodeN k).
Proof.
  introv Hv. destruct c ; simpl in Hv ; inversion Hv.
  - left. exists z l l0. inversion Hv. auto.
  - right. left. inversion Hv. exists z l. auto.
  - right. right. left. exists z l. auto.
  - right. right. right. exists z. auto.
Qed.  
     
Section SplayTreePredicate.

Record Inv R D F V : Prop := {
  Inv_bst  : is_bst R D F V
}.

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

Lemma outgoing_edge_with_same_orientation_have_same_outgoing_node_if_bst : forall p D F V x y o z,
    Inv p D F V ->    
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

Lemma edge_value_left_if_bst : forall p D F V x y,
    Inv p D F V ->    
    (F x y LEFT -> V x > V y). 
Proof.
  intros.
  inversion H. unfold is_bst in *.
  unfold searchtree in *. unpack.
  assert (F x y LEFT /\ path F y y). split ; auto using path_refl.
  apply H4 in H7. destruct H7. auto.
Qed.

Lemma edge_value_right_if_bst : forall p D F V x y,
    Inv p D F V ->    
    (F x y RIGHT -> V x < V y).
Proof.
  intros.
  inversion H. unfold is_bst in *.
  unfold searchtree in *. unpack.
  assert (F x y RIGHT /\ path F y y). split ; auto using path_refl.
  apply H6 in H7. destruct H7. auto.
Qed.

(*

  If F x y o and F x y u then o = u:

                       x    x
                       | u  | o
                       y    y 

*)

Lemma unique_direction_if_bst : forall p D F V x y u o,
    Inv p D F V ->    
    F x y o ->
    F x y u ->
    u = o.
Proof.
  intros.
  destruct u, o ; auto.
  - pose proof (edge_value_left_if_bst p D F V x y H H1).
    pose proof (edge_value_right_if_bst p D F V x y H H0).
    lia.
  - pose proof (edge_value_left_if_bst p D F V x y H H0).
    pose proof (edge_value_right_if_bst p D F V x y H H1).
    lia.
Qed.
    
Lemma path_right_left_step_beginning_if_bst : forall p D F V x y,
    Inv p D F V ->
    path F x y ->
    ~(x = y) ->
    exists t, (F x t RIGHT \/ F x t LEFT) /\ path F t y.
Proof.
  intros.
  induction H0.
  + exfalso. apply H1 ; auto.
  + exists y. split ; auto using path_refl. destruct o ; auto.
  + destruct (bool_decide (x = y)) eqn:XY.
    - apply bool_decide_eq_true in XY. subst.
      specialize (IHpath2 H H1).
      destruct IHpath2. 
      exists x. auto.
    - apply bool_decide_eq_false in XY. subst.
      specialize (IHpath1 H XY).
      destruct IHpath1. 
      exists x0. unpack. split ; auto.
      apply path_trans with y ; auto.     
Qed.

Lemma path_right_left_step_end_if_bst : forall p D F V x y,
    Inv p D F V ->
    path F x y ->
    ~(x = y) ->
    exists t, (F t y RIGHT \/ F t y LEFT) /\ path F x t.
Proof.
  intros.
  induction H0.
  + exfalso. apply H1 ; auto.
  + exists x. split ; auto using path_refl. destruct o ; auto.
  + destruct (bool_decide (x = y)) eqn:XY.
    - apply bool_decide_eq_true in XY. subst.
      specialize (IHpath2 H H1).
      destruct IHpath2. 
      exists x. auto.
    - apply bool_decide_eq_false in XY.
      destruct (bool_decide (y = z)) eqn:E.
      * apply bool_decide_eq_true in E. subst.
        auto.
      * apply bool_decide_eq_false in E.
        specialize (IHpath2 H E ).
        specialize (IHpath1 H XY ).
        destruct IHpath2 ; auto.
        exists x0. unpack. split ; auto.        
        apply path_trans with y ; auto.     
Qed.

Lemma path_value_if_bst : forall p D F V x y,
    Inv p D F V ->
    path F x y ->
    ~(x = y) -> 
    V x < V y \/ V y < V x.
Proof.
  intros.
  inversion H. unfold is_bst in *.
  unfold searchtree in *. unpack.
  pose proof (path_right_left_step_beginning_if_bst p D F V x y H H0 H1).
  destruct H8. unpack. destruct H8.
  - assert (F x x0 RIGHT /\ path F x0 y). split ; auto. 
    specialize (H7 x x0 y H10). lia.
  - assert (F x x0 LEFT /\ path F x0 y). split ; auto. 
    specialize (H5 x x0 y H10). lia.
Qed.

(*
  A splay tree cannot have a node pointing to itself:

                       x <-
                      / \ /
                     y   ^
                    / \
                   zl zr

*)

Lemma cant_point_to_itself_if_bst : forall p D F V p' o, 
    Inv p D F V ->
    ~ (F p' p' o).
Proof.
  intros. unfold not.
  intros. inversion H. unfold is_bst in *.
  unfold searchtree in *.
  unpack. destruct o.
  + assert (F p' p' LEFT /\ path F p' p').
    split ; auto using path_refl.
    apply H4 in H7. lia.
  + assert (F p' p' RIGHT /\ path F p' p').
    split ; auto using path_refl.
    apply H6 in H7. lia.
Qed.


(*

                       x 
                      / \
                     y   
              
   então F x y o

*)

Lemma diffent_pointers_if_bst : forall p D F V p' p'' o, 
  Inv p D F V -> F p' p'' o -> not (p' = p'').
Proof.
  intros.
  inversion H. unfold is_bst in Inv_bst0.
  unfold not. intros. subst. apply (cant_point_to_itself_if_bst p D F V p'' o H) in H0.
  auto.
Qed.

Lemma diffent_pointers_split_if_bst : forall p D F V p' p'' p''', 
    Inv p D F V ->
    F p' p''  LEFT ->
    F p' p''' RIGHT -> not (p'' = p''').
Proof.
  intros.
  inversion H. unfold is_bst in Inv_bst0.
  unpack. inversion H. unfold not. intros.
  unfold searchtree in H6.
  unpack. subst.
  pose proof (edge_value_left_if_bst p D F V p' p''' H H0).
  pose proof (edge_value_right_if_bst p D F V p' p''' H H1).
  lia.
Qed.

Lemma no_single_step_cycles_if_bst : forall p D F V p' p'' o u, 
    Inv p D F V ->
    F p' p'' o ->
    F p'' p' u ->
    False.
Proof.
  intros.
  inversion H. unfold is_bst in Inv_bst0.
  unpack. unfold searchtree in * ; unpack.
  destruct o.
  + specialize (H6 p' p'' p').
    assert (F p' p'' LEFT /\ path F p'' p').
    - split ; auto. apply (path_single F p'' p') in H1.
      auto.
    - apply H5 in H8. lia.
  + specialize (H7 p' p'' p').
    assert (F p' p'' RIGHT /\ path F p'' p').
    - split ; auto. apply (path_single F p'' p') in H1.
      auto.
    - apply H7 in H8. lia.   
Qed.

Lemma no_cycles_if_bst : forall p D F V p' p'' o , 
    Inv p D F V ->
    F p' p'' o ->
    path F p'' p' ->
    False.
Proof.
  intros.
  inversion H. unfold is_bst in Inv_bst0.
  unpack. unfold searchtree in * ; unpack.
  destruct o.
  + specialize (H6 p' p'' p').
    assert (F p' p'' LEFT ∧ path F p'' p'). split ; auto.
    apply H5 in H8. lia.
  + specialize (H7 p' p'' p').
    assert (F p' p'' RIGHT ∧ path F p'' p'). split ; auto.
    apply H7 in H8. lia.
Qed.

Lemma diffent_pointers_for_path_if_bst : forall p D F V p' p'' p''' o, 
    Inv p D F V ->
    F p' p'' o ->
    path F p'' p''' -> not (p' = p'''). 
Proof.
  intros.
  inversion H. unfold is_bst in Inv_bst0.
  unpack. inversion H. unfold not. intros.
  unfold searchtree in H6.
  unpack. 
  subst. apply (no_cycles_if_bst p D F V p''' p'' o H H0 H1).
Qed.

Lemma path_step_equal_if_bst : forall p D F V p' p'', 
    Inv p D F V ->
    path F p' p'' ->
    path F p'' p' ->
    p' = p''.
Proof.
  intros. induction H1 ; subst ; auto.
  + pose proof (diffent_pointers_for_path_if_bst p D F V x y x o H H1 H0).
    exfalso. apply H2 ; auto.
  + apply (path_trans F z x y H0) in H1_.
    specialize (IHpath2 H H1_). subst.
    specialize (IHpath1 H H0). subst. auto.
Qed.

Lemma different_nodes_on_bifurcation_if_bst : forall p D F V p' x y z1 z2, 
    Inv p D F V ->
    F p' y RIGHT ->
    F p' x LEFT  ->
    path F x z1 ->
    path F y z2 ->
    not (z1 = z2).
Proof.
  intros. unfold not. intros.
  subst. inversion H. unfold is_bst in Inv_bst0. 
  unfold searchtree in *. unpack.
  assert ( F p' x LEFT /\ path F x z2). split ; auto.
  specialize (H7 p' x z2 H10).
  assert ( F p' y RIGHT /\ path F y z2). split ; auto.
  specialize (H9 p' y z2 H11). unpack ; lia.
Qed.

(* don't need unique root definition! *)
Lemma unique_root_if_bst : forall p D F V, 
    Inv p D F V ->
    exists! r, isroot F r.
Proof.
  intros.
  inversion H. unfold is_bst in Inv_bst0.
  unpack. exists p.
  unfold isroot in *. split ; auto.
  intros.
  specialize (H2 y RIGHT).
  specialize (H5 p RIGHT).
  unpack. apply (path_step_equal_if_bst p D F V y) ; auto.
Qed.  
  

(*
  Two cases:
  
          n 
         / \
        ~   ~            or
       /     \
      x       y


          n 
         / \
        ~   ~
       /     \
      y       x

*)

Lemma two_path_impossible_from_node_x_if_bst : forall p D F V x y z t,
    Inv p D F V ->
    F x y LEFT  ->
    F x z RIGHT ->
    path F y t -> path F z t -> False.
Proof.
  intros.
  inversion H. unfold is_bst in Inv_bst0.
  unfold searchtree in *. unpack.
  specialize (H7 x y t).
  specialize (H9 x z t).
  assert (F x y LEFT ∧ path F y t). split ; auto.
  assert (F x z RIGHT ∧ path F z t). split ; auto.
  apply H7 in H10. apply H9 in H11.
  lia.
Qed.

Lemma two_path_impossible_if_bst_case_1 : forall p D F V x y z o u,
    Inv p D F V ->
    F x z o ->
    F y z u ->
    ~(x = y) ->
    ~(path F x y).
Proof.
  intros.
  unfold not. intro.
  inversion H. unfold is_bst in *.
  unfold searchtree in *. unfold binarytree in *.
  pose proof (path_right_left_step_beginning_if_bst p D F V x y H H3 H2).
  destruct H4. unpack.
  destruct H4, o.
  - pose proof (edge_value_left_if_bst p D F V x z H H0).
    assert (path F x0 z).
    apply path_trans with y ; auto.
    apply path_single with u ; auto.
    assert (F x x0 RIGHT /\ path F x0 z). split ; auto.
    specialize (H11 x x0 z H14). unpack ; lia.
  - pose proof (outgoing_edge_with_same_orientation_have_same_outgoing_node_if_bst p D F V x x0 RIGHT z H H4 H0).
    subst.
    assert (path F y x0).
    apply path_single with u ; auto.
    pose proof (path_step_equal_if_bst p D F V x0 y H H5 H12). subst.
    pose proof (cant_point_to_itself_if_bst p D F V y u H). auto.
  - pose proof (outgoing_edge_with_same_orientation_have_same_outgoing_node_if_bst p D F V x x0 LEFT z H H4 H0).
    subst.
    assert (path F y x0).
    apply path_single with u ; auto.
    pose proof (path_step_equal_if_bst p D F V x0 y H H5 H12). subst.
    pose proof (cant_point_to_itself_if_bst p D F V y u H). auto.
  - pose proof (edge_value_right_if_bst p D F V x z H H0).
    assert (path F x0 z).
    apply path_trans with y ; auto.
    apply path_single with u ; auto.
    assert (F x x0 LEFT /\ path F x0 z). split ; auto.
    specialize (H9 x x0 z H14). unpack ; lia.
Qed.

Lemma no_single_step_triangles_if_bst : forall p D F V x y z o u w,
    Inv p D F V -> 
    F x z o -> 
    F y z u ->
    F x y w ->
    False.
Proof.
  intros.
  inversion H. unfold is_bst in *.
  unfold searchtree in *. unfold binarytree in *. unpack.
  destruct o, u, w.
  + pose proof (outgoing_edge_with_same_orientation_have_same_outgoing_node_if_bst p D F V x z LEFT y H H0 H2).
    subst. apply (cant_point_to_itself_if_bst p D F V z LEFT H H1).
  + apply (edge_value_left_if_bst p D F V) in H0 ; auto.
    assert (F x y RIGHT /\ path F y z). split ; auto.
    apply path_single with LEFT ; auto.
    apply H8 in H9. lia.
  + pose proof (outgoing_edge_with_same_orientation_have_same_outgoing_node_if_bst p D F V x z LEFT y H H0 H2).
    subst. apply (cant_point_to_itself_if_bst p D F V z RIGHT H H1).
  + apply (edge_value_left_if_bst p D F V) in H0 as H0' ; auto.
    assert (F x y RIGHT /\ path F y z). split ; auto.
    apply path_single with RIGHT ; auto.
    apply H8 in H9. lia.
  + apply (edge_value_right_if_bst p D F V) in H0 as H0' ; auto.
    assert (F x y LEFT /\ path F y z). split ; auto.
    apply path_single with LEFT ; auto.
    apply H6 in H9. lia.
  + pose proof (outgoing_edge_with_same_orientation_have_same_outgoing_node_if_bst p D F V x z RIGHT y H H0 H2).
    subst. apply (cant_point_to_itself_if_bst p D F V z LEFT H H1).
  + apply (edge_value_right_if_bst p D F V) in H0 as H0' ; auto.
    assert (F x y LEFT /\ path F y z). split ; auto.
    apply path_single with RIGHT; auto.
    apply H6 in H9. lia.
  + pose proof (outgoing_edge_with_same_orientation_have_same_outgoing_node_if_bst p D F V x z RIGHT y H H0 H2).
    subst. apply (cant_point_to_itself_if_bst p D F V z RIGHT H H1).
Qed.

Lemma two_path_impossible_if_bst_case_2 : forall p D F V x y z o u w k,
    Inv p D F V ->
    F x z o ->
    F y z u ->
    F w x k ->
    ~(x = y) ->
    ~(path F w y).
Proof.
  intros.
  unfold not. intro.
  inversion H. unfold is_bst in *.
  unfold searchtree in *. unfold binarytree in *. unpack.
  pose proof (path_right_left_step_beginning_if_bst p D F V w y H H4).
  destruct (bool_decide (w = y)) eqn:E.
  - apply bool_decide_eq_true in E. subst.
    apply (no_single_step_triangles_if_bst p D F V y x z u o k H H1 H0 H2).
  - apply bool_decide_eq_false in E.
    specialize (H11 E). destruct H11. unpack.
    destruct H11, k.
    * assert (F w x0 RIGHT /\ path F x0 z). split ; auto.
      apply path_trans with y ; auto. apply path_single with u ; auto.
      assert (F w x  LEFT  /\ path F x  z). split ; auto.
      apply path_single with o ; auto.
      apply H8 in H14. apply H10 in H13. lia.
    * pose proof (outgoing_edge_with_same_orientation_have_same_outgoing_node_if_bst p D F V w x RIGHT x0 H H2 H11).
      subst. pose proof (no_single_step_triangles_if_bst p D F V w).
      apply (two_path_impossible_if_bst_case_1 p D F V x y z o u H H0 H1 H3 H12).      
    * pose proof (outgoing_edge_with_same_orientation_have_same_outgoing_node_if_bst p D F V w x LEFT x0 H H2 H11).
      subst. pose proof (no_single_step_triangles_if_bst p D F V w).
      apply (two_path_impossible_if_bst_case_1 p D F V x y z o u H H0 H1 H3 H12).
    * assert (F w x0 LEFT /\ path F x0 z). split ; auto.
      apply path_trans with y ; auto. apply path_single with u ; auto.
      assert (F w x  RIGHT  /\ path F x  z). split ; auto.
      apply path_single with o ; auto.
      apply H8 in H13. apply H10 in H14. lia.    
Qed.

(*
  change name
 *)

Inductive path_ : (elem -> elem -> orientation -> Prop) -> elem -> elem -> (list elem) -> Prop :=
  path_o_refl : forall F x, path_ F x x nil
| path_o_single  : forall (F : elem -> elem -> orientation -> Prop) x y o,
    F x y o ->
    path_ F x y (cons x nil)
| path_o_add : forall (F : elem -> elem -> orientation -> Prop) x y z o l,
    F x y o ->
    path_ F y z l ->
    path_ F x z (cons x l).

Lemma path__implies_path : forall F x y l,
    (path_ F x y l -> path F x y).
Proof.
  intros.
  induction H.
  + apply path_refl.
  + apply path_single with o. auto.
  + apply path_trans with y ; auto.
    apply path_single with o. auto.
Qed.

Lemma path_add_end: forall (F :  (elem -> elem -> orientation -> Prop) ) x y o z l,
   F y z o -> 
   path_ F x y l ->
   path_ F x z (l ++ (cons y nil)).
Proof.
  intros.
  induction H0.
  + simpl. apply path_o_single with o ; auto.
  + simpl. apply path_o_add with y o0 ; auto.
    apply path_o_single with o ; auto.
  + specialize (IHpath_ H).
    apply path_o_add with y o0 ; auto.
Qed.

Lemma path_must_be_equal_if_bst : forall p D F V x y l1 l2,
   Inv p D F V ->
   path_ F x y l1 ->
   path_ F x y l2 ->
   l1 = l2.
Proof.
  intros p D F V x y l1 l2 H H0.
  generalize l2.
  inversion H. unfold is_bst in Inv_bst0. unpack.
  induction H0.
  + intros. inversion H0 ; subst ; auto.
    - pose proof (cant_point_to_itself_if_bst p D F V x o H H6).
      contradiction.
    - apply path__implies_path in H7.
      pose proof (no_cycles_if_bst p D F V x y o H H6 H7).
      contradiction.
  + intros. induction H6 ; subst ; auto.
    - pose proof (cant_point_to_itself_if_bst p D F V x o H H0).
      contradiction.
    - destruct (bool_decide (z = y)) eqn:E.
      * apply bool_decide_eq_true in E. subst.
        pose proof (unique_direction_if_bst p D F V x y o o0 H H6 H0).
        subst.
        inversion H7 ; subst ; auto.
        { pose proof (cant_point_to_itself_if_bst p D F V y o H H8).
          contradiction. }
        { apply path__implies_path in H9.
          pose proof (no_cycles_if_bst p D F V y y0 o H H8 H9).
          contradiction. }
      * apply bool_decide_eq_false in E.
        unfold binarytree in H5.
        specialize (H5 x y z o0 o E H6 H0).
        destruct o, o0 ; try exfalso ; apply H5 ; auto ;
        unfold searchtree in H4 ;unpack ;
        apply path__implies_path in H7.
        { 
          assert (F x y RIGHT /\ path F y z). split ; auto.
          apply H8 in H9. unpack.
          apply (edge_value_left_if_bst p D F V) in H0 ; auto.
          lia.
        }
        {
          assert (F x y LEFT /\ path F y z). split ; auto.
          apply H4 in H9. unpack.
          apply (edge_value_right_if_bst p D F V) in H0 ; auto.
          lia.
        }
  + specialize (IHpath_ H H1 H3 H4 H5).
    intros. destruct l0.
    - inversion H7 ; subst.
      apply path__implies_path in H6.
      pose proof (no_cycles_if_bst p D F V z y o H H0 H6).
      contradiction.
    - inversion H7 ; subst.
      * destruct (bool_decide (y = z)) eqn:E.
        {
          apply bool_decide_eq_true in E. subst.
          pose proof (unique_direction_if_bst p D F V l0 z o o0 H H12 H0).
          subst.
          assert (path_ F z z nil). apply path_o_refl.
          specialize (IHpath_ nil H8). subst. auto.
        }
        {
          apply bool_decide_eq_false in E.
          unfold binarytree in H5.
          specialize (H5 l0 z y o0 o E H12 H0).
          apply path__implies_path in H6.
          unfold searchtree in H4 ; unpack.
          destruct o, o0 ; try (exfalso ; contradiction).
          {
            assert (F l0 y LEFT /\ path F y z). split ; auto.
            apply H4 in H9. unpack.
            apply (edge_value_right_if_bst p D F V) in H12 ; auto.
            lia.
          }
          {
            assert (F l0 y RIGHT /\ path F y z). split ; auto.
            apply H8 in H9. unpack.
            apply (edge_value_left_if_bst p D F V) in H12 ; auto.
            lia.
          }
        }        
      * destruct (bool_decide (y0 = y)) eqn:E.
        {
          apply bool_decide_eq_true in E. subst.
          specialize (IHpath_ l1 H14). subst.
          pose proof (unique_direction_if_bst p D F V l0 y o o0 H H13 H0).
          subst. auto.
        }
        {
          apply bool_decide_eq_false in E.
          unfold binarytree in H5.
          specialize (H5 l0 y y0 o o0 E H0 H13).
          apply path__implies_path in H6.
          apply path__implies_path in H14.
          unfold searchtree in H4 ; unpack.
          destruct o, o0 ; try (exfalso ; contradiction).
          {
            assert (F l0 y LEFT /\ path F y z). split ; auto.
            apply H4 in H9. unpack.
            assert (F l0 y0 RIGHT /\ path F y0 z). split ; auto.
            apply H8 in H11. unpack.
            lia.
          }
          {
            assert (F l0 y RIGHT /\ path F y z). split ; auto.
            apply H8 in H9. unpack.
            assert (F l0 y0 LEFT /\ path F y0 z). split ; auto.
            apply H4 in H11. unpack.
            lia.
          }
        }        
Qed.

Lemma path__implies_only_path : forall p D F V x y l,
    Inv p D F V ->
    path_ F x y l ->
    exists! l', path_ F x y l'.
Proof.
  intros.
  exists l.
  split ; auto.
  intros. apply (path_must_be_equal_if_bst p D F V  x y l y0 H) in H0 ; auto.
Qed.

Lemma path_app : forall F x y z x0 x1,
    path_ F x y x0 ->
    path_ F y z x1 ->
    path_ F x z (x0 ++ x1).
Proof.
  intros.
  induction H ; auto.
  + apply (path_o_add F x y z) with o ; auto.
  + apply IHpath_ in H0. apply (path_o_add F x y z) with o ; auto.
Qed.

Lemma path_exists_one : forall p D F V x y,
    Inv p D F V -> 
    (path F x y -> exists l, path_ F x y l).
Proof.
  intros.
  induction H0.
  + eexists. apply path_o_refl.
  + exists (cons x nil). apply path_o_single with o ; auto.
  + specialize (IHpath1 H).
    specialize (IHpath2 H). destruct IHpath1, IHpath2.
    exists (x0 ++ x1).
    apply path_app with y ; auto.
Qed.

Lemma path_exists_only_one : forall p D F V x y,
    Inv p D F V -> 
    (path F x y -> exists! l, path_ F x y l).
Proof.
  intros.
  apply (path_exists_one p D F V) in H0 as H0' ; auto.
  destruct H0'. exists x0 ; split ; auto.
  intros. pose proof (path_must_be_equal_if_bst p D F V x y x0 y0 H H1 H2).
  auto.
Qed.

(*
          p'
         / \
        ~  ~
        \  /
        x  y
        \ /
         z
*)

Require Coq.Lists.List.

Lemma two_path_impossible_if_bst : forall p D F V p' x y z o u,
    Inv p D F V ->
    path F p' x ->
    path F p' y ->
    ~(x = y) ->
    F x z o -> F y z u ->
    False.
Proof.
  intros.
  apply (path_exists_only_one p D F V p' x) in H0 ; auto.
  apply (path_exists_only_one p D F V p' y) in H1 ; auto.
  destruct H0. destruct H1. destruct H0. destruct H1.
  pose proof (path_add_end F p' y u z x1 H4 H1).
  pose proof (path_add_end F p' x o z x0 H3 H0).
  pose proof (path_exists_only_one p D F V p' z H).
  apply path__implies_path in H8 as H8'.
  specialize (H9 H8'). destruct H9.
  destruct H9. apply H10 in H7. apply H10 in H8. subst.
  apply app_inj_tail in H8. unpack.
  apply H2 in H8. auto.
Qed.

Theorem only_one_parent_if_bst : forall p D F V x y z o u, 
    Inv p D F V ->
    F x z o ->
    F y z u ->
    x = y.
Proof.
  intros.
  inversion H. unfold is_bst in Inv_bst0.
  unfold searchtree in *. unpack.
  destruct (bool_decide (x = y)) eqn:E.
  + apply bool_decide_eq_true in E ; auto.
  + apply bool_decide_eq_false in E.
    exfalso. unfold isroot in *.
    apply (two_path_impossible_if_bst p D F V p x y z o u H) ; auto.
    specialize (H4 x o). destruct H4 ; auto.
    specialize (H4 y o). destruct H4 ; auto.
Qed.

Context `{!tctrHeapG Σ} (nmax : nat).
Definition mapsto_M (M : gmap elem content) : iProp Σ :=
  ([∗ map] l ↦ c ∈ M, from_option (mapsto l 1) False (val_of_content c))%I.

Lemma mapsto_M_acc : forall M x c,
  M !! x = Some c ->
  mapsto_M M -∗
    ∃ v, ⌜val_of_content c = Some v⌝ ∗ x ↦ v ∗
     (∀ c' v', ⌜val_of_content c' = Some v'⌝ -∗
               x ↦ v' -∗ mapsto_M (<[x:=c']>M)).
Proof.
  introv HM. iIntros "HM".
  rewrite -[in mapsto_M _](insert_id _ _ _ HM) -insert_delete /mapsto_M.
  rewrite big_sepM_insert ?lookup_delete //. iDestruct "HM" as "[Hc HM]".
  destruct (val_of_content c); [|done]. iExists _. iFrame. iSplit; [done|].
  iIntros (c' v' Hv') "?".
  rewrite -insert_delete big_sepM_insert ?lookup_delete // Hv'. iFrame.
Qed.

Lemma mapsto_M_acc_same : forall M x c,
  M !! x = Some c ->
  mapsto_M M -∗
    ∃ v, ⌜val_of_content c = Some v⌝ ∗ x ↦ v ∗ (x ↦ v -∗ mapsto_M M).
Proof.
  introv HM. iIntros "HM".
  iDestruct (mapsto_M_acc with "HM") as (v Hv) "[Hv HM]"; [done|].
  iExists _. iFrame. iSplit; [done|].
  iSpecialize ("HM" $! _ _ Hv). Check insert_id. by rewrite insert_id.
Qed.

Definition remove_edge (F : elem -> elem -> orientation -> Prop) x y :=
  fun x' y' o' =>
    ((x' ≠ x) \/ (y' ≠ y)) /\ F x' y' o'.

Lemma remove_edge_specification : forall (F : elem -> elem -> orientation -> Prop) x y o,
    ~ ((remove_edge F x y) x y o).
Proof.
  intros. unfold not ; intro.
  unfold remove_edge in H.
  unpack. destruct H ; auto.
Qed.

Definition add_edge (F : elem -> elem -> orientation -> Prop) x y o :=
  fun x' y' o' =>
    F x' y' o' \/ (x' = x /\ y' = y /\ o' = o).

Lemma add_edge_specification : forall (F : elem -> elem -> orientation -> Prop) x y o,
    (add_edge F x y o) x y o.
Proof.
  intros. unfold add_edge. right.
  repeat split ; auto.
Qed.

(*
    F
   / \
 /\

     x
      \    elimina
       y

   x
    \      elimina
     y''

   liga 
 
    x
     \o''
      y''


 *)

Definition update_edge (F : elem -> elem -> orientation -> Prop) x y y'' o'':=
  fun x' y' o' => 
    (((x' ≠ x) \/ (y' ≠ y)) /\
     ((x' ≠ x) \/ (y' ≠ y'')) /\ F x' y' o') \/
    (((x' = x) /\ (y' = y'') /\ (o' = o''))).

Lemma update_edge_specification :
  forall (F : elem -> elem -> orientation -> Prop) x y y'' o'',
    (add_edge (remove_edge (remove_edge F x y) x y'') x y'' o'') =
    (update_edge F x y y'' o'') .
Proof.
  intros. do 3 (apply functional_extensionality ; intro).
  unfold add_edge in *.
  unfold remove_edge in *.
  unfold update_edge in *. auto.
Admitted.

(*

  p
   \
    x

   x
  /
 p

 *)

Lemma add_edge_does_not_remove_path : forall F x y a b o,
    path F x y ->
    let F' := add_edge F a b o in
    path F' x y.
Proof.
  unfold add_edge.
  intros.
  induction H.
  + apply path_refl.
  + apply path_single with o0. auto.
  + apply path_trans with y ; auto.
Qed.

Lemma add_edge_path_if_bst : forall F x y o p' p'', 
    path F p' x  ->
    path F y p'' ->
    let F' := add_edge F x y o in
    path F' p' p''.
Proof.
  unfold add_edge in *.
  intros.
  apply path_trans with x.
  - pose proof (add_edge_does_not_remove_path F p' x x y o H) ; auto.
  - apply path_trans with y.
    * apply path_single with o. auto.
    * pose proof (add_edge_does_not_remove_path F y p'' x y o H0) ; auto. 
Qed.

Lemma update_edge_path_if_bst : forall F x y o p p', 
    path F p p' ->
    let F' := update_edge F x y o RIGHT in
    path F' p p'.
Proof.
Admitted.

Lemma three_option_path_x_y : forall F x y, 
  (x = y \/ (exists t, F x t RIGHT /\ path F t y) \/ (exists t, F x t LEFT /\ path F t y)) <->
  path F x y.
Proof.
  intros. split ; intros.
  + destruct H ; subst ; auto using path_refl.
    do 2 destruct H ; unpack.
    - apply path_trans with x0 ; auto. apply path_single with RIGHT ; auto.
    - apply path_trans with x0 ; auto. apply path_single with LEFT ; auto.
  + induction H.
    - left ; auto.
    - right. destruct o.
      * right. exists y. split ; auto using path_refl.
      * left. exists y. split ; auto using path_refl.
    - destruct IHpath1, IHpath2 ; subst ; auto.
      do 2destruct H1, H2 ; unpack.
      * right. left. exists x0. split ; auto.
        apply path_trans with y ; auto.
      * right. left. exists x0. split ; auto.
        apply path_trans with y ; auto.
      * right. right. exists x0. split ; auto.
        apply path_trans with y ; auto.
      * right. right. exists x0. split ; auto.
        apply path_trans with y ; auto.
Qed.

Search "Exist".

Lemma remove_invariance_if_bst : forall p D F V x y a b o l,
    Inv p D F V -> 
    path_ F x y l ->
    F a b o ->
    LibList.Exists (fun c => c = a) l ->
    path_ (remove_edge F a b) x y l.
Proof.   
Admitted.
  
Lemma rotate_right_isroot_if_bst : forall p D F V x z, 
    Inv p D F V ->
    F p x RIGHT ->
    F x z LEFT  ->
    let F' := (update_edge F p x z RIGHT) in
    let F'' := (update_edge F' x z p LEFT) in
    isroot F'' x.
Proof.
  split.
  + unfold not ; intros. destruct H2 ; unpack ; subst.
    - destruct H4 ; unpack ; subst.
      * destruct H4 ; auto. apply H4.
        pose proof (only_one_parent_if_bst p D F V x0 p x o RIGHT H H6 H0).
        auto.
      * pose proof (cant_point_to_itself_if_bst p D F V z LEFT H H1).
        auto.
    - pose proof (cant_point_to_itself_if_bst p D F V p RIGHT H H0).
      auto.
   + inversion H. unfold is_bst in Inv_bst0.
     unpack. specialize (H4 x0 o) as H4'.
     unpack. apply three_option_path_x_y in H8.
     repeat destruct H8 ; subst ; auto.
     - admit.
     - admit.
     - apply path_trans with p.
       * apply path_single with LEFT. unfold update_edge. right. auto.
       * 
       
Lemma rotate_right_if_bst : forall p D F V x z, 
    Inv p D F V ->
    F p x RIGHT ->
    F x z LEFT  ->
    let F' := (update_edge F p x z RIGHT) in
    let F'' := (update_edge F' x z p LEFT) in
    Inv x D F'' V.
Proof using. 
  unfold update_edge in *. intros.
  inversion H ; unfold is_bst in * ; unpack.
  constructor.
  unfold is_bst.
  repeat split.
  (*CONFINED*)
  + destruct H7 ; unpack ; subst.
    - destruct H9 ; unpack ; subst.
      * apply H2 in H11. destruct H11 ; auto.
      * apply H2 in H0. destruct H0 ; auto.
    - apply H2 in H1. destruct H1 ; auto.
  + destruct H7 ; unpack ; subst.
    - destruct H9 ; unpack ; subst.
      * apply H2 in H11. destruct H11 ; auto.
      * apply H2 in H1. destruct H1 ; auto.
    - apply H2 in H1. destruct H1 ; auto.
  (*ROOTISINDOMAIN*)
  + unfold rootisindomain. apply H2 in H0. destruct H0 ; auto.
  (*ISROOT*)
  (*No edge is connected with root*)
  + unfold not ; intros. destruct H7 ; unpack ; subst.
    - destruct H9 ; unpack ; subst.
      * destruct H9 ; auto. apply H9.
        pose proof (only_one_parent_if_bst p D F V x0 p x o RIGHT H H11 H0).
        auto.
      * pose proof (cant_point_to_itself_if_bst p D F V z LEFT H H1).
        auto.
    - pose proof (cant_point_to_itself_if_bst p D F V p RIGHT H H0).
      auto.
  (*Exists a path from root to all nodes*)
  + 
        
        
Lemma F_update_specification1 : forall (F : elem → elem → orientation → Prop) x y o y' o',
    F x y o ->
    (update_edge F x y y' o') x y' o'.
Proof.
  intros.
  unfold update_edge. right.
  split ; try split ; auto.
Qed.

Lemma F_update_specification2 : forall (F : elem → elem → orientation → Prop) x y o y' o',
    y ≠ y'  ->
    F x y o ->
    ~(update_edge F x y y' o') x y o.
Proof.
  intros.
  unfold update_edge. unfold not.
  intros. destruct H1 ; try destruct H1.
  - destruct H1. apply H1 ; auto.
    destruct H1. auto.
  - destruct H2. subst. apply H. auto.
Qed.

Lemma F_lookup_on_update_eq : forall (F : elem → elem → orientation → Prop) p l0 l1 o,
    (update_edge F p l0 l1 o) p l1 o.
Proof.    
  intros.
  unfold update_edge.
  auto.
Qed.

Lemma F_lookup_orientation_equal :  forall F p l0 l1 k o,
    (update_edge F p l0 l1 k) p l1 o ->
    o = k.
Proof.
  intros.
  unfold update_edge in H.
  destruct H.
  + unpack. destruct H0 ; exfalso ; apply H0 ; auto.
  + unpack ; auto.    
Qed.

Lemma F_lookup_update_neq :  forall F x y y' o' x'' y'' o'',
    (x ≠ x'') \/ (y ≠ y'' /\ y' ≠ y'') ->
    ((update_edge F x y y' o') x'' y'' o'' <-> F x'' y'' o'').
Proof.
  intros. split ; intro H0 ; unpack.
  - unfold update_edge in H0.
    destruct H0 ; unpack ; subst ; auto.
    exfalso. destruct H ; apply H ; reflexivity.
  - unfold update_edge. left.
    repeat split ; auto. destruct H ; unpack.
    * left ; auto.
    * right ; auto.
    * destruct H. left. auto.
      unpack. right. auto.
Qed.
    
Definition ST R D V : iProp Σ :=
  (∃ F M,
  ⌜ Inv R D F V ⌝ ∗
  ⌜ Mem D F V M ⌝ ∗
  mapsto_M M ).
(*time credit + time receipt*)


Check ST.


End SplayTreePredicate.

