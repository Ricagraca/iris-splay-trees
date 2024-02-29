From ST Require Import STorientation STpredicate STdomain STlink.
From iris_time.heap_lang Require Import proofmode.
From TLC Require Import LibTactics LibInt.
Require Import Coq.Lists.List.
Import ListNotations.

Section PathWithMemory.

  Notation elem := loc.
  Notation EdgeSet := (elem -> elem -> orientation -> Prop).
  
  Inductive path_memory : EdgeSet -> elem -> elem -> (list elem) -> Prop :=
    path_m_refl : forall F x,
      path_memory F x x []
  | path_m_single  : forall (F : EdgeSet) x y o,
      F x y o ->
      path_memory F x y [x]
  | path_m_add : forall (F : EdgeSet) x y z o l,
      F x y o ->
      path_memory F y z l ->
      path_memory F x z (x::l).

  Lemma path_app : forall F x y z x0 x1,
      path_memory F x y x0 ->
      path_memory F y z x1 ->
      path_memory F x z (x0 ++ x1).
  Proof.
    intros.
    induction H ; auto.
    + apply (path_m_add F x y z) with o ; auto.
    + apply IHpath_memory in H0. apply (path_m_add F x y z) with o ; auto.
  Qed.
  
  Lemma path_memory_implies_path : forall F x y l,
    (path_memory F x y l -> path F x y).
  Proof.
    intros.
    induction H.
    + apply path_refl.
    + apply path_single with o. auto.
    + apply path_trans with y ; auto.
      apply path_single with o. auto.
  Qed.

  Lemma path_memory_add_end: forall (F : EdgeSet ) x y o z l,
      F y z o -> 
      path_memory F x y l ->
      path_memory F x z (l ++ [y]).
  Proof.
    intros.
    induction H0.
    + simpl. apply path_m_single with o ; auto.
    + simpl. apply path_m_add with y o0 ; auto.
      apply path_m_single with o ; auto.
    + specialize (IHpath_memory H).
      apply path_m_add with y o0 ; auto.
  Qed.

  Lemma path_exists_one : forall F x y,
      (path F x y -> exists l, path_memory F x y l).
  Proof.
    intros.
    induction H.
    + eexists. apply path_m_refl.
    + exists [x]. apply path_m_single with o ; auto.
    + destruct IHpath1, IHpath2. exists (x0 ++ x1).
      apply path_app with y ; auto.
  Qed.

  Lemma path_add_end : forall (F : EdgeSet ) x y o z,
      F y z o -> 
      path F x y ->
      path F x z.
  Proof.
    intros. apply path_exists_one in H0. destruct H0.
    apply path_memory_implies_path with (x0 ++ [y]).
    apply path_memory_add_end with o ; auto.
  Qed.
  
  Lemma path_memory_to_sub_path : forall F x y e l,
      path_memory F x y l ->
      In e l ->
      exists l', path_memory F x e l'.
  Proof.
    intros F x y e l H.
    induction H ; intros.
    + inversion H.
    + inversion H0 ; subst.
      - eexists []. apply path_m_refl.
      - inversion H1.
    + inversion H1 ; subst.
      - eexists []. apply path_m_refl.
      - apply IHpath_memory in H2.
        destruct H2. exists ([x] ++ x0).
        apply path_app with y ; auto.
        apply path_m_single with o ; auto.
  Qed.
  
  Lemma exists_node_that_points_to_the_beginning_of_path : forall F x y l,
      path_memory F x y l ->
      (Exists (fun e => exists u, F e x u) l) ->
      exists l', ¬(l' = []) /\ path_memory F x x l'.
  Proof.
    intros F x y l E Q.
    apply Exists_exists in Q.
    destruct Q. unpack.
    apply (path_memory_to_sub_path F x y x0 l) in E ; auto.
    destruct E. exists (x1 ++ [x0]). split.
    intro O. apply app_eq_nil in O. unpack ; discriminate.
    apply path_app with x0 ; auto.
    apply path_m_single with u ; auto.
  Qed.
  
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
      do 2destruct H1, H2 ; unpack ;
      do 2 (right + left) ; exists x0 ; split ; auto ;
        apply path_trans with y ; auto.
  Qed.

  
  Lemma if_no_edge_then_path_to_itself : forall F x z0,
      path F x z0 ->
      ¬(exists y o, F x y o) ->
      x = z0.
  Proof.
    intros.
    apply path_implies_path_add_memory in H.
    destruct H.
    assert (exists x1, rev x1 = x0).
    exists (rev x0). rewrite rev_involutive ; auto.
    destruct H1. rewrite <- H1 in H. clear dependent x0.
    generalize dependent z0.
    induction x1 ; intros.
    + inversion H ; subst ; auto.
      apply app_eq_nil in H1 ; unpack ; discriminate.
    + inversion H ; subst ; auto.
      - exfalso. apply H0. exists z0 o ; auto.
      - apply app_inj_tail in H1. unpack ; subst.
        apply IHx1 in H6. subst. exfalso.
        apply H0. exists z0, o ; auto.
  Qed.

  Lemma path_memory_end : forall (F : EdgeSet) x y z o l,
      F y z o ->
      path_memory F x y l ->
      path_memory F x z (l ++ [y]).
  Proof.
    intros.
    generalize dependent x. 
    generalize dependent y. 
    induction l ; intros.
    + inversion H0 ; subst. simpl.
      apply path_m_single with o ; auto.
    + inversion H0 ; subst.
      - pose proof (path_m_add F a y z o0 [y] H5).
        apply H1. apply path_m_single with o ; auto.
      - specialize (IHl y H y0 H7).
        pose proof (path_m_add F a y0 z o0 (l ++ [y])).
        apply H1 ; auto.
  Qed.
              
  Lemma path_memory_equiv_path_add_memory : forall F x y l,
      path_memory F x y l <-> path_add_memory F x y l.
  Proof.
    intros.
    split ; intro.
    + induction H.
      - apply path_am_refl.
      - apply path_am_single with o ; auto.
      - pose proof (path_add_memory_begin F x y z o l H IHpath_memory).
        auto.
    + induction H.
      - apply path_m_refl.
      - apply path_m_single with o ; auto.
      - pose proof ( path_memory_end F x y z o l).
        apply H1 ; auto.
  Qed.
        
End PathWithMemory.

From TLC Require Import LibSet.

Section PathSplayTree.

  Notation elem := loc.
  
  (* Graph structure *)
  Variable p : elem.
  Variable D : LibSet.set elem.   (* domain *)
  Variable V : elem -> Z.       (* data stored in nodes *)
  Variable W : elem -> Z. (* weight nodes *)
  Variable M : gmap elem content. (* view of the memory *)
  
  Lemma path_value_left_if_bst : forall F x y z,
      Inv p D F V W ->    
      (F x y LEFT -> path F y z -> (V x > V z)%Z). 
  Proof.
    intros F x y z Inv H1 H2.
    inversion Inv. unfold is_bst in *.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    assert (F x y LEFT /\ path F y z). split ; auto using path_refl.
    apply searchleft in H. destruct H. lia.
  Qed.

  Lemma path_value_right_if_bst : forall F x y z,
      Inv p D F V W ->    
      (F x y RIGHT -> path F y z -> (V x < V z)%Z). 
  Proof.
    intros F x y z Inv H1 H2.
    inversion Inv. unfold is_bst in *.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    assert (F x y RIGHT /\ path F y z). split ; auto using path_refl.
    apply searchright in H. destruct H. lia.
  Qed.

  Lemma path_to_root_then_root_if_bst : forall F x,
      Inv p D F V W ->    
      path F x p -> x = p.
  Proof.
    intros F x Inv H.
    apply path_add_equiv_path in H.
    inversion Inv. unfold is_bst in *.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].    
    inversion H as [| a b c o E | ] ; subst ; auto.
    + assert (x \in D) as xindomain. stdomain_tac.
      apply (isroot x o) in xindomain.
      destruct xindomain as [NE Ppx].
      contradiction.
    + assert (y \in D) as xindomain. stdomain_tac.
      apply (isroot y o) in xindomain.
      destruct xindomain as [NE Ppx].
      contradiction.
  Qed.

  Lemma path_right_left_step_beginning_if_bst : forall F x y,
    path F x y ->
    ~(x = y) ->
    exists t, (F x t RIGHT \/ F x t LEFT) /\ path F t y.
  Proof.
    intros F x y H H0.
    induction H ; intros.
    + exfalso. contradiction.
    + exists y. split ; auto using path_refl. destruct o ; auto.
    + destruct (bool_decide (x = y)) eqn:XY ;
        [apply bool_decide_eq_true in XY; subst|apply bool_decide_eq_false in XY].
    - specialize (IHpath2 H0).
      destruct IHpath2. 
      exists x. auto.
    - specialize (IHpath1 XY).
      destruct IHpath1. 
      exists x0. unpack. split ; auto. 
      apply path_trans with y ; auto.     
  Qed.

  Lemma path_right_left_step_end_if_bst : forall F x y, 
      path F x y ->
      ~(x = y) ->
      exists t, (F t y RIGHT \/ F t y LEFT) /\ path F x t.
  Proof.    
    intros F x y H H0.
    induction H ; intros.
    + exfalso. contradiction.
    + exists x. split ; auto using path_refl. destruct o ; auto.
    + destruct (bool_decide (x = y)) eqn:XY ;
        [apply bool_decide_eq_true in XY; subst|apply bool_decide_eq_false in XY].
    - specialize (IHpath2 H0).
      destruct IHpath2. 
      exists x. auto.
    - destruct (bool_decide (y = z)) eqn:YZ ;
        [apply bool_decide_eq_true in YZ; subst; auto|apply bool_decide_eq_false in YZ].
      specialize (IHpath2 YZ).
      specialize (IHpath1 XY ).
      destruct IHpath2 ; auto.
      exists x0. unpack. split ; subst ; auto.
      apply path_trans with y ; auto.     
  Qed.

  Lemma path_value_if_bst : forall F x y, 
      Inv p D F V W ->
      path F x y ->
      ~(x = y) -> 
      (V x < V y)%Z \/ (V y < V x)%Z.
  Proof.
    intros F x y Inv Pxy XY.
    inversion Inv. unfold is_bst in *.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]]. 
    pose proof (path_right_left_step_beginning_if_bst F x y Pxy XY) as prlsb.
    destruct prlsb as [t [ED Pty]]. destruct ED.
    - assert (F x t RIGHT /\ path F t y) as FPxyr. split ; auto. 
      specialize (searchright x t y FPxyr). lia.  
    - assert (F x t LEFT /\ path F t y) as FPxyl. split ; auto. 
      specialize (searchleft x t y FPxyl). lia.
  Qed.

  Lemma no_cycles_if_bst : forall F x y o,
      Inv p D F V W ->
      F x y o ->
      ¬(path F y x).
  Proof.
    intros F x y o Inv E H.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]]. 
    destruct o.
    + assert (F x y LEFT ∧ path F y x) as FPxxl. split ; auto.
      apply searchleft in FPxxl. lia.
    + assert (F x y RIGHT ∧ path F y x) as FPxxr. split ; auto.
      apply searchright in FPxxr. lia.
  Qed.

  Lemma different_pointers_for_path_if_bst : forall F x y z o,
      Inv p D F V W ->
      F x y o ->
      path F y z -> ¬(x = z). 
  Proof.
    intros F x y z o Inv E H.
    inversion Inv. unfold is_bst in Inv_bst.
    intro XZ. subst z.
    apply (no_cycles_if_bst F x y o Inv) ; auto.
  Qed.
  
  Lemma path_step_equal_if_bst : forall F x y,
      Inv p D F V W ->
      path F x y ->
      path F y x ->
      x = y.
  Proof.  
    intros F x y Inv P1 P2. induction P1 ; subst ; auto.
    + pose proof (different_pointers_for_path_if_bst) as dpfp.
      specialize (dpfp F x y x o Inv H P2).
      contradiction.
    + pose proof (IHP1_1 Inv (path_trans F y z x P1_2 P2)).
      pose proof (IHP1_2 Inv (path_trans F z x y P2 P1_1)). 
      subst. reflexivity.
  Qed.

  Lemma different_nodes_on_bifurcation_if_bst : forall F p' x y z1 z2, 
      Inv p D F V W ->
      F p' y RIGHT ->
      F p' x LEFT  ->
      path F x z1 ->
      path F y z2 ->
      ¬(z1 = z2).
  Proof.
    intros F p' x y z1 z2 Inv. unfold not. intros.
    subst. inversion Inv. unfold is_bst in Inv_bst. 
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]]. 
    assert ( F p' x LEFT /\ path F x z2) as Fp'xl. split ; auto.
    assert ( F p' y RIGHT /\ path F y z2) as Fp'yr. split ; auto.
    apply searchleft in Fp'xl.
    apply searchright in Fp'yr.
    lia.
  Qed.

  (*
 
        Only one root r:

         r
        /\

   *)
  
  Lemma unique_root_if_bst : forall F, 
      Inv p D F V W ->
      exists! r, isroot D F r.
  Proof.
    intros F Inv.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    exists p.
    split ; auto. intros x' x'isroot.
    specialize (x'isroot p RIGHT rootisindomain) as [NFpx'r Px'p].
    pose proof (path_to_root_then_root_if_bst F x' Inv Px'p).
    subst ; auto.
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

  Lemma two_path_impossible_from_node_x_if_bst : forall F x y z t,
      Inv p D F V W ->
      F x y LEFT  ->
      F x z RIGHT ->
      path F y t -> path F z t -> False.
  Proof.
    intros F x y z t Inv **.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    assert (F x y LEFT ∧ path F y t) as FPxtl. split ; auto.
    assert (F x z RIGHT ∧ path F z t) as FPxtr. split ; auto.
    apply searchleft in FPxtl.
    apply searchright in FPxtr.    
    lia.
  Qed.

  (*

        x -~-> x then l = [] , i.e.:
 
        To reach x from x, we don't need to 
        got trough any other node!
 
  *)
  
  Lemma path_refl_implies_unique : forall F x l,
      Inv p D F V W ->
      path_memory F x x l ->
      [] = l.
  Proof.
    intros F x l Inv H.
    inversion H ; auto ; subst.
    + exfalso. stlink_tac. 
    + pose proof (path_memory_implies_path F y x l0 H1).
      pose proof (no_cycles_if_bst F x y o Inv H0 H2).
      contradiction.
  Qed.

  (*
    
        In a binary search tree, 
        if x -> y and x -> z, then it can only
        exist one path from y to z, if y = z.

                      x
                     /  \
                    /    \     -->  y = z
                   /      \ 
                  /        \
                 y   -~->   z
                   
       
   *)

  Lemma path_memory_only_if_child_equal : forall F x y z o u l,
      Inv p D F V W ->
      F x y o ->
      F x z u ->
      path_memory F y z l ->
      y = z.
  Proof.
    intros F x y z o u l Inv H1 H2 H.
    inversion Inv. unfold is_bst in Inv_bst. 
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    destruct (bool_decide (z = y)) eqn:YZ ;
      [apply bool_decide_eq_true in YZ;subst|apply bool_decide_eq_false in YZ] ; auto.
    specialize (binarytree x y z o u YZ H1 H2).
    destruct u, o ; try contradiction.
    + apply (edge_value_left_if_bst p D V W F) in H2 as HvalLeft ; auto.
      apply path_memory_implies_path in H.
      pose proof ( path_value_right_if_bst F x y z Inv H1 H). lia.
    + apply (edge_value_right_if_bst p D V W F) in H2 as HvalLeft ; auto.
      apply path_memory_implies_path in H.
      pose proof (path_value_left_if_bst F x y z Inv H1 H). lia.
  Qed.
  
  Lemma path_only_if_child_equal : forall F x y z o u,
      Inv p D F V W ->
      F x y o ->
      F x z u ->
      path F y z ->
      y = z.
  Proof.
    intros F x y z o u Inv H1 H2 H.
    apply path_exists_one in H.
    destruct H.
    pose proof (path_memory_only_if_child_equal F x y z o u x0).
    apply H0 ; auto.
  Qed.

  (*

        If bst then, for every edge (x,y)
        there exists a unique path from 
        x to y and the path consists of:
        
                    x -> y
       
   *)
      
  Lemma path_single_implies_unique : forall F x y o l,
      Inv p D F V W ->
      F x y o -> 
      path_memory F x y l → [x] = l.
  Proof.
    intros F x y o l Inv E H **.
    induction H ; auto.
    + exfalso ; stlink_tac.
    + pose proof (path_memory_only_if_child_equal F x y z o0 o l Inv H E H0).
      subst. apply path_refl_implies_unique in H0 ; subst ; auto.
  Qed.

  Lemma path_add_implies_unique : forall F x y z o l l',
      Inv p D F V W -> 
      F x y o ->
      path_memory F y z l ->
      (∀ l2 : list elem, path_memory F y z l2 → l = l2) ->
      path_memory F x z l' ->
      x :: l = l'.
  Proof.
    intros F x y z o l l' Inv E PM1 IH PM2.
    pose proof (path_m_add F x y z o l E PM1).
    inversion Inv.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    inversion PM2 ; subst ; auto.
    + apply path_refl_implies_unique in H ; auto.
    + destruct (bool_decide (y = z)) eqn:YZ ;
        [apply bool_decide_eq_true in YZ ; subst|apply bool_decide_eq_false in YZ].
      - apply path_refl_implies_unique in PM1 ; subst ; auto.
      - specialize (binarytree x z y o0 o YZ H0 E).
        pose proof (path_memory_only_if_child_equal F x y z o o0 l Inv E H0 PM1).
        subst. contradiction. 
    + destruct (bool_decide (y = y0)) eqn:YY0 ;
      [apply bool_decide_eq_true in  YY0 ; subst ; apply IH in H1 ; subst ; auto
      |apply bool_decide_eq_false in YY0].
      specialize (binarytree x y0 y o0 o YY0 H0 E).
      destruct o, o0 ; try contradiction.
      - pose proof (different_nodes_on_bifurcation_if_bst F x y y0 z z Inv H0 E).
        apply path_memory_implies_path in PM1.
        apply path_memory_implies_path in H1.
        specialize (H2 PM1 H1). contradiction.
      - pose proof (different_nodes_on_bifurcation_if_bst F x y0 y z z Inv E H0).
        apply path_memory_implies_path in H1.
        apply path_memory_implies_path in PM1.
        specialize (H2 H1 PM1). contradiction.
  Qed.
      
  Lemma path_must_be_equal_if_bst : forall F x y l1 l2,
      Inv p D F V W ->
      path_memory F x y l1 ->
      path_memory F x y l2 ->
      l1 = l2.
  Proof.
    intros F x y l1 l2 Inv H.
    generalize l2.
    induction H.
    + intros l. apply (path_refl_implies_unique) ; auto. 
    + intros l H1. pose proof (path_single_implies_unique F x y o l Inv H H1).
      auto.
    + intros l' H1. apply (path_add_implies_unique F x y z o l l' ) ; auto.
  Qed.

  Lemma path_memory_implies_only_one_path : forall F x y l,
    Inv p D F V W ->
    path_memory F x y l ->
    exists! l', path_memory F x y l'.
  Proof.
    intros.
    exists l.
    split ; auto.
    intros. apply (path_must_be_equal_if_bst F x y l x' H) in H0 ; auto.
  Qed.

  Lemma path_exists_only_one : forall F x y,
    Inv p D F V W -> 
    (path F x y -> exists! l, path_memory F x y l).
  Proof.
    intros.
    apply (path_exists_one F) in H0 as H0' ; auto.
    destruct H0'. exists x0 ; split ; auto.
    intros. pose proof (path_must_be_equal_if_bst F x y x0 x' H H1 H2).
    auto.
  Qed.

  (*

        If we have two paths from p' to x and y, 
        if x and y are different they can't point
        to the same node:

                    p'
                  /   \
                 ~    ~
                 |    |     -> False
                 \   /
                 x  y
                 \ /       
                  z
       
   *)

  Lemma two_path_impossible_if_bst : forall F p' x y z o u,
    Inv p D F V W ->
    path F p' x ->
    path F p' y ->
    ~(x = y) ->
    F x z o -> F y z u ->
    False.
  Proof.
    intros.
    apply (path_exists_only_one F p' x) in H0 ; auto.
    apply (path_exists_only_one F p' y) in H1 ; auto.
    destruct H0. destruct H1. destruct H0. destruct H1.
    pose proof (path_memory_add_end F p' y u z x1 H4 H1).
    pose proof (path_memory_add_end F p' x o z x0 H3 H0).
    pose proof (path_exists_only_one F p' z H).
    apply path_memory_implies_path in H8 as H8'.
    specialize (H9 H8'). destruct H9.
    destruct H9. apply H10 in H7. apply H10 in H8. subst.
    apply app_inj_tail in H8. unpack. subst.
    contradiction.
  Qed.


  (*

        ~(path F x y)

              p
             / \
            x   y
           / \          
          a  e
        c/\   \
        b      

        If:

        path_memory F x z l
 
              p
             / \
            x   y
           / \          
          a  e
        c/\   \
        b z    
       
        Then: 

        y can't be in l

   *)

  Lemma if_no_path_then_not_in_memory_if_bst : forall F x y z l,
      Inv p D F V W ->
      ~(path F x y) ->
      path_memory F x z l ->
      (Forall (fun e => ¬(e = y)) l).
  Proof.
    intros. induction H1.
    + auto.
    + apply Forall_cons ; auto.
      intro ; subst. apply H0 ; apply path_refl.
    + apply Forall_cons.
      * intro ; subst. apply H0 ; apply path_refl.
      * apply IHpath_memory ; auto ; intro.
        apply path_single in H1.
        apply (path_trans F x y0 y) in H1 ; auto.
  Qed.

  Lemma if_list_ends_with_y_then_edge_from_y_to_z : forall F x y z l,
      Inv p D F V W -> 
      path_memory F x z (l ++ [y]) ->
      exists o, path_memory F x y l /\ F y z o.
  Proof.
    intros F x y z l.
    generalize x y z.
    induction l ; simpl in * ; intros.
    + inversion H0 ; subst ; auto.
      - exists o ; auto using path_m_refl.
      - inversion H7 ; subst. exists o ; auto using path_m_refl.
    + inversion H0 ; subst.
      - symmetry in H6. apply app_eq_nil in H6.
        unpack ; discriminate.
      - specialize (IHl y1 y0 z0 H). apply IHl in H7.
        destruct H7. exists x0 ; unpack ; split ; auto.
        apply path_m_add with y1 o ; auto.
  Qed.
    
  Lemma if_edge_does_not_exist_then_not_in_path_if_bst : forall F x y z l,
      Inv p D F V W ->
      ¬ (exists u, F x y u) ->
      path_memory F z y l ->
      ¬ (exists l', l = l' ++ [x]).
  Proof.
    intros F x y z l Inv NE H.
    intro NEl ; destruct NEl ; subst.
    inversion H ; subst ; auto.
    + symmetry in H4. apply app_eq_nil in H4.
      unpack ; discriminate.
    + symmetry in H0. apply app_eq_unit in H0.
      destruct H0 ; unpack ; subst. injection H1 as Hxz ; subst.
      apply NE. exists o ; auto.
      inversion H1.
    + pose proof (if_list_ends_with_y_then_edge_from_y_to_z F z x y x0 Inv H).
      destruct H2. unpack. apply NE. exists x1 ; auto.
  Qed.

  (*

              p
             / \
         -->x   k
        /  / \          
       ^--e  a
        c/\   \
        b y    
       
       If some node e is in path F x y 
       then there is no path from e to 
       x, otherwise there would be a 
       cycle and consequently, it 
       wouldnt be a binary search tree

   *)
  
  Lemma no_node_in_path_points_to_its_parent_if_bst : forall F x y l,
      Inv p D F V W ->
      path_memory F x y l ->
      ¬(Exists (fun e => exists u, F e x u) l).
  Proof.
    intros F x y l Inv H Q.
    pose proof exists_node_that_points_to_the_beginning_of_path as Hproof.
    specialize (Hproof F x y l H Q). destruct Hproof.
    unpack. apply path_refl_implies_unique in H1 ; subst ; auto.
  Qed.

  Lemma in_path_then_in_domain_if_bst : forall F x y l, 
    Inv p D F V W -> 
    path_memory F x y l ->
    Forall (fun e => e \in D) l.
  Proof.
    intros F x y l Inv H.
    induction H ; auto.
    + apply Forall_cons ; auto.
      inversion Inv. unfold is_bst in Inv_bst.
      unpack. apply H0 in H ; unpack ; auto.
    + specialize (IHpath_memory Inv).
      apply Forall_cons ; auto.
      inversion Inv. unfold is_bst in Inv_bst.
      unpack. apply H1 in H ; unpack ; auto.
  Qed.

  Lemma in_domain_if_edge_and_path_if_bst : forall F x y o z, 
    Inv p D F V W -> 
    F x y o ->
    path F y z -> 
    x \in D /\ y \in D /\ z \in D.
  Proof.
    intros F x y o z Inv E P.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    apply confined in E as Dxy.
    destruct Dxy as [Dx Dy].
    repeat split ; auto.
    pose proof (in_domain_if_neq_if_bst p D V W F x z Inv).
    assert (path F x z) as Pxz. apply path_trans with y ; auto.
    apply path_single with o ; auto.
    destruct (bool_decide (x = z)) eqn:XZ ;
      [apply bool_decide_eq_true in XZ;subst|apply bool_decide_eq_false in XZ] ;
      auto. apply H ; auto.
  Qed.   
  
  Lemma if_not_in_domain_then_if_path_then_refl_if_bst : forall F x y, 
      Inv p D F V W ->
      ¬(x \in D) \/ ¬(y \in D) ->
      (exists l, path_memory F x y l) -> x = y.
  Proof.
    intros F x y Inv H HE.
    destruct H, HE.
    + inversion Inv. unfold is_bst in Inv_bst.
      inversion H0 ; unpack ; subst ; auto.
      - apply H6 in H1. unpack ; contradiction.
      - apply H7 in H1. unpack ; contradiction.
    + induction H0 ; unpack ; subst ; auto.
      - inversion Inv. unfold is_bst in Inv_bst. unpack.
        apply H1 in H0 ; unpack ; contradiction.
      - specialize (IHpath_memory Inv H). subst.
        inversion Inv. unfold is_bst in Inv_bst.
        unpack. apply H2 in H0. unpack ; contradiction.
  Qed.
  
  Lemma if_not_in_domain_then_not_in_path_if_bst : forall F z, 
      Inv p D F V W ->
      ¬(z \in D) ->
      ¬(exists x y l, path_memory F x y l /\ (Exists (fun e => z = e) l)).
  Proof.
    intros F z Inv H.
    pose proof (if_not_in_domain_then_if_path_then_refl_if_bst).
    intro. do 3destruct H1. unpack.
    induction H1.
    + inversion H2.
    + inversion H2 ; subst ; [|inversion H4].
      inversion Inv. unfold is_bst in * ; unpack.
      apply H3 in H1. unpack ; contradiction.
    + inversion H2 ; subst.
      - inversion Inv. unfold is_bst in * ; unpack.
        apply H4 in H1. unpack ; contradiction.
      - apply IHpath_memory ; auto.
  Qed.

  Lemma iff_not_in_domain_not_path_from_root_if_bst : forall F x, 
      Inv p D F V W ->
      (¬(x \in D) <-> ¬(path F p x)).
  Proof.
    intros F x Inv.
    split ; intro H.
    + intro. apply (path_domain_if_bst p D V W) in H0 ; auto.
    + intro. inversion Inv. unfold is_bst in * ; unpack.
      apply (H3 x RIGHT) in H0 ; auto. unpack ; auto.
  Qed.

  Theorem only_one_parent_if_bst : forall F x y z o u, 
      Inv p D F V W ->
      F x z o ->
      F y z u ->
      x = y.
  Proof.
    intros F x y z o u Inv E1 E2.
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    destruct (bool_decide (x = y)) eqn:E.
    + apply bool_decide_eq_true in E ; auto.
    + apply bool_decide_eq_false in E.
      exfalso. 
      pose proof (confined x z o E1) as [Dx Dz].
      pose proof (confined y z u E2) as [Dy _]. 
      pose proof (isroot x o Dx) as [_ Px].
      pose proof (isroot y o Dy) as [_ Py]. 
      apply (two_path_impossible_if_bst F p x y z o u) ; auto.
  Qed.

  Lemma only_one_parent_left_right_if_bst : forall F x y z, 
      Inv p D F V W ->
      F x z LEFT ->
      F y z RIGHT ->
      False.
  Proof.
    intros F x y z Inv E1 E2.
    pose proof (only_one_parent_if_bst F x y z LEFT RIGHT Inv E1 E2).
    subst. pose proof (unique_direction_if_bst p D V W F y z RIGHT LEFT Inv E1 E2).
    discriminate.
  Qed.

  Lemma edge_from_root_path_or_if_bst : forall F x y o, 
      Inv p D F V W ->
      F p x o ->
      path F y x -> y = x \/ y = p.
  Proof.
    intros F x y o Inv H P.
    induction P ; auto.
    + pose proof (only_one_parent_if_bst F p x y o o0 Inv H H0).
      auto.
    + specialize (IHP2 Inv). destruct IHP2 ; subst ; auto.
      pose proof (path_to_root_then_root_if_bst F x Inv P1).
      auto.
  Qed.

  Lemma bottom_up_path_remove : forall F x y z o, 
    Inv p D F V W -> 
    F x z o ->
    path F y z ->
    (x = y) \/ (z = y) \/ (path F y x).
  Proof.
    intros.
    apply path_add_equiv_path in H1.
    inversion H1 ; subst.
    + right. left. auto.
    + pose proof (only_one_parent_if_bst F x y z o o0 H H0 H2).
      subst. left. auto.
    + right. right.
      pose proof (only_one_parent_if_bst F x y0 z o o0 H H0 H2).
      subst. apply path_add_equiv_path in H3. auto.
  Qed.

  Lemma no_path_from_end_to_root : forall (F : EdgeSet) x x' o, 
    Inv p D F V W -> 
    F x x' o ->
    ¬(path F x' p).
  Proof.
    intros.
    intro.
    apply path_to_root_then_root_if_bst in H1 ; auto.
    subst. stlink_tac.
  Qed.

  Lemma descendants_right_if_bst : forall F x y, 
    Inv p D F V W -> 
    F p x RIGHT ->
    y \in (descendants F x) ->
    (V p < V y)%Z.
  Proof.
    intros F x y Inv H Y.
    rewrite in_set_st_eq in Y.
    pose proof (path_value_right_if_bst F p x y).
    apply H0 ; auto.
  Qed.

  Lemma descendants_left_if_bst : forall F x y, 
    Inv p D F V W -> 
    F p x LEFT ->
    y \in (descendants F x) ->
    (V p > V y)%Z.
  Proof.
    intros F x y Inv H Y.
    rewrite in_set_st_eq in Y.
    pose proof (path_value_left_if_bst F p x y).
    apply H0 ; auto.
  Qed.
  
  Lemma if_in_domain_then_path_from_root_if_bst : forall F x, 
    Inv p D F V W -> 
    x \in D ->
    path F p x.
  Proof.
    intros F x Inv H.
    inversion Inv.
    unfold is_bst in Inv_bst.
    unpack.
    apply (H2 x RIGHT) in H ; unpack ; auto.
  Qed.
  
  Lemma if_path_then_refl_or_in_domain_if_bst : forall F y x, 
    Inv p D F V W -> 
    path F y x ->
    y = x \/ y \in D.
  Proof.
    intros F x y Inv **.
    apply path_implies_path_add in H.
    induction H ; auto.
    + right. stdomain_tac.
    + assert (x = y \/ x \in D).
      apply IHpath_add ; auto. destruct H1 ; auto.
      subst. right. stdomain_tac.
  Qed.
  
  Lemma if_node_not_in_domain_and_edge_then_end_also_not_in_domain_if_bst :
    forall F a x o x',
      Inv p D F V W ->      
      let D' := (descendants F x) in
      ¬(a \in D') ->
      ~(x = x') ->
      F a x' o -> 
      ¬(x' \in D').
  Proof.
    intros.
    rewrite in_set_st_eq.
    rewrite in_set_st_eq in H0.
    intro.
    pose proof (path_right_left_step_end_if_bst F x x' H3 H1).
    do 2destruct H4.
    destruct H4 ; [
      assert ( a = x0 ) ; [pose proof (only_one_parent_if_bst F a x0 x' o RIGHT) ;
                           apply H6 ; auto|]
    | assert ( a = x0 ) ; [pose proof (only_one_parent_if_bst F a x0 x' o LEFT) ;
                           apply H6 ; auto|]
    ] ; subst ; contradiction.
  Qed.
  
  Lemma if_path_from_x_to_y_then_no_edge_if_bst :
    forall F x y o,
      Inv p D F V W ->
      path F x y -> 
      F y x o ->
      False.
  Proof.
    intros F x y o Inv **.
    assert (path F y x) as Pyx.
    apply path_single with o ; auto.
    assert (x = y).
    pose proof (path_step_equal_if_bst F x y Inv H Pyx).
    auto. subst. stlink_tac.
  Qed.
  
  Lemma orientation_path_value :
    forall F x y z o,
      Inv p D F V W ->
      F x y o ->
      path F y z -> 
      orientation_op o (V x) (V z).
  Proof.
    intros.
    destruct o ; simpl.
    + pose proof (path_value_left_if_bst F x y z).
      auto.
    + pose proof (path_value_right_if_bst F x y z).
      auto.
  Qed.
    
End PathSplayTree.

Ltac stpath_tac :=
  match goal with
  (* path_refl *)
  | |- path ?F ?x ?x =>
    apply path_refl
  (* path_single *)
  | h1 : ?F ?x ?y ?o |- path ?F ?x ?y =>
    apply (path_single F x y o h1)
  (* path_trans *)
  | h1 : path ?F ?x ?y, h2 : path ?F ?y ?z  |- path ?F ?x ?z =>
    apply (path_trans F x y z h1 h2)
  (* path_value_left_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y LEFT, h3 : path ?F ?y ?z |- (?V ?x > ?V ?z)%Z =>
    apply (path_value_left_if_bst p D V W F x y z h1 h2 h3)
  (* path_value_right_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y RIGHT, h3 : path ?F ?y ?z |- (?V ?x < ?V ?z)%Z =>
    apply (path_value_right_if_bst p D V W F x y z h1 h2 h3)
  (*different_nodes_on_bifurcation_if_bst*)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y LEFT, h3 : ?F ?x ?z RIGHT,
    h4 : path ?F ?y ?y', h5 : path ?F ?z ?z' |- ¬(?y' = ?z') => 
    apply (different_nodes_on_bifurcation_if_bst p D V W F x y z y' z' h1 h3 h2 h4) in h5 ; lia
  (*different_nodes_on_bifurcation_if_bst*)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y LEFT, h3 : ?F ?x ?z RIGHT,
    h4 : path ?F ?y ?y', h5 : path ?F ?z ?z' |- ¬(?z' = ?y') => 
    apply (different_nodes_on_bifurcation_if_bst p D V W F x y z y' z' h1 h3 h2 h4) in h5 ; lia
  (* only_one_parent_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?z ?o, h3 : ?F ?y ?z ?u |- (?x = ?y) =>
    apply (only_one_parent_if_bst p D V W F x y z o u h1 h2 h3)     
  (* only_one_parent_left_right_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?z LEFT, h3 : ?F ?y ?z RIGHT |- _ =>
    exfalso ; apply (only_one_parent_left_right_if_bst p D V W F x y z h1 h2 h3)
  (* different_pointers_for_path_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?o, h3 : path ?F ?y ?z |- ¬(?x = ?z) =>
    apply (different_pointers_for_path_if_bst p D V W F x y z o h1 h2) in h3 ; lia
  (* different_pointers_for_path_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?o, h3 : path ?F ?y ?z |- ¬(?z = ?x) =>
    apply (different_pointers_for_path_if_bst p D V W F x y z o h1 h2) in h3 ; lia
  (* no_path_from_end_to_root *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?o, h3 : path ?F ?y ?p |- _ =>
    exfalso ; apply (no_path_from_end_to_root p D V W F x y o h1 h2 h3)
  (* if_in_domain_then_path_from_root_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?x \in ?D |- path ?F ?p ?x =>
    apply (if_in_domain_then_path_from_root_if_bst p D V W F x h1 h2)
  (* path_only_if_child_equal *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?u, h3 : ?F ?x ?z ?o,
    h4 : path ?F ?y ?z |- ?y = ?z =>
    apply (path_only_if_child_equal p D V W F x y z u o h1 h2 h3) in h4 ; lia
  (* path_only_if_child_equal *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?u, h3 : ?F ?x ?z ?o,
    h4 : path ?F ?y ?z |- ?z = ?y =>
    apply (path_only_if_child_equal p D V W F x y z u o h1 h2 h3) in h4 ; lia
  (* path_only_if_child_equal *)
  | h1 : ?F ?x ?y ?u, h2 : ?F ?y ?z ?o |- path ?F ?x ?z =>
    apply path_single in h1 ; apply path_single in h2 ; apply path_trans with y ; auto
  (* path_only_if_child_equal *)
  | h1 : ?F ?x ?y ?u, h2 : path ?F ?y ?z |- path ?F ?x ?z =>
    apply path_single in h1 ; apply path_trans with y ; auto
  (* path_only_if_child_equal *)
  | h1 : path ?F ?x ?y, h2 : ?F ?y ?z ?o |- path ?F ?x ?z =>
    apply path_single in h2 ; apply path_trans with y ; auto
  (* path_to_root_then_root_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : path ?F ?x ?p |- ?x = ?p =>
    apply (path_to_root_then_root_if_bst p D V W F x h1) in h2 ; lia
  (* path_to_root_then_root_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : path ?F ?x ?p |- ?p = ?x =>
    apply (path_to_root_then_root_if_bst p D V W F x h1) in h2 ; lia
                                                                   
  (* if_path_from_x_to_y_then_no_edge_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : path ?F ?x ?y, h3 : ?F ?y ?x ?o |- _  =>
    exfalso ; apply (if_path_from_x_to_y_then_no_edge_if_bst p D V W F x y o h1 h2) in h3 ; auto

                            
  (* if_path_from_x_to_y_then_no_edge_if_bst *)
  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?o , h3 : path ?F ?y ?z |-
    orientation_op ?o (?V ?x) (?V ?z)  =>
    apply (orientation_path_value p D V W F x y z o h1 h2 h3) ; auto

  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?o , h3 : ?F ?y ?x ?u |- _
    =>
    apply path_single in h3;
    apply (no_cycles_if_bst p D V W F x y o) in h2 ; auto ; contradiction

  | h1 : Inv ?p ?D ?F ?V ?W, h2 : ?F ?x ?y ?o , h3 : ?F ?y ?z ?u, h4 : ?F ?z ?x ?t |- _
    =>
    apply path_single in h3 ;
    apply path_single in h4 ;
    exfalso ;
    apply (no_cycles_if_bst p D V W F x y o) ; auto ; apply path_trans with z ; auto


  | h1 : Inv ?p ?D ?F ?V ?W, h2 : path ?F ?x ?y , h3 : path ?F ?y ?x |-
    (?x = ?y)
    => apply (path_step_equal_if_bst p D V W F x y) ; auto
  | _ => idtac
  end.
                                                    
Example ex1 : forall p D V F W x y z,
    Inv p D F V W ->    
    F x y LEFT ->
    path F y z ->
    (V x > V z)%Z.
Proof.
  intros. stpath_tac.
Qed.

Example ex2 : forall p D V F W x y z,
    Inv p D F V W ->    
    F x y RIGHT ->
    path F y z ->
    (V x < V z)%Z.
Proof.
  intros. stpath_tac.
Qed.


Example ex3 : forall p D V F W x y z u o,
    Inv p D F V W ->    
    F x y u ->
    F z y o ->
    x = z.
Proof.
  intros. stpath_tac.
Qed.

Example ex4 : forall p D V F W x y z P,
    Inv p D F V W ->    
    F x z LEFT ->
    F y z RIGHT ->
    P.
Proof.
  intros. stpath_tac.
Qed.

Example ex5 : forall p D V F W x y z y' z',
    Inv p D F V W ->    
    F x y LEFT ->    
    F x z RIGHT ->
    path F y y' ->
    path F z z' ->
    ¬(y' = z').
Proof.
  intros. stpath_tac.
Qed.

Example ex6 : forall p D V F W x y z o,
    Inv p D F V W ->    
    F x y o ->    
    path F y z ->
    ¬(x = z).
Proof.
  intros. stpath_tac.
Qed.

Example ex7 : forall (F : EdgeSet) x y o,
    F x y o -> 
    path F x y.
Proof.
  intros. stpath_tac.
Qed.

Example ex8 : forall (F : EdgeSet) x,
    path F x x.
Proof.
  intros. stpath_tac.
Qed.

Example ex9 : forall (F : EdgeSet) x y z,
    path F x y ->
    path F y z ->    
    path F x z.
Proof.
  intros.
  stpath_tac.
Qed.

Example ex10 : forall p D V F W x y o P,
    Inv p D F V W ->    
    F x y o -> 
    path F y p ->
    P.
Proof.
  intros. stpath_tac.
Qed.

Example ex11 : forall p D V F W x,
    Inv p D F V W ->    
    x \in D ->
    path F p x.
Proof.
  intros. stpath_tac.
Qed.

Example ex12 : forall p D V F W x y z u o,
    Inv p D F V W ->    
    F x y u -> 
    F x z o ->
    path F y z ->
    z = y.
Proof.
  intros. stpath_tac.
Qed.

Example ex13 : forall p D V F W x y z u o,
    Inv p D F V W ->    
    F x y o ->
    F y z u ->
    path F x z.
Proof.
  intros. stpath_tac.
Qed.

Example ex14 : forall p D V F W x y z o,
    Inv p D F V W ->    
    F x y o ->
    path F y z -> 
    path F x z.
Proof.
  intros. stpath_tac.
Qed.

Example ex15 : forall p D V F W x y z u,
    Inv p D F V W ->
    path F x y -> 
    F y z u ->
    path F x z.
Proof.
  intros. stpath_tac.
Qed.

Example ex16 : forall p D V F W x,
    Inv p D F V W ->
    path F x p ->
    x = p.
Proof.
  intros. stpath_tac.
Qed.

Example ex17 : forall p D V F W x,
    Inv p D F V W ->
    path F x p ->
    p = x.
Proof.
  intros. stpath_tac.
Qed.

Example ex18 : forall p D V F W x y z o,
    Inv p D F V W ->
    F x y o ->
    path F y z -> 
    orientation_op o (V x) (V z).
Proof.
  intros. stpath_tac.
Qed.
                                         
Example ex19 : forall p D V F W x y P u,
    Inv p D F V W ->    
    F x y LEFT ->
    F y x u ->
    P.
Proof.
  intros. stpath_tac.
Qed.
                                         
Example ex20 : forall p D V F W x y z P u o t,
    Inv p D F V W ->    
    F x y o ->
    F y z u ->
    F z x t ->
    P.
Proof.
  intros. stpath_tac.
Qed.
                                        
Example ex21 : forall p D V F W x y,
    Inv p D F V W ->
    path F x y ->
    path F y x ->
    x = y.
Proof.
  intros. stpath_tac.
Qed.


