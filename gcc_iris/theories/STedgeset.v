From ST Require Import STorientation STpredicate STdomain STlink STpath STvaluefunction.
From TLC Require Import LibTactics LibLogic LibSet LibRelation LibFun LibEqual LibInt.
Require Import Coq.Logic.FunctionalExtensionality.

From iris_time.heap_lang Require Import proofmode.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

Notation elem := loc.
Notation EdgeSet := (elem -> elem -> orientation -> Prop).
  
Section EdgeSetOperations.

  (*

           F :

            \/
            x
          /  \
         /   ª    
        z----y
       /\  
         
    (remove_edge F x y) :

           \/
           x
          /      
         z--y
        /\  

   *)
  
  Definition remove_edge (F : EdgeSet) x y :=
    fun x' y' o' =>
      ((x' ≠ x) \/ (y' ≠ y)) /\ F x' y' o'.

  (*

           F :

            \/
            x
          /       
         z---y
        /\  
         
    (add_edge F x y) :

           \/
           x
          / \     
         z--y
        /\  

   *)

  Definition add_edge (F : EdgeSet) x y o :=
    fun x' y' o' =>
      F x' y' o' \/ (x' = x /\ y' = y /\ o' = o).

  (*

           F :

            \/
            x ---u--- p
          /  \     
         z---y
        /\  
         
    (update_edge F x y p o) :

           \/
           x ---o--- p
          /      
         z--y
        /\  

    Update edge, removes edge (x,y) and (x,p) and 
    adds (x,p). It removes (x,p), because we can 
    have (x,p) with orientation u and want to update
    it to o.

   *)
  
  Definition update_edge (F : EdgeSet) x y y'' o'':=
    fun x' y' o' => 
      (((x' ≠ x) \/ (y' ≠ y)) /\ ((x' ≠ x) \/ (y' ≠ y'')) /\ F x' y' o') \/
      (((x' = x) /\ (y' = y'') /\ (o' = o''))).

  (* Remove edges that have a path from node *)

  Definition remove_edge_that_are_not_in_D (F : EdgeSet) (D : set elem) :=
    fun x' y' o' =>
      (x' \in D) /\ (y' \in D) /\ F x' y' o'.

  Definition remove_edge_that_are_in_D (F : EdgeSet) (D : set elem) :=
    fun x' y' o' =>
      (¬(x' \in D) /\ ¬(y' \in D)) /\ F x' y' o'.

  (* Union of edgeset *)
  
  Definition union_edge (F1 F2 : EdgeSet):=
    fun x' y' o' =>
      F1 x' y' o' \/ F2 x' y' o'.

  Definition disjointed_edge_set (F1 F2 : EdgeSet) :=
    forall x y o x' y' o',
      F1 x y o -> F2 x' y' o' ->
      ¬(x = x') /\ ¬(x = y') /\ ¬(y = x') /\ ¬(y = y').
  
  Definition incl_edge_set (F1 F2 : EdgeSet) :=
    forall x y o,
      F1 x y o -> F2 x y o.
  
End EdgeSetOperations.

Section EdgeSetProof.

  Lemma add_edge_specification : forall F x y o,
      (add_edge F x y o) x y o.
  Proof.
    intros. unfold add_edge. right.
    repeat split ; auto.
  Qed.
  
  Lemma remove_edge_specification : forall F x y o,
      ~ ((remove_edge F x y) x y o).
  Proof.
    intros. unfold not ; intro.
    unfold remove_edge in H.
    unpack. destruct H ; auto.
  Qed.

  Lemma remove_edge_path_add_memory_inv : forall F x y a b l,
      path_add_memory (remove_edge F a b) x y (rev l) ->
      path_add_memory F x y (rev l).
  Proof.
    intros F x y a b l.
    generalize y ; induction l ; intros y' H.
    + inversion H ; subst.
      - apply path_am_refl.
      - apply app_eq_nil in H0 ; unpack ; discriminate.
    + simpl in H. inversion H ; subst.
      - symmetry in H4. apply app_eq_nil in H4 ; unpack ; discriminate.
      - symmetry in H0. apply app_eq_unit in H0. destruct H0 ; unpack ; try discriminate.
        inversion H1 ; subst. simpl. rewrite -> H0 in *. simpl in *.
        destruct H4. apply path_am_single with o ; auto.
      - apply app_inj_tail in H0. unpack ; subst.
        apply IHl in H5. simpl.
        destruct H1. 
        apply (path_add_memory_transitivity) with a0 ; auto.
        apply path_am_single with o ; auto.
  Qed.  

  (*

        If removing an edge on a graph
        doesn't modify the path from x
        to y, then the path exists on 
        the graph.

        If path from x y:

        x --- ~ a ~ --- > y


        Then, adding (a,b) does not 
        modify the path!

                  b
                 /
        x --- ~ a ~ --- > y

  *)
  
  Lemma remove_edge_inv : forall F x y a b,
      path (remove_edge F a b) x y ->
      path F x y.
  Proof.
    intros.
    apply path_implies_path_add in H.
    apply path_add_memory_equiv_path_add in H. destruct H.
    pose proof (remove_edge_path_add_memory_inv F x y a b (rev x0)).
    rewrite rev_involutive in H0. apply H0 in H.
    apply path_add_memory_implies_path in H ; auto.
  Qed.
    
  Lemma add_edge_inv : forall F x y a b c,
      path F x y ->
      path (add_edge F a b c) x y.
  Proof.
    intros. 
    induction H.
    + apply path_refl.
    + apply path_single with o. unfold add_edge.
      auto.
    + apply path_trans with y ; auto.
  Qed.

  Lemma add_edge_memory_inv : forall F x y a b c l,
      path_memory F x y l ->
      path_memory (add_edge F a b c) x y l.
  Proof.
    intros. 
    induction H.
    + apply path_m_refl.
    + apply path_m_single with o. unfold add_edge.
      auto.
    + apply path_m_add with y o ; auto.
      unfold add_edge. left ; auto.
  Qed.


  (*

        path (add_edge F a b c) x y l

              p
             /
            x 
           / \          
          a  e
        c/\   \
        b      y

        IF:

        there is no a in l, i.e., we 
        don't need to go trough a to 
        get from x to y.

        THEN:
 
        path F x y l

              p
             /
            x 
           / \          
          a  e
          \   \
        b      y
   *)
  
  Lemma add_edge_with_memory_inv_backwards : forall F x y a b c l,
      path_memory (add_edge F a b c) x y l ->
      Forall (fun e => ¬(e = a)) l ->
      path_memory F x y l.
  Proof.
    intros F x y a b c l. generalize x y a b c.
    induction l ; intros.
    + inversion H ; subst.
      apply path_m_refl.
    + inversion H0 ; subst.
      inversion H ; subst.
      - destruct H7 ; auto.
        * apply path_m_single with o ; auto.
        * unpack ; subst ; auto. exfalso ; contradiction.
      - apply IHl in H9 ; auto. destruct H8 ; unpack ; subst ; auto.
        * apply path_m_add with y1 o ; auto.
        * exfalso ; contradiction.
  Qed.
  
  Lemma if_x_not_in_path_then_adding_edge_from_x_does_not_change_ :
    forall F x y1 y2 z o l,
      path_memory (add_edge F x y1 o) y2 z l ->
      Forall (fun e => ~(x = e)) l -> 
      path_memory F y2 z l.
  Proof.
    intros F x y1 y2 z o l.
    generalize x y1 y2 z o.
    induction l ; intros.
    + inversion H ; subst. apply path_m_refl.
    + inversion H ; subst.
      - destruct H5 ; unpack ; subst.
        * apply path_m_single with o1 ; auto.
        * inversion H0 ; subst. contradiction.
      - destruct H6 ; unpack ; subst.
        * apply path_m_add with y o1 ; auto.
          apply IHl with x0 y0 o0 ; auto.
          inversion H0 ; auto.
        * inversion H0 ; subst. contradiction.
  Qed.

  Lemma adding_edge_to_end_of_path_memory_inv :
    forall F x y z o l,
      path_memory (add_edge F y z o) x y l ->
      exists l', path_memory F x y l'.
  Proof.
    intros F x y z o l.
    generalize x y z o.
    induction l.
    + intros. inversion H ; subst. eexists ([]). apply path_m_refl.
    + intros. inversion H ; subst.
      - destruct H4.
        * exists [a]. apply path_m_single with o1 ; auto.
        * destruct H0 ; subst. eexists ([]). apply path_m_refl.
      - destruct H5 ; unpack ; subst.
        * apply IHl in H6. destruct H6.
          exists ([a] ++ x0). apply path_app with y1 ; auto.
          apply path_m_single with o1 ; auto.
        * eexists ([]). apply path_m_refl.
  Qed.

  (*
       
    path (add_edge F y z o) x y     path F x y

        x                               x
        \                               \
        ~                               ~
        \            then               \
        y                               y
        \
        z
              
   *)
  
  Theorem adding_edge_to_end_of_path_inv :
    forall F x y z o,
      path (add_edge F y z o) x y ->
      path F x y.
  Proof.
    intros F x y z o H.
    apply path_exists_one in H.
    destruct H.
    pose proof (adding_edge_to_end_of_path_memory_inv F x y z o).
    apply H0 in H. destruct H. apply path_memory_implies_path in H. auto.
  Qed.  
  
  Lemma adding_edge_to_beginning_of_path_add_memory_rev_inv :
    forall F x y z o l,
      path_add_memory (add_edge F z x o) x y (rev l) ->
      exists l', path_add_memory F x y l'.
  Proof.
    intros F x y z o l.
    generalize x y z o.
    induction l.
    + intros. inversion H ; subst. eexists ([]). apply path_am_refl.
      apply app_eq_nil in H0. unpack. inversion H2.
    + intros. inversion H ; subst.
      - symmetry in H4. apply app_eq_nil in H4. unpack.
        discriminate.
      - destruct H4 ; unpack ; subst.
        * exists [x0]. apply path_am_single with o1 ; auto.
        * eexists ([]). apply path_am_refl.
      - destruct H1 ; unpack ; subst.
        * apply app_inj_tail in H0. unpack ; subst. apply IHl in H5.
          destruct H5. exists (x1 ++ [a]). apply path_add_memory_transitivity with a ; auto.
          apply path_am_single with o1 ; auto.
        * eexists ([]). apply path_am_refl.
  Qed.

  Lemma adding_edge_to_beginning_of_path_add_memory_inv :
    forall F x y z o l,
      path_add_memory (add_edge F z x o) x y l ->
      exists l', path_add_memory F x y l'.
  Proof.
    intros F x y z o l.
    pose proof (adding_edge_to_beginning_of_path_add_memory_rev_inv F x y z o (rev l)).
    rewrite rev_involutive in H. auto.
  Qed.

  (*
       
    path (add_edge F x y o) y z     path F y z

        x                            
        \
        y                               y
        \                               \
        ~                               ~
        \            then               \
        z                               z
              
   *)
  
  Theorem adding_edge_to_beginning_of_path_inv: forall F x y z o,
      path (add_edge F x y o) y z ->
      path F y z.
  Proof.
    intros F x y z o H.
    apply path_add_equiv_path in H.
    apply path_add_memory_equiv_path_add in H.
    destruct H. 
    pose proof (adding_edge_to_beginning_of_path_add_memory_inv F y z x o x0 H).
    apply path_add_memory_equiv_path_add in H0.
    apply path_add_equiv_path in H0. auto.
  Qed.
  
  Lemma update_edge_equiv_specification : forall F x y y'' o'',
      forall a b c,
        ((add_edge (remove_edge (remove_edge F x y) x y'') x y'' o'') a b c <->
         (update_edge F x y y'' o'') a b c).
  Proof.
    intros. 
    unfold add_edge in *.
    unfold remove_edge in *.
    unfold update_edge in *.
    split ; intro ;destruct H ; unpack ;
      repeat split ; auto.
  Qed.

  Lemma update_edge_comm : forall F x y z x' y' z' o u,
      forall a b c,
        ¬(x = x') -> 
        (update_edge (update_edge F x y z u) x' y' z' o) a b c <->
        (update_edge (update_edge F x' y' z' o) x y z u) a b c.
  Proof.
    intros. split ; unfold update_edge ;intro H1. 
    + destruct H1 ; unpack ; subst.
      - destruct H2 ; unpack ; subst.
        * left. split ; auto.
        * right ; auto.
      - left. split ; auto.
    + destruct H1 ; unpack ; subst.
      - destruct H2 ; unpack ; subst ; auto.
        left. split ; auto.
      - left. split ; auto.        
  Qed.

  Lemma update_edge_path_memory_comm : forall F x y z x' y' z' o u a b l,
        ¬(x = x') -> 
        path_add_memory (update_edge (update_edge F x y z u) x' y' z' o) a b (rev l) ->
        path_add_memory (update_edge (update_edge F x' y' z' o) x y z u) a b (rev l).
  Proof.
    intros. generalize dependent b. induction l ; intros.
    + inversion H0 ; subst.
      - apply path_am_refl.
      - apply app_eq_nil in H1 ; unpack ; discriminate.
    + inversion H0 ; subst.
      - symmetry in H5. apply app_eq_nil in H5. unpack ; discriminate.
      - symmetry in H1. apply app_eq_unit in H1. destruct H1 ; unpack ; try discriminate.
        rewrite -> H1 in *.
        inversion H2 ; subst.
        destruct H5 ; unpack ; subst ; simpl in * ; rewrite -> H1 in * ; simpl in *.
        * simpl. destruct H5 ; unpack ; subst.
          { apply path_am_single with o0. left.
            repeat split ; auto. 
            left. repeat split ; auto.
          }
          {
            apply path_am_single with u. right ; auto.
          }
        * apply path_am_single with o.
          left. repeat split ; auto.  right. auto.
      - apply app_inj_tail in H1 ; unpack ; subst.
        apply IHl in H6. simpl. apply path_am_add with o0 ; auto.
        apply update_edge_comm ; auto.
  Qed.

  Lemma update_edge_path_comm : forall F x y z x' y' z' o u a b,
      ¬(x = x') -> 
      path (update_edge (update_edge F x y z u) x' y' z' o) a b ->
      path (update_edge (update_edge F x' y' z' o) x y z u) a b.
  Proof.
    intros.
    apply path_implies_path_add in H0.
    apply path_add_memory_equiv_path_add in H0.
    destruct H0. rewrite <- (rev_involutive x0) in H0.
    apply update_edge_path_memory_comm in H0 ; auto.
    rewrite rev_involutive in H0. apply path_add_memory_implies_path with x0 ; auto.
  Qed.

  Lemma add_edge_if_no_path_add_memory_inv : forall F x' y' o' x y l,
      ¬(path F x x') ->
      path_add_memory (add_edge F x' y' o') x y (rev l) ->
      path_add_memory F x y (rev l).
  Proof.
    intros F x' y' o' x y l NP P.
    generalize dependent y.
    induction l ; intros.
    + inversion P ; subst.
      - apply path_am_refl.
      - apply app_eq_nil in H. unpack ; discriminate.
    + inversion P.
      - symmetry in H3. apply app_eq_nil in H3. unpack ; discriminate.
      - symmetry in H. apply app_eq_unit in H. destruct H ;  unpack ; try discriminate.
        inversion H4 ; subst. simpl. rewrite H. simpl.
        destruct H3 ; unpack ; subst.
        * simpl. apply path_am_single with o ; auto.
        * exfalso. apply NP. apply path_refl.
      - apply app_inj_tail in H. unpack ; subst.
        apply IHl in H4. destruct H0 ; unpack ; subst.
        * simpl. apply path_add_memory_transitivity with a ; auto.
          apply path_am_single with o ; auto.
        * apply path_add_memory_implies_path in H4. contradiction.
  Qed.
  
  Lemma add_edge_if_no_path_inv : forall F x' y' o' x y,
      ¬(path F x x') ->
      path (add_edge F x' y' o') x y ->
      path F x y.
  Proof.
    intros F x' y' o' x y NP P.
    apply path_add_equiv_path in P.
    apply path_add_memory_equiv_path_add in P.
    destruct P.
    pose proof (add_edge_if_no_path_add_memory_inv F x' y' o' x y (rev x0)).
    rewrite rev_involutive in H0.
    assert (path_add_memory F x y x0). apply H0 ; auto.
    apply path_add_memory_implies_path in H1. auto.
  Qed.
  
  Lemma remove_edge_comm : forall F x' y' x'' y'' x y,
    path (remove_edge (remove_edge F x' y') x'' y'') x y ->
    path (remove_edge (remove_edge F x'' y'') x' y') x y.
  Proof.
    intros F x' y' x'' y'' x y.
    intro H ; apply path_implies_path_add_memory in H ; destruct H.
    assert (exists x1, (rev x1 = x0)).
    exists (rev x0) ; rewrite rev_involutive ;
    auto. destruct H0 ; rewrite <- H0 in * ;
    clear dependent  x0 ;
    generalize dependent y ;
    induction x1 ; intros.
    + inversion H ; subst. apply path_refl.
      apply app_eq_nil in H0. unpack ; discriminate.
    + inversion H ; subst.
      - symmetry in H4. apply app_eq_nil in H4.
        unpack ; discriminate.
      - symmetry in H0. apply app_eq_unit in H0.
        destruct H0 ; unpack ; try discriminate.
        inversion H1. subst. destruct H4.
        destruct H3. apply path_single with o.
        repeat split ; auto.
      - apply app_inj_tail in H0. unpack ; subst.
        apply IHx1 in H5.
        apply path_trans with a ; auto.
        apply path_single with o.
        destruct H1. destruct H1. repeat split ; auto.
  Qed.  


  Lemma path_remove_domain : forall F D x y, 
      path (remove_edge_that_are_not_in_D F D) x y ->
      path F x y.
  Proof.
    intros.
    apply path_implies_path_add_memory in H ; destruct H.
    assert (exists x1, (rev x1 = x0)).
    exists (rev x0) ; rewrite rev_involutive ;
    auto. destruct H0 ; rewrite <- H0 in *.
    clear dependent x0. generalize dependent y.
    induction x1 ; intros.
    + inversion H ; subst ; stpath_tac.
      apply app_eq_nil in H0 ; unpack ; discriminate.
    + inversion H ; subst.
      - symmetry in H4. apply app_eq_nil in H4.
        unpack ; discriminate.
      - symmetry in H0. apply app_eq_unit in H0.
        destruct H0 ; unpack ; try discriminate.
        inversion H1. subst. destruct H4 ; unpack.
        apply path_single with o ; auto.
      - apply app_inj_tail in H0.
        unpack ; subst.
        destruct H1 ; unpack. apply IHx1 in H5.
        apply path_trans with a ; auto.
        stpath_tac.
  Qed.
  
  Lemma union_edge_inv_l : forall F1 F2 x y,
      path F1 x y -> 
      path (union_edge F1 F2) x y.
  Proof.
    intros.
    apply path_implies_path_add_memory in H ; destruct H.
    assert (exists x1, (rev x1 = x0)).
    exists (rev x0) ; rewrite rev_involutive ;
    auto. destruct H0 ; rewrite <- H0 in *.
    clear dependent x0. generalize dependent y.
    induction x1 ; intros.
    + inversion H ; subst ; stpath_tac.
      apply app_eq_nil in H0 ; unpack ; discriminate.
    + inversion H ; subst.
      - symmetry in H4. apply app_eq_nil in H4.
        unpack ; discriminate.
      - symmetry in H0. apply app_eq_unit in H0.
        destruct H0 ; unpack ; try discriminate.
        inversion H1. subst. 
        apply path_single with o ; auto.
        left. auto.
      - apply app_inj_tail in H0.
        unpack ; subst. apply IHx1 in H5.
        assert (path (union_edge F1 F2) a y).
        apply path_single with o. left. auto.
        apply path_trans with a ; auto.
  Qed.

  Lemma union_edge_inv_r : forall F1 F2 x y,
      path F2 x y -> 
      path (union_edge F1 F2) x y.
  Proof.
    intros.
    apply path_implies_path_add_memory in H ; destruct H.
    assert (exists x1, (rev x1 = x0)).
    exists (rev x0) ; rewrite rev_involutive ;
    auto. destruct H0 ; rewrite <- H0 in *.
    clear dependent x0. generalize dependent y.
    induction x1 ; intros.
    + inversion H ; subst ; stpath_tac.
      apply app_eq_nil in H0 ; unpack ; discriminate.
    + inversion H ; subst.
      - symmetry in H4. apply app_eq_nil in H4.
        unpack ; discriminate.
      - symmetry in H0. apply app_eq_unit in H0.
        destruct H0 ; unpack ; try discriminate.
        inversion H1. subst. 
        apply path_single with o ; auto.
        right. auto.
      - apply app_inj_tail in H0.
        unpack ; subst. apply IHx1 in H5.
        assert (path (union_edge F1 F2) a y).
        apply path_single with o. right. auto.
        apply path_trans with a ; auto.
  Qed.

  Lemma union_edge_inv_2 : forall F1 F2 x y,
      path F1 x y \/ path F2 x y -> 
      path (union_edge F1 F2) x y.
  Proof.
    intros.
    destruct H.
    + apply union_edge_inv_l ; auto.
    + apply union_edge_inv_r ; auto.
  Qed.

  Lemma union_edge_comm_inv : forall F1 F2 x y,
      path (union_edge F1 F2) x y ->
      path (union_edge F2 F1) x y.
  Proof.
    intros.
    intros.
    apply path_implies_path_add_memory in H ; destruct H.
    assert (exists x1, (rev x1 = x0)).
    exists (rev x0) ; rewrite rev_involutive ;
    auto. destruct H0 ; rewrite <- H0 in *.
    clear dependent x0. generalize dependent y.
    induction x1 ; intros.
    + inversion H ; subst ; stpath_tac.
      apply app_eq_nil in H0 ; unpack ; discriminate.
    + inversion H ; subst.
      - symmetry in H4. apply app_eq_nil in H4.
        unpack ; discriminate.
      - symmetry in H0. apply app_eq_unit in H0.
        destruct H0 ; unpack ; try discriminate.
        inversion H1. subst.
        destruct H4 ; 
          apply path_single with o ; auto ;
            [right|left] ; auto. 
      - apply app_inj_tail in H0.
        unpack ; subst. apply IHx1 in H5.
        apply path_trans with a ; auto.
        apply path_single with o.
        destruct H1 ; [right|left] ; auto.
  Qed.

  Lemma union_edge_end_inv : forall F1 F2 x y, 
      path (union_edge F1 F2) x y ->
      (exists z o, F1 z y o \/ F2 z y o) \/ x = y.
  Proof.
    intros.
    apply path_implies_path_add_memory in H ; destruct H.
    assert (exists x1, (rev x1 = x0)).
    exists (rev x0) ; rewrite rev_involutive ;
      auto. destruct H0 ; rewrite <- H0 in *.
    clear dependent x0. generalize dependent y.
    induction x1 ; intros.
    + inversion H ; subst ; stpath_tac.
      - right. auto.
      - apply app_eq_nil in H0 ; unpack ; discriminate.
    + inversion H ; subst.
      - symmetry in H4. apply app_eq_nil in H4 ; unpack ; discriminate.
      - symmetry in H0. apply app_eq_unit in H0 ; destruct H0 ; unpack ; try discriminate.
        inversion H1 ; subst. destruct H4 ; left ; eauto.
      - apply app_inj_tail in H0. unpack ; subst.
        destruct H1.
        * left. exists a, o. auto.
        * left. exists a, o. auto.
  Qed.

  Lemma union_edge_disjointed_inv : forall F1 F2 x y,
      disjointed_edge_set F1 F2 ->
      path (union_edge F1 F2) x y ->
      path F1 x y \/ path F2 x y.
  Proof.
    intros.
    apply path_implies_path_add_memory in H0 ; destruct H0.
    assert (exists x1, (rev x1 = x0)).
    exists (rev x0) ; rewrite rev_involutive ; auto.
    destruct H1 ; rewrite <- H1 in *.
    clear dependent x0. generalize dependent y.
    induction x1 ; intros.
    + inversion H0 ; subst ; stpath_tac.
      - auto using path_refl.
      - apply app_eq_nil in H1 ; unpack ; discriminate.
    + inversion H0 ; subst.
      - symmetry in H5. apply app_eq_nil in H5 ; unpack ; discriminate.
      - symmetry in H1. apply app_eq_unit in H1 ; destruct H1 ; unpack ; try discriminate.
        inversion H2 ; subst.
        destruct H5 ; [left|right] ; apply path_single with o ; auto.
      - apply app_inj_tail in H1. unpack ; subst.
        apply IHx1 in H6. 
        destruct H6.
        * destruct H2.
          { left. apply path_trans with a ; auto. apply path_single with o ; auto. }
          { pose proof (path_right_left_step_end_if_bst F1 x a H1).
            pose proof (classic (x = a)).
            destruct H4.
            + subst. right. apply path_single with o ; auto.
            + apply H3 in H4. destruct H4.
              destruct H4.
              left. destruct H4.
              - specialize (H x0 a RIGHT a y o H4 H2).
                unpack ; contradiction.
              - specialize (H x0 a LEFT a y o H4 H2).
                unpack ; contradiction.              
          }
        * destruct H2.
          { pose proof (path_right_left_step_end_if_bst F2 x a H1).
            pose proof (classic (x = a)).
            destruct H4.
            + subst. left. apply path_single with o ; auto.
            + apply H3 in H4. destruct H4.
              destruct H4.
              right. destruct H4.
              - specialize (H a y o x0 a RIGHT H2 H4).
                unpack ; contradiction.
              - specialize (H a y o x0 a LEFT H2 H4).
                unpack ; contradiction. 
          }
          { right. apply path_trans with a ; auto.
            apply path_single with o ; auto.
          }
  Qed.

  Lemma union_edge_disjointed_l_inv : forall F1 F2 x y,
      disjointed_edge_set F1 F2 ->
      path (union_edge F1 F2) x y ->
      ¬(path F2 x y) ->
      path F1 x y.
  Proof.
    intros.
    apply union_edge_disjointed_inv in H0 ; auto.
    destruct H0 ; auto. contradiction.
  Qed.

  Lemma union_edge_disjointed_r_inv : forall F1 F2 x y,
      disjointed_edge_set F1 F2 ->
      path (union_edge F1 F2) x y ->
      ¬(path F1 x y) ->
      path F2 x y.
  Proof.
    intros.
    apply union_edge_disjointed_inv in H0 ; auto.
    destruct H0 ; auto. contradiction.
  Qed.  

  Lemma path_edgeset_incl : forall (F1 F2 : EdgeSet) x y,
      (forall x y o, (F1 x y o -> F2 x y o)) ->
      path F1 x y -> path F2 x y.
  Proof.
    intros F1 F2 x y **.
    induction H0.
    + stpath_tac.
    + apply H in H0. stpath_tac.
    + apply path_trans with y ;
      [apply IHpath1|apply IHpath2] ; intros ; apply H in H0 ; auto.
  Qed.

  Lemma path_remove_edges_that_are_not_descendants : forall (F : EdgeSet) a y o x,
      F a y o ->
      path F y x ->
      path (remove_edge_that_are_not_in_D F (descendants F a)) y x.
  Proof.
    intros. apply path_implies_path_add in H0.
    induction H0 ; stpath_tac.
    + apply path_single with o0.
      repeat split ; [rewrite in_set_st_eq |rewrite in_set_st_eq |auto ] ; stpath_tac.
    + apply path_trans with y ; auto.
      apply path_single with o0. apply path_add_implies_path in H1.
      repeat split ; [rewrite in_set_st_eq|rewrite in_set_st_eq| ] ; auto ; stpath_tac.
      apply path_trans with y ; auto ; stpath_tac.
  Qed.

  Lemma path_add_remove_edges_that_are_not_descendants' : forall (F : EdgeSet) y x,
      path_add F y x ->
      path_add (remove_edge_that_are_not_in_D F (descendants F y)) y x.
  Proof.
    intros.
    induction H.
    + apply path_a_refl.
    + apply path_a_single with o. repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
    + pose proof (path_a_add (remove_edge_that_are_not_in_D F (descendants F x)) x y z o).
      apply H1 ; auto.
      apply path_add_implies_path in H0.
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
  Qed.
  
  Lemma path_add_remove_edges_that_are_not_descendants_double_path : forall (F : EdgeSet) y x z,
      path_add F y x ->
      path_add F x z ->
      path_add (remove_edge_that_are_not_in_D F (descendants F y)) x z.
  Proof.
    intros.
    induction H0.
    + apply path_a_refl.
    + apply path_a_single with o.
      repeat split ; auto ; rewrite in_set_st_eq.
      - apply path_add_equiv_path ; auto.
      - apply path_add_equiv_path. apply path_a_add with x o ; auto.
    + pose proof (H).
      apply IHpath_add in H.
      apply path_add_transitivity with y0 ; auto.
      apply path_a_single with o.
      apply path_add_equiv_path in H2.
      apply path_add_equiv_path in H1.        
      repeat split ; auto ; rewrite in_set_st_eq.
      - apply path_trans with x ; stpath_tac ; auto.
      - apply path_trans with x ; auto.
        apply path_trans with y0 ; auto. stpath_tac.
  Qed.
  
  Lemma path_remove_edges_that_are_not_descendants_double_path : forall (F : EdgeSet) y x z,
      path F y x ->
      path F x z ->
      path (remove_edge_that_are_not_in_D F (descendants F y)) x z.
  Proof.
    intros.
    apply path_add_equiv_path.
    apply path_add_equiv_path in H0.
    apply path_add_equiv_path in  H.
    apply path_add_remove_edges_that_are_not_descendants_double_path ; auto.
  Qed.
  
  Lemma path_remove_edges_that_are_not_descendants' : forall (F : EdgeSet) y x,
      path F y x ->
      path (remove_edge_that_are_not_in_D F (descendants F y)) y x.
  Proof.
    intros.
    apply path_add_equiv_path. apply path_add_equiv_path in H.
    apply path_add_remove_edges_that_are_not_descendants' ; auto.
  Qed.
  
  Lemma if_path_on_remove_edge_then_path : forall (F : EdgeSet) x y z,
      path (remove_edge_that_are_not_in_D F (descendants F z)) x y ->
      path F x y.
  Proof.
    intros.
    apply path_implies_path_add_memory in H.
    destruct H.
    assert (exists l, rev l = x0).
    exists (rev x0). rewrite rev_involutive. auto.
    destruct H0. rewrite <- H0 in *. clear dependent x0.
    rename x1 into x0.
    generalize dependent y.
    induction x0 ;intros.
    + inversion H ; subst ; stpath_tac.
      apply app_eq_nil in H0.
      unpack ; discriminate.
    + inversion H ; subst ; stpath_tac.
      - symmetry in H0. apply app_eq_unit in H0 ; destruct H0 ; unpack ; try discriminate.
        inversion H1 ; subst. destruct H4 ; unpack. stpath_tac.
      - apply app_inj_tail in H0 ; unpack ; subst.
        apply IHx0 in H5. destruct H1 ; unpack ; stpath_tac.
  Qed.
  
  Lemma if_path_on_edge_set_then_path_on_descendant : forall F x y,
      path F x y ->
      path (remove_edge_that_are_not_in_D F (descendants F x)) x y.
  Proof.
    intros.
    apply path_implies_path_add_memory in H.
    destruct H.
    assert (exists l, rev l = x0).
    exists (rev x0). rewrite rev_involutive. auto.
    destruct H0. rewrite <- H0 in *. clear dependent x0.
    rename x1 into x0.
    generalize dependent y.
    induction x0 ;intros.
    + inversion H ; subst ; stpath_tac.
      apply app_eq_nil in H0.
      unpack ; discriminate.
    + inversion H ; subst ; stpath_tac.
      - symmetry in H0. apply app_eq_unit in H0 ; destruct H0 ; unpack ; try discriminate.
        inversion H1 ; subst. apply path_single with o.
        repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      - apply app_inj_tail in H0 ; unpack ; subst.
        apply IHx0 in H5.
        assert (path (remove_edge_that_are_not_in_D F (descendants F x)) a y).
        apply path_single with o. repeat split ; auto ; rewrite in_set_st_eq.
        apply if_path_on_remove_edge_then_path  in H5 ; stpath_tac ; auto.
        apply if_path_on_remove_edge_then_path  in H5 ; stpath_tac ; auto.
        stpath_tac.
  Qed.

  Lemma path_preserved_when_remove_edges_not_descendants :
    forall (F : EdgeSet) a y x o, 
      F a y o ->
      path (remove_edge_that_are_not_in_D F (descendants F a)) y x ->
      path (remove_edge_that_are_not_in_D F (descendants F y)) y x.
  Proof.
    intros.
    apply if_path_on_remove_edge_then_path in H0.
    apply if_path_on_edge_set_then_path_on_descendant in H0. auto.
  Qed.
  
  Lemma path_add_memory_preserved_when_remove_edges_not_descendants :
    forall (F : EdgeSet) a y x o l, 
      F a y o ->
      path_add_memory (remove_edge_that_are_not_in_D F (descendants F a)) y x l ->
      path_add_memory (remove_edge_that_are_not_in_D F (descendants F y)) y x l.
  Proof.
    intros.
    assert (exists l', l = rev l').
    exists (rev l). rewrite rev_involutive. auto.
    destruct H1. rewrite H1 in H0.  rewrite H1.
    clear dependent l.
    rename x0 into l. generalize dependent x.
    induction l ; intros.
    + inversion H0 ; subst.
      - apply path_am_refl.
      - apply app_eq_nil in H1 ; unpack ; discriminate.
    + inversion H0 ; subst.
      - symmetry in H5. apply app_eq_nil in H5. unpack ; discriminate.
      - symmetry in H1. apply app_eq_unit in H1. destruct H1 ; unpack ; try discriminate.
        inversion H2 ; subst. destruct H5 ; unpack.
        destruct l ; [|simpl in H1 ; apply app_eq_nil in H1 ; unpack ; discriminate].
        apply path_am_single with o0. repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      - apply app_inj_tail in H1 ; unpack ; subst.
        apply IHl in H6. simpl. apply path_add_memory_transitivity with a0 ; auto.
        apply path_am_single with o0.
        destruct H2 ; unpack.
        apply path_add_memory_implies_path in H6.
        apply if_path_on_remove_edge_then_path in H6.
        repeat split ; auto ; rewrite in_set_st_eq.
        rewrite in_set_st_eq in H1.
        rewrite in_set_st_eq in H2. stpath_tac.        
  Qed.

  Lemma path_domain_inclusion :
    forall (F : EdgeSet) D D' y x, 
      path (remove_edge_that_are_not_in_D F D) x y ->
      D \c D' -> 
      path (remove_edge_that_are_not_in_D F D') x y.
  Proof.
    intros.
    rewrite incl_in_eq in H0.
    apply path_implies_path_add_memory in H.
    destruct H.
    assert (exists x', rev x' = x0).
    exists (rev x0). rewrite rev_involutive. auto.
    destruct H1. rewrite <- H1 in H. clear dependent x0.
    rename x1 into x0.
    generalize dependent y.
    induction x0 ; intros.
    + inversion H ; subst ; stpath_tac.
      apply app_eq_nil in H1. unpack ; discriminate.
    + inversion H ; subst.
      - symmetry in H5. apply app_eq_nil in H5. unpack ; discriminate.
      - symmetry in H1. apply app_eq_unit in H1.
        destruct H1 ; unpack ; try discriminate.
        inversion H2 ; subst.
        destruct H5 ; unpack.
        apply path_single with o. repeat split ; auto.
      - apply app_inj_tail in H1 ; unpack ; subst.
        apply IHx0 in H6. apply path_trans with a ; auto.
        apply path_single with o. destruct H2 ; unpack.
        repeat split ; auto.
  Qed.
  
  Lemma remove_edge_if_inv : forall F x y t1 t2,
      path F x y ->
      ¬(path F x t1) -> 
      path (remove_edge F t1 t2) x y.
  Proof.
    intros.
    apply path_implies_path_add_memory in H.
    destruct H.
    assert (exists l, rev l = x0).
    exists (rev x0). rewrite rev_involutive ; auto.
    destruct H1. rewrite <- H1 in *. clear dependent x0.
    generalize dependent x.
    generalize dependent y.
    induction x1 ; intros.
    + inversion H ; subst.
      - apply path_refl.
      - apply app_eq_nil in H1. unpack. discriminate.
    + inversion H ; subst.
      - symmetry in H5. apply app_eq_nil in H5 ; unpack ; discriminate.
      - symmetry in H1. apply app_eq_unit in H1 ; destruct H1 ; unpack ; try discriminate.
        inversion H2 ; subst. apply path_single with o ; auto.
        split ; auto. rewrite  <- not_and_eq. intro. unpack ; subst.
        apply H0 ; stpath_tac.
      - apply app_inj_tail in H1 ; unpack ; subst. apply IHx1 in H6 ; auto.
        apply path_trans with a ; auto. apply path_single with o.
        repeat split ; auto. rewrite <- not_and_eq. intro. unpack ; subst.
        apply H0. apply remove_edge_inv in H6. auto.
  Qed.  
        
  Lemma update_edge_if_inv : forall F x y t1 t2 t3 o,
      path F x y ->
      ¬(path F x t1) -> 
      path (update_edge F t1 t2 t3 o) x y.
  Proof.
    intros.
    apply add_edge_inv.
    apply remove_edge_if_inv ; auto.
    - apply remove_edge_if_inv ; auto.
    - intro. apply remove_edge_inv in H1. contradiction.
  Qed.  

  Lemma remove_edge_that_are_in_D_path_inv : forall D F x y, 
      path (remove_edge_that_are_in_D F D) x y ->
      path F x y.
  Proof.
    intros.
    apply path_implies_path_add_memory in H.
    destruct H.
    assert (exists l, rev l = x0).
    exists (rev x0). rewrite rev_involutive ; auto.
    destruct H0. rewrite <- H0 in *. clear dependent x0.
    generalize dependent x.
    generalize dependent y.
    induction x1 ; intros.
    + inversion H ; subst.
      - apply path_refl.
      - apply app_eq_nil in H0. unpack. discriminate.
    + inversion H ; subst.
      - symmetry in H4. apply app_eq_nil in H4 ; unpack ; discriminate.
      - symmetry in H0. apply app_eq_unit in H0 ; destruct H0 ; unpack ; try discriminate.
        inversion H1 ; subst. apply path_single with o ; auto.
        destruct H4 ; unpack ; auto.
      - apply app_inj_tail in H0 ; unpack ; subst. apply IHx1 in H5 ; auto.
        apply path_trans with a ; auto. apply path_single with o.
        destruct H1 ; auto.
  Qed.
  
End EdgeSetProof.
  
Section EdgeSetSplayTree.
  
  Variable p : elem.
  Variable D : LibSet.set elem. (* domain *)
  Variable W : elem -> Z. (* weight nodes *)
  Variable V : elem -> Z. (* data stored in nodes *)
  
  Lemma subdomain_of_edgeset_in_domain : forall F x o,
      Inv p D F V W ->
      F p x o -> 
      let D' := (descendants F x) in
      D' \c D.
  Proof.
    intros.
    unfold D'.
    unfold descendants. intros. eapply incl_prove. intros. rew_set in *.
    pose proof (in_domain_if_edge_and_path_if_bst p D V W F p x o x0 H H0 H1).
    unpack ; auto.
  Qed.  

  Lemma adding_edge_to_itself_not_bst : forall F x o,
      ¬(Inv p D (add_edge F x x o) V W).    
  Proof.
    intros F x o Inv.
    inversion Inv.
    unfold is_bst in Inv_bst.    
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].    
    destruct o.
    + specialize (searchleft x x x).
      assert (add_edge F x x LEFT x x LEFT ∧ path (add_edge F x x LEFT) x x).
      split ; auto using path_refl.
      unfold add_edge. right ; auto. apply searchleft in H. lia.
    + specialize (searchright x x x).
      assert (add_edge F x x RIGHT x x RIGHT ∧ path (add_edge F x x RIGHT) x x).
      split ; auto using path_refl.
      unfold add_edge. right ; auto. apply searchright in H. lia.
  Qed.

    (*
              
        Adding an edge to a binary search tree,
        that currently does not exist, makes it
        a non binary search tree. 

        Suppose we have a binary search tree, 
        and both x and y belong to the domain of
        the tree. 

        Then, there are two paths from the root p 
        to each of these nodes!      

        p -> a -> x   p -> y
                  
              p            p
            // \          /\\
            a  y         a  y
          // \         // \
          x  t         x  t
         /\           /\

        Adding edge x -> y to the tree, implies that
        we have two different paths from node p to y:
        
        p -> a -> x -> y and p -> y

               p            
            //   \\          
            a    y         
          // \  /        
         //  t /
         x----/        
         /\           

        Which cannot happen in a binary search tree!
         

     *)
  
  Lemma adding_an_edge_to_a_bst_makes_it_not_bst : forall F x y o,
      Inv p D F V W ->
      x \in D /\ y \in D ->
      ¬ (exists u, F x y u) ->
      ¬(Inv p D (add_edge F x y o) V W).    
  Proof.
    intros F x y o Inv [xindomain yindomain] NE.
    intro InvN. inversion Inv. inversion InvN as [Inv_bst'].
    unfold is_bst in *.    
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]]. 
    destruct Inv_bst' as
        [confined' [rootisindomain' [isroot' [[searchleft' searchright'] [binarytree' finite']]]]]. 
    pose proof (isroot x RIGHT xindomain) as [_ Hxpath]. 
    pose proof (isroot y RIGHT yindomain) as [_ Hypath].
    apply (path_exists_only_one p D V W) in Hxpath ; auto. 
    apply (path_exists_only_one p D V W) in Hypath ; auto.
    destruct Hxpath, Hypath. destruct H, H0.
    pose proof (path_must_be_equal_if_bst p D V W (add_edge F x y o) p y x1 (x0++[x]) InvN).
    assert (path_memory (add_edge F x y o) p y x1).
    apply add_edge_memory_inv ; auto.
    assert (path_memory (add_edge F x y o) p y (x0 ++ [x])).
    apply path_app with x. apply add_edge_memory_inv ; auto.
    apply path_m_single with o. unfold add_edge. right ; auto.
    specialize (H3 H4 H5).
    pose proof (if_no_path_then_not_in_memory_if_bst p D V W (add_edge F x y o)). subst.
    pose proof
    (if_edge_does_not_exist_then_not_in_path_if_bst p D V W F x y p (x0 ++ [x]) Inv NE H0).
    apply H3. exists x0 ; auto.
  Qed.
  
  Lemma adding_edge_from_node_not_in_domain_path_memory_inv :
    forall F p' x y o l,
      Inv p D F V W ->
      ¬(x = p') /\ ¬(p' \in D) ->
      path_memory (add_edge F p' p o) x y l ->
      path_memory F x y l.
  Proof.
    intros F p' x y o l. 
    generalize p' x y o. 
    induction l ; intros p'' x' y' o' Inv H P ;
    inversion Inv ;
    unfold is_bst in Inv_bst ; 
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]]. 
    + inversion P ; subst. apply path_m_refl.
    + inversion P ; subst.
      - destruct H4 ; unpack ; subst.
        * apply path_m_single with o0 ; auto.
        * contradiction.
      - destruct H5 ; unpack ; subst.
        * apply path_m_add with y0 o0 ; auto.
          apply IHl with p'' o' ; auto.
          split ; auto.
          apply confined in H0 as [aindomain y0indomain]. intro ; subst.
          unpack ; contradiction.
        * contradiction.
  Qed.

  Lemma adding_edge_from_node_not_in_domain_to_root_path_inv : forall F p' x y o,
      Inv p D F V W ->
      ¬(x = p') /\ ¬(p' \in D) ->
      path (add_edge F p' p o) x y ->
      path F x y.
  Proof.
    intros F p' x y o Inv D' P.
    pose proof (adding_edge_from_node_not_in_domain_path_memory_inv).
    apply path_exists_one in P. destruct P.
    specialize (H F p' x y o x0 Inv D' H0).
    apply path_memory_implies_path in H. auto.
  Qed.
  
  (*

         Inv p D F V

              p
             /
            x 
           / \     
          z  y
         /\  
        
   Inv p' (D U p') (add_edge F p' p LEFT) (update V x v)
         
         
                p'
               /
              p
             /
            x 
           / \     
          z  y
         /\  
        
   if V p' > V p

 
   *)

  Lemma add_to_root_right_confined_if_bst : forall F p' v,
    Inv p D F V W ->
    ¬(exists y, F p y RIGHT) ->
    ¬(p' \in D) ->      
    v > V p -> 
    confined (D \u '{p'}) (add_edge F p' p LEFT).
  Proof.
    intros F p' v Inv **. unfold confined. intros.
    inversion Inv. unfold is_bst in Inv_bst. unpack.
    destruct H2 ; unpack ; subst.
    - apply H3 in H2 ; unpack.
      split ; apply in_union_l ; auto.
    - split.
      * apply in_union_r. apply in_single_self. 
      * apply in_union_l. auto. 
  Qed.

  Lemma add_to_root_right_rootisindomain_if_bst : forall F p' v,
    Inv p D F V W ->
    ¬(exists y, F p y RIGHT) ->
    ¬(p' \in D) ->      
    v > V p -> 
    rootisindomain p' (D \u '{p'}).
  Proof.
    intros F p' v Inv **. unfold rootisindomain. intros.
    inversion Inv. unfold is_bst in Inv_bst. unpack.
    apply in_union_r. apply in_single_self.
  Qed.

  Lemma add_to_root_right_isroot_if_bst : forall F p' v,
      Inv p D F V W ->
      ¬(exists y, F p y RIGHT) ->
      ¬(p' \in D) ->      
      v > V p -> 
      isroot (D \u '{p'}) (add_edge F p' p LEFT) p'.
  Proof.
    intros F p' v Inv.
    unfold isroot. intros.
    inversion Inv.
    unfold is_bst in Inv_bst ; 
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]]. 
    split.
    + intro. destruct H3 ; unpack ; subst.
      - apply confined in H3. unpack ; contradiction.
      - contradiction.
    + destruct H2.
      - apply isroot in H2 ; auto.
        apply path_trans with p ;
          [apply path_single with LEFT ; right ; auto
          |apply add_edge_inv;auto].
      - inversion H2 ; subst ; apply path_refl.
  Qed.

  Lemma add_to_root_right_searchtree_if_bst : forall F p' v,
    Inv p D F V W ->
    ¬(exists y, F p y RIGHT) ->
    ¬(p' \in D) ->      
    v > V p -> 
    searchtree (add_edge F p' p LEFT) (update_value V p' v).
  Proof.
    intros F p' v Inv.
    unfold isroot. intros.
    inversion Inv. 
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright]
                                             [binarytree [finite positive]]]]]]. 
    pose proof (if_no_right_branch_then_maximum_if_bst p D V W F Inv) as Max.
    split ; intros ; unpack ; unfold update_value.
    + destruct H2 ; unpack ; subst.
      - destruct (bool_decide (x = p')) eqn:XP'.
        apply bool_decide_eq_true in XP'. subst.
        apply confined in H2 ; unpack ; contradiction.
        destruct (bool_decide (y = p')) eqn:YP'.
        apply bool_decide_eq_true in YP'. subst.
        apply confined in H2 ; unpack ; contradiction.
        destruct (bool_decide (z = p')) eqn:ZP'.
        apply bool_decide_eq_true in ZP'. subst.
        apply adding_edge_to_end_of_path_inv in H3.
        apply confined in H2. unpack. specialize (isroot y LEFT H4).
        unpack. assert (path F p p'). apply path_trans with y ; auto.
        apply (path_domain_if_bst p D V W) in H7 ; auto. contradiction.
        split.
        * stlink_tac. 
        * apply adding_edge_from_node_not_in_domain_to_root_path_inv in H3 ; auto.
          assert (F x y LEFT /\ path F y z). split ; auto.
          destruct H4. stpath_tac.
          apply bool_decide_eq_false in YP'. split ; auto.
      - assert (bool_decide (p' = p') = true). apply bool_decide_eq_true ; auto.
        rewrite H2.
        destruct (bool_decide (p = p')) eqn:PP' ;
        try apply bool_decide_eq_true in PP' ;
        try apply bool_decide_eq_false in PP' ; subst.
        contradiction. split ; auto.
        destruct (bool_decide (z = p')) eqn:ZP' ;
        try apply bool_decide_eq_true in ZP' ;
        try apply bool_decide_eq_false in ZP' ; subst ;
        apply adding_edge_to_beginning_of_path_inv in H3 ;
        apply (path_domain_if_bst p D V W) in H3 ; auto.
        contradiction.
        apply Max in H3 ; auto. lia.      
    + destruct H2 ; unpack ; subst.
      - destruct (bool_decide (x = p')) eqn:XP'.
        apply bool_decide_eq_true in XP'. subst.
        apply confined in H2 ; unpack ; contradiction.
        destruct (bool_decide (y = p')) eqn:YP'.
        apply bool_decide_eq_true in YP'. subst.
        apply confined in H2 ; unpack ; contradiction.
        destruct (bool_decide (z = p')) eqn:ZP'.
        apply bool_decide_eq_true in ZP'. subst.
        apply adding_edge_to_end_of_path_inv in H3.
        apply confined in H2. unpack. specialize (isroot y LEFT H4).
        unpack. assert (path F p p'). apply path_trans with y ; auto.
        apply (path_domain_if_bst p D V W) in H7 ; auto. contradiction.
        split.
        * stlink_tac. 
        * apply adding_edge_from_node_not_in_domain_to_root_path_inv in H3 ; auto.
          assert (F x y RIGHT /\ path F y z). split ; auto.
          destruct H4. stpath_tac.
          apply bool_decide_eq_false in YP'. split ; auto.
      - assert (bool_decide (p' = p') = true). apply bool_decide_eq_true ; auto.
        rewrite H2.
        destruct (bool_decide (p = p')) eqn:PP' ;
        try apply bool_decide_eq_true in PP' ;
        try apply bool_decide_eq_false in PP' ; subst.
        contradiction. split ; auto ; try discriminate.
  Qed.  
  
  Lemma add_to_root_right_binarytree_if_bst : forall F p' v,
    Inv p D F V W ->
    ¬(exists y, F p y RIGHT) ->
    ¬(p' \in D) ->      
    v > V p -> 
    binarytree (add_edge F p' p LEFT) .
  Proof.
    intros F p' v Inv **. unfold binarytree. intros.
    inversion Inv.  unfold is_bst in Inv_bst. unpack.
    destruct H3, H4 ; unpack ; subst.
    - specialize (H9 x y z l r H2 H3 H4). auto.
    - apply H5 in H3 ; unpack ; contradiction.
    - apply H5 in H4 ; unpack ; contradiction.
    - contradiction.
  Qed.
        
  Theorem add_to_root_right_if_bst : forall F p' v,
    Inv p D F V W ->
    ¬(exists y, F p y RIGHT) ->
    ¬(p' \in D) ->      
    v > V p -> 
    Inv p' (D \u \{p'}) (add_edge F p' p LEFT) (update_value V p' v) W.
  Proof.
    intros F p' v Inv H1 H2 H3. inversion Inv.
    unfold is_bst in Inv_bst. unpack.
    constructor. unfold is_bst.
    split ; auto.
    (* confined *)
    apply add_to_root_right_confined_if_bst with v ; auto.
    split ; auto.
    (*rootisindomain*)
    apply add_to_root_right_rootisindomain_if_bst with F v ; auto.
    split ; auto.
    (*isroot*)
    apply add_to_root_right_isroot_if_bst with v ; auto.
    split ; auto.
    (*searchtree*)
    apply add_to_root_right_searchtree_if_bst ; auto.    
    (*binarytree*)
    split ; auto.
    apply add_to_root_right_binarytree_if_bst with v ; auto.
    split ; auto.
    apply finite_union ; [|apply finite_single] ; auto.
  Qed.

  Lemma update_comm_confined_inv : forall F x y z x' y' z' u o,
      ¬(x = x') ->
      confined D (update_edge (update_edge F x y z o) x' y' z' u) ->
      confined D (update_edge (update_edge F x' y' z' u) x y z o).
  Proof.
    intros. unfold confined in *. intros. apply (H0 x0 y0 o0).
    apply update_edge_comm in H1 ; auto.
  Qed.

  Lemma update_comm_isroot_inv : forall F x y z x' y' z' u o,
      ¬(x = x') -> 
      isroot D (update_edge (update_edge F x y z o) x' y' z' u) p ->
      isroot D (update_edge (update_edge F x' y' z' u) x y z o) p.
  Proof.
    intros F x y z x' y' z' u o H1 H2.
    unfold isroot in *. intros. apply (H2 x0 o0) in H ; auto.
    unpack. split.
    * intro. apply update_edge_comm in H3 ; auto.
    * apply update_edge_path_comm in H0 ; auto.
  Qed.

  Lemma update_comm_searchtree_inv : forall F x y z x' y' z' u o,
      ¬(x = x') -> 
      searchtree (update_edge (update_edge F x y z o) x' y' z' u) V ->
      searchtree (update_edge (update_edge F x' y' z' u) x y z o) V.
  Proof.
    intros F x y z x' y' z' u o H1 H2.
    unfold searchtree in *. split ; intros ;
    unpack ; apply update_edge_comm in H ; auto ;
    apply update_edge_path_comm in H0 ; auto.
  Qed.

  Lemma update_comm_binarytree_inv : forall F x y z x' y' z' u o,
    ¬(x = x') -> 
    binarytree (update_edge (update_edge F x y z o) x' y' z' u) ->
    binarytree (update_edge (update_edge F x' y' z' u) x y z o).
  Proof.
    intros F x y z x' y' z' u o H1 H2.
    unfold binarytree in *. intros.
    apply (H2 x0 y0 z0 l r) ; auto.
    + apply update_edge_comm in H0 ; auto.
    + apply update_edge_comm in H3 ; auto.
  Qed.
    
  Lemma update_comm_inv : forall F x y z x' y' z' u o,
      ¬(x = x') ->
      Inv p D (update_edge (update_edge F x y z o) x' y' z' u) V W ->
      Inv p D (update_edge (update_edge F x' y' z' u) x y z o) V W.      
  Proof.
    intros F x y z x' y' z' u o H Inv.
    inversion Inv. unfold is_bst in Inv_bst.
    unpack. constructor. unfold is_bst.
    apply update_comm_confined_inv in H0 ; auto.
    apply update_comm_isroot_inv in H2 ; auto.
    apply update_comm_searchtree_inv in H3 ; auto.
    apply update_comm_binarytree_inv in H4 ; auto.
    repeat (split ; [assumption|]). auto.
  Qed.  
    
  Lemma update_edge_if_no_path_add_memory_inv : forall F x y y' z o x' l,
      path_add_memory (update_edge F x y' z o) x' y (rev l) ->
      ¬(path F x' x) ->
      path_add_memory F x' y (rev l).
  Proof.
    intros F x y y' z o x' l.
    generalize y.
    induction l ; intros.
    + inversion H ; subst.
      - apply path_am_refl.
      - apply app_eq_nil in H1. unpack ; discriminate.
    + inversion H ; subst.
      - symmetry in H5. apply app_eq_nil in H5.
        unpack ; discriminate.
      - symmetry in H1. apply app_eq_unit in H1.
        destruct H1 ; unpack ; try discriminate.
        inversion H2 ; subst. simpl in *.
        rewrite -> H1 in *. simpl in *.
        destruct H5 ; unpack ; subst.
        * apply path_am_single with o0 ; auto.
        * exfalso ; apply H0 ; apply path_refl.
      - apply app_inj_tail in H1. unpack ; subst.
        simpl in *. apply IHl in H6 ; auto.
        destruct H2 ; unpack ; subst.
        * apply path_am_add with o0 ; auto.
        * apply path_add_memory_transitivity with x ; auto.
          apply path_add_memory_implies_path in H6 ; contradiction.
  Qed.  

  Lemma update_edge_if_no_path_inv : forall F x y y' z o x',
      ¬(path F x' x) ->
      path (update_edge F x y' z o) x' y ->
      path F x' y.
  Proof.
    intros F x y y' z o x' Q P.
    apply path_add_equiv_path in P.
    apply path_add_memory_equiv_path_add in P.
    destruct P.
    pose proof (update_edge_if_no_path_add_memory_inv F x y y' z o x' (rev x0)).
    rewrite rev_involutive in H0.
    apply H0 in H ; auto. apply path_add_memory_implies_path in H ; auto.
  Qed.

  Lemma update_edge_unroll_if_no_path_inv : forall F x' y' x y a b c d e f,
      Inv p D F V W ->
      ¬(path F x' x) ->
      ¬(path F x' y) ->
      path (update_edge (update_edge F x a b c) y d e f) x' y' ->
      path (update_edge F x a b c) x' y'.
  Proof.
    intros. 
    apply path_implies_path_add in H2.
    apply path_add_memory_equiv_path_add in H2.
    destruct H2. assert (exists x1, x0 = rev x1).
    exists (rev x0). rewrite rev_involutive ; auto.
    destruct H3. rewrite H3 in H2. clear H3.
    generalize dependent y'. induction x1 ; intros.
    + inversion H2 ; subst.
      - apply path_refl.
      - apply app_eq_nil in H3. unpack ; discriminate.
    + inversion H2 ; subst.
      - symmetry in H7. apply app_eq_nil in H7. unpack ; discriminate.
      - symmetry in H3. apply app_eq_unit in H3. destruct H3 ; unpack ; try discriminate.
        inversion H4 ; subst.
        apply path_single with o. destruct H7 ; unpack ; subst ; auto.
        exfalso ; apply H1 ; apply path_refl.
      - apply app_inj_tail in H3 ; unpack ; subst.
        apply IHx1 in H8. apply path_trans with a0 ; auto.
        apply path_single with o.
        destruct H4 ; unpack ; subst ; auto.
        apply update_edge_if_no_path_inv in H8 ; auto. contradiction.
  Qed.  

  Lemma update_edge_twice_if_no_path_inv : forall F x' y' x y a b c d e f,
      Inv p D F V W ->
      ¬(path F x' x) ->
      ¬(path F x' y) ->
      path (update_edge (update_edge F x a b c) y d e f) x' y' ->
      path F x' y'.
  Proof.
    intros.
    pose proof (update_edge_unroll_if_no_path_inv F x' y' x y a b c d e f H H0 H1 H2).
    pose proof (update_edge_if_no_path_inv F x y' a b c x' H0 H3). auto.
  Qed.  
  
  Lemma update_edge_if_diff_inv : forall (F : EdgeSet) x y o a b c d,
      F x y o ->
      ¬(a = x) ->
      (update_edge F a b c d) x y o.
  Proof.
    intros.
    left. split ; auto.
  Qed.
  
  Lemma remove_direction_edge_inv : forall F p' x z o,
      Inv p D F V W -> 
      F p' x o ->
      path (remove_edge F p' x) p' z ->
      z = p' \/ (exists y, F p' y (invert_orientation o) /\ path F y z).
  Proof.
    intros.
    pose proof (classic (z = p')).
    destruct H2 ; subst.
    + left ; auto.
    + apply path_implies_path_add in H1.
      apply path_add_memory_equiv_path_add in H1.
      destruct H1. assert (exists x1, (rev x1 = x0)).
      exists (rev x0). rewrite rev_involutive.
      auto. destruct H3. rewrite <- H3 in *.
      clear dependent  x0.
      generalize dependent z.
      induction x1 ; intros.
      - inversion H1 ; subst ; auto.
        apply app_eq_nil in H3 ; unpack ; discriminate.
      - inversion H1 ; auto.
        * symmetry in H3.
          apply app_eq_unit in H3 ; destruct H3 ; unpack ; try discriminate.
          inversion H8 ; subst. destruct H7. destruct H4 ; try contradiction.
          destruct (classic (o = o0)) ; subst ; simpl in *.
          { left. exfalso. apply H4. stlink_tac. }
          { right. exists z. apply different_orientation_then_equal_invert in H6.
            subst. rewrite involutive_invert. split ; auto using path_refl. }
        * apply app_inj_tail in H3. unpack ; subst.
          destruct (classic ((a = p'))) ; subst. 
          {
            inversion H. unfold is_bst in Inv_bst.            
            destruct Inv_bst as
                [_ [_ [isroot [[searchleft searchright] [binarytree finite]]]]].
            destruct (classic (o = o0)) ; simpl in * ; subst.
            * destruct H4 ; try contradiction.
              destruct H3 ; try contradiction.
              exfalso. apply H3. stlink_tac.
            * apply different_orientation_then_equal_invert in H3.
              subst. rewrite involutive_invert.
              destruct H4. right. exists z.
              split ; auto using path_refl.
          }
          apply IHx1 in H8 ; auto. destruct H8 ; subst ; auto ; try contradiction.
          destruct H5. right. exists x0. unpack ; split ; auto.
          destruct H4.
          apply path_trans with a ; auto.
          apply path_single with o0. auto.
  Qed.

  Lemma remove_edge_then_path_from_itself_if_inv : forall F x y z o,
    Inv p D F V W -> 
    F x z o ->
    path (remove_edge F x z) y z ->
    y = z.
  Proof.
    intros F x y z o Inv **.
    apply path_implies_path_add_memory in H0.
    destruct H0.
    assert (exists x1, rev x1 = x0).
    exists (rev x0). rewrite rev_involutive.
    auto. destruct H1. rewrite <- H1 in H0.
    clear dependent x0. generalize dependent z.
    induction x1 ; intros.
    + inversion H0 ; subst ; auto.
      apply app_eq_nil in H1. unpack ; discriminate.
    + inversion H0 ; subst ; auto.
      - symmetry in H1. apply app_eq_unit in H1.
        destruct H1 ; unpack ; try discriminate.
        inversion H2. subst. destruct H5.
        assert (x = y). stpath_tac. subst.
        destruct H3 ; contradiction.
      - destruct H2 ; unpack ; try discriminate.
        apply app_inj_tail in H1.
        unpack ; subst.
        assert (a = x). stpath_tac. subst.
        destruct H2 ; contradiction.
  Qed.

  Lemma if_path_then_itself_or_path_if_inv : forall F x y,
    Inv p D F V W ->
    path F x y ->
    x = p \/ x = y \/ (exists t o, F x t o /\ path F t y).
  Proof.
    intros F x y Inv **.
    apply path_implies_path_add_memory in H.
    destruct H.
    assert (exists x1, rev x1 = x0).
    exists (rev x0). rewrite rev_involutive.
    auto. destruct H0. rewrite <- H0 in H.
    clear dependent x0. generalize dependent y.
    induction x1 ; intros.
    + inversion H ; subst.
      - right. left ; auto.
      - apply app_eq_nil in H0. unpack ; discriminate.
    + inversion H ; subst.
      - right. left. auto.
      - symmetry in H0. apply app_eq_unit in H0.
        destruct H0 ; unpack ; try discriminate.
        inversion H1 ; subst.
        right. right. exists y o. split ; auto using path_refl.
      - apply app_inj_tail in H0. unpack ; subst.
        apply IHx1 in H5. destruct H5 ; auto.
        destruct H0 ; subst ; auto.
        * right. right. exists y o. split ; auto using path_refl.
        * do 3destruct H0. right. right.
          exists x0 x2. split ; auto. apply path_trans with a ; auto.
          stpath_tac.
  Qed.

  Lemma child_if_confined_inv : forall F x o,
    Inv p D F V W ->
    F p x o ->
    let D' := (descendants F x) in 
    confined D' (remove_edge_that_are_not_in_D F D').
  Proof.
    intros.
    intros x' y' o' H'. destruct H'.
    unpack. auto.
  Qed.
  
  Lemma child_if_rootisindomain_inv : forall F x,
    Inv p D F V W ->
    let D' := (descendants F x) in 
    rootisindomain x D'.
  Proof.
    intros.
    unfold rootisindomain.
    unfold D'. unfold descendants.
    rewrite in_set_st_eq.
    apply path_refl.
  Qed.
  
  Lemma child_if_isroot_no_parent_inv : forall F x y o u,
    Inv p D F V W ->
    F p x o ->
    let D' := (descendants F x) in 
    y \in D' ->
    ¬ remove_edge_that_are_not_in_D F D' y x u.
  Proof.
    intros.
    intro.
    destruct H2 ; unpack.
    unfold D' in H1.
    rewrite in_set_st_eq in H1.
    assert (y = p). stpath_tac. subst.
    rewrite in_set_st_eq in H2.
    stpath_tac.
  Qed.
    
  Lemma child_if_isroot_path_to_all_inv : forall F x y o,
    Inv p D F V W ->
    F p x o ->
    let D' := (descendants F x) in 
    y \in D' ->
    path (remove_edge_that_are_not_in_D F D') x y.
  Proof.
    intros.
    unfold D' in *.
    pose proof (H1) as H1'.
    rewrite in_set_st_eq in H1.
    apply path_implies_path_add_memory in H1.
    destruct H1.
    assert (exists x1, rev x1 = x0).
    exists (rev x0). rewrite rev_involutive.
    auto. destruct H2. rewrite <- H2 in H1.
    clear dependent x0. generalize dependent y.
    induction x1 ; intros.
    + inversion H1 ; subst.
      - apply path_refl.
      - apply app_eq_nil in H2. unpack ; discriminate.
    + inversion H1 ; subst.
      - symmetry in H6. apply app_eq_nil in H6. unpack ; discriminate.
      - symmetry in H2. apply app_eq_unit in H2. destruct H2 ; unpack ; try discriminate. 
        inversion H3. subst. apply path_single with o0.
        repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      - apply app_inj_tail in H2. unpack ; subst.
        assert ( a \in D' ). apply path_add_memory_implies_path in H7 ;
        rewrite in_set_st_eq ; auto. apply IHx1 in H7 ; auto.
        apply path_trans with a ; auto. apply path_single with o0.
        repeat split ; auto ; rewrite in_set_st_eq ; auto.
  Qed.
  
  Lemma child_if_isroot_inv : forall F x o,
    Inv p D F V W ->
    F p x o ->
    let D' := (descendants F x) in 
    isroot D' (remove_edge_that_are_not_in_D F D') x.
  Proof.
    intros.
    unfold  isroot.
    intros.
    unfold D'. 
    split.
    + apply (child_if_isroot_no_parent_inv F x x0 o o0) ; auto.
    + apply (child_if_isroot_path_to_all_inv) with o ; auto.
  Qed.
  
  Lemma child_if_searchtree_inv : forall F x o,
    Inv p D F V W ->
    F p x o ->
    let D' := (descendants F x) in
    searchtree (remove_edge_that_are_not_in_D F D') V.
  Proof.
    intros.
    split ; intros ; unpack ;
      apply path_remove_domain in H2 ; destruct H1 ; unpack ;
        split ; stlink_tac ; stpath_tac.
  Qed.
  
  Lemma child_if_binarytree_inv : forall F x o,
    Inv p D F V W ->
    F p x o ->
    let D' := (descendants F x) in 
    binarytree (remove_edge_that_are_not_in_D F D').
  Proof.
    intros.
    unfold binarytree.
    intros.
    intro ; subst.
    destruct H2, H3 ; unpack.
    assert (y = z). stlink_tac. subst.
    contradiction.
  Qed.
             
  Theorem child_if_inv : forall F x o,
    Inv p D F V W ->
    F p x o ->
    let D' := (descendants F x) in 
    Inv x D' (remove_edge_that_are_not_in_D F D') V W.
  Proof.
    intros F x o Inv E.
    constructor. unfold is_bst.
    split ; auto.
    (* confined *)
    apply (child_if_confined_inv F x o) ; auto.
    split ; auto.
    (*rootisindomain*)
    apply (child_if_rootisindomain_inv F x) ; auto.
    split ; auto.
    (*isroot*)
    apply (child_if_isroot_inv F x o) ; auto.
    split ; auto.
    (*searchtree*)
    apply child_if_searchtree_inv with o ; auto.
    split ; auto.
    (*binarytree*)
    apply child_if_binarytree_inv with o ; auto.
    split ;
      [|inversion Inv ; unfold is_bst in * ; unpack ; auto].
    assert (x \in D) as xindomain. stdomain_tac.
    pose proof (descendants_finite_if_bst p D V W F x Inv xindomain).
    auto.
  Qed.
    
  Lemma element_is_tree_confined_inv : forall F x,
    Inv p D F V W ->
    x \in D ->
    let D' := (descendants F x) in 
    confined D' (remove_edge_that_are_not_in_D F D').
  Proof.
    intros.
    intros x' y' o' H'. destruct H'.
    unpack. auto.
  Qed.
  
  Lemma join_confined_inv : forall F F' x z o,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W -> 
    confined D (add_edge (union_edge F' FC') p z o).
  Proof.
    intros F F' x z o Inv **.
    intros x' y' o' H'.
    destruct H' ; unpack ; subst.
    inversion Inv. unfold is_bst in Inv_bst.
        destruct Inv_bst as
            [confined [rootisindomain [isroot [[searchleft searchright] [binarytree
            [finite positive]]]]]].
    + destruct H1 ; unpack ; subst.
      - pose proof (subdomain_of_edgeset_in_domain F x o Inv H).
        split.
        * rew_set in *. apply H2. stdomain_tac.
        * rew_set in *. apply H2. stdomain_tac.
      - unfold FC' in H. destruct H1.
        split ; stdomain_tac.
    + split ; stdomain_tac.
      pose proof (subdomain_of_edgeset_in_domain F x o Inv H).
      rew_set in *. apply H1. 
      stdomain_tac.
  Qed.
  
  Lemma join_rootisindomain_inv : forall F F' x z o,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W -> 
    rootisindomain p D.
  Proof.
    intros. unfold rootisindomain.
    stdomain_tac.
  Qed.

  Lemma join_isroot_no_parent_inv : forall F F' x z x' o' o,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W -> 
    x' \in D ->
    ¬ add_edge (union_edge F' FC') p z o x' p o'.
  Proof.
    intros.
    intro. destruct H3 ; unpack ; subst.
    + destruct H3 ; unpack ; subst.
      - assert (¬(p \in D')).
        intro. unfold D' in H4. 
        rewrite in_set_st_eq in H4.
        stpath_tac.
        assert (p \in D').
        stdomain_tac. contradiction.
      - destruct H3 ; unpack. stlink_tac.
    + assert (z \in D'). stdomain_tac.
      rewrite in_set_st_eq in H3.
      assert (x = z). stpath_tac. subst.
      stlink_tac.
  Qed.

  Lemma join_isroot_path_to_all_inv : forall F F' x z x' o,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W -> 
    x' \in D ->
    path (add_edge (union_edge F' FC') p z o) p x'.
  Proof.
    intros F F' x z x' o Inv **.
    inversion Inv. unfold is_bst in Inv_bst.
        destruct Inv_bst as
            [confined [rootisindomain [isroot [[searchleft searchright] [binarytree
            [finite positive]]]]]].        
    pose proof (classic (x' \in D')).
    destruct H2.
    + apply path_trans with z ; auto.
      - apply path_single with o.
        right. auto.
      - apply add_edge_inv.
        apply union_edge_inv_l.
        stpath_tac.
    + unfold is_bst in *.
      unpack. specialize (isroot x' LEFT H1).
      unpack. 
      apply add_edge_inv.
      apply union_edge_comm_inv.
      apply union_edge_inv_l.
      unfold FC'.
      apply path_implies_path_add_memory in H4.
      destruct H4.
      assert (exists x1, rev x1 = x0).
      exists (rev x0). rewrite rev_involutive.
      auto. destruct H5. rewrite <- H5 in *.
      clear dependent x0. generalize dependent x'.
      induction x1 ; intros.
      - inversion H4 ; subst.
        * apply path_refl.
        * apply app_eq_nil in H5. unpack ; discriminate.
      - inversion H4 ; subst.
        * apply symmetry in H9.
          apply app_eq_nil in H9. unpack ; discriminate.
        * apply symmetry in H5.
          apply app_eq_unit in H5.
          destruct H5 ; unpack ; try discriminate.
          inversion H6 ; subst.
          destruct o.
          { apply path_single with o0.
            repeat split ; auto. intro.
            rewrite in_set_st_eq in H7. stpath_tac.
          }
          {
            apply path_single with o0.
            repeat split ; auto. intro.
            rewrite in_set_st_eq in H7. stpath_tac.
          }
        * apply app_inj_tail in H5.
          unpack ; subst.
          assert (¬(a \in D')).
          intro. assert (x' \in D').
          pose proof (if_node_in_domain_and_edge_then_end_also_in_domain_if_bst).
          specialize (H7 p D V W F a x o0 x' Inv). auto.
          contradiction.
          apply IHx1 in H10 ; auto ; stdomain_tac ; [|intro ; stlink_tac].
          apply path_trans with a ; auto.
          apply path_single with o0.
          repeat split ; auto. 
  Qed.
  
  Lemma join_isroot_inv : forall F F' x z o,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W -> 
    isroot D (add_edge (union_edge F' FC') p z o) p.
  Proof.
    intros.
    intros x' o' H'.
    split.
    + apply join_isroot_no_parent_inv ; auto.
    + apply join_isroot_path_to_all_inv ; auto.
  Qed.

  Lemma join_searchtree_left_case_1_inv : forall F F' x z o x0 z0,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W ->
    x ≠ p ->
    disjointed_edge_set F' FC' ->
    add_edge (union_edge F' FC') p z o x0 x LEFT ->
    path F' x z0 ∨ path FC' x z0 -> 
    V x0 > V x ∧ V x0 > V z0.
  Proof.
    intros.
    destruct H4 ; unpack ; subst.
    + destruct H5.
      - destruct H4.
        * split ; stpath_tac ; stlink_tac.
        * do 3destruct H4.
          rewrite in_set_st_eq in H7. exfalso ; apply H7.
          stpath_tac.
      - destruct H4.
        * pose proof (if_no_edge_then_path_to_itself FC' x z0 H5).
          assert (¬ (∃ (y : elem) (o : orientation), FC' x y o)).
          intro. do 2destruct H7.
          specialize (H3 x0 x LEFT x x1 x2 H4 H7).
          unpack ; contradiction.
          apply H6 in H7 ; subst. split ; stlink_tac.
        * assert ((∀ (x0 y0 : elem) (o : orientation), FC' x0 y0 o → F x0 y0 o)).
          intros. destruct H6 ; auto. 
          apply (path_edgeset_incl FC' F) with x z0 in H6 ; auto.
          destruct H4 ; unpack.
          split ; stlink_tac ; stpath_tac.
    + destruct H5.
      - assert (z0 \in D'). stdomain_tac.
        rewrite in_set_st_eq in H5.
        split ; stlink_tac ; stpath_tac.
      - pose proof (if_no_edge_then_path_to_itself FC' z z0 H4).
        assert (¬ (∃ (y : elem) (o : orientation), FC' z y o)).
        * intro. do 4destruct H6.
          apply H6. rewrite in_set_st_eq. stpath_tac.
        * apply H5 in H6. subst. split ; stlink_tac.
  Qed.

  Lemma join_searchtree_left_case_2_inv : forall F F' x z o x0 z0,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W ->
    p ≠ x ->
    disjointed_edge_set F' FC' ->
    add_edge (union_edge F' FC') p z o x0 p LEFT ->
    path F' p z0 ∨ path FC' p z0-> 
    V x0 > V p ∧ V x0 > V z0.
  Proof.
    intros.
    destruct H4 ; unpack ; subst.
    + destruct H5.
      - destruct H4.
        * split ; stpath_tac ; stlink_tac.
        * do 3destruct H4. stlink_tac.
      - destruct H4.
        * assert (p \in D'). stdomain_tac.
          rewrite in_set_st_eq in H6. stpath_tac.
        * do 2destruct H4. stlink_tac.
    + assert (z \in D'). stdomain_tac.
      destruct H5 ; rewrite in_set_st_eq in H4 ; stpath_tac.
  Qed.
  
  Lemma join_searchtree_left_case_3_inv : forall F F' x y z o x0 z0,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W ->
    y ≠ x ->
    y ≠ p ->
    disjointed_edge_set F' FC' ->
    add_edge (union_edge F' FC') p z o x0 y LEFT ->
    path F' y z0 ∨ path FC' y z0-> 
    V x0 > V y ∧ V x0 > V z0.
  Proof.
    intros.
    assert ((∀ (x0 y0 : elem) (o : orientation), FC' x0 y0 o → F x0 y0 o)).
    intros. destruct H7 ; auto. 
    destruct H5 ; unpack ; subst.
    + destruct H5.
      - destruct H6.
        * split ; stlink_tac ; stpath_tac.
        * assert (y = z0).
          pose proof (if_no_edge_then_path_to_itself FC' y z0).
          apply H8 ; auto. intro. do 2destruct H9.
          specialize (H4 x0 y LEFT y x1 x2 H5 H9). unpack ; contradiction.
          subst. split ; stlink_tac.
      - destruct H5. unpack.
        destruct H6 ; split ; stlink_tac ; stpath_tac.
        * pose proof (if_path_then_refl_or_in_domain_if_bst z D' V W F' y z0 H1 H6).
          destruct H10 ; subst.
          { stlink_tac. }
          { contradiction. }
        * apply (path_edgeset_incl FC' F) with y z0 in H6 ; auto.
          stpath_tac.
    + assert (z \in D'). stdomain_tac.
      rewrite in_set_st_eq in H5.
      destruct H6.
      - assert (z0 \in D'). stdomain_tac.
        rewrite in_set_st_eq in H8.
        split ; stpath_tac.
      - apply (path_edgeset_incl FC' F) with z z0 in H6 ; auto.
        assert (path F x z0). apply path_trans with z ; auto.
        split ; stpath_tac.
  Qed.
        
  Lemma join_searchtree_left_inv : forall F F' x z o x0 y z0,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W ->
    add_edge (union_edge F' FC') p z o x0 y LEFT ->
    path (add_edge (union_edge F' FC') p z o) y z0 ->
    V x0 > V y ∧ V x0 > V z0.
  Proof.
    intros F F' x z o x0 y z0 Inv **.
    inversion Inv. unfold is_bst in Inv_bst.
        destruct Inv_bst as
            [confined [rootisindomain [isroot [[searchleft searchright] [binarytree
            [finite positive]]]]]].        
    assert (disjointed_edge_set F' FC').
    unfold disjointed_edge_set. intros.
    destruct H4 ; unpack.
    assert (x1 \in D'). stdomain_tac.
    assert (y0 \in D'). stdomain_tac.
    repeat split ; intro ; subst ; contradiction.
    apply add_edge_if_no_path_inv in H2.
    + apply union_edge_disjointed_inv in H2 ; auto.
      destruct (bool_decide (y = x)) eqn:YX ;
      destruct (bool_decide (y = p)) eqn:YP ;
      try apply bool_decide_eq_true in YX ; 
      try apply bool_decide_eq_true in YP ;
      try apply bool_decide_eq_false in YX ;
      try apply bool_decide_eq_false in YP ; unpack ; subst.
      - stlink_tac.
      - apply (join_searchtree_left_case_1_inv F F' x z o x0 z0) ; auto.
      - apply (join_searchtree_left_case_2_inv F F' x z o x0 z0) ; auto.
      - apply (join_searchtree_left_case_3_inv F F' x y z o x0 z0) ; auto.
    + intro.
      apply union_edge_end_inv in H4.
      destruct H4 ; subst.
      do 3destruct H4.
      { assert (p \in D'). stdomain_tac. rewrite in_set_st_eq in H5. stpath_tac. }
      { destruct H4 ; unpack. stlink_tac. }
      { destruct H1 ; unpack ; subst.
        + destruct H1.
        - assert (p \in D'). stdomain_tac. rewrite in_set_st_eq in H4. stpath_tac.
        - destruct H1. unpack. stlink_tac.
          + assert (z \in D'). stdomain_tac.
            rewrite in_set_st_eq in H1. stpath_tac.
      }
  Qed.
  
  Lemma join_searchtree_right_case_1_inv : forall F F' x z o x0 z0,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W ->
    x ≠ p ->
    disjointed_edge_set F' FC' ->
    add_edge (union_edge F' FC') p z o x0 x RIGHT ->
    path F' x z0 ∨ path FC' x z0 -> 
    V x0 < V x ∧ V x0 < V z0.
  Proof.
    intros.
    destruct H4 ; unpack ; subst.
    + destruct H5.
      - destruct H4.
        * split ; stpath_tac ; stlink_tac.
        * do 3destruct H4.
          rewrite in_set_st_eq in H7. exfalso ; apply H7.
          stpath_tac.
      - destruct H4.
        * pose proof (if_no_edge_then_path_to_itself FC' x z0 H5).
          assert (¬ (∃ (y : elem) (o : orientation), FC' x y o)).
          intro. do 2destruct H7.
          specialize (H3 x0 x RIGHT x x1 x2 H4 H7).
          unpack ; contradiction.
          apply H6 in H7 ; subst. split ; stlink_tac.
        * assert ((∀ (x0 y0 : elem) (o : orientation), FC' x0 y0 o → F x0 y0 o)).
          intros. destruct H6 ; auto. 
          apply (path_edgeset_incl FC' F) with x z0 in H6 ; auto.
          destruct H4 ; unpack.
          split ; stlink_tac ; stpath_tac.
    + destruct H5.
      - assert (z0 \in D'). stdomain_tac.
        rewrite in_set_st_eq in H5.
        split ; stlink_tac ; stpath_tac.
      - pose proof (if_no_edge_then_path_to_itself FC' z z0 H4).
        assert (¬ (∃ (y : elem) (o : orientation), FC' z y o)).
        * intro. do 4destruct H6.
          apply H6. rewrite in_set_st_eq. stpath_tac.
        * apply H5 in H6. subst. split ; stlink_tac.
  Qed.

  Lemma join_searchtree_right_case_2_inv : forall F F' x z o x0 z0,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W ->
    p ≠ x ->
    disjointed_edge_set F' FC' ->
    add_edge (union_edge F' FC') p z o x0 p RIGHT ->
    path F' p z0 ∨ path FC' p z0-> 
    V x0 < V p ∧ V x0 < V z0.
  Proof.
    intros.
    destruct H4 ; unpack ; subst.
    + destruct H5.
      - destruct H4.
        * split ; stpath_tac ; stlink_tac.
        * do 3destruct H4. stlink_tac.
      - destruct H4.
        * assert (p \in D'). stdomain_tac.
          rewrite in_set_st_eq in H6. stpath_tac.
        * do 2destruct H4. stlink_tac.
    + assert (z \in D'). stdomain_tac.
      destruct H5 ; rewrite in_set_st_eq in H4 ; stpath_tac.
  Qed.
  
  Lemma join_searchtree_right_case_3_inv : forall F F' x y z o x0 z0,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W ->
    y ≠ x ->
    y ≠ p ->
    disjointed_edge_set F' FC' ->
    add_edge (union_edge F' FC') p z o x0 y RIGHT ->
    path F' y z0 ∨ path FC' y z0-> 
    V x0 < V y ∧ V x0 < V z0.
  Proof.
    intros.
    assert ((∀ (x0 y0 : elem) (o : orientation), FC' x0 y0 o → F x0 y0 o)).
    intros. destruct H7 ; auto. 
    destruct H5 ; unpack ; subst.
    + destruct H5.
      - destruct H6.
        * split ; stlink_tac ; stpath_tac.
        * assert (y = z0).
          pose proof (if_no_edge_then_path_to_itself FC' y z0).
          apply H8 ; auto. intro. do 2destruct H9.
          specialize (H4 x0 y RIGHT y x1 x2 H5 H9). unpack ; contradiction.
          subst. split ; stlink_tac.
      - destruct H5. unpack.
        destruct H6 ; split ; stlink_tac ; stpath_tac.
        * pose proof (if_path_then_refl_or_in_domain_if_bst z D' V W F' y z0 H1 H6).
          destruct H10 ; subst.
          { stlink_tac. }
          { contradiction. }
        * apply (path_edgeset_incl FC' F) with y z0 in H6 ; auto.
          stpath_tac.
    + assert (z \in D'). stdomain_tac.
      rewrite in_set_st_eq in H5.
      destruct H6.
      - assert (z0 \in D'). stdomain_tac.
        rewrite in_set_st_eq in H8.
        split ; stpath_tac.
      - apply (path_edgeset_incl FC' F) with z z0 in H6 ; auto.
        assert (path F x z0). apply path_trans with z ; auto.
        split ; stpath_tac.
  Qed.
        
  Lemma join_searchtree_right_inv : forall F F' x z o x0 y z0,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W ->
    add_edge (union_edge F' FC') p z o x0 y RIGHT ->
    path (add_edge (union_edge F' FC') p z o) y z0 ->
    V x0 < V y ∧ V x0 < V z0.
  Proof.
    intros F F' x z o x0 y z0 Inv **.
    inversion Inv. unfold is_bst in Inv_bst.
        destruct Inv_bst as
            [confined [rootisindomain [isroot [[searchleft searchright] [binarytree
            [finite positive]]]]]].        
    assert (disjointed_edge_set F' FC').
    unfold disjointed_edge_set. intros.
    destruct H4 ; unpack.
    assert (x1 \in D'). stdomain_tac.
    assert (y0 \in D'). stdomain_tac.
    repeat split ; intro ; subst ; contradiction.
    apply add_edge_if_no_path_inv in H2.
    + apply union_edge_disjointed_inv in H2 ; auto.
      destruct (bool_decide (y = x)) eqn:YX ;
      destruct (bool_decide (y = p)) eqn:YP ;
      try apply bool_decide_eq_true in YX ; 
      try apply bool_decide_eq_true in YP ;
      try apply bool_decide_eq_false in YX ;
      try apply bool_decide_eq_false in YP ; unpack ; subst.
      - stlink_tac.
      - apply (join_searchtree_right_case_1_inv F F' x z o x0 z0) ; auto.
      - apply (join_searchtree_right_case_2_inv F F' x z o x0 z0) ; auto.
      - apply (join_searchtree_right_case_3_inv F F' x y z o x0 z0) ; auto.
    + intro.
      apply union_edge_end_inv in H4.
      destruct H4 ; subst.
      do 3destruct H4.
      { assert (p \in D'). stdomain_tac. rewrite in_set_st_eq in H5. stpath_tac. }
      { destruct H4 ; unpack. stlink_tac. }
      { destruct H1 ; unpack ; subst.
        + destruct H1.
        - assert (p \in D'). stdomain_tac. rewrite in_set_st_eq in H4. stpath_tac.
        - destruct H1. unpack. stlink_tac.
          + assert (z \in D'). stdomain_tac.
            rewrite in_set_st_eq in H1. stpath_tac.
      }
  Qed.
  
  Lemma join_searchtree_inv : forall F F' x z o,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W ->
    searchtree (add_edge (union_edge F' FC') p z o) V.
  Proof.
    intros.
    split ; intros ; unpack.
    + apply (join_searchtree_left_inv F F' x z o) ; auto.
    + apply (join_searchtree_right_inv F F' x z o) ; auto.
  Qed.
    
  Lemma join_binarytree_inv : forall F F' x z o,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W -> 
    binarytree (add_edge (union_edge F' FC') p z o).
  Proof.
    intros.
    unfold binarytree. intros.
    inversion H.
    inversion H1.
    unfold is_bst in *. unpack.    
    destruct H3, H4 ; unpack ; subst ; try contradiction.
    + destruct H3, H4.
      - specialize (H9 x0 y z0 l r H2 H3 H4).
        auto.
      - unfold FC' in H4. unfold remove_edge_that_are_in_D in H4.
        unpack. apply H5 in H3 ; unpack. contradiction.
      - unfold FC' in H3. unfold remove_edge_that_are_in_D in H3.
        unpack. apply H5 in H4 ; unpack. contradiction.
      - unfold FC' in *. unfold remove_edge_that_are_in_D in *.
        unpack.
        specialize (H16 x0 y z0 l r). auto.
    + destruct H3.
      - apply H5 in H3. unpack.
        rewrite in_set_st_eq in H3.
        stpath_tac.
      - unfold FC' in H3. destruct H3 ; unpack.
        intro ; subst. assert (x = y). stlink_tac.
        subst y. apply H19. rewrite in_set_st_eq.
        stpath_tac.
    + intro. subst.
      destruct H4.
      - apply H5 in H3. unpack.
        rewrite in_set_st_eq in H3.
        stpath_tac.
      - unfold FC' in H3. destruct H3 ; unpack.
        assert (x = z0). stlink_tac.
        subst z0. apply H19. rewrite in_set_st_eq.
        stpath_tac.
  Qed.
         
  Theorem join_if_inv : forall F F' x z o,
    Inv p D F V W ->
    F p x o -> 
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W -> 
    Inv p D (add_edge (union_edge F' FC') p z o) V W.
  Proof.
    intros F F' x z o Inv **.
    constructor. unfold is_bst.
    split ; auto.
    (* confined *)
    apply (join_confined_inv F) ; auto.
    split ; auto.
    (* rootisindomain *)
    apply (join_rootisindomain_inv F F' x z o) ; auto.
    split ; auto.
    (* isroot *)
    apply (join_isroot_inv F F' x z) ; auto.
    split ; auto.
    apply (join_searchtree_inv F F' x z) ; auto.
    (* binarytree *)
    split ; auto.
    apply (join_binarytree_inv F F' x z) ; auto.
    split ; inversion Inv ; unfold is_bst in * ; unpack ; auto.
  Qed.

  Lemma path_delete_edges_from_D_if_inv : forall F x y,
      Inv p D F V W -> 
      path (remove_edge_that_are_not_in_D F D) x y <->
      path F x y.
  Proof.
    intros.
    split ; intro.
    + apply path_implies_path_add_memory in H0.
      destruct H0. generalize dependent y.
      assert (exists l', rev l' = x0).
      exists (rev x0). rewrite rev_involutive. auto.
      destruct H0. rewrite <- H0. clear dependent x0.
      rename x1 into x0.
      induction x0 ; intros.
      - inversion H0 ; subst ; stpath_tac.
        apply app_eq_nil in H1 ; unpack ; discriminate.
      - inversion H0 ; subst ; stpath_tac.
        * symmetry in H1. apply app_eq_unit in H1 ; destruct H1 ; unpack ; try discriminate.
          inversion H2 ; subst.
          destruct H5 ; unpack. stpath_tac.
        * apply app_inj_tail in H1 ; unpack ; subst.
          destruct H2 ; unpack. apply IHx0 in H6. stpath_tac.
    + induction H0 ; stpath_tac.
      - apply path_single with o. repeat split ; stdomain_tac ; auto.
      - specialize (IHpath1 H).
        specialize (IHpath2 H). stpath_tac.
  Qed.
  
  Theorem same_remove_edge_if_inv : forall F,
      Inv p D F V W ->
      Inv p D (remove_edge_that_are_not_in_D F D) V W.
  Proof.
    intros.
    split ; intros.
    inversion H. unfold is_bst in Inv_bst.
    destruct Inv_bst as
    [confined [rootisindomain [isroot [[searchleft searchright] [binarytree [finite maximum]]]]]].
    constructor. unfold STpredicate.confined.
    intros. destruct H0 ; unpack ; auto.
    split ; auto. 
    split ; auto.
    split ; [intro ; destruct H1 ; unpack ; stlink_tac|apply path_delete_edges_from_D_if_inv ; stpath_tac ; auto].
    split. split.
    - intros ; unpack ; destruct H0 ; unpack.
      pose proof (path_delete_edges_from_D_if_inv F y z H).
      apply H4 in H1. split ; stpath_tac ; stlink_tac.
    - intros ; unpack ; destruct H0 ; unpack.
      pose proof (path_delete_edges_from_D_if_inv F y z H).
      apply H4 in H1. split ; stpath_tac ; stlink_tac.
    - split.
      + unfold STpredicate.binarytree.
        intros. destruct H1, H2 ; unpack.
        specialize (binarytree x y z l r). auto.
      + repeat split ; auto.
  Qed.
  
  Lemma same_descendants_edge_if_inv : forall F,
      Inv p D F V W ->
      Inv p (descendants F p) (remove_edge_that_are_not_in_D F (descendants F p)) V W.
  Proof.
    intros.
    pose proof (set_ext_eq).
    specialize (H0 elem D (descendants F p)).
    assert ((∀ x : elem, x \in D ↔ x \in descendants F p)).
    intros. split ; intros.
    - rewrite in_set_st_eq. stpath_tac.
    - rewrite in_set_st_eq in H1. stdomain_tac.
    - rewrite <- H0 in H1. rewrite <- H1.
      apply same_remove_edge_if_inv ; auto.
  Qed.
  
  Lemma on_path_descendants_edge_if_inv : forall F x,
      Inv p (descendants F p) (remove_edge_that_are_not_in_D F (descendants F p)) V W ->
      path F p x -> 
      Inv x (descendants F x) (remove_edge_that_are_not_in_D F (descendants F x)) V W.
  Proof.
    intros.
    induction H0 ; auto.
    constructor. unfold is_bst.
    split ; auto.
    unfold confined. intros.
    destruct H1 ; unpack.
    rewrite in_set_st_eq in H1.
    rewrite in_set_st_eq in H2.
    split ; rewrite in_set_st_eq ; auto.
    (* confined *)
    split ; auto.
    (* rootisindomain *)
    unfold rootisindomain. rewrite in_set_st_eq. stpath_tac.
    (* isroot *)
    split ; auto.
    unfold isroot ; intros. split.
    - intro.
      destruct H2 ; unpack.
      rewrite in_set_st_eq in H2.
      assert (remove_edge_that_are_not_in_D F (descendants F x) x0 y o0).
      repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
      assert (path (remove_edge_that_are_not_in_D F (descendants F x)) y x0).
      pose proof (if_path_on_edge_set_then_path_on_descendant F y x0 H2).
      pose proof (path_domain_inclusion F (descendants F y) (descendants F x) x0 y).
      apply H7 ; auto. rewrite incl_in_eq. intros. rewrite in_set_st_eq.
      rewrite in_set_st_eq in H8. stpath_tac.
      assert (x0 = y). stpath_tac. subst. stlink_tac.
    - apply if_path_on_edge_set_then_path_on_descendant.
      rewrite in_set_st_eq in H1. auto.
    - split ; auto.
      * split ; intros.
        + unpack. assert (path (remove_edge_that_are_not_in_D F (descendants F x)) y0 z).
          pose proof (path_domain_inclusion F (descendants F y) (descendants F x) z y0).
          apply H3 ; auto. rewrite incl_in_eq. intros.
          rewrite in_set_st_eq in H4. rewrite in_set_st_eq. stpath_tac.
          assert ((remove_edge_that_are_not_in_D F (descendants F x)) x0 y0 LEFT).
          destruct H1 ; unpack. rewrite in_set_st_eq in H1.
          rewrite in_set_st_eq in H4.
          repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
          split ; stpath_tac ; stlink_tac.
        + unpack. assert (path (remove_edge_that_are_not_in_D F (descendants F x)) y0 z).
          pose proof (path_domain_inclusion F (descendants F y) (descendants F x) z y0).
          apply H3 ; auto. rewrite incl_in_eq. intros.
          rewrite in_set_st_eq in H4. rewrite in_set_st_eq. stpath_tac.
          assert ((remove_edge_that_are_not_in_D F (descendants F x)) x0 y0 RIGHT).
          destruct H1 ; unpack. rewrite in_set_st_eq in H1.
          rewrite in_set_st_eq in H4.
          repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
          split ; stpath_tac ; stlink_tac.
      * split ; intros.
        { unfold binarytree. intros.
          assert ((remove_edge_that_are_not_in_D F (descendants F x)) x0 y0 l).
          destruct H2 ; unpack. rewrite in_set_st_eq in H2.
          rewrite in_set_st_eq in H4.
          destruct H3 ; unpack. rewrite in_set_st_eq in H3.
          rewrite in_set_st_eq in H6.
          repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
          assert ((remove_edge_that_are_not_in_D F (descendants F x)) x0 z r).
          destruct H2 ; unpack. rewrite in_set_st_eq in H2.
          rewrite in_set_st_eq in H5.
          destruct H3 ; unpack. rewrite in_set_st_eq in H3.
          rewrite in_set_st_eq in H7.
          repeat split ; auto ; rewrite in_set_st_eq ; stpath_tac.
          inversion H.
          unfold is_bst in Inv_bst. unpack.
          specialize (H10 x0 y0 z). apply H10 ; auto.
        }
        repeat split.
        + pose proof (descendants_of_descendants_finite_if_bst F x y o).
          apply H1 ; auto.
          inversion H. unfold is_bst in * ; unpack ; auto.
        + inversion H. unfold is_bst in * ; unpack ; auto.
  Qed.

End EdgeSetSplayTree.
