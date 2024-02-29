From ST Require Import STorientation STpredicate STlink STpath STdomain.

From TLC Require Import LibTactics LibInt LibSet.
From iris_time.heap_lang Require Import proofmode.
From stdpp Require Import gmap.

Notation elem := loc.

Section ValueOperations.

  Definition update_value (V : elem -> Z) (x : elem) v (e : elem) :=
    if (bool_decide (e = x)) then
      v
    else
      V e.

  Definition update_function_constant (V : elem -> Z) (c : Z) (e : elem) :=
    (V e + c)%Z.

End ValueOperations.


Section ValueSplayTree.

  Variable p : elem.
  Variable D : LibSet.set elem. (* domain *)
  Variable V : elem -> Z. (* data stored in nodes *)
  Variable W : elem -> Z. (* weight nodes *)
  Variable M : gmap elem content. (* view of the memory *)

  (*   

                    p
                  /  \  
                 ~ EMPTY
                /
               x

   V p >= V x if there is no right 
   child
  
   *)
  
  Lemma if_no_right_branch_then_maximum_if_bst : forall F,
      Inv p D F V W ->
      ¬(exists y, F p y RIGHT) ->
      (forall x, x \in D -> (V p >= V x)%Z).
  Proof.
    intros F Inv H1 x xindomain.     
    inversion Inv. unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    specialize (isroot x LEFT). 
    apply isroot in xindomain as [NExpl Ppx].
    apply three_option_path_x_y in Ppx as opt3.
    destruct opt3 as [opt1| [opt2|opt3] ] ; subst ; try lia.
    + destruct opt2 as [t [Fpt _]].
      exfalso ; apply H1. eauto.
    + destruct opt3 as [t FP].
      apply searchleft in FP. 
      lia.
  Qed.
  
  (*
    
    If p has value pv,

                   p
                 /  \
                x   y
               /     \       
              ~      ~
             /        \
           t1         t2


    we can change pv to v, if
    v > v(t1) and V(t2) > v.

   *)
  
  Lemma update_root_between_if_bst : forall F v,
      Inv p D F V W ->
      (forall x t, (F p x RIGHT /\ path F x t -> (v < V t))%Z) ->
      (forall x t, (F p x LEFT  /\ path F x t -> (V t < v))%Z) ->
      Inv p D F (update_value V p v) W.
  Proof.
    intros F v Inv E1 E2. inversion Inv.
    unfold is_bst in Inv_bst.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    constructor. unfold is_bst.
    unfold update_value.
    repeat (split ; auto) ;
      destruct (bool_decide (x = p)) eqn:XP ;
      try (apply bool_decide_eq_true in XP) ;
      try (apply bool_decide_eq_false in XP).
    - destruct (bool_decide (y = p)) eqn:YP ;
        try (apply bool_decide_eq_true in YP) ;
        try (apply bool_decide_eq_false in YP) ; destruct H as [Fpyl Pyz] ; subst ; stlink_tac.
        assert (F p y LEFT /\ path F y y). split ; auto using path_refl.
        apply E2 in H. lia.
    - destruct (bool_decide (y = p)) eqn:YP ;
        try (apply bool_decide_eq_true in YP) ;
        try (apply bool_decide_eq_false in YP) ; subst ; unpack ; stlink_tac.
    - destruct (bool_decide (z = p)) eqn:ZP ;
        try (apply bool_decide_eq_true in ZP) ;
        try (apply bool_decide_eq_false in ZP) ; subst ; destruct H as [Fpyl Pyz] ; stpath_tac.
        assert (F p y LEFT /\ path F y z). split ; auto.
        apply E2 in H. lia.
    - destruct (bool_decide (z = p)) eqn:ZP ;
        try (apply bool_decide_eq_true in ZP) ;
        try (apply bool_decide_eq_false in ZP) ; subst ; unpack.
      + assert (x \in D) as xindomain. stdomain_tac.
        specialize (isroot x RIGHT xindomain). unpack.
        apply (path_single) in H.
        apply (path_trans F x y p H) in H0.
        assert (p = x) as XP'. stpath_tac. subst. contradiction.
      + assert (F x y LEFT /\ path F y z) as FPxzl. split ; auto.
        apply searchleft in FPxzl. lia.
    - destruct (bool_decide (y = p)) eqn:ZP ;
        try (apply bool_decide_eq_true in ZP) ;
        try (apply bool_decide_eq_false in ZP) ; subst ; stlink_tac.
      + destruct H ; stlink_tac.
      + apply E1 with y. unpack ; split ; auto using path_refl.
    - destruct (bool_decide (y = p)) eqn:YP ;
        try (apply bool_decide_eq_true in YP) ;
        try (apply bool_decide_eq_false in YP) ; subst ; unpack.
      + assert (x \in D) as xindomain. stdomain_tac.
        specialize (isroot x RIGHT xindomain). unpack ; contradiction.
      + stlink_tac. 
    - destruct (bool_decide (z = p)) eqn:ZP ;
        try (apply bool_decide_eq_true in ZP) ;
        try (apply bool_decide_eq_false in ZP) ; subst ; unpack.
      + assert (y = p). stpath_tac.  subst. stlink_tac.
      + assert (F p y RIGHT /\ path F y z) as FPpzr. split ; auto.
        apply E1 in FPpzr. lia.
    - destruct (bool_decide (z = p)) eqn:ZP ;
        try (apply bool_decide_eq_true in ZP) ;
        try (apply bool_decide_eq_false in ZP) ; subst ; unpack.
      + assert (y = p) as YP. stpath_tac. subst. stlink_tac.
      + assert (F x y RIGHT /\ path F y z) as FPxzr. split ; auto.
        apply searchright in FPxzr. lia.
  Qed.        

  Lemma update_value_with_constant_if_bst : forall F c,
      Inv p D F V W ->
      Inv p D F (update_function_constant V c) W.
  Proof.
    intros F c Inv. inversion Inv.
    unfold is_bst in Inv_bst. 
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    constructor. unfold is_bst.
    unfold update_function_constant.
    repeat (split ; auto) ; unpack.
    + pose proof (edge_value_left_if_bst p D V W F x y Inv H).
      lia.
    + pose proof (path_value_left_if_bst p D V W F x y z Inv H H0).
      lia.
    + pose proof (edge_value_right_if_bst p D V W F x y Inv H).
      lia.
    + pose proof (path_value_right_if_bst p D V W F x y z Inv H H0).
      lia.
  Qed.

  Lemma forall_v_diff_z : forall F z, 
      Inv p D F V W ->
      ¬(exists x, x \in D /\ z = V x) ->
      forall x, x \in D -> ¬(z = V x).
  Proof.
    intros.
    intro. apply H0. exists x. split ; auto.
  Qed.
  
End ValueSplayTree.
    
