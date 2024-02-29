From iris.heap_lang Require Import notation lib.assert.
Require Coq.omega.Omega.
Require Coq.micromega.Lia.


Lemma asdf : forall x y z : nat,
  x = y /\ y = x /\ x = z.
Proof.
  repeat split.
  + admit.
  + admit.
  +
    

Definition example_tree :=
  InjR (InjL #4 , #2 , InjL #5).

Definition f e :=
  match e with
  | InjR e1 => e1
  | _ => InjL #()
  end.

Compute (f example_tree).

Fixpoint list_of_nat_to_value (l : list Z) :=
  match l with
  | [] => InjLV #()
  | hd::tl => InjRV (#hd, list_of_nat_to_value tl)
  end.

Compute (list_of_nat_to_value [5;2;3]).

Check bi_sep.
(* Contains definitions of the weakest precondition assertion, and its basic rules. *)
From iris.program_logic Require Export weakestpre.

(* Instantiation of Iris with the particular language. The notation file
   contains many shorthand notations for the programming language constructs, and
   the lang file contains the actual language syntax. *)
From iris.heap_lang Require Export notation lang.

(* Files related to the interactive proof mode. The first import includes the
   general tactics of the proof mode. The second provides some more specialized
   tactics particular to the instantiation of Iris to a particular programming
   language. *)
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.

Set Default Proof Using "Type".


Section list_model.
Context `{!heapG Σ}.

Notation iProp := (iProp Σ).

Implicit Types l : loc.


Fixpoint is_list (hd : val) (xs : list Z) : iProp :=
  match xs with
  | [] => ⌜hd = InjLV (#())⌝
  | x :: xs => ∃ l hd', ⌜hd = InjRV #l⌝ ∗ l ↦ (#x,hd') ∗ is_list hd' xs
end%I.

Definition insert : val :=
  rec: "insert" "l" "v" :=
    match: !"l" with
      NONE     => ref (SOME ("v", NONE))
    | SOME "e" => 
      let: "x" := Fst "e" in
      let: "p" := Snd "e" in
      if: "v" ≤ "x" then
        ref (SOME ("v", "l"))
      else
        "insert" "p" "v" ;;
        "l" <- SOME ("x","p")
    end.

Lemma list_example2 :
  {{{ True }}}
     insert (insert (ref NONE) #3) #2
  {{{ w , RET #w; ∃ l2, w ↦ SOMEV (#2, #l2) ∗ l2 ↦ SOMEV (#3, NONEV) }}}.
Proof.
  iIntros (Φ) "H1 H2".
  unfold insert. wp_alloc l as "H".
  wp_load. wp_match. wp_alloc r as "H3".
  wp_load. wp_match.
  do 2 (wp_proj ; wp_let).
  wp_op. wp_if_true. wp_alloc q as "H4".
  iApply "H2". iExists r.
  iSplitL "H4" ; iFrame.
Qed.

Definition mul : val :=
  rec: "mul" "hd" :=
    match: "hd" with
      NONE     => #1
    | SOME "l" =>
      let: "x" := Fst ! "l" in
      let: "p" := Snd ! "l" in
      "x" * ("mul" "p")
    end.

Fixpoint mul_list xs :=
  match xs with
  | [] => 1
  | hd :: tl => hd * (mul_list tl)
  end.

Lemma inc_spec (hd : val) (xs : list Z) :
  {{{ is_list hd xs }}}
     mul hd
  {{{ w, RET w; ⌜w = #(mul_list xs)⌝ }}}.
Proof.
  iIntros (ϕ) "Hxs H".
  iInduction xs as [|] "IH" forall (hd ϕ).
  + iSimpl in "Hxs". iDestruct "Hxs" as "%".
    rewrite H. wp_rec. wp_match.
    iApply "H". iSimpl. done.
  + iDestruct "Hxs" as (l hd') "[% [H2 H3]]".
    wp_rec. rewrite H. wp_match.
    do 2 (wp_load ; wp_proj ; wp_let).
    iSpecialize ("IH" with "H3").
    iSimpl in "H". Check #a. Check (mul hd').
    wp_pures. wp_bind (mul hd').
    iApply "IH". iNext. iIntros.
    rewrite a0. wp_op. iApply "H". done.    
Qed.
  

Definition right_child : val :=
  λ: "v",
  match: !"v" with
    NONE     => NONE
  | SOME "p" =>
    match: Snd "p" with
      NONE => NONE
    | SOME "pl" => Snd "pl"
    end
  end.

Definition left_child : val :=
  λ: "v",
  match: !"v" with
    NONE     => NONE
  | SOME "p" =>
    match: Snd "p" with
      NONE => NONE
    | SOME "pr" => Fst "pr"
    end
  end.

Definition change_left_child : val :=
  λ: "r" "v",
  match: !"r" with
    NONE     => NONE
  | SOME "p" =>
    match: Snd "p" with
      NONE => NONE
    | SOME "pr" => SOME (Fst "p", SOME("v", Snd "pr"))
    end
  end.

Definition change_right_child : val :=
  λ: "r" "v",
  match: !"r" with
    NONE     => NONE
  | SOME "p" =>
    match: Snd "p" with
      NONE => NONE
    | SOME "pr" => SOME (Fst "p", SOME(Fst "pr", "v"))
    end
  end.

Definition func : val := rec: "func" "p" :=
  if: (!"p" < #10) && (#1 ≠ #0) then
    ("p" <- !"p" + #1 ;; "func" "p")
  else
    #().


Lemma rotate_left_spec `{!heapG Σ} (p : loc) :
  {{{ p ↦ #0 }}}
    (rec: "func" "p" :=
  if: (!"p" < #10) && (#1 ≠ #0) then
    ("p" <- !"p" + #1 ;; "func" "p")
  else
    #()) (#p)
  {{{ RET #() ; p ↦ #10 }}}.
Proof.
  iIntros (Φ) "Hp H".
  do 10 (wp_load ; wp_op ; wp_if ; wp_op ; wp_op ; wp_if ; wp_load ; wp_store).
  wp_lam. wp_load. wp_op. wp_if. wp_if. 
  iApply "H". done.
Qed.

Definition rotate_left : val :=
   λ: "pp" "p" "n",
   let: "tmp" := create_node #0 in
   "tmp" <- (right_child "n") ;;
   "n" <- change_right_child "n" "p" ;;
   "p" <- change_left_child "p" !"tmp";;
   !"pp" <- "n".

Lemma rotate_left_spec `{!heapG Σ} (pp pp' p n : loc) v1 p1 v2 n1 n2 :
  {{{ pp ↦ #pp' ∗ pp' ↦ - ∗ p ↦ SOMEV(v1,InjRV(#n,p1)) ∗ n ↦ SOMEV(v2,InjRV(n1,n2)) }}}
    rotate_left #pp #p #n
  {{{ RET #() ; pp' ↦ #n ∗ p ↦ SOMEV(v1,SOMEV(n2,p1)) ∗ n ↦ SOMEV(v2,SOMEV(n1,#p)) }}}.
Proof.
  iIntros (Φ) "Hp H".
  unfold rotate_left. wp_lam.
  iDestruct "Hp" as "[H1 [H2 [H3 H4]]]".
  wp_let. wp_let. unfold create_node.
  wp_lam. wp_alloc tmp as "Htmp".
  wp_let. unfold right_child.
  wp_lam. wp_load. wp_match. wp_proj.
  wp_match. wp_proj. wp_store. unfold change_right_child. wp_lam.
  wp_load. wp_match. wp_proj.
  wp_match. wp_proj. wp_store.
  unfold change_left_child. wp_load. wp_lam.
  wp_load. wp_match. wp_proj. wp_match.
  wp_store. wp_load. 
  iDestruct "H2" as (l) "H'". wp_store. iApply "H". iFrame.
Qed.

Definition func : val := rec: "func" "p" :=
  if: !"p" < #10 then
    ("p" <- !"p" + #1 ;; "func" "p")
  else
    #().

Lemma func_spec `{!heapG Σ} (p : loc) :
  {{{ p ↦ #1 }}}
    func #p
  {{{ RET #() ; p ↦ #10 }}}.
Proof.
  iIntros (Φ) "Hp H".
  do 9 (wp_lam ; wp_load ; wp_pures ; wp_load ; wp_pures ; wp_store).
  wp_lam. wp_load. wp_pures. iApply "H". iApply "Hp".
Qed.


Definition func1 : val := rec: "func1" "p" "q" :=
  if: !"p" < #10 then
    ("p" <- !"p" + #1 ;; "func1" "p" "q" )
  else
    #().

Lemma func_spec1 `{!heapG Σ} (p : loc) :
  {{{ p ↦ #1 }}}
    func1 #p #0
  {{{ RET #() ; p ↦ #10 }}}.
Proof.
  iIntros (Φ) "Hp H".
  do 9 (wp_lam ; wp_let ; wp_load ; wp_pures ; wp_load ; wp_pures ; wp_store).
  wp_lam. wp_let. wp_load. wp_pures.
  iApply "H". iApply "Hp".
Qed.

Definition func2 : val := rec: "func2" "f" "x" "q" "r" :=
  if: "q" < "r" then
    let:  "y" := "q" + #1 in                             
    ("f" "x" ;; "func2" "f" "x" "y" "r" )
  else
    #().

Lemma func_spec2 `{!heapG Σ} (p : loc) :
  {{{ p ↦ #0 }}}
    func2 (λ: "x", "x" <- !"x" + #1) #p #0 #10
  {{{ RET #() ; p ↦ #10 }}}.
Proof.
  iIntros (Φ) "Hp H".  
  wp_pures.
  do 10 (wp_rec ; do 3 wp_let ; wp_pures ;
  wp_load ; wp_store).
  wp_rec. do 3 wp_let. wp_pures.
  iApply "H". iApply "Hp".
Qed.
