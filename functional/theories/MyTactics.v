

Ltac logical_reduction :=
  try intros ; simpl in * ; subst ; try assumption ; try eauto ;
  match goal with
  | h : ?a = ?a |- _ =>
    clear h; logical_reduction
  | h1 : False |- _ =>
    contradiction
  | h : True |- _ =>
    clear h; logical_reduction
  | h : _ /\ _ |- _ =>
    destruct h; logical_reduction
  | h : exists a, _ |- _ =>
    destruct h; logical_reduction
  | h : _ |- _ /\ _ =>
    split; logical_reduction
  | h1 : ?A,
    h2 : ?A |-  _ =>
    clear h1 ; logical_reduction   
  | h : _ \/ _ |-  _ =>
    destruct h; logical_reduction
  | h1 : ?A, h2 : ?A -> ?B |- _ =>
    apply h2 in h1 as new
  | _ => idtac
  end.           
