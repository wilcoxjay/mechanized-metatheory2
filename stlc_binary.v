From mm Require Import util stlc.
Set Implicit Arguments.

Module terminating.
  Definition t (P : expr.t -> expr.t -> Prop) (e1 e2 : expr.t) :=
    exists v1 v2,
      step.star e1 v1 /\
      step.star e2 v2 /\
      value.t v1 /\
      value.t v2 /\
      P v1 v2
  .
End terminating.

Fixpoint V ty e1 e2 :=
  match ty with
    | type.unit => e1 = expr.tt /\ e2 = expr.tt
    | type.arrow ty1 ty2 =>
      expr.wf 0 e1 /\
      expr.wf 0 e2 /\
      exists body1 body2,
          e1 = expr.abs body1 /\
          e2 = expr.abs body2 /\
          forall v1 v2,
            V ty1 v1 v2 ->
            terminating.t (V ty2) (expr.subst [v1] body1) (expr.subst [v2] body2)
  end.
Notation E ty :=
  (terminating.t (V ty)).

Lemma V_value :
  forall ty v1 v2,
    V ty v1 v2 ->
    value.t v1 /\ value.t v2.
Proof.
  intros ty v1 v2 HV.
  destruct ty; cbn [V] in HV.
  - intuition; subst; constructor.
  - destruct HV as [WF1 [WF2 [body1 [body2 [? [? _]]]]]].
    intuition; subst; constructor.
Qed.

Lemma V_E :
  forall ty v1 v2,
    V ty v1 v2 ->
    E ty v1 v2.
Proof.
  intros.
  exists v1, v2.
  intuition.
  - firstorder using V_value.
  - firstorder using V_value.
Qed.

Theorem fundamental :
  forall G e ty,
    has_type.t G e ty ->
    forall vs1 vs2,
      Forall3 V G vs1 vs2 ->
      E ty (expr.subst vs1 e) (expr.subst vs2 e).
Proof.
  induction 1; intros vs1 vs2 F.
  - apply V_E.
    destruct (Forall3_nth_error1 _ F H) as [v1 [v2 [NE1 [NE2 V12]]]].
    simpl.
    now rewrite NE1, NE2.
  - apply V_E.
    simpl.
    intuition.
  - apply V_E.
    cbn [V].
    split; [|split].
    + apply expr.wf_subst.

Admitted.