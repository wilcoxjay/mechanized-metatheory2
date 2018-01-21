From mm Require Import util stlc.

Module terminating.
  Definition t (P : expr.t -> Prop) (e : expr.t) :=
    exists v,
      step.star e v /\
      value.t v /\
      P v
  .
End terminating.

Fixpoint V ty e :=
  match ty with
    | type.bool => e = expr.tt \/ e = expr.ff
    | type.arrow ty1 ty2 =>
      expr.wf 0 e /\
      exists body,
          e = expr.abs body /\
          forall e2,
            V ty1 e2 ->
            terminating.t (V ty2) (expr.subst [e2] body)
  end.
Notation E ty :=
  (terminating.t (V ty)).

Lemma V_value :
  forall ty v,
    V ty v ->
    value.t v.
Proof.
  intros ty v HV.
  destruct ty; cbn [V] in HV.
  - intuition; subst; constructor.
  - destruct HV as [WF [body [E H]]].
    subst. constructor.
Qed.

Lemma V_E :
  forall ty v,
    V ty v ->
    E ty v.
Proof.
  intros.
  exists v.
  intuition.
  eauto using V_value.
Qed.

Lemma V_closed :
  forall ty e,
    V ty e ->
    expr.wf 0 e.
Proof.
  induction ty; simpl; intuition; subst; simpl; auto.
Qed.

Lemma V_list_closed :
  forall G vs,
    Forall2 V G vs ->
    Forall (expr.wf 0) vs.
Proof.
  intros G vs F.
  apply Forall_from_nth.
  intros n e NEe.
  destruct (Forall2_nth_error_l F NEe) as [ty [NEty Ve]].
  eauto using V_closed.
Qed.

Lemma E_step :
  forall ty e e',
    step.t e e' ->
    E ty e' ->
    E ty e.
Proof.
  intros ty e e' S HE.
  revert ty HE.
  induction S; intros ty0 [v [Star [Val HV]]]; exists v; intuition.
  all: eapply step.step_l; eauto.
Qed.

Lemma E_star :
  forall ty e e',
    step.star e e' ->
    E ty e' ->
    E ty e.
Proof.
  intros ty e e' Star HE.
  revert ty HE.
  now induction Star; eauto using E_step.
Qed.

Theorem fundamental :
  forall G e ty,
    has_type.t G e ty ->
    forall vs,
      List.Forall2 V G vs ->
      E ty (expr.subst vs e).
Proof.
  induction 1; intros vs F.
  - cbn [expr.subst].
    destruct (Forall2_nth_error_r F H) as [v [Hvs HV]].
    simpl.
    rewrite Hvs.
    auto using V_E.
  - apply V_E.
    simpl.
    intuition.
  - apply V_E.
    simpl.
    intuition.
  - apply V_E.
    cbn [V].
    assert (expr.wf (S (length vs)) e) as WFe
      by (apply has_type.wf in H;
          simpl in *;
          now erewrite Forall2_length in * by eauto).
    split.
    + apply expr.wf_subst; eauto using V_list_closed.
    + exists (expr.subst (expr.descend 1 vs) e).
      split; [now rewrite expr.descend_1|].
      intros e2 Ve2.
      rewrite expr.subst_cons; eauto using V_list_closed.
  - cbn [expr.subst].
    specialize (IHt1 vs F).
    specialize (IHt2 vs F).
    destruct IHt1 as [v1 [S1 [Val1 V1]]].
    destruct IHt2 as [v2 [S2 [Val2 V2]]].
    destruct V1 as [WF1 [body [? H1]]].
    subst v1.
    eapply E_star; [|now eauto].
    eapply step.star_trans.
    eapply step.star_app1. now eauto.
    eapply step.star_trans.
    eapply step.star_app2. now eauto.
    eauto using step.step_l, step.beta.
  - cbn [expr.subst].
    specialize (IHt1 vs F).
    destruct IHt1 as [v1 [S1 [Val1 V1]]].
    eapply E_star.
    eapply step.star_If; now eauto.
    destruct V1 as [|]; subst v1;
      (eapply E_step; [constructor|]); auto.
Qed.
Print Assumptions fundamental.

Theorem fundamental_closed :
  forall e ty,
    has_type.t [] e ty ->
    E ty e.
Proof.
  intros e ty HT.
  pose proof fundamental _ _ _ HT [] ltac:(constructor).
  now rewrite expr.subst_identity with (n := 0) in H.
Qed.
