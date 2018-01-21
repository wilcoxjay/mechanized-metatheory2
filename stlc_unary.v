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
  destruct (Forall2_nth_error2 F NEe) as [ty [NEty Ve]].
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

Module has_sem_type.
  Definition t G e ty :=
    expr.wf (length G) e /\
    forall vs,
      Forall2 V G vs ->
      E ty (expr.subst vs e).

  Lemma var :
    forall G x ty,
      nth_error G x = Some ty ->
      t G (expr.var x) ty.
  Proof.
    unfold t.
    intros G x ty NE.
    do_nth_error_Some.
    split; [apply H; congruence|].
    intros vs F.
    apply V_E.
    destruct (Forall2_nth_error1 F NE) as [v [NEv Vv]].
    cbn.
    now rewrite NEv.
  Qed.

  Lemma tt :
    forall G,
      t G expr.tt type.bool.
  Proof.
    unfold t.
    intros G.
    split; [exact I|].
    intros vs F.
    apply V_E.
    cbn.
    intuition.
  Qed.

  Lemma ff :
    forall G,
      t G expr.ff type.bool.
  Proof.
    unfold t.
    intros G.
    split; [exact I|].
    intros vs F.
    apply V_E.
    cbn.
    intuition.
  Qed.

  Lemma abs :
    forall G e ty1 ty2,
      t (ty1 :: G) e ty2 ->
      t G (expr.abs e) (type.arrow ty1 ty2).
  Proof.
    unfold t.
    intros G e ty1 ty2 [WF HT].
    split; [now auto|].
    intros vs F.
    apply V_E.
    cbn [V].
    pose proof (Forall2_length F) as EG.
    cbn [length] in *.
    split; [apply expr.wf_subst;
            [now rewrite EG in WF| now firstorder using V_list_closed]|].
    exists (expr.subst (expr.descend 1 vs) e).
    split; [now rewrite expr.descend_1|].
    intros v Vv.
    rewrite !expr.subst_cons;
      firstorder using V_list_closed.
    now rewrite EG in *.
  Qed.

  Lemma app :
    forall G e1 e2 ty1 ty2,
      t G e1 (type.arrow ty1 ty2) ->
      t G e2 ty1 ->
      t G (expr.app e1 e2) ty2.
  Proof.
    intros G e1 e2 ty1 ty2.
    intros [WF1 HT1].
    intros [WF2 HT2].
    split; [now cbn; auto|].
    intros vs F.

    cbn [expr.subst].
    specialize (HT1 vs F).
    specialize (HT2 vs F).
    destruct HT1 as [v1 [Star1 [Val1 V1]]].
    destruct HT2 as [v2 [Star2 [Val2 V2]]].
    destruct V1 as [WFv1 [body1 [? H1]]].
    subst v1.
    eapply E_star; [|now eauto].

    eapply step.star_trans.
    eapply step.star_app1. now eauto.
    eapply step.star_trans.
    eapply step.star_app2. now eauto.
    eauto using step.step_l, step.beta.
  Qed.

  Lemma If :
    forall G e1 e2 e3 ty,
      t G e1 type.bool ->
      t G e2 ty ->
      t G e3 ty ->
      t G (expr.If e1 e2 e3) ty.
  Proof.
    intros G e1 e2 e3 ty.
    intros [WF1 HT1].
    intros [WF2 HT2].
    intros [WF3 HT3].
    split; [now cbn; auto|].
    intros vs F.

    cbn [expr.subst].
    specialize (HT1 vs F).
    destruct HT1 as [v1 [Star1 [Val1 V1]]].
    eapply E_star; [apply step.star_If|]; eauto.
    destruct V1 as [?|?]; subst;
      (eapply E_step; [constructor|]); auto.
  Qed.
End has_sem_type.

Theorem fundamental :
  forall G e ty,
    has_type.t G e ty ->
    has_sem_type.t G e ty.
Proof.
  induction 1.
  - now apply has_sem_type.var.
  - apply has_sem_type.tt.
  - apply has_sem_type.ff.
  - apply has_type.wf in H.
    apply has_sem_type.abs; auto.
  - eapply has_sem_type.app; eauto.
  - apply has_sem_type.If; auto.
Qed.
Print Assumptions fundamental.

Theorem fundamental_closed :
  forall e ty,
    has_type.t [] e ty ->
    E ty e.
Proof.
  intros e ty HT.
  destruct (fundamental _ _ _ HT) as [WF SHT].
  specialize (SHT [] ltac:(constructor)).
  now rewrite expr.subst_identity with (n := 0) in SHT.
Qed.
