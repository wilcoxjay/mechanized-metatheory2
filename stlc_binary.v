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

Lemma V_closed :
  forall ty v1 v2 ,
    V ty v1 v2 ->
    expr.wf 0 v1 /\ expr.wf 0 v2.
Proof.
  induction ty; simpl; intuition; subst; simpl; auto.
Qed.

Lemma V_list_closed :
  forall G vs1 vs2,
    Forall3 V G vs1 vs2 ->
    Forall (expr.wf 0) vs1 /\ Forall (expr.wf 0) vs2.
Proof.
  intros G vs1 vs2 F.
  split; apply Forall_from_nth.
  - intros n e1 NEe1.
    destruct (Forall3_nth_error2 _ F NEe1) as [ty [e2 [NEty [NEe2 Ve2]]]].
    firstorder using V_closed.
  - intros n e2 NEe2.
    destruct (Forall3_nth_error3 _ F NEe2) as [ty [e1 [NEty [NEe1 Ve1]]]].
    firstorder using V_closed.
Qed.

Lemma E_step1 :
  forall ty e1 e1' e2,
    step.t e1 e1' ->
    E ty e1' e2 ->
    E ty e1 e2.
Proof.
  intros ty e1 e1' e2 S HE.
  revert ty e2 HE.
  induction S; intros ty0 e0 [v1 [v2 [Star1 [Star2 [Val1 [Val2 V12]]]]]]; exists v1, v2; intuition.
  all: eapply step.step_l; eauto.
Qed.

Lemma E_step2 :
  forall ty e1 e2 e2',
    step.t e2 e2' ->
    E ty e1 e2' ->
    E ty e1 e2.
Proof.
  intros ty e1 e2 e2' S HE.
  revert ty e1 HE.
  induction S; intros ty0 e0 [v1 [v2 [Star1 [Star2 [Val1 [Val2 V12]]]]]]; exists v1, v2; intuition.
  all: eapply step.step_l; eauto.
Qed.

Lemma E_star1 :
  forall ty e1 e1' e2,
    step.star e1 e1' ->
    E ty e1' e2 ->
    E ty e1 e2.
Proof.
  intros ty e1 e1' e2 Star E12.
  revert ty e2 E12.
  now induction Star; eauto using E_step1.
Qed.

Lemma E_star2 :
  forall ty e1 e2 e2',
    step.star e2 e2' ->
    E ty e1 e2' ->
    E ty e1 e2.
Proof.
  intros ty e1 e2 e2' Star E12.
  revert ty e1 E12.
  now induction Star; eauto using E_step2.
Qed.

Lemma E_star :
  forall ty e1 e1' e2 e2',
    step.star e1 e1' ->
    step.star e2 e2' ->
    E ty e1' e2' ->
    E ty e1 e2.
Proof.
  intros ty e1 e1' e2 e2' Star1 Star2 E12.
  eapply E_star1; [|eapply E_star2]; eauto.
Qed.

Module has_sem_type.
  Definition t G e1 e2 ty :=
    expr.wf (length G) e1 /\
    expr.wf (length G) e2 /\
    forall vs1 vs2,
      Forall3 V G vs1 vs2 ->
      E ty (expr.subst vs1 e1) (expr.subst vs2 e2).

  Lemma var : forall G x ty,
      nth_error G x = Some ty ->
      t G (expr.var x) (expr.var x) ty.
  Proof.
    unfold t.
    intros G x ty NE.
    do_nth_error_Some.
    split; [apply H; congruence|].
    split; [apply H; congruence|].
    intros vs1 vs2 F.
    apply V_E.
    destruct (Forall3_nth_error1 _ F NE) as [v1 [v2 [NE1 [NE2 V12]]]].
    cbn.
    now rewrite NE1, NE2.
  Qed.

  Lemma tt : forall G,
      t G expr.tt expr.tt type.unit.
  Proof.
    unfold t.
    intros G.
    split; [exact I|].
    split; [exact I|].
    intros vs1 vs2 F.
    apply V_E.
    cbn.
    intuition.
  Qed.

  Lemma abs :
    forall G e1 e2 ty1 ty2,
      t (ty1 :: G) e1 e2 ty2 ->
      t G (expr.abs e1) (expr.abs e2) (type.arrow ty1 ty2).
  Proof.
    unfold t.
    intros G e1 e2 ty1 ty2 [WF1 [WF2 HT]].
    split; [now auto|].
    split; [now auto|].
    intros vs1 vs2 F.
    apply V_E.
    cbn [V].
    destruct (Forall3_length F) as [EG1 EG2].
    cbn [length] in *.
    split; [apply expr.wf_subst;
            [now rewrite EG1 in WF1| now firstorder using V_list_closed]|].
    split; [apply expr.wf_subst;
            [now rewrite EG2 in WF2| now firstorder using V_list_closed]|].
    exists (expr.subst (expr.descend 1 vs1) e1), (expr.subst (expr.descend 1 vs2) e2).
    split; [now rewrite expr.descend_1|].
    split; [now rewrite expr.descend_1|].
    intros v1 v2 V12.
    rewrite !expr.subst_cons;
      firstorder using V_list_closed.
    now rewrite EG2 in *.
    now rewrite EG1 in *.
  Qed.

  Lemma app :
    forall G e11 e12 e21 e22 ty1 ty2,
      t G e11 e21 (type.arrow ty1 ty2) ->
      t G e12 e22 ty1 ->
      t G (expr.app e11 e12) (expr.app e21 e22) ty2.
  Proof.
    intros G e11 e12 e21 e22 ty1 ty2.
    intros [WF11 [WF12 HT1]].
    intros [WF21 [WF22 HT2]].
    split; [now cbn; auto|].
    split; [now cbn; auto|].
    intros vs1 vs2 F.

    cbn [expr.subst].
    specialize (HT1 vs1 vs2 F).
    specialize (HT2 vs1 vs2 F).
    destruct HT1 as [v11 [v12 [Star11 [Star12 [Val11 [Val12 V1]]]]]].
    destruct HT2 as [v21 [v22 [Star21 [Star22 [Val21 [Val22 V2]]]]]].
    destruct V1 as [WF1 [WF2 [body1 [body2 [? [? H1]]]]]].
    subst v11 v12.
    eapply E_star; [| |now eauto].

    eapply step.star_trans.
    eapply step.star_app1. now eauto.
    eapply step.star_trans.
    eapply step.star_app2. now eauto.
    eauto using step.step_l, step.beta.

    eapply step.star_trans.
    eapply step.star_app1. now eauto.
    eapply step.star_trans.
    eapply step.star_app2. now eauto.
    eauto using step.step_l, step.beta.
  Qed.
End has_sem_type.

Theorem fundamental :
  forall G e ty,
    has_type.t G e ty ->
    has_sem_type.t G e e ty.
Proof.
  induction 1.
  - now apply has_sem_type.var.
  - apply has_sem_type.tt.
  - apply has_type.wf in H.
    apply has_sem_type.abs; auto.
  - eapply has_sem_type.app; eauto.
Qed.
Print Assumptions fundamental.

Corollary fundamental_closed :
  forall e ty,
    has_type.t [] e ty ->
    E ty e e.
Proof.
  intros e ty HT.
  apply fundamental with (vs1 := []) (vs2 := []) in HT; auto.
  now rewrite !expr.subst_identity with (n := 0) in *.
Qed.

Lemma fundamental_value :
  forall v ty,
    has_type.t [] v ty ->
    value.t v ->
    V ty v v.
Proof.
  intros v ty HT Val.
  pose proof fundamental_closed HT as Ev.
  destruct Ev as [v1 [v2 [Star1 [Star2 [Val1 [Val2 V12]]]]]].
  apply step.star_value in Star1; auto.
  apply step.star_value in Star2; auto.
  subst.
  auto.
Qed.

Corollary termination :
  forall e ty,
    has_type.t [] e ty ->
    exists v, value.t v /\ step.star e v.
Proof.
  intros e ty HT.
  destruct (fundamental_closed HT) as [v1 [v2 [Star1 [Star2 [Val1 [Val2 V12]]]]]].
  eauto.
Qed.




