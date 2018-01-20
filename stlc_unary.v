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
    | type.unit => e = expr.tt
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
  - subst. constructor.
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
  - constructor.
  - eauto using V_value.
Qed.

Lemma has_type_wf :
  forall G e ty,
    has_type.t G e ty ->
    expr.wf (List.length G) e.
Proof.
  induction 1; simpl in *; intuition.
  pose proof nth_error_Some G x. intuition congruence.
Qed.

Lemma V_closed :
  forall ty e,
    V ty e ->
    expr.wf 0 e.
Proof.
  induction ty; simpl; intuition.
  subst. simpl. auto.
Qed.

Lemma V_list_closed :
  forall G vs,
    Forall2 V G vs ->
    Forall (expr.wf 1) (expr.var 0 :: map (expr.shift 0 1) vs).
Proof.
  intros G vs F.
  constructor.
  - simpl. omega.
  - rewrite Forall_map.
    induction F; constructor; auto.
    apply expr.wf_shift with (d := 1) (n := 0).
    now eauto using V_closed.
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
  - eapply step.step_l; eauto.
  - eapply step.step_l; eauto.
  - eapply step.step_l; eauto.
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
    rewrite Hvs.
    auto using V_E.
  - apply V_E.
    reflexivity.
  - cbn [expr.subst].
    apply V_E.
    cbn [V].
    split.
    + simpl. apply expr.wf_subst.
      * simpl. rewrite map_length.
        apply has_type_wf in H.
        simpl in *.
        now erewrite Forall2_length in * by eauto.
      * eapply V_list_closed; eauto.
    + eexists. split. reflexivity.
      intros e2 Ve2.
      cbn [expr.subst].
      set (vs' := e2 :: vs).
      match goal with
      | [  |- E _ ?foo ] =>
        replace foo with (expr.subst vs' e)
      end.
      apply IHt.
      constructor; auto.
      rewrite expr.subst_subst.
      * simpl. f_equal. subst vs'. f_equal.
        rewrite map_map.
        erewrite map_ext_in; [now rewrite map_id|].
        intros e' I. simpl.
        rewrite expr.subst_shift_singleton; auto.
        destruct (In_nth_error _ _ I) as [n NE].
        destruct (Forall2_nth_error_l F NE) as [ty [NE2 HV]].
        now eauto using V_closed.
      * simpl. rewrite map_length.
        eapply has_type_wf in H. simpl in *.
        now erewrite <- Forall2_length by eauto.
      * eapply V_list_closed; eauto.
  - simpl.
    specialize (IHt1 vs F).
    specialize (IHt2 vs F).
    destruct IHt1 as [v1 [S1 [Val1 V1]]].
    destruct IHt2 as [v2 [S2 [Val2 V2]]].
    destruct V1 as [WF1 [body [? H1]]].
    subst v1.
    apply E_star with (e' := expr.subst [v2] body); [|now eauto].
    eapply step.star_trans.
    eapply step.star_app1; eauto.
    eapply step.star_trans.
    eapply step.star_app2; eauto.
    eapply step.step_l.
    apply step.beta.
    constructor.
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
