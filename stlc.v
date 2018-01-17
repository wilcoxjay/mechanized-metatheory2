Require Import util abt.

Module exprop.
  Inductive t' :=
  | abs
  | app
  | tt
  .
  Definition t := t'.

  Definition arity (op : t) : arity.t :=
    match op with
    | abs => [1]
    | app => [0; 0]
    | tt => []
    end.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
  Defined.
End exprop.

Module type.
  Inductive t :=
  | unit
  | arrow : t -> t -> t
  .
End type.

Module expr.
   Include abt.abt exprop.
   Notation abs e := (op exprop.abs [bind 1 e]).
   Notation app e1 e2 := (op exprop.app [bind 0 e1; bind 0 e2]).
   Notation tt := (op exprop.tt []).
End expr.


Module has_type.
  Inductive t : list type.t -> expr.t -> type.t -> Prop :=
  | var : forall G x ty,
      List.nth_error G x = Some ty ->
      t G (expr.var x) ty
  | tt : forall G,
      t G expr.tt type.unit
  | abs : forall G e ty1 ty2,
      t (ty1 :: G) e ty2 ->
      t G (expr.abs e) (type.arrow ty1 ty2)
  | app : forall G e1 e2 ty1 ty2,
      t G e1 (type.arrow ty1 ty2) ->
      t G e2 ty1 ->
      t G (expr.app e1 e2) ty2
  .
End has_type.


Module ctx.
  Definition t := list type.t.
End ctx.

Lemma has_type_shift :
  forall G e ty,
    has_type.t G e ty ->
    forall G1 G2 G',
      G1 ++ G2 = G ->
      has_type.t (G1 ++ G' ++ G2) (expr.shift (List.length G1) (List.length G') e) ty.
Proof.
  induction 1; intros G1 G2 G' E; subst G.
  - constructor.
    do_ltb.
    + now rewrite nth_error_app1 in * by assumption.
    + rewrite !nth_error_app2 in * by omega.
      now do_app2_minus.
  - constructor.
  - cbn [expr.shift].
    constructor.
    change (ty1 :: G1 ++ G' ++ G2) with ((ty1 :: G1) ++ G' ++ G2).
    now apply IHt.
  - simpl. econstructor.
    + now apply IHt1.
    + now apply IHt2.
Qed.

Lemma has_type_shift' :
  forall G e ty G',
    has_type.t G e ty ->
    has_type.t (G' ++ G) (expr.shift 0 (List.length G') e) ty.
Proof.
  intros.
  now apply has_type_shift with (G := G) (G1 := []).
Qed.

Lemma has_type_shift_cons :
  forall G e ty ty0,
    has_type.t G e ty ->
    has_type.t (ty0 :: G) (expr.shift 0 1 e) ty.
Proof.
  intros.
  now apply has_type_shift' with (G' := [ty0]).
Qed.

Lemma has_type_subst :
  forall G e ty,
    has_type.t G e ty ->
    forall G' rho,
      List.Forall2 (has_type.t G') rho G ->
      has_type.t G' (expr.subst rho e) ty.
Proof.
  induction 1; intros G' rho F; cbn [expr.subst].
  - destruct (Forall2_nth_error_l F H) as [z [Hz Ht]].
    now rewrite Hz.
  - constructor.
  - constructor.
    apply IHt.
    constructor.
    + now constructor.
    + apply Forall2_map_l.
      apply Forall2_forall_suff_weak.
      * now erewrite Forall2_length by eauto.
      * intros.
        apply has_type_shift_cons.
        eapply (Forall2_nth_error F); eauto.
  - cbn [expr.subst_binder]. rewrite expr.descend_0.
    econstructor.
    + now apply IHt1.
    + now apply IHt2.
Qed.

Module value.
  Inductive t : expr.t -> Prop :=
  | tt : t expr.tt
  | abs : forall e, t (expr.abs e)
  .
End value.

Module step.
  Inductive t : expr.t -> expr.t -> Prop :=
  | app1  : forall e1 e1' e2,
      t e1 e1' ->
      t (expr.app e1 e2) (expr.app e1' e2)
  | app2  : forall e1 e2 e2',
      t e2 e2' ->
      t (expr.app e1 e2) (expr.app e1 e2')
  | beta : forall e1 e2,
      t (expr.app (expr.abs e1) e2)
        (expr.subst [e2] e1)
  .
  Hint Constructors t.

  Definition star : expr.t -> expr.t -> Prop := clos_refl_trans_n1 _ t.

  Lemma step_l :
    forall e1 e2 e3,
      step.t e1 e2 ->
      step.star e2 e3 ->
      step.star e1 e3.
  Proof.
    intros e1 e2 e3 S Star.
    apply clos_rt_rtn1.
    apply clos_rtn1_rt in Star.
    eapply rt_trans; eauto using rt_step.
  Qed.

  Lemma star_app1 :
    forall e1 e1' e2,
      star e1 e1' ->
      star (expr.app e1 e2) (expr.app e1' e2).
  Proof.
    intros e1 e1' e2 Star.
    revert e2.
    induction Star; intros e2.
    - constructor.
    - econstructor; [|apply IHStar].
      eauto.
  Qed.

  Lemma star_app2 :
    forall e1 e2 e2',
      star e2 e2' ->
      star (expr.app e1 e2) (expr.app e1 e2').
  Proof.
    intros e1 e2 e2' Star.
    revert e1.
    induction Star; intros e1.
    - constructor.
    - econstructor; [|apply IHStar].
      eauto.
  Qed.

  Lemma star_trans :
    forall e1 e2 e3,
      star e1 e2 ->
      star e2 e3 ->
      star e1 e3.
  Proof.
    intros e1 e2 e3 S1 S2.
    apply clos_rtn1_rt in S1.
    apply clos_rtn1_rt in S2.
    apply clos_rt_rtn1.
    eauto using rt_trans.
  Qed.
End step.

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
    + simpl. split; [|exact I]. apply expr.wf_subst.
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
        rewrite expr.subst_shift with (rho1 := []) (rho2 := [e2]) (rho3 := []).
        -- now rewrite expr.subst_identity with (n := 0).
        -- simpl.
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
    rewrite expr.descend_0.
    eapply step.star_trans.
    eapply step.star_app1; eauto.
    eapply step.star_trans.
    eapply step.star_app2; eauto.
    eapply step.step_l.
    apply step.beta.
    constructor.
Qed.

Theorem fundamental_closed :
  forall e ty,
    has_type.t [] e ty ->
    E ty e.
Proof.
  intros e ty HT.
  pose proof fundamental _ _ _ HT [] ltac:(constructor).
  now rewrite expr.subst_identity with (n := 0) in H.
Qed.
