Require Import util.
Require Import abt.

Module tyop.
  Inductive t' :=
  | arrow
  | all
  .
  Definition t := t'.

  Definition arity (op : t) : arity.t :=
    match op with
    | arrow => [0; 0]
    | all => [1]
    end.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
  Defined.

End tyop.

Module exprop.
  Inductive t' :=
  | abs
  | app
  | tyabs
  | tyapp
  .
  Definition t := t'.

  Definition arity (op : t) : arity.t :=
    match op with
    | abs => [1]
    | app => [0; 0]
    | tyabs => [0]
    | tyapp => [0]
    end.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
  Defined.
End exprop.

Module type.
   Include abt.abt tyop.
   Notation arrow ty1 ty2 := (op tyop.arrow [bind 0 ty1; bind 0 ty2]).
   Notation all ty := (op tyop.all [bind 1 ty]).
End type.

Module expr.
   Include abt.abt exprop.
   Notation abs e := (op exprop.abs [bind 1 e]).
   Notation app e1 e2 := (op exprop.app [bind 0 e1; bind 0 e2]).
   Notation tyabs e := (op exprop.tyabs [bind 0 e]).
   Notation tyapp e := (op exprop.tyapp [bind 0 e]).
End expr.

Module has_type.
  Inductive t : nat -> list type.t -> expr.t -> type.t -> Prop :=
  | var : forall n G x ty,
      nth_error G x = Some ty ->
      t n G (expr.var x) ty

  | abs : forall n G ty1 ty2 e
      (WFty1 : type.wf n ty1),
      t n (ty1 :: G) e ty2 ->
      t n G (expr.abs e) (type.arrow ty1 ty2)
  | app : forall n G ty1 ty2 e1 e2,
      t n G e1 (type.arrow ty1 ty2) -> 
      t n G e2 ty1 ->
      t n G (expr.app e1 e2) ty2

  | tyabs : forall n G e ty,
      t (S n) (map (type.shift 0 1) G) e ty ->
      t n G (expr.tyabs e) (type.all ty)
  | tyapp : forall n G e ty_body ty,
      type.wf n ty ->
      t n G e (type.all ty_body) ->
      t n G (expr.tyapp e) (type.subst (ty :: type.identity_subst n) ty_body)
  .

  Lemma t_type_wf :
    forall n G e ty,
      t n G e ty ->
      Forall (type.wf n) G ->
      type.wf n ty.
  Proof.
    induction 1; simpl in *; intuition.
    - now eapply Forall_nth; eauto.
    - apply IHt.
      rewrite Forall_map.
      eapply Forall_impl; [|now eauto].
      intros e' WF.
      now apply type.wf_shift with (c := 0) (d := 1).
    - apply type.wf_subst.
      + simpl. now rewrite type.identity_subst_length.
      + constructor; auto.
        clear H H0 H1 H3 H4.
        induction n; simpl; constructor.
        * simpl. omega.
        * rewrite Forall_map.
          eapply Forall_impl; [|now eauto].
          intros e' WF'.
          now apply type.wf_shift with (c := 0) (d := 1).
  Qed.

  Lemma t_expr_wf :
    forall n G e ty,
      t n G e ty ->
      expr.wf (length G) e.
  Proof.
    induction 1; simpl in *; intuition.
    - apply nth_error_Some. congruence.
    - now rewrite map_length in *.
  Qed.
End has_type.

Module value.
  Inductive t : expr.t -> Prop :=
  | abs : forall e, t (expr.abs e)
  | tyabs : forall e, t (expr.tyabs e)
  .
End value.

Module step.
  Inductive t : expr.t -> expr.t -> Prop :=
  | app1 : forall e1 e1' e2,
      t e1 e1' ->
      t (expr.app e1 e2) (expr.app e1' e2)
  | app2 : forall e1 e2 e2',
      value.t e1 ->
      t e2 e2' ->
      t (expr.app e1 e2) (expr.app e1 e2')
  | beta : forall body v,
      value.t v ->
      t (expr.app (expr.abs body) v) (expr.subst [v] body)
  | tyapp : forall e e' ,
      t e e' ->
      t (expr.tyapp e) (expr.tyapp e')
  | tybeta : forall body,
      t (expr.tyapp (expr.tyabs body))
        body
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
      value.t e1 ->
      star e2 e2' ->
      star (expr.app e1 e2) (expr.app e1 e2').
  Proof.
    intros e1 e2 e2' V1 Star.
    revert e1 V1.
    induction Star; intros e1.
    - constructor.
    - econstructor; [|apply IHStar]; eauto.
  Qed.

  Lemma star_tyapp :
    forall e e',
      star e e' ->
      star (expr.tyapp e) (expr.tyapp e').
  Proof.
    intros e e' Star.
    induction Star.
    - constructor.
    - econstructor; [|apply IHStar]; eauto.
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

  Lemma value :
    forall v e',
      value.t v ->
      step.t v e' ->
      False.
  Proof.
    intros v e' Val Step.
    inversion Step; subst; inversion Val.
  Qed.

  Lemma star_value :
    forall v e',
      value.t v ->
      step.star v e' ->
      e' = v.
  Proof.
    intros v e' Val Star.
    apply clos_rtn1_rt in Star.
    apply clos_rt_rt1n in Star.
    inversion Star; subst; auto.
    exfalso; eauto using value.
  Qed.
End step.
