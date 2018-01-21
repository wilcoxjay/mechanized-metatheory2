From mm Require Import util abt.

Module tyop.
  Inductive t' :=
  | arrow
  | all
  | exist
  .
  Definition t := t'.

  Definition arity (op : t) : arity.t :=
    match op with
    | arrow => [0; 0]
    | all => [1]
    | exist => [1]
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
  | pack
  | unpack
  .
  Definition t := t'.

  Definition arity (op : t) : arity.t :=
    match op with
    | abs => [1]
    | app => [0; 0]
    | tyabs => [0]
    | tyapp => [0]
    | pack => [0]
    | unpack => [0; 1]
    end.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
  Defined.
End exprop.

Module type_abt := abt.abt tyop.

Module type_ast.
  Inductive t :=
  | var (alpha : nat) : t
  | arrow : t -> t -> t
  | all : t -> t
  | exist : t -> t
  .
End type_ast.

Module type_basis.
  Module A := type_abt.

  Import type_ast.
  Definition t := t.

  Fixpoint to_abt (ty : t) : A.t :=
    match ty with
    | var n => A.var n
    | arrow ty1 ty2 => A.op tyop.arrow [A.bind 0 (to_abt ty1); A.bind 0 (to_abt ty2)]
    | all ty' => A.op tyop.all [A.bind 1 (to_abt ty')]
    | exist ty' => A.op tyop.exist [A.bind 1 (to_abt ty')]
    end.

  Fixpoint of_abt (a : A.t) : t :=
    match a with
    | A.var n => var n
    | A.op tyop.arrow [A.bind 0 a1; A.bind 0 a2] => arrow (of_abt a1) (of_abt a2)
    | A.op tyop.all [A.bind 1 a'] => all (of_abt a')
    | A.op tyop.exist [A.bind 1 a'] => exist (of_abt a')
    | _ => var 0 (* bogus *)
    end.

  Fixpoint shift c d (ty : t) : t :=
    match ty with
    | var alpha => var (if alpha <? c then alpha else alpha + d)
    | arrow ty1 ty2 => arrow (shift c d ty1) (shift c d ty2)
    | all ty' => all (shift (S c) d ty')
    | exist ty' => exist (shift (S c) d ty')
    end.

  Fixpoint subst rho ty :=
    match ty with
    | var alpha => match nth_error rho alpha with
                  | Some ty' => ty'
                  | None => ty
                  end
    | arrow ty1 ty2 => arrow (subst rho ty1) (subst rho ty2)
    | all ty' => all (subst (var 0 :: map (shift 0 1) rho) ty')
    | exist ty' => exist (subst (var 0 :: map (shift 0 1) rho) ty')
    end.

  Fixpoint wf n ty :=
    match ty with
    | var alpha => alpha < n
    | arrow ty1 ty2 => wf n ty1 /\ wf n ty2
    | all ty' => wf (S n) ty'
    | exist ty' => wf (S n) ty'
    end.

  Fixpoint identity_subst (n : nat) : list t :=
    match n with
    | 0 => []
    | S n => var 0 :: map (shift 0 1) (identity_subst n)
    end.

    Lemma ws_to_abt : forall e, A.ws (to_abt e).
  Proof. A.basis_util.prove_ws_to_abt. Qed.

  Lemma of_to_abt : forall e, of_abt (to_abt e) = e.
  Proof. A.basis_util.prove_of_to_abt. Qed.

  Lemma to_of_abt : forall a, A.ws a -> to_abt (of_abt a) = a.
  Proof. A.basis_util.prove_to_of_abt to_abt of_abt. Qed.

  Lemma shift_to_abt_comm : forall e c d, to_abt (shift c d e) = A.shift c d (to_abt e).
  Proof. A.basis_util.prove_shift_to_abt_comm. Qed.

  Lemma map_shift_to_abt_comm :
    forall c d rho, map to_abt (map (shift c d) rho) = map (A.shift c d) (map to_abt rho).
  Proof. A.basis_util.prove_map_shift_to_abt_comm shift_to_abt_comm. Qed.

  Lemma subst_to_abt_comm : forall e rho,
      to_abt (subst rho e) = A.subst (map to_abt rho) (to_abt e).
  Proof. A.basis_util.prove_subst_to_abt_comm t map_shift_to_abt_comm. Qed.

  Lemma wf_to_abt : forall e n, wf n e <-> A.wf n (to_abt e).
  Proof. A.basis_util.prove_wf_to_abt. Qed.

  Lemma identity_subst_to_abt_comm :
    forall n, List.map to_abt (identity_subst n) = A.identity_subst n.
  Proof. A.basis_util.prove_identity_subst_to_abt_comm map_shift_to_abt_comm. Qed.

  Definition var := var.
  Arguments var /.
  Lemma var_to_abt : forall n, to_abt (var n) = A.var n.
  Proof. reflexivity. Qed.
End type_basis.

Module type.
   Include abt.abt_util type_basis.
   Notation arrow := type_ast.arrow.
   Notation all := type_ast.all.
   Notation exist := type_ast.exist.
End type.

Module expr_abt := abt.abt exprop.

Module expr_ast.
  Inductive t :=
  | var (x : nat) : t
  | abs : t -> t
  | app : t -> t -> t
  | tyabs : t -> t
  | tyapp : t -> t
  | pack : t -> t
  | unpack : t -> t -> t
  .
End expr_ast.

Module expr_basis.
  Module A := expr_abt.

  Import expr_ast.
  Definition t := t.

  Fixpoint to_abt (ty : t) : A.t :=
    match ty with
    | var n => A.var n
    | abs e' => A.op exprop.abs [A.bind 1 (to_abt e')]
    | app e1 e2 => A.op exprop.app [A.bind 0 (to_abt e1); A.bind 0 (to_abt e2)]
    | tyabs e' => A.op exprop.tyabs [A.bind 0 (to_abt e')] 
    | tyapp e' => A.op exprop.tyapp [A.bind 0 (to_abt e')]
    | pack e' => A.op exprop.pack [A.bind 0 (to_abt e')] 
    | unpack e1 e2 => A.op exprop.unpack [A.bind 0 (to_abt e1); A.bind 1 (to_abt e2)] 
    end.

  Fixpoint of_abt (a : A.t) : t :=
    match a with
    | A.var n => var n
    | A.op exprop.abs [A.bind 1 a'] => abs (of_abt a')
    | A.op exprop.app [A.bind 0 a1; A.bind 0 a2] => app (of_abt a1) (of_abt a2)
    | A.op exprop.tyabs [A.bind 0 a'] => tyabs (of_abt a')
    | A.op exprop.tyapp [A.bind 0 a'] => tyapp (of_abt a')
    | A.op exprop.pack [A.bind 0 a'] => pack (of_abt a')
    | A.op exprop.unpack [A.bind 0 a1; A.bind 1 a2] => unpack (of_abt a1) (of_abt a2)
    | _ => var 0 (* bogus *)
    end.

  Fixpoint shift c d (e : t) : t :=
    match e with
    | var x => var (if x <? c then x else x + d)
    | abs e' => abs (shift (S c) d e')
    | app e1 e2 => app (shift c d e1) (shift c d e2)
    | tyabs e' => tyabs (shift c d e')
    | tyapp e' => tyapp (shift c d e')
    | pack e' => pack (shift c d e')
    | unpack e1 e2 => unpack (shift c d e1) (shift (S c) d e2)
    end.

  Fixpoint subst rho e :=
    match e with
    | var x => match nth_error rho x with
                  | Some e' => e'
                  | None => e
                  end
    | abs e' => abs (subst (var 0 :: map (shift 0 1) rho) e')
    | app e1 e2 => app (subst rho e1) (subst rho e2)
    | tyabs e' => tyabs (subst rho e')
    | tyapp e' => tyapp (subst rho e')
    | pack e' => pack (subst rho e')
    | unpack e1 e2 => unpack (subst rho e1) (subst (var 0 :: map (shift 0 1) rho) e2)
    end.

  Fixpoint wf n e :=
    match e with
    | var x => x < n
    | abs e' => wf (S n) e'
    | app e1 e2 => wf n e1 /\ wf n e2
    | tyabs e' => wf n e'
    | tyapp e' => wf n e'
    | pack e' => wf n e'
    | unpack e1 e2 => wf n e1 /\ wf (S n) e2
    end.

  Fixpoint identity_subst (n : nat) : list t :=
    match n with
    | 0 => []
    | S n => var 0 :: map (shift 0 1) (identity_subst n)
    end.

  Lemma ws_to_abt : forall e, A.ws (to_abt e).
  Proof. A.basis_util.prove_ws_to_abt. Qed.

  Lemma of_to_abt : forall e, of_abt (to_abt e) = e.
  Proof. A.basis_util.prove_of_to_abt. Qed.

  Lemma to_of_abt : forall a, A.ws a -> to_abt (of_abt a) = a.
  Proof. A.basis_util.prove_to_of_abt to_abt of_abt. Qed.

  Lemma shift_to_abt_comm : forall e c d, to_abt (shift c d e) = A.shift c d (to_abt e).
  Proof. A.basis_util.prove_shift_to_abt_comm. Qed.

  Lemma map_shift_to_abt_comm :
    forall c d rho, map to_abt (map (shift c d) rho) = map (A.shift c d) (map to_abt rho).
  Proof. A.basis_util.prove_map_shift_to_abt_comm shift_to_abt_comm. Qed.

  Lemma subst_to_abt_comm : forall e rho,
      to_abt (subst rho e) = A.subst (map to_abt rho) (to_abt e).
  Proof. A.basis_util.prove_subst_to_abt_comm t map_shift_to_abt_comm. Qed.

  Lemma wf_to_abt : forall e n, wf n e <-> A.wf n (to_abt e).
  Proof. A.basis_util.prove_wf_to_abt. Qed.

  Lemma identity_subst_to_abt_comm :
    forall n, List.map to_abt (identity_subst n) = A.identity_subst n.
  Proof. A.basis_util.prove_identity_subst_to_abt_comm map_shift_to_abt_comm. Qed.

  Definition var := var.
  Arguments var /.
  Lemma var_to_abt : forall n, to_abt (var n) = A.var n.
  Proof. reflexivity. Qed.
End expr_basis.

Module expr.
  Include abt.abt_util expr_basis.
  Notation abs := expr_ast.abs.
  Notation app := expr_ast.app.
  Notation tyabs := expr_ast.tyabs.
  Notation tyapp := expr_ast.tyapp.
  Notation pack := expr_ast.pack.
  Notation unpack := expr_ast.unpack.
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

  | pack : forall n G e ty_interface ty_rep,
      type.wf n ty_rep -> 
      t n G e (type.subst (ty_rep :: type.identity_subst n) ty_interface) ->
      t n G (expr.pack e) (type.exist ty_interface)
  | unpack : forall n G e1 e2 ty1 ty2 ty2',
      t n G e1 (type.exist ty1) ->
      t (S n) (ty1 :: map (type.shift 0 1) G) e2 ty2 ->
      ty2 = type.shift 0 1 ty2' ->
      t n G (expr.unpack e1 e2) ty2'
  .

  Lemma t_type_wf :
    forall n G e ty,
      t n G e ty ->
      Forall (type.wf n) G ->
      type.wf n ty.
  Proof.
    induction 1; cbn in *; intros F; intuition.
    - now eapply Forall_nth; eauto.
    - apply IHt.
      rewrite Forall_map.
      eapply Forall_impl; try eassumption.
      intros ty' WF'.
      now apply type.wf_shift with (d := 1).
    - apply type.wf_subst.
      + simpl. now rewrite type.identity_subst_length in *.
      + constructor; auto.
        apply type.wf_identity_subst.
    - apply type.wf_subst_inv in H1.
      simpl in *. rewrite type.identity_subst_length in *.
      now rewrite Nat.max_r in * by omega.
    - subst ty2.
      assert (type.wf (S n) (type.shift 0 1 ty2')).
      {
        apply IHt2.
        constructor; auto.
        rewrite Forall_map.
        apply Forall_forall.
        intros ty' I.
        apply type.wf_shift with (d := 1).
        eapply Forall_forall; eauto.
      }

      apply type.wf_shift_inv with (c := 0) (d := 1) in H1.
      simpl in *.
      now rewrite Nat.sub_0_r in *.
  Qed.

  Lemma t_expr_wf :
    forall n G e ty,
      t n G e ty ->
      expr.wf (length G) e.
  Proof.
    induction 1; simpl in *; intuition.
    - apply nth_error_Some. congruence.
    - now rewrite map_length in *.
    - now rewrite map_length in *.
  Qed.
End has_type.

Module value.
  Inductive t : expr.t -> Prop :=
  | abs : forall e, t (expr.abs e)
  | tyabs : forall e, t (expr.tyabs e)
  | pack : forall e, t e -> t (expr.pack e)
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
  | pack : forall e e',
      t e e' ->
      t (expr.pack e) (expr.pack e')
  | unpack : forall e1 e1' e2,
      t e1 e1' ->
      t (expr.unpack e1 e2) (expr.unpack e1' e2)
  | packbeta : forall v e2,
      value.t v -> 
      t (expr.unpack (expr.pack v) e2) (expr.subst [v] e2)
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

  Lemma star_pack :
    forall e e',
      star e e' ->
      star (expr.pack e) (expr.pack e').
  Proof.
    intros e e' Star.
    induction Star.
    - constructor.
    - econstructor; [|apply IHStar]; eauto.
  Qed.

  Lemma star_unpack :
    forall e1 e1' e2,
      star e1 e1' ->
      star (expr.unpack e1 e2) (expr.unpack e1' e2).
  Proof.
    intros e1 e1' e2 Star.
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
    forall v,
      value.t v ->
      forall e',
      step.t v e' ->
      False.
  Proof.
    induction 1; intros e' Step; inversion Step; subst.
    eauto.
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
