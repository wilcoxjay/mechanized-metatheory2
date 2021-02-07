From mm Require Import util abt abtutil.

Module tyop.
  Inductive t' :=
  | arrow
  | all
  | exist
  | bool
  .
  Definition t := t'.

  Definition arity (op : t) : arity.t :=
    match op with
    | arrow => [0; 0]
    | all => [1]
    | exist => [1]
    | bool => []
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
  | tt
  | ff
  | If
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
    | tt => []
    | ff => []
    | If => [0; 0; 0]
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
  | bool : t
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
    | bool => A.op tyop.bool []
    end.

  Fixpoint of_abt (a : A.t) : t :=
    match a with
    | A.var n => var n
    | A.op tyop.arrow [A.bind 0 a1; A.bind 0 a2] => arrow (of_abt a1) (of_abt a2)
    | A.op tyop.all [A.bind 1 a'] => all (of_abt a')
    | A.op tyop.exist [A.bind 1 a'] => exist (of_abt a')
    | A.op tyop.bool [] => bool
    | _ => var 0 (* bogus *)
    end.

  Fixpoint shift c d (ty : t) : t :=
    match ty with
    | var alpha => var (if alpha <? c then alpha else alpha + d)
    | arrow ty1 ty2 => arrow (shift c d ty1) (shift c d ty2)
    | all ty' => all (shift (S c) d ty')
    | exist ty' => exist (shift (S c) d ty')
    | bool => bool
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
    | bool => bool
    end.

  Fixpoint wf n ty :=
    match ty with
    | var alpha => alpha < n
    | arrow ty1 ty2 => wf n ty1 /\ wf n ty2
    | all ty' => wf (S n) ty'
    | exist ty' => wf (S n) ty'
    | bool => True
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
   Include abt_util type_basis.
   Notation arrow := type_ast.arrow.
   Notation all := type_ast.all.
   Notation exist := type_ast.exist.
   Notation bool := type_ast.bool.

   Hint Resolve wf_shift' wf_subst : core.
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
  | tt : t
  | ff : t
  | If : t -> t -> t -> t
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
    | tt => A.op exprop.tt []
    | ff => A.op exprop.ff []
    | If e1 e2 e3 => A.op exprop.If [A.bind 0 (to_abt e1);
                                            A.bind 0 (to_abt e2);
                                            A.bind 0 (to_abt e3)]
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
    | A.op exprop.tt [] => tt
    | A.op exprop.ff [] => ff
    | A.op exprop.If [A.bind 0 a1; A.bind 0 a2; A.bind 0 a3] =>
      If (of_abt a1) (of_abt a2) (of_abt a3)
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
    | tt => tt
    | ff => ff
    | If e1 e2 e3 => If (shift c d e1) (shift c d e2) (shift c d e3)
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
    | tt => tt
    | ff => ff
    | If e1 e2 e3 => If (subst rho e1) (subst rho e2) (subst rho e3)
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
    | tt => True
    | ff => True
    | If e1 e2 e3 => wf n e1 /\ wf n e2 /\ wf n e3
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
  Include abt_util expr_basis.
  Notation abs := expr_ast.abs.
  Notation app := expr_ast.app.
  Notation tyabs := expr_ast.tyabs.
  Notation tyapp := expr_ast.tyapp.
  Notation pack := expr_ast.pack.
  Notation unpack := expr_ast.unpack.
  Notation tt := expr_ast.tt.
  Notation ff := expr_ast.ff.
  Notation If := expr_ast.If.
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

  | tt : forall n G,
      t n G expr.tt type.bool
  | ff : forall n G,
      t n G expr.ff type.bool
  | If : forall n G e1 e2 e3 ty,
      t n G e1 type.bool ->
      t n G e2 ty ->
      t n G e3 ty ->
      t n G (expr.If e1 e2 e3) ty
  .
  Hint Constructors t.

  Lemma t_type_wf :
    forall n G e ty,
      t n G e ty ->
      Forall (type.wf n) G ->
      type.wf n ty.
  Proof.
    induction 1; cbn in *; intros F; intuition.
    - now eapply Forall_nth_error; eauto.
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
      now rewrite Nat.max_r in * by lia.
    - subst ty2.
      auto using type.wf_shift_inv', type.wf_map_shift'.
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

  Lemma shift :
  forall n G1 G2 G3 e ty,
    has_type.t n (G1 ++ G3) e ty ->
    has_type.t n (G1 ++ G2 ++ G3) (expr.shift (length G1) (length G2) e) ty.
  Proof.
    intros n G1 G2 G3 e ty HT.
    revert G2.
    remember (G1 ++ G3) as G eqn:EG in *.
    revert G1 G3 EG.
    induction HT; intros G1 G3 EG G2; subst G; simpl; econstructor; eauto.
    - now rewrite nth_error_shift.
    - rewrite app_comm_cons.
      now apply IHHT.
    - specialize (IHHT (map (type.shift 0 1) G1) (map (type.shift 0 1) G3)
                       (ltac:(auto using map_app)) (map (type.shift 0 1) G2)).
      now rewrite !map_app, !map_length in *.
    - specialize (IHHT2 (ty1 :: map (type.shift 0 1) G1) (map (type.shift 0 1) G3)
                        ltac:(simpl; apply f_equal; apply map_app) (map (type.shift 0 1) G2)).
      cbn[length] in *.
      now rewrite !map_app, !map_length in *.
  Qed.

  Lemma shift' :
    forall n G e ty G',
      t n G e ty ->
      t n (G' ++ G) (expr.shift 0 (List.length G') e) ty.
  Proof.
    intros.
    now apply shift with (G1 := []).
  Qed.

  Lemma shift_cons :
  forall n G e ty ty',
    has_type.t n G e ty ->
    has_type.t n (ty' :: G) (expr.shift 0 1 e) ty.
  Proof.
    intros n G e ty ty' HT.
    now apply shift' with (G' := [ty']).
  Qed.

  Lemma tyshift :
    forall n c d G e ty,
      c <= n ->
      Forall (type.wf n) G ->
      has_type.t n G e ty ->
      has_type.t (d + n) (map (type.shift c d) G) e (type.shift c d ty).
  Proof.
    intros n c d G e ty LE WFG HT.
    revert c LE.
    induction HT; intros c LE; eauto.
    - constructor.
      now rewrite nth_error_map, H.
    - simpl in *. constructor; auto using type.wf_shift.
    - simpl. econstructor.
      rewrite plus_n_Sm.
      rewrite type.map_shift_map_shift'.
      now auto using type.wf_map_shift' with *.
    - simpl in *.
      specialize (IHHT WFG c).

      rewrite type.shift_subst
      by (simpl; rewrite type.identity_subst_length;
          apply t_type_wf in HT; auto).

      simpl in *.
      apply has_type.tyapp with (ty := type.shift c d ty) in IHHT;
        [|now auto using type.wf_shift| assumption].

      rewrite type.subst_shift_cons_identity_subst in IHHT; auto.
      now apply t_type_wf in HT; [|assumption].
    - simpl.
      specialize (IHHT WFG c LE).
      rewrite type.shift_subst in IHHT
      by (simpl; rewrite type.identity_subst_length;
          now eauto using t_type_wf, type.wf_subst_id_inv).
      apply pack with (ty_rep := type.shift c d ty_rep); [now auto using type.wf_shift|].

      rewrite type.subst_shift_cons_identity_subst; auto.
      clear - HT WFG.
      apply t_type_wf in HT; [|assumption].
      apply type.wf_subst_inv in HT.
      simpl in *.
      rewrite type.identity_subst_length in *.
      now rewrite Nat.max_r in * by lia.
    - cbn[type.shift] in *.
      assert (type.wf (S n) ty1) as WFty1 by now apply t_type_wf in HT1.
      econstructor.
      now apply IHHT1.

      specialize (IHHT2 (type.wf_cons WFty1 WFG) (S c) ltac:(lia)).
      rewrite Nat.add_succ_r in IHHT2.
      cbn[map] in IHHT2.
      rewrite type.map_shift_map_shift'.
      apply IHHT2.

      subst ty2.
      now rewrite type.shift_shift'.
  Qed.

  Lemma tyshift' :
    forall n G e ty,
      Forall (type.wf n) G ->
      has_type.t n G e ty ->
      has_type.t (S n) (map (type.shift 0 1) G) e (type.shift 0 1 ty).
  Proof.
    intros n G e ty HT.
    apply tyshift with (n := n) (d := 1); auto.
    lia.
  Qed.

  Lemma subst :
    forall n G e ty,
      t n G e ty ->
      Forall (type.wf n) G ->
      forall G' rho,
        Forall (type.wf n) G' ->
        List.Forall2 (t n G') rho G ->
        t n G' (expr.subst rho e) ty.
  Proof.
    induction 1; intros WFG G' rho WFG' F; cbn [expr.subst]; eauto.
    - destruct (Forall2_nth_error2 F H) as [z [Hz Ht]].
      cbn.
      unfold expr.t in *. (* ugh *)
      now rewrite Hz.
    - eauto 10 using shift_cons, Forall2_impl, Forall2_map_l.
    - econstructor.
      apply IHt;
        eauto using Forall_map_bwd, Forall_impl, type.wf_shift'.
      eauto using Forall2_map_r, Forall2_impl, tyshift'.
    - econstructor; eauto.
      apply t_type_wf in H; [|assumption].
      apply IHt2.
      + eauto using Forall_map_bwd, Forall_impl, type.wf_shift'.
      + eauto using Forall_map_bwd, Forall_impl, type.wf_shift'.
      + eauto 10 using Forall2_map_bwd, Forall2_impl, tyshift', shift_cons.
  Qed.

  Lemma t_type_wf_S_all :
    forall n ty,
      type.wf n (type.all ty) ->
      type.wf (S n) ty.
  Proof.
    auto.
  Qed.

  Lemma t_type_wf_S_exist :
    forall n ty,
      type.wf n (type.exist ty) ->
      type.wf (S n) ty.
  Proof.
    auto.
  Qed.
  Hint Resolve t_type_wf_S_all t_type_wf_S_exist : core.

  Lemma tysubst :
    forall n G e ty,
      t n G e ty ->
      Forall (type.wf n) G ->
      forall n' delta,
        length delta = n ->
        Forall (type.wf n') delta ->
        t n' (map (type.subst delta) G) e (type.subst delta ty).
  Proof.
    induction 1; intros FG n' delta E Fd; subst n; eauto.
    - constructor.
      now rewrite nth_error_map, H.
    - cbn [type.subst map] in *.
      auto.
    - cbn [type.subst].
      forward IHt;
        [eauto using Forall_map_bwd, Forall_impl, type.wf_shift'|].
      constructor.
      specialize (IHt (S n') (type.descend 1 delta)).
      forward IHt; [now simpl; rewrite map_length|].
      forward IHt; [now auto using type.descend_wf1|].
      eqapply IHt.
      rewrite !map_map.
      eauto using map_ext_Forall, Forall_impl, type.subst_descend_shift_shift_subst.
    - forward IHt; [assumption|].
      specialize (IHt n' delta eq_refl Fd).
      cbn [type.subst] in *.
      rewrite <- type.descend_1 in *.
      apply has_type.tyapp with (ty := type.subst delta ty) in IHt; [|now auto].
      assert (type.wf (S (length delta)) ty_body) by eauto using t_type_wf.
      eqapply IHt.
      rewrite !type.subst_subst
        by (cbn [length];
            rewrite ?type.identity_subst_length, ?type.descend_length1;
            auto using type.descend_wf1, type.wf_identity_subst).
      cbn.
      now rewrite map_map, type.map_subst_cons_identity_subst_shift_1.
    - cbn [type.subst].
      rewrite <- type.descend_1.
      apply has_type.pack with (ty_rep := type.subst delta ty_rep); [now auto|].
      forward IHt; [assumption|].
      specialize (IHt _ _ eq_refl Fd).
      assert (type.wf (S (length delta)) ty_interface) as WFint
          by eauto using type.wf_subst_id_inv, t_type_wf.
      eqapply IHt.
      rewrite !type.subst_subst
        by (cbn [length];
            rewrite ?type.identity_subst_length, ?type.descend_length1;
            auto using type.descend_wf1, type.wf_identity_subst).
      cbn.
      now rewrite map_map, type.map_subst_cons_identity_subst_shift_1.
    - forward IHt2; [now eauto using t_type_wf, type.wf_map_shift'|].
      specialize (IHt2 (S n') (type.descend 1 delta)).
      forward IHt2; [now apply type.descend_length1|].
      forward IHt2; [now auto using type.descend_wf1|].
      apply unpack
        with (ty1 := type.subst (type.descend 1 delta) ty1)
             (ty2 := type.subst (type.descend 1 delta) ty2).
      + cbn [type.subst] in IHt1.
        now apply IHt1; auto.
      + eqapply IHt2.
        cbn [map].
        f_equal.
        rewrite !map_map.
        apply map_ext_Forall.
        eapply Forall_impl; [| apply FG].
        intros t WF.
        rewrite type.subst_descend_shift by assumption.
        now rewrite type.shift_subst by assumption.
      + subst ty2.
        assert (type.wf (length delta) ty2')
          by eauto using t_type_wf, type.wf_shift_inv'.
        rewrite type.subst_descend_shift by assumption.
        now rewrite type.shift_subst by assumption.
  Qed.
End has_type.

Module value.
  Inductive t : expr.t -> Prop :=
  | abs : forall e, t (expr.abs e)
  | tyabs : forall e, t (expr.tyabs e)
  | pack : forall e, t e -> t (expr.pack e)
  | tt : t expr.tt
  | ff : t expr.ff
  .
  Hint Constructors t : core.
End value.

Module step.
  Inductive t : expr.t -> expr.t -> Prop :=
  | beta : forall body v,
      value.t v ->
      t (expr.app (expr.abs body) v) (expr.subst [v] body)
  | app1 : forall e1 e1' e2,
      t e1 e1' ->
      t (expr.app e1 e2) (expr.app e1' e2)
  | app2 : forall e1 e2 e2',
      value.t e1 ->
      t e2 e2' ->
      t (expr.app e1 e2) (expr.app e1 e2')
  | tybeta : forall body,
      t (expr.tyapp (expr.tyabs body))
        body
  | tyapp : forall e e' ,
      t e e' ->
      t (expr.tyapp e) (expr.tyapp e')
  | packbeta : forall v e2,
      value.t v ->
      t (expr.unpack (expr.pack v) e2) (expr.subst [v] e2)
  | pack : forall e e',
      t e e' ->
      t (expr.pack e) (expr.pack e')
  | unpack : forall e1 e1' e2,
      t e1 e1' ->
      t (expr.unpack e1 e2) (expr.unpack e1' e2)
  | IfT : forall e2 e3,
      t (expr.If expr.tt e2 e3) e2
  | IfF : forall e2 e3,
      t (expr.If expr.ff e2 e3) e3
  | If : forall e1 e1' e2 e3,
      t e1 e1' ->
      t (expr.If e1 e2 e3) (expr.If e1' e2 e3)
  .
  Hint Constructors t : core.

  Definition star : expr.t -> expr.t -> Prop := clos_refl_trans_n1 _ t.

  Lemma star_refl :
    forall e,
      star e e.
  Proof.
    constructor.
  Qed.

  Hint Resolve star_refl : core.

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

  Lemma star_If :
    forall e1 e1' e2 e3,
      star e1 e1' ->
      star (expr.If e1 e2 e3) (expr.If e1' e2 e3).
  Proof.
    intros e1 e1' e2 e3 Star.
    revert e2 e3.
    induction Star; intros e2 e3.
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

  Lemma det :
    forall e e1 e2,
      t e e1 ->
      t e e2 ->
      e1 = e2.
  Proof.
    intros e e1 e2 Step1 Step2.
    generalize dependent e2.
    induction Step1; intros e4 Step4; inversion Step4; subst; try reflexivity;
      try solve [ exfalso; eauto using value ];
      try match goal with
          | [ H : _ |- _ ] => solve [inversion H; try solve [ exfalso; eauto using value ]]
          end;
      auto using f_equal, f_equal2, f_equal3.
  Qed.

  Lemma star_det :
    forall e v1 v2,
      value.t v1 ->
      value.t v2 ->
      star e v1 ->
      star e v2 ->
      v1 = v2.
  Proof.
    intros e v1 v2 V1 V2 Star1 Star2.
    apply clos_rtn1_rt in Star1.
    apply clos_rtn1_rt in Star2.
    apply clos_rt_rt1n in Star1.
    apply clos_rt_rt1n in Star2.
    induction Star1; invc Star2.
    - reflexivity.
    - exfalso. eauto using value.
    - exfalso. eauto using value.
    - assert (y = y0) by eauto using det.
      subst y0.
      auto.
  Qed.
End step.

Module type_safety.
  Definition safe (e : expr.t) :=
    value.t e \/
    exists e',
      step.t e e'.

  Lemma canonical_forms_arrow :
    forall n G e ty1 ty2,
      has_type.t n G e (type.arrow ty1 ty2) ->
      value.t e ->
      exists e',
        e = expr.abs e'.
  Proof.
    intros n G e ty1 ty2 HT V.
    invc HT; invc V; eauto.
  Qed.

  Lemma canonical_forms_all :
    forall n G e ty,
      has_type.t n G e (type.all ty) ->
      value.t e ->
      exists e',
        e = expr.tyabs e'.
  Proof.
    intros n G e ty HT V.
    invc HT; invc V; eauto.
  Qed.

  Lemma canonical_forms_exist :
    forall n G e ty,
      has_type.t n G e (type.exist ty) ->
      value.t e ->
      exists e',
        e = expr.pack e'.
  Proof.
    intros n G e ty HT V.
    invc HT; invc V; eauto.
  Qed.

  Lemma canonical_forms_bool :
    forall n G e,
      has_type.t n G e type.bool ->
      value.t e ->
      e = expr.tt \/ e = expr.ff.
  Proof.
    intros n G e HT V.
    invc HT; invc V; auto.
  Qed.

  Lemma progress :
    forall e ty,
      has_type.t 0 [] e ty ->
      safe e.
  Proof.
    intros e ty HT.
    remember [] as G eqn:EG in HT.
    remember 0 as n eqn:EN in HT.
    revert EN EG.
    induction HT; intros EN EG; subst n G;
      try solve [repeat econstructor];
      repeat match goal with
             | [ H : _ |- _ ] => specialize (H eq_refl)
             end.
    - destruct x; discriminate.
    - invc IHHT1; [invc IHHT2|];
        try solve [firstorder; unfold safe; eauto].
      apply canonical_forms_arrow in HT1; [|assumption].
      destruct HT1 as [b1 ?].
      subst e1.
      unfold safe.
      eauto.
    - invc IHHT; try solve [firstorder; unfold safe; eauto].
      apply canonical_forms_all in HT; [|assumption].
      destruct HT as [b ?].
      subst e.
      unfold safe.
      eauto.
    - destruct IHHT as [|[e' Step]];
        unfold safe; eauto.
    - destruct IHHT1 as [V|]; [|firstorder; unfold safe; now eauto].
      apply canonical_forms_exist in HT1; [|assumption].
      destruct HT1 as [e' ?]. subst e1.
      invc V.
      unfold safe.
      eauto.
    - destruct IHHT1; [|firstorder; unfold safe; now eauto].
      apply canonical_forms_bool in HT1; [|assumption].
      destruct HT1; subst e1; unfold safe; eauto.
  Qed.

  Lemma preservation :
    forall e e' ty,
      has_type.t 0 [] e ty ->
      step.t e e' ->
      has_type.t 0 [] e' ty.
  Proof.
    intros e e' ty HT S.
    remember [] as G eqn:EG in HT.
    remember 0 as n eqn:EN in HT.
    revert EN EG e' S.
    induction HT; intros EN EG e' S; subst n G; invc S; auto;
      try solve [econstructor; eauto].
    - invc HT1.
      eauto using has_type.subst.
    - invc HT.
      apply has_type.tysubst with (G := []) (n := 1);
        auto using type.wf_identity_subst.
    - assert (type.wf 1 ty1).
      {
        eapply has_type.t_type_wf in HT1.
        assumption.
        constructor.
      }
      assert (type.wf 0 ty2').
      {
        eapply has_type.t_type_wf in HT2.
        now auto using type.wf_shift_inv'.
        constructor.
        assumption.
        constructor.
      }
      invc HT1.
      cbn in *.
      eapply has_type.subst.
      eapply has_type.tysubst with (delta := [ty_rep]) in HT2.
      eqapply HT2.
      all: cbn; auto using type.wf_subst.
      now rewrite type.subst_shift_singleton.
  Qed.

  Theorem type_safety :
    forall e e' ty,
      has_type.t 0 [] e ty ->
      step.star e e' ->
      safe e'.
  Proof.
    intros e e' ty HT S.
    generalize dependent ty.
    apply clos_rtn1_rt in S.
    apply clos_rt_rt1n in S.
    induction S; intros.
    - eauto using progress.
    - eauto using preservation.
  Qed.
End type_safety.
Print Assumptions type_safety.type_safety.
