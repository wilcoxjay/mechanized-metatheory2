From mm Require Import util abt abtutil map.

Module exprop.
  Inductive t' :=
  | abs
  | app
  | tt
  | ff
  | If
  | ref
  | deref
  | assign
  | addr (a : nat)
  .
  Definition t := t'.

  Definition arity (op : t) : arity.t :=
    match op with
    | abs => [1]
    | app => [0; 0]
    | tt => []
    | ff => []
    | If => [0; 0; 0]
    | ref => [0]
    | deref => [0]
    | assign => [0; 0]
    | addr _ => []
    end.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
    apply eq_nat_dec.
  Defined.
End exprop.

Module type.
  Inductive t :=
  | bool
  | arrow : t -> t -> t
  | ref : t -> t
  .
End type.

Module expr_abt := abt.abt exprop.

Module expr_ast.
  Inductive t :=
  | var (x : nat) : t
  | abs : t -> t
  | app : t -> t -> t
  | tt : t
  | ff : t
  | If : t -> t -> t -> t
  | addr (a : nat) : t
  | ref : t -> t
  | deref : t -> t
  | assign : t -> t -> t
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
    | tt => A.op exprop.tt []
    | ff => A.op exprop.ff []
    | If e1 e2 e3 => A.op exprop.If [A.bind 0 (to_abt e1);
                                            A.bind 0 (to_abt e2);
                                            A.bind 0 (to_abt e3)]
    | addr n => A.op (exprop.addr n) []
    | ref e' => A.op exprop.ref [A.bind 0 (to_abt e')]
    | deref e' => A.op exprop.deref [A.bind 0 (to_abt e')]
    | assign e1 e2 => A.op exprop.assign [A.bind 0 (to_abt e1); A.bind 0 (to_abt e2)]
    end.

  Fixpoint of_abt (a : A.t) : t :=
    match a with
    | A.var n => var n
    | A.op exprop.abs [A.bind 1 a'] => abs (of_abt a')
    | A.op exprop.app [A.bind 0 a1; A.bind 0 a2] => app (of_abt a1) (of_abt a2)
    | A.op exprop.tt [] => tt
    | A.op exprop.ff [] => ff
    | A.op exprop.If [A.bind 0 a1; A.bind 0 a2; A.bind 0 a3] =>
      If (of_abt a1) (of_abt a2) (of_abt a3)
    | A.op (exprop.addr n) [] => addr n
    | A.op exprop.ref [A.bind 0 a'] => ref (of_abt a')
    | A.op exprop.deref [A.bind 0 a'] => deref (of_abt a')
    | A.op exprop.assign [A.bind 0 a1; A.bind 0 a2] => assign (of_abt a1) (of_abt a2)
    | _ => var 0 (* bogus *)
    end.

  Fixpoint t_map ov c (e : t) : t :=
    match e with
    | var x => ov c x
    | abs e' => abs (t_map ov (S c) e')
    | app e1 e2 => app (t_map ov c e1) (t_map ov c e2)
    | tt => tt
    | ff => ff
    | If e1 e2 e3 => If (t_map ov c e1) (t_map ov c e2) (t_map ov c e3)
    | addr n => addr n
    | ref e' => ref (t_map ov c e')
    | deref e' => deref (t_map ov c e')
    | assign e1 e2 => assign (t_map ov c e1) (t_map ov c e2)
    end.

  Fixpoint shift c d (e : t) : t :=
    match e with
    | var x => var (if x <? c then x else x + d)
    | abs e' => abs (shift (S c) d e')
    | app e1 e2 => app (shift c d e1) (shift c d e2)
    | tt => tt
    | ff => ff
    | If e1 e2 e3 => If (shift c d e1) (shift c d e2) (shift c d e3)
    | addr n => addr n
    | ref e' => ref (shift c d e')
    | deref e' => deref (shift c d e')
    | assign e1 e2 => assign (shift c d e1) (shift c d e2)
    end.

  Fixpoint subst rho e :=
    match e with
    | var x => match nth_error rho x with
                  | Some e' => e'
                  | None => e
                  end
    | abs e' => abs (subst (var 0 :: map (shift 0 1) rho) e')
    | app e1 e2 => app (subst rho e1) (subst rho e2)
    | tt => tt
    | ff => ff
    | If e1 e2 e3 => If (subst rho e1) (subst rho e2) (subst rho e3)
    | addr n => addr n
    | ref e' => ref (subst rho e')
    | deref e' => deref (subst rho e')
    | assign e1 e2 => assign (subst rho e1) (subst rho e2)
    end.

  Fixpoint wf n e :=
    match e with
    | var x => x < n
    | abs e' => wf (S n) e'
    | app e1 e2 => wf n e1 /\ wf n e2
    | tt => True
    | ff => True
    | If e1 e2 e3 => wf n e1 /\ wf n e2 /\ wf n e3
    | addr _ => True
    | ref e' => wf n e'
    | deref e' => wf n e'
    | assign e1 e2 => wf n e1 /\ wf n e2
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

  Lemma t_map_to_abt_comm : forall ov e c,
      to_abt (t_map ov c e) = A.t_map (fun c x => to_abt (ov c x)) c (to_abt e).
  Proof. A.basis_util.prove_t_map_to_abt_comm. Qed.

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
  Notation tt := expr_ast.tt.
  Notation ff := expr_ast.ff.
  Notation If := expr_ast.If.
  Notation addr := expr_ast.addr.
  Notation ref := expr_ast.ref.
  Notation deref := expr_ast.deref.
  Notation assign := expr_ast.assign.
End expr.

Module has_type.
  Inductive t : NatMap.t type.t -> list type.t -> expr.t -> type.t -> Prop :=
  | var : forall S G x ty,
      List.nth_error G x = Some ty ->
      t S G (expr.var x) ty
  | tt : forall S G,
      t S G expr.tt type.bool
  | ff : forall S G,
      t S G expr.ff type.bool
  | abs : forall S G e ty1 ty2,
      t S (ty1 :: G) e ty2 ->
      t S G (expr.abs e) (type.arrow ty1 ty2)
  | app : forall S G e1 e2 ty1 ty2,
      t S G e1 (type.arrow ty1 ty2) ->
      t S G e2 ty1 ->
      t S G (expr.app e1 e2) ty2
  | If : forall S G e1 e2 e3 ty,
      t S G e1 type.bool ->
      t S G e2 ty ->
      t S G e3 ty ->
      t S G (expr.If e1 e2 e3) ty
  | addr : forall S G a ty,
      NatMap.get a S = Some ty ->
      t S G (expr.addr a) ty
  | ref : forall S G e ty,
      t S G e ty ->
      t S G (expr.ref e) (type.ref ty)
  | deref : forall S G e ty,
      t S G e (type.ref ty) ->
      t S G (expr.deref e) ty
  | assign : forall S G e1 e2 ty,
      t S G e1 (type.ref ty) ->
      t S G e2 ty ->
      t S G (expr.assign e1 e2) type.bool
  .

  Lemma wf :
    forall S G e ty,
      t S G e ty ->
      expr.wf (List.length G) e.
  Proof.
    induction 1; simpl in *; intuition.
    pose proof nth_error_Some G x. intuition congruence.
  Qed.

  Lemma shift :
    forall S G e ty,
      t S G e ty ->
      forall G1 G2 G',
        G1 ++ G2 = G ->
        t S (G1 ++ G' ++ G2) (expr.shift (List.length G1) (List.length G') e) ty.
  Proof.
    induction 1; intros G1 G2 G' E; subst G; simpl; try solve [econstructor; eauto].
    - constructor.
      do_ltb.
      + now rewrite nth_error_app1 in * by assumption.
      + rewrite !nth_error_app2 in * by lia.
        now do_app2_minus.
    - cbn [expr.shift].
      constructor.
      change (ty1 :: G1 ++ G' ++ G2) with ((ty1 :: G1) ++ G' ++ G2).
      now apply IHt.
  Qed.

  Lemma shift' :
    forall S G e ty G',
      t S G e ty ->
      t S (G' ++ G) (expr.shift 0 (List.length G') e) ty.
  Proof.
    intros.
    now apply shift with (G := G) (G1 := []).
  Qed.

  Lemma shift_cons :
    forall S G e ty ty0,
      t S G e ty ->
      t S (ty0 :: G) (expr.shift 0 1 e) ty.
  Proof.
    intros.
    now apply shift' with (G' := [ty0]).
  Qed.

  Lemma subst :
    forall S G e ty,
      t S G e ty ->
      forall G' rho,
        List.Forall2 (t S G') rho G ->
        t S G' (expr.subst rho e) ty.
  Proof.
    induction 1; intros G' rho F; cbn [expr.subst]; try solve [econstructor; eauto].
    - destruct (Forall2_nth_error2 F H) as [z [Hz Ht]].
      unfold expr.t in *.
      simpl.
      now rewrite Hz.
    - constructor.
      apply IHt.
      constructor.
      + now constructor.
      + apply Forall2_map_l.
        apply Forall2_from_forall.
        * now erewrite Forall2_length by eauto.
        * intros.
          apply shift_cons.
          eapply (Forall2_nth_error F); eauto.
  Qed.
End has_type.

Module value.
  Inductive t : expr.t -> Prop :=
  | tt : t expr.tt
  | ff : t expr.ff
  | abs : forall e, t (expr.abs e)
  | addr : forall a, t (expr.addr a)
  .
End value.

Module step.
  Inductive t : NatMap.t expr.t * expr.t -> NatMap.t expr.t * expr.t -> Prop :=
  | beta : forall h e1 e2,
      value.t e2 ->
      t (h, expr.app (expr.abs e1) e2)
        (h, expr.subst [e2] e1)
  | app1 : forall h h' e1 e1' e2,
      t (h, e1) (h', e1') ->
      t (h, expr.app e1 e2) (h', expr.app e1' e2)
  | app2  : forall h h' e1 e2 e2',
      value.t e1 ->
      t (h, e2) (h', e2') ->
      t (h, expr.app e1 e2) (h', expr.app e1 e2')
  | IfT : forall h e2 e3,
      t (h, expr.If expr.tt e2 e3) (h, e2)
  | IfF : forall h e2 e3,
      t (h, expr.If expr.ff e2 e3) (h, e3)
  | If : forall h h' e1 e1' e2 e3,
      t (h, e1) (h', e1') ->
      t (h, expr.If e1 e2 e3) (h', expr.If e1' e2 e3)
  | alloc : forall h a v,
      NatMap.get a h = None ->
      value.t v ->
      t (h, expr.ref v) (NatMap.set a v h, expr.addr a)
  | ref : forall h h' e e',
      t (h, e) (h', e') ->
      t (h, expr.ref e) (h', expr.ref e')
  | deref_beta :
      forall h a v,
        NatMap.get a h = Some v ->
        t (h, expr.deref (expr.addr a)) (h, v)
  | deref : forall h h' e e',
      t (h, e) (h', e') ->
      t (h, expr.deref e) (h', expr.deref e')
  | assign_beta :
      forall h a v,
        NatMap.get a h <> None ->
        value.t v ->
        t (h, expr.assign (expr.addr a) v) (NatMap.set a v h, expr.tt)
  | assign1 : forall h h' e1 e1' e2,
      t (h, e1) (h', e1') ->
      t (h, expr.assign e1 e2) (h', expr.assign e1' e2)
  | assign2 : forall h h' v e2 e2',
        value.t v ->
        t (h, e2) (h', e2') ->
        t (h, expr.assign v e2) (h', expr.assign v e2')
  .
  Global Hint Constructors t : core.

  Definition star : _ -> _ -> Prop := clos_refl_trans_n1 _ t.

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
    forall h h' e1 e1' e2,
      star (h, e1) (h', e1') ->
      star (h, expr.app e1 e2) (h', expr.app e1' e2).
  Proof.
    intros h h' e1 e1' e2 Star.
    remember (h, e1) as c.
    remember (h', e1') as c'.
    revert h h' e1 e1' Heqc Heqc' e2.
    induction Star; intros h h' e1 e1' Heqc Heqc' e2; subst.
    - invc Heqc'. constructor.
    - destruct y as [h0 e0].
      econstructor; [|apply IHStar].
      all: eauto.
  Qed.

  Lemma star_app2 :
    forall h h' e1 e2 e2',
      value.t e1 ->
      star (h, e2) (h', e2') ->
      star (h, expr.app e1 e2) (h', expr.app e1 e2').
  Proof.
    intros h h' e1 e2 e2' Val1 Star.
    remember (h, e2) as c.
    remember (h', e2') as c'.
    revert h h' e2 e2' Heqc Heqc' e1 Val1.
    induction Star; intros h h' e2 e2' Heqc Heqc' e1 Val1; subst.
    - invc Heqc'. constructor.
    - destruct y as [h0 e0].
      econstructor; [apply app2 | apply IHStar]; eauto.
  Qed.

  Lemma star_If :
    forall h h' e1 e1' e2 e3,
      star (h, e1) (h', e1') ->
      star (h, expr.If e1 e2 e3) (h', expr.If e1' e2 e3).
  Proof.
    intros h h' e1 e1' e2 e3 Star.
    remember (h, e1) as c.
    remember (h', e1') as c'.
    revert h h' e1 e1' Heqc Heqc' e2 e3.
    induction Star; intros h h' e1 e1' Heqc Heqc' e2 e3; subst.
    - invc Heqc'. constructor.
    - destruct y as [h0 e0].
      econstructor; [apply If|apply IHStar]; eauto.
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

  Lemma star_refl :
    forall e,
      star e e.
  Proof.
    constructor.
  Qed.

  Global Hint Resolve star_app2 star_app1 star_refl : core.

  Lemma value :
    forall v,
      value.t v ->
      forall h h' e',
        step.t (h, v) (h', e') ->
        False.
  Proof.
    induction 1; intros h h' e' Step; inversion Step; subst.
  Qed.

  Lemma star_value :
    forall h h' v e',
      value.t v ->
      step.star (h, v) (h', e') ->
      e' = v.
  Proof.
    intros h h' v e' Val Star.
    apply clos_rtn1_rt in Star.
    apply clos_rt_rt1n in Star.
    inversion Star; subst; auto.
    destruct y as [h0 e0].
    exfalso; eauto using value.
  Qed.

(*
  Lemma det :
    forall e1 e2 e2',
      t e1 e2 ->
      t e1 e2' ->
      e2 = e2'.
  Proof.
    intros e1 e2 e2' Step.
    revert e2'.
    induction Step; intros e2'' Step'; invc Step'; auto;
      try match goal with
          | [ H : _ |- _ ] => solve [invc H]
          end;
      try solve [exfalso; eauto using value];
      f_equal; auto.
  Qed.

  Lemma star_step_det :
    forall e1 e2 e2',
      star e1 e2 ->
      t e1 e2' ->
      e1 = e2 \/ star e2' e2.
  Proof.
    intros e1 e2 e2' Star Step.
    apply clos_rtn1_rt in Star.
    apply clos_rt_rt1n in Star.
    invc Star; auto.
    right.
    assert (y = e2') by eauto using det. subst y.
    apply clos_rt_rtn1.
    apply clos_rt1n_rt.
    auto.
  Qed.

  Lemma star_det :
    forall e1 e2 e2',
      star e1 e2 ->
      star e1 e2' ->
      star e2 e2' \/ star e2' e2.
  Proof.
    intros e1 e2 e2' Star Star'.
    revert e2' Star'.
    induction Star; intros e2' Star'.
    - auto.
    - specialize (IHStar _ Star'). clear Star'.
      intuition.
      + pose proof star_step_det _ _ _ H0 H.
        intuition.
        subst. right. econstructor. eauto. constructor.
      + right. econstructor. eauto. auto.
  Qed.

  Lemma star_det_value :
    forall e v v',
      step.star e v ->
      step.star e v' ->
      value.t v ->
      value.t v' ->
      v = v'.
  Proof.
    intros e v v' Star Star' Val Val'.
    pose proof star_det _ _ _ Star Star'; clear Star Star'.
    destruct H as [H|H];
      eapply star_value in H; eauto.
  Qed.
*)
End step.
