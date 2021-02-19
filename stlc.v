From mm Require Import util abt abtutil.

Module exprop.
  Inductive t' :=
  | abs
  | app
  | tt
  | ff
  | If
  .
  Definition t := t'.

  Definition arity (op : t) : arity.t :=
    match op with
    | abs => [1]
    | app => [0; 0]
    | tt => []
    | ff => []
    | If => [0; 0; 0]
    end.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
  Defined.
End exprop.

Module type.
  Inductive t :=
  | bool
  | arrow : t -> t -> t
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
    end.

  Fixpoint shift c d (e : t) : t :=
    match e with
    | var x => var (if x <? c then x else x + d)
    | abs e' => abs (shift (S c) d e')
    | app e1 e2 => app (shift c d e1) (shift c d e2)
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
    | tt => tt
    | ff => ff
    | If e1 e2 e3 => If (subst rho e1) (subst rho e2) (subst rho e3)
    end.

  Fixpoint wf n e :=
    match e with
    | var x => x < n
    | abs e' => wf (S n) e'
    | app e1 e2 => wf n e1 /\ wf n e2
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
End expr.


Module has_type.
  Inductive t : list type.t -> expr.t -> type.t -> Prop :=
  | var : forall G x ty,
      List.nth_error G x = Some ty ->
      t G (expr.var x) ty
  | tt : forall G,
      t G expr.tt type.bool
  | ff : forall G,
      t G expr.ff type.bool
  | abs : forall G e ty1 ty2,
      t (ty1 :: G) e ty2 ->
      t G (expr.abs e) (type.arrow ty1 ty2)
  | app : forall G e1 e2 ty1 ty2,
      t G e1 (type.arrow ty1 ty2) ->
      t G e2 ty1 ->
      t G (expr.app e1 e2) ty2
  | If : forall G e1 e2 e3 ty,
      t G e1 type.bool ->
      t G e2 ty ->
      t G e3 ty ->
      t G (expr.If e1 e2 e3) ty
  .
  Hint Constructors t : core.

  Lemma wf :
    forall G e ty,
      t G e ty ->
      expr.wf (List.length G) e.
  Proof.
    induction 1; simpl in *; intuition.
    pose proof nth_error_Some G x. intuition congruence.
  Qed.

  Definition extends (G' G : list type.t) : Prop :=
    exists G_pre,
      G' = G_pre ++ G.

  Lemma t_map :
    forall R ov,
      (forall G G' c' x ty, R G G' c' -> nth_error G x = Some ty -> t G' (ov c' x) ty) ->
      (forall G G' c' ty,
          R G G' c' ->
          R (ty :: G) (ty :: G') (S c')) ->
    forall G e ty,
      t G e ty ->
      forall G' c',
        R G G' c' ->
        t G' (expr.t_map ov c' e) ty.
  Proof.
    intros R ov NE Hext.
    induction 1; intros G' c' HR; cbn; try solve[constructor; auto].
    - eauto.
    - econstructor; eauto.
  Qed.

  Lemma shift :
    forall G e ty,
      t G e ty ->
      forall G1 G2 G',
        G1 ++ G2 = G ->
        t (G1 ++ G' ++ G2) (expr.shift (List.length G1) (List.length G') e) ty.
  Proof.
    intros G e ty HT G1 G2 G' EG.
    rewrite <- expr.shift_via_t_map_is_shift.
    unfold expr.shift_via_t_map.
    apply t_map with (R := fun G3 G'3 c'3 => exists G_pre,
                               [/\ G3 = G_pre ++ G1 ++ G2
                                , G'3 = G_pre ++ G1 ++ G' ++ G2
                                & c'3 = length (G_pre ++ G1)])
                     (G := G); auto.
    - intros G0 G'0 c' x ty0 [G_pre [? ? ?]] NE.
      subst.
      unfold expr.shift_onvar.
      rewrite app_assoc in NE.
      rewrite <- nth_error_shift with (l2 := G') in NE.
      destruct (Nat.ltb_spec x (length (G_pre ++ G1))); constructor;
        rewrite <- app_assoc in NE; auto.
    - intros G0 G'0 c' ty0 [G_pre [? ? ?]].
      exists (ty0 :: G_pre). cbn; split; auto; try congruence.
    - subst G.
      exists [].
      auto.
  Qed.

  Lemma shift_old :
    forall G e ty,
      t G e ty ->
      forall G1 G2 G',
        G1 ++ G2 = G ->
        t (G1 ++ G' ++ G2) (expr.shift (List.length G1) (List.length G') e) ty.
  Proof.
    induction 1; intros G1 G2 G' E; subst G.
    - constructor.
      do_ltb.
      + now rewrite nth_error_app1 in * by assumption.
      + rewrite !nth_error_app2 in * by lia.
        now do_app2_minus.
    - constructor.
    - constructor.
    - cbn [expr.shift].
      constructor.
      change (ty1 :: G1 ++ G' ++ G2) with ((ty1 :: G1) ++ G' ++ G2).
      now apply IHt.
    - simpl. econstructor.
      + now apply IHt1.
      + now apply IHt2.
    - simpl. econstructor.
      + now apply IHt1.
      + now apply IHt2.
      + now apply IHt3.
  Qed.

  Lemma shift' :
    forall G e ty G',
      t G e ty ->
      t (G' ++ G) (expr.shift 0 (List.length G') e) ty.
  Proof.
    intros.
    now apply shift with (G := G) (G1 := []).
  Qed.

  Lemma shift_cons :
    forall G e ty ty0,
      t G e ty ->
      t (ty0 :: G) (expr.shift 0 1 e) ty.
  Proof.
    intros.
    now apply shift' with (G' := [ty0]).
  Qed.

  Lemma subst :
    forall G e ty,
      t G e ty ->
      forall G' rho,
        List.Forall2 (t G') rho G ->
        t G' (expr.subst rho e) ty.
  Proof.
    induction 1; intros G' rho F; cbn [expr.subst].
    - destruct (Forall2_nth_error2 F H) as [z [Hz Ht]].
      unfold expr.t in *.
      simpl.
      now rewrite Hz.
    - constructor.
    - constructor.
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
    - econstructor.
      + now apply IHt1.
      + now apply IHt2.
    - econstructor.
      + now apply IHt1.
      + now apply IHt2.
      + now apply IHt3.
  Qed.
End has_type.

Module ctx.
  Definition t := list type.t.
End ctx.

Module value.
  Inductive t : expr.t -> Prop :=
  | tt : t expr.tt
  | ff : t expr.ff
  | abs : forall e, t (expr.abs e)
  .
End value.

Module step.
  Inductive t : expr.t -> expr.t -> Prop :=
  | beta : forall e1 e2,
      value.t e2 ->
      t (expr.app (expr.abs e1) e2)
        (expr.subst [e2] e1)
  | app1  : forall e1 e1' e2,
      t e1 e1' ->
      t (expr.app e1 e2) (expr.app e1' e2)
  | app2  : forall e1 e2 e2',
      value.t e1 ->
      t e2 e2' ->
      t (expr.app e1 e2) (expr.app e1 e2')
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
    intros e1 e2 e2' Val1 Star.
    revert e1 Val1.
    induction Star; intros e1 Val1.
    - constructor.
    - econstructor; [|apply IHStar]; auto.
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

  Lemma star_refl :
    forall e,
      star e e.
  Proof.
    constructor.
  Qed.

  Hint Resolve star_app2 star_app1 star_refl : core.

  Lemma value :
    forall v,
      value.t v ->
      forall e',
        step.t v e' ->
        False.
  Proof.
    induction 1; intros e' Step; inversion Step; subst.
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
End step.

Module type_safety.
  Definition safe (e : expr.t) :=
    value.t e \/
    exists e',
      step.t e e'.

  Lemma canonical_forms_arrow :
    forall G e ty1 ty2,
      has_type.t G e (type.arrow ty1 ty2) ->
      value.t e ->
      exists e',
        e = expr.abs e'.
  Proof.
    intros G e ty1 ty2 HT V.
    invc HT; invc V; eauto.
  Qed.

  Lemma canonical_forms_bool :
    forall G e,
      has_type.t G e type.bool ->
      value.t e ->
      e = expr.tt \/ e = expr.ff.
  Proof.
    intros G e HT V.
    invc HT; invc V; auto.
  Qed.

  Lemma progress :
    forall e ty,
      has_type.t [] e ty ->
      safe e.
  Proof.
    intros e ty HT.
    remember [] as G eqn:E in *.
    revert E.
    induction HT; intro E; subst G; try solve [repeat econstructor];
      repeat match goal with
             | [ H : _ |- _ ] => specialize (H eq_refl)
             end.
    - destruct x; discriminate.
    - invc IHHT1; [invc IHHT2|]; try solve [firstorder; unfold safe; eauto].
      destruct (canonical_forms_arrow _ _ _ _ HT1 ltac:(assumption)) as [b1 ?].
      subst e1.
      unfold safe.
      eauto.
    - invc IHHT1; [|firstorder; unfold safe; eauto].
      destruct (canonical_forms_bool _ _ HT1 ltac:(assumption)); subst e1;
        unfold safe; eauto.
  Qed.

  Lemma preservation :
    forall e e' ty,
      has_type.t [] e ty ->
      step.t e e' ->
      has_type.t [] e' ty.
  Proof.
    intros e e' ty HT S.
    remember [] as G eqn:E in *.
    revert E e' S.
    induction HT; intros E e' S; subst G; invc S; auto.
    - invc HT1.
      eauto using has_type.subst.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Theorem type_safety :
    forall e e' ty,
      has_type.t [] e ty ->
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

Module context.
  Inductive t :=
  | hole
  | abs : t -> t
  | app1 : t -> expr.t -> t
  | app2 : expr.t -> t -> t
  | If1 : t -> expr.t -> expr.t -> t
  | If2 : expr.t -> t -> expr.t -> t
  | If3 : expr.t -> expr.t -> t -> t
  .

  Fixpoint plug (C : t) (e : expr.t) : expr.t :=
    match C with
    | hole => e
    | abs C' => expr.abs (plug C' e)
    | app1 C1 e2 => expr.app (plug C1 e) e2
    | app2 e1 C2 => expr.app e1 (plug C2 e)
    | If1 C1 e2 e3 => expr.If (plug C1 e) e2 e3
    | If2 e1 C2 e3 => expr.If e1 (plug C2 e) e3
    | If3 e1 e2 C3 => expr.If e1 e2 (plug C3 e)
    end.
End context.

Module context_has_type.
  Inductive t : list type.t -> context.t -> list type.t -> type.t -> type.t -> Prop :=
  | hole : forall G ty, t G context.hole G ty ty
  | abs : forall G' C G ty ty1' ty2',
      t (ty1' :: G') C (ty1' :: G) ty ty2' ->
      t G' (context.abs C) (ty1' :: G) ty (type.arrow ty1' ty2')
  | app1 : forall G' C G ty ty1' ty2' e,
      t G' C G ty (type.arrow ty1' ty2') ->
      has_type.t G' e ty1' ->
      t G' (context.app1 C e) G ty ty2'
  | app2 : forall G' C G ty ty1' ty2' e,
      has_type.t G' e (type.arrow ty1' ty2') ->
      t G' C G ty ty1' ->
      t G' (context.app2 e C) G ty ty2'
  | If1 : forall G' C1 G ty ty' e2 e3,
      t G' C1 G ty type.bool ->
      has_type.t G' e2 ty' ->
      has_type.t G' e3 ty' ->
      t G' (context.If1 C1 e2 e3) G ty ty'
  | If2 : forall G' C2 G ty ty' e1 e3,
      has_type.t G' e1 type.bool ->
      t G' C2 G ty ty' ->
      has_type.t G' e3 ty' ->
      t G' (context.If2 e1 C2 e3) G ty ty'
  | If3 : forall G' C3 G ty ty' e1 e2,
      has_type.t G' e1 type.bool ->
      has_type.t G' e2 ty' ->
      t G' C3 G ty ty' ->
      t G' (context.If3 e1 e2 C3) G ty ty'
  .

  Theorem plug :
    forall G' C G ty ty',
      t G' C G ty ty' ->
      forall e,
        has_type.t G e ty ->
        has_type.t G' (context.plug C e) ty'.
  Proof.
    induction 1; intros e0 HT0; cbn [context.plug]; try assumption;
      apply IHt in HT0; econstructor; eauto.
  Qed.
End context_has_type.

Module context_equiv.
  Definition t G e1 e2 ty : Prop :=
    forall C v1 v2,
      context_has_type.t [] C G ty type.bool ->
      step.star (context.plug C e1) v1 ->
      value.t v1 ->
      step.star (context.plug C e2) v2 ->
      value.t v2 ->
      v1 = v2.
End context_equiv.
