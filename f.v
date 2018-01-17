Require Import util.

Module type.
  Inductive t :=
  | var (alpha : nat) : t
  | arrow : t -> t -> t
  | all : t -> t
  .

  Fixpoint wf (n : nat) (ty : t) :=
    match ty with
    | var a => a < n
    | arrow ty1 ty2 => wf n ty1 /\ wf n ty2
    | all ty' => wf (S n) ty'
    end.

  Fixpoint shift (c d : nat) (ty : t) : t :=
    match ty with
    | var a => var (if a <? c then a else d + a)
    | arrow ty1 ty2 => arrow (shift c d ty1) (shift c d ty2)
    | all ty' => all (shift (S c) d ty')
    end.

  Fixpoint identity_subst (n : nat) : list type.t :=
    match n with
    | 0 => []
    | S n => var 0 :: List.map (shift 0 1) (identity_subst n)
    end.

  Lemma identity_subst_length : forall n, length (identity_subst n) = n.
  Proof.
    induction n; simpl.
    - auto.
    - rewrite map_length. auto using f_equal.
  Qed.

  Lemma shift_shift :
    forall ty c1 d1 c2 d2,
      c2 <= c1 ->
      shift c2 d2 (shift c1 d1 ty) =
      shift (c1 + d2) d1 (shift c2 d2 ty).
  Proof.
    induction ty; intros c1 d1 c2 d2 LT; simpl.
    - f_equal.
      repeat match goal with
      | [  |- context [ ?x <? ?y ] ] =>
        destruct (Nat.ltb_spec x y)
      end; omega.
    - f_equal; eauto.
    - f_equal. now rewrite IHty by omega.
  Qed.

  Fixpoint subst (D : list t) (ty : t) : t :=
    match ty with
    | var a => match List.nth_error D a with
              | Some ty' => ty'
              | None => ty
              end
    | arrow ty1 ty2 => arrow (subst D ty1) (subst D ty2)
    | all ty' => all (subst (var 0 :: map (shift 0 1) D) ty')
    end.

  Lemma shift_subst :
    forall ty c d D,
      wf (List.length D) ty ->
      shift c d (subst D ty) =
      subst (List.map (shift c d) D) ty.
  Proof.
    induction ty; intros c d D WF.
    - simpl in *.
      rewrite nth_error_map.
      destruct (nth_error D alpha) eqn:?.
      + reflexivity.
      + pose proof nth_error_Some D alpha.
        intuition.
    - simpl in *. f_equal; intuition.
    - simpl. f_equal.
      rewrite IHty by (simpl; rewrite map_length; assumption).
      simpl.
      f_equal. f_equal.
      rewrite !map_map.
      apply map_ext.
      intros ty'.
      rewrite shift_shift with (c2 := 0) by omega.
      f_equal. omega.
  Qed.

  Lemma subst_shift :
    forall ty D1 D2 D3,
      wf (List.length (D1 ++ D3)) ty ->
      subst (D1 ++ D2 ++ D3) (shift (List.length D1) (List.length D2) ty) =
      subst (D1 ++ D3) ty.
  Proof.
    induction ty; simpl; intros D1 D2 D3 H.
    - destruct (Nat.ltb_spec alpha (length D1)).
      + now rewrite !nth_error_app1 by assumption.
      + rewrite !nth_error_app2 by omega.
        rewrite plus_comm.
        rewrite Nat.add_sub_swap by assumption.
        rewrite <- Nat.add_sub_assoc by omega.
        rewrite Nat.sub_diag.
        rewrite Nat.add_0_r.
        break_match; auto.
        pose proof nth_error_Some D3 (alpha - length D1).
        rewrite !app_length in *.
        now intuition.
    - f_equal; intuition.
    - f_equal.
      rewrite !map_app.
      rewrite !app_comm_cons.
      erewrite <- IHty.
      + f_equal. simpl.
        now rewrite !map_length.
      + simpl. now rewrite app_length, !map_length in *.
  Qed.

  Lemma wf_shift :
    forall ty c d n,
      wf n ty ->
      wf (d + n) (shift c d ty).
  Proof.
    induction ty; simpl; intros c d m H.
    - destruct (Nat.ltb_spec alpha c); omega.
    - intuition.
    - rewrite plus_n_Sm. auto.
  Qed.

  Lemma subst_subst :
    forall ty D1 D2,
      wf (List.length D1) ty ->
      List.Forall (wf (List.length D2)) D1 ->
      subst D2 (subst D1 ty) =
      subst (List.map (subst D2) D1) ty.
  Proof.
    induction ty; intros D1 D2 WF F.
    - cbn [subst].
      cbn [wf] in WF.
      pose proof nth_error_Some D1 alpha.
      rewrite nth_error_map.
      destruct (nth_error D1 alpha) eqn:TY; intuition congruence.
    - simpl in *.
      intuition.
      now rewrite IHty1, IHty2 by auto.
    - cbn [subst].
      erewrite IHty.
      + f_equal. f_equal.
        simpl. f_equal.
        rewrite !map_map.
        apply map_ext_in.
        intros ty' I.
        assert (wf (length D2) ty') by (eapply Forall_forall; eauto).
        rewrite shift_subst by assumption.
        apply subst_shift with (D1 := []) (D2 := [var 0]).
        simpl.
        now rewrite map_length.
      + simpl.
        now rewrite map_length.
      + simpl. constructor.
        * rewrite map_length. simpl. omega.
        * rewrite map_length.
          rewrite Forall_map.
          eapply Forall_impl; [|eauto].
          intros ty' H.
          apply wf_shift with (d := 1); auto.
  Qed.

  Lemma wf_subst :
    forall ty n D,
      wf (length D) ty ->
      List.Forall (wf n) D ->
      wf n (subst D ty).
  Proof.
    induction ty; simpl; intros x D WF F.
    - break_match.
      + now eapply Forall_nth; eauto.
      + pose proof nth_error_Some D alpha.
        intuition.
    - intuition eauto.
    - eapply IHty; eauto.
      + simpl. now rewrite map_length.
      + constructor.
        * simpl. omega.
        * rewrite Forall_map.
          eapply Forall_impl; [|eauto].
          intros.
          now apply wf_shift with (d := 1).
  Qed.

  Lemma nth_error_identity_subst :
    forall n x y,
      nth_error (identity_subst n) x = Some y ->
      y = var x.
  Proof.
    induction n; intros x y NE; destruct x; simpl in *; try congruence.
    rewrite nth_error_map in NE.
    break_match; try discriminate.
    apply IHn in Heqo.
    subst. simpl in *. congruence.
  Qed.

  Lemma subst_identity :
    forall e n,
      subst (identity_subst n) e = e.
  Proof.
    induction e as [x| |]; intros n; cbn [subst].
    - destruct (nth_error (identity_subst n) x) eqn:E; auto.
      now apply nth_error_identity_subst in E.
    - now f_equal; auto.
    - f_equal.
      now apply IHe with (n := (S n)).
  Qed.

  Lemma subst_empty :
    forall e,
      subst [] e = e.
  Proof.
    intros e.
    exact (subst_identity e 0).
  Qed.

  Lemma wf_weaken :
    forall ty n d,
      n <= d ->
      wf n ty ->
      wf d ty.
  Proof.
    induction ty; simpl; intros n d WF; intuition eauto with arith.
  Qed.

  Lemma shift_nop :
    forall ty c d n,
      n <= c ->
      wf n ty ->
      shift c d ty = ty.
  Proof.
    induction ty; simpl; intros c d n LE WF; f_equal; intuition eauto.
    - destruct (Nat.ltb_spec alpha c); omega.
    - eapply IHty; [|eauto]. omega.
  Qed.

  Lemma shift_nop_d :
    forall ty c,
      shift c 0 ty = ty.
  Proof.
    induction ty; intros c; simpl; f_equal; auto.
    break_match; auto.
  Qed.

  Lemma identity_subst_wf :
    forall n,
      Forall (wf n) (identity_subst n).
  Proof.
    induction n; simpl; constructor.
    - simpl. omega.
    - rewrite Forall_map. eapply Forall_impl; [|apply IHn].
      intros ty WF.
      now apply wf_shift with (c := 0) (d := 1).
  Qed.

  Lemma shift_merge :
    forall e c d1 d2,
      shift c d2 (shift c d1 e) = shift c (d2 + d1) e.
  Proof.
    induction e; intros c d1 d2; simpl.
    - destruct (Nat.ltb_spec alpha c).
      + destruct (Nat.ltb_spec alpha c); [reflexivity|omega].
      + destruct (Nat.ltb_spec (d1 + alpha) c); f_equal; omega.
    - f_equal; auto.
    - f_equal. auto.
  Qed.
End type.

Module expr.
  Inductive t :=
  | var (x : nat) : t
  | abs : t -> t
  | app : t -> t -> t
  | tyabs : t -> t
  | tyapp : t -> t
  .

  Fixpoint wf (n : nat) (e : t) :=
    match e with
    | var x => x < n
    | abs e' => wf (S n) e'
    | app e1 e2 => wf n e1 /\ wf n e2
    | tyabs e' => wf n e'
    | tyapp e' => wf n e'
    end.

  Fixpoint shift (c d : nat) (e : t) : t :=
    match e with
    | var x => var (if x <? c then x else d + x)
    | abs e' => abs (shift (S c) d e')
    | app e1 e2 => app (shift c d e1) (shift c d e2)
    | tyabs e' => tyabs (shift c d e')
    | tyapp e' => tyapp (shift c d e')
    end.

  Fixpoint subst (rho : list expr.t) (e : t) : t :=
    match e with
    | var x => match nth_error rho x with
              | Some e' => e'
              | None => e
              end
    | abs e' => abs (subst (var 0 :: List.map (shift 0 1) rho) e')
    | app e1 e2 => app (subst rho e1) (subst rho e2)
    | tyabs e' => tyabs (subst rho e')
    | tyapp e' => tyapp (subst rho e')
    end.

  Fixpoint identity_subst (n : nat) : list expr.t :=
    match n with
    | 0 => []
    | S n => var 0 :: List.map (shift 0 1) (identity_subst n)
    end.

  Lemma identity_subst_length : forall n, length (identity_subst n) = n.
  Proof.
    induction n; simpl.
    - auto.
    - rewrite map_length. auto using f_equal.
  Qed.

  Lemma wf_shift :
    forall e c d n,
      wf n e ->
      wf (d + n) (shift c d e).
  Proof.
    induction e; simpl; intros c d m H.
    - destruct (Nat.ltb_spec x c); omega.
    - rewrite plus_n_Sm. auto.
    - intuition.
    - auto.
    - auto.
  Qed.

  Lemma wf_subst :
    forall e n rho,
      wf (length rho) e ->
      Forall (wf n) rho ->
      wf n (subst rho e).
  Proof.
    induction e; simpl; intros n rho WF F.
    - break_match.
      + now eapply Forall_nth; eauto.
      + pose proof nth_error_Some rho x.
        intuition.
    - eapply IHe; eauto.
      + simpl. now rewrite map_length.
      + constructor.
        * simpl. omega.
        * rewrite Forall_map.
          eapply Forall_impl; [|eauto].
          intros.
          now apply wf_shift with (d := 1).
    - intuition eauto.
    - apply IHe; auto.
    - auto.
  Qed.

  Lemma shift_shift :
    forall e c1 d1 c2 d2,
      c2 <= c1 ->
      shift c2 d2 (shift c1 d1 e) =
      shift (c1 + d2) d1 (shift c2 d2 e).
  Proof.
    induction e; simpl; intros c1 d1 c2 d2 LT.
    - f_equal.
      repeat match goal with
      | [  |- context [ ?x <? ?y ] ] =>
        destruct (Nat.ltb_spec x y)
      end; omega.
    - f_equal. now rewrite IHe by omega.
    - f_equal; eauto.
    - f_equal. eauto.
    - f_equal. eauto.
  Qed.

  Lemma shift_subst :
    forall e c d rho,
      wf (List.length rho) e ->
      shift c d (subst rho e) =
      subst (List.map (shift c d) rho) e.
  Proof.
    induction e; intros c d rho WF.
    - simpl in *.
      rewrite nth_error_map.
      destruct (nth_error rho x) eqn:?.
      + reflexivity.
      + pose proof nth_error_Some rho x.
        intuition.
    - simpl. f_equal.
      rewrite IHe by (simpl; rewrite map_length; assumption).
      simpl.
      f_equal. f_equal.
      rewrite !map_map.
      apply map_ext.
      intros e'.
      rewrite shift_shift with (c2 := 0) by omega.
      f_equal. omega.
    - simpl in *. f_equal; intuition.
    - simpl in *. f_equal.
      now rewrite IHe by assumption.
    - simpl in *. f_equal.
      auto.
  Qed.

  Lemma subst_shift :
    forall e r1 r2 r3,
      wf (List.length (r1 ++ r3)) e ->
      subst (r1 ++ r2 ++ r3) (shift (List.length r1) (List.length r2) e) =
      subst (r1 ++ r3) e.
  Proof.
    induction e; simpl; intros r1 r2 r3 WF; f_equal; intuition.
    - destruct (Nat.ltb_spec x (length r1)).
      + now rewrite !nth_error_app1 by assumption.
      + rewrite !nth_error_app2 by omega.
        rewrite plus_comm.
        rewrite Nat.add_sub_swap by assumption.
        rewrite <- Nat.add_sub_assoc by omega.
        rewrite Nat.sub_diag.
        rewrite Nat.add_0_r.
        break_match; auto.
        pose proof nth_error_Some r3 (x - length r1).
        rewrite !app_length in *.
        intuition.
    - rewrite !map_app.
      rewrite !app_comm_cons.
      erewrite <- IHe.
      + f_equal. simpl.
        now rewrite !map_length.
      + simpl. now rewrite app_length, !map_length in *.
  Qed.

  Lemma subst_subst :
    forall e rho1 rho2,
      wf (length rho1) e ->
      Forall (wf (length rho2)) rho1 ->
      subst rho2 (subst rho1 e) =
      subst (List.map (subst rho2 ) rho1) e.
  Proof.
    induction e; simpl; intros rho1 rho2 WF F.
    - rewrite nth_error_map.
      break_match; auto.
      pose proof nth_error_Some rho1 x.
      intuition.
    - f_equal. rewrite IHe.
      + simpl.
        f_equal. f_equal.
        rewrite !map_map.
        apply map_ext_in.
        intros e' I.
        pose proof subst_shift e' [] [var 0] (map (shift 0 1) rho2).
        simpl in H.
        assert (wf (length rho2) e') by (eapply Forall_forall; eauto).
        rewrite H by now rewrite map_length.
        now rewrite shift_subst by assumption.
      + simpl. now rewrite map_length.
      + simpl. rewrite map_length.
        constructor.
        * simpl. omega.
        * rewrite Forall_map.
          eapply Forall_impl; [| now eauto].
          intros e' WF'.
          now apply wf_shift with (d := 1).
    - f_equal; intuition.
    - f_equal; auto.
    - f_equal; auto.
  Qed.

  Lemma nth_error_identity_subst :
    forall n x y,
      nth_error (identity_subst n) x = Some y ->
      y = var x.
  Proof.
    induction n; intros x y NE; destruct x; simpl in *; try congruence.
    rewrite nth_error_map in NE.
    break_match; try discriminate.
    apply IHn in Heqo.
    subst. simpl in *. congruence.
  Qed.

  Lemma subst_identity :
    forall e n,
      subst (identity_subst n) e = e.
  Proof.
    induction e as [x| | | |]; intros n; cbn [subst].
    - destruct (nth_error (identity_subst n) x) eqn:E; auto.
      now apply nth_error_identity_subst in E.
    - f_equal.
      now apply IHe with (n := (S n)).
    - now f_equal; auto.
    - f_equal. auto.
    - f_equal. auto.
  Qed.

  Lemma subst_empty :
    forall e,
      subst [] e = e.
  Proof.
    intros e.
    exact (subst_identity e 0).
  Qed.


  Lemma subst_shift' :
    forall e e' g,
      wf (length g) e ->
      subst (e' :: g) (shift 0 1 e) = subst g e.
  Proof.
    intros.
    pose proof subst_shift e [] [e'] g.
    auto.
  Qed.

  Lemma subst_shift_singleton :
    forall e e',
      wf 0 e ->
      subst [e'] (shift 0 1 e) = e.
  Proof.
    intros.
    rewrite subst_shift' by auto.
    now rewrite subst_identity with (n := 0).
  Qed.
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
        clear H H0 H1 H2.
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
