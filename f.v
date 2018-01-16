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
End type.

Module expr.
  Inductive t :=
  | var (x : nat) : t
  | abs : t -> type.t -> t
  | app : t -> t -> t
  | tyabs : t -> t
  | tyapp : t -> type.t -> t
  .

  Fixpoint tywf (n : nat) (e : t) :=
    match e with
    | var x => True
    | abs e' ty => tywf n e' /\ type.wf n ty
    | app e1 e2 => tywf n e1 /\ tywf n e2
    | tyabs e' => tywf (S n) e'
    | tyapp e' ty => tywf n e' /\ type.wf n ty
    end.

  Fixpoint tyshift (c d : nat) (e : t) : t :=
    match e with
    | var x => var x
    | abs e' ty => abs (tyshift c d e') (type.shift c d ty)
    | app e1 e2 => app (tyshift c d e1) (tyshift c d e2)
    | tyabs e' => tyabs (tyshift (S c) d e')
    | tyapp e' ty => tyapp (tyshift c d e') (type.shift c d ty)
    end.

  Fixpoint tysubst (D : list type.t) (e : t) : t :=
    match e with
    | var x => var x
    | abs e' ty => abs (tysubst D e') (type.subst D ty)
    | app e1 e2 => app (tysubst D e1) (tysubst D e2)
    | tyabs e' => tyabs (tysubst (type.var 0 :: List.map (type.shift 0 1) D) e')
    | tyapp e' ty => tyapp (tysubst D e') (type.subst D ty)
    end.

  Fixpoint wf (n : nat) (e : t) :=
    match e with
    | var x => x < n
    | abs e' ty => wf (S n) e'
    | app e1 e2 => wf n e1 /\ wf n e2
    | tyabs e' => wf n e'
    | tyapp e' ty => wf n e'
    end.

  Fixpoint shift (c d : nat) (e : t) : t :=
    match e with
    | var x => var (if x <? c then x else d + x)
    | abs e' ty => abs (shift (S c) d e') ty
    | app e1 e2 => app (shift c d e1) (shift c d e2)
    | tyabs e' => tyabs (shift c d e')
    | tyapp e' ty => tyapp (shift c d e') ty
    end.

  Fixpoint subst (rho : list expr.t) (e : t) : t :=
    match e with
    | var x => match nth_error rho x with
              | Some e' => e'
              | None => e
              end
    | abs e' ty => abs (subst (var 0 :: List.map (shift 0 1) rho) e') ty
    | app e1 e2 => app (subst rho e1) (subst rho e2)
    | tyabs e' => tyabs (subst (List.map (tyshift 0 1) rho) e')
    | tyapp e' ty => tyapp (subst rho e') ty
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

  Lemma wf_tyshift_iff :
    forall e n c d,
      wf n e <-> wf n (tyshift c d e).
  Proof.
    induction e; simpl; intros n c d; firstorder.
  Qed.

  Lemma wf_tyshift :
    forall e n c d,
      wf n e -> wf n (tyshift c d e).
  Proof.
    intros.
    now apply wf_tyshift_iff.
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
    - apply IHe.
      + simpl. now rewrite map_length.
      + rewrite Forall_map.
        eapply Forall_impl; [|eauto].
        eauto using wf_tyshift.
    - auto.
  Qed.

  Lemma tywf_tysubst :
    forall e n D,
      tywf (length D) e ->
      Forall (type.wf n) D ->
      tywf n (tysubst D e).
  Proof.
    induction e; simpl; intros n D WF F; intuition.
    - apply type.wf_subst; auto.
    - apply IHe.
      + simpl. now rewrite map_length.
      + constructor.
        * simpl. omega.
        * rewrite Forall_map.
          eapply Forall_impl; [|eauto].
          intros ty' TWF.
          now apply type.wf_shift with (d := 1).
    - apply type.wf_subst; auto.
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

  Lemma shift_tyshift :
    forall e c1 d1 c2 d2,
      shift c2 d2 (tyshift c1 d1 e) =
      tyshift c1 d1 (shift c2 d2 e).
  Proof.
    induction e; simpl; intros c1 d1 c2 d2; f_equal; auto.
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
      rewrite IHe by (simpl; rewrite map_length; assumption).
      f_equal.
      rewrite !map_map.
      apply map_ext.
      intros e'.
      apply shift_tyshift.
    - simpl in *. f_equal.
      auto.
  Qed.

  Lemma subst_shift :
    forall e r1 r2 r3,
      wf (List.length (r1 ++ r3)) e ->
      subst (r1 ++ r2 ++ r3) (shift (List.length r1) (List.length r2) e) =
      subst (r1 ++ r3) e.
  Proof.
    induction e; simpl; intros r1 r2 r3 WF.
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
    - f_equal.
      rewrite !map_app.
      rewrite !app_comm_cons.
      erewrite <- IHe.
      + f_equal. simpl.
        now rewrite !map_length.
      + simpl. now rewrite app_length, !map_length in *.
    - f_equal; intuition.
    - f_equal.
      rewrite !map_app.
      erewrite <- IHe.
      + f_equal. now rewrite !map_length.
      + now rewrite app_length, !map_length in *.
    - f_equal; auto.
  Qed.

  Lemma tyshift_tyshift :
    forall e c1 d1 c2 d2,
      c2 <= c1 ->
      tyshift c2 d2 (tyshift c1 d1 e) =
      tyshift (c1 + d2) d1 (tyshift c2 d2 e).
  Proof.
    induction e; simpl; intros c1 d1 c2 d2 LE; f_equal; auto using type.shift_shift.
    now rewrite IHe by omega.
  Qed.

  Lemma tyshift_subst :
    forall e c d rho,
      tyshift c d (subst rho e) =
      subst (map (tyshift c d) rho) (tyshift c d e).
  Proof.
    induction e; simpl; intros c d rho; f_equal; auto.
    - rewrite nth_error_map.
      break_match; auto.
    - rewrite IHe.
      simpl. f_equal. f_equal.
      rewrite !map_map.
      apply map_ext.
      now auto using shift_tyshift.
    - rewrite IHe.
      f_equal.
      rewrite !map_map.
      apply map_ext.
      intros e'.
      rewrite tyshift_tyshift with (c2 := 0) by omega.
      f_equal. omega.
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
    - f_equal. rewrite IHe.
      + rewrite !map_map. f_equal.
        apply map_ext_in.
        intros e' I.
        now rewrite tyshift_subst.
      + now rewrite map_length.
      + rewrite map_length, Forall_map.
        eapply Forall_impl; [|now eauto].
        now auto using wf_tyshift.
    - f_equal; auto.
  Qed.

  Lemma tysubst_tysubst :
    forall e D1 D2,
      tywf (length D1) e ->
      Forall (type.wf (length D2)) D1 ->
      tysubst D2 (tysubst D1 e) =
      tysubst (List.map (type.subst D2 ) D1) e.
  Proof.
    induction e; simpl; intros D1 D2 WF F; simpl; f_equal;
      intuition auto using type.subst_subst.
    rewrite IHe.
    + f_equal. simpl.
      f_equal.
      rewrite !map_map.
      apply map_ext_in.
      intros ty I.
      assert (type.wf (length D2) ty) as WFty by (eapply Forall_forall; eauto).
      rewrite type.shift_subst.
      * pose proof type.subst_shift ty [] [type.var 0].
        simpl in H.
        rewrite H; auto.
        now rewrite map_length.
      * auto.
    + simpl. now rewrite map_length.
    + simpl. rewrite map_length.
      constructor.
      * simpl. omega.
      * rewrite Forall_map.
        eapply Forall_impl; [|now eauto].
        intros e' WF'.
        now apply type.wf_shift with (c := 0) (d := 1).
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

  Lemma tyshift_identity_subst :
    forall n c d,
      map (tyshift c d) (identity_subst n) = identity_subst n.
  Proof.
    induction n; simpl; intuition.
    f_equal.
    rewrite !map_map.
    erewrite map_ext.
    erewrite <- map_map.
    f_equal.
    apply IHn with (c := c) (d := d).
    intros e'. simpl.
    auto using shift_tyshift.
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
    - f_equal.
      now rewrite tyshift_identity_subst.
    - f_equal. auto.
  Qed.

  Lemma subst_empty :
    forall e,
      subst [] e = e.
  Proof.
    intros e.
    exact (subst_identity e 0).
  Qed.

  Lemma tywf_shift :
    forall e n c d,
      tywf n e ->
      tywf n (shift c d e).
  Proof.
    induction e; simpl; intros n c d TWF; intuition.
  Qed.

  Lemma tywf_tyshift :
    forall e n c d,
      tywf n e ->
      tywf (d + n) (tyshift c d e).
  Proof.
    induction e; simpl; intros n c d TWF; intuition; auto using type.wf_shift.
    rewrite plus_n_Sm.
    now auto.
  Qed.

  Lemma tywf_subst :
    forall e n rho,
      tywf n e ->
      Forall (tywf n) rho ->
      tywf n (subst rho e).
  Proof.
    induction e; simpl; intros n rho TWF F; intuition.
    - break_match; [|now auto].
      now eapply Forall_nth; eauto.
    - apply IHe; [assumption|].
      constructor; [now auto|].
      rewrite Forall_map.
      eapply Forall_impl; eauto.
      auto using tywf_shift.
    - apply IHe; auto.
      rewrite Forall_map.
      eapply Forall_impl; eauto.
      intros.
      now apply tywf_tyshift with (d := 1).
  Qed.

  Lemma tywf_weaken :
    forall e n d,
      n <= d ->
      tywf n e ->
      tywf d e.
  Proof.
    induction e; simpl; intros n d LT TWF; intuition; eauto using type.wf_weaken with arith.
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

  Lemma tysubst_shift :
    forall e D c d,
      expr.tysubst D (expr.shift c d e) =
      expr.shift c d (expr.tysubst D e).
  Proof.
    induction e; simpl; intros D c d; f_equal; auto.
  Qed.

  Lemma tyshift_tysubst :
    forall e c d D,
      expr.tywf (length D) e ->
      expr.tyshift c d (expr.tysubst D e) =
      expr.tysubst (map (type.shift c d) D) e.
  Proof.
    induction e; simpl; intros c d D TWF; f_equal; intuition; auto using type.shift_subst.
    rewrite IHe.
    - simpl. f_equal. f_equal.
      rewrite !map_map.
      apply map_ext.
      intros ty.
      rewrite type.shift_shift with (c2 := 0) (d2 := 1) by omega.
      f_equal. omega.
    - simpl. now rewrite map_length.
  Qed.

  Lemma tysubst_tyshift :
    forall e D1 D2 D3,
      expr.tywf (List.length (D1 ++ D3)) e ->
      expr.tysubst (D1 ++ D2 ++ D3) (expr.tyshift (List.length D1) (List.length D2) e) =
      expr.tysubst (D1 ++ D3) e.
  Proof.
    induction e; simpl; intros D1 D2 D3 TWF; f_equal; intuition; auto using type.subst_shift.
    - rewrite !map_app.
      rewrite !app_comm_cons.
      erewrite <- IHe.
      + f_equal. simpl. now rewrite !map_length.
      + simpl. now rewrite app_length, !map_length in *.
  Qed.

  Lemma tysubst_subst :
    forall e D rho,
      expr.tywf (length D) e ->
      Forall (expr.tywf (length D)) rho ->
      expr.tysubst D (expr.subst rho e) =
      expr.subst (map (expr.tysubst D) rho) (expr.tysubst D e).
  Proof.
    induction e; simpl; intros D rho WF F; f_equal; intuition.
    - rewrite nth_error_map.
      break_match; auto.
    - rewrite IHe.
      * f_equal.
        simpl.
        f_equal.
        rewrite !map_map.
        apply map_ext.
        now auto using tysubst_shift.
      * assumption.
      * constructor; [now auto|].
        rewrite Forall_map.
        eapply Forall_impl; [|now eauto].
        intros e' TWF.
        now apply expr.tywf_shift.
    - f_equal.
      rewrite IHe.
      + f_equal.
        rewrite !map_map.
        apply map_ext_in.
        intros e' I.
        assert (expr.tywf (length D) e').
        { destruct (In_nth_error _ _ I) as [n NE].
          eapply Forall_nth; eauto. }
        rewrite tyshift_tysubst by assumption.
        pose proof tysubst_tyshift e' [] [type.var 0] (map (type.shift 0 1) D) as TS.
        simpl in TS.
        rewrite map_length in TS.
        specialize (TS H).
        now rewrite TS.
      + simpl. now rewrite map_length.
      + simpl. rewrite map_length.
        rewrite Forall_map.
        eapply Forall_impl; [|now eauto].
        intros e' TWF'.
        now apply expr.tywf_tyshift with (c := 0) (d := 1).
  Qed.

  Lemma tyshift_nop :
    forall e c d n,
      n <= c ->
      tywf n e ->
      tyshift c d e = e.
  Proof.
    induction e; simpl; intros c d n LE WF; f_equal; intuition eauto using type.shift_nop.
    eapply IHe; [|eauto].
    omega.
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
      t n G (expr.abs e ty1) (type.arrow ty1 ty2)
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
      t n G (expr.tyapp e ty) (type.subst (ty :: type.identity_subst n) ty_body)
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

  Lemma t_expr_tywf :
    forall n G e ty,
      t n G e ty ->
      expr.tywf n e.
  Proof.
    induction 1; simpl in *; intuition.
  Qed.
End has_type.

Module value.
  Inductive t : expr.t -> Prop :=
  | abs : forall e ty, t (expr.abs e ty)
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
  | beta : forall body ty v,
      value.t v ->
      t (expr.app (expr.abs body ty) v) (expr.subst [v] body)
  | tyapp : forall e e' ty,
      t e e' ->
      t (expr.tyapp e ty) (expr.tyapp e' ty)
  | tybeta : forall body ty,
      t (expr.tyapp (expr.tyabs body) ty)
        (expr.tysubst [ty] body)
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

Module semtype.
  Definition t := expr.t -> Prop.

  Definition wf (S : t) :=
    forall e,
      S e ->
      value.t e /\ expr.wf 0 e /\ expr.tywf 0 e.
End semtype.

Fixpoint V ty (d : list semtype.t) e :=
  match ty with
    | type.var alpha =>
      match nth_error d alpha with
      | Some X => X e
      | None => False
      end
    | type.arrow ty1 ty2 =>
      expr.wf 0 e /\
      exists body ty,
          e = expr.abs body ty /\
          forall e2,
            V ty1 d e2 ->
            terminating.t (V ty2 d) (expr.subst [e2] body)
    | type.all ty' =>
      expr.wf 0 e /\
      exists body,
        e = expr.tyabs body /\
        forall (S : semtype.t),
          semtype.wf S  ->
          terminating.t (V ty' (S :: d)) body
  end.

Notation E ty d :=
  (terminating.t (V ty d)).

Lemma V_value :
  forall ty d v,
    Forall semtype.wf d ->
    V ty d v ->
    value.t v.
Proof.
  intros ty d v WFd HV.
  destruct ty; cbn [V] in HV.
  - break_match; intuition.
    assert (semtype.wf t) by (eapply Forall_nth; eauto).
    firstorder.
  - destruct HV as [WF [body [ty [E H]]]].
    subst. constructor.
  - destruct HV as [WF [body [E H]]].
    subst. constructor.
Qed.

Lemma V_wf :
  forall ty d v,
    Forall semtype.wf d ->
    V ty d v ->
    expr.wf 0 v.
Proof.
  intros ty d v F.
  destruct ty; cbn [V]; intuition.
  break_match; intuition.
  assert (semtype.wf t) by (eapply Forall_nth; eauto).
  firstorder.
Qed.

Lemma V_E :
  forall ty d v,
    Forall semtype.wf d ->
    V ty d v ->
    E ty d v.
Proof.
  intros.
  exists v.
  intuition.
  - constructor.
  - eauto using V_value.
Qed.

Lemma E_step :
  forall ty d e e',
    step.t e e' ->
    E ty d e' ->
    E ty d e.
Proof.
  intros ty d e e' S HE.
  revert ty d HE.
  induction S; intros ty0 d [v2 [Star [Val HV]]]; exists v2; intuition.
  all: eauto using step.step_l.
Qed.

Lemma E_star :
  forall ty d e e',
    step.star e e' ->
    E ty d e' ->
    E ty d e.
Proof.
  intros ty d e e' Star HE.
  revert ty d HE.
  now induction Star; eauto using E_step.
Qed.

Lemma type_shift_wf_inv :
  forall ty n c d,
    type.wf n (type.shift c d ty) ->
    type.wf (max (min n c) (n - d)) ty.
Proof.
  induction ty; simpl; intros n c d WF; intuition; eauto.
  - destruct (Nat.ltb_spec alpha c).
    + pose proof Nat.max_spec (min n c) (n - d).
      pose proof Nat.min_spec n c.
      omega.
    + pose proof Nat.max_spec (min n c) (n - d).
      pose proof Nat.min_spec n c.
      omega.
  - apply IHty in WF.
    eapply type.wf_weaken; [|eauto].
    pose proof Nat.max_spec (min (S n) (S c)) (S n - d).
    pose proof Nat.max_spec (min n c) (n - d).
    pose proof Nat.min_spec (S n) (S c).
    pose proof Nat.min_spec n c.
    omega.
Qed.

Lemma tyshift_tywf_inv :
  forall e n c d,
    expr.tywf n (expr.tyshift c d e) ->
    expr.tywf (max (min n c) (n - d)) e.
Proof.
  induction e; simpl; intros n c d WF; intuition; eauto.
  - auto using type_shift_wf_inv.
  - eapply expr.tywf_weaken; [|eauto].
    pose proof Nat.max_spec (min (S n) (S c)) (S n - d).
    pose proof Nat.max_spec (min n c) (n - d).
    pose proof Nat.min_spec (S n) (S c).
    pose proof Nat.min_spec n c.
    omega.
  - auto using type_shift_wf_inv.
Qed.

Lemma tyshift_tywf_inv' :
  forall e c d,
    expr.tywf 0 (expr.tyshift c d e) ->
    expr.tywf 0 e.
Proof.
  intros.
  now apply (tyshift_tywf_inv e 0 c d).
Qed.

Lemma V_tyshift :
  forall ty D c d v,
    Forall semtype.wf D ->
    V ty D v <-> V ty D (expr.tyshift c d v).
Proof.
  induction ty; intros D c d v F.
  - simpl. break_match; [|now intuition].
    assert (semtype.wf t) as T by (eapply Forall_nth; eauto).
    unfold semtype.wf in T.
    split; intros TV.
    + destruct (T _ TV) as [Valv [WF TWF]].
      erewrite expr.tyshift_nop; [assumption| | exact TWF]; omega.
    + destruct (T _ TV) as [Valv [WF TWF]].
      eapply tyshift_tywf_inv' in TWF.
      now rewrite expr.tyshift_nop with (n := 0) in * by auto with *.
  - cbn [V].
    rewrite <- expr.wf_tyshift_iff.
    split; intros [WF [body [ty [? Vbody]]]]; subst; (split; [assumption|]);
      cbn [expr.tyshift].
    + do 2 eexists; split; [reflexivity|].
      admit.
    + destruct v; simpl in H; try discriminate.
      inversion H; subst. clear H.
      do 2 eexists; split; [reflexivity|].
      intros v2 V2.
      apply Vbody in V2.
      destruct V2 as [v2' [Star2' [Val2' V2']]].
      pose proof expr.tyshift_subst v c d [v2] as SS.
      cbn[map] in SS.


Lemma subst_tyshift :
  forall e rho c d,
    expr.subst rho (expr.tyshift c d








Lemma V_shift :
  forall ty d1 d2 d3 v,
    Forall semtype.wf (d1 ++ d3) ->
    V ty (d1 ++ d3) v <->
    V (type.shift (length d1) (length d2) ty) (d1 ++ d2 ++ d3) v.
Proof.
  induction ty; intros d1 d2 d3 v F; [|split|].
  - simpl.
    destruct (Nat.ltb_spec alpha (length d1)).
    + now rewrite !nth_error_app1 by assumption.
    + rewrite !nth_error_app2 by omega.
      replace (length d2 + alpha - length d1 - length d2)
         with (alpha - length d1) by omega.
      now auto.
  - intros Vv.
    destruct Vv as [WFe [body [ty1' [? Ebody]]]].
    split.
    + auto using expr.wf_tyshift.
    + subst v.
      do 2 eexists.
      split; [reflexivity|].
      intros v2 V2.
      assert (E ty2 (d1 ++ d3) (expr.subst [v2] body)) as Ev2.
      { apply Ebody.
        eapply IHty1; [assumption|].
        eauto.
      }
      destruct Ev2 as [v2' [Star2' [Val2' Vv2']]].
      eapply IHty2 with (d2 := d2) in Vv2'; [|assumption].
      exists v2'; intuition.
  - simpl.
    intros Vv.
    destruct Vv as [WF [body [ty [? Hv]]]].
    intuition.
    subst v.
    do 2 eexists.
    split; [reflexivity|].
    intros v2 V2.
    assert (E (type.shift (length d1) (length d2) ty2) (d1 ++ d2 ++ d3) (expr.subst [v2] body))
           as Ev2.
    {
      eapply Hv.
      apply IHty1; auto.
    }
    destruct Ev2 as [v2' [Star2' [Val2' Vv2']]].
    eapply IHty2 with (d2 := d2) in Vv2'; [|assumption].
    exists v2'; intuition.
  - simpl.
    split; intros Vv; destruct Vv as [Wf [body [? Hv]]];
      split; auto; subst v; eexists; (split; [reflexivity|]);
        intros S WFS.
    + destruct (Hv _ WFS) as [v2 [Star2 [Val2 V2]]].
      exists v2. intuition.
      apply IHty with (d1 := S :: d1); auto.
      simpl. constructor; auto.
    + destruct (Hv _ WFS) as [v2 [Star2 [Val2 V2]]].
      exists v2. intuition.
      specialize (IHty (S :: d1) d2 d3 v2).
      apply IHty; auto.
      simpl. constructor; auto.
Qed.

Lemma V_shift' :
  forall ty S d v,
    Forall semtype.wf d ->
    V ty d v ->
    V (type.shift 0 1 ty) (S :: d) (expr.tyshift 0 1 v).
Proof.
  intros.
  apply V_shift with (d1 := []) (d2 := [S]) (d3 := d); auto.
  apply V_tyshift; auto.
Qed.

Theorem fundamental :
  forall n G e ty,
    has_type.t n G e ty ->
    forall d g,
      length d = n ->
      Forall semtype.wf d ->
      Forall2 (fun ty e => V ty d e) G g ->
      E ty d (expr.subst g e).
Proof.
  induction 1; intros d g ? WFd WFg; subst n.
  - simpl. apply V_E; auto.
    destruct (Forall2_nth_error_r WFg H) as [v [Hv HV]].
    now rewrite Hv.
  - apply V_E; auto.
    cbn [expr.subst V].
    split.
    + cbn [expr.wf].
      apply expr.wf_subst.
      * apply has_type.t_expr_wf in H.
        cbn [length] in *.
        rewrite map_length.
        now erewrite <- Forall2_length by eauto.
      * constructor; [simpl; omega|].
        rewrite Forall_map.
        apply Forall_from_nth.
        intros n x Hnx.
        destruct (Forall2_nth_error_l WFg Hnx) as [y [Hny Vxy]].
        apply V_wf in Vxy; auto.
        now apply expr.wf_shift with (c := 0) (d := 1).
(*
    + cbn [expr.tywf]. intuition.
      apply expr.tywf_subst.
      * eapply has_type.t_expr_tywf; eauto.
      * constructor; simpl; [now auto|].
        rewrite Forall_map.
        apply Forall_from_nth.
        intros n x Hnx.
        destruct (Forall2_nth_error_l WFg Hnx) as [y [Hny Vxy]].
        apply expr.tywf_shift.
        eapply V_tywf; eauto.
*)
    + do 2 eexists. split; [reflexivity|].
      intros v2 V2.
      rewrite expr.subst_subst.
      * apply IHt; auto.
        simpl. rewrite map_map.
        constructor; [assumption|].
        erewrite map_ext_in.
        rewrite map_id.
        assumption.
        intros e' I. simpl.
        rewrite expr.subst_shift_singleton.
        reflexivity.
        destruct (In_nth_error _ _ I) as [n NE].
        destruct (Forall2_nth_error_l WFg NE) as [ty' [NE' V']].
        eapply V_wf; eauto.
      * simpl. rewrite map_length.
        apply has_type.t_expr_wf in H.
        erewrite <- Forall2_length by eauto.
        assumption.
      * simpl. constructor; [simpl; omega|].
        rewrite Forall_map.
        apply Forall_from_nth.
        intros n x NEx.
        apply expr.wf_shift with (d := 1).
        destruct (Forall2_nth_error_l WFg NEx) as [y [NEy Vxy]].
        eauto using V_wf.
  - cbn [expr.subst].
    specialize (IHt1 d g eq_refl WFd WFg).
    specialize (IHt2 d g eq_refl WFd WFg).
    destruct IHt1 as [v1 [S1 [Val1 V1]]].
    destruct IHt2 as [v2 [S2 [Val2 V2]]].
    destruct V1 as [WF1 [body [ty [? H1]]]].
    subst v1.
    apply E_star with (e' := expr.subst [v2] body); [|now eauto].
    eapply step.star_trans.
    eapply step.star_app1; eauto.
    eapply step.star_trans.
    eapply step.star_app2; eauto.
    eapply step.step_l.
    apply step.beta.
    assumption.
    constructor.
  - apply V_E; [assumption|].
    cbn [expr.subst V].
    split.
    + cbn [expr.wf]. apply expr.wf_subst.
      * eapply has_type.t_expr_wf in H.
        rewrite map_length in *.
        now erewrite <- Forall2_length by eauto.
      * rewrite Forall_map.
        apply Forall_from_nth.
        intros n x NEx.
        destruct (Forall2_nth_error_l WFg NEx) as [y [NEy Vy]].
        apply expr.wf_tyshift.
        eapply V_wf; eauto.
(*
    + cbn [expr.tywf].
      apply expr.tywf_subst.
      * eapply has_type.t_expr_tywf; eauto.
      * rewrite Forall_map.
        apply Forall_from_nth.
        intros n x NEx.
        destruct (Forall2_nth_error_l WFg NEx) as [y [NEy Vy]].
        apply expr.tywf_tyshift with (c := 0) (d := 1).
        eapply V_tywf; eauto.
*)
    + eexists. split; [reflexivity|].
      intros S SWF.
      apply IHt.
      * auto.
      * constructor; auto.
      * rewrite Forall2_map.
        eapply Forall2_impl; [|now eauto].
        simpl.
        intros ty' e' V'.
        now apply V_shift'; auto.
  -

Admitted.
