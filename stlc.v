Require Import util.

Module type.
  Inductive t :=
  | unit
  | arrow : t -> t -> t
  .
End type.

Module expr.
  Inductive t :=
  | var : nat -> t
  | tt : t
  | abs : t -> type.t -> t
  | app : t -> t -> t
  .

  Fixpoint wf (c : nat) (e : t) : Prop :=
    match e with
    | var x => x < c
    | tt => True
    | abs e' ty => wf (S c) e'
    | app e1 e2 => wf c e1 /\ wf c e2
    end.

  Fixpoint shift (c d : nat) (e : t) : t :=
    match e with
    | var x => var (if x <? c then x else d + x)
    | tt => tt
    | abs e' ty => abs (shift (S c) d e') ty
    | app e1 e2 => app (shift c d e1) (shift c d e2)
    end.

  Lemma wf_shift :
    forall e c d n,
      wf n e ->
      wf (d + n) (shift c d e).
  Proof.
    induction e; simpl; intros c d m H.
    - destruct (Nat.ltb_spec n c); omega.
    - auto.
    - rewrite plus_n_Sm. auto.
    - intuition.
  Qed.

  Lemma shift_0 :
    forall e c,
      shift c 0 e = e.
  Proof.
    induction e; simpl; intros c.
    - destruct (_ <? _); reflexivity.
    - reflexivity.
    - now f_equal; auto.
    - now f_equal; auto.
  Qed.

  Fixpoint subst (rho : list t) (e : t) : t :=
    match e with
    | var x => match List.nth_error rho x with
               | None => var x
               | Some e' => e'
               end
    | tt => tt
    | abs e ty => abs (subst (var 0 :: List.map (shift 0 1) rho) e) ty
    | app e1 e2 => app (subst rho e1) (subst rho e2)
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
    induction e as [x| | |]; intros n; cbn [subst].
    - destruct (nth_error (identity_subst n) x) eqn:E; auto.
      now apply nth_error_identity_subst in E.
    - now auto.
    - f_equal.
      now apply IHe with (n := (S n)).
    - now f_equal; auto.
  Qed.

  Lemma subst_empty :
    forall e,
      subst [] e = e.
  Proof.
    intros e.
    exact (subst_identity e 0).
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
    - reflexivity.
    - f_equal. now rewrite IHe by omega.
    - f_equal; eauto.
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
      destruct (nth_error rho n) eqn:?.
      + reflexivity.
      + pose proof nth_error_Some rho n.
        intuition.
    - reflexivity.
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
  Qed.
  
  Lemma subst_shift :
    forall e r1 r2 r3,
      wf (List.length (r1 ++ r3)) e ->
      subst (r1 ++ r2 ++ r3) (shift (List.length r1) (List.length r2) e) =
      subst (r1 ++ r3) e.
  Proof.
    induction e; simpl; intros r1 r2 r3 H.
    - destruct (Nat.ltb_spec n (length r1)).
      + now rewrite !nth_error_app1 by assumption.
      + rewrite !nth_error_app2 by omega.
        rewrite plus_comm.
        rewrite Nat.add_sub_swap by assumption.
        rewrite <- Nat.add_sub_assoc by omega.
        rewrite Nat.sub_diag.
        rewrite Nat.add_0_r.
        break_match; auto.
        pose proof nth_error_Some r3 (n - length r1).
        rewrite !app_length in *.
        intuition.
    - reflexivity.
    - f_equal.
      rewrite !map_app.
      rewrite !app_comm_cons.
      erewrite <- IHe.
      + f_equal. simpl.
        now rewrite !map_length.
      + simpl. now rewrite app_length, !map_length in *.
    - f_equal; intuition.
  Qed.
  
  Lemma subst_subst :
    forall e rho1 rho2,
      wf (List.length rho1) e ->
      List.Forall (wf (List.length rho2)) rho1 ->
      subst rho2 (subst rho1 e) =
      subst (List.map (subst rho2) rho1) e.
  Proof.
    induction e; intros rho1 rho2 WF F.
    - cbn [subst].
      cbn [wf] in WF.
      pose proof nth_error_Some rho1 n.
      rewrite nth_error_map.
      destruct (nth_error rho1 n) eqn:E; intuition congruence.
    - reflexivity.
    - cbn [subst].
      erewrite IHe.
      + f_equal. f_equal.
        simpl. f_equal.
        rewrite !map_map.
        apply map_ext_in.
        intros e' I.
        assert (wf (length rho2) e') by (eapply Forall_forall; eauto).
        rewrite shift_subst by assumption.
        apply subst_shift with (r1 := []) (r2 := [var 0]).
        simpl.
        now rewrite map_length.
      + simpl.
        now rewrite map_length.
      + simpl. constructor.
        * rewrite map_length. simpl. omega.
        * rewrite map_length.
          rewrite Forall_map.
          eapply Forall_impl; [|eauto].
          intros e' H.
          apply wf_shift with (d := 1); auto.
    - simpl in *.
      intuition.
      now rewrite IHe1, IHe2 by auto.
  Qed.

  Lemma wf_subst :
    forall e n rho,
      wf (length rho) e ->
      List.Forall (wf n) rho ->
      wf n (subst rho e).
  Proof.
    induction e; simpl; intros x rho WF F.
    - break_match.
      + now eapply Forall_nth; eauto.
      + pose proof nth_error_Some rho n.
        intuition.
    - auto.
    - eapply IHe; eauto.
      + simpl. now rewrite map_length.
      + constructor.
        * simpl. omega.
        * rewrite Forall_map.
          eapply Forall_impl; [|eauto].
          intros.
          now apply wf_shift with (d := 1).
    - intuition eauto.
  Qed.

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
      t G (expr.abs e ty1) (type.arrow ty1 ty2)
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
    destruct (Nat.ltb_spec x (length G1)).
    + now rewrite nth_error_app1 in * by assumption.
    + rewrite nth_error_app2 in * by omega.
      rewrite <- Nat.add_sub_assoc by assumption.
      rewrite nth_error_app2 in * by omega.
      rewrite Nat.add_sub_swap by reflexivity.
      now rewrite Nat.sub_diag, Nat.add_0_l.
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
  - econstructor.
    + now apply IHt1.
    + now apply IHt2.
Qed.

Module value.
  Inductive t : expr.t -> Prop :=
  | tt : t expr.tt
  | abs : forall ty e, t (expr.abs e ty)
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
  | beta : forall ty e1 e2,
      t (expr.app (expr.abs e1 ty) e2)
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
          e = expr.abs body ty1 /\
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
      * eauto using V_list_closed.
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
        rewrite expr.subst_shift with (r1 := []) (r2 := [e2]) (r3 := []).
        -- now rewrite expr.subst_identity with (n := 0).
        -- simpl.
           destruct (In_nth_error _ _ I) as [n NE].
           destruct (Forall2_nth_error_l F NE) as [ty [NE2 HV]].
           now eauto using V_closed.
      * simpl. rewrite map_length.
        eapply has_type_wf in H. simpl in *.
        now erewrite <- Forall2_length by eauto.
      * eauto using V_list_closed.
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

Theorem fundamental_closed :
  forall e ty,
    has_type.t [] e ty ->
    E ty e.
Proof.
  intros e ty HT.
  pose proof fundamental _ _ _ HT [] ltac:(constructor).
  now rewrite expr.subst_identity with (n := 0) in H.
Qed.
