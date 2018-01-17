Require Import util f.

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
      value.t e /\ expr.wf 0 e.
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
      exists body,
          e = expr.abs body /\
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
  - destruct HV as [WF [body [E H]]].
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
    destruct Vv as [WFe [body [? Ebody]]].
    split; auto.
    subst v.
    eexists.
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
    destruct Vv as [WF [body [? Hv]]].
    intuition.
    subst v.
    eexists.
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
    V ty d v <-> V (type.shift 0 1 ty) (S :: d) v.
Proof.
  intros.
  apply V_shift with (d1 := []) (d2 := [S]) (d3 := d); auto.
Qed.

Lemma terminating_iff :
  forall (P Q : expr.t -> Prop),
    (forall e, P e <-> Q e) ->
    (forall e, terminating.t P e <-> terminating.t Q e).
Proof.
  firstorder.
Qed.

Lemma V_map_identity :
  forall d2 d1,
    Forall2 (fun P Q => forall e, P e <-> Q e)
            (map (fun ty0 => V ty0 (d1 ++ d2)) (map (type.shift 0 (length d1)) (type.identity_subst (length d2))))
            d2.
Proof.
  induction d2; intros d1; simpl; constructor.
  - intros e.
    rewrite nth_error_app2 by omega.
    replace (length d1 + 0 - length d1)
       with 0 by omega.
    reflexivity.
  - rewrite map_map with (g := type.shift _ _).
    rewrite map_ext
       with (f := (fun x => type.shift 0 (length d1) (type.shift 0 1 x)))
            (g := (fun x => type.shift 0 (S (length d1)) x))
         by (intros; rewrite type.shift_merge; f_equal; omega).
    specialize (IHd2 (d1 ++ [a])).
    rewrite app_length in IHd2.
    cbn [length] in IHd2.
    rewrite <- plus_n_Sm in IHd2.
    rewrite <- plus_n_O in IHd2.
    rewrite map_ext
       with (f := (fun ty0 => V ty0 ((d1 ++ [a]) ++ d2)))
            (g := (fun ty0 => V ty0 (d1 ++ a :: d2)))
         in IHd2
         by (now intros; rewrite app_ass).
    auto.
Qed.

Lemma V_map_identity' :
  forall d,
    Forall2 (fun P Q => forall e, P e <-> Q e)
            (map (fun ty0 => V ty0 d) (type.identity_subst (length d)))
            d.
Proof.
  intros.
  pose proof V_map_identity d [].
  simpl in H.
  rewrite map_ext with (f := type.shift _ _) (g := fun x => x) in H by auto using type.shift_nop_d.
  now rewrite map_id in H.
Qed.

Lemma V_semtype :
  forall ty d,
    Forall semtype.wf d ->
    semtype.wf (V ty d).
Proof.
  intros.
  split.
  - eauto using V_value.
  - eauto using V_wf.
Qed.

Lemma V_ext :
  forall ty d1 d2,
    Forall2 (fun P Q => forall e, P e <-> Q e) d1 d2 ->
    forall e,
      V ty d1 e <-> V ty d2 e.
Proof.
  induction ty; simpl; intros d1 d2 F e.
  - break_match.
    + destruct (Forall2_nth_error_r F Heqo) as [t' [NE' H]].
      unfold semtype.t.
      now rewrite NE'.
    + pose proof Forall2_length F.
      pose proof nth_error_None d1 alpha.
      pose proof nth_error_None d2 alpha.
      assert (nth_error d2 alpha = None) by intuition.
      unfold semtype.t. rewrite H2.
      intuition.
  - specialize (IHty1 d1 d2 F).
    specialize (IHty2 d1 d2 F).
    split; intros [WF [body [? H]]]; (split; [assumption|]); subst; exists body; (split; [reflexivity|]);
      intros e2 V2.
    + rewrite <- terminating_iff.
      apply H.
      firstorder.
      assumption.
    + rewrite terminating_iff.
      apply H.
      firstorder.
      assumption.
  - split; intros [WF [body [? H]]]; (split; [assumption|]); subst; exists body; (split; [reflexivity|]);
      intros S SWF; specialize (IHty (S :: d1) (S :: d2)).
    + rewrite <- terminating_iff.
      apply H.
      apply SWF.
      apply IHty.
      constructor; intuition.
    + rewrite terminating_iff.
      apply H.
      apply SWF.
      apply IHty.
      constructor; intuition.
Qed.

Lemma V_subst :
  forall ty D d,
    type.wf (length D) ty ->
    Forall (type.wf (length d)) D ->
    Forall semtype.wf d ->
    (forall e, V (type.subst D ty) d e <-> V ty (map (fun ty0 => V ty0 d) D) e).
Proof.
  induction ty; simpl; intros D d WFty F e.
  - rewrite nth_error_map.
    break_match; [now intuition|].
    pose proof nth_error_None D alpha.
    now firstorder.
  - unfold terminating.t.
    setoid_rewrite IHty1; try solve [intuition].
    setoid_rewrite IHty2; try solve [intuition].
  - unfold terminating.t.
    split; intros [WF [body [? Ebody]]]; (split;[assumption|]);
      subst; exists body; (split; [reflexivity|]);
        intros S SWF; specialize (Ebody S SWF);
          destruct Ebody as [v [Star [Val Vv]]]; exists v; intuition.
    + rewrite IHty in Vv.
      * simpl in Vv. rewrite map_map in Vv.
        eapply V_ext; [|apply Vv].
        constructor; [now intuition|].
        apply Forall2_map.
        apply Forall2_forall_suff_weak; auto.
        intros.
        assert (y = z) by congruence.
        subst.
        apply V_shift'; auto.
      * simpl. rewrite map_length. auto.
      * simpl. constructor; [simpl; omega|].
        rewrite Forall_map.
        apply Forall_from_nth.
        intros.
        apply type.wf_shift with (d := 1).
        eapply Forall_nth; eauto.
      * constructor; auto.
    + rewrite IHty.
      * simpl. rewrite map_map.
        eapply V_ext; [|apply Vv].
        constructor; [now intuition|].
        apply Forall2_map.
        apply Forall2_forall_suff_weak; auto.
        intros.
        assert (y = z) by congruence.
        subst.
        rewrite <- V_shift'; intuition.
      * simpl. rewrite map_length. auto.
      * simpl. constructor; [simpl; omega|].
        rewrite Forall_map.
        apply Forall_from_nth.
        intros.
        apply type.wf_shift with (d := 1).
        eapply Forall_nth; eauto.
      * constructor; auto.
Qed.

Lemma E_subst :
  forall ty D d,
    type.wf (length D) ty ->
    Forall (type.wf (length d)) D ->
    Forall semtype.wf d ->
    (forall e, E (type.subst D ty) d e <-> E ty (map (fun ty0 => V ty0 d) D) e).
Proof.
  intros ty D d TWF F SWF.
  apply terminating_iff.
  apply V_subst; auto.
Qed.

Theorem fundamental :
  forall n G e ty,
    Forall (type.wf n) G ->
    has_type.t n G e ty ->
    forall d g,
      length d = n ->
      Forall semtype.wf d ->
      Forall2 (fun ty e => V ty d e) G g ->
      E ty d (expr.subst g e).
Proof.
  intros n G e ty GWF HT.
  induction HT; intros d g ? WFd WFg; subst n.
  - simpl. apply V_E; auto.
    destruct (Forall2_nth_error_r WFg H) as [v [Hv HV]].
    now rewrite Hv.
  - apply V_E; auto.
    cbn [expr.subst V].
    split.
    + cbn [expr.wf].
      apply expr.wf_subst.
      * apply has_type.t_expr_wf in HT.
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
    + eexists. split; [reflexivity|].
      intros v2 V2.
      rewrite expr.subst_subst.
      * apply IHHT; auto.
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
        apply has_type.t_expr_wf in HT.
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
    specialize (IHHT1 GWF d g eq_refl WFd WFg).
    specialize (IHHT2 GWF d g eq_refl WFd WFg).
    destruct IHHT1 as [v1 [S1 [Val1 V1]]].
    destruct IHHT2 as [v2 [S2 [Val2 V2]]].
    destruct V1 as [WF1 [body [? H1]]].
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
      * eapply has_type.t_expr_wf in HT.
        rewrite map_length in *.
        now erewrite <- Forall2_length by eauto.
      * apply Forall_from_nth.
        intros n x NEx.
        destruct (Forall2_nth_error_l WFg NEx) as [y [NEy Vy]].
        eapply V_wf; eauto.
    + eexists. split; [reflexivity|].
      intros S SWF.
      apply IHHT.
      * rewrite Forall_map. eapply Forall_impl; [| apply GWF].
        intros ty' WF'.
        now apply type.wf_shift with (c := 0) (d := 1).
      * auto.
      * constructor; auto.
      * apply Forall2_map_l.
        eapply Forall2_impl; [|now eauto].
        simpl.
        intros ty' e' V'.
        now apply V_shift'; auto.
  - specialize (IHHT GWF d g eq_refl WFd WFg).
    destruct IHHT as [v [S [Val Vv]]].
    destruct Vv as [WFv [body [? Ebody]]].
    cbn [expr.subst].
    subst v.
    eapply E_star.
    eapply step.star_trans.
    eapply step.star_tyapp.
    eauto.
    eapply step.step_l.
    apply step.tybeta.
    constructor.
    apply E_subst.
    + simpl. rewrite type.identity_subst_length.
      apply has_type.t_type_wf in HT; auto.
    + constructor; auto.
      apply type.identity_subst_wf.
    + auto.
    + simpl.
      eapply terminating_iff; [| apply Ebody with (S := V ty d); auto using V_semtype].
      intros e'.
      apply V_ext.
      constructor; [now intuition|].
      apply V_map_identity'.
Qed.

Print Assumptions fundamental.

Corollary fundamental_closed :
  forall e ty,
    has_type.t 0 [] e ty ->
    E ty [] e.
Proof.
  intros e ty HT.
  rewrite <- expr.subst_identity with (n := 0).
  eapply fundamental; try apply HT; try constructor.
Qed.

Corollary termination :
  forall e ty,
    has_type.t 0 [] e ty ->
    exists v, value.t v /\ step.star e v.
Proof.
  intros e ty HT.
  destruct (fundamental_closed e ty HT) as [v [Star [Val _]]].
  eauto.
Qed.

Corollary no_universal_value :
  forall e,
    has_type.t 0 [] e (type.all (type.var 0)) ->
    False.
Proof.
  intros e HT.
  pose proof fundamental_closed e _ HT as Ee.
  destruct Ee as [v [Star [Val Vv]]].
  cbn [V] in Vv.
  destruct Vv as [WF [body [? Ebody]]].
  subst v.
  set (S := fun _ : expr.t => False).
  assert (semtype.wf S) as SWF.
  {
    unfold semtype.wf.
    subst S.
    simpl.
    now intuition.
  }
  specialize (Ebody S SWF).
  destruct Ebody as [v' [Star' [Val' Vv']]].
  simpl in *.
  exact Vv'.
Qed.

Lemma fundamental_value :
  forall v ty,
    has_type.t 0 [] v ty ->
    value.t v ->
    V ty [] v.
Proof.
  intros v ty HT Val.
  pose proof fundamental_closed v ty HT as Ev.
  destruct Ev as [v' [Star [Val' Vv']]].
  apply step.star_value in Star; auto.
  subst.
  auto.
Qed.

Corollary identity_is_identity :
  forall e ty v,
    has_type.t 0 [] e (type.all (type.arrow (type.var 0) (type.var 0))) ->
    has_type.t 0 [] v ty ->
    value.t v ->
    step.star (expr.app (expr.tyapp e) v) v.
Proof.
  intros e ty v HTe HTv Val.
  pose proof HTe as HTe0.
  apply fundamental_closed in HTe.
  destruct HTe as [v1 [Star [Val1 V1]]].
  cbn [V] in V1.
  destruct V1 as [WF1 [body [? Sbody]]].
  subst.
  set (S := fun x => x = v).
  assert (semtype.wf S) as SWF.
  { unfold semtype.wf. subst S. simpl. intros. subst.
    intuition.
    now apply has_type.t_expr_wf in HTv.
  }
  specialize (Sbody S SWF).
  destruct Sbody as [vbody [Star' [Val' [WF' [body' [? Vbody']]]]]].
  subst.
  simpl in *.
  specialize (Vbody' v eq_refl).
  destruct Vbody' as [v'' [Star'' [Val'' Sv'']]].
  subst S. simpl in *.
  subst v''.
  eapply step.star_trans.
  eapply step.star_app1.
  eapply step.star_tyapp.
  eassumption.
  eapply step.star_trans.
  eapply step.star_app1.
  eapply step.step_l.
  eapply step.tybeta.
  eassumption.
  eapply step.step_l.
  apply step.beta; auto.
  auto.
Qed.


