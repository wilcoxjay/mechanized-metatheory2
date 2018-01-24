From mm Require Import util f.

Module terminating.
  Definition t (P : expr.t -> Prop) (e : expr.t) :=
    exists v,
      step.star e v /\
      value.t v /\
      P v
  .

  Lemma impl :
    forall (P Q : expr.t -> Prop),
      (forall e, P e -> Q e) ->
      (forall e, terminating.t P e -> terminating.t Q e).
  Proof. firstorder. Qed.

  Lemma iff :
    forall (P Q : expr.t -> Prop),
      (forall e, P e <-> Q e) ->
      (forall e, terminating.t P e <-> terminating.t Q e).
  Proof. firstorder. Qed.
End terminating.

Module candidate.
  Definition t := expr.t -> Prop.

  Definition wf (S : t) :=
    forall e,
      S e ->
      value.t e /\ expr.wf 0 e.
End candidate.

Fixpoint V ty (d : list candidate.t) e :=
  match ty with
  | type_ast.var alpha =>
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
      forall (S : candidate.t),
        candidate.wf S  ->
        terminating.t (V ty' (S :: d)) body
  | type.exist ty' =>
    expr.wf 0 e /\
    exists v,
      value.t v /\
      e = expr.pack v /\
      exists S : candidate.t,
        candidate.wf S /\
        V ty' (S :: d) v
    | type.bool => e = expr.tt \/ e = expr.ff
  end.

Notation E ty d :=
  (terminating.t (V ty d)).

Lemma V_value :
  forall ty d v,
    Forall candidate.wf d ->
    V ty d v ->
    value.t v.
Proof.
  intros ty d v WFd HV.
  destruct ty; cbn in HV.
  - break_match; intuition.
    assert (candidate.wf t) by (eapply Forall_nth_error; eauto).
    now firstorder.
  - destruct HV as [WF [body [E H]]].
    subst. constructor.
  - destruct HV as [WF [body [E H]]].
    subst. constructor.
  - destruct HV as [WF [v' [Valv' [? [S [SWF Vv']]]]]].
    subst. constructor. auto.
  - intuition; subst; constructor.
Qed.

Lemma V_wf :
  forall ty d v,
    Forall candidate.wf d ->
    V ty d v ->
    expr.wf 0 v.
Proof.
  intros ty d v F.
  destruct ty; cbn [V]; intuition.
  - break_match; intuition.
    assert (candidate.wf t) by (eapply Forall_nth_error; eauto).
    firstorder.
  - subst; simpl; auto.
  - subst; simpl; auto.
Qed.

Lemma V_list_closed :
  forall G d vs,
    Forall candidate.wf d ->
    Forall2 (fun ty v => V ty d v) G vs ->
    Forall (expr.wf 0) vs.
Proof.
  intros G d vs WFd WFvs.
  apply Forall_from_nth.
  intros n e NEe.
  destruct (Forall2_nth_error2 WFvs NEe) as [ty [NEty Ve]].
  eauto using V_wf.
Qed.

Lemma V_E :
  forall ty d v,
    Forall candidate.wf d ->
    V ty d v ->
    E ty d v.
Proof.
  intros.
  exists v.
  intuition.
  eauto using V_value.
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

Lemma V_shift :
  forall ty d1 d2 d3 v,
    Forall candidate.wf (d1 ++ d3) ->
    V ty (d1 ++ d3) v <->
    V (type.shift (length d1) (length d2) ty) (d1 ++ d2 ++ d3) v.
Proof.
  induction ty as [alpha| | | |]; intros d1 d2 d3 v F; simpl.
  - destruct (Nat.ltb_spec alpha (length d1)).
    + rewrite !nth_error_app1 by assumption. intuition.
    + rewrite !nth_error_app2 by omega.
      do_app2_minus.
      now auto.
  - split; intros Vv; destruct Vv as [WF [body [? Hv]]]; (split; [assumption|]);
      subst v; eexists; (split; [reflexivity|]);
        intros v2 V2.
    + rewrite <- IHty1 in V2 by assumption.
      apply Hv in V2.
      eapply terminating.impl; [|eassumption].
      intros e; rewrite IHty2; eauto.
    + rewrite (IHty1 d1 d2 d3) in V2 by assumption.
      apply Hv in V2.
      eapply terminating.impl; [|eassumption].
      intros e; rewrite IHty2; eauto.
  - split; intros Vv; destruct Vv as [Wf [body [? Hv]]];
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
  - split; intros Vv; destruct Vv as [WF [v' [Val' [? [S [SWF Vv']]]]]];
      split; auto; subst v; eexists; (split; [eassumption|]); (split; [reflexivity|]);
        exists S; (split; [assumption|]).
    + rewrite app_comm_cons.
      rewrite <- IHty with (d1 := (S :: d1)); auto.
      constructor; auto.
    + rewrite app_comm_cons in *.
      rewrite IHty with (d1 := (S :: d1)); eauto.
      constructor; auto.
  - firstorder.
Qed.

Lemma V_shift' :
  forall ty S d v,
    Forall candidate.wf d ->
    V ty d v <-> V (type.shift 0 1 ty) (S :: d) v.
Proof.
  intros.
  apply V_shift with (d1 := []) (d2 := [S]) (d3 := d); auto.
Qed.

Lemma V_map_identity :
  forall d2 d1,
    Forall2 (fun P Q => forall e, P e <-> Q e)
            (map (fun ty0 => V ty0 (d1 ++ d2))
                 (map (type.shift 0 (length d1)) (type.identity_subst (length d2))))
            d2.
Proof.
  induction d2; intros d1; simpl; constructor.
  - intros e.
    rewrite nth_error_app2 by omega.
    rewrite Nat.sub_diag.
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

Lemma V_candidate :
  forall ty d,
    Forall candidate.wf d ->
    candidate.wf (V ty d).
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
    + destruct (Forall2_nth_error1 F Heqo) as [t' [NE' H]].
      unfold candidate.t.
      now rewrite NE'.
    + pose proof Forall2_length F.
      pose proof nth_error_None d1 alpha.
      pose proof nth_error_None d2 alpha.
      assert (nth_error d2 alpha = None) by intuition.
      unfold candidate.t. rewrite H2.
      intuition.
  - specialize (IHty1 d1 d2 F).
    specialize (IHty2 d1 d2 F).
    split; intros [WF [body [? H]]];
      (split; [assumption|]);
      subst; exists body;
        (split; [reflexivity|]);
        intros e2 V2.
    + rewrite <- terminating.iff.
      apply H.
      firstorder.
      assumption.
    + rewrite terminating.iff.
      apply H.
      firstorder.
      assumption.
  - split; intros [WF [body [? H]]];
      (split; [assumption|]);
      subst; exists body;
        (split; [reflexivity|]);
        intros S SWF;
        specialize (IHty (S :: d1) (S :: d2)).
    + rewrite <- terminating.iff.
      apply H.
      apply SWF.
      apply IHty.
      constructor; intuition.
    + rewrite terminating.iff.
      apply H.
      apply SWF.
      apply IHty.
      constructor; intuition.
  - split; intros Vv; destruct Vv as [WF [v' [Val' [? [S [SWF Vv']]]]]];
      split; auto; subst e; eexists; (split; [eassumption|]); (split; [reflexivity|]);
        exists S; (split; [assumption|]).
    + rewrite <- IHty.
      apply Vv'.
      constructor; auto.
      intuition.
    + rewrite IHty.
      apply Vv'.
      constructor; auto.
      intuition.
  - firstorder.
Qed.

Lemma V_Forall_equiv_shift' :
  forall d D S,
    Forall candidate.wf d ->
    Forall2 (fun P Q => forall e, P e <-> Q e)
            (map (fun ty => V ty d) D)
            (map (fun ty => V (type.shift 0 1 ty) (S :: d)) D).
Proof.
  intros d D S F.
  apply Forall2_map.
  apply Forall2_from_forall; auto.
  intros x y z NEy NEz e.
  unfold type_basis.t in *.
  assert (y = z) by congruence.
  subst.
  apply V_shift'; auto.
Qed.

Lemma V_descend :
  forall ty S d D v,
    Forall candidate.wf d ->
    V ty (S :: map (fun ty0 => V ty0 d) D) v <->
    V ty (map (fun ty0 => V ty0 (S :: d)) (type.descend 1 D)) v.
Proof.
  intros ty S d D v F.
  simpl. rewrite map_map.
  split; intro Vv.
  - erewrite <- V_ext. eassumption.
    constructor; intuition auto using V_Forall_equiv_shift'.
  - erewrite V_ext. eassumption.
    constructor; intuition auto using V_Forall_equiv_shift'.
Qed.

Lemma V_subst :
  forall ty D d,
    type.wf (length D) ty ->
    Forall (type.wf (length d)) D ->
    Forall candidate.wf d ->
    (forall e, V (type.subst D ty) d e <-> V ty (map (fun ty0 => V ty0 d) D) e).
Proof.
  induction ty; simpl; intros D d WFty F WFd e.
  - rewrite nth_error_map.
    break_match; intuition.
    pose proof nth_error_None D alpha.
    now firstorder.
  - unfold terminating.t.
    setoid_rewrite IHty1; try solve [intuition].
    setoid_rewrite IHty2; try solve [intuition].
  - unfold terminating.t.
    rewrite <- type.descend_1 in *.
    split; intros [WF [body [? Ebody]]]; (split;[assumption|]);
      subst; exists body; (split; [reflexivity|]);
        intros S SWF; specialize (Ebody S SWF);
          destruct Ebody as [v [Star [Val Vv]]]; exists v; intuition.
    + rewrite IHty in Vv.
      * now rewrite V_descend.
      * now rewrite type.descend_length.
      * now apply type.descend_wf with (s := 1).
      * constructor; auto.
    + rewrite IHty.
      * now rewrite <- V_descend.
      * now rewrite type.descend_length.
      * now apply type.descend_wf with (s := 1).
      * constructor; auto.
  - rewrite <- type.descend_1 in *.
    split; intros Vv; destruct Vv as [WF [v' [Val' [? [S [SWF Vv']]]]]];
      split; auto; subst e; eexists; (split; [eassumption|]); (split; [reflexivity|]);
        exists S; (split; [assumption|]).
    + rewrite IHty in Vv'.
      * now rewrite V_descend.
      * now rewrite type.descend_length.
      * now apply type.descend_wf with (s := 1).
      * constructor; auto.
    + rewrite IHty.
      * now rewrite <- V_descend.
      * now rewrite type.descend_length.
      * now apply type.descend_wf with (s := 1).
      * constructor; auto.
  - firstorder.
Qed.

Lemma E_subst :
  forall ty D d,
    type.wf (length D) ty ->
    Forall (type.wf (length d)) D ->
    Forall candidate.wf d ->
    (forall e, E (type.subst D ty) d e <-> E ty (map (fun ty0 => V ty0 d) D) e).
Proof.
  intros ty D d TWF F SWF.
  apply terminating.iff.
  apply V_subst; auto.
Qed.

Lemma V_map_shift' :
  forall S d G g,
    Forall candidate.wf d ->
    Forall2 (fun ty e => V ty d e) G g ->
    Forall2 (fun ty e => V ty (S :: d) e) (map (type.shift 0 1) G) g.
Proof.
  intros S d G g WFd WFg.
  apply Forall2_map_l.
  eapply Forall2_impl; [|now eauto].
  simpl.
  intros ty' e' V'.
  now apply V_shift'; auto.
Qed.

Module has_sem_type.
  Definition t n G e ty :=
    [/\ expr.wf (length G) e
     , type.wf n ty
     , Forall (type.wf n) G
     & forall d g,
         length d = n ->
         Forall candidate.wf d ->
         Forall2 (fun ty e => V ty d e) G g ->
         E ty d (expr.subst g e)
    ].

  Lemma var :
    forall n G x ty,
      Forall (type.wf n) G ->
      type.wf n ty ->
      nth_error G x = Some ty ->
      t n G (expr.var x) ty.
  Proof.
    intros n G x ty F WFty NE.
    split; auto.
    - do_nth_error_Some.
      simpl.
      apply H. congruence.
    - intros d g ? WFd WFg.
      simpl. apply V_E; auto.
      destruct (Forall2_nth_error1 WFg NE) as [v [Hv HV]].
      unfold expr.t in *.
      now rewrite Hv.
  Qed.

  Lemma abs :
    forall n G e ty1 ty2,
      t n (ty1 :: G) e ty2 ->
      t n G (expr.abs e) (type.arrow ty1 ty2).
  Proof.
    intros n G e ty1 ty2 [WFe WFty WFG HT].
    invc WFG.
    split; [now auto| now auto| now simpl; auto|].
    intros d g ? WFd WFg.
    apply V_E; auto.
    cbn [expr.subst V].
    rewrite <- expr.descend_1.
    pose proof (Forall2_length WFg) as EG.
    split.
    + apply expr.wf_subst.
      * now rewrite expr.descend_length, <- EG.
      * apply expr.descend_wf with (s := 1).
        eauto using V_list_closed.
    + exists (expr.subst (expr.descend 1 g) e).
      split; [now rewrite expr.descend_1|].
      intros v Vv.
      rewrite !expr.subst_cons;
        firstorder using V_list_closed.
      now rewrite <- EG.
  Qed.

  Lemma app :
    forall n G e1 e2 ty1 ty2,
      t n G e1 (type.arrow ty1 ty2) ->
      t n G e2 ty1 ->
      t n G (expr.app e1 e2) ty2.
  Proof.
    intros n G e1 e2 ty1 ty2.
    intros [WFe1 [WFty1 WFty2] WFG HT1].
    intros [WFe2 _ _ HT2].
    split; [ now cbn; auto | now auto | now auto|].
    intros d g E WFd WFg.

    cbn [expr.subst].
    specialize (HT1 d g E WFd WFg).
    specialize (HT2 d g E WFd WFg).
    destruct HT1 as [v1 [Star1 [Val1 V1]]].
    destruct HT2 as [v2 [Star2 [Val2 V2]]].
    destruct V1 as [WFv1 [body1 [? H1]]].
    subst v1.
    eapply E_star; [|now eauto].

    eapply step.star_trans.
    eapply step.star_app1. now eauto.
    eapply step.star_trans.
    now eapply step.star_app2; eauto.
    eauto using step.step_l, step.beta.
  Qed.

  Lemma tyabs :
    forall n G e ty,
      t (S n) (map (type.shift 0 1) G) e ty ->
      t n G (expr.tyabs e) (type.all ty).
  Proof.
    intros n G e ty [WFe WFty WFmG HT].
    rewrite map_length in *.
    split; [assumption|assumption|now auto using type.wf_map_shift_inv'|].
    intros d g ? WFd WFg.
    apply V_E; [assumption|].
    cbn [expr.subst V].
    pose proof (Forall2_length WFg) as EG.
    split.
    + apply expr.wf_subst.
      * now rewrite <- EG.
      * eauto using V_list_closed.
    + eexists. split; [reflexivity|].
      intros S SWF.
      apply HT.
      * simpl. congruence.
      * auto.
      * auto using V_map_shift'.
  Qed.

  Lemma tyapp :
    forall n G e ty_body ty,
      type.wf n ty ->
      t n G e (type.all ty_body) -> 
      t n G (expr.tyapp e) (type.subst (ty :: type.identity_subst n) ty_body).
  Proof.
    intros n G e ty_body ty WFty [WFe WFtyall WFG HT].
    split; [assumption| now auto using type.wf_subst_id | now auto |].

    intros d g En WFd WFg. subst n.
    specialize (HT d g eq_refl WFd WFg).
    destruct HT as [v [S [Val Vv]]].
    destruct Vv as [WFv [body [? Ebody]]].
    cbn [expr.subst].
    subst v.
    eapply E_star.
    eapply step.star_trans.
    eapply step.star_tyapp. now eauto.
    eapply step.step_l.
    apply step.tybeta.
    now constructor.

    apply E_subst.
    + simpl. now rewrite type.identity_subst_length.
    + auto using type.wf_identity_subst.
    + auto.
    + simpl.
      eapply terminating.iff; [| apply Ebody with (S := V ty d); auto using V_candidate].
      intros e'.
      apply V_ext.
      constructor; [now intuition|].
      apply V_map_identity'.
  Qed.

  Lemma pack :
    forall n G e ty_interface ty_rep,
      type.wf n ty_rep ->
      t n G e (type.subst (ty_rep :: type.identity_subst n) ty_interface) ->
      t n G (expr.pack e) (type.exist ty_interface).
  Proof.
    intros n G e ty_interface ty_rep WFrep [WFe WFtysubst WFG HT].

    split; [ now auto | now simpl; eauto using type.wf_subst_id_inv | now auto | ].

    intros d g En WFd WFg. subst n.

    specialize (HT d g eq_refl WFd WFg).
    destruct HT as [v [Star [Val Vv]]].
    rewrite V_subst in Vv; auto using type.wf_identity_subst.
    + cbn [expr.subst].
      eapply E_star.
      apply step.star_pack. eassumption.
      apply V_E; auto.
      rewrite V_ext with (d2 := V ty_rep d :: d) in Vv
        by (simpl; constructor; intuition; apply V_map_identity').
      cbn [V].
      split.
      * simpl. eauto using V_wf, V_candidate.
      * eauto 10 using V_candidate.
    + simpl. rewrite type.identity_subst_length.
      eauto using type.wf_subst_id_inv. 
  Qed.

  Lemma unpack :
    forall n G e1 e2 ty1 ty2,
      t n G e1 (type.exist ty1) ->
      t (S n) (ty1 :: map (type.shift 0 1) G) e2 (type.shift 0 1 ty2) ->
      t n G (expr.unpack e1 e2) ty2.
  Proof.
    intros n G e1 e2 ty1 ty2 [WFe1 WFexty1 WFG HT1] [WFe2 WFty2 _ HT2].
    split; [ now simpl in *; rewrite map_length in *; auto | now auto using type.wf_shift_inv' | now auto | ].
    intros d g En WFd WFg. subst n.
    cbn[length] in WFe2. rewrite map_length in WFe2.

    specialize (HT1 d g eq_refl WFd WFg).
    destruct HT1 as [v1 [Star1 [Val1 Vv1]]].
    cbn [V] in Vv1.
    destruct Vv1 as [WFv1 [v2 [Val2 [? [S [SWF Vv2]]]]]].
    subst v1.
    cbn [expr.subst].
    eapply E_star.
    eapply step.star_trans.
    apply step.star_unpack. eassumption.
    eapply step.step_l.
    apply step.packbeta. assumption.
    constructor.

    rewrite <- expr.descend_1.
    rewrite expr.subst_cons.
    - set (G' := ty1 :: map (type.shift 0 1) G) in *.
      specialize (HT2 (S :: d) (v2 :: g) eq_refl ltac:(auto)
                      ltac:(subst G'; auto using V_map_shift')).
      destruct HT2 as [v3 [Star3 [Val3 Vv3]]].
      eapply E_star. eauto.
      rewrite <- V_shift' in Vv3 by auto.
      apply V_E; auto.
    - unfold type.t in *.
      now rewrite (Forall2_length WFg) in *.
    - eauto using V_list_closed.
  Qed.

  Lemma tt :
    forall n G,
      Forall (type.wf n) G ->
      t n G expr.tt type.bool.
  Proof.
    intros n G F.
    split; [ now simpl; auto | now simpl; auto | assumption | ].
    intros d g En WFd WFg.
    apply V_E; [assumption|].
    cbn.
    intuition.
  Qed.

  Lemma ff :
    forall n G,
      Forall (type.wf n) G ->
      t n G expr.ff type.bool.
  Proof.
    intros n G F.
    split; [ now simpl; auto | now simpl; auto | assumption | ].
    intros d g En WFd WFg.
    apply V_E; [assumption|].
    cbn.
    intuition.
  Qed.

  Lemma If :
    forall G n e1 e2 e3 ty,
      t n G e1 type.bool ->
      t n G e2 ty ->
      t n G e3 ty ->
      t n G (expr.If e1 e2 e3) ty.
  Proof.
    intros G n e1 e2 e3 ty.
    intros [WFe1 _ WFG HT1].
    intros [WFe2 WFty _ HT2].
    intros [WFe3 _ _ HT3].
    split; [ now simpl; auto | assumption | assumption | ].
    intros d g En WFd WFg.

    cbn [expr.subst].
    specialize (HT1 d g En WFd WFg).
    destruct HT1 as [v1 [Star1 [Val1 V1]]].
    eapply E_star; [apply step.star_If|]; eauto.
    destruct V1 as [?|?]; subst;
      (eapply E_step; [constructor|]); auto.
  Qed.
End has_sem_type.

Theorem fundamental :
  forall n G e ty,
    Forall (type.wf n) G ->
    has_type.t n G e ty ->
    has_sem_type.t n G e ty.
Proof.
  intros n G e ty GWF HT.
  induction HT.
  - apply has_sem_type.var; eauto.
    eapply Forall_nth_error; eauto.
  - now apply has_sem_type.abs; auto.
  - now eapply has_sem_type.app; eauto.
  - now apply has_sem_type.tyabs; auto using type.wf_map_shift'.
  - now apply has_sem_type.tyapp; auto.
  - now eapply has_sem_type.pack; eauto.
  - subst ty2.
    apply has_type.t_type_wf in HT1; auto.
    now eapply has_sem_type.unpack; eauto using type.wf_map_shift'.
  - now apply has_sem_type.tt.
  - now apply has_sem_type.ff.
  - now apply has_sem_type.If; auto.
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
  assert (candidate.wf S) as SWF.
  {
    unfold candidate.wf.
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
  assert (candidate.wf S) as SWF.
  { unfold candidate.wf. subst S. simpl. intros. subst.
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

Corollary there_are_two_bools :
  forall e ty v1 v2,
    has_type.t 0 [] e (type.all (type.arrow (type.var 0)
                                            (type.arrow (type.var 0) (type.var 0)))) ->
    has_type.t 0 [] v1 ty -> 
    has_type.t 0 [] v2 ty ->
    value.t v1 ->
    value.t v2 ->
    step.star (expr.app (expr.app (expr.tyapp e) v1) v2) v1 \/
    step.star (expr.app (expr.app (expr.tyapp e) v1) v2) v2.
Proof.
  intros e ty v1 v2 HTe HTv1 HTv2 Val1 Val2.
  apply fundamental_closed in HTe.
  destruct HTe as [f [Star [Valf Vf]]].
  cbn [V] in Vf.
  destruct Vf as [WFf [body [? Hf]]]. subst f.
  set (S := fun x => x = v1 \/ x = v2).
  assert (candidate.wf S) as SWF.
  { unfold candidate.wf. subst S. simpl. intros.
    intuition; subst; auto.
    - now apply has_type.t_expr_wf in HTv1.
    - now apply has_type.t_expr_wf in HTv2.
  }

  specialize (Hf S SWF).
  destruct Hf as [v' [Star' [Val' [WFv' [body' [? Hbody']]]]]].
  simpl in Hbody'. subst v'.
  specialize (Hbody' v1 (or_introl eq_refl)).
  destruct Hbody' as [v'' [Star'' [Val'' [WFv'' [body'' [? Hbody'']]]]]].
  subst v''.
  specialize (Hbody'' v2 (or_intror eq_refl)).
  destruct Hbody'' as [v''' [Star''' [Val''' Sv''']]].
  destruct Sv'''; [left|right]; subst v'''.
  - eapply step.star_trans.
    apply step.star_app1.
    eapply step.star_trans.
    apply step.star_app1.
    eapply step.star_trans.
    apply step.star_tyapp.
    eauto.
    eapply step.step_l.
    apply step.tybeta.
    eauto.
    eapply step.step_l.
    apply step.beta. assumption.
    eauto.
    eapply step.step_l.
    apply step.beta. assumption.
    assumption.
  - eapply step.star_trans.
    apply step.star_app1.
    eapply step.star_trans.
    apply step.star_app1.
    eapply step.star_trans.
    apply step.star_tyapp.
    eauto.
    eapply step.step_l.
    apply step.tybeta.
    eauto.
    eapply step.step_l.
    apply step.beta. assumption.
    eauto.
    eapply step.step_l.
    apply step.beta. assumption.
    assumption.
Qed.

