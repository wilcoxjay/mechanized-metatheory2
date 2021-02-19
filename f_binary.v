From mm Require Import util f.
Set Implicit Arguments.

Module terminating.
  Definition t (P : expr.t -> expr.t -> Prop) (e1 e2 : expr.t) :=
    exists v1 v2,
      [/\ step.star e1 v1
       , step.star e2 v2
       , value.t v1
       , value.t v2
       & P v1 v2
      ]
  .

  Lemma impl :
    forall (P Q : expr.t -> expr.t -> Prop),
      (forall e1 e2, P e1 e2 -> Q e1 e2) ->
      (forall e1 e2, terminating.t P e1 e2 -> terminating.t Q e1 e2).
  Proof. firstorder. Qed.

  Lemma iff :
    forall (P Q : expr.t -> expr.t -> Prop),
      (forall e1 e2, P e1 e2 <-> Q e1 e2) ->
      (forall e1 e2, terminating.t P e1 e2 <-> terminating.t Q e1 e2).
  Proof.
    intros P Q HPQ e1 e2.
    split; apply impl; firstorder.
  Qed.
End terminating.


Module candidate.
  Definition t := expr.t -> expr.t -> Prop.

  Definition wf (S : t) :=
    forall e1 e2,
      S e1 e2 ->
      [/\ value.t e1
       , expr.wf 0 e1
       , value.t e2
       & expr.wf 0 e2
      ]
  .
End candidate.

Fixpoint V ty (d : list candidate.t) e1 e2 :=
  match ty with
  | type_ast.var alpha =>
    match nth_error d alpha with
    | Some X => X e1 e2
    | None => False
    end
  | type.arrow ty1 ty2 =>
    [/\ expr.wf 0 e1
     , expr.wf 0 e2
     & exists body1 body2,
         [/\ e1 = expr.abs body1
          , e2 = expr.abs body2
          & forall v1 v2,
              V ty1 d v1 v2 ->
              terminating.t (V ty2 d) (expr.subst [v1] body1) (expr.subst [v2] body2)
         ]
    ]
  | type.all ty' =>
    [/\ expr.wf 0 e1
     , expr.wf 0 e2
     & exists body1 body2,
         [/\ e1 = expr.tyabs body1
          , e2 = expr.tyabs body2
          & forall (S : candidate.t),
              candidate.wf S  ->
              terminating.t (V ty' (S :: d)) body1 body2
         ]
    ]
  | type.exist ty' =>
    [/\ expr.wf 0 e1
     , expr.wf 0 e2
     & exists v1 v2,
         [/\ value.t v1
          , value.t v2
          , e1 = expr.pack v1
          , e2 = expr.pack v2
          & exists (S : candidate.t),
              candidate.wf S /\
              (V ty' (S :: d)) v1 v2
         ]
    ]
    | type.bool => (e1 = expr.tt /\ e2 = expr.tt) \/ (e1 = expr.ff /\ e2 = expr.ff)
  end.

Notation E ty d :=
  (terminating.t (V ty d)).

Lemma V_value :
  forall ty d v1 v2,
    Forall candidate.wf d ->
    V ty d v1 v2 ->
    value.t v1 /\ value.t v2.
Proof.
  intros ty d v1 v2 WFd HV.
  destruct ty; cbn in HV.
  - break_match; try solve[intuition].
    assert (candidate.wf t) by (eapply Forall_nth_error; eauto).
    now firstorder.
  - destruct HV as [WF1 WF2 [body1 [body2 [E1 E2 H]]]].
    subst. split; constructor.
  - destruct HV as [WF1 WF2 [body1 [body2 [E1 E2 H]]]].
    subst. split; constructor.
  - destruct HV as [WF1 WF2 [v3 [v4 [Val3 Val4 E3 E4 [S [WFS V34]]]]]].
    subst. split; constructor; auto.
  - intuition; subst; constructor.
Qed.

Lemma V_wf :
  forall ty d v1 v2,
    Forall candidate.wf d ->
    V ty d v1 v2 ->
    expr.wf 0 v1 /\ expr.wf 0 v2.
Proof.
  intros ty d v1 v2 F.
  destruct ty; cbn [V]; try first [now intuition|now firstorder].
  - break_match; try solve[intuition].
    assert (candidate.wf t) by (eapply Forall_nth_error; eauto).
    firstorder.
  - intuition; subst; simpl; auto.
Qed.

Lemma V_list_closed :
  forall G d vs1 vs2,
    Forall candidate.wf d ->
    Forall3 (fun ty v => V ty d v) G vs1 vs2 ->
    Forall (expr.wf 0) vs1 /\ Forall (expr.wf 0) vs2.
Proof.
  intros G d vs1 vs2 WFd WFg.
  split; apply Forall_from_nth.
  - intros n e1 NEe1.
    destruct (Forall3_nth_error2 _ WFg NEe1) as [ty [e2 [NEty [NEe2 Ve]]]].
    apply V_wf in Ve; firstorder.
  - intros n e2 NEe2.
    destruct (Forall3_nth_error3 _ WFg NEe2) as [ty [e1 [NEty [NEe1 Ve]]]].
    apply V_wf in Ve; firstorder.
Qed.

Lemma V_E :
  forall ty d v1 v2,
    Forall candidate.wf d ->
    V ty d v1 v2 ->
    E ty d v1 v2.
Proof.
  intros ty d v1 v2 F V12.
  exists v1, v2.
  split; auto.
  all: apply V_value in V12; firstorder.
Qed.

Lemma E_step1 :
  forall ty d e1 e1' e2,
    step.t e1 e1' ->
    E ty d e1' e2 ->
    E ty d e1 e2.
Proof.
  intros ty d e1 e1' e2 S HE.
  revert ty e2 HE.
  induction S; intros ty0 e0 [v1 [v2 [Star1 Star2 Val1 Val2 V12]]]; exists v1, v2; split; auto.
  all: eapply step.step_l; eauto.
Qed.

Lemma E_step2 :
  forall ty d e1 e2 e2',
    step.t e2 e2' ->
    E ty d e1 e2' ->
    E ty d e1 e2.
Proof.
  intros ty d e1 e1' e2 S HE.
  revert ty e1 HE.
  induction S; intros ty0 e0 [v1 [v2 [Star1 Star2 Val1 Val2 V12]]]; exists v1, v2; split; auto.
  all: eapply step.step_l; eauto.
Qed.

Lemma E_step :
  forall ty d e1 e1' e2 e2',
    step.t e1 e1' ->
    step.t e2 e2' ->
    E ty d e1' e2' ->
    E ty d e1 e2.
Proof.
  intros ty d e1 e1' e2 e2' S1 S2 HE.
  eapply E_step1; [|eapply E_step2]; eauto.
Qed.

Lemma E_star1 :
  forall ty d e1 e1' e2,
    step.star e1 e1' ->
    E ty d e1' e2 ->
    E ty d e1 e2.
Proof.
  intros ty d e1 e1' e2 Star E12.
  revert ty e2 E12.
  now induction Star; eauto using E_step1.
Qed.

Lemma E_star2 :
  forall ty d e1 e2 e2',
    step.star e2 e2' ->
    E ty d e1 e2' ->
    E ty d e1 e2.
Proof.
  intros ty d e1 e2 e2' Star E12.
  revert ty e1 E12.
  now induction Star; eauto using E_step2.
Qed.

Lemma E_star :
  forall ty d e1 e1' e2 e2',
    step.star e1 e1' ->
    step.star e2 e2' ->
    E ty d e1' e2' ->
    E ty d e1 e2.
Proof.
  intros ty d e1 e1' e2 e2' Star1 Star2 E12.
  eapply E_star1; [|eapply E_star2]; eauto.
Qed.

Lemma V_shift :
  forall ty d1 d2 d3 v1 v2 ,
    Forall candidate.wf (d1 ++ d3) ->
    V ty (d1 ++ d3) v1 v2 <->
    V (type.shift (length d1) (length d2) ty) (d1 ++ d2 ++ d3) v1 v2.
Proof.
  induction ty as [alpha| | | |]; intros d1 d2 d3 v1 v2 F; simpl.
  - destruct (Nat.ltb_spec alpha (length d1)).
    + rewrite !nth_error_app1 by assumption. intuition.
    + rewrite !nth_error_app2 by lia.
      do_app2_minus.
      now auto.
  - split; intros [WFv1 Wfv2 [body1 [body2 [Ev1 Ev2 Vbody]]]]; (split; [assumption| assumption|]);
      subst v1 v2; do 2 eexists; (split; [reflexivity|reflexivity|]);
        intros v1 v2 V12.
    + rewrite <- IHty1 in V12 by assumption.
      apply Vbody in V12.
      eapply terminating.impl; [|eassumption].
      intros e1 e2; rewrite IHty2; eauto.
    + rewrite (IHty1 d1 d2 d3) in V12 by assumption.
      apply Vbody in V12.
      eapply terminating.impl; [|eassumption].
      intros e1 e2; rewrite IHty2; eauto.
  - split; intros [WFv1 Wfv2 [body1 [body2 [Ev1 Ev2 Vbody]]]]; (split; [assumption| assumption|]);
      subst v1 v2; do 2 eexists; (split; [reflexivity|reflexivity|]);
        intros S SWF.
    + destruct (Vbody _ SWF) as [v1 [v2 [Star1 Star2 Val1 Val2 V12]]].
      exists v1, v2. split; auto.
      apply IHty with (d1 := S :: d1); auto.
      simpl. constructor; auto.
    + destruct (Vbody _ SWF) as [v1 [v2 [Star1 Star2 Val1 Val2 V12]]].
      exists v1, v2. split; auto.
      specialize (IHty (S :: d1) d2 d3 v1 v2).
      apply IHty; auto.
      simpl. constructor; auto.
  - split; intros [WFv1 Wfv2 [body1 [body2 [Val1 Val2 Ev1 Ev2 [S [SWF HV]]]]]];
      (split; [assumption| assumption|]);
      subst v1 v2; exists body1, body2; (split; [assumption| assumption| reflexivity| reflexivity|]);
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
  forall ty S d v1 v2,
    Forall candidate.wf d ->
    V ty d v1 v2 <-> V (type.shift 0 1 ty) (S :: d) v1 v2.
Proof.
  intros.
  apply V_shift with (d1 := []) (d2 := [S]) (d3 := d); auto.
Qed.

Lemma V_map_shift' :
  forall S d G g1 g2,
    Forall candidate.wf d ->
    Forall3 (fun ty e => V ty d e) G g1 g2 ->
    Forall3 (fun ty e => V ty (S :: d) e) (map (type.shift 0 1) G) g1 g2.
Proof.
  intros S d G g1 g2 WFd WFg.
  apply Forall3_map1.
  eapply Forall3_impl; [|now eauto].
  simpl.
  intros ty' e' V'.
  now apply V_shift'; auto.
Qed.

Lemma V_candidate :
  forall ty d,
    Forall candidate.wf d ->
    candidate.wf (V ty d).
Proof.
  intros ty d F e1 e2 H12.
  split.
  - apply V_value in H12; intuition.
  - apply V_wf in H12; intuition.
  - apply V_value in H12; intuition.
  - apply V_wf in H12; intuition.
Qed.

Lemma V_map_identity :
  forall d2 d1,
    Forall2 (fun P Q => forall e1 e2, P e1 e2 <-> Q e1 e2)
            (map (fun ty0 => V ty0 (d1 ++ d2))
                 (map (type.shift 0 (length d1)) (type.identity_subst (length d2))))
            d2.
Proof.
  induction d2; intros d1; simpl; constructor.
  - intros e1 e2.
    rewrite nth_error_app2 by lia.
    rewrite Nat.sub_diag.
    replace (length d1 + 0 - length d1)
       with 0 by lia.
    reflexivity.
  - rewrite map_map with (g := type.shift _ _).
    rewrite map_ext
       with (f := (fun x => type.shift 0 (length d1) (type.shift 0 1 x)))
            (g := (fun x => type.shift 0 (S (length d1)) x))
         by (intros; rewrite type.shift_merge'; f_equal; lia).
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
    Forall2 (fun P Q => forall e1 e2, P e1 e2 <-> Q e1 e2)
            (map (fun ty0 => V ty0 d) (type.identity_subst (length d)))
            d.
Proof.
  intros.
  pose proof V_map_identity d [].
  simpl in H.
  rewrite map_ext with (f := type.shift _ _) (g := fun x => x) in H by auto using type.shift_nop_d.
  now rewrite map_id in H.
Qed.


Lemma V_ext :
  forall ty d1 d2,
    Forall2 (fun P Q => forall e1 e2, P e1 e2 <-> Q e1 e2) d1 d2 ->
    forall e1 e2,
      V ty d1 e1 e2 <-> V ty d2 e1 e2.
Proof.
  induction ty; simpl; intros d1 d2 F e1 e2.
  - break_match.
    + destruct (Forall2_nth_error1 F Heqo) as [t' [NE' H]].
      unfold candidate.t.
      now rewrite NE'.
    + pose proof Forall2_length F as Hlen.
      pose proof nth_error_None d1 alpha.
      pose proof nth_error_None d2 alpha.
      assert (nth_error d2 alpha = None) as Hd2 by (rewrite Hlen in *; intuition).
      unfold candidate.t. rewrite Hd2.
      intuition.
  - specialize (IHty1 d1 d2 F).
    specialize (IHty2 d1 d2 F).
    split; intros [WF1 WF2 [body1 [body2 [E1 E2 Hbody]]]];
      (split; [assumption| assumption|]);
      subst; exists body1, body2;
        (split; [reflexivity|reflexivity|]);
        intros v1 v2 V12.
    + rewrite <- terminating.iff.
      apply Hbody.
      firstorder.
      assumption.
    + rewrite terminating.iff.
      apply Hbody.
      firstorder.
      assumption.
  - split; intros [WF1 WF2 [body1 [body2 [E1 E2 Hbody]]]];
      (split; [assumption| assumption|]);
      subst; exists body1, body2;
        (split; [reflexivity| reflexivity|]);
        intros S SWF;
        specialize (IHty (S :: d1) (S :: d2)).
    + rewrite <- terminating.iff.
      apply Hbody.
      apply SWF.
      apply IHty.
      constructor; intuition.
    + rewrite terminating.iff.
      apply Hbody.
      apply SWF.
      apply IHty.
      constructor; intuition.
  - split; intros [WF1 WF2 [v1 [v2 [Val1 Val2 E1 E2 [S [SWF V12]]]]]];
      split; auto; subst e1 e2; exists v1, v2; split; auto;
        exists S; (split; [assumption|]).
    + rewrite <- IHty.
      apply V12.
      constructor; auto.
      intuition.
    + rewrite IHty.
      apply V12.
      constructor; auto.
      intuition.
  - firstorder.
Qed.

Lemma V_Forall_equiv_shift' :
  forall d D S,
    Forall candidate.wf d ->
    Forall2 (fun P Q => forall e1 e2, P e1 e2 <-> Q e1 e2)
            (map (fun ty => V ty d) D)
            (map (fun ty => V (type.shift 0 1 ty) (S :: d)) D).
Proof.
  intros d D S F.
  apply Forall2_map.
  apply Forall2_from_forall; auto.
  intros x y z NEy NEz e1 e2.
  unfold type_basis.t in *.
  assert (y = z) by congruence.
  subst.
  apply V_shift'; auto.
Qed.

Lemma V_descend :
  forall ty S d D v1 v2,
    Forall candidate.wf d ->
    V ty (S :: map (fun ty0 => V ty0 d) D) v1 v2 <->
    V ty (map (fun ty0 => V ty0 (S :: d)) (type.descend 1 D)) v1 v2.
Proof.
  intros ty S d D v1 v2 F.
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
    (forall e1 e2, V (type.subst D ty) d e1 e2 <-> V ty (map (fun ty0 => V ty0 d) D) e1 e2).
Proof.
  induction ty; simpl; intros D d WFty F WFd e1 e2.
  - rewrite nth_error_map.
    break_match; intuition.
    pose proof nth_error_None D alpha.
    firstorder. lia.
  - unfold terminating.t.
    destruct WFty as [WFty1 WFty2].
    split; intros [WF1 WF2 [body1 [body2 [E1 E2 H12]]]];
      (split; [assumption|assumption|]);
      exists body1, body2; (split; [assumption|assumption|]);
        intros v3 v4 V34; specialize (H12 v3 v4).
    + rewrite IHty1 in H12; auto.
      specialize (H12 V34).
      destruct H12 as [v5 [v6 [Star5 Star6 Val5 Val6 V56]]].
      exists v5, v6.
      rewrite IHty2 in V56; auto.
    + rewrite <- IHty1 in H12; auto.
      specialize (H12 V34).
      destruct H12 as [v5 [v6 [Star5 Star6 Val5 Val6 V56]]].
      exists v5, v6.
      rewrite <- IHty2 in V56; auto.
  - unfold terminating.t.
    rewrite <- type.descend_1 in *.
    split; intros [WF1 WF2 [body1 [body2 [E1 E2 Ebody]]]];
      (split;[assumption|assumption|]);
      subst; exists body1, body2; (split; [reflexivity|reflexivity|]);
        intros S SWF; specialize (Ebody S SWF);
          destruct Ebody as [v1 [v2 [Star1 Star2 Val1 Val2 V12]]];
          exists v1, v2; split; auto.
    + rewrite IHty in V12.
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
    split; intros [WF1 WF2 [v1 [v2 [Val1 Val2 E1 E2 [S [SWF V12]]]]]];
      split; auto; subst e1 e2; exists v1, v2; (split; auto);
        exists S; (split; [assumption|]).
    + rewrite IHty in V12.
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
    (forall e1 e2, E (type.subst D ty) d e1 e2 <-> E ty (map (fun ty0 => V ty0 d) D) e1 e2).
Proof.
  intros ty D d TWF F SWF.
  apply terminating.iff.
  apply V_subst; auto.
Qed.

Module has_sem_type.
  Definition t n G e1 e2 ty :=
    [/\ expr.wf (length G) e1
     , expr.wf (length G) e2
     , type.wf n ty
     , Forall (type.wf n) G
     & forall d g1 g2,
         length d = n ->
         Forall candidate.wf d ->
         Forall3 (fun ty e => V ty d e) G g1 g2 ->
         E ty d (expr.subst g1 e1) (expr.subst g2 e2)
    ].

  Lemma var :
    forall n G x ty,
      Forall (type.wf n) G ->
      type.wf n ty ->
      nth_error G x = Some ty ->
      t n G (expr.var x) (expr.var x) ty.
  Proof.
    intros n G x ty F WFty NE.
    do_nth_error_Some.
    split; auto.
    - simpl. apply H. congruence.
    - simpl. apply H. congruence.
    - intros d g1 g2 ? WFd WFg.
      simpl. apply V_E; auto.
      destruct (Forall3_nth_error1 _ WFg NE) as [v1 [v2 [NE1 [NE2 V12]]]].
      unfold expr.t in *.
      now rewrite NE1, NE2.
  Qed.

  Lemma abs :
    forall n G e1 e2 ty1 ty2,
      t n (ty1 :: G) e1 e2 ty2 ->
      t n G (expr.abs e1) (expr.abs e2) (type.arrow ty1 ty2).
  Proof.
    intros n G e1 e2 ty1 ty2 [WFe1 WFe2 WFty WFG HT].
    invc WFG.
    split; [now auto| now auto | now auto| now simpl; auto|].
    intros d g1 g2 En WFd WFg.
    apply V_E; auto.
    cbn [expr.subst V].
    rewrite <- !expr.descend_1.
    pose proof (Forall3_length WFg) as [EG1 EG2].
    split.
    + apply expr.wf_subst.
      * now rewrite expr.descend_length, <- EG1.
      * apply expr.descend_wf with (s := 1).
        apply V_list_closed in WFg; firstorder.
    + apply expr.wf_subst.
      * now rewrite expr.descend_length, <- EG2.
      * apply expr.descend_wf with (s := 1).
        apply V_list_closed in WFg; firstorder.
    + exists (expr.subst (expr.descend 1 g1) e1), (expr.subst (expr.descend 1 g2) e2).
      split; [now rewrite !expr.descend_1| now rewrite expr.descend_1|].
      intros v1 v2 V12.
      cbn [length] in *.
      rewrite !expr.subst_cons.
      * auto.
      * now rewrite <- EG2 in *.
      * now apply V_list_closed in WFg; firstorder.
      * now rewrite <- EG1 in *.
      * now apply V_list_closed in WFg; firstorder.
  Qed.

  Lemma app :
    forall n G e11 e12 e21 e22 ty1 ty2,
      t n G e11 e21 (type.arrow ty1 ty2) ->
      t n G e12 e22 ty1 ->
      t n G (expr.app e11 e12) (expr.app e21 e22) ty2.
  Proof.
    intros n G e11 e12 e21 e22 ty1 ty2.
    intros [WFe11 WFe21 [WFty1 WFty2] WFG HT1].
    intros [WFe12 WFe22 _ _ HT2].

    split; [ now cbn; auto | now cbn; auto | now auto | now auto|].
    intros d g1 g2 En WFd WFg.

    cbn [expr.subst].
    specialize (HT1 d g1 g2 En WFd WFg).
    specialize (HT2 d g1 g2 En WFd WFg).
    destruct HT1 as [v11 [v21 [Star11 Star21 Val11 Val21 V1]]].
    destruct HT2 as [v12 [v22 [Star12 Star22 Val12 Val22 V2]]].
    destruct V1 as [WFv11 WFv21 [body1 [body2 [E11 E12 Hbody]]]].
    subst v11 v21.
    eapply E_star; [| |now eauto].

    eapply step.star_trans.
    eapply step.star_app1. now eauto.
    eapply step.star_trans.
    now eapply step.star_app2; eauto.
    eauto using step.step_l, step.beta.

    eapply step.star_trans.
    eapply step.star_app1. now eauto.
    eapply step.star_trans.
    now eapply step.star_app2; eauto.
    eauto using step.step_l, step.beta.
  Qed.

  Lemma tyabs :
    forall n G e1 e2 ty,
      t (S n) (map (type.shift 0 1) G) e1 e2 ty ->
      t n G (expr.tyabs e1) (expr.tyabs e2) (type.all ty).
  Proof.
    intros n G e1 e2 ty [WFe1 WFe2 WFty WFmG HT].
    rewrite map_length in *.
    split; [assumption|assumption|assumption|now auto using type.wf_map_shift_inv'|].
    intros d g1 g2 En WFd WFg.
    apply V_E; [assumption|].
    cbn [expr.subst V].
    pose proof (Forall3_length WFg) as [EG1 EG2].
    split.
    + apply expr.wf_subst.
      * now rewrite <- EG1.
      * apply V_list_closed in WFg; firstorder.
    + apply expr.wf_subst.
      * now rewrite <- EG2.
      * apply V_list_closed in WFg; firstorder.
    + do 2 eexists. split; [reflexivity|reflexivity|].
      intros S SWF.
      apply HT.
      * simpl. congruence.
      * auto.
      * auto using V_map_shift'.
  Qed.

  Lemma tyapp :
    forall n G e1 e2 ty_body ty,
      type.wf n ty ->
      t n G e1 e2 (type.all ty_body) ->
      t n G (expr.tyapp e1) (expr.tyapp e2) (type.subst (ty :: type.identity_subst n) ty_body).
  Proof.
    intros n G e1 e2 ty_body ty WFty [WFe1 WFe2 WFtyall WFG HT].
    split; [assumption| assumption| now auto using type.wf_subst_id | now auto |].

    intros d g1 g2 En WFd WFg. subst n.
    specialize (HT d g1 g2 eq_refl WFd WFg).
    destruct HT as [v1 [v2 [Star1 Star2 Val1 Val2 V12]]].
    destruct V12 as [WFv1 WFv2 [body1 [body2 [E1 E2 Hbody]]]].
    cbn [expr.subst].
    subst v1 v2.
    eapply E_star.

    eapply step.star_trans.
    eapply step.star_tyapp. now eauto.
    eapply step.step_l.
    apply step.tybeta.
    now constructor.

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
      eapply terminating.iff; [| apply Hbody with (S := V ty d); auto using V_candidate].
      intros e'.
      apply V_ext.
      constructor; [now intuition|].
      apply V_map_identity'.
  Qed.

  Lemma pack :
    forall n G e1 e2 ty_interface ty_rep,
      type.wf n ty_rep ->
      t n G e1 e2 (type.subst (ty_rep :: type.identity_subst n) ty_interface) ->
      t n G (expr.pack e1) (expr.pack e2) (type.exist ty_interface).
  Proof.
    intros n G e1 e2 ty_interface ty_rep WFrep [WFe1 WFe2 WFtysubst WFG HT].

    split; [ now auto | now auto | now simpl; eauto using type.wf_subst_id_inv | now auto | ].

    intros d g1 g2 En WFd WFg. subst n.

    specialize (HT d g1 g2 eq_refl WFd WFg).
    destruct HT as [v1 [v2 [Star1 Star2 Val1 Val2 V12]]].
    rewrite V_subst in V12; auto using type.wf_identity_subst.
    + cbn [expr.subst].
      eapply E_star.
      apply step.star_pack. eassumption.
      apply step.star_pack. eassumption.
      apply V_E; auto.
      rewrite V_ext with (d2 := V ty_rep d :: d) in V12
        by (simpl; constructor; intuition; apply V_map_identity').
      cbn [V].
      split.
      * simpl. apply V_wf in V12; intuition auto using V_candidate.
      * simpl. apply V_wf in V12; intuition auto using V_candidate.
      * exists v1, v2. split; auto.
        eauto 10 using V_candidate.
    + simpl. rewrite type.identity_subst_length.
      eauto using type.wf_subst_id_inv.
  Qed.

  Lemma unpack :
    forall n G e11 e12 e21 e22 ty1 ty2,
      t n G e11 e12 (type.exist ty1) ->
      t (S n) (ty1 :: map (type.shift 0 1) G) e21 e22 (type.shift 0 1 ty2) ->
      t n G (expr.unpack e11 e21) (expr.unpack e12 e22) ty2.
  Proof.
    intros n G e11 e12 e21 e22 ty1 ty2 [WFe11 WFe12 WFexty1 WFG HT1] [WFe21 WFe22 WFty2 _ HT2].
    split; [ now simpl in *; rewrite map_length in *; auto
           | now simpl in *; rewrite map_length in *; auto
           | now auto using type.wf_shift_inv' | now auto | ].
    intros d g1 g2 En WFd WFg. subst n.
    cbn[length] in WFe21, WFe22. rewrite map_length in WFe21, WFe22.

    specialize (HT1 d g1 g2 eq_refl WFd WFg).
    destruct HT1 as [v11 [v12 [Star11 Star12 Val11 Val12 V1]]].
    cbn [V] in V1.
    destruct V1 as [WFv1 WFv2 [v11' [v12' [Val11' Val12' E11 E12 [S [SWF V'1]]]]]].
    subst v11 v12.
    cbn [expr.subst].
    eapply E_star.
    eapply step.star_trans.
    apply step.star_unpack. eassumption.
    eapply step.step_l.
    apply step.packbeta. assumption.
    constructor.

    eapply step.star_trans.
    apply step.star_unpack. eassumption.
    eapply step.step_l.
    apply step.packbeta. assumption.
    constructor.

    destruct (Forall3_length WFg) as [Eg1 Eg2].
    rewrite <- !expr.descend_1.
    rewrite !expr.subst_cons.
    - set (G' := ty1 :: map (type.shift 0 1) G) in *.
      specialize (HT2 (S :: d) (v11' :: g1) (v12' :: g2) eq_refl ltac:(auto)
                      ltac:(subst G'; auto using V_map_shift')).
      destruct HT2 as [v21 [v22 [Star21 Star22 Val21 Val22 V2]]].
      eapply E_star. eauto. eauto.
      rewrite <- V_shift' in V2 by auto.
      apply V_E; auto.
    - unfold type.t in *.
      now rewrite Eg2 in *.
    - apply V_list_closed in WFg; intuition.
    - unfold type.t in *.
      now rewrite Eg1 in *.
    - apply V_list_closed in WFg; intuition.
  Qed.

  Lemma tt :
    forall n G,
      Forall (type.wf n) G ->
      t n G expr.tt expr.tt type.bool.
  Proof.
    intros n G F.
    split; [ now simpl; auto | now simpl; auto |now simpl; auto | assumption |].
    intros d g1 g2 En WFd WFg.
    apply V_E; [assumption|].
    cbn.
    intuition.
  Qed.

  Lemma ff :
    forall n G,
      Forall (type.wf n) G ->
      t n G expr.ff expr.ff type.bool.
  Proof.
    intros n G F.
    split; [ now simpl; auto | now simpl; auto |now simpl; auto | assumption |].
    intros d g1 g2 En WFd WFg.
    apply V_E; [assumption|].
    cbn.
    intuition.
  Qed.

  Lemma If :
    forall G n e11 e12 e21 e22 e31 e32 ty,
      t n G e11 e12 type.bool ->
      t n G e21 e22 ty ->
      t n G e31 e32 ty ->
      t n G (expr.If e11 e21 e31) (expr.If e12 e22 e32) ty.
  Proof.
    intros G n e11 e12 e21 e22 e31 e32 ty.
    intros [WFe11 WFe12 _ WFG HT1].
    intros [WFe21 WFe22 WFty _ HT2].
    intros [WFe31 WFe32 _ _ HT3].
    split; [ now simpl; auto| now simpl; auto | assumption | assumption | ].
    intros d g1 g2 En WFd WFg.

    cbn [expr.subst].
    specialize (HT1 d g1 g2 En WFd WFg).
    destruct HT1 as [v1 [v2 [Star1 Star2 Val1 Val2 V12]]].
    eapply E_star; [apply step.star_If|apply step.star_If |]; eauto.
    destruct V12 as [[??]|[??]]; subst;
      (eapply E_step; [constructor| |]); auto.
  Qed.
End has_sem_type.

Theorem fundamental :
  forall n G e ty,
    Forall (type.wf n) G ->
    has_type.t n G e ty ->
    has_sem_type.t n G e e ty.
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
    E ty [] e e.
Proof.
  intros e ty HT.
  replace e with (expr.subst (expr.identity_subst 0) e)
    by now rewrite expr.subst_identity.
  eapply fundamental; try apply HT; try constructor.
Qed.

Corollary termination :
  forall e ty,
    has_type.t 0 [] e ty ->
    exists v, value.t v /\ step.star e v.
Proof.
  intros e ty HT.
  destruct (fundamental_closed HT) as [v [Star [Val _]]].
  eauto.
Qed.

Corollary there_are_two_bools_and_they_don't_change_their_mind :
  forall e u1 u2 v1 v2 tyu tyv, 
    has_type.t 0 [] e (type.all (type.arrow (type.var 0)
                                            (type.arrow (type.var 0) (type.var 0)))) ->

    has_type.t 0 [] u1 tyu -> 
    has_type.t 0 [] u2 tyu ->
    has_type.t 0 [] v1 tyv -> 
    has_type.t 0 [] v2 tyv ->

    value.t u1 ->
    value.t u2 ->
    value.t v1 ->
    value.t v2 ->
    [\/ [/\ step.star (expr.app (expr.app (expr.tyapp e) u1) u2) u1 
        & step.star (expr.app (expr.app (expr.tyapp e) v1) v2) v1]
    |  [/\ step.star (expr.app (expr.app (expr.tyapp e) u1) u2) u2 
        & step.star (expr.app (expr.app (expr.tyapp e) v1) v2) v2]].
Proof.
  intros e u1 u2 v1 v2 tyu tyv HTe HTu1 HTu2 HTv1 HTv2 Vu1 Vu2 Vv1 Vv2.
  apply fundamental_closed in HTe.
  destruct HTe as (w1 & w2 & [StarW1 StarW2 Vw1 Vw2 Vw1w2]).
  assert (w1 = w2)
    by eauto using step.star_det.
  subst w2.
  cbn [V] in Vw1w2.
  destruct Vw1w2 as [WFw1 _ (body1 & body2 & [Eb1 Eb2 HS])].
  assert (body1 = body2) by congruence. subst body2 w1.
  set (S := fun x y => (x = u1 /\ y = v1) \/ (x = u2 /\ y = v2)).
  assert (candidate.wf S) as SWF.
  { unfold candidate.wf. subst S. simpl. intros.
    split; intuition; subst; auto.
    - now apply has_type.t_expr_wf in HTu1.
    - now apply has_type.t_expr_wf in HTu2.
    - now apply has_type.t_expr_wf in HTv1.
    - now apply has_type.t_expr_wf in HTv2.
  }
  specialize (HS S SWF).
  destruct HS as (z1 & z2 & [StarZ1 StarZ2 Vz1 Vz2 [WfZ1 WfZ2 (zbody1 & zbody2 & [Ez1 Ez2 Hz])]]).
  assert (z1 = z2) by (eauto using step.star_det). subst z2.
  assert (zbody1 = zbody2) by congruence. subst zbody2 z1.
  specialize (Hz u1 v1).
  assert (S u1 v1) as HSu1v1.
  {
    subst S. simpl. intuition.
  }

  specialize (Hz HSu1v1).
  destruct Hz as (a1 & a2 & [StarA1 StarA2 Va1 Va2 [WFa1 WFa2 (abody1 & abody2 & [EA1 EA2 Ha])]]).
  subst a1 a2.
  specialize (Ha u2 v2).
  assert (S u2 v2) as HSu2v2.
  {
    subst S. simpl. intuition.
  }
  specialize (Ha HSu2v2).
  destruct Ha as (b1 & b2 & [StarB1 StarB2 Vb1 Vb2 Vb1b2]).
  assert (step.star (expr.app (expr.app (expr.tyapp e) u1) u2) b1).
  {
    eapply step.star_trans.
    eapply step.star_app1.
    eapply step.star_app1.
    eapply step.star_tyapp.
    eassumption.
  
    eapply step.star_trans.
    eapply step.star_app1.
    eapply step.star_app1.
    eapply step.step_l.
    eapply step.tybeta.
    eassumption.

    eapply step.star_trans.
    eapply step.star_app1.
    eapply step.step_l.
    eapply step.beta.
    assumption.
    eassumption.

    eapply step.star_trans.
    eapply step.step_l.
    eapply step.beta.
    assumption.
    eassumption.
    constructor.
  } 
  assert (step.star (expr.app (expr.app (expr.tyapp e) v1) v2) b2).
  {
    eapply step.star_trans.
    eapply step.star_app1.
    eapply step.star_app1.
    eapply step.star_tyapp.
    eassumption.
  
    eapply step.star_trans.
    eapply step.star_app1.
    eapply step.star_app1.
    eapply step.step_l.
    eapply step.tybeta.
    eassumption.

    eapply step.star_trans.
    eapply step.star_app1.
    eapply step.step_l.
    eapply step.beta.
    assumption.
    eassumption.

    eapply step.star_trans.
    eapply step.step_l.
    eapply step.beta.
    assumption.
    eassumption.
    constructor.
  }
  destruct Vb1b2; [left|right]; intuition; subst; assumption.
Qed.

Corollary there_are_two_bools :
  forall e,
    has_type.t 0 [] e (type.all (type.arrow (type.var 0)
                                            (type.arrow (type.var 0) (type.var 0)))) ->
    [\/ forall v1 v2 ty,
        has_type.t 0 [] v1 ty ->
        has_type.t 0 [] v2 ty ->
        value.t v1 ->
        value.t v2 ->
        step.star (expr.app (expr.app (expr.tyapp e) v1) v2) v1
    | forall v1 v2 ty,
        has_type.t 0 [] v1 ty ->
        has_type.t 0 [] v2 ty ->
        value.t v1 ->
        value.t v2 ->
        step.star (expr.app (expr.app (expr.tyapp e) v1) v2) v2
    ].
Proof.
  intros e HTe.
  specialize (@there_are_two_bools_and_they_don't_change_their_mind 
                e expr.tt expr.ff expr.tt expr.ff type.bool type.bool) as T.
  specialize (T HTe ltac:(constructor) ltac:(constructor) ltac:(constructor) ltac:(constructor)
                    ltac:(constructor) ltac:(constructor) ltac:(constructor) ltac:(constructor)).
  destruct T as [[? ?]|[? ?]]; [left|right]; intros v1 v2 ty HTv1 HTv2 Vv1 Vv2.
  - specialize (@there_are_two_bools_and_they_don't_change_their_mind e expr.tt expr.ff v1 v2 type.bool ty) as T.
    specialize (T HTe ltac:(constructor) ltac:(constructor) ltac:(assumption) ltac:(assumption)
                      ltac:(constructor) ltac:(constructor) ltac:(assumption) ltac:(assumption)).
    intuition.
    exfalso.
    assert (expr.tt = expr.ff).
    eapply step.star_det; eauto.
    discriminate.
  - specialize (@there_are_two_bools_and_they_don't_change_their_mind e expr.tt expr.ff v1 v2 type.bool ty) as T.
    specialize (T HTe ltac:(constructor) ltac:(constructor) ltac:(assumption) ltac:(assumption)
                      ltac:(constructor) ltac:(constructor) ltac:(assumption) ltac:(assumption)).
    intuition.
    exfalso.
    assert (expr.tt = expr.ff).
    eapply step.star_det; eauto.
    discriminate.
Qed.
