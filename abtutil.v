From mm Require Import util abt.
Set Implicit Arguments.

Module Type SYNTAX_BASIS.
  Declare Module A : ABT.

  Parameter t : Type.

  Parameter var : nat -> t.

  Parameter to_abt : t -> A.t.
  Parameter of_abt : A.t -> t.

  Parameter var_to_abt : forall n, to_abt (var n) = A.var n.

  Parameter ws_to_abt : forall e, A.ws (to_abt e).
  Parameter of_to_abt : forall e, of_abt (to_abt e) = e.
  Parameter to_of_abt : forall a, A.ws a -> to_abt (of_abt a) = a.

  Parameter shift : nat -> nat -> t -> t.
  Parameter shift_to_abt_comm : forall e c d, to_abt (shift c d e) = A.shift c d (to_abt e).

  Parameter subst : list t -> t -> t.
  Parameter subst_to_abt_comm : forall e rho,
      to_abt (subst rho e) = A.subst (map to_abt rho) (to_abt e).
  Parameter map_shift_to_abt_comm : forall c d rho,
      map to_abt (map (shift c d) rho) = map (A.shift c d) (map to_abt rho).

  Parameter wf : nat -> t -> Prop.
  Parameter wf_to_abt : forall e n, wf n e <-> A.wf n (to_abt e).

  Parameter identity_subst : nat -> list t.
  Parameter identity_subst_to_abt_comm : forall n, map to_abt (identity_subst n) = A.identity_subst n.
End SYNTAX_BASIS.

Module abt_util (SB : SYNTAX_BASIS).
  Include SB.

  Definition descend n rho :=
    identity_subst n ++ map (shift 0 n) rho.

  Lemma descend_to_abt_comm :
    forall n rho,
      map to_abt (descend n rho) = A.descend n (map to_abt rho).
  Proof.
    unfold descend.
    intros n rho.
    now rewrite map_app, identity_subst_to_abt_comm, map_shift_to_abt_comm.
  Qed.

  Lemma wf_of_abt :
    forall a n,
      A.ws a ->
      wf n (of_abt a) <-> A.wf n a.
  Proof.
    intros.
    pose proof wf_to_abt (of_abt a) n.
    rewrite to_of_abt in *; auto.
  Qed.

  Lemma wf_shift : forall e c d n, wf n e -> wf (d + n) (shift c d e).
  Proof.
    intros.
    rewrite wf_to_abt in *.
    rewrite shift_to_abt_comm.
    now apply A.wf_shift.
  Qed.

  Lemma wf_shift' : forall e n, wf n e -> wf (S n) (shift 0 1 e).
  Proof.
    intros e n WF.
    now apply wf_shift with (c := 0) (d := 1).
  Qed.

  Lemma wf_map_shift' :
    forall n G,
      Forall (wf n) G ->
      Forall (wf (S n)) (map (shift 0 1) G).
  Proof.
    intros n G F.
    rewrite Forall_map.
    eapply Forall_impl; [|eassumption].
    intros ty WF.
    now apply wf_shift'.
  Qed.

  Lemma map_subst_to_abt_comm :
    forall rho1 rho2,
      map to_abt (map (subst rho2) rho1) =
      map (A.subst (map to_abt rho2)) (map to_abt rho1).
  Proof.
    intros rho1 rho2.
    rewrite !map_map.
    apply map_ext.
    intros e'.
    auto using subst_to_abt_comm.
  Qed.

  Lemma wf_subst : forall e n rho, wf (length rho) e -> Forall (wf n) rho -> wf n (subst rho e).
  Proof.
    intros e n rho WF F.
    rewrite wf_to_abt in *.
    rewrite subst_to_abt_comm.
    apply A.wf_subst.
    - now rewrite map_length.
    - rewrite Forall_map.
      eapply Forall_impl; try eassumption.
      intros e' WF'.
      now rewrite <- wf_to_abt.
  Qed.

  Lemma identity_subst_length : forall n, length (identity_subst n) = n.
  Proof.
    intros.
    pose proof A.identity_subst_length n.
    rewrite <- identity_subst_to_abt_comm in *.
    now rewrite map_length in *.
  Qed.

  Lemma wf_identity_subst: forall n : nat, Forall (wf n) (identity_subst n).
  Proof.
    intros.
    pose proof A.wf_identity_subst n.
    rewrite <- identity_subst_to_abt_comm in *.
    rewrite Forall_map in *.
    eapply Forall_impl; [|eassumption].
    intros e. simpl.
    now rewrite wf_to_abt.
  Qed.

  Lemma wf_subst_id :
    forall n e1 e2,
      wf n e1 ->
      wf (S n) e2 ->
      wf n (subst (e1 :: identity_subst n) e2).
  Proof.
    intros n e1 e2 WF1 WF2.
    apply wf_subst.
    - simpl. now rewrite identity_subst_length.
    - constructor; [now auto|].
      apply wf_identity_subst.
  Qed.

  Lemma wf_weaken : forall e n d, n <= d -> wf n e -> wf d e.
  Proof.
    intros e n d LE.
    rewrite !wf_to_abt.
    eauto using A.wf_weaken.
  Qed.

  Lemma to_abt_inj :
    forall e1 e2,
      to_abt e1 = to_abt e2 -> e1 = e2.
  Proof.
    intros e1 e2.
    rewrite <- of_to_abt with (e := e1).
    rewrite <- of_to_abt with (e := e2).
    rewrite !to_of_abt by auto using ws_to_abt.
    congruence.
  Qed.

  Lemma shift_merge : forall e c d1 d2 , shift c d2 (shift c d1 e) = shift c (d2 + d1) e.
  Proof.
    intros e c d1 d2.
    apply to_abt_inj.
    rewrite !shift_to_abt_comm.
    now rewrite A.shift_merge.
  Qed.

  Lemma shift_nop_d :
    forall e c,
      shift c 0 e = e.
  Proof.
    intros e c.
    apply to_abt_inj.
    rewrite shift_to_abt_comm.
    now rewrite A.shift_nop_d.
  Qed.

  Lemma subst_subst :
    forall e rho1 rho2,
      wf (List.length rho1) e ->
      List.Forall (wf (List.length rho2)) rho1 ->
      subst rho2 (subst rho1 e) =
      subst (List.map (subst rho2) rho1) e.
  Proof.
    intros e rho1 rho2 WF F.
    apply to_abt_inj.
    rewrite !subst_to_abt_comm.
    rewrite A.subst_subst.
    - now rewrite map_subst_to_abt_comm.
    - now rewrite map_length, <- wf_to_abt.
    - rewrite map_length, Forall_map.
        eapply Forall_impl; [|eassumption].
        intros e'.
        now rewrite wf_to_abt.
  Qed.

  Lemma subst_shift_singleton :
    forall e e',
      wf 0 e ->
      subst [e'] (shift 0 1 e) = e.
  Proof.
    intros.
    apply to_abt_inj.
    rewrite subst_to_abt_comm, shift_to_abt_comm.
    simpl.
    rewrite A.subst_shift_singleton; auto.
    now rewrite <- wf_to_abt.
  Qed.

  Lemma subst_identity :
    forall e n,
      subst (identity_subst n) e = e.
  Proof.
    intros e n.
    apply to_abt_inj.
    rewrite subst_to_abt_comm, identity_subst_to_abt_comm.
    now rewrite A.subst_identity.
  Qed.

  Lemma map_subst_identity_subst :
    forall rho,
      map (subst rho) (identity_subst (length rho))
      = rho.
  Proof.
    intros rho.
    apply map_inj with (f := to_abt).
    apply to_abt_inj.
    rewrite map_subst_to_abt_comm.
    rewrite SB.identity_subst_to_abt_comm.
    replace (length rho) with (length (map to_abt rho))
      by auto using map_length.
    apply A.map_subst_identity_subst.
  Qed.

  Lemma wf_subst_inv :
    forall e n rho,
      wf n (subst rho e) ->
      wf (max n (length rho)) e.
  Proof.
    intros e n rho.
    rewrite !wf_to_abt.
    rewrite subst_to_abt_comm.
    intros WF.
    apply A.wf_subst_inv in WF.
    now rewrite map_length in WF.
  Qed.

  Lemma wf_subst_id_inv :
    forall n e1 e2,
      wf n (subst (e1 :: identity_subst n) e2) ->
      wf (S n) e2.
  Proof.
    intros n e1 e2 WF.
    apply wf_subst_inv in WF.
    simpl in *.
    rewrite identity_subst_length in *.
    now rewrite Nat.max_r in * by lia.
  Qed.

  Lemma wf_shift_inv :
    forall e c d n,
      wf n (shift c d e) ->
      wf (max c (n - d)) e.
  Proof.
    intros e c d n.
    rewrite !wf_to_abt.
    rewrite shift_to_abt_comm.
    intros WF.
    now apply A.wf_shift_inv in WF.
  Qed.

  Lemma wf_shift_inv' :
    forall e n,
      wf (S n) (shift 0 1 e) ->
      wf n e.
  Proof.
    intros e n WF.
    apply wf_shift_inv with (c := 0) (d := 1) in WF.
    simpl in *.
    now rewrite Nat.sub_0_r in *.
  Qed.

  Lemma wf_map_shift_inv' :
    forall l n,
      Forall (wf (S n)) (map (shift 0 1) l) ->
      Forall (wf n) l.
  Proof.
    intros l n F.
    rewrite Forall_map in *.
    eapply Forall_impl; [|eassumption].
    auto using wf_shift_inv'.
  Qed.

  Lemma subst_cons :
    forall e v rho,
      wf (S (length rho)) e ->
      Forall (wf 0) rho ->
      subst [v] (subst (descend 1 rho) e) =
      subst (v :: rho) e.
  Proof.
    intros e v rho WF F.
    apply to_abt_inj.
    rewrite !subst_to_abt_comm, descend_to_abt_comm.
    simpl.
    rewrite A.subst_cons; auto.
    - now rewrite map_length, <- wf_to_abt.
    - rewrite Forall_map.
      eapply Forall_impl; [|eassumption].
      intros.
      now rewrite <- wf_to_abt.
  Qed.

  Lemma descend_length :
    forall n rho,
      length (descend n rho) = n + length rho.
  Proof.
    intros n rho.
    unfold descend.
    now rewrite app_length, map_length, identity_subst_length.
  Qed.

  Lemma Forall_wf_to_abt :
    forall n l,
      Forall (wf n) l <-> Forall (A.wf n) (map to_abt l).
  Proof.
    intros n l.
    rewrite Forall_map.
    split; refine (@Forall_impl _ _ _ _ _); firstorder using wf_to_abt.
  Qed.

  Lemma descend_wf :
    forall n s rho,
      Forall (wf n) rho ->
      Forall (wf (s + n)) (descend s rho).
  Proof.
    intros n s rho F.
    rewrite Forall_wf_to_abt in *.
    rewrite descend_to_abt_comm.
    auto using A.descend_wf.
  Qed.

  Lemma descend_1 :
    forall rho,
      descend 1 rho = var 0 :: map (shift 0 1) rho.
  Proof.
    intros rho.
    apply map_inj with (f := to_abt).
    apply to_abt_inj.
    rewrite descend_to_abt_comm.
    simpl.
    rewrite var_to_abt.
    rewrite map_shift_to_abt_comm.
    now rewrite A.descend_1.
  Qed.

  Lemma descend_2 :
    forall rho,
      descend 2 rho = var 0 :: var 1 :: map (shift 0 2) rho.
  Proof.
    intros rho.
    apply map_inj with (f := to_abt).
    apply to_abt_inj.
    rewrite descend_to_abt_comm.
    simpl.
    rewrite A.descend_2.
    rewrite !var_to_abt.
    now rewrite map_shift_to_abt_comm.
  Qed.

  Lemma shift_shift' :
    forall c d e,
      shift 0 1 (shift c d e) = shift (S c) d (shift 0 1 e).
  Proof.
    intros c d e.
    apply to_abt_inj.
    rewrite !shift_to_abt_comm.
    apply A.shift_shift'.
  Qed.

  Lemma map_shift_map_shift' :
    forall c d l,
      map (shift 0 1) (map (shift c d) l) =
      map (shift (S c) d) (map (shift 0 1) l).
  Proof.
    intros c d l.
    rewrite !map_map.
    apply map_ext.
    auto using shift_shift'.
  Qed.

  Definition SIS d n := (map (shift 0 d) (identity_subst n)).
  Lemma SIS_to_abt_comm :
    forall d n,
      map to_abt (SIS d n) = A.SIS d n.
  Proof.
    intros d n.
    unfold SIS.
    now rewrite map_shift_to_abt_comm, identity_subst_to_abt_comm.
  Qed.

  Lemma map_shift_identity_subst_split :
    forall c d n,
      c <= n ->
      map (shift c d) (identity_subst n) =
      identity_subst c ++ SIS (c + d) (n - c).
  Proof.
    intros c d n LE.
    apply map_inj with (f := to_abt).
    apply to_abt_inj.
    rewrite map_app.
    rewrite !map_shift_to_abt_comm.
    rewrite !identity_subst_to_abt_comm, SIS_to_abt_comm.
    now rewrite A.map_shift_identity_subst_split.
  Qed.

  Lemma subst_shift :
    forall e rho1 rho2 rho3 n1 n2,
      wf (List.length (rho1 ++ rho3)) e ->
      List.length rho1 = n1 ->
      List.length rho2 = n2 ->
      subst (rho1 ++ rho2 ++ rho3) (shift n1 n2 e) =
      subst (rho1 ++ rho3) e.
  Proof.
    intros e rho1 rho2 rho3 n1 n2 WF En1 En2. subst n1 n2.
    apply to_abt_inj.
    rewrite !subst_to_abt_comm, shift_to_abt_comm, !map_app.
    pose proof (A.subst_shift (to_abt e) (map to_abt rho1)
                              (map to_abt rho2) (map to_abt rho3)) as H.
    rewrite !map_length in *.
    rewrite H; auto.
    apply wf_to_abt.
    now rewrite !app_length, !map_length in *.
  Qed.

  Lemma shift_subst :
    forall e c d rho,
      wf (List.length rho) e ->
      shift c d (subst rho e) =
      subst (List.map (shift c d) rho) e.
  Proof.
    intros e c d rho WF.
    apply to_abt_inj.
    rewrite shift_to_abt_comm, !subst_to_abt_comm, !map_shift_to_abt_comm.
    apply A.shift_subst.
    rewrite map_length.
    now apply wf_to_abt.
  Qed.

  Lemma identity_subst_app :
    forall n1 n2,
      identity_subst (n1 + n2) = identity_subst n1 ++ SIS n1 n2.
  Proof.
    intros n1 n2.
    apply map_inj with (f := to_abt).
    apply to_abt_inj.
    rewrite map_app, !identity_subst_to_abt_comm,
           SIS_to_abt_comm.
    apply A.identity_subst_app.
  Qed.

  Lemma subst_extend_with_identity :
    forall e rho n,
      subst rho e = subst (rho ++ SIS (length rho) n) e.
  Proof.
    intros e rho n.
    apply to_abt_inj.
    rewrite !subst_to_abt_comm, map_app, SIS_to_abt_comm.
    rewrite A.subst_extend_with_identity with (n := n).
    now rewrite map_length.
  Qed.

  Lemma SIS_length :
    forall d n,
      length (SIS d n) = n.
  Proof.
    intros d n.
    rewrite <- map_length with (f := to_abt).
    rewrite SIS_to_abt_comm.
    now rewrite A.SIS_length.
  Qed.

  Lemma wf_SIS : forall d n, Forall (wf (d + n)) (SIS d n).
  Proof.
    intros d n.
    rewrite Forall_wf_to_abt.
    rewrite SIS_to_abt_comm.
    apply A.wf_SIS.
  Qed.

  Lemma SIS_merge :
    forall n d1 d2,
      map (shift 0 d2) (SIS d1 n) = SIS (d1 + d2) n.
  Proof.
    intros n d1 d2.
    apply map_inj with (f := to_abt).
    apply to_abt_inj.
    rewrite map_shift_to_abt_comm, !SIS_to_abt_comm.
    now rewrite A.SIS_merge.
  Qed.

  Lemma SIS_merge' :
    forall n d,
      map (shift 0 1) (SIS d n) = SIS (S d) n.
  Proof.
    intros n d.
    rewrite SIS_merge.
    now rewrite Nat.add_1_r.
  Qed.

  Lemma SIS_0 : forall n, SIS 0 n = identity_subst n.
  Proof.
    intros n.
    apply map_inj with (f := to_abt).
    apply to_abt_inj.
    rewrite SIS_to_abt_comm, identity_subst_to_abt_comm.
    now rewrite A.SIS_0.
  Qed.

  Lemma SIS_app :
    forall n1 n2 d,
      SIS d (n1 + n2) = SIS d n1 ++ SIS (n1 + d) n2.
  Proof.
    intros n1 n2 d.
    apply map_inj with (f := to_abt).
    apply to_abt_inj.
    rewrite map_app, !SIS_to_abt_comm.
    now rewrite A.SIS_app.
  Qed.

  Lemma subst_shift_cons_identity_subst :
    forall c d n e1 e2,
      c <= n ->
      wf (S n) e2 ->
      subst (shift c d e1 :: identity_subst (d + n)) (shift (S c) d e2) =
      subst (shift c d e1 :: map (shift c d) (identity_subst n)) e2.
  Proof.
    intros c d n e1 e2 LE WF.

    replace (d + n) with (c + (d + (n - c))) by lia.
    rewrite identity_subst_app.
    rewrite SIS_app.
    rewrite app_comm_cons.
    rewrite subst_shift; simpl;
      [| | auto using f_equal, identity_subst_length | auto using SIS_length].
    + rewrite map_shift_identity_subst_split by assumption.
      now rewrite Nat.add_comm.
    + rewrite app_length, identity_subst_length, SIS_length.
      now replace (c + (n - c)) with n by lia.
  Qed.

  Lemma wf_cons :
    forall n e l,
      wf (S n) e ->
      Forall (wf n) l ->
      Forall (wf (S n)) (e :: map (shift 0 1) l).
  Proof.
    auto using wf_map_shift'.
  Qed.

  Lemma subst_shift_cons :
    forall e e' g,
      wf (length g) e ->
      subst (e' :: g) (shift 0 1 e) = subst g e.
  Proof.
    intros.
    pose proof @subst_shift e [] [e'] g.
    auto.
  Qed.
End abt_util.
