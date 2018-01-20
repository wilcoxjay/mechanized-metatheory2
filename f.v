From mm Require Import util abt.

Module tyop.
  Inductive t' :=
  | arrow
  | all
  .
  Definition t := t'.

  Definition arity (op : t) : arity.t :=
    match op with
    | arrow => [0; 0]
    | all => [1]
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
  .
  Definition t := t'.

  Definition arity (op : t) : arity.t :=
    match op with
    | abs => [1]
    | app => [0; 0]
    | tyabs => [0]
    | tyapp => [0]
    end.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
  Defined.
End exprop.

Module type.
  Module A := abt.internal tyop.

  Inductive t :=
  | var (alpha : nat) : t
  | arrow : t -> t -> t
  | all : t -> t
  .

  Fixpoint to_abt (ty : t) : A.t :=
    match ty with
    | var n => A.var n
    | arrow ty1 ty2 => A.op tyop.arrow [A.bind 0 (to_abt ty1); A.bind 0 (to_abt ty2)]
    | all ty' => A.op tyop.all [A.bind 1 (to_abt ty')]
    end.

  Fixpoint of_abt (a : A.t) : t :=
    match a with
    | A.var n => var n
    | A.op tyop.arrow [A.bind 0 a1; A.bind 0 a2] => arrow (of_abt a1) (of_abt a2)
    | A.op tyop.all [A.bind 1 a'] => all (of_abt a')
    | _ => var 0 (* bogus *)
    end.

  Lemma ws_to_abt : forall ty, A.ws (to_abt ty).
  Proof. induction ty; simpl; intuition. Qed.

  Lemma of_to_abt : forall ty, of_abt (to_abt ty) = ty.
  Proof. induction ty; simpl; f_equal; auto. Qed.

  Lemma to_of_abt : forall a, A.ws a -> to_abt (of_abt a) = a.
  Proof.
    induction a using A.rect'
    with (Pb := fun b => forall v,
                    A.ws_binder v b ->
                    match b with
                    | A.bind _ a => to_abt (of_abt a) = a
                    end) ; simpl; intros; f_equal; intuition;
      fold A.ws_binders in *.
    - repeat break_match; subst; simpl in *; intuition;
        repeat match goal with
               | [ H : Forall _ (_ :: _) |- _ ] => inversion H; subst; clear H
               end; simpl in *; try omega;
      repeat f_equal; eauto.
  Qed.

  Fixpoint shift c d (ty : t) : t :=
    match ty with
    | var alpha => var (if alpha <? c then alpha else alpha + d)
    | arrow ty1 ty2 => arrow (shift c d ty1) (shift c d ty2)
    | all ty' => all (shift (S c) d ty')
    end.

  Lemma shift_to_of_abt : forall ty c d, shift c d ty = of_abt (A.shift c d (to_abt ty)).
  Proof. induction ty; simpl; intros c d; f_equal; auto. Qed.
    
  Fixpoint subst rho ty :=
    match ty with
    | var alpha => match nth_error rho alpha with
                  | Some ty' => ty'
                  | None => ty
                  end
    | arrow ty1 ty2 => arrow (subst rho ty1) (subst rho ty2)
    | all ty' => all (subst (var 0 :: map (shift 0 1) rho) ty')
    end.

  Hint Resolve A.ws_shift ws_to_abt.

  Lemma shift_to_abt_comm : forall ty c d, to_abt (shift c d ty) = A.shift c d (to_abt ty).
  Proof. intros. rewrite shift_to_of_abt, to_of_abt; auto. Qed.

  Lemma map_shift_to_abt_comm :
    forall c d rho, map to_abt (map (shift c d) rho) = map (A.shift c d) (map to_abt rho).
  Proof.
    intros.
    rewrite !map_map.
    now erewrite map_ext by (intros; apply shift_to_abt_comm).
  Qed.
  
  Lemma subst_to_of_abt :
    forall ty rho,
      subst rho ty = of_abt (A.subst (map to_abt rho) (to_abt ty)).
  Proof.
    induction ty; simpl; intros rho; try rewrite ?A.descend_0, ?A.descend_1; f_equal; auto.
    - rewrite nth_error_map.
      break_match; auto.
      now rewrite of_to_abt.
    - rewrite IHty. simpl.
      now rewrite map_shift_to_abt_comm.
  Qed.

  Fixpoint wf n ty :=
    match ty with
    | var alpha => alpha < n
    | arrow ty1 ty2 => wf n ty1 /\ wf n ty2
    | all ty' => wf (S n) ty'
    end.

  Lemma wf_to_abt : forall ty n, wf n ty <-> A.wf n (to_abt ty).
  Proof. induction ty; simpl; firstorder. Qed.

  Lemma wf_of_abt :
    forall a n,
      A.ws a -> 
      wf n (of_abt a) <-> A.wf n a.
  Proof.
    intros.
    pose proof wf_to_abt (of_abt a) n.
    rewrite to_of_abt in *; auto.
  Qed.

  Fixpoint identity_subst (n : nat) : list t :=
    match n with
    | 0 => []
    | S n => var 0 :: map (shift 0 1) (identity_subst n)
    end.

  Lemma shift_of_abt_comm :
    forall a c d,
      A.ws a -> 
      shift c d (of_abt a) = of_abt (A.shift c d a).
  Proof.
    intros a c d WS.
    rewrite shift_to_of_abt.
    now rewrite to_of_abt by assumption.
  Qed.

  Lemma map_shift_of_abt_comm :
    forall rho c d,
      Forall A.ws rho -> 
      map (shift c d) (map of_abt rho) = map of_abt (map (A.shift c d) rho).
  Proof.
    intros rho c d WS.
    rewrite !map_map.
    apply map_ext_in.
    intros a I.
    rewrite shift_of_abt_comm; auto.
    eapply Forall_forall; eauto.
  Qed.

  Lemma identity_subst_of_abt :
    forall n,
      identity_subst n = List.map of_abt (A.identity_subst n).
  Proof.
    induction n; simpl; f_equal; auto.
    rewrite IHn.
    rewrite map_shift_of_abt_comm; auto.
    apply A.ws_identity_subst.
  Qed.

  Lemma wf_shift : forall ty c d n, wf n ty -> wf (d + n) (shift c d ty).
  Proof.
    intros.
    rewrite shift_to_of_abt.
    rewrite wf_of_abt; auto.
    apply A.wf_shift.
    now rewrite <- wf_to_abt.
  Qed.

  Lemma wf_subst : forall ty n rho, wf (length rho) ty -> Forall (wf n) rho -> wf n (subst rho ty).
  Proof.
    intros ty n rho WF F.
    rewrite subst_to_of_abt.
    rewrite wf_of_abt.
    - apply A.wf_subst.
      + now rewrite map_length, <- wf_to_abt.
      + rewrite Forall_map.
        eapply Forall_impl; try eassumption.
        intros ty' WF'.
        now rewrite <- wf_to_abt.
    - apply A.ws_subst; auto.
      rewrite Forall_map.
      apply Forall_forall; auto.
  Qed.

  Lemma identity_subst_length : forall n, length (identity_subst n) = n.
  Proof.
    intros.
    rewrite identity_subst_of_abt.
    rewrite map_length.
    apply A.identity_subst_length.
  Qed.

  Lemma wf_identity_subst: forall n : nat, Forall (wf n) (identity_subst n).
  Proof.
    intros.
    rewrite identity_subst_of_abt.
    rewrite Forall_map.
    rewrite Forall_forall.
    intros ty I.
    rewrite wf_of_abt.
    - eapply Forall_forall; [apply A.wf_identity_subst|]; auto.
    - eapply Forall_forall; [apply A.ws_identity_subst|]; eauto.
  Qed.

  Lemma wf_weaken : forall ty n d, n <= d -> wf n ty -> wf d ty.
  Proof.
    intros ty n d LE.
    rewrite !wf_to_abt.
    eauto using A.wf_weaken.
  Qed.

  Lemma shift_merge : forall ty c d1 d2 , shift c d2 (shift c d1 ty) = shift c (d2 + d1) ty.
  Proof.
    intros ty c d1 d2.
    rewrite !shift_to_of_abt.
    rewrite to_of_abt by auto.
    now rewrite A.shift_merge.
  Qed.

  Lemma shift_nop_d :
    forall ty c,
      shift c 0 ty = ty.
  Proof.
    intros ty c.
    rewrite shift_to_of_abt.
    rewrite A.shift_nop_d.
    now rewrite of_to_abt.
  Qed.

  Lemma subst_to_abt_comm : forall ty rho, to_abt (subst rho ty) = A.subst (map to_abt rho) (to_abt ty).
  Proof.
    intros. rewrite subst_to_of_abt, to_of_abt; auto.
    apply A.ws_subst; auto.
    rewrite Forall_map.
    apply Forall_forall.
    auto.
  Qed.

  Lemma map_subst_to_abt_comm :
    forall rho1 rho2,
      map to_abt (map (subst rho2) rho1) =
      map (A.subst (map to_abt rho2)) (map to_abt rho1).
  Proof.
    intros rho1 rho2.
    rewrite !map_map.
    apply map_ext.
    intros ty'.
    auto using subst_to_abt_comm.
  Qed.

  Lemma subst_subst :
    forall ty rho1 rho2,
      wf (List.length rho1) ty ->
      List.Forall (wf (List.length rho2)) rho1 ->
      subst rho2 (subst rho1 ty) =
      subst (List.map (subst rho2) rho1) ty.
  Proof.
    intros ty rho1 rho2 WF F.
    rewrite !subst_to_of_abt.
    rewrite !to_of_abt.
    - rewrite A.subst_subst.
      + now rewrite map_subst_to_abt_comm.
      + now rewrite map_length, <- wf_to_abt.
      + rewrite map_length, Forall_map.
        eapply Forall_impl; try eassumption.
        intros ty'.
        now rewrite wf_to_abt.
    - apply A.ws_subst; auto.
      rewrite Forall_map.
      apply Forall_forall; auto.
  Qed.

  Lemma subst_shift_singleton :
    forall ty ty',
      wf 0 ty ->
      subst [ty'] (shift 0 1 ty) = ty.
  Proof.
    intros.
    rewrite subst_to_of_abt, shift_to_of_abt.
    simpl.
    rewrite to_of_abt.
    - rewrite A.subst_shift_singleton.
      + now rewrite of_to_abt.
      + now rewrite <- wf_to_abt.
    - apply A.ws_shift; auto.
  Qed.

  Lemma subst_identity :
    forall ty n,
      subst (identity_subst n) ty = ty.
  Proof.
    intros ty n.
    rewrite subst_to_of_abt, identity_subst_of_abt.
    rewrite !map_map.
    erewrite map_ext_in.
    rewrite map_id.
    rewrite A.subst_identity.
    now rewrite of_to_abt.
    intros ty' I.
    simpl.
    rewrite to_of_abt; auto.
    eapply Forall_forall.
    apply A.ws_identity_subst.
    eauto.
  Qed.

End type.

Module expr.
  Module A := abt.internal exprop.

  Inductive t :=
  | var (x : nat) : t
  | abs : t -> t
  | app : t -> t -> t
  | tyabs : t -> t
  | tyapp : t -> t
  .

  Fixpoint to_abt (ty : t) : A.t :=
    match ty with
    | var n => A.var n
    | abs e' => A.op exprop.abs [A.bind 1 (to_abt e')]
    | app e1 e2 => A.op exprop.app [A.bind 0 (to_abt e1); A.bind 0 (to_abt e2)]
    | tyabs e' => A.op exprop.tyabs [A.bind 0 (to_abt e')] 
    | tyapp e' => A.op exprop.tyapp [A.bind 0 (to_abt e')]
    end.

  Fixpoint of_abt (a : A.t) : t :=
    match a with
    | A.var n => var n
    | A.op exprop.abs [A.bind 1 a'] => abs (of_abt a')
    | A.op exprop.app [A.bind 0 a1; A.bind 0 a2] => app (of_abt a1) (of_abt a2)
    | A.op exprop.tyabs [A.bind 0 a'] => tyabs (of_abt a')
    | A.op exprop.tyapp [A.bind 0 a'] => tyapp (of_abt a')
    | _ => var 0 (* bogus *)
    end.

  Lemma ws_to_abt : forall e, A.ws (to_abt e).
  Proof. induction e; simpl; intuition. Qed.

  Lemma of_to_abt : forall e, of_abt (to_abt e) = e.
  Proof. induction e; simpl; f_equal; auto. Qed.

  Lemma to_of_abt : forall a, A.ws a -> to_abt (of_abt a) = a.
  Proof.
    induction a using A.rect'
    with (Pb := fun b => forall v,
                    A.ws_binder v b ->
                    match b with
                    | A.bind _ a => to_abt (of_abt a) = a
                    end) ; simpl; intros; f_equal; intuition;
      fold A.ws_binders in *.
    - repeat break_match; subst; simpl in *; intuition;
        repeat match goal with
               | [ H : Forall _ (_ :: _) |- _ ] => inversion H; subst; clear H
               end; simpl in *; try omega;
      repeat f_equal; eauto.
  Qed.

  Fixpoint shift c d (e : t) : t :=
    match e with
    | var x => var (if x <? c then x else x + d)
    | abs e' => abs (shift (S c) d e')
    | app e1 e2 => app (shift c d e1) (shift c d e2)
    | tyabs e' => tyabs (shift c d e')
    | tyapp e' => tyapp (shift c d e')
    end.

  Lemma shift_to_of_abt : forall e c d, shift c d e = of_abt (A.shift c d (to_abt e)).
  Proof. induction e; simpl; intros c d; f_equal; auto. Qed.
    
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
    end.

  Hint Resolve A.ws_shift ws_to_abt.

  Lemma shift_to_abt_comm : forall e c d, to_abt (shift c d e) = A.shift c d (to_abt e).
  Proof. intros. rewrite shift_to_of_abt, to_of_abt; auto. Qed.

  Lemma map_shift_to_abt_comm :
    forall c d rho, map to_abt (map (shift c d) rho) = map (A.shift c d) (map to_abt rho).
  Proof.
    intros.
    rewrite !map_map.
    now erewrite map_ext by (intros; apply shift_to_abt_comm).
  Qed.
  
  Lemma subst_to_of_abt :
    forall e rho,
      subst rho e = of_abt (A.subst (map to_abt rho) (to_abt e)).
  Proof.
    induction e; simpl; intros rho; try rewrite ?A.descend_0, ?A.descend_1; f_equal; auto.
    - rewrite nth_error_map.
      break_match; auto.
      now rewrite of_to_abt.
    - rewrite IHe. simpl.
      now rewrite map_shift_to_abt_comm.
  Qed.

  Fixpoint wf n e :=
    match e with
    | var x => x < n
    | abs e' => wf (S n) e'
    | app e1 e2 => wf n e1 /\ wf n e2
    | tyabs e' => wf n e'
    | tyapp e' => wf n e'
    end.

  Lemma wf_to_abt : forall e n, wf n e <-> A.wf n (to_abt e).
  Proof. induction e; simpl; firstorder. Qed.

  Lemma wf_of_abt :
    forall a n,
      A.ws a -> 
      wf n (of_abt a) <-> A.wf n a.
  Proof.
    intros.
    pose proof wf_to_abt (of_abt a) n.
    rewrite to_of_abt in *; auto.
  Qed.

  Fixpoint identity_subst (n : nat) : list t :=
    match n with
    | 0 => []
    | S n => var 0 :: map (shift 0 1) (identity_subst n)
    end.

  Lemma shift_of_abt_comm :
    forall a c d,
      A.ws a -> 
      shift c d (of_abt a) = of_abt (A.shift c d a).
  Proof.
    intros a c d WS.
    rewrite shift_to_of_abt.
    now rewrite to_of_abt by assumption.
  Qed.

  Lemma map_shift_of_abt_comm :
    forall rho c d,
      Forall A.ws rho -> 
      map (shift c d) (map of_abt rho) = map of_abt (map (A.shift c d) rho).
  Proof.
    intros rho c d WS.
    rewrite !map_map.
    apply map_ext_in.
    intros a I.
    rewrite shift_of_abt_comm; auto.
    eapply Forall_forall; eauto.
  Qed.

  Lemma identity_subst_of_abt :
    forall n,
      identity_subst n = List.map of_abt (A.identity_subst n).
  Proof.
    induction n; simpl; f_equal; auto.
    rewrite IHn.
    rewrite map_shift_of_abt_comm; auto.
    apply A.ws_identity_subst.
  Qed.

  Lemma wf_shift : forall e c d n, wf n e -> wf (d + n) (shift c d e).
  Proof.
    intros.
    rewrite shift_to_of_abt.
    rewrite wf_of_abt; auto.
    apply A.wf_shift.
    now rewrite <- wf_to_abt.
  Qed.

  Lemma wf_subst : forall e n rho, wf (length rho) e -> Forall (wf n) rho -> wf n (subst rho e).
  Proof.
    intros e n rho WF F.
    rewrite subst_to_of_abt.
    rewrite wf_of_abt.
    - apply A.wf_subst.
      + now rewrite map_length, <- wf_to_abt.
      + rewrite Forall_map.
        eapply Forall_impl; try eassumption.
        intros e' WF'.
        now rewrite <- wf_to_abt.
    - apply A.ws_subst; auto.
      rewrite Forall_map.
      apply Forall_forall; auto.
  Qed.

  Lemma identity_subst_length : forall n, length (identity_subst n) = n.
  Proof.
    intros.
    rewrite identity_subst_of_abt.
    rewrite map_length.
    apply A.identity_subst_length.
  Qed.

  Lemma wf_identity_subst: forall n : nat, Forall (wf n) (identity_subst n).
  Proof.
    intros.
    rewrite identity_subst_of_abt.
    rewrite Forall_map.
    rewrite Forall_forall.
    intros e I.
    rewrite wf_of_abt.
    - eapply Forall_forall; [apply A.wf_identity_subst|]; auto.
    - eapply Forall_forall; [apply A.ws_identity_subst|]; eauto.
  Qed.

  Lemma wf_weaken : forall e n d, n <= d -> wf n e -> wf d e.
  Proof.
    intros e n d LE.
    rewrite !wf_to_abt.
    eauto using A.wf_weaken.
  Qed.

  Lemma shift_merge : forall e c d1 d2 , shift c d2 (shift c d1 e) = shift c (d2 + d1) e.
  Proof.
    intros e c d1 d2.
    rewrite !shift_to_of_abt.
    rewrite to_of_abt by auto.
    now rewrite A.shift_merge.
  Qed.

  Lemma shift_nop_d :
    forall e c,
      shift c 0 e = e.
  Proof.
    intros e c.
    rewrite shift_to_of_abt.
    rewrite A.shift_nop_d.
    now rewrite of_to_abt.
  Qed.

  Lemma subst_to_abt_comm : forall e rho, to_abt (subst rho e) = A.subst (map to_abt rho) (to_abt e).
  Proof.
    intros. rewrite subst_to_of_abt, to_of_abt; auto.
    apply A.ws_subst; auto.
    rewrite Forall_map.
    apply Forall_forall.
    auto.
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

  Lemma subst_subst :
    forall e rho1 rho2,
      wf (List.length rho1) e ->
      List.Forall (wf (List.length rho2)) rho1 ->
      subst rho2 (subst rho1 e) =
      subst (List.map (subst rho2) rho1) e.
  Proof.
    intros e rho1 rho2 WF F.
    rewrite !subst_to_of_abt.
    rewrite !to_of_abt.
    - rewrite A.subst_subst.
      + now rewrite map_subst_to_abt_comm.
      + now rewrite map_length, <- wf_to_abt.
      + rewrite map_length, Forall_map.
        eapply Forall_impl; try eassumption.
        intros e'.
        now rewrite wf_to_abt.
    - apply A.ws_subst; auto.
      rewrite Forall_map.
      apply Forall_forall; auto.
  Qed.

  Lemma subst_shift_singleton :
    forall e e',
      wf 0 e ->
      subst [e'] (shift 0 1 e) = e.
  Proof.
    intros.
    rewrite subst_to_of_abt, shift_to_of_abt.
    simpl.
    rewrite to_of_abt.
    - rewrite A.subst_shift_singleton.
      + now rewrite of_to_abt.
      + now rewrite <- wf_to_abt.
    - apply A.ws_shift; auto.
  Qed.

  Lemma subst_identity :
    forall e n,
      subst (identity_subst n) e = e.
  Proof.
    intros e n.
    rewrite subst_to_of_abt, identity_subst_of_abt.
    rewrite !map_map.
    erewrite map_ext_in.
    rewrite map_id.
    rewrite A.subst_identity.
    now rewrite of_to_abt.
    intros e' I.
    simpl.
    rewrite to_of_abt; auto.
    eapply Forall_forall.
    apply A.ws_identity_subst.
    eauto.
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
    induction 1; cbn in *; intuition.
    - now eapply Forall_nth; eauto.
    - apply IHt.
      rewrite Forall_map.
      eapply Forall_impl; try eassumption.
      intros ty' WF'.
      now apply type.wf_shift with (d := 1).
    - apply type.wf_subst.
      + simpl. now rewrite type.identity_subst_length in *.
      + constructor; auto.
        apply type.wf_identity_subst.
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
