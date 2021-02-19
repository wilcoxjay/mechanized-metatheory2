Require Import mm.util.
Set Implicit Arguments.

Module valence.
  Definition t : Type := nat.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y} := eq_nat_dec.
End valence.

Module arity.
  Definition t : Type := list valence.t.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    apply list_eq_dec.
    apply valence.eq_dec.
  Defined.
End arity.

Module Type OPERATOR.
  Parameter t : Type.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
  Parameter arity : t -> arity.t.
End OPERATOR.

Module Type ABT.
  Declare Module O : OPERATOR.

  Local Unset Elimination Schemes.
  Inductive t : Type :=
  | var (x : nat) : t
  | op : O.t -> list binder -> t
  with
  binder :=
  | bind (v : valence.t) : t -> binder.

  Section rect.
    Variable P : t -> Type.
    Variable Pb : binder -> Type.
    Variable Pbl : list binder -> Type.

    Hypotheses Pvar : forall x, P (var x).
    Hypothesis Pop : forall o bs, Pbl bs -> P (op o bs).
    Hypothesis Pbind : forall s e, P e -> Pb (bind s e).
    Hypothesis Pblnil : Pbl [].
    Hypothesis Pblcons : forall b bs, Pb b -> Pbl bs -> Pbl (b :: bs).

    Fixpoint rect (e : t) : P e :=
      let fix rect_list (l : list binder) : Pbl l :=
          match l with
          | [] => Pblnil
          | b :: bs => Pblcons (rect_binder b) (rect_list bs)
          end
      in
      match e with
      | var x => Pvar x
      | op o bs => Pop o (rect_list bs)
      end
    with rect_binder (b : binder) : Pb b :=
      match b with
      | bind s e => Pbind s (rect e)
      end
    .

    Definition rect_list :=
      fix rect_list (l : list binder) : Pbl l :=
          match l with
          | [] => Pblnil
          | b :: bs => Pblcons (rect_binder b) (rect_list bs)
          end.
  End rect.


  Section rect'.
    Variable P : t -> Prop.
    Variable Pb : binder -> Prop.
    Let Pbl (bs : list binder) : Prop := Forall Pb bs.

    Hypotheses Pvar : forall n, P (var n).
    Hypothesis Pop : forall o bs, Pbl bs -> P (op o bs).
    Hypothesis Pbind : forall n e, P e -> Pb (bind n e).

    Definition rect' (e : t) : P e.
      refine (rect P Pb Pbl Pvar Pop Pbind (Forall_nil _) _ e).
      intros. constructor; auto.
    Defined.
  End rect'.

  Fixpoint ws (e : t) {struct e} :=
    let fix go_list (a : arity.t) (bs : list binder) {struct bs} :=
        match a, bs with
        | [], [] => True
        | v :: a, b :: bs => ws_binder v b /\ go_list a bs
        | _, _ => False
        end
    in
    match e with
    | var n => True
    | op o bs => go_list (O.arity o) bs
    end
  with
  ws_binder (v : valence.t) (b : binder) {struct b} :=
    match b with
    | bind v' e => v = v' /\ ws e
    end.
  Definition ws_binders :=
    fix go_list (a : arity.t) (bs : list binder) {struct bs} :=
        match a, bs with
        | [], [] => True
        | v :: a, b :: bs => ws_binder v b /\ go_list a bs
        | _, _ => False
        end.

  Fixpoint wf (n : nat) (e : t) :=
    let fix go_list (n : nat) (bs : list binder) :=
        match bs with
        | [] => True
        | b :: bs => wf_binder n b /\ go_list n bs
        end
    in
    match e with
    | var x => x < n
    | op o bs => go_list n bs
    end
  with wf_binder (n : nat) (b : binder) :=
         match b with
         | bind s e => wf (s + n) e
         end.
  Definition wf_binders :=
    fix go_list (n : nat) (bs : list binder) :=
        match bs with
        | [] => True
        | b :: bs => wf_binder n b /\ go_list n bs
        end.

  Fixpoint t_map (onvar : (*c*) nat -> (*x*) nat -> t) (c : nat) (e : t) : t :=
    let fix go_list (onvar : nat -> nat -> t) (c : nat) (bs : list binder) : list binder :=
        match bs with
        | [] => []
        | b :: bs => t_map_binder onvar c b :: go_list onvar c bs
        end
    in
        match e with
        | var x => onvar c x
        | op o bs => op o (go_list onvar c bs)
        end
  with t_map_binder (onvar : nat -> nat -> t) (c : nat) (b : binder) : binder :=
         match b with
         | bind n e => bind n (t_map onvar (n + c) e)
         end
  .
  Definition t_map_binders :=
    fix go_list (onvar : nat -> nat -> t) (c : nat) (bs : list binder) : list binder :=
      match bs with
      | [] => []
      | b :: bs => t_map_binder onvar c b :: go_list onvar c bs
      end.

  Definition shift_onvar d := (fun c x => if x <? c then var x else var (x + d)).
  Definition shift_via_t_map (c d : nat) (e : t) : t :=
    t_map (shift_onvar d) c e.
  Definition shift_binder_via_t_map (c d : nat) (b : binder) : binder :=
    t_map_binder (shift_onvar d) c b.
  Definition shift_binders_via_t_map (c d : nat) (bs : list binder) : list binder :=
    t_map_binders (shift_onvar d) c bs.

  Fixpoint shift (c d : nat) (e : t) : t :=
    let fix go_list (c d : nat) (bs : list binder) : list binder :=
        match bs with
        | [] => []
        | b :: bs => shift_binder c d b :: go_list c d bs
        end
    in
        match e with
        | var x => var (if x <? c then x else x + d)
        | op o bs => op o (go_list c d bs)
        end
  with shift_binder (c d : nat) (b : binder) : binder :=
         match b with
         | bind n e => bind n (shift (n + c) d e)
         end
  .
  Definition shift_binders :=
    fix go_list (c d : nat) (bs : list binder) : list binder :=
        match bs with
        | [] => []
        | b :: bs => shift_binder c d b :: go_list c d bs
        end.

  Parameter shift_via_t_map_is_shift :
    forall d e c,
      shift_via_t_map c d e = shift c d e.

  Parameter t_map_bump :
    forall ov d e c,
      t_map ov (c + d) e = t_map (fun c x => ov (c + d) x) c e.

  Parameter t_map_ext :
    forall ov ov',
      (forall c x, ov c x = ov' c x) ->
      forall e c,
        t_map ov c e = t_map ov' c e.

  Parameter t_map_t_map :
    forall ov1 ov2 e c1 c2,
      t_map ov2 c2 (t_map ov1 c1 e) =
      t_map (fun c x => t_map ov2 (c + c2 - c1) (ov1 c x)) c1 e.

  Fixpoint identity_subst (n : nat) : list t :=
    match n with
    | 0 => []
    | S n => var 0 :: map (shift 0 1) (identity_subst n)
    end.

  Definition SIS d n := (map (shift 0 d) (identity_subst n)).

  Definition descend (n : nat) (rho : list t) : list t :=
    identity_subst n ++ map (shift 0 n) rho.

  Fixpoint subst (rho : list t) (e : t) : t :=
    let fix go_list (rho : list t) (bs : list binder) : list binder :=
        match bs with
        | [] => []
        | b :: bs => subst_binder rho b :: go_list rho bs
        end
    in
    match e with
    | var x => match nth_error rho x with
              | Some e' => e'
              | None => e
              end
    | op o bs => op o (go_list rho bs)
    end
  with subst_binder (rho : list t) (b : binder) : binder :=
         match b with
         | bind n e => bind n (subst (descend n rho) e)
         end
  .
  Definition subst_binders :=
    fix go_list (rho : list t) (bs : list binder) : list binder :=
        match bs with
        | [] => []
        | b :: bs => subst_binder rho b :: go_list rho bs
        end.

  Parameter ws_shift : forall e c d, ws e -> ws (shift c d e).
  Parameter ws_subst :
    forall e rho, ws e -> Forall ws rho -> ws (subst rho e).
  Parameter ws_identity_subst : forall n, Forall ws (identity_subst n).

  Parameter wf_shift : forall e c d n, wf n e -> wf (d + n) (shift c d e).
  Parameter wf_subst : forall e n rho,
      wf (length rho) e -> List.Forall (wf n) rho -> wf n (subst rho e).
  Parameter wf_identity_subst : forall n, Forall (wf n) (identity_subst n).
  Parameter wf_weaken : forall e n d, n <= d -> wf n e -> wf d e.
  Parameter wf_shift_inv : forall e c d n, wf n (shift c d e) -> wf (max c (n - d)) e.
  Parameter wf_subst_inv : forall e n rho, wf n (subst rho e) -> wf (max n (length rho)) e.

  Parameter identity_subst_length : forall n, length (identity_subst n) = n.

  Parameter shift_merge :
    forall e c1 c2 d1 d2,
      c1 <= c2 ->
      c2 <= c1 + d1  ->
      shift c2 d2 (shift c1 d1 e) = shift c1 (d1 + d2) e.

  Parameter shift_merge' : forall e c d1 d2, shift c d2 (shift c d1 e) = shift c (d2 + d1) e.
  Parameter shift_nop_d : forall e c, shift c 0 e = e.
  Parameter shift_shift :
    forall e c1 d1 c2 d2,
      c2 <= c1 ->
      shift c2 d2 (shift c1 d1 e) =
      shift (c1 + d2) d1 (shift c2 d2 e).

  Parameter shift_shift' : forall c d e,
      shift 0 1 (shift c d e) = shift (S c) d (shift 0 1 e).

  Parameter shift_inj :
    forall e1 e2 c d,
      shift c d e1 = shift c d e2 ->
      e1 = e2.

  Parameter subst_subst :
    forall e rho1 rho2,
      wf (List.length rho1) e ->
      List.Forall (wf (List.length rho2)) rho1 ->
      subst rho2 (subst rho1 e) =
      subst (List.map (subst rho2) rho1) e.

  Parameter subst_identity : forall e n, subst (identity_subst n) e = e.
  Parameter subst_shift_singleton : forall e e', wf 0 e -> subst [e'] (shift 0 1 e) = e.
  Parameter subst_shift_cons :
    forall e e' g,
      wf (length g) e ->
      subst (e' :: g) (shift 0 1 e) = subst g e.

  Parameter map_subst_identity_subst :
    forall rho,
      map (subst rho) (identity_subst (length rho)) = rho.

  Parameter subst_shift :
    forall e rho1 rho2 rho3,
      wf (List.length (rho1 ++ rho3)) e ->
      subst (rho1 ++ rho2 ++ rho3) (shift (List.length rho1) (List.length rho2) e) =
      subst (rho1 ++ rho3) e.

  Parameter shift_subst :
    forall e c d rho,
      wf (List.length rho) e ->
      shift c d (subst rho e) =
      subst (List.map (shift c d) rho) e.

  Parameter descend_0 : forall rho, descend 0 rho = rho.
  Parameter descend_1 : forall rho, descend 1 rho = var 0 :: map (shift 0 1) rho.
  Parameter descend_2 : forall rho, descend 2 rho = var 0 :: var 1 :: map (shift 0 2) rho.

  Parameter descend_wf : forall n s rho, Forall (wf n) rho -> Forall (wf (s + n)) (descend s rho).

  Parameter subst_cons :
    forall e v rho,
      wf (S (length rho)) e ->
      Forall (wf 0) rho ->
      subst [v] (subst (descend 1 rho) e) =
      subst (v :: rho) e.

  Parameter map_shift_identity_subst_split :
    forall c d n,
      c <= n ->
      map (shift c d) (identity_subst n) =
      identity_subst c ++ SIS (c + d) (n - c).

  Parameter identity_subst_app :
    forall n1 n2,
      identity_subst (n1 + n2) = identity_subst n1 ++ SIS n1 n2.

  Parameter subst_extend_with_identity :
    forall e rho n,
      subst rho e = subst (rho ++ SIS (length rho) n) e.

  Parameter SIS_length :
    forall d n,
      length (SIS d n) = n.

  Parameter wf_SIS : forall d n, Forall (wf (d + n)) (SIS d n).

  Parameter SIS_merge :
    forall n c d1 d2,
      c <= d1 ->
      map (shift c d2) (SIS d1 n) = SIS (d1 + d2) n.

  Parameter SIS_merge_0 :
    forall n d1 d2,
      map (shift 0 d2) (SIS d1 n) = SIS (d1 + d2) n.

  Parameter SIS_0 :
    forall n,
      SIS 0 n = identity_subst n.

  Parameter SIS_app :
    forall n1 n2 d,
      SIS d (n1 + n2) = SIS d n1 ++ SIS (n1 + d) n2.

  Module basis_util.
    Ltac prove_ws_to_abt :=
      intros e; induction e; simpl; intuition.

    Ltac prove_of_to_abt :=
      intros e; induction e; simpl; f_equal; auto.

    Ltac prove_to_of_abt to_abt of_abt :=
      intros a;
      induction a using rect'
      with (Pb :=
              (fun b => forall v, ws_binder v b ->
                match b with
                | bind _ a => to_abt (of_abt a) = a
                end)) ; simpl; intros; f_equal; intuition;
        fold ws_binders in *;
        repeat break_match; subst; simpl in *; intuition;
        repeat match goal with
               | [ H : Forall _ (_ :: _) |- _ ] => inversion H; subst; clear H
               end; simpl in *; try lia;
          repeat f_equal; eauto.

    Ltac prove_t_map_to_abt_comm :=
      intros ov e; induction e; simpl; intros c; auto; repeat f_equal; auto.

    Ltac prove_shift_to_abt_comm :=
      intros e; induction e; simpl; intros c d; auto; repeat f_equal; auto.

    Ltac prove_map_shift_to_abt_comm stac :=
      intros; rewrite !map_map; now erewrite map_ext by (intros; apply stac).

    Ltac prove_subst_to_abt_comm t mstac :=
      unfold t;
      intros e; induction e; simpl; intros rho; rewrite ?descend_0, ?descend_1, ?descend_2;
      repeat match goal with
      | [ IH : forall _, _ = _ |- _ ] => rewrite IH; clear IH
      end;
      simpl; repeat f_equal;
      auto using mstac;
      try (rewrite nth_error_map; break_match; auto).

    Ltac prove_wf_to_abt :=
      intros e; induction e; simpl; firstorder.

    Ltac prove_identity_subst_to_abt_comm mstac :=
      intros n; induction n; simpl; f_equal; auto;
      now match goal with
          | [ H : _ = _ |- _ ] => rewrite mstac, H
          end.

  End basis_util.
End ABT.

Module abt (O_ : OPERATOR) : ABT with Module O := O_.
  Module O := O_.
  Local Unset Elimination Schemes.
  Inductive t : Type :=
  | var (x : nat) : t
  | op : O.t -> list binder -> t
  with
  binder :=
  | bind (v : valence.t) : t -> binder.

  Section rect.
    Variable P : t -> Type.
    Variable Pb : binder -> Type.
    Variable Pbl : list binder -> Type.

    Hypotheses Pvar : forall x, P (var x).
    Hypothesis Pop : forall o bs, Pbl bs -> P (op o bs).
    Hypothesis Pbind : forall s e, P e -> Pb (bind s e).
    Hypothesis Pblnil : Pbl [].
    Hypothesis Pblcons : forall b bs, Pb b -> Pbl bs -> Pbl (b :: bs).

    Fixpoint rect (e : t) : P e :=
      let fix rect_list (l : list binder) : Pbl l :=
          match l with
          | [] => Pblnil
          | b :: bs => Pblcons (rect_binder b) (rect_list bs)
          end
      in
      match e with
      | var x => Pvar x
      | op o bs => Pop o (rect_list bs)
      end
    with rect_binder (b : binder) : Pb b :=
      match b with
      | bind s e => Pbind s (rect e)
      end
    .

    Definition rect_list :=
      fix rect_list (l : list binder) : Pbl l :=
          match l with
          | [] => Pblnil
          | b :: bs => Pblcons (rect_binder b) (rect_list bs)
          end.
  End rect.


  Section rect'.
    Variable P : t -> Prop.
    Variable Pb : binder -> Prop.
    Let Pbl (bs : list binder) : Prop := Forall Pb bs.

    Hypotheses Pvar : forall n, P (var n).
    Hypothesis Pop : forall o bs, Pbl bs -> P (op o bs).
    Hypothesis Pbind : forall n e, P e -> Pb (bind n e).

    Definition rect' (e : t) : P e.
      refine (rect P Pb Pbl Pvar Pop Pbind (Forall_nil _) _ e).
      intros. constructor; auto.
    Defined.
  End rect'.

  Fixpoint wf (n : nat) (e : t) :=
    let fix go_list (n : nat) (bs : list binder) :=
        match bs with
        | [] => True
        | b :: bs => wf_binder n b /\ go_list n bs
        end
    in
    match e with
    | var x => x < n
    | op o bs => go_list n bs
    end
  with wf_binder (n : nat) (b : binder) :=
         match b with
         | bind s e => wf (s + n) e
         end.
  Definition wf_binders :=
    fix go_list (n : nat) (bs : list binder) :=
        match bs with
        | [] => True
        | b :: bs => wf_binder n b /\ go_list n bs
        end.

  Fixpoint t_map (onvar : (*c*) nat -> (*x*) nat -> t) (c : nat) (e : t) : t :=
    let fix go_list (onvar : nat -> nat -> t) (c : nat) (bs : list binder) : list binder :=
        match bs with
        | [] => []
        | b :: bs => t_map_binder onvar c b :: go_list onvar c bs
        end
    in
        match e with
        | var x => onvar c x
        | op o bs => op o (go_list onvar c bs)
        end
  with t_map_binder (onvar : nat -> nat -> t) (c : nat) (b : binder) : binder :=
         match b with
         | bind n e => bind n (t_map onvar (n + c) e)
         end
  .
  Definition t_map_binders :=
    fix go_list (onvar : nat -> nat -> t) (c : nat) (bs : list binder) : list binder :=
      match bs with
      | [] => []
      | b :: bs => t_map_binder onvar c b :: go_list onvar c bs
      end.

  Definition shift_onvar d := (fun c x => if x <? c then var x else var (x + d)).
  Definition shift_via_t_map (c d : nat) (e : t) : t :=
    t_map (shift_onvar d) c e.
  Definition shift_binder_via_t_map (c d : nat) (b : binder) : binder :=
    t_map_binder (shift_onvar d) c b.
  Definition shift_binders_via_t_map (c d : nat) (bs : list binder) : list binder :=
    t_map_binders (shift_onvar d) c bs.

  Fixpoint shift (c d : nat) (e : t) : t :=
    let fix go_list (c d : nat) (bs : list binder) : list binder :=
        match bs with
        | [] => []
        | b :: bs => shift_binder c d b :: go_list c d bs
        end
    in
        match e with
        | var x => var (if x <? c then x else x + d)
        | op o bs => op o (go_list c d bs)
        end
  with shift_binder (c d : nat) (b : binder) : binder :=
         match b with
         | bind n e => bind n (shift (n + c) d e)
         end
  .
  Definition shift_binders :=
    fix go_list (c d : nat) (bs : list binder) : list binder :=
        match bs with
        | [] => []
        | b :: bs => shift_binder c d b :: go_list c d bs
        end.


  Lemma shift_via_t_map_is_shift :
    forall d e c,
      shift_via_t_map c d e = shift c d e.
  Proof.
    intros d.
    induction e using rect
      with (Pb := fun b => forall c, shift_binder_via_t_map c d b = shift_binder c d b)
           (Pbl := fun bs => forall c, shift_binders_via_t_map c d bs = shift_binders c d bs);
      intros c.
    - cbn -[Nat.ltb]. unfold shift_onvar.
      destruct (_ <? _); reflexivity.
    - cbn. now rewrite <- IHe.
    - cbn. now rewrite <- IHe.
    - reflexivity.
    - cbn. now rewrite <- IHe, <- IHe0.
  Qed.

  Lemma t_map_bump :
    forall ov d e c,
      t_map ov (c + d) e = t_map (fun c x => ov (c + d) x) c e.
  Proof.
    intros ov d.
    induction e using rect
      with (Pb := fun b => forall c : nat,
                      t_map_binder ov (c + d) b =
                      t_map_binder (fun c x : nat => ov (c + d) x) c b)
           (Pbl := fun bs => forall c : nat,
                       t_map_binders ov (c + d) bs =
                       t_map_binders (fun c x => ov (c + d) x) c bs);
      intros; cbn.
    - reflexivity.
    - fold t_map_binders. f_equal. auto.
    - f_equal. rewrite <- IHe. f_equal. lia.
    - reflexivity.
    - f_equal; auto.
  Qed.

  Lemma t_map_ext :
    forall ov ov',
      (forall c x, ov c x = ov' c x) ->
      forall e c,
        t_map ov c e = t_map ov' c e.
  Proof.
    intros ov ov' Ext.
    induction e using rect
      with (Pb := fun b => forall c : nat, t_map_binder ov c b = t_map_binder ov' c b)
           (Pbl := fun bs => forall c : nat, t_map_binders ov c bs = t_map_binders ov' c bs);
      intros c; cbn; auto.
    - fold t_map_binders. f_equal. auto.
    - f_equal. auto.
    - f_equal; auto.
  Qed.

  Lemma t_map_t_map :
    forall ov1 ov2 e c1 c2,
      t_map ov2 c2 (t_map ov1 c1 e) =
      t_map (fun c x => t_map ov2 (c + c2 - c1) (ov1 c x)) c1 e.
  Proof.
    intros ov1 ov2.
    induction e using rect
      with (Pb := fun b => forall c1 c2 : nat,
                      t_map_binder ov2 c2 (t_map_binder ov1 c1 b) =
                      t_map_binder (fun c x => t_map ov2 (c + c2 - c1) (ov1 c x)) c1 b)
           (Pbl := fun bs => forall c1 c2 : nat,
                       t_map_binders ov2 c2 (t_map_binders ov1 c1 bs) =
                       t_map_binders (fun c x => t_map ov2 (c + c2 - c1) (ov1 c x)) c1 bs);
      intros c1 c2; cbn; auto.
    - f_equal. lia.
    - fold t_map_binders. f_equal. auto.
    - f_equal. rewrite IHe. apply t_map_ext. clear.
      intros c x. f_equal. lia.
    - f_equal; auto.
  Qed.

  Fixpoint identity_subst (n : nat) : list t :=
    match n with
    | 0 => []
    | S n => var 0 :: map (shift 0 1) (identity_subst n)
    end.
  Definition SIS d n := (map (shift 0 d) (identity_subst n)).

  Lemma identity_subst_length : forall n, length (identity_subst n) = n.
  Proof.
    induction n; simpl.
    - auto.
    - rewrite map_length. auto using f_equal.
  Qed.
  Hint Rewrite identity_subst_length : list.

  Definition descend (n : nat) (rho : list t) : list t :=
    (identity_subst n ++ map (shift 0 n) rho).

  Lemma descend_length :
    forall n rho,
      length (descend n rho) = n + length rho.
  Proof.
    intros.
    unfold descend.
    now rewrite app_length, map_length, identity_subst_length.
  Qed.

  Fixpoint subst (rho : list t) (e : t) : t :=
    let fix go_list (rho : list t) (bs : list binder) : list binder :=
        match bs with
        | [] => []
        | b :: bs => subst_binder rho b :: go_list rho bs
        end
    in
    match e with
    | var x => match nth_error rho x with
              | Some e' => e'
              | None => e
              end
    | op o bs => op o (go_list rho bs)
    end
  with subst_binder (rho : list t) (b : binder) : binder :=
         match b with
         | bind n e => bind n (subst (descend n rho) e)
         end
  .
  Definition subst_binders :=
    fix go_list (rho : list t) (bs : list binder) : list binder :=
        match bs with
        | [] => []
        | b :: bs => subst_binder rho b :: go_list rho bs
        end.

(*
  Lemma shift_shift :
    forall e c1 d1 c2 d2,
      c2 <= c1 ->
      shift c2 d2 (shift c1 d1 e) =
      shift (c1 + d2) d1 (shift c2 d2 e).
  Proof.
    intros e c1 d1 c2 d2.
    rewrite <- !shift_via_t_map_is_shift.
    unfold shift_via_t_map.
    rewrite !t_map_t_map.
*)


  Lemma shift_shift :
    forall e c1 d1 c2 d2,
      c2 <= c1 ->
      shift c2 d2 (shift c1 d1 e) =
      shift (c1 + d2) d1 (shift c2 d2 e).
  Proof.
    induction e using rect
    with (Pb := fun b =>
             forall c1 d1 c2 d2,
               c2 <= c1 ->
               shift_binder c2 d2 (shift_binder c1 d1 b) =
               shift_binder (c1 + d2) d1 (shift_binder c2 d2 b))
         (Pbl := fun bs =>
             forall c1 d1 c2 d2,
               c2 <= c1 ->
               shift_binders c2 d2 (shift_binders c1 d1 bs) =
               shift_binders (c1 + d2) d1 (shift_binders c2 d2 bs));
      intros c1 d1 c2 d2 LE; simpl; f_equal; auto.
    - repeat do_ltb; lia.
    - simpl.
      rewrite IHe by lia.
      f_equal.
      lia.
  Qed.

  Lemma shift_inj :
    forall e1 e2 c d,
      shift c d e1 = shift c d e2 ->
      e1 = e2.
  Proof.
    induction e1 using rect
    with (Pb := fun b1 =>
             forall b2 c d,
               shift_binder c d b1 = shift_binder c d b2 ->
               b1 = b2)
         (Pbl := fun bs1 =>
             forall bs2 c d,
               shift_binders c d bs1 = shift_binders c d bs2 ->
               bs1 = bs2);
      intros [] c d EQ; try invc EQ; f_equal; eauto.
    - destruct (Nat.ltb_spec x c) in *;
      destruct (Nat.ltb_spec x0 c) in *; lia.
  Qed.

  Lemma shift_nop :
    forall e c d n,
      n <= c ->
      wf n e ->
      shift c d e = e.
  Proof.
    induction e using rect
    with (Pb := fun b =>
                  forall c d n,
                    n <= c ->
                    wf_binder n b ->
                    shift_binder c d b = b)
           (Pbl := fun bs =>
                     forall c d n,
                       n <= c ->
                       wf_binders n bs ->
                       shift_binders c d bs = bs);
      simpl; intros c d n LE WF; f_equal; intuition eauto.
    - destruct (Nat.ltb_spec x c); auto.
      lia.
    - eapply IHe; try eassumption. lia.
  Qed.

  Lemma shift_nop' :
    forall e c d,
      wf c e ->
      shift c d e = e.
  Proof.
    intros.
    eapply shift_nop; eauto.
  Qed.

  Lemma shift_shift' :
    forall c d e,
      shift 0 1 (shift c d e) = shift (S c) d (shift 0 1 e).
  Proof.
    intros c d e.
    rewrite shift_shift with (c2 := 0) by lia.
    f_equal. lia.
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

  Lemma shift_identity_subst :
    forall n c d,
      n <= c ->
      map (shift c d) (identity_subst n) = identity_subst n.
  Proof.
    induction n; simpl; intros c d LE.
    - reflexivity.
    - f_equal.
      + destruct (Nat.ltb_spec 0 c); auto.
        lia.
      + destruct c; [lia|].
        rewrite <- IHn with (c := c) (d := d) at 2 by lia.
        auto using map_shift_map_shift'.
  Qed.

  Lemma descend_shift :
    forall n rho c d,
      descend n (map (shift c d) rho) =
      map (shift (n + c) d) (descend n rho).
  Proof.
    unfold descend.
    intros.
    rewrite map_app.
    f_equal.
    - now rewrite shift_identity_subst by lia.
    - rewrite !map_map.
      apply map_ext.
      intros e.
      rewrite shift_shift by lia.
      f_equal.
      lia.
  Qed.

  Hint Rewrite app_length nth_error_map : list.
  Hint Rewrite map_app app_ass : list.

  Lemma descend_app :
    forall s rho1 rho2,
      descend s (rho1 ++ rho2) = descend s rho1 ++ map (shift 0 s) rho2.
  Proof.
    intros.
    unfold descend.
    now autorewrite with list.
  Qed.

  Hint Rewrite descend_app descend_length : list.

  Lemma shift_subst :
    forall e c d rho,
      wf (List.length rho) e ->
      shift c d (subst rho e) =
      subst (List.map (shift c d) rho) e.
  Proof.
    induction e using rect
    with (Pb := fun b =>
             forall c d rho,
               wf_binder (List.length rho) b ->
               shift_binder c d (subst_binder rho b) =
               subst_binder (List.map (shift c d) rho) b)
         (Pbl := fun bs =>
             forall c d rho,
               wf_binders (List.length rho) bs ->
               shift_binders c d (subst_binders rho bs) =
               subst_binders (List.map (shift c d) rho) bs);
      simpl; intros c d rho WF; f_equal; intuition; autorewrite with list in *.
    - break_match; auto.
      do_nth_error_Some.
      intuition lia.
    - rewrite IHe by now rewrite descend_length.
      f_equal.
      now rewrite descend_shift.
  Qed.


  Lemma subst_shift :
    forall e rho1 rho2 rho3,
      wf (List.length (rho1 ++ rho3)) e ->
      subst (rho1 ++ rho2 ++ rho3) (shift (List.length rho1) (List.length rho2) e) =
      subst (rho1 ++ rho3) e.
  Proof.
    induction e using rect
    with (Pb := fun b =>
         forall rho1 rho2 rho3,
           wf_binder (List.length (rho1 ++ rho3)) b ->
           subst_binder (rho1 ++ rho2 ++ rho3)
                        (shift_binder (List.length rho1) (List.length rho2) b) =
           subst_binder (rho1 ++ rho3) b)
         (Pbl := fun bs =>
         forall rho1 rho2 rho3,
           wf_binders (List.length (rho1 ++ rho3)) bs ->
           subst_binders (rho1 ++ rho2 ++ rho3)
                         (shift_binders (List.length rho1) (List.length rho2) bs) =
           subst_binders (rho1 ++ rho3) bs);
      simpl; intros rho1 rho2 rho3 WF; fold subst_binders shift_binders wf_binders in *;
        f_equal; intuition.
    - rewrite nth_error_shift.
      do_nth_error_Some.
      break_match; auto.
      intuition.
    - autorewrite with list in *.
      erewrite <- IHe.
      now f_equal; autorewrite with list.
      now autorewrite with list; rewrite plus_assoc in *.
  Qed.

  Lemma subst_shift' :
    forall e rho1 rho2,
      wf (List.length rho2) e ->
      subst (rho1 ++ rho2) (shift 0 (List.length rho1) e) =
      subst rho2 e.
  Proof.
    intros.
    now apply subst_shift with (rho1 := []).
  Qed.

  Lemma shift_nop_d :
    forall e c,
      shift c 0 e = e.
  Proof.
    induction e using rect
    with (Pb := fun b =>
             forall c,
               shift_binder c 0 b = b)
         (Pbl := fun bs =>
             forall c,
               shift_binders c 0 bs = bs);
      simpl; intros c; fold subst_binders shift_binders wf_binders in *;
        f_equal; intuition; autorewrite with list in *.
    repeat do_ltb; lia.
  Qed.

  Lemma shift_merge :
    forall e c1 c2 d1 d2,
      c1 <= c2 ->
      c2 <= c1 + d1  ->
      shift c2 d2 (shift c1 d1 e) = shift c1 (d1 + d2) e.
  Proof.
    induction e using rect
    with (Pb := fun b =>
             forall c1 c2 d1 d2,
               c1 <= c2 ->
               c2 <= c1 + d1  ->
               shift_binder c2 d2 (shift_binder c1 d1 b) = shift_binder c1 (d1 + d2) b)
         (Pbl := fun bs =>
             forall c1 c2 d1 d2,
               c1 <= c2 ->
               c2 <= c1 + d1  ->
               shift_binders c2 d2 (shift_binders c1 d1 bs) = shift_binders c1 (d1 + d2) bs);
      intros c1 c2 d1 d2 LE1 LE2.
    - cbn [shift].
      destruct (Nat.ltb_spec x c1).
      + destruct (Nat.ltb_spec x c2).
        * reflexivity.
        * lia.
      + destruct (Nat.ltb_spec (x + d1) c2).
        * lia.
        * f_equal. lia.
    - cbn [shift]. fold shift_binders.
      now rewrite IHe by assumption.
    - cbn [shift_binder].
      f_equal.
      now rewrite IHe by lia.
    - reflexivity.
    - cbn [shift_binders].
      f_equal; auto.
  Qed.

  Lemma shift_merge' :
    forall e c d1 d2,
      shift c d2 (shift c d1 e) = shift c (d2 + d1) e.
  Proof.
    intros.
    rewrite shift_merge by lia.
    f_equal.
    lia.
  Qed.

  Lemma SIS_merge :
    forall n c d1 d2,
      c <= d1 ->
      map (shift c d2) (SIS d1 n) = SIS (d1 + d2) n.
  Proof.
    unfold SIS.
    intros.
    rewrite !map_map.
    apply map_ext.
    intros e.
    now rewrite shift_merge by lia.
  Qed.

  Lemma SIS_merge_0 :
    forall n d1 d2,
      map (shift 0 d2) (SIS d1 n) = SIS (d1 + d2) n.
  Proof.
    intros n d1 d2.
    apply SIS_merge.
    lia.
  Qed.

  Lemma SIS_unroll :
    forall n d, SIS d (S n) = var d :: SIS (S d) n.
  Proof.
    unfold SIS.
    intros.
    simpl.
    fold (SIS 1 n).
    now rewrite SIS_merge_0.
  Qed.

  Lemma SIS_unroll_r :
    forall n d, SIS d (S n) = SIS d n ++ [var (d + n)].
  Proof.
    induction n; intros.
    - unfold SIS. simpl. do 2 f_equal. lia.
    - rewrite !SIS_unroll with (d := d).
      rewrite IHn.
      simpl.
      repeat f_equal.
      lia.
  Qed.

  Lemma subst_identity_subst :
    forall n rho1 rho2,
      map (subst (rho1 ++ SIS (length rho1) n ++ rho2)) (SIS (length rho1) n) =
      SIS (length rho1) n.
  Proof.
    induction n; simpl; intros rho1 rho2.
    - reflexivity.
    - rewrite SIS_unroll. f_equal.
      + rewrite nth_error_app2 by lia.
        now rewrite minus_diag.
      + fold (SIS 1 n).
        rewrite SIS_merge_0.
        specialize (IHn (rho1 ++ [var (length rho1)]) rho2).
        autorewrite with list in *.
        simpl in *.
        rewrite <- plus_n_Sm, <- plus_n_O in *.
        assumption.
  Qed.

  Lemma SIS_0 :
    forall n,
      SIS 0 n = identity_subst n.
  Proof.
    unfold SIS.
    intros.
    erewrite map_ext.
    now rewrite map_id.
    intros e.
    now rewrite shift_nop_d.
  Qed.

  Lemma descend_subst :
    forall s rho1 rho2,
      Forall (wf (length rho2)) rho1 ->
      descend s (map (subst rho2) rho1) =
      map (subst (descend s rho2)) (descend s rho1).
  Proof.
    intros s rho1 rho2 WF.
    unfold descend.
    autorewrite with list.
    symmetry.
    f_equal.
    - generalize (map (shift 0 s) rho2). clear WF rho1 rho2. intro rho.
      pose proof subst_identity_subst s [] rho.
      simpl in *.
      now rewrite SIS_0 in *.
    - rewrite !map_map.
      apply map_ext_in.
      intros e I.
      assert (wf (length rho2) e) by (eapply Forall_forall; eauto).
      rewrite shift_subst by assumption.
      pose proof subst_shift' e (identity_subst s) (map (shift 0 s) rho2).
      autorewrite with list in *.
      auto.
  Qed.

  Lemma wf_shift :
    forall e c d n,
      wf n e ->
      wf (d + n) (shift c d e).
  Proof.
    induction e using rect
    with (Pb := fun b =>
             forall c d n,
               wf_binder n b ->
               wf_binder (d + n) (shift_binder c d b))
         (Pbl := fun bs =>
             forall c d n,
               wf_binders n bs ->
               wf_binders (d + n) (shift_binders c d bs));
      simpl; intros c d n; fold subst_binders shift_binders wf_binders in *;
        f_equal; intuition; autorewrite with list in *.
    - do_ltb; lia.
    - specialize (IHe (s + c) d (s + n)).
      intuition.
      now rewrite Nat.add_shuffle3.
  Qed.

  Lemma wf_identity_subst :
    forall n,
      Forall (wf n) (identity_subst n).
  Proof.
    induction n; simpl; constructor.
    - simpl. lia.
    - rewrite Forall_map. eapply Forall_impl; [|apply IHn].
      intros e WF.
      now apply wf_shift with (c := 0) (d := 1).
  Qed.

  Lemma wf_weaken :
    forall e n d,
      n <= d ->
      wf n e ->
      wf d e.
  Proof.
    induction e using rect
    with (Pb := fun b =>
             forall n d,
               n <= d ->
               wf_binder n b ->
               wf_binder d b)
         (Pbl := fun bs =>
             forall n d,
               n <= d ->
               wf_binders n bs ->
               wf_binders d bs);
      simpl; intros n d LE WF; fold subst_binders shift_binders wf_binders in *;
        f_equal; intuition; autorewrite with list in *; eauto with arith.
  Qed.

  Lemma descend_wf :
    forall n s rho,
      Forall (wf n) rho ->
      Forall (wf (s + n)) (descend s rho).
  Proof.
    intros n s rho WF.
    unfold descend.
    rewrite Forall_app.
    split.
    - eapply Forall_impl; [|apply wf_identity_subst].
      eauto using wf_weaken with arith.
    - rewrite Forall_map.
      eapply Forall_impl; [|eassumption].
      auto using wf_shift.
  Qed.

  Lemma wf_subst :
    forall e n rho,
      wf (length rho) e ->
      List.Forall (wf n) rho ->
      wf n (subst rho e).
  Proof.
    induction e using rect
    with (Pb := fun b =>
             forall n rho,
               wf_binder (length rho) b ->
               List.Forall (wf n) rho ->
               wf_binder n (subst_binder rho b))
         (Pbl := fun bs =>
             forall n rho,
               wf_binders (length rho) bs ->
               List.Forall (wf n) rho ->
               wf_binders n (subst_binders rho bs));
      simpl; intros c d1 d2; fold subst_binders shift_binders wf_binders in *;
        f_equal; intuition; autorewrite with list in *.
    - break_match.
      + eapply Forall_nth_error; eauto.
      + do_nth_error_Some. intuition.
    - apply IHe.
      + now autorewrite with list.
      + now apply descend_wf.
  Qed.

  Lemma wf_shift_inv :
    forall e c d n,
      wf n (shift c d e) ->
      wf (max c (n - d)) e.
  Proof.
    induction e using rect
    with (Pb := fun b =>
              forall c d n,
                wf_binder n (shift_binder c d b) ->
                wf_binder (max c (n - d)) b)
         (Pbl := fun bs =>
              forall c d n,
                wf_binders n (shift_binders c d bs) ->
                wf_binders (max c (n - d)) bs);
    simpl; intros c d n; fold subst_binders shift_binders wf_binders in *;
        f_equal; intuition; autorewrite with list in *.
    - do_ltb; do_max_spec; lia.
    - apply IHe in H.
      eapply wf_weaken; [|eassumption].
      pose proof Nat.max_spec (s + c) (s + n - d).
      pose proof Nat.max_spec c (n - d).
      lia.
  Qed.

  Lemma wf_subst_inv :
    forall e n rho,
      wf n (subst rho e) ->
      wf (max n (length rho)) e.
  Proof.
    induction e using rect
    with (Pb := fun b =>
                  forall n rho,
                    wf_binder n (subst_binder rho b) ->
                    wf_binder (max n (length rho)) b)
         (Pbl := fun bs =>
                  forall n rho,
                    wf_binders n (subst_binders rho bs) ->
                    wf_binders (max n (length rho)) bs);
      simpl; intros n rho; fold subst_binders shift_binders wf_binders in *;
        f_equal; intuition; autorewrite with list in *.
    - break_match.
      + do_nth_error_Some.
        assert (x < length rho) by (intuition congruence).
        do_max_spec.
        lia.
      + simpl in *.
        do_max_spec.
        lia.
    - apply IHe in H.
      rewrite descend_length in *.
      assert (Init.Nat.max (s + n) (s + length rho) = s + Init.Nat.max n (length rho)).
      do_max_spec.
      pose proof Nat.max_spec n (length rho).
      lia.
      congruence.
  Qed.

  Lemma subst_subst :
    forall e rho1 rho2,
      wf (List.length rho1) e ->
      List.Forall (wf (List.length rho2)) rho1 ->
      subst rho2 (subst rho1 e) =
      subst (List.map (subst rho2) rho1) e.
  Proof.
    induction e using rect
    with (Pb := fun b =>
         forall rho1 rho2,
           wf_binder (List.length rho1) b ->
           List.Forall (wf (List.length rho2)) rho1 ->
           subst_binder rho2 (subst_binder rho1 b) =
           subst_binder (List.map (subst rho2) rho1) b)
         (Pbl := fun bs =>
         forall rho1 rho2,
           wf_binders (List.length rho1) bs ->
           List.Forall (wf (List.length rho2)) rho1 ->
           subst_binders rho2 (subst_binders rho1 bs) =
           subst_binders (List.map (subst rho2) rho1) bs);
      simpl; intros rho1 rho2 rho3 WF; fold subst_binders shift_binders wf_binders in *;
        autorewrite with list in *;
        f_equal; intuition.
    - break_match; auto.
      do_nth_error_Some. intuition.
    - rewrite IHe.
      + f_equal. now rewrite descend_subst.
      + now autorewrite with list.
      + autorewrite with list.
        auto using descend_wf.
  Qed.

  Lemma nth_error_SIS :
    forall n s x y,
      nth_error (SIS s n) x = Some y ->
      y = var (s + x).
  Proof.
    unfold SIS.
    induction n; intros s x y NE; destruct x; simpl in *; try congruence.
    - rewrite Nat.add_0_r. congruence.
    - fold (SIS 1 n) in *. rewrite SIS_merge_0 in *.
      unfold SIS in *.
      apply IHn in NE.
      now rewrite Nat.add_succ_r, Nat.add_1_l, Nat.add_succ_l in *.
  Qed.

  Lemma nth_error_identity_subst :
    forall n x y,
      nth_error (identity_subst n) x = Some y ->
      y = var x.
  Proof.
    intros n x y.
    rewrite <- SIS_0.
    apply nth_error_SIS.
  Qed.

  Lemma identity_subst_unroll_r :
    forall n,
      identity_subst (S n) = identity_subst n ++ [var n].
  Proof.
    intros.
    pose proof SIS_unroll_r n 0.
    now rewrite !SIS_0 in *.
  Qed.

  Lemma descend_identity :
    forall s n,
      descend s (identity_subst n) = identity_subst (s + n).
  Proof.
    unfold descend.
    intros s n.
    rewrite plus_comm.
    revert s.
    induction n; simpl; intros s.
    - now rewrite app_nil_r.
    - fold (SIS 1 n). rewrite SIS_merge_0.
      specialize (IHn (S s)). unfold SIS.
      rewrite identity_subst_unroll_r in *.
      rewrite app_ass in IHn.
      cbn [app] in IHn.
      cbn [plus].
      rewrite IHn.
      now rewrite <- plus_n_Sm.
  Qed.

  Lemma subst_identity :
    forall e n,
      subst (identity_subst n) e = e.
  Proof.
    induction e using rect
    with (Pb := fun b =>
            forall n,
              subst_binder (identity_subst n) b = b)
         (Pbl := fun bs =>
            forall n,
              subst_binders (identity_subst n) bs = bs);
      simpl; intros n; fold subst_binders shift_binders wf_binders in *;
        autorewrite with list in *;
        f_equal; intuition.
    - break_match; auto.
      now apply nth_error_identity_subst in Heqo.
    - rewrite descend_identity. auto.
  Qed.

  Lemma subst_empty :
    forall e,
      subst [] e = e.
  Proof.
    intros e.
    exact (subst_identity e 0).
  Qed.

  Lemma subst_shift_cons :
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
    rewrite subst_shift_cons by auto.
    now rewrite subst_identity with (n := 0).
  Qed.

  Lemma descend_0 :
    forall rho,
      descend 0 rho = rho.
  Proof.
    unfold descend.
    intros.
    simpl.
    erewrite map_ext, map_id; auto.
    simpl.
    intros e.
    now rewrite shift_nop_d.
  Qed.

  Lemma descend_1 :
    forall rho,
      descend 1 rho = var 0 :: map (shift 0 1) rho.
  Proof. reflexivity. Qed.

  Lemma descend_2 :
    forall rho,
      descend 2 rho = var 0 :: var 1 :: map (shift 0 2) rho.
  Proof. reflexivity. Qed.

  Fixpoint ws (e : t) {struct e} :=
    let fix go_list (a : arity.t) (bs : list binder) {struct bs} :=
        match a, bs with
        | [], [] => True
        | v :: a, b :: bs => ws_binder v b /\ go_list a bs
        | _, _ => False
        end
    in
    match e with
    | var n => True
    | op o bs => go_list (O.arity o) bs
    end
  with
  ws_binder (v : valence.t) (b : binder) {struct b} :=
    match b with
    | bind v' e => v = v' /\ ws e
    end.
  Definition ws_binders :=
    fix go_list (a : arity.t) (bs : list binder) {struct bs} :=
        match a, bs with
        | [], [] => True
        | v :: a, b :: bs => ws_binder v b /\ go_list a bs
        | _, _ => False
        end.

  Lemma ws_var : forall n, ws (var n).
  Proof. simpl. intuition. Qed.

  Lemma ws_op : forall o bs, Forall2 ws_binder (O.arity o) bs -> ws (op o bs).
  Proof.
    simpl.
    fold ws_binders.
    intros o bs.
    generalize (O.arity o). clear o.
    intros a.
    induction 1; simpl; intuition.
  Qed.

  Lemma ws_binder_bind : forall v e, ws e -> ws_binder v (bind v e).
  Proof. simpl. intuition. Qed.

  Lemma ws_shift :
    forall e c d,
      ws e ->
      ws (shift c d e).
  Proof.
    induction e using rect
    with (Pb := fun b => forall v c d, ws_binder v b ->
                               ws_binder v (shift_binder c d b))
           (Pbl := fun bs => forall a c d , ws_binders a bs ->
                                    ws_binders a (shift_binders c d bs));
      simpl; intros rho; fold shift_binders ws_binders in *;
        autorewrite with list in *;
        f_equal; intuition.
    break_match; intuition.
  Qed.

  Lemma ws_SIS :
    forall n d,
      Forall ws (SIS d n).
  Proof.
    unfold SIS.
    induction n; simpl; intros d; constructor.
    - exact I.
    - rewrite map_map.
      erewrite map_ext.
      apply (IHn (S d)).
      intros e.
      rewrite shift_merge'.
      f_equal.
      lia.
  Qed.

  Lemma ws_identity_subst :
    forall n,
      Forall ws (identity_subst n).
  Proof.
    intros n.
    rewrite <- SIS_0.
    apply ws_SIS.
  Qed.

  Lemma ws_descend :
    forall s rho,
      Forall ws rho ->
      Forall ws (descend s rho).
  Proof.
    unfold descend.
    intros s rho F.
    rewrite Forall_app.
    split.
    - auto using ws_identity_subst.
    - rewrite Forall_map.
      eapply Forall_impl; try eassumption.
      auto using ws_shift.
  Qed.

  Lemma ws_subst :
    forall e rho,
      ws e ->
      Forall ws rho ->
      ws (subst rho e).
  Proof.
    induction e using rect
    with (Pb := fun b => forall rho v, ws_binder v b -> Forall ws rho ->
                               ws_binder v (subst_binder rho b))
         (Pbl := fun bs => forall rho a , ws_binders a bs -> Forall ws rho ->
                                 ws_binders a (subst_binders rho bs));
      simpl; intros rho; fold subst_binders ws_binders in *;
        autorewrite with list in *;
        f_equal; intuition.
    - break_match.
      + eapply Forall_nth_error; eauto.
      + do_nth_error_Some.
        intuition.
    - apply IHe; auto.
      auto using ws_descend.
    - break_match; intuition.
  Qed.

  Lemma map_subst_SIS :
    forall rho1 rho2,
      map (subst (rho1 ++ rho2)) (SIS (length rho1) (length rho2)) = rho2.
  Proof.
    unfold SIS.
    intros rho1 rho2. revert rho1.
    induction rho2; simpl; intros rho1.
    - reflexivity.
    - f_equal.
      + rewrite nth_error_app2 by lia.
        now rewrite Nat.sub_diag.
      + fold (SIS 1 (length rho2)). rewrite SIS_merge_0. unfold SIS.
        specialize (IHrho2 (rho1 ++ [a])).
        autorewrite with list in *.
        simpl in *.
        now rewrite Nat.add_1_r in *.
  Qed.

  Lemma map_subst_identity_subst :
    forall rho,
      map (subst rho) (identity_subst (length rho)) = rho.
  Proof.
    intros rho.
    pose proof map_subst_SIS [] rho.
    simpl in *.
    now rewrite SIS_0 in *.
  Qed.

  Lemma subst_extend_with_identity :
    forall e rho n,
      subst rho e = subst (rho ++ SIS (length rho) n) e.
  Proof.
    induction e using rect
    with (Pb := fun b =>
                  forall rho n,
                    subst_binder rho b = subst_binder (rho ++ SIS (length rho) n) b)
         (Pbl := fun bs =>
                   forall rho n,
                     subst_binders rho bs = subst_binders (rho ++ SIS (length rho) n) bs);
      intros rho n; simpl; fold subst_binders; f_equal; auto.
    - do_nth_error_Some; break_match.
      + rewrite nth_error_app1 by (apply H; congruence).
        now rewrite Heqo.
      + intuition.
        assert (length rho <= x) by (apply not_lt; intro; auto with * ).
        rewrite nth_error_app2 by assumption.
        break_match; auto.
        apply nth_error_SIS in Heqo0.
        subst. f_equal.
        lia.
    - rewrite IHe with (n := n).
      rewrite descend_app, descend_length, SIS_merge_0.
      now rewrite plus_comm.
  Qed.

  Lemma subst_shift_id :
    forall rho e,
      wf 0 e ->
      subst rho (shift 0 (length rho) e) = e.
  Proof.
    intros rho e WF.
    pose proof subst_shift' e rho [] WF.
    rewrite app_nil_r in *.
    now rewrite subst_identity with (n := 0) in *.
  Qed.

  Lemma subst_descend :
    forall rho1 rho2,
      Forall (wf 0) rho2 ->
      map (subst rho1) (descend (length rho1) rho2) = rho1 ++ rho2.
  Proof.
    intros rho1 rho2 F.
    unfold descend.
    autorewrite with list.
    f_equal.
    + now rewrite map_subst_identity_subst.
    + rewrite map_map.
      erewrite map_ext_in, map_id; auto.
      intros ty I.
      rewrite subst_shift_id; auto.
      eapply Forall_forall; eauto.
  Qed.

  Lemma subst_subst_descend :
    forall e rho1 rho2,
      wf (length (rho1 ++ rho2)) e ->
      Forall (wf 0) rho2 ->
      subst rho1 (subst (descend (length rho1) rho2) e) =
      subst (rho1 ++ rho2) e.
  Proof.
    intros e rho1 rho2 WF F.
    rewrite subst_subst, subst_descend; auto.
    - now rewrite descend_length, app_length in *.
    - apply descend_wf with (s := (length rho1)) in F.
      now rewrite Nat.add_0_r in *.
  Qed.

  Lemma subst_cons :
    forall e v rho,
      wf (S (length rho)) e ->
      Forall (wf 0) rho ->
      subst [v] (subst (descend 1 rho) e) =
      subst (v :: rho) e.
  Proof.
    intros e v rho WF F.
    apply subst_subst_descend with (rho1 := [v]); auto.
  Qed.

  Lemma map_shift_SIS_big_c :
    forall n d1 d2 c,
      c <= d1 ->
      map (shift c d2) (SIS d1 n) =
      SIS (d1 + d2) n.
  Proof.
    induction n; intros d1 d2 c LE.
    - reflexivity.
    - rewrite !SIS_unroll.
      cbn [map].
      f_equal.
      + simpl.
        destruct (Nat.ltb_spec d1 c); [lia|reflexivity].
      + rewrite IHn by lia.
        reflexivity.
  Qed.

  Lemma map_shift_SIS_split :
    forall n d1 d2 c,
      c <= n + d1 ->
      map (shift c d2) (SIS d1 n) =
      SIS d1 (c - d1) ++ SIS (d1 + (c - d1) + d2) (n - (c - d1)).
  Proof.
    induction n; intros d1 d2 c LE.
    - replace (c - d1) with 0 by lia.
      reflexivity.
    - rewrite SIS_unroll.
      cbn[map].
      cbn[shift].
      destruct (Nat.ltb_spec d1 c).
      + destruct c as [|c]; [lia|].
        rewrite Nat.sub_succ_l by lia.
        cbn[Nat.sub].
        rewrite SIS_unroll.
        cbn[app].
        f_equal.
        rewrite IHn by lia.
        simpl.
        repeat f_equal.
        lia.
      + rewrite map_shift_SIS_big_c by lia.
        replace (c - d1) with 0 by lia.
        rewrite <- SIS_unroll.
        simpl.
        f_equal.
        lia.
  Qed.

  Lemma map_shift_identity_subst_split :
    forall c d n,
      c <= n ->
      map (shift c d) (identity_subst n) =
      identity_subst c ++ SIS (c + d) (n - c).
  Proof.
    intros c d n LE.
    pose proof (@map_shift_SIS_split n 0 d c) as H.
    rewrite Nat.sub_0_r in *.
    rewrite !SIS_0 in *.
    rewrite H by lia.
    f_equal.
  Qed.

  Lemma SIS_app :
    forall n1 n2 d,
      SIS d (n1 + n2) = SIS d n1 ++ SIS (n1 + d) n2.
  Proof.
    induction n1; intros n2 d.
    - reflexivity.
    - cbn[plus].
      rewrite !SIS_unroll.
      cbn[app].
      f_equal.
      rewrite IHn1.
      f_equal.
      f_equal.
      f_equal.
      lia.
  Qed.

  Lemma identity_subst_app :
    forall n1 n2,
      identity_subst (n1 + n2) = identity_subst n1 ++ map (shift 0 n1) (identity_subst n2).
  Proof.
    intros.
    pose proof SIS_app n1 n2 0 as H.
    rewrite !SIS_0 in *.
    now rewrite Nat.add_0_r in *.
  Qed.

  Lemma SIS_length :
    forall d n,
      length (SIS d n) = n.
  Proof.
    intros d n.
    unfold SIS.
    now rewrite map_length, identity_subst_length.
  Qed.

  Lemma wf_SIS : forall d n, Forall (wf (d + n)) (SIS d n).
  Proof.
    intros d n.
    unfold SIS.
    rewrite Forall_map.
    eapply Forall_impl; [| apply wf_identity_subst].
    auto using wf_shift.
  Qed.

  Module basis_util.
  End basis_util.
End abt.
