From mm Require Import util abt abtutil.
Set Implicit Arguments.

Module type.
  Inductive t :=
  | lolli : t -> t -> t
  | tensor : t -> t -> t
  | ichoose : t -> t -> t
  | uchoose : t -> t -> t
  | one : t
  .
End type.

Module expr.
  Module op.
    Inductive t' :=
    | abs
    | app
    | both
    | let_pair
    | oneof
    | fst
    | snd
    | inl
    | inr
    | case
    | tt
    | let_tt
    .
    Definition t := t'.

    Definition arity (op : t) : arity.t :=
      match op with
      | abs => [1]
      | app => [0; 0]
      | both => [0; 0]
      | let_pair => [0; 2]
      | oneof => [0; 0]
      | fst => [0]
      | snd => [0]
      | inl => [0]
      | inr => [0]
      | case => [0; 1; 1]
      | tt => []
      | let_tt => [0; 0]
      end.

    Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
      decide equality.
    Defined.
  End op.

  Module abt := abt.abt op.

  Module ast.
    Inductive t :=
    | var (x : nat)
    | abs : t -> t
    | app : t -> t -> t
    | both : t -> t -> t
    | let_pair : t -> t -> t
    | oneof : t -> t -> t
    | fst : t -> t
    | snd : t -> t
    | inl : t -> t
    | inr : t -> t
    | case : t -> t -> t -> t
    | tt : t
    | let_tt : t -> t -> t
    .
  End ast.

  Module basis.
    Module A := abt.

    Definition t := ast.t.

    Fixpoint to_abt (e : ast.t) : A.t :=
      match e with
      | ast.var n => A.var n
      | ast.abs e' => A.op op.abs [A.bind 1 (to_abt e')]
      | ast.app e1 e2 => A.op op.app [A.bind 0 (to_abt e1); A.bind 0 (to_abt e2)]
      | ast.both e1 e2 => A.op op.both [A.bind 0 (to_abt e1); A.bind 0 (to_abt e2)]
      | ast.let_pair e1 e2 => A.op op.let_pair [A.bind 0 (to_abt e1); A.bind 2 (to_abt e2)]
      | ast.oneof e1 e2 => A.op op.oneof [A.bind 0 (to_abt e1); A.bind 0 (to_abt e2)]
      | ast.fst e' => A.op op.fst [A.bind 0 (to_abt e')]
      | ast.snd e' => A.op op.snd [A.bind 0 (to_abt e')]
      | ast.inl e' => A.op op.inl [A.bind 0 (to_abt e')]
      | ast.inr e' => A.op op.inr [A.bind 0 (to_abt e')]
      | ast.case e1 e2 e3 => A.op op.case [A.bind 0 (to_abt e1);
                                          A.bind 1 (to_abt e2);
                                          A.bind 1 (to_abt e3)]
      | ast.tt => A.op op.tt []
      | ast.let_tt e1 e2 => A.op op.let_tt [A.bind 0 (to_abt e1); A.bind 0 (to_abt e2)]
      end.

    Fixpoint of_abt (a : A.t) : t :=
      match a with
      | A.var n => ast.var n
      | A.op op.abs [A.bind 1 a'] => ast.abs (of_abt a')
      | A.op op.app [A.bind 0 a1; A.bind 0 a2] => ast.app (of_abt a1) (of_abt a2)
      | A.op op.both [A.bind 0 a1; A.bind 0 a2] => ast.both (of_abt a1) (of_abt a2)
      | A.op op.let_pair [A.bind 0 a1; A.bind 2 a2] => ast.let_pair (of_abt a1) (of_abt a2)
      | A.op op.oneof [A.bind 0 a1; A.bind 0 a2] => ast.oneof (of_abt a1) (of_abt a2)
      | A.op op.fst [A.bind 0 a'] => ast.fst (of_abt a')
      | A.op op.snd [A.bind 0 a'] => ast.snd (of_abt a')
      | A.op op.inl [A.bind 0 a'] => ast.inl (of_abt a')
      | A.op op.inr [A.bind 0 a'] => ast.inr (of_abt a')
      | A.op op.case [A.bind 0 a1; A.bind 1 a2; A.bind 1 a3] =>
        ast.case (of_abt a1) (of_abt a2) (of_abt a3)
      | A.op op.tt [] => ast.tt
      | A.op op.let_tt [A.bind 0 a1; A.bind 0 a2] => ast.let_tt (of_abt a1) (of_abt a2)
      | _ => ast.var 0 (* bogus *)
      end.

    Fixpoint shift c d (e : t) : t :=
      match e with
      | ast.var x => ast.var (if x <? c then x else x + d)
      | ast.abs e' => ast.abs (shift (S c) d e')
      | ast.app e1 e2 => ast.app (shift c d e1) (shift c d e2)
      | ast.both e1 e2 => ast.both (shift c d e1) (shift c d e2)
      | ast.let_pair e1 e2 => ast.let_pair (shift c d e1) (shift (S (S c)) d e2)
      | ast.oneof e1 e2 => ast.oneof (shift c d e1) (shift c d e2)
      | ast.fst e' => ast.fst (shift c d e')
      | ast.snd e' => ast.snd (shift c d e')
      | ast.inl e' => ast.inl (shift c d e')
      | ast.inr e' => ast.inr (shift c d e')
      | ast.case e1 e2 e3 => ast.case (shift c d e1) (shift (S c) d e2) (shift (S c) d e3)
      | ast.tt => ast.tt
      | ast.let_tt e1 e2 => ast.let_tt (shift c d e1) (shift c d e2)
      end.

    Fixpoint subst rho e :=
      match e with
      | ast.var x => match nth_error rho x with
                    | Some e' => e'
                    | None => e
                    end
      | ast.abs e' => ast.abs (subst (ast.var 0 :: map (shift 0 1) rho) e')
      | ast.app e1 e2 => ast.app (subst rho e1) (subst rho e2)
      | ast.both e1 e2 => ast.both (subst rho e1) (subst rho e2)
      | ast.let_pair e1 e2 => ast.let_pair (subst rho e1)
                                          (subst (ast.var 0 :: ast.var 1 :: map (shift 0 2) rho)
                                                 e2)
      | ast.oneof e1 e2 => ast.oneof (subst rho e1) (subst rho e2)
      | ast.fst e' => ast.fst (subst rho e')
      | ast.snd e' => ast.snd (subst rho e')
      | ast.inl e' => ast.inl (subst rho e')
      | ast.inr e' => ast.inr (subst rho e')
      | ast.case e1 e2 e3 => ast.case (subst rho e1)
                                     (subst (ast.var 0 :: map (shift 0 1) rho) e2)
                                     (subst (ast.var 0 :: map (shift 0 1) rho) e3)

      | ast.tt => ast.tt
      | ast.let_tt e1 e2 => ast.let_tt (subst rho e1) (subst rho e2)
      end.

    Fixpoint wf n e :=
      match e with
      | ast.var x => x < n
      | ast.abs e' => wf (S n) e'
      | ast.app e1 e2 => wf n e1 /\ wf n e2
      | ast.both e1 e2 => wf n e1 /\ wf n e2
      | ast.let_pair e1 e2 => wf n e1 /\ wf (S (S n)) e2
      | ast.oneof e1 e2 => wf n e1 /\ wf n e2
      | ast.fst e' => wf n e'
      | ast.snd e' => wf n e'
      | ast.inl e' => wf n e'
      | ast.inr e' => wf n e'
      | ast.case e1 e2 e3 => wf n e1 /\ wf (S n) e2 /\ wf (S n) e3
      | ast.tt => True
      | ast.let_tt e1 e2 => wf n e1 /\ wf n e2
      end.

    Fixpoint identity_subst (n : nat) : list t :=
      match n with
      | 0 => []
      | S n => ast.var 0 :: map (shift 0 1) (identity_subst n)
      end.

    Lemma ws_to_abt : forall e, abt.ws (to_abt e).
    Proof. abt.basis_util.prove_ws_to_abt. Qed.

    Lemma of_to_abt : forall e, of_abt (to_abt e) = e.
    Proof. abt.basis_util.prove_of_to_abt. Qed.

    Lemma to_of_abt : forall a, abt.ws a -> to_abt (of_abt a) = a.
    Proof. abt.basis_util.prove_to_of_abt to_abt of_abt. Qed.

    Lemma shift_to_abt_comm : forall e c d, to_abt (shift c d e) = abt.shift c d (to_abt e).
    Proof. abt.basis_util.prove_shift_to_abt_comm. Qed.

    Lemma map_shift_to_abt_comm :
      forall c d rho, map to_abt (map (shift c d) rho) = map (abt.shift c d) (map to_abt rho).
    Proof. abt.basis_util.prove_map_shift_to_abt_comm shift_to_abt_comm. Qed.

    Lemma subst_to_abt_comm : forall e rho,
        to_abt (subst rho e) = abt.subst (map to_abt rho) (to_abt e).
    Proof. abt.basis_util.prove_subst_to_abt_comm t map_shift_to_abt_comm. Qed.

    Lemma wf_to_abt : forall e n, wf n e <-> abt.wf n (to_abt e).
    Proof. abt.basis_util.prove_wf_to_abt. Qed.

    Lemma identity_subst_to_abt_comm :
      forall n, List.map to_abt (identity_subst n) = abt.identity_subst n.
    Proof. abt.basis_util.prove_identity_subst_to_abt_comm map_shift_to_abt_comm. Qed.

    Definition var := ast.var.
    Arguments var /.
    Lemma var_to_abt : forall n, to_abt (var n) = abt.var n.
    Proof. reflexivity. Qed.
  End basis.

  Include abt_util basis.

  Notation abs := ast.abs.
  Notation app := ast.app.
  Notation both := ast.both.
  Notation let_pair := ast.let_pair.
  Notation oneof := ast.oneof.
  Notation fst := ast.fst.
  Notation snd := ast.snd.
  Notation inl := ast.inl.
  Notation inr := ast.inr.
  Notation case := ast.case.
  Notation tt := ast.tt.
  Notation let_tt := ast.let_tt.

End expr.

Definition join_one (oty1 oty2 : option type.t) : option (option type.t) :=
  match oty1, oty2 with
  | None, None => Some None
  | Some ty1, None => Some (Some ty1)
  | None, Some ty2 => Some (Some ty2)
  | _, _ => None
  end.

Lemma join_one_comm :
  forall l1 l2,
    join_one l1 l2 = join_one l2 l1.
Proof.
  unfold join_one.
  intros.
  repeat break_match; auto.
Qed.

Lemma join_one_assoc :
  forall a1 a2 b,
    match join_one a1 b with
    | Some b' => join_one a2 b'
    | None => None
    end = match join_one a2 b with
          | Some b' => join_one a1 b'
          | None => None
          end.
Proof.
  unfold join_one.
  intros.
  repeat break_match; congruence.
Qed.

Definition join G1 G2 := partial_zip.f join_one G1 G2.
Hint Opaque join.

Lemma join_nil :
  join [] [] = Some [].
Proof.
  apply partial_zip.nil.
Qed.
Hint Resolve join_nil.

Lemma join_nil_inv :
  forall G1 G2,
    join G1 G2 = Some [] ->
    G1 = [] /\ G2 = [].
Proof.
  apply partial_zip.nil_inv.
Qed.

Definition empty n : list (option type.t) := repeat None n.

Lemma join_one_None_l :
  forall oty,
    join_one None oty = Some oty.
Proof.
  destruct oty; auto.
Qed.

Lemma join_empty_l :
  forall G,
    join (empty (length G)) G = Some G.
Proof.
  unfold join, empty.
  intros G.
  now rewrite partial_zip.id_l by auto using join_one_None_l.
Qed.

Lemma join_empty_l' :
  forall n G,
    length G = n ->
    join (empty n) G = Some G.
Proof.
  intros.
  subst n.
  apply join_empty_l.
Qed.

Lemma join_length1 :
  forall l1 l2 l3,
    join l1 l2 = Some l3 ->
    length l3 = length l1.
Proof.
  apply partial_zip.length1.
Qed.

Lemma join_length2 :
  forall l1 l2 l3,
    join l1 l2 = Some l3 ->
    length l3 = length l2.
Proof.
  apply partial_zip.length2.
Qed.

Lemma join_unroll :
  forall x1 x2 l1 l2,
    join (x1 :: l1) (x2 :: l2) =
    match join_one x1 x2 with
    | None => None
    | Some y =>
      match join l1 l2 with
      | None => None
      | Some ys => Some (y :: ys)
      end
    end.
Proof.
  reflexivity.
Qed.

Lemma join_comm :
  forall l1 l2,
    join l1 l2 = join l2 l1.
Proof.
  apply partial_zip.comm.
  apply join_one_comm.
Qed.

Lemma join_empty_r :
  forall G,
    join G (empty (length G)) = Some G.
Proof.
  intros.
  now rewrite join_comm, join_empty_l.
Qed.

Lemma join_empty_r' :
  forall G n,
    length G = n ->
    join G (empty n) = Some G.
Proof.
  intros.
  subst.
  now rewrite join_empty_r.
Qed.

Lemma join_assoc :
  forall a1 a2 b,
    match join a1 b with
    | Some b' => join a2 b'
    | None => None
    end = match join a2 b with
          | Some b' => join a1 b'
          | None => None
          end.
Proof.
  intros.
  apply partial_zip.assoc.
  apply join_one_assoc.
Qed.

Fixpoint is_empty (G : list (option type.t)) : Prop :=
  match G with
  | [] => True
  | None :: G => is_empty G
  | _ => False
  end.

Lemma is_empty_empty :
  forall n,
    is_empty (empty n).
Proof.
  unfold empty.
  induction n; simpl; auto.
Qed.
Hint Resolve is_empty_empty.

Lemma is_empty_equal_empty :
  forall l,
    is_empty l ->
    l = empty (length l).
Proof.
  induction l; cbn; intros IS.
  - auto.
  - destruct a; intuition.
    f_equal. apply H.
Qed.

Fixpoint is_singleton (x : nat) (ty : type.t) (G : list (option type.t)) {struct G} : Prop :=
  match x, G with
  | 0, Some ty' :: G => ty = ty' /\ is_empty G
  | S x, None :: G => is_singleton x ty G
  | _, _ => False
  end.

Lemma is_singleton_nth_error1 :
  forall x ty G,
    is_singleton x ty G ->
    List.nth_error G x = Some (Some ty).
Proof.
  induction x; intros ty G IS; (destruct G; [|destruct o]); cbn in *; intuition.
  congruence.
Qed.

Definition big_join n Gs :=
  partial_fold_left.f join (empty n) Gs.
Hint Opaque big_join.

Lemma big_join_unroll :
  forall n G Gs,
    big_join n (G :: Gs) =
    match big_join n Gs with
    | Some G' => join G G'
    | None => None
    end.
Proof.
  unfold big_join.
  intros n G Gs.
  pose proof partial_fold_left.push_step join join_assoc as Push.
  now rewrite <- Push.
Qed.

Lemma big_join_map_cons_None2 :
  forall n Gs,
    big_join (S (S n)) (map (fun x => None :: None :: x) Gs) =
    match big_join n Gs with
    | None => None
    | Some G' => Some (None :: None :: G')
    end.
Proof.
  intros n Gs.
  apply partial_fold_left.distr with (mulA := fun x => None :: None :: x)
                                     (mulB := fun x => None :: None :: x).
  simpl.
  intros.
  repeat break_match; congruence.
Qed.

Lemma big_join_map_cons_None :
  forall n Gs,
    big_join (S n) (map (fun x => None :: x) Gs) =
    match big_join n Gs with
    | None => None
    | Some G' => Some (None :: G')
    end.
Proof.
  intros n Gs.
  apply partial_fold_left.distr with (mulA := fun x => None :: x) (mulB := fun x => None :: x).
  reflexivity.
Qed.

Lemma join_one_Some_inv :
  forall a b o,
    join_one (Some a) b = Some o ->
    o = Some a.
Proof.
  unfold join_one.
  intros.
  destruct b; congruence.
Qed.

Lemma join_project1 :
  forall G1 G2 G,
    join G1 G2 = Some G ->
    project None G1 G = G1.
Proof.
  unfold join.
  intros G1 G2 G J.
  eapply partial_zip_project; [|now apply J].
  apply join_one_Some_inv.
Qed.

Lemma join_project2 :
  forall G1 G2 G,
    join G1 G2 = Some G ->
    project None G2 G = G2.
Proof.
  intros G1 G2 G J.
  rewrite join_comm in J.
  eauto using join_project1.
Qed.

Lemma empty_length :
  forall n,
    length (empty n) = n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma big_join_length_acc :
  forall Gs n G',
    big_join n Gs = Some G' ->
    length G' = n.
Proof.
  induction Gs; intros n G' BJ.
  - cbn in *. invc BJ.
    auto using empty_length.
  - rewrite big_join_unroll in BJ.
    destruct big_join eqn:BJ2; [|discriminate].
    rename BJ into J.
    rename BJ2 into BJ.
    erewrite join_length2 by eauto.
    eauto.
Qed.

Lemma big_join_length :
  forall Gs n G' G1 x,
    big_join n Gs = Some G' ->
    nth_error Gs x = Some G1 ->
    length G1 = n.
Proof.
  induction Gs; intros n G' G1 x BJ NE.
  - destruct x; discriminate.
  - rewrite big_join_unroll in BJ.
    destruct big_join eqn:BJ2; [|discriminate].
    rename BJ into J.
    rename BJ2 into BJ.
    destruct x; cbn in NE.
    + invc NE.
      erewrite <- join_length1 by eauto.
      erewrite join_length2 by eauto.
      eauto using big_join_length_acc.
    + eapply IHGs; eauto.
Qed.

Lemma big_join_project :
  forall Gs G1 G2 G G' n,
    join G1 G2 = Some G ->
    big_join n Gs = Some G' ->
    Forall2 (fun Γ oty => oty = None -> is_empty Γ) Gs G ->
    exists G1' G2',
      big_join n (project (empty n) G1 Gs) = Some G1' /\
      big_join n (project (empty n) G2 Gs) = Some G2' /\
      join G1' G2' = Some G'.
Proof.
  induction Gs; intros G1 G2 G G' n J BJ F.
  - cbn in BJ. invc BJ.
    cbn.
    do 2 eexists.
    split; [|split]; eauto.
    now rewrite join_empty_l' by auto using empty_length.
  - rewrite big_join_unroll in BJ.
    destruct big_join eqn:BJ2; [|discriminate].
    rename BJ into J'.
    rename BJ2 into BJ.
    invc F.
    destruct G1, G2; try solve [cbn in J; discriminate].
    rewrite join_unroll in J.
    destruct join_one eqn:JO; [|discriminate].
    destruct join eqn:J12; [|discriminate].
    invc J.

    eapply IHGs with (G1 := G1) in BJ; eauto.
    destruct BJ as (G1' & G2' & BJ1' & BJ2' & J).
    assert (length G1' = n) as LG1' by eauto using big_join_length_acc.
    assert (length G2' = n) as LG2' by eauto using big_join_length_acc.

    cbn [project].
    destruct o, o0; try solve [cbn in *; discriminate];
      rewrite !big_join_unroll, BJ1', BJ2';
      rewrite !join_empty_l' by auto.
    + pose proof join_assoc G2' a G1' as JA.
      rewrite join_comm in JA.
      rewrite J, J' in JA. symmetry in JA.
      destruct (join a G1') eqn:JA'; [|discriminate].
      setoid_rewrite join_comm.
      eauto.
    + pose proof join_assoc G1' a G2' as JA.
      rewrite J, J' in JA. symmetry in JA.
      destruct (join a G2') eqn:JA'; [|discriminate].
      eauto.
    + invc JO.
      rewrite is_empty_equal_empty with (l := a) in J' by auto.
      rewrite join_empty_l' in J'
        by (erewrite <- join_length2 by eauto;
            erewrite join_length1 by eauto;
            now rewrite empty_length).
      invc J'.
      eauto.
Qed.

Ltac break_join :=
 match goal with
 | [ H : join _ _ = Some [] |- _ ] =>
   apply join_nil_inv in H;
   destruct H as [? ?]; subst
 end.

Lemma is_singleton_cons :
  forall ty G,
    is_empty G ->
    is_singleton 0 ty (Some ty :: G).
Proof. simpl. auto. Qed.
Hint Resolve is_singleton_cons.

Lemma is_singleton_skip :
  forall ty G n,
    is_singleton n ty G ->
    is_singleton (S n) ty (None :: G).
Proof. auto. Qed.
Hint Resolve is_singleton_skip.

Lemma big_join_is_empty :
  forall n Gs G',
    Forall is_empty Gs ->
    big_join n Gs = Some G' ->
    is_empty G'.
Proof.
  unfold big_join.
  intros n Gs G' F BJ.
  eapply partial_fold_left.ind_Some with (P := is_empty); try apply BJ; auto.
  clear.
  intros a b b' A B J.
  apply is_empty_equal_empty in A.
  apply is_empty_equal_empty in B.
  pose proof join_length1 _ _ J as L1.
  pose proof join_length2 _ _ J as L2.
  rewrite <- L1, <- L2 in *. clear L1 L2.
  subst a b.
  rewrite join_empty_l' in J.
  - invc J. auto.
  - now rewrite empty_length.
Qed.

Lemma is_empty_Forall_is_empty :
  forall G Gs,
    Forall2 (fun Γ oty => oty = None -> is_empty Γ) Gs G ->
    is_empty G ->
    Forall is_empty Gs.
Proof.
  induction 1; intros IE.
  - constructor.
  - cbn in *.
    destruct y; intuition.
Qed.

Lemma big_join_is_singleton :
  forall x ty Gs G G1 G',
    is_singleton x ty G ->
    Forall2 (fun Γ oty => oty = None -> is_empty Γ) Gs G ->
    nth_error Gs x = Some G1 ->
    big_join (length G1) Gs = Some G' ->
    G' = G1.
Proof.
  intros x ty Gs G G1 G' IS F NE.
  revert ty G IS Gs G1 G' F NE.
  induction x; cbn in *; intros ty G IS Gs G1 G' F NE BJ.
  - destruct Gs; [discriminate|].
    invc NE.
    rewrite big_join_unroll in BJ.
    destruct big_join eqn:BJ2; [|discriminate].
    rename BJ into J.
    rename BJ2 into BJ.
    destruct G; cbn in IS; [now intuition|].
    destruct o; [|now intuition].
    destruct IS as [? IE]; subst.
    invc F.
    apply big_join_is_empty in BJ; [|now eauto using is_empty_Forall_is_empty].
    apply is_empty_equal_empty in BJ.
    pose proof join_length2 _ _ J as L.
    rewrite <- L in *.
    subst l.
    erewrite join_length1 in J by eassumption.
    rewrite join_empty_r in J.
    congruence.
  - destruct Gs; [discriminate|].
    invc F.
    rewrite big_join_unroll in BJ.
    destruct big_join eqn:BJ2; [|discriminate].
    rename BJ into J.
    rename BJ2 into BJ.
    cbn in IS.
    destruct y; [now intuition|].
    cbn in H1.
    apply is_empty_equal_empty in H1; [|reflexivity].
    erewrite <- join_length1 in H1 by eauto. subst l.
    erewrite join_length2 in J by eauto.
    rewrite join_empty_l in J.
    invc J.
    eauto.
Qed.

Lemma is_singleton_app :
  forall n x ty G,
    is_singleton x ty G ->
    is_singleton (x + n) ty (empty n ++ G).
Proof.
  intros n x ty G IS.
  rewrite plus_comm.
  induction n; auto.
Qed.

Lemma is_singleton_not_nil :
  forall x ty G,
    is_singleton x ty G ->
    G <> [].
Proof.
  intros x ty G IS.
  apply is_singleton_nth_error1 in IS.
  intro C.
  subst.
  destruct x; discriminate.
Qed.

Lemma is_empty_app :
  forall G G',
    is_empty G ->
    is_empty G' ->
    is_empty (G ++ G').
Proof.
  induction G; cbn; intros G' IE IE'.
  - auto.
  - destruct a; [now intuition|].
    auto.
Qed.

Lemma is_empty_splice :
  forall n n' G,
    is_empty G ->
    is_empty (splice n (empty n') G).
Proof.
  induction n; cbn; intros n' G IE.
  - auto using is_empty_app.
  - destruct G.
    + now auto.
    + cbn in *.
      destruct o; [now intuition|].
      auto.
Qed.

Lemma if_pull_f :
  forall A B (f : A -> B) (b : bool) a1 a2,
    (if b then f a1 else f a2) = f (if b then a1 else a2).
Proof.
  destruct b; auto.
Qed.

Lemma is_singleton_splice :
  forall n n' x ty G,
    is_singleton x ty G ->
    is_singleton (if x <? n then x else x + n') ty (splice n (empty n') G).
Proof.
  induction n; intros n' x ty G IS; simpl splice.
  - destruct (Nat.ltb_spec0 x 0); [omega|].
    auto using is_singleton_app.
  - destruct G eqn:EQG; [now exfalso; eapply is_singleton_not_nil; eauto|].
    destruct x.
    + simpl in *. destruct o; intuition. auto using is_empty_splice.
    + simpl plus.
      rewrite if_pull_f.
      simpl is_singleton in *.
      destruct o; [now auto|].
      change (S x <? S n) with (x <? n).
      now auto.
Qed.

Lemma join_app :
  forall G1 G2 G G1' G2' G',
    join G1 G2 = Some G ->
    join G1' G2' = Some G' ->
    join (G1 ++ G1') (G2 ++ G2') = Some (G ++ G').
Proof.
  apply partial_zip.app.
Qed.

Lemma join_splice :
  forall n n' G1 G2 G,
    join G1 G2 = Some G ->
    join (splice n (empty n') G1) (splice n (empty n') G2) = Some (splice n (empty n') G).
Proof.
  intros.
  apply partial_zip.splice;
    auto using join_empty_l', empty_length.
Qed.

Module has_type.
  Inductive t : list (option type.t) -> expr.t -> type.t -> Prop :=
  | var : forall G x ty,
      is_singleton x ty G ->
      t G (expr.var x) ty
  | abs : forall G e ty1 ty2 ,
      t (Some ty1 :: G) e ty2 ->
      t G (expr.abs e) (type.lolli ty1 ty2)
  | app : forall G G1 G2 e1 e2 ty1 ty2,
      join G1 G2 = Some G ->
      t G1 e1 (type.lolli ty1 ty2) ->
      t G2 e2 ty1 ->
      t G (expr.app e1 e2) ty2
  | both : forall G G1 G2 e1 e2 ty1 ty2,
      join G1 G2 = Some G ->
      t G1 e1 ty1 ->
      t G2 e2 ty2 ->
      t G (expr.both e1 e2) (type.tensor ty1 ty2)
  | let_pair : forall G G1 G2 e1 e2 ty1 ty2 ty,
      join G1 G2 = Some G ->
      t G1 e1 (type.tensor ty1 ty2) ->
      t (Some ty2 :: Some ty1 :: G2) e2 ty ->
      t G (expr.let_pair e1 e2) ty
  | oneof : forall G e1 e2 ty1 ty2,
      t G e1 ty1 ->
      t G e2 ty2 ->
      t G (expr.oneof e1 e2) (type.uchoose ty1 ty2)
  | fst : forall G e ty1 ty2,
      t G e (type.uchoose ty1 ty2) ->
      t G (expr.fst e) ty1
  | snd : forall G e ty1 ty2,
      t G e (type.uchoose ty1 ty2) ->
      t G (expr.snd e) ty2
 | inl : forall G e ty1 ty2,
      t G e ty1 ->
      t G (expr.inl e) (type.ichoose ty1 ty2)
  | inr : forall G e ty1 ty2,
      t G e ty2 ->
      t G (expr.inr e) (type.ichoose ty1 ty2)
  | case : forall G G1 G2 e e1 e2 ty1 ty2 ty,
      join G1 G2 = Some G ->
      t G1 e (type.ichoose ty1 ty2) ->
      t (Some ty1 :: G2) e1 ty ->
      t (Some ty2 :: G2) e2 ty ->
      t G (expr.case e e1 e2) ty
  | tt : forall G,
      is_empty G ->
      t G expr.tt type.one
  | let_tt : forall G G1 G2 e1 e2 ty,
      join G1 G2 = Some G ->
      t G1 e1 type.one ->
      t G2 e2 ty ->
      t G (expr.let_tt e1 e2) ty
  .
  Hint Constructors t.

  Definition has_opt_type G e oty :=
    match oty with
    | None => is_empty G
    | Some ty => has_type.t G e ty
    end.
  Arguments has_opt_type _ _ _ : simpl nomatch.

  Lemma has_opt_type_None :
    forall n e,
      has_opt_type (empty n) e None.
  Proof.
    unfold has_opt_type.
    auto using is_empty_empty.
  Qed.
  Hint Resolve has_opt_type_None.

  Lemma has_opt_type_None_skip :
    forall G e,
      has_opt_type G e None ->
      has_opt_type (None :: G) e None.
  Proof.
    unfold has_opt_type.
    auto.
  Qed.
  Hint Resolve has_opt_type_None_skip.

  Lemma has_opt_type_Some :
    forall G e ty,
      has_opt_type G e (Some ty) ->
      has_type.t G e ty.
  Proof.
    intros G e ty HT.
    now unfold has_opt_type in HT.
  Qed.

  Lemma has_opt_type_Some_intro :
    forall G e ty,
      t G e ty ->
      has_opt_type G e (Some ty).
  Proof.
    simpl.
    auto.
  Qed.
  Hint Resolve has_opt_type_Some_intro.

  Lemma has_opt_type_empty :
    forall Gs rho G,
      is_empty G ->
      Forall3 has_opt_type Gs rho G ->
      Forall is_empty Gs.
  Proof.
    intros Gs rho G E F.
    induction F.
    + constructor.
    + simpl in E. destruct c; [now intuition|now auto].
  Qed.

  Lemma Forall3_has_opt_type_Forall2_None_is_empty :
    forall Gs rho G,
      Forall3 has_opt_type Gs rho G ->
      Forall2 (fun Γ oty => oty = None -> is_empty Γ) Gs G.
  Proof.
    induction 1; constructor; auto.
    now intros ?; subst c.
  Qed.

  Lemma shift :
    forall G e ty,
      t G e ty ->
      forall n n',
        t (splice n (empty n') G) (expr.shift n n' e) ty.
  Proof.
    induction 1; simpl expr.shift; intros n n';
      try solve [econstructor; eauto using join_splice].
    - constructor. auto using is_singleton_splice.
    - constructor. apply IHt with (n := S n).
    - econstructor; [|now eauto|now apply IHt2 with (n := S (S n))].
      now eauto using join_splice.
    - econstructor; [|now eauto| apply IHt2 with (n := S n)|apply IHt3 with (n := S n)].
      now eauto using join_splice.
    - constructor.
      now apply is_empty_splice.
  Qed.

  Lemma shift' :
    forall G e ty n,
      t G e ty ->
      t (empty n ++ G) (expr.shift 0 n e) ty.
  Proof.
    intros.
    now apply shift with (n := 0) (n' := n).
  Qed.

  Lemma shift_cons :
    forall G e ty,
      t G e ty ->
      t (None :: G) (expr.shift 0 1 e) ty.
  Proof.
    intros.
    now apply shift' with (n := 1).
  Qed.

  Lemma shift_cons_opt_None :
    forall G e ty,
      has_opt_type G e ty ->
      has_opt_type (None :: G) (expr.shift 0 1 e) ty.
  Proof.
    unfold has_opt_type.
    intros G e [ty|] H; [|now idtac].
    now apply shift_cons.
  Qed.

  Lemma shift_cons_opt_None_skip :
    forall n G e ty,
      has_opt_type G (expr.shift 0 n e) ty ->
      has_opt_type (None :: G) (expr.shift 0 (S n) e) ty.
  Proof.
    intros n G e ty H.
    rewrite <- expr.shift_merge with (d2 := 1).
    now apply shift_cons_opt_None.
  Qed.

  Let FHO := Forall3_has_opt_type_Forall2_None_is_empty.

  Lemma subst :
    forall G e ty,
      has_type.t G e ty ->
      forall G' Gs rho n,
        Forall3 has_opt_type Gs rho G ->
        big_join n Gs = Some G' ->
        n = List.length G' ->
        has_type.t G' (expr.subst rho e) ty.
  Proof.
    induction 1; intros G' Gs rho n F J EN; cbn [expr.subst]; eauto.
    - simpl expr.subst.
      pose proof is_singleton_nth_error1 _ _ _ H as NEty.
      destruct (Forall3_nth_error3 _ F NEty) as [G1 [e [NEG1 [NEe HT]]]].
      unfold expr.t in *.
      apply has_opt_type_Some in HT.
      rewrite NEe.
      erewrite <- big_join_length with (n := _) in J by eauto.
      eapply big_join_is_singleton in J; eauto using FHO.
      congruence.
    - constructor.
      apply IHt with (n := S n)
                     (Gs := (Some ty1 :: empty (length G')) :: map (fun G => None :: G) Gs).
      + constructor.
        now simpl; auto.
        eauto using Forall3_map1, Forall3_map2, Forall3_impl, shift_cons_opt_None.
      + now rewrite big_join_unroll, big_join_map_cons_None, J, join_unroll, join_empty_l.
      + simpl. congruence.
    - pose proof big_join_project _ _ _ H J (FHO F) as (G1' & G2' & J1' & J2' & J').
      econstructor; [| eapply IHt1 | eapply IHt2 ]; subst;
        try solve [eauto using join_length1, join_length2].
      now erewrite <- join_project1 by eauto; auto.
      now erewrite <- join_project2 by eauto; auto.
    - pose proof big_join_project _ _ _ H J (FHO F) as (G1' & G2' & J1' & J2' & J').
      econstructor; [| eapply IHt1| eapply IHt2]; subst;
        try solve [eauto using join_length1, join_length2].
      now erewrite <- join_project1 by eauto; auto.
      now erewrite <- join_project2 by eauto; auto.
    - pose proof big_join_project _ _ _ H J (FHO F) as (G1' & G2' & J1' & J2' & J').
      assert (n = length G2') by (subst; eauto using join_length2, eq_sym).
      econstructor; [| eapply IHt1|
                     eapply IHt2 with (n := S (S n))
                                      (Gs := (Some ty2 :: empty (S n)) ::
                                             (None :: Some ty1 :: empty n) ::
                                             (map (fun G => None :: None :: G)
                                                  (project (empty n) G2 Gs)))];
      try solve [subst; eauto using join_length1, join_length2].
      + now erewrite <- join_project1 by eauto; auto.
      + constructor; [now simpl; auto |].
        constructor; [now simpl; auto |].

        erewrite <- join_project2 with (G2 := G2) at 2 by eauto.
        eauto 10 using Forall3_map1, Forall3_map2, Forall3_project, Forall3_impl,
                       shift_cons_opt_None_skip, shift_cons_opt_None.
      + do 2 rewrite big_join_unroll.
        rewrite big_join_map_cons_None2, J2'.
        do 2 rewrite join_unroll.
        cbn[join_one].
        rewrite join_empty_l' by congruence.
        rewrite join_unroll.
        cbn[join_one].
        now rewrite join_empty_l' by (cbn; congruence).
      + cbn. congruence.
    - pose proof big_join_project _ _ _ H J (FHO F) as (G1' & G2' & J1' & J2' & J').
      econstructor; [now eauto| | | ].
      + eapply IHt1; [| now eauto | now subst; eauto using join_length1].
        now erewrite <- join_project1 by eauto; auto.
      + apply IHt2 with (n := S n) (Gs := (Some ty1 :: empty n) ::
                                          map (fun G => None :: G) (project (empty n) G2 Gs));
          [| |now subst; simpl; eauto using join_length2].
        constructor; [now auto|].
        apply Forall3_map1.
        apply Forall3_map2.
        erewrite <- join_project2 by eauto.
        apply Forall3_project.
        now auto using shift_cons_opt_None.
        eapply Forall3_impl. 2: eassumption.
        now auto using shift_cons_opt_None.

        rewrite big_join_unroll.
        rewrite big_join_map_cons_None.
        rewrite J2'.
        rewrite join_unroll.
        cbn[join_one].
        now rewrite join_empty_l' by (subst; eauto using join_length2, eq_sym).
      + apply IHt3 with (n := S n) (Gs := (Some ty2 :: empty n) ::
                                          map (fun G => None :: G) (project (empty n) G2 Gs));
          [| |now subst; simpl; eauto using join_length2].
        constructor; [now auto|].
        apply Forall3_map1.
        apply Forall3_map2.
        erewrite <- join_project2 by eauto.
        apply Forall3_project.
        now auto using shift_cons_opt_None.
        eapply Forall3_impl. 2: eassumption.
        now auto using shift_cons_opt_None.

        rewrite big_join_unroll.
        rewrite big_join_map_cons_None.
        rewrite J2'.
        rewrite join_unroll.
        cbn[join_one].
        now rewrite join_empty_l' by (subst; eauto using join_length2, eq_sym).
    - econstructor.
      eapply big_join_is_empty; [|now eauto].
      now eauto using has_opt_type_empty.
    - pose proof big_join_project _ _ _ H J (FHO F) as (G1' & G2' & J1' & J2' & J').
      econstructor; [now eauto| |].
      + eapply IHt1; [|now eauto|].
        erewrite <- join_project1 by eauto.
        apply Forall3_project; auto.
        subst. eauto using join_length1.
      + eapply IHt2; [|now eauto|].
        erewrite <- join_project2 by eauto.
        apply Forall3_project; auto.
        subst. eauto using join_length2.
  Qed.
End has_type.

Module value.
  Inductive t : expr.t -> Prop :=
  | abs : forall e, t (expr.abs e)
  | both : forall e1 e2, t e1 -> t e2 -> t (expr.both e1 e2)
  | oneof : forall e1 e2, t (expr.both e1 e2)
  | inl : forall e, t e -> t (expr.inl e)
  | inr : forall e, t e -> t (expr.inr e)
  | tt : t expr.tt
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
  | tensor_beta : forall v1 v2 e,
      value.t v1 ->
      value.t v2 ->
      t (expr.let_pair (expr.both v1 v2) e) (expr.subst [v2; v1] e)
  | both1 : forall e1 e1' e2,
      t e1 e1' ->
      t (expr.both e1 e2) (expr.both e1' e2)
  | both2 : forall e1 e2 e2',
      value.t e1 ->
      t e2 e2' ->
      t (expr.both e1 e2) (expr.both e1 e2')
  | let_pair : forall e1 e1' e2,
      t e1 e1' ->
      t (expr.let_pair e1 e2) (expr.let_pair e1' e2)
  | fst_beta : forall e1 e2,
      t (expr.fst (expr.oneof e1 e2)) e1
  | snd_beta : forall e1 e2,
      t (expr.snd (expr.oneof e1 e2)) e2
  | fst : forall e e',
      t e e' ->
      t (expr.fst e) (expr.fst e')
  | snd : forall e e',
      t e e' ->
      t (expr.snd e) (expr.snd e')
  | inl_beta : forall v e1 e2,
      value.t v ->
      t (expr.case (expr.inl v) e1 e2) (expr.subst [v] e1)
  | inr_beta : forall v e1 e2,
      value.t v ->
      t (expr.case (expr.inr v) e1 e2) (expr.subst [v] e2)
  | inl : forall e e',
      t e e' ->
      t (expr.inl e) (expr.inl e')
  | inr : forall e e',
      t e e' ->
      t (expr.inr e) (expr.inr e')
  | case : forall e1 e1' e2 e3,
      t e1 e1' ->
      t (expr.case e1 e2 e3) (expr.case e1' e2 e3)
  | one_beta : forall e,
      t (expr.let_tt expr.tt e) e
  | let_tt : forall e1 e1' e2,
      t e1 e1' ->
      t (expr.let_tt e1 e2) (expr.let_tt e1' e2)
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
    intros e1 e2 e2' Val1 Star.
    revert e1 Val1.
    induction Star; intros e1 Val1.
    - constructor.
    - econstructor; [|apply IHStar]; auto.
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

  Hint Resolve star_app2 star_app1 star_refl.
End step.

Lemma preservation :
  forall G e ty,
    has_type.t G e ty ->
    G = [] ->
    forall e',
      step.t e e' ->
      has_type.t [] e' ty.
Proof.
  induction 1; intros ? e' Step; subst; invc Step; try break_join;
    try solve [try econstructor; eauto];
    match goal with
    | [ H : has_type.t _ (_ _) _ |- _ ] => invc H
    end;
    try break_join;
    eauto;
    eapply has_type.subst; eauto; auto.
Qed.
