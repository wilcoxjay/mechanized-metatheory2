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

Module empty.
  Definition empty n : list (option type.t) := repeat None n.

  Lemma unroll : forall n, empty (S n) = None :: empty n.
  Proof.
    reflexivity.
  Qed.
End empty.
Notation empty := empty.empty.

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
Hint Resolve is_empty_empty : core.

Lemma is_empty_equal_empty :
  forall l,
    is_empty l ->
    l = empty (length l).
Proof.
  induction l; cbn; intros IS.
  - auto.
  - destruct a; intuition auto using f_equal2.
Qed.

Definition empty_if_None Γ (oty : option type.t) := oty = None -> is_empty Γ.

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

Lemma empty_length :
  forall n,
    length (empty n) = n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma is_singleton_cons :
  forall ty G,
    is_empty G ->
    is_singleton 0 ty (Some ty :: G).
Proof. simpl. auto. Qed.
Hint Resolve is_singleton_cons : core.

Lemma is_singleton_skip :
  forall ty G n,
    is_singleton n ty G ->
    is_singleton (S n) ty (None :: G).
Proof. auto. Qed.
Hint Resolve is_singleton_skip : core.

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

Module joinable_one.
  Definition joinable_one (x y : option type.t) := x = None \/ y = None.

  Lemma None_l :
    forall oty,
      joinable_one None oty.
  Proof.
    now left.
  Qed.

  Lemma None_r :
    forall oty,
      joinable_one oty None.
  Proof.
    now right.
  Qed.

  Lemma comm :
    forall x y,
      joinable_one x y ->
      joinable_one y x.
  Proof.
    unfold joinable_one.
    intuition.
  Qed.

  Lemma Some2 :
    forall x y,
      joinable_one (Some x) (Some y) -> False.
  Proof.
    destruct 1; discriminate.
  Qed.
End joinable_one.
Notation joinable_one := joinable_one.joinable_one.

Module join_one.
  Definition join_one (oty1 oty2 : option type.t) : option type.t :=
    match oty1, oty2 with
    | None, None => None
    | Some _, None => oty1
    | None, Some _ => oty2
    | _, _ => None (* bogus *)
    end.

  Lemma None_l :
    forall oty,
      join_one None oty = oty.
  Proof.
    destruct oty; reflexivity.
  Qed.

  Lemma None_r :
    forall oty,
      join_one oty None = oty.
  Proof.
    destruct oty; reflexivity.
  Qed.

  Lemma comm :
    forall x y,
      join_one x y = join_one y x.
  Proof.
    destruct x, y; reflexivity.
  Qed.

  Lemma joinable_one_r :
    forall a b c,
      joinable_one a b ->
      joinable_one a c ->
      joinable_one b c ->
      joinable_one a (join_one b c).
  Proof.
    unfold joinable_one, join_one.
    now intuition; subst; auto.
  Qed.

  Lemma Some_l :
    forall x y,
      joinable_one (Some x) y ->
      join_one (Some x) y = Some x.
  Proof.
    unfold joinable_one.
    destruct x, y; cbn; intuition discriminate.
  Qed.

  Lemma assoc :
    forall a b c,
      joinable_one a b ->
      join_one (join_one a b) c = join_one a (join_one b c).
  Proof.
    destruct a, b, c; cbn; auto.
    unfold joinable_one.
    intuition discriminate.
  Qed.

  Lemma joinable_one :
    forall a b c d,
      joinable_one a b ->
      joinable_one a c ->
      joinable_one a d ->
      joinable_one b c ->
      joinable_one b d ->
      joinable_one c d ->
      joinable_one (join_one a b) (join_one c d).
  Proof.
    unfold joinable_one, join_one.
    intros a b c d [|]; subst.
    - intros _ _. intuition; subst; auto.
    - intros ? ? _ _. intuition; subst; auto.
  Qed.
End join_one.
Notation join_one := join_one.join_one.

Module joinable.
  Definition joinable (G1 G2 : list (option type.t)) : Prop :=
    Forall2 joinable_one G1 G2.

  Lemma cons_intro :
    forall x y xs ys,
      joinable_one x y ->
      joinable xs ys ->
      joinable (x :: xs) (y :: ys).
  Proof.
    intros x y xs ys.
    unfold joinable.
    intuition.
  Qed.

  Lemma app :
    forall G1 G2 G1' G2',
      joinable G1 G2 ->
      joinable G1' G2' ->
      joinable (G1 ++ G1') (G2 ++ G2').
  Proof.
    unfold joinable.
    induction 1; cbn; auto.
  Qed.

  Lemma splice :
    forall n G1 G2 G1' G2',
      joinable G1 G2 ->
      joinable G1' G2' ->
      joinable (splice n G1' G1) (splice n G2' G2).
  Proof.
    unfold joinable.
    induction n; intros G1 G2 G1' G2' J J'; cbn [splice].
    - apply app; auto.
    - invc J; auto.
  Qed.

  Lemma is_empty_l :
    forall G1 G2,
      is_empty G1 ->
      length G1 = length G2 ->
      joinable G1 G2.
  Proof.
    unfold joinable.
    induction G1; cbn; intros G2 IE L.
    - destruct G2; [|discriminate].
      now auto.
    - destruct a; [now intuition|].
      destruct G2; [discriminate|].
      now auto using joinable_one.None_l.
  Qed.

  Lemma empty_l :
    forall n G,
      length G = n ->
      joinable (empty n) G.
  Proof.
    intros n G <-.
    auto using is_empty_l, empty_length.
  Qed.

  Lemma comm :
    forall G1 G2,
      joinable G1 G2 ->
      joinable G2 G1.
  Proof.
    unfold joinable.
    induction 1; constructor; intuition auto using joinable_one.comm.
  Qed.

  Lemma is_empty_r :
    forall G1 G2,
      is_empty G2 ->
      length G1 = length G2 ->
      joinable G1 G2.
  Proof.
    auto using comm, is_empty_l.
  Qed.

  Lemma empty_r :
    forall n G,
      length G = n ->
      joinable G (empty n).
  Proof.
    auto using comm, empty_l.
  Qed.

  Lemma empty_internal :
    forall n,
      joinable (empty n) (empty n).
  Proof.
    intros n.
    apply is_empty_l; auto.
  Qed.
  Hint Resolve empty_internal : core.

  Lemma splice_empty :
    forall n n' G1 G2,
      joinable G1 G2 ->
      joinable (util.splice n (empty n') G1) (util.splice n (empty n') G2).
  Proof.
    eauto using splice.
  Qed.

  Lemma cons_None :
    forall a1 a2,
      joinable a1 a2 ->
      joinable (None :: a1) (None :: a2).
  Proof.
    unfold joinable.
    auto using joinable_one.None_l.
  Qed.

  Lemma Forall_length :
    forall n Gs,
      Forall (fun G => length G = n) Gs ->
      Forall (joinable (empty n)) Gs.
  Proof.
    intros n Gs.
    apply Forall_impl.
    auto using empty_l.
  Qed.

  Lemma nil :
    joinable [] [].
  Proof.
    constructor.
  Qed.
  Hint Resolve nil : core.

  Notation empty := empty_internal.
End joinable.
Notation joinable := joinable.joinable.

Module join.
  Definition join (G1 G2 : list (option type.t)) : list (option type.t) :=
    zip join_one G1 G2.

  Lemma unroll :
    forall x y xs ys,
      join (x :: xs) (y :: ys) = join_one x y :: join xs ys.
  Proof.
    reflexivity.
  Qed.

  Lemma app :
    forall G1 G1' G2 G2',
      joinable G1 G2 ->
      joinable G1' G2' ->
      join (G1 ++ G1') (G2 ++ G2') = join G1 G2 ++ join G1' G2'.
  Proof.
    unfold joinable, join.
    induction 1; intros J'; cbn; auto using f_equal.
  Qed.

  Lemma splice :
    forall n G1 G1' G2 G2',
      joinable G1 G2 ->
      joinable G1' G2' ->
      join (splice n G1' G1) (splice n G2' G2) = splice n (join G1' G2') (join G1 G2).
  Proof.
    unfold join, joinable.
    induction n; intros G1 G1' G2 G2' JA JA'; cbn[splice].
    - apply app; auto.
    - invc JA; cbn; auto using f_equal.
  Qed.

  Lemma is_empty_l :
    forall G1 G2,
      joinable G1 G2 ->
      is_empty G1 ->
      join G1 G2 = G2.
  Proof.
    unfold joinable, join.
    induction 1; cbn; intros IE.
    - now auto.
    - destruct x; [now intuition|].
      rewrite join_one.None_l.
      auto using f_equal.
  Qed.

  Lemma empty_l :
    forall n G,
      length G = n ->
      join (empty n) G = G.
  Proof.
    intros n G L.
    apply is_empty_l; auto using joinable.empty_l.
  Qed.

  Lemma empty_internal :
    forall n,
      join (empty n) (empty n) = empty n.
  Proof.
    auto using is_empty_l.
  Qed.

  Lemma splice_empty :
    forall n n' G1 G2 G,
      joinable G1 G2 ->
      join G1 G2 = G ->
      join (util.splice n (empty n') G1)
           (util.splice n (empty n') G2) =
        util.splice n (empty n') G.
  Proof.
    intros n n' G1 G2 G JA J.
    rewrite splice by auto using joinable.is_empty_l.
    rewrite is_empty_l by auto.
    congruence.
  Qed.

  Lemma comm :
    forall G1 G2,
      joinable G1 G2 ->
      join G1 G2 = join G2 G1.
  Proof.
    unfold joinable, join.
    induction 1; cbn.
    - now auto.
    - auto using f_equal2, join_one.comm.
  Qed.

  Lemma length1 :
    forall xs ys,
      joinable xs ys ->
      length (join xs ys) = length xs.
  Proof.
    unfold joinable, join.
    induction 1; cbn; auto.
  Qed.

  Lemma joinable_r :
    forall a b c,
      joinable a b ->
      joinable a c ->
      joinable b c ->
      joinable a (join b c).
  Proof.
    unfold joinable, join.
    intros a b c Jab.
    revert c.
    induction Jab; intros c Jac Jbc; invc Jac; invc Jbc; constructor;
      auto using join_one.joinable_one_r.
  Qed.

  Lemma joinable_internal :
    forall a b c d,
      joinable a b ->
      joinable a c ->
      joinable a d ->
      joinable b c ->
      joinable b d ->
      joinable c d ->
      joinable (join a b) (join c d).
  Proof.
    unfold joinable, join.
    intros a b c d Jab.
    revert c d.
    induction Jab; intros c d Jac Jad Jbc Jbd Jcd;
      invc Jac; invc Jad; invc Jbc; invc Jbd; invc Jcd;
        constructor;
        auto using join_one.joinable_one.
  Qed.

  Lemma project1 :
    forall G1 G2 G,
      joinable G1 G2 ->
      join G1 G2 = G ->
      project None G1 G = G1.
  Proof.
    unfold joinable.joinable, join.
    intros G1 G2 G JA J.
    revert G J.
    induction JA; intros G J; subst; cbn.
    - reflexivity.
    - destruct x; f_equal; eauto using join_one.Some_l.
  Qed.

  Lemma project2 :
    forall G1 G2 G,
      joinable G1 G2 ->
      join G1 G2 = G ->
      project None G2 G = G2.
  Proof.
    intros G1 G2 G JA J.
    rewrite comm in J by auto.
    eauto using project1, joinable.comm.
  Qed.

  Lemma assoc :
    forall a b c,
      joinable a b ->
      join (join a b) c = join a (join b c).
  Proof.
    induction a; intros [|? b] [|? c] JA; cbn; auto.
    invc JA.
    auto using join_one.assoc, f_equal2.
  Qed.

  Lemma swizzle :
    forall a b c d,
      joinable a b ->
      joinable a c ->
      joinable b c ->
      joinable b d ->
      joinable c d ->
      join (join a b) (join c d) = join (join a c) (join b d).
  Proof.
    intros a b c d.
    intros.
    rewrite join.assoc by assumption.
    rewrite join.comm with (G1 := b) by auto using join.joinable_r.
    rewrite join.assoc by assumption.
    rewrite <- join.comm with (G1 := b) by assumption.
    rewrite <- join.assoc by assumption.
    reflexivity.
  Qed.

  Lemma nil_elim :
    forall G1 G2,
      joinable G1 G2 ->
      join G1 G2 = [] ->
      G1 = [] /\ G2 = [].
  Proof.
    intros G1 G2 J.
    invc J; cbn; auto.
    discriminate.
  Qed.

  Notation empty := empty_internal.
End join.
Notation join := join.join.

Module big_joinable.
  Definition big_joinable n Gs :=
    Forall (fun G => length G = n) Gs /\
    ForallOrdPairs joinable Gs.

  Lemma unroll :
    forall n G Gs,
      big_joinable n (G :: Gs) <->
      length G = n /\
      Forall (joinable G) Gs /\
      big_joinable n Gs .
  Proof.
    intros n G Gs.
    split.
    - intros [L Js].
      invc L.
      invc Js.
      unfold big_joinable.
      intuition.
    - intros (L & F & BJA).
      unfold big_joinable in *.
      intuition.
      constructor; auto.
  Qed.

  Lemma extend :
    forall n Gs ty,
      big_joinable n Gs ->
      big_joinable (S n) ((Some ty :: empty n) :: map (fun G => None :: G) Gs).
  Proof.
    intros n Gs ty [L Js].
    split.
    - constructor.
      + cbn. auto using empty_length.
      + apply Forall_map.
        eapply Forall_impl; try apply L.
        cbn. auto.
    - constructor.
      + apply Forall_map.
        eapply Forall_impl; try apply L.
        auto using joinable.cons_intro, joinable_one.None_r, joinable.empty_l.
      + apply ForallOrdPairs_map.
        eapply ForallOrdPairs_impl; try apply Js.
        auto using joinable.cons_None.
  Qed.

  Lemma extend2 :
    forall n Gs ty1 ty2,
      big_joinable n Gs ->
      big_joinable (S (S n)) ((Some ty1 :: empty (S n)) :: (None :: Some ty2 :: empty n) :: map (fun G => None :: None :: G) Gs).
  Proof.
    intros n Gs ty1 ty2 [L Js].
    rewrite empty.unroll.
    split.
    - constructor; [now cbn; auto using empty_length|].
      constructor; [now cbn; auto using empty_length|].
      apply Forall_map.
      eapply Forall_impl; try apply L.
      cbn. auto.
    - constructor.
      + constructor.
        auto using joinable.cons_intro, joinable_one.None_r, joinable.cons_intro,
                   joinable_one.None_l, joinable.empty.
        apply Forall_map.
        eapply Forall_impl; try apply L.
        auto using joinable.cons_intro, joinable_one.None_r, joinable.cons_intro,
                   joinable_one.None_l, joinable.empty_l.
      + constructor.
        * apply Forall_map.
          eapply Forall_impl; try apply L.
          auto using joinable.cons_intro, joinable_one.None_r, joinable.cons_intro,
                     joinable_one.None_l, joinable.empty_l.
        * apply ForallOrdPairs_map.
          eapply ForallOrdPairs_impl; try apply Js.
          auto using joinable.cons_None.
  Qed.

  Lemma project :
    forall n Gs (G : list (option type.t)),
      big_joinable n Gs ->
      big_joinable n (project (empty n) G Gs).
  Proof.
    induction Gs; intros G BJ; cbn.
    - auto.
    - rewrite unroll in BJ.
      destruct BJ as (L & FJ & BJ).
      destruct G as [|[|]]; apply unroll;
        intuition auto using empty_length;
        destruct BJ as (FL & FOPJ);
         auto using Forall_project, joinable.Forall_length, joinable.empty_r.
  Qed.

  Lemma zero_nil :
    big_joinable 0 [].
  Proof.
    repeat constructor.
  Qed.
  Hint Resolve zero_nil : core.

  Lemma zero_cons :
    forall l,
      big_joinable 0 l ->
      big_joinable 0 ([] :: l).
  Proof.
    unfold big_joinable.
    intros.
    repeat constructor; intuition.
    apply joinable.Forall_length with (n := 0); auto.
  Qed.
  Hint Resolve zero_cons : core.
End big_joinable.
Notation big_joinable := big_joinable.big_joinable.

Module big_join.
  Definition big_join n Gs :=
    List.fold_right join (empty n) Gs.

  Lemma unroll :
    forall n G Gs,
      big_join n (G :: Gs) = join G (big_join n Gs).
  Proof.
    reflexivity.
  Qed.

  Lemma is_empty_internal :
    forall Gs G n,
      Forall2 (fun Γ oty => oty = None -> is_empty Γ) Gs G ->
      is_empty G ->
      big_joinable n Gs ->
      big_join n Gs = empty n.
  Proof.
    induction 1; intros IE BJA.
    - now auto.
    - apply big_joinable.unroll in BJA as (L & F & BJA).
      rewrite unroll.
      cbn in IE.
      destruct y; [now intuition|].
      rewrite IHForall2; auto.
      rewrite is_empty_equal_empty with (l := x);
        subst; auto using join.empty.
  Qed.

  Lemma is_singleton :
    forall x ty G Gs n G1,
      is_singleton x ty G ->
      Forall2 (fun Γ oty => oty = None -> is_empty Γ) Gs G ->
      nth_error Gs x = Some G1 ->
      big_joinable n Gs ->
      big_join n Gs = G1.
  Proof.
    intros x ty G Gs n G1 IS F NE BJA.
    revert x ty n G1 IS NE BJA.
    induction F as [|Γ [ty'|] Gs G]; intros [|x] ty n G1 IS NE BJA;
      cbn in NE, IS; try solve [intuition];
        apply big_joinable.unroll in BJA as (L & FJ & BJA);
        rewrite unroll.
    - destruct IS as [? IE]. invc NE.
      erewrite is_empty_internal by eauto.
      rewrite join.comm by auto using joinable.comm, joinable.is_empty_l, empty_length.
      now rewrite join.is_empty_l by auto using joinable.is_empty_l, empty_length.
    - erewrite IHF by eauto.
      now rewrite join.is_empty_l; [|now eapply Forall_nth_error; eauto|now auto].
  Qed.

  Lemma map_cons_None :
    forall n Gs,
      big_joinable n Gs ->
      big_join (S n) (map (fun G => None :: G) Gs) = None :: big_join n Gs.
  Proof.
    induction Gs; intros BJA.
    - reflexivity.
    - cbn[map]. rewrite !unroll.
      rewrite big_joinable.unroll in BJA.
      destruct BJA as (L & F & BJA).
      now rewrite IHGs by auto.
  Qed.

  Lemma map_cons_None2 :
    forall n Gs,
      big_joinable n Gs ->
      big_join (S (S n)) (map (fun G => None :: None :: G) Gs) = None :: None :: big_join n Gs.
  Proof.
    induction Gs; intros BJA.
    - reflexivity.
    - cbn [map]. rewrite !unroll.
      rewrite big_joinable.unroll in BJA.
      destruct BJA as (L & F & BJA).
      now rewrite IHGs by auto.
  Qed.

  Lemma joinable_all :
    forall n Gs G,
      Forall (joinable G) Gs ->
      length G = n ->
      big_joinable n Gs ->
      joinable G (big_join n Gs).
  Proof.
    induction Gs; intros G F LG BJA.
    - cbn. auto using joinable.empty_r.
    - inversion F as [|tmp1 tmp2 JGa FG]; subst tmp1 tmp2; clear F.
      rewrite big_join.unroll.
      rewrite big_joinable.unroll in BJA.
      destruct BJA as (La & Fa & BJA).
      auto using join.joinable_r.
  Qed.

  Lemma length :
    forall Gs n,
      big_joinable n Gs ->
      length (big_join n Gs) = n.
  Proof.
    induction Gs; intros n BJA.
    - cbn. auto using empty_length.
    - rewrite unroll.
      rewrite big_joinable.unroll in BJA.
      destruct BJA as (L & F & BJA).
      now rewrite join.length1 by auto using joinable_all.
  Qed.

  Lemma extend :
    forall n Gs ty,
      big_joinable n Gs ->
      big_join (S n) ((Some ty :: empty n) :: map (fun G => None :: G) Gs) =
      Some ty :: big_join n Gs.
  Proof.
    intros n Gs ty BJA.
    rewrite unroll, map_cons_None by assumption.
    rewrite join.unroll, join_one.None_r.
    now rewrite join.empty_l by auto using length.
  Qed.

  Lemma extend2 :
    forall n Gs ty1 ty2,
      big_joinable n Gs ->
      big_join (S (S n)) ((Some ty1 :: empty (S n)) :: (None :: Some ty2 :: empty n) :: map (fun G => None :: None :: G) Gs) =
      Some ty1 :: Some ty2 :: big_join n Gs.
  Proof.
    intros n Gs ty1 ty2 BJA.
    rewrite empty.unroll.
    rewrite !unroll, map_cons_None2 by assumption.
    rewrite !join.unroll, !join_one.None_r, join_one.None_l.
    rewrite !join.empty_l; auto using length.
    rewrite join.length1 by auto using joinable.empty_l, length.
    auto using empty_length.
  Qed.

  Lemma project_joinable :
    forall n G1 G2 Gs,
      joinable G1 G2 ->
      big_joinable n Gs ->
      joinable (big_join n (project (empty n) G1 Gs))
               (big_join n (project (empty n) G2 Gs)).
  Proof.
    intros n G1 G2 Gs.
    revert n G1 G2.
    induction Gs; intros n G1 G2 J BJA.
    - apply joinable.empty.
    - apply big_joinable.unroll in BJA.
      destruct BJA as (L & F & BJA).
      rewrite !project_unroll.
      rewrite !big_join.unroll.
      destruct G1 as [|[|]], G2 as [|[|]]; invc J;
        remember (Datatypes.length a) as n in *;
        try rewrite !join.empty_l by auto using big_join.length, big_joinable.project;
        auto.
      + exfalso. eauto using joinable_one.Some2.
      + apply joinable.comm.
        apply join.joinable_r;
          auto using joinable.comm, joinable_all, Forall_project, big_joinable.project,
                     joinable.empty_r.
      + apply join.joinable_r;
          auto using joinable.comm, joinable_all, Forall_project, big_joinable.project,
                     joinable.empty_r.
  Qed.

  Lemma project_join :
    forall n G1 G2 G Gs,
      joinable G1 G2 ->
      join G1 G2 = G ->
      big_joinable n Gs ->
      Forall2 empty_if_None Gs G ->
      join (big_join n (project (empty n) G1 Gs))
           (big_join n (project (empty n) G2 Gs)) =
      big_join n Gs.
  Proof.
    intros n G1 G2 G Gs.
    revert n G1 G2 G.
    induction Gs; intros n G1 G2 G JA J BJA F.
    - apply join.empty.
    - apply big_joinable.unroll in BJA.
      destruct BJA as (L & FL & BJA).
      rewrite !project_unroll.
      rewrite !big_join.unroll.
      inversion F as [|tmp1 b tmp2 G' EIN F']; subst tmp1 tmp2 G; clear F.
      destruct G1, G2; try solve [discriminate].
      rewrite join.unroll in *.
      invc H1.
      inversion JA as [|? ? ? ? JO JA']; subst; clear JA.

      destruct o, o0;
        try solve [unfold joinable_one in JO; intuition discriminate];
        rewrite !join.empty_l by auto using big_join.length, big_joinable.project.
      + rewrite join.assoc by auto using joinable_all, Forall_project, big_joinable.project, joinable.empty_r.
        eauto using f_equal2.
      + rewrite join.comm.
        rewrite join.assoc by auto using joinable_all, Forall_project, big_joinable.project, joinable.empty_r.
        rewrite join.comm with (G1 := big_join _ _)
          by auto using joinable.comm, project_joinable.
        eauto using f_equal2.
        apply join.joinable_r;
          auto using joinable_all, Forall_project, big_joinable.project,
                     project_joinable, joinable.comm, joinable.empty_r.
      + rewrite join.is_empty_l with (G1 := a); eauto.
        apply joinable.is_empty_l; auto.
        rewrite length; auto.
  Qed.

  Notation is_empty := is_empty_internal.
End big_join.
Notation big_join := big_join.big_join.

Module has_type.
  Inductive t : list (option type.t) -> expr.t -> type.t -> Prop :=
  | var : forall G x ty,
      is_singleton x ty G ->
      t G (expr.var x) ty
  | abs : forall G e ty1 ty2 ,
      t (Some ty1 :: G) e ty2 ->
      t G (expr.abs e) (type.lolli ty1 ty2)
  | app : forall G G1 G2 e1 e2 ty1 ty2,
      joinable G1 G2 ->
      join G1 G2 = G ->
      t G1 e1 (type.lolli ty1 ty2) ->
      t G2 e2 ty1 ->
      t G (expr.app e1 e2) ty2
  | both : forall G G1 G2 e1 e2 ty1 ty2,
      joinable G1 G2 ->
      join G1 G2 = G ->
      t G1 e1 ty1 ->
      t G2 e2 ty2 ->
      t G (expr.both e1 e2) (type.tensor ty1 ty2)
  | let_pair : forall G G1 G2 e1 e2 ty1 ty2 ty,
      joinable G1 G2 ->
      join G1 G2 = G ->
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
      joinable G1 G2 ->
      join G1 G2 = G ->
      t G1 e (type.ichoose ty1 ty2) ->
      t (Some ty1 :: G2) e1 ty ->
      t (Some ty2 :: G2) e2 ty ->
      t G (expr.case e e1 e2) ty
  | tt : forall G,
      is_empty G ->
      t G expr.tt type.one
  | let_tt : forall G G1 G2 e1 e2 ty,
      joinable G1 G2 ->
      join G1 G2 = G ->
      t G1 e1 type.one ->
      t G2 e2 ty ->
      t G (expr.let_tt e1 e2) ty
  .
  Hint Constructors t : core.

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
    auto.
  Qed.
  Hint Resolve has_opt_type_None : core.

  Lemma has_opt_type_None_skip :
    forall G e,
      has_opt_type G e None ->
      has_opt_type (None :: G) e None.
  Proof.
    unfold has_opt_type.
    auto.
  Qed.
  Hint Resolve has_opt_type_None_skip : core.

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
  Hint Resolve has_opt_type_Some_intro : core.

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

  Lemma Forall3_has_opt_type_Forall2_empty_if_None :
    forall Gs rho G,
      Forall3 has_opt_type Gs rho G ->
      Forall2 empty_if_None Gs G.
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
      try solve [eauto using joinable.splice_empty, join.splice_empty].
    - constructor. now auto using is_singleton_splice.
    - constructor. apply IHt with (n := S n).
    - econstructor; [| |now eauto| apply IHt2 with (n := S (S n))];
        eauto using joinable.splice_empty, join.splice_empty.
    - econstructor; [| |now eauto|apply IHt2 with (n := S n)|apply IHt3 with (n := S n)];
        eauto using joinable.splice_empty, join.splice_empty.
    - constructor. now apply is_empty_splice.
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

  Lemma shift_cons2 :
    forall G e ty,
      t G e ty ->
      t (None :: None :: G) (expr.shift 0 2 e) ty.
  Proof.
    intros.
    now apply shift' with (n := 2).
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

  Lemma shift_cons_opt_None2 :
    forall G e ty,
      has_opt_type G e ty ->
      has_opt_type (None :: None :: G) (expr.shift 0 2 e) ty.
  Proof.
    unfold has_opt_type.
    intros G e [ty|] H; [|now idtac].
    now apply shift_cons2.
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

  Local Definition FHO := Forall3_has_opt_type_Forall2_empty_if_None.

  Lemma has_opt_type_extend :
    forall Gs rho G n ty,
      Forall3 has_opt_type Gs rho G ->
      Forall3 has_opt_type
              ((Some ty :: empty n) :: map (fun G => None :: G) Gs)
              (expr.var 0 :: map (expr.shift 0 1) rho)
              (Some ty :: G).
  Proof.
    intros Gs rho G n ty F.
    constructor.
    now simpl; auto.
    eauto using Forall3_map1, Forall3_map2, Forall3_impl, shift_cons_opt_None.
  Qed.

  Lemma has_opt_type_extend2 :
    forall Gs rho G n ty1 ty2,
      Forall3 has_opt_type Gs rho G ->
      Forall3 has_opt_type
              ((Some ty1 :: empty (S n)) :: (None :: Some ty2 :: empty n) :: map (fun G => None :: None :: G) Gs)
              (expr.var 0 :: expr.var 1 :: map (expr.shift 0 2) rho)
              (Some ty1 :: Some ty2 :: G).
  Proof.
    intros Gs rho G n ty F.
    constructor.
    now simpl; auto.
    constructor.
    now simpl; auto.
    eauto using Forall3_map1, Forall3_map2, Forall3_impl, shift_cons_opt_None2.
  Qed.

  Lemma Forall3_project1 :
    forall Gs rho G G1 G2 n,
      joinable G1 G2 ->
      join G1 G2 = G ->
      Forall3 has_opt_type Gs rho G ->
      Forall3 has_opt_type (project (empty n) G1 Gs) rho G1.
  Proof.
    intros.
    erewrite <- join.project1 by eauto.
    auto using Forall3_project.
  Qed.

  Lemma Forall3_project2 :
    forall Gs rho G G1 G2 n,
      joinable G1 G2 ->
      join G1 G2 = G ->
      Forall3 has_opt_type Gs rho G ->
      Forall3 has_opt_type (project (empty n) G2 Gs) rho G2.
  Proof.
    intros.
    erewrite <- join.project2 by eauto.
    auto using Forall3_project.
  Qed.

  Create HintDb subst_db.
  Hint Resolve big_join.extend has_opt_type_extend big_joinable.extend
               big_join.extend2 has_opt_type_extend2 big_joinable.extend2
               big_joinable.project big_join.project_joinable
               big_join.length big_joinable.project eq_sym
               big_join.project_join FHO Forall3_project1 Forall3_project2
     : subst_db.

  Lemma subst :
    forall G e ty,
      has_type.t G e ty ->
      forall G' Gs rho n,
        Forall3 has_opt_type Gs rho G ->
        big_joinable n Gs ->
        big_join n Gs = G' ->
        has_type.t G' (expr.subst rho e) ty.
  Proof.
    induction 1; intros G' Gs rho n F BJA BJ; cbn [expr.subst]; eauto.
    - simpl expr.subst.
      pose proof is_singleton_nth_error1 _ _ _ H as NEty.
      destruct (Forall3_nth_error3 _ F NEty) as [G1 [e [NEG1 [NEe HT]]]].
      unfold expr.t in *.
      apply has_opt_type_Some in HT.
      rewrite NEe.
      erewrite big_join.is_singleton in BJ; eauto using FHO.
      congruence.
    - apply abs; eapply IHt; subst; eauto with subst_db.
    - eapply app with (G1 := big_join n (project (empty n) G1 Gs));
        [| |eapply IHt1|eapply IHt2];
        subst; eauto 5 with subst_db.
    - eapply both with (G1 := big_join n (project (empty n) G1 Gs));
        [| |eapply IHt1|eapply IHt2];
        subst; eauto with subst_db.
    - eapply let_pair with (G1 := big_join n (project (empty n) G1 Gs));
        [| |eapply IHt1|eapply IHt2];
        subst; eauto with subst_db.
    - eapply case with (G1 := big_join n (project (empty n) G1 Gs));
        [| | eapply IHt1| eapply IHt2 | eapply IHt3]; subst; eauto with subst_db.
    - apply tt.
      erewrite big_join.is_empty in BJ; eauto using FHO.
      now subst.
    - eapply let_tt with (G1 := big_join n (project (empty n) G1 Gs));
        [| |eapply IHt1|eapply IHt2];
        subst; eauto with subst_db.
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
  Hint Constructors t : core.

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

  Hint Resolve star_app2 star_app1 star_refl : core.
End step.

Ltac break_join :=
 match goal with
 | [ H : join _ _ = [] |- _ ] =>
   apply join.nil_elim in H;
   destruct H; subst
 end.

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
    eapply has_type.subst with (n := 0); eauto.
Qed.
