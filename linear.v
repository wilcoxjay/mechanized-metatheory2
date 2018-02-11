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

Fixpoint nth_set A (l : list A) (n : nat) (x : A) {struct n} : list A :=
  match n with
  | 0 =>
    match l with
    | [] => []
    | y :: l => x :: l
    end
  | S n =>
    match l with
    | [] => []
    | y :: l => y :: nth_set l n x
    end
  end.

Lemma nth_set_length :
  forall A n (l : list A) x,
    length (nth_set l n x) = length l.
Proof.
  induction n; destruct l; simpl; intros x; auto.
Qed.

Lemma nth_error_nth_set :
  forall A n2 n1 (l : list A) x,
    n1 < List.length l ->
    nth_error (nth_set l n1 x) n2 =
    if Nat.eq_dec n1 n2 then Some x else nth_error l n2.
Proof.
  induction n2; destruct n1; destruct l; intros x LT; simpl in *;
    try reflexivity;
    try omega.
  rewrite IHn2 by omega.
  destruct Nat.eq_dec; auto.
Qed.

Module has_type.
  Inductive t : list (option type.t) -> expr.t -> type.t -> list (option type.t) -> Prop :=
  | var : forall G x ty,
      List.nth_error G x = Some (Some ty) ->
      t G (expr.var x) ty (nth_set G x None)
  | abs : forall G e ty1 ty2 G',
      t (Some ty1 :: G) e ty2 (None :: G') ->
      t G (expr.abs e) (type.lolli ty1 ty2) G'
  | app : forall G G' G'' e1 e2 ty1 ty2,
      t G e1 (type.lolli ty1 ty2) G' ->
      t G' e2 ty1 G'' ->
      t G (expr.app e1 e2) ty2 G''
  | both : forall G G' G'' e1 e2 ty1 ty2,
      t G e1 ty1 G' ->
      t G' e2 ty2 G'' ->
      t G (expr.both e1 e2) (type.tensor ty1 ty2) G''
  | let_pair : forall G G' G'' e1 e2 ty1 ty2 ty,
      t G e1 (type.tensor ty1 ty2) G' ->
      t (Some ty2 :: Some ty1 :: G') e2 ty (None :: None :: G'') ->
      t G (expr.let_pair e1 e2) ty G''
  | oneof : forall G G' e1 e2 ty1 ty2,
      t G e1 ty1 G' ->
      t G e2 ty2 G' ->
      t G (expr.oneof e1 e2) (type.uchoose ty1 ty2) G'
  | fst : forall G G' e ty1 ty2,
      t G e (type.uchoose ty1 ty2) G' ->
      t G (expr.fst e) ty1 G'
  | snd : forall G G' e ty1 ty2,
      t G e (type.uchoose ty1 ty2) G' ->
      t G (expr.snd e) ty2 G'
  | inl : forall G G' e ty1 ty2,
      t G e ty1 G' ->
      t G (expr.inl e) (type.ichoose ty1 ty2) G'
  | inr : forall G G' e ty1 ty2,
      t G e ty2 G' ->
      t G (expr.inr e) (type.ichoose ty1 ty2) G'
  | case : forall G G' G'' e e1 e2 ty1 ty2 ty,
      t G e (type.ichoose ty1 ty2) G' ->
      t (Some ty1 :: G') e1 ty (None :: G'') ->
      t (Some ty2 :: G') e2 ty (None :: G'') ->
      t G (expr.case e e1 e2) ty G''
  | tt : forall G,
      t G expr.tt type.one G
  | let_tt : forall G G' G'' e1 e2 ty,
      t G e1 type.one G' ->
      t G' e2 ty G'' ->

      t G (expr.let_tt e1 e2) ty G''
  .

  Lemma length :
    forall G e ty G',
      t G e ty G' ->
      length G = length G'.
  Proof.
    induction 1; simpl in *; try congruence.
    now rewrite nth_set_length.
  Qed.

  Lemma subctx :
    forall G e ty G',
      t G e ty G' ->
      forall n tyn,
        nth_error G' n = Some (Some tyn) ->
        nth_error G n = Some (Some tyn).
  Proof.
    induction 1; intros n tyn HG'; simpl in *; auto.
    - rewrite nth_error_nth_set in HG' by (rewrite <- nth_error_Some; congruence).
      break_match; [discriminate|assumption].
    - now apply IHt with (n := S n).
    - apply IHt1.
      now apply IHt2 with (n := (S (S n))).
    - apply IHt1.
      now apply IHt2 with (n := (S n)).
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
  forall G e ty G',
    has_type.t G e ty G' ->
    G = [] ->
    G' = [] ->
    forall e',
      step.t e e' ->
      has_type.t [] e' ty [].
Proof.
  induction 1; intros ? ? e' Step; subst; invc Step.
  - assert (G' = [])
      by (rewrite <- length_zero_iff_nil;
          now erewrite <- has_type.length by eauto).
    subst G'.
Admitted.
