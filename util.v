Require Export List Arith Omega.
Require Export Relations.Relations.

Export ListNotations.
Set Implicit Arguments.

Hint Constructors Forall Forall2 : core.

Ltac break_match :=
  match goal with
  | [  |- context [ match ?X with _ => _ end ] ] => destruct X eqn:?
  | [ H : context [ match ?X with _ => _ end ] |- _ ] => destruct X eqn:?
  end.

Ltac invc H :=
  inversion H; subst; clear H.

Lemma nth_error_map :
  forall A B (f : A -> B) n l,
    nth_error (map f l) n =
    match nth_error l n with
    | None => None
    | Some x => Some (f x)
    end.
Proof.
  induction n; intros; destruct l; simpl in *; auto.
Qed.

Lemma Forall_map :
  forall A B (f : A -> B) P l,
    Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
  intros A B f P l.
  split.
  - induction l; simpl; intuition.
    invc H. constructor; auto.
  - induction 1; simpl; constructor; auto.
Qed.

Lemma Forall2_nth_error2 :
  forall {A B} {P : A -> B -> Prop} {l1 l2 x y},
    List.Forall2 P l1 l2 ->
    List.nth_error l2 x = Some y ->
    exists z,
      List.nth_error l1 x = Some z /\
      P z y
.
Proof.
  intros A B P l1 l2 x y F.
  revert x y.
  induction F as [|a b l1' l2' HR F']; intros x y NE; destruct x; simpl in *; try discriminate.
  - invc NE. eauto.
  - auto.
Qed.

Lemma Forall2_nth_error1 :
  forall {A B} {P : A -> B -> Prop} {l1 l2 x y},
    List.Forall2 P l1 l2 ->
    List.nth_error l1 x = Some y ->
    exists z,
      List.nth_error l2 x = Some z /\
      P y z
.
Proof.
  intros A B P l1 l2 x y F.
  revert x y.
  induction F as [|a b l1' l2' HR F']; intros x y NE; destruct x; simpl in *; try discriminate.
  - invc NE. eauto.
  - auto.
Qed.

Lemma Forall2_nth_error :
  forall {A B} {P : A -> B -> Prop} {l1 l2 x y z},
    List.Forall2 P l1 l2 ->
    List.nth_error l1 x = Some y ->
    List.nth_error l2 x = Some z ->
    P y z
.
Proof.
  intros A B P l1 l2 x y z F.
  revert x y z.
  induction F as [|a b l1' l2' HR F']; intros x y z NEy NEz;
    destruct x; simpl in *; try discriminate.
  - congruence.
  - eauto.
Qed.

Lemma Forall2_map_l :
  forall A B (P : A -> B -> Prop) A' (f : A' -> A) l1 l2,
    List.Forall2 (fun x => P (f x)) l1 l2 ->
    List.Forall2 P (List.map f l1) l2
.
Proof.
  induction 1; simpl; constructor; auto.
Qed.

Lemma Forall2_from_forall :
  forall A B (P : A -> B -> Prop) l1 l2,
    length l1 = length l2 ->
    (forall x y z,
        List.nth_error l1 x = Some y ->
        List.nth_error l2 x = Some z ->
        P y z) ->
    List.Forall2 P l1 l2.
Proof.
  induction l1; destruct l2; simpl; intros L HP; try omega; constructor.
  - now apply HP with (x := 0).
  - apply IHl1.
    + congruence.
    + intros x y z NE1 NE2.
      now apply HP with (x := (S x)).
Qed.

Lemma nth_error_app1 :
  forall A (l1 l2 : list A) x,
    x < List.length l1 ->
    nth_error (l1 ++ l2) x = nth_error l1 x
.
Proof.
  induction l1; intros l2 x H; simpl.
  - invc H.
  - destruct x.
    + reflexivity.
    + simpl in *.
      apply IHl1.
      omega.
Qed.

Lemma nth_error_app2 :
  forall A (l1 l2 : list A) x,
    List.length l1 <= x ->
    nth_error (l1 ++ l2) x = nth_error l2 (x - List.length l1)
.
Proof.
  induction l1; intros l2 x H; destruct x; simpl in *; auto.
  - omega.
  - now rewrite IHl1 by omega.
Qed.

Lemma Forall_nth_error :
  forall A (P : A -> Prop) l n x,
    Forall P l ->
    nth_error l n = Some x ->
    P x.
Proof.
  intros A P l n x F NE.
  revert n x NE.
  induction F; simpl; intros n y NE; destruct n; invc NE; eauto.
Qed.

Lemma Forall2_length :
  forall A B (P : A -> B -> Prop) l1 l2,
    Forall2 P l1 l2 ->
    length l1 = length l2.
Proof.
  induction 1; simpl; auto using f_equal.
Qed.

Section pair_eq_dec.
  Variable A B : Type.
  Hypothesis A_eq_dec : forall (x y : A), {x = y}+{x <> y}.
  Hypothesis B_eq_dec : forall (x y : B), {x = y}+{x <> y}.

  Lemma pair_eq_dec : forall p p' : A * B, {p = p'} + {p <> p'}.
  Proof. decide equality. Defined.
End pair_eq_dec.

Lemma Forall_from_nth :
  forall A (P : A -> Prop) l,
    (forall n x, nth_error l n = Some x -> P x) ->
    Forall P l.
Proof.
  induction l; intros H; constructor.
  - now apply H with (n := 0).
  - apply IHl.
    intros n x Hnx.
    now apply H with (n := (S n)).
Qed.

Lemma Forall2_map :
  forall A B A' B' (P : A -> B -> Prop) (f : A' -> A) (g : B' -> B) l1 l2,
    Forall2 P (map f l1) (map g l2) <-> Forall2 (fun x y => P (f x) (g y)) l1 l2.
Proof.
  intros A B A' B' P f g l1 l2.
  split.
  - revert l2.
    induction l1; destruct l2; simpl; intros F; invc F; constructor; auto.
  - induction 1; simpl; constructor; auto.
Qed.

Lemma Forall2_impl :
  forall A B (P Q : A -> B -> Prop) l1 l2,
    (forall a b, P a b -> Q a b) ->
    Forall2 P l1 l2 ->
    Forall2 Q l1 l2.
Proof.
  intros A B P Q l1 l2 H F.
  induction F; constructor; auto.
Qed.

Lemma app_comm_cons' :
  forall A xs (y : A) zs,
    xs ++ y :: zs = (xs ++ [y]) ++ zs.
Proof.
  intros.
  now rewrite app_ass.
Qed.

Lemma Forall_app :
  forall A (P : A -> Prop) l1 l2,
    Forall P (l1 ++ l2) <-> (Forall P l1 /\ Forall P l2).
Proof.
  induction l1; simpl; intros l2; intuition;
    try match goal with
    | [ H : Forall _ (_ :: _) |- _ ] => invc H
    end; firstorder.
Qed.

Ltac do_ltb :=
  match goal with
  | [ |- context [ if ?x <? ?y then _ else _ ] ] =>
    destruct (Nat.ltb_spec x y)
  | [ H : context [ if ?x <? ?y then _ else _ ] |- _ ] =>
    destruct (Nat.ltb_spec x y)
  end.

Ltac do_app2_minus :=
  match goal with
  | [  |- context [ ?x + ?r2 - ?r1 - ?r2 ] ] =>
    replace (x + r2 - r1 - r2)
    with (x - r1) by omega
  end.

Ltac do_nth_error_Some :=
  match goal with
  | [  |- context [ nth_error ?l ?n] ] => pose proof nth_error_Some l n
  | [ H : context [ nth_error ?l ?n] |- _ ] => pose proof nth_error_Some l n
  end.

Ltac do_max_spec :=
      match goal with
      | [ H : context [ Init.Nat.max ?x ?y ] |- _ ] =>
        pose proof Nat.max_spec x y
      | [ |- context [ Init.Nat.max ?x ?y ] ] =>
        pose proof Nat.max_spec x y
      end.

Section Forall3.
  Variable A B C : Type.
  Variable P : A -> B -> C -> Prop.

  Inductive Forall3 : list A -> list B -> list C -> Prop :=
  | Forall3_nil : Forall3 [] [] []
  | Forall3_cons : forall a b c xs ys zs,
      P a b c ->
      Forall3 xs ys zs ->
      Forall3 (a :: xs) (b :: ys) (c :: zs).

  Lemma Forall3_nth_error1 :
    forall xs ys zs n x,
    Forall3 xs ys zs ->
    nth_error xs n = Some x ->
    exists y z,
      nth_error ys n = Some y /\
      nth_error zs n = Some z /\
      P x y z.
  Proof.
    intros xs ys zs n x F. revert n x.
    induction F; intros n x NE; destruct n; simpl in *; try discriminate.
    - invc NE. eauto.
    - eauto.
  Qed.

  Lemma Forall3_nth_error2 :
    forall xs ys zs n y,
    Forall3 xs ys zs ->
    nth_error ys n = Some y ->
    exists x z,
      nth_error xs n = Some x /\
      nth_error zs n = Some z /\
      P x y z.
  Proof.
    intros xs ys zs n x F. revert n x.
    induction F; intros n x NE; destruct n; simpl in *; try discriminate.
    - invc NE. eauto.
    - eauto.
  Qed.

  Lemma Forall3_nth_error3 :
    forall xs ys zs n z,
    Forall3 xs ys zs ->
    nth_error zs n = Some z ->
    exists x y,
      nth_error xs n = Some x /\
      nth_error ys n = Some y /\
      P x y z.
  Proof.
    intros xs ys zs n x F. revert n x.
    induction F; intros n x NE; destruct n; simpl in *; try discriminate.
    - invc NE. eauto.
    - eauto.
  Qed.

  Lemma Forall3_length :
    forall xs ys zs,
      Forall3 xs ys zs ->
      length xs = length ys /\
      length xs = length zs.
  Proof.
    induction 1; simpl; intuition.
  Qed.

  Lemma Forall3_length12 :
    forall xs ys zs,
      Forall3 xs ys zs ->
      length xs = length ys.
  Proof.
    intros xs ys zs F.
    now apply Forall3_length in F as [? ?].
  Qed.

  Lemma Forall3_length13 :
    forall xs ys zs,
      Forall3 xs ys zs ->
      length xs = length zs.
  Proof.
    intros xs ys zs F.
    now apply Forall3_length in F as [? ?].
  Qed.

  Lemma Forall3_length23 :
    forall xs ys zs,
      Forall3 xs ys zs ->
      length ys = length zs.
  Proof.
    intros xs ys zs F.
    apply Forall3_length in F as [? ?].
    congruence.
  Qed.
End Forall3.
Hint Constructors Forall3 : core.

Lemma Forall3_map1 :
  forall A A' B C (P : A -> B -> C -> Prop) (f : A' -> A) l1 l2 l3,
    Forall3 (fun x => P (f x)) l1 l2 l3 ->
    Forall3 P (List.map f l1) l2 l3
.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma Forall3_map2 :
  forall A B B' C (P : A -> B -> C -> Prop) (f : B' -> B) l1 l2 l3,
    Forall3 (fun x y => P x (f y)) l1 l2 l3 ->
    Forall3 P l1 (List.map f l2) l3
.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma Forall3_impl :
  forall A B C (P Q : A -> B -> C -> Prop) l1 l2 l3,
    (forall a b c, P a b c -> Q a b c) ->
    Forall3 P l1 l2 l3 ->
    Forall3 Q l1 l2 l3.
Proof.
  intros A B C P Q l1 l2 l3 H.
  induction 1; simpl; auto.
Qed.

Lemma map_inj :
  forall A B (f : A -> B) l1 l2,
    (forall a1 a2, f a1 = f a2 -> a1 = a2) ->
    map f l1 = map f l2 ->
    l1 = l2.
Proof.
  intros A B f l1 l2 Inj.
  revert l1 l2.
  induction l1; destruct l2; simpl; intros; try congruence.
  invc H.
  f_equal; auto.
Qed.

Inductive and3 (P1 P2 P3 : Prop) : Prop :=
  And3 : P1 -> P2 -> P3 -> and3 P1 P2 P3.

Inductive and4 (P1 P2 P3 P4 : Prop) : Prop :=
  And4 : P1 -> P2 -> P3 -> P4 -> and4 P1 P2 P3 P4.

Inductive and5 (P1 P2 P3 P4 P5 : Prop) : Prop :=
  And5 : P1 -> P2 -> P3 -> P4 -> P5 -> and5 P1 P2 P3 P4 P5.

Inductive or3 (P1 P2 P3 : Prop) : Prop := Or31 : P1 -> or3 P1 P2 P3
                                  | Or32 : P2 -> or3 P1 P2 P3
                                  | Or33 : P3 -> or3 P1 P2 P3.

Inductive or4 (P1 P2 P3 P4 : Prop) : Prop := Or41 : P1 -> or4 P1 P2 P3 P4
                                     | Or42 : P2 -> or4 P1 P2 P3 P4
                                     | Or43 : P3 -> or4 P1 P2 P3 P4
                                     | Or44 : P4 -> or4 P1 P2 P3 P4.

Notation "[ /\ P1 & P2 ]" := (and P1 P2) (only parsing) : type_scope.
Notation "[ /\ P1 , P2 & P3 ]" := (and3 P1 P2 P3) : type_scope.
Notation "[ /\ P1 , P2 , P3 & P4 ]" := (and4 P1 P2 P3 P4) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 & P5 ]" := (and5 P1 P2 P3 P4 P5) : type_scope.

Notation "[ \/ P1 | P2 ]" := (or P1 P2) (only parsing) : type_scope.
Notation "[ \/ P1 , P2 | P3 ]" := (or3 P1 P2 P3) : type_scope.
Notation "[ \/ P1 , P2 , P3 | P4 ]" := (or4 P1 P2 P3 P4) : type_scope.

Lemma nth_error_shift :
  forall A (l1 l2 l3 : list A) n,
    nth_error (l1 ++ l2 ++ l3) (if n <? length l1 then n else n + length l2) =
    nth_error (l1 ++ l3) n.
Proof.
  intros A l1 l2 l3 n.
  destruct (Nat.ltb_spec n (length l1)).
  - now rewrite !nth_error_app1 by assumption.
  - rewrite !nth_error_app2 by omega.
    f_equal. omega.
Qed.


(*
          xs     |   zs
    ----------------------
      xs' |     zs'

   xs = xs' ++ W
   zs' = W ++ zs
 *)

Lemma app_inv :
  forall A (xs zs xs' zs' : list A),
    xs ++ zs = xs' ++ zs' ->
    [\/ exists W,
        [/\ xs = xs' ++ W
         & zs' = W ++ zs]
    | exists W,
      [/\ xs' = xs ++ W
       & zs = W ++ zs']].
Proof.
  induction xs; simpl; intros zs xs' zs' H.
  - subst. eauto.
  - destruct xs'; simpl in *.
    + destruct zs'; invc H.
      eauto.
    + invc H.
      apply IHxs in H2.
      destruct H2 as [[W [? ?]]|[W [? ?]]]; subst; eauto.
Qed.


Lemma app_singleton_inv :
  forall A (x : A) xs ys,
    [x] = xs ++ ys ->
    [\/ xs = [x] /\ ys = []
    | xs = [] /\ ys = [x]].
Proof.
  intros A x xs ys H.
  destruct xs; auto.
  destruct xs.
  destruct ys; try discriminate.
  auto.
  discriminate.
Qed.

Lemma app_singleton_middle_inv :
  forall A (x x' : A) xs ys,
    [x] = xs ++ x' :: ys ->
    [/\ x = x'
     , xs = []
     & ys = []].
Proof.
  intros A x x' xs ys H.
  apply app_singleton_inv in H.
  destruct H as [[? ?]|[? ?]]; subst.
  - discriminate.
  - invc H0. split; auto.
Qed.

Lemma app_cons_inv :
  forall A (x : A) ys xs' ys',
    x :: ys = xs' ++ ys' ->
    [\/ [/\ [] = xs' & ys' = x :: ys]
    | exists W, [/\ xs' = [x] ++ W & ys = W ++ ys']].
Proof.
  intros A x ys xs' ys' H.
  replace (x :: ys) with ([x] ++ ys) in H by reflexivity.
  apply app_inv in H.
  destruct H as [[W1 [? ?]] | [W1 [? ?]]]; subst; firstorder.
  - apply app_singleton_inv in H.
    intuition; subst; auto.
    right. exists []. auto.
  - right. exists W1. auto.
Qed.

Lemma app_middle_inv :
  forall A y y' (xs zs xs' zs' : list A),
    xs ++ y :: zs = xs' ++ y' :: zs' ->
    [\/ [/\ xs = xs'
        , y = y'
          & zs = zs']
     , exists W,
        [/\ xs = xs' ++ y' :: W
         & zs' = W ++ y :: zs]
    | exists W,
      [/\ xs' = xs ++ y :: W
       & zs = W ++ y' :: zs']].
Proof.
  intros A y y' xs zs xs' zs' H.
  apply app_inv in H.
  destruct H as [[W [? ?]]|[W [? ?]]]; subst.
  - apply app_cons_inv in H0.
    destruct H0 as [[? ?]|[W' [? ?]]]; subst.
    + invc H0. constructor 1. rewrite app_nil_r. split; auto.
    + constructor 2. exists W'. split; auto.
  - apply app_cons_inv in H0.
    destruct H0 as [[? ?]|[W' [? ?]]]; subst.
    + invc H0. constructor 1. rewrite app_nil_r. split; auto.
    + constructor 3. exists W'. split; auto.
Qed.

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

Fixpoint splice A n (l' l : list A) :=
  match n with
  | 0 => l' ++ l
  | S n =>
    match l with
    | [] => l' (* bogus *)
    | x :: l => x :: splice n l' l
    end
  end.


Module partial_zip.
Section partial_zip.
  Variable A B C : Type.
  Variable one : A -> B -> option C.

  Fixpoint f l1 l2 :=
    match l1, l2 with
    | [], [] => Some []
    | x :: l1, y :: l2 =>
      match one x y, f l1 l2 with
      | Some z, Some l => Some (z :: l)
      | _, _ => None
      end
    | _, _ => None
    end.

  Lemma nil :
    f [] [] = Some [].
  Proof.
    reflexivity.
  Qed.

  Lemma nil_inv :
    forall l1 l2,
      f l1 l2 = Some [] ->
      l1 = [] /\ l2 = [].
  Proof.
    now destruct l1, l2; simpl; repeat break_match; try discriminate.
  Qed.

  Lemma length1 :
    forall l1 l2 l3,
      f l1 l2 = Some l3 ->
      length l3 = length l1.
  Proof.
    induction l1; destruct l2; simpl; intros l3 F; try discriminate.
    - invc F. reflexivity.
    - repeat break_match; try discriminate.
      invc F. simpl.
      eauto using f_equal.
  Qed.

  Lemma length2 :
    forall l1 l2 l3,
      f l1 l2 = Some l3 ->
      length l3 = length l2.
  Proof.
    induction l1; destruct l2; simpl; intros l3 F; try discriminate.
    - invc F. reflexivity.
    - repeat break_match; try discriminate.
      invc F. simpl.
      eauto using f_equal.
  Qed.

  Lemma app :
    forall l1 l2 l3 l1' l2' l3',
      f l1 l2 = Some l3 ->
      f l1' l2' = Some l3' ->
      f (l1 ++ l1') (l2 ++ l2') = Some (l3 ++ l3').
  Proof.
    induction l1; simpl; intros l2 l3 l1' l2' l3' F F'; destruct l2; try discriminate; simpl.
    - invc F. auto.
    - destruct one; [|discriminate].
      destruct f eqn:F2; [|discriminate].
      invc F.
      now erewrite IHl1 by eauto.
  Qed.

  Lemma splice :
    forall n l1 l2 l3 l1' l2' l3',
      f l1 l2 = Some l3 ->
      f l1' l2' = Some l3' ->
      f (splice n l1 l1') (splice n l2 l2') = Some (splice n l3 l3').
  Proof.
    induction n; simpl; intros l1 l2 l3 l1' l2' l3' F F'.
    - auto using app.
    - destruct l1', l2'; simpl in F' |- *; try discriminate.
      + now invc F'.
      + destruct one; [|discriminate].
        destruct (f l1' l2') eqn:F2; [|discriminate].
        invc F'.
        now erewrite IHn by eauto.
  Qed.
End partial_zip.
  Lemma id_l :
    forall A B (one : A -> B -> option B) a0,
      (forall b, one a0 b = Some b) ->
      forall l,
        f one (repeat a0 (length l)) l = Some l.
  Proof.
    intros A B one a0 id.
    induction l; simpl; auto.
    now rewrite id, IHl.
  Qed.

  Lemma comm :
    forall A B (one : A -> A -> option B),
      (forall x y, one x y = one y x) ->
      forall l1 l2,
        f one l1 l2 = f one l2 l1.
  Proof.
    intros A B one C.
    induction l1; destruct l2; simpl; auto.
    rewrite C.
    destruct one; auto.
    rewrite IHl1.
    destruct f; auto.
  Qed.

  Lemma assoc :
    forall A (one : A -> A -> option A),
    (forall a1 a2 b,
        match one a1 b with
        | Some b' => one a2 b'
        | None => None
        end = match one a2 b with
              | Some b' => one a1 b'
              | None => None
              end) ->
    forall a1 a2 b,
        match f one a1 b with
        | Some b' => f one a2 b'
        | None => None
        end = match f one a2 b with
              | Some b' => f one a1 b'
              | None => None
              end.
  Proof.
    intros A one Step a1.
    induction a1; destruct a2, b; simpl; auto.
    - repeat break_match; congruence.
    - repeat break_match; congruence.
    - specialize (Step a a0 a3).
      specialize (IHa1 a2 b).
      destruct (one a a3) eqn:?.
      destruct (f one a1 b) eqn:?.
      rewrite Step.
      repeat break_match; congruence.
      repeat break_match; congruence.
      repeat break_match; congruence.
  Qed.
End partial_zip.

Module partial_fold_left.
Section partial_fold_left.
  Variable A B : Type.
  Variable step : A -> B -> option B.

  Fixpoint f acc l :=
    match l with
    | [] => Some acc
    | x :: l =>
      match step x acc with
      | None => None
      | Some acc => f acc l
      end
    end.

  Lemma push_step :
    (forall a1 a2 b,
      match step a1 b with
      | None => None
      | Some b' => step a2 b'
      end
      =
      match step a2 b with
      | None => None
      | Some b' => step a1 b'
      end) ->
    forall x l acc,
      match step x acc with
      | None => None
      | Some acc' => f acc' l
      end
      =
      match f acc l with
      | None => None
      | Some acc'' => step x acc''
      end.
  Proof.
    intros Swap.
    induction l; intros acc; simpl; [break_match; reflexivity|].
    pose proof Swap x a acc as Swap_ax.
    specialize (IHl (match step a acc with
                     | None => acc
                     | Some acc' => acc'
                     end)).
    repeat break_match; congruence.
  Qed.

  Lemma distr :
    forall (mulA : A -> A) (mulB : B -> B),
      (forall a b,
          step (mulA a) (mulB b) =
          match step a b with
          | Some b' => Some (mulB b')
          | None => None
          end) ->
      forall l acc,
        f (mulB acc) (map mulA l) =
        match f acc l with
        | Some b => Some (mulB b)
        | None => None
        end.
  Proof.
    intros mulA mulB Distr.
    induction l; intros acc; simpl; [reflexivity|].
    rewrite Distr.
    destruct step; auto.
  Qed.

  Lemma ind_Some :
    forall (P : A -> Prop) (Q : B -> Prop),
      (forall a b b', P a -> Q b -> step a b = Some b' -> Q b') ->
      forall l b b',
        Forall P l ->
        Q b ->
        f b l = Some b' ->
        Q b'.
  Proof.
    intros P Q H.
    induction l; cbn; intros b b' All HQ F.
    - now invc F.
    - invc All.
      destruct step eqn:Step; [|discriminate].
      eauto.
  Qed.
End partial_fold_left.
End partial_fold_left.

Section project.
  Variable A B : Type.
  Variable default : B.
  Fixpoint project (l1 : list (option A)) (l2 : list B) : list B :=
    match l2 with
    | [] => []
    | x :: l2 =>
      match l1 with
      | [] => default :: project l1 l2
      | None :: l1 => default :: project l1 l2
      | Some _ :: l1 => x :: project l1 l2
      end
    end.
End project.

Lemma Forall_project :
  forall F A (P : A -> Prop) d,
    P d ->
    forall l1,
      Forall P l1 ->
      forall l : list (option F),
        Forall P (project d l l1).
Proof.
  intros F A P d Pd.
  induction 1; intros xs; cbn.
  - constructor.
  - destruct xs as [|[|]]; auto.
Qed.

Lemma Forall3_project :
  forall F A B C (P : A -> B -> C -> Prop) (dA : A) (dC: C),
    (forall b, P dA b dC) ->
    forall l1 l2 l3,
      Forall3 P l1 l2 l3 ->
      forall (l : list (option F)),
        Forall3 P (project dA l l1) l2 (project dC l l3).
Proof.
  intros F A B C P dA dC D.
  induction 1; simpl.
  - constructor.
  - destruct l; [now auto|].
    destruct o; auto.
Qed.
Hint Resolve Forall3_project : core.

Lemma partial_zip_project :
  forall A B (f : option A -> B -> option (option A)) l1 l2 l3,
    (forall a b o, f (Some a) b = Some o -> o = Some a) ->
    partial_zip.f f l1 l2 = Some l3 ->
    project None l1 l3 = l1.
Proof.
  induction l1; destruct l2; simpl; intros l3 F EQ.
  - invc EQ. reflexivity.
  - discriminate.
  - discriminate.
  - destruct f eqn:EF; [|discriminate].
    destruct partial_zip.f eqn:EPZ; [|discriminate].
    invc EQ.
    simpl.
    destruct a eqn:EQa.
    + apply F in EF. subst. eauto using f_equal.
    + eauto using f_equal.
Qed.

Lemma ForallOrdPairs_map :
  forall A B (f : A -> B) (P : B -> B -> Prop) l,
    ForallOrdPairs (fun a1 a2 => P (f a1) (f a2)) l ->
    ForallOrdPairs P (map f l).
Proof.
  induction 1; cbn; constructor; auto.
  now apply Forall_map.
Qed.

Lemma ForallOrdPairs_impl :
  forall A (P Q : A -> A -> Prop) l,
    (forall a1 a2, P a1 a2 -> Q a1 a2) ->
    ForallOrdPairs P l ->
    ForallOrdPairs Q l.
Proof.
  intros A P Q l I F.
  induction F; constructor; auto.
  now eapply Forall_impl; try apply I.
Qed.

Module zip.
Section zip.
  Variable A B C : Type.
  Variable f : A -> B -> C.

  Fixpoint zip l1 l2 :=
    match l1, l2 with
    | [], [] => []
    | x :: l1, y :: l2 => f x y :: zip l1 l2
    | _, _ => [] (* bogus *)
    end.
End zip.
End zip.
Notation zip := zip.zip.

Lemma project_unroll :
  forall A B (d : B) (l : list (option A)) b bs,
    project d l (b :: bs) =
    match l with
    | [] | None :: _ => d
    | Some _ :: _ => b
    end ::
        project d (match l with
                   | [] => []
                   | _ :: l => l
                   end) bs.
Proof.
  intros A B d l b bs.
  cbn.
  destruct l as [|[|]]; reflexivity.
Qed.
