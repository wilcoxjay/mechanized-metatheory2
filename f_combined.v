From mm Require Import util abt abtutil.

Module op.
  Inductive t' :=
  | arrow
  | all
  | bool

  | abs
  | app
  | tyabs
  | tyapp
  | tt
  | ff
  | If
  .
  Definition t := t'.

  Definition arity (op : t) : arity.t :=
    match op with
    | arrow => [0; 0]
    | all => [1]
    | bool => []

    | abs => [0; 1]
    | app => [0; 0]
    | tyabs => [1]
    | tyapp => [0; 0]
    | tt => []
    | ff => []
    | If => [0; 0; 0]
    end.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
  Defined.
End op.

Module abt := abt.abt op.

Module ast.
  Inductive t :=
  | var (x : nat) : t
  | arrow : t -> t -> t
  | all : t -> t
  | bool : t
  | abs : t -> t -> t
  | app : t -> t -> t
  | tyabs : t -> t
  | tyapp : t -> t -> t
  | tt : t
  | ff : t
  | If : t -> t -> t -> t
  .
End ast.

Module basis.
  Module A := abt.

  Import ast.
  Definition t := t.

  Fixpoint to_abt (term : t) : A.t :=
    match term with
    | var n => A.var n
    | arrow ty1 ty2 => A.op op.arrow [A.bind 0 (to_abt ty1); A.bind 0 (to_abt ty2)]
    | all ty => A.op op.all [A.bind 1 (to_abt ty)]
    | bool => A.op op.bool []
    | abs ty e => A.op op.abs [A.bind 0 (to_abt ty); A.bind 1 (to_abt e)]
    | app e1 e2 => A.op op.app [A.bind 0 (to_abt e1); A.bind 0 (to_abt e2)]
    | tyabs e => A.op op.tyabs [A.bind 1 (to_abt e)]
    | tyapp e ty => A.op op.tyapp [A.bind 0 (to_abt e); A.bind 0 (to_abt ty)]
    | tt => A.op op.tt []
    | ff => A.op op.ff []
    | If e1 e2 e3 => A.op op.If [A.bind 0 (to_abt e1);
                               A.bind 0 (to_abt e2);
                               A.bind 0 (to_abt e3)]
    end.

  Fixpoint of_abt (term : A.t) : t :=
    match term with
    | A.var n => var n
    | A.op op.arrow [A.bind 0 a1; A.bind 0 a2] => arrow (of_abt a1) (of_abt a2)
    | A.op op.all [A.bind 1 a'] => all (of_abt a')
    | A.op op.bool [] => bool
    | A.op op.abs [A.bind 0 a_ty; A.bind 1 a_e] => abs (of_abt a_ty) (of_abt a_e)
    | A.op op.app [A.bind 0 a1; A.bind 0 a2] => app (of_abt a1) (of_abt a2)
    | A.op op.tyabs [A.bind 1 a'] => tyabs (of_abt a')
    | A.op op.tyapp [A.bind 0 a_e; A.bind 0 a_ty] => tyapp (of_abt a_e) (of_abt a_ty)
    | A.op op.tt [] => tt
    | A.op op.ff [] => ff
    | A.op op.If [A.bind 0 a1; A.bind 0 a2; A.bind 0 a3] =>
      If (of_abt a1) (of_abt a2) (of_abt a3)
    | _ => var 0 (* bogus *)
    end.

  Fixpoint t_map ov c (term : t) : t :=
    match term with
    | var x => ov c x
    | arrow ty1 ty2 => arrow (t_map ov c ty1) (t_map ov c ty2)
    | all ty => all (t_map ov (S c) ty)
    | bool => bool
    | abs ty e => abs (t_map ov c ty) (t_map ov (S c) e)
    | app e1 e2 => app (t_map ov c e1) (t_map ov c e2)
    | tyabs e => tyabs (t_map ov (S c) e)
    | tyapp e ty => tyapp (t_map ov c e) (t_map ov c ty)
    | tt => tt
    | ff => ff
    | If e1 e2 e3 => If (t_map ov c e1) (t_map ov c e2) (t_map ov c e3)
    end.

  Fixpoint shift c d (term : t) : t :=
    match term with
    | var alpha => var (if alpha <? c then alpha else alpha + d)
    | arrow ty1 ty2 => arrow (shift c d ty1) (shift c d ty2)
    | all ty => all (shift (S c) d ty)
    | bool => bool
    | abs ty e => abs (shift c d ty) (shift (S c) d e)
    | app e1 e2 => app (shift c d e1) (shift c d e2)
    | tyabs e => tyabs (shift (S c) d e)
    | tyapp e ty => tyapp (shift c d e) (shift c d ty)
    | tt => tt
    | ff => ff
    | If e1 e2 e3 => If (shift c d e1) (shift c d e2) (shift c d e3)
    end.

  Fixpoint subst rho term :=
    match term with
    | var alpha => match nth_error rho alpha with
                  | Some ty' => ty'
                  | None => term
                  end
    | arrow ty1 ty2 => arrow (subst rho ty1) (subst rho ty2)
    | all ty => all (subst (var 0 :: map (shift 0 1) rho) ty)
    | bool => bool
    | abs ty e => abs (subst rho ty) (subst (var 0 :: map (shift 0 1) rho) e)
    | app e1 e2 => app (subst rho e1) (subst rho e2)
    | tyabs e => tyabs (subst (var 0 :: map (shift 0 1) rho) e)
    | tyapp e ty => tyapp (subst rho e) (subst rho ty)
    | tt => tt
    | ff => ff
    | If e1 e2 e3 => If (subst rho e1) (subst rho e2) (subst rho e3)
    end.

  Fixpoint wf n term :=
    match term with
    | var alpha => alpha < n
    | arrow ty1 ty2 => wf n ty1 /\ wf n ty2
    | all ty => wf (S n) ty
    | bool => True
    | abs ty e => wf n ty /\ wf (S n) e
    | app e1 e2 => wf n e1 /\ wf n e2
    | tyabs e => wf (S n) e
    | tyapp e ty => wf n e /\ wf n ty
    | tt => True
    | ff => True
    | If e1 e2 e3 => wf n e1 /\ wf n e2 /\ wf n e3
    end.

  Fixpoint identity_subst (n : nat) : list t :=
    match n with
    | 0 => []
    | S n => var 0 :: map (shift 0 1) (identity_subst n)
    end.

  Lemma ws_to_abt : forall e, A.ws (to_abt e).
  Proof. A.basis_util.prove_ws_to_abt. Qed.

  Lemma of_to_abt : forall e, of_abt (to_abt e) = e.
  Proof. A.basis_util.prove_of_to_abt. Qed.

  Lemma to_of_abt : forall a, A.ws a -> to_abt (of_abt a) = a.
  Proof. A.basis_util.prove_to_of_abt to_abt of_abt. Qed.

  Lemma t_map_to_abt_comm : forall ov e c,
      to_abt (t_map ov c e) = A.t_map (fun c x => to_abt (ov c x)) c (to_abt e).
  Proof. A.basis_util.prove_t_map_to_abt_comm. Qed.

  Lemma shift_to_abt_comm : forall e c d, to_abt (shift c d e) = A.shift c d (to_abt e).
  Proof. A.basis_util.prove_shift_to_abt_comm. Qed.

  Lemma map_shift_to_abt_comm :
    forall c d rho, map to_abt (map (shift c d) rho) = map (A.shift c d) (map to_abt rho).
  Proof. A.basis_util.prove_map_shift_to_abt_comm shift_to_abt_comm. Qed.

  Lemma subst_to_abt_comm : forall e rho,
      to_abt (subst rho e) = A.subst (map to_abt rho) (to_abt e).
  Proof. A.basis_util.prove_subst_to_abt_comm t map_shift_to_abt_comm. Qed.

  Lemma wf_to_abt : forall e n, wf n e <-> A.wf n (to_abt e).
  Proof. A.basis_util.prove_wf_to_abt. Qed.

  Lemma identity_subst_to_abt_comm :
    forall n, List.map to_abt (identity_subst n) = A.identity_subst n.
  Proof. A.basis_util.prove_identity_subst_to_abt_comm map_shift_to_abt_comm. Qed.

  Definition var := var.
  Arguments var /.
  Lemma var_to_abt : forall n, to_abt (var n) = A.var n.
  Proof. reflexivity. Qed.
End basis.

Module term.
  Include abt_util basis.
  Notation arrow := ast.arrow.
  Notation all := ast.all.
  Notation bool := ast.bool.
  Notation abs := ast.abs.
  Notation app := ast.app.
  Notation tyabs := ast.tyabs.
  Notation tyapp := ast.tyapp.
  Notation tt := ast.tt.
  Notation ff := ast.ff.
  Notation If := ast.If.
End term.

Module cat.
  Inductive t := TYPE | EXPR.
End cat.

Module wc.
  Inductive t : list cat.t -> term.t -> cat.t -> Prop :=
  | var : forall C n c,
      nth_error C n = Some c ->
      t C (term.var n) c
  | arrow : forall C t1 t2,
      t C t1 cat.TYPE ->
      t C t2 cat.TYPE ->
      t C (term.arrow t1 t2) cat.TYPE
  | all : forall C ty,
      t (cat.TYPE :: C) ty cat.TYPE ->
      t C (term.all ty) cat.TYPE
  | bool : forall C,
      t C ast.bool cat.TYPE
  | abs : forall C ty e,
      t C ty cat.TYPE ->
      t (cat.EXPR :: C) e cat.EXPR ->
      t C (term.abs ty e) cat.EXPR
  | app : forall C e1 e2,
      t C e1 cat.EXPR ->
      t C e2 cat.EXPR ->
      t C (term.app e1 e2) cat.EXPR
  | tyabs : forall C e,
      t (cat.TYPE :: C) e cat.EXPR ->
      t C (term.tyabs e) cat.EXPR
  | tyapp : forall C e ty,
      t C e cat.EXPR ->
      t C ty cat.TYPE ->
      t C (term.tyapp e ty) cat.EXPR
  | tt : forall C,
      t C term.tt cat.EXPR
  | ff : forall C,
      t C term.ff cat.EXPR
  | If : forall C e1 e2 e3,
      t C e1 cat.EXPR ->
      t C e2 cat.EXPR ->
      t C e3 cat.EXPR ->
      t C (term.If e1 e2 e3) cat.EXPR
  .
  Global Hint Constructors t : core.

  Lemma t_wf :
    forall C e c,
      t C e c ->
      term.wf (length C) e.
  Proof.
    induction 1; cbn; intuition.
    apply nth_error_Some.
    congruence.
  Qed.

  Lemma shift :
    forall C1 C2 C3 e c,
      t (C1 ++ C3) e c ->
      t (C1 ++ C2 ++ C3) (term.shift (length C1) (length C2) e) c.
  Proof.
    intros C1 C2 C3 e c WC.
    revert C2.
    remember (C1 ++ C3) as C eqn:EC in *.
    revert C1 C3 EC.
    induction WC; intros C1 C3 EC C2; subst C; cbn [term.shift]; constructor; auto.
    - now rewrite nth_error_shift.
    - now apply IHWC with (C2 := _ :: _).
    - now apply IHWC2 with (C2 := _ :: _).
    - now apply IHWC with (C2 := _ :: _).
  Qed.

  Lemma shift' :
    forall C e c C',
      t C e c ->
      t (C' ++ C) (term.shift 0 (List.length C') e) c.
  Proof.
    intros.
    now apply shift with (C1 := []).
  Qed.

  Lemma shift_cons :
  forall C e c c',
    t C e c ->
    t (c' :: C) (term.shift 0 1 e) c.
  Proof.
    intros C e c c' HT.
    now apply shift' with (C' := [c']).
  Qed.

  Lemma t_skipn_shift :
    forall C e c n,
      n <= length C ->
      t (skipn n C) e c ->
      t C (term.shift 0 n e) c.
  Proof.
    intros C e c n L T.
    rewrite <- firstn_skipn with (n := n) (l := C).
    apply shift' with (C' := firstn n C) in T.
    now rewrite firstn_length_le in * by assumption.
  Qed.

  Lemma shift_inv :
  forall e C1 C2 C3 c,
    t (C1 ++ C2 ++ C3) (term.shift (length C1) (length C2) e) c ->
    t (C1 ++ C3) e c.
  Proof.
    induction e; intros C1 C2 C3 c HT; invc HT; constructor; eauto.
    - now rewrite nth_error_shift in *.
    - eapply IHe with (C1 := _ :: _); eauto.
    - eapply IHe2 with (C1 := _ :: _); eauto.
    - eapply IHe with (C1 := _ :: _); eauto.
  Qed.

  Lemma shift_inv' :
    forall C e c C',
      t (C' ++ C) (term.shift 0 (List.length C') e) c ->
      t C e c.
  Proof.
    intros.
    now eapply shift_inv with (C1 := []); eauto.
  Qed.

  Lemma shift_cons_inv :
  forall C e c c',
    t (c' :: C) (term.shift 0 1 e) c ->
    t C e c.
  Proof.
    intros C e c c' HT.
    now apply shift_inv' with (C' := [c']).
  Qed.

  Lemma subst :
    forall C e c,
      t C e c ->
      forall C' rho,
        List.Forall2 (t C') rho C ->
        t C' (term.subst rho e) c.
  Proof.
    induction 1; intros C' rho F; cbn [term.subst]; try constructor;
      eauto 10 using shift_cons, Forall2_impl, Forall2_map_l.
    cbn.
    destruct (Forall2_nth_error2 F H) as [z [Hz Ht]].
    unfold term.t in Hz.
    now rewrite Hz.
  Qed.

  Lemma Forall2_identity_subst :
    forall C n,
      n = length C ->
      Forall2 (t C) (term.identity_subst n) C.
  Proof.
    intros C n ?. subst n.
    induction C; cbn; constructor.
    - auto.
    - apply Forall2_map_l.
      eauto using Forall2_impl, shift_cons.
  Qed.

  Lemma Forall2_t_Forall_wf :
    forall C es tys,
      Forall2 (wc.t C) es tys ->
      Forall (term.wf (length C)) es.
  Proof.
    induction 1; eauto using t_wf.
  Qed.
End wc.

Module ctx_ent.
  Inductive t :=
  | TYVAR
  | EXVAR : term.t -> t
  .

  Definition map (f : term.t -> term.t) (ce : t) : t :=
    match ce with
    | TYVAR => TYVAR
    | EXVAR t => EXVAR (f t)
    end.

  Definition prop (P : term.t -> Prop) (ce : t) : Prop :=
    match ce with
    | TYVAR => True
    | EXVAR t => P t
    end.

  Definition to_cat (ce : t) : cat.t :=
    match ce with
    | TYVAR => cat.TYPE
    | EXVAR _ => cat.EXPR
    end.

  Module exports.
    Notation TYVAR := TYVAR.
    Notation EXVAR := EXVAR.
  End exports.
End ctx_ent.

Module tele.
  Import ctx_ent.exports.

  Definition t := list ctx_ent.t.

  Notation to_cat_ctx T := (map ctx_ent.to_cat T).
  Notation map f := (map (ctx_ent.map f)).

  Fixpoint wf (T : t) : Prop :=
    match T with
    | [] => True
    | ce :: T =>
      wf T /\ ctx_ent.prop (fun ty => wc.t (to_cat_ctx T) ty cat.TYPE) ce
    end.

  Fixpoint shift (c d : nat) (T : t) : t :=
    match T with
    | [] => []
    | ce :: T =>
      match c with
      | 0 => ctx_ent.map (term.shift c d) ce :: shift c d T
      | S c => ctx_ent.map (term.shift c d) ce :: shift c d T
      end
    end.

  Lemma shift_length :
    forall T c d,
      length (shift c d T) = length T.
  Proof.
    induction T; intros [|] d; cbn; auto.
  Qed.

  Definition is_tyvar (T : t) (n : nat) : Prop :=
    nth_error T n = Some TYVAR.

  Definition lookup_exvar (T : t) (n : nat) (expect : term.t) : Prop :=
    exists expect',
      nth_error T n = Some (EXVAR expect') /\
      expect = term.shift 0 (S n) expect'.

  Fixpoint globalize (i : nat) (T : t) : list ctx_ent.t :=
    match T with
    | [] => []
    | ce :: T =>
      ctx_ent.map (term.shift 0 (S i)) ce :: globalize (S i) T
    end.

  Lemma nth_error_globalize :
    forall T i n,
      nth_error (globalize i T) n =
      match nth_error T n with
      | None => None
      | Some e => Some (ctx_ent.map (term.shift 0 (n + S i)) e)
      end.
  Proof.
    induction T; intros i [|n]; cbn; auto.
    rewrite IHT.
    break_match; auto.
    repeat f_equal.
    lia.
  Qed.

  Lemma lookup_exvar_globalize :
    forall T n ty,
      lookup_exvar T n ty ->
      nth_error (globalize 0 T) n = Some (EXVAR ty).
  Proof.
    intros T n ty [ty' [NE ?]].
    subst ty.
    rewrite nth_error_globalize, NE.
    cbn.
    repeat f_equal.
    lia.
  Qed.

  Lemma to_cat_shift :
    forall T c d,
      to_cat_ctx (shift c d T) = to_cat_ctx T.
  Proof.
    unfold ctx_ent.to_cat.
    induction T; cbn [List.map shift]; intros c d.
    - reflexivity.
    - destruct c, a; cbn; f_equal; auto.
  Qed.

  Lemma nth_error_tele_shift_exvar1 :
    forall T c d n ty,
      nth_error (shift c d T) n = Some (EXVAR ty) ->
      exists ty',
        term.shift (c - S n) d ty' = ty /\
        nth_error T n = Some (EXVAR ty').
  Proof.
    induction T; intros [|c] d [|n] ty NE; cbn in *; try discriminate.
    - unfold ctx_ent.map in *. destruct a; try congruence.
      invc NE. eauto.
    - apply IHT in NE. assumption.
    - destruct a; cbn in *; try congruence.
      invc NE.
      rewrite Nat.sub_0_r.
      eauto.
    - auto.
  Qed.

  Lemma nth_error_tele_shift_exvar2 :
    forall T c d n ty,
      nth_error T n = Some (EXVAR ty) ->
      nth_error (shift c d T) n = Some (EXVAR (term.shift (c - S n) d ty)).
  Proof.
    induction T; intros [|c] d [|n] ty NE; cbn in *; try discriminate.
    - invc NE; reflexivity.
    - now erewrite IHT by eassumption.
    - rewrite Nat.sub_0_r.
      invc NE; reflexivity.
    - eauto.
  Qed.

  Lemma lookup_exvar_shift :
    forall T1 T2 T3 n expect,
     lookup_exvar (shift (length T1) (length T2) T1 ++ T2 ++ T3)
                  (if n <? length T1 then n else n + length T2)
                  (term.shift (length T1) (length T2) expect) <->
     lookup_exvar (T1 ++ T3) n expect.
  Proof.
    intros T1 T2 T3 n expect.
    unfold lookup_exvar.
    rewrite nth_error_shift' in * by now rewrite shift_length.
    destruct (Nat.ltb_spec n (length T1)).
    - rewrite !nth_error_app1 by now rewrite ?shift_length.
      split; intros [expect' [NE ?]]; subst.
      + apply nth_error_tele_shift_exvar1 in NE.
        destruct NE as [ty' [Ety' NE]].
        subst. eexists. split; [eassumption|].
        rewrite term.shift_shift in * by lia.
        replace (length T1 - S n + S n) with (length T1) in * by lia.
        eauto using term.shift_inj.
      + erewrite nth_error_tele_shift_exvar2 by eassumption.
        eexists. split; [reflexivity|].
        rewrite term.shift_shift with (c2 := 0) by lia.
        f_equal. lia.
    - rewrite !nth_error_app2 by (rewrite ?shift_length; lia).
      rewrite shift_length.
      split; intros [expect' [NE ?]]; subst;
        (eexists; split; [eassumption|]).
      + apply term.shift_inj with (c := length T1) (d := length T2).
        now rewrite term.shift_merge by lia.
      + now rewrite term.shift_merge by lia.
  Qed.

  Lemma lookup_exvar_nth_error :
    forall T n ty,
      lookup_exvar T n ty ->
      exists ty',
        nth_error T n = Some (EXVAR ty').
  Proof.
    intros T n ty LE.
    unfold lookup_exvar in *.
    destruct LE as [expect' [NE ?]]. subst.
    eauto.
  Qed.

  Lemma nth_error_wc :
    forall T n ty,
      nth_error T n = Some (EXVAR ty) ->
      wf T ->
      wc.t (skipn (S n) (to_cat_ctx T)) ty cat.TYPE.
  Proof.
    induction T; cbn; intros n ty NE WF; destruct n; try discriminate.
    - invc NE. intuition.
    - apply IHT; intuition.
  Qed.

  Lemma lookup_exvar_wc :
    forall T n ty,
      lookup_exvar T n ty ->
      wf T ->
      wc.t (to_cat_ctx T) ty cat.TYPE.
  Proof.
    intros T n ty [expect' [NE ?]] WFT. subst.
    apply wc.t_skipn_shift.
    - apply lt_le_S. apply nth_error_Some.
      rewrite nth_error_map, NE.
      discriminate.
    - auto using nth_error_wc.
  Qed.

  Lemma to_cat_ctx_cons :
    forall ce T,
      to_cat_ctx (cons ce T) = ctx_ent.to_cat ce :: to_cat_ctx T.
  Proof. reflexivity. Qed.

  Lemma wf_cons_exvar :
    forall ty T,
      wc.t (to_cat_ctx T) ty cat.TYPE ->
      wf T ->
      wf (cons (EXVAR ty) T).
  Proof. cbn. auto. Qed.

  Lemma wf_cons_tyvar :
    forall T,
      wf T ->
      wf (cons TYVAR T).
  Proof. cbn. auto. Qed.

  Lemma to_cat_ctx_globalize :
    forall (G : t) i,
      to_cat_ctx (globalize i G) =
      to_cat_ctx G.
  Proof.
    induction G; cbn; intros i.
    - reflexivity.
    - f_equal; [|now auto].
      destruct a; reflexivity.
  Qed.

  Lemma to_cat_ctx_subst :
    forall rho G,
      to_cat_ctx (List.map (ctx_ent.map (term.subst rho)) G) =
      to_cat_ctx G.
  Proof.
    induction G; cbn.
    - reflexivity.
    - f_equal; [|now auto].
      destruct a; reflexivity.
  Qed.

  Lemma globalize_length :
    forall G i,
      length (tele.globalize i G) = length G.
  Proof.
    induction G; cbn; intros i; auto.
  Qed.

  Lemma globalize_0 :
    forall G i,
      globalize i G = List.map (ctx_ent.map (term.shift 0 i)) (globalize 0 G).
  Proof.
    induction G; intros i; cbn; f_equal.
    - destruct a; cbn; f_equal; auto.
      now rewrite term.shift_merge by lia.
    - rewrite IHG with (i := S i).
      rewrite IHG with (i := 1).
      rewrite map_map.
      apply map_ext.
      clear.
      intros [|ty]; cbn; f_equal; auto.
      now rewrite term.shift_merge by lia.
  Qed.

  Lemma wf_globalize :
    forall G,
      tele.wf G ->
      Forall (ctx_ent.prop (term.wf (length G))) (tele.globalize 0 G).
  Proof.
    intros G WF.
    induction G; cbn in *; constructor; destruct WF as [WF HA].
    - destruct a as [|ty]; cbn in *; auto.
      apply wc.t_wf in HA.
      apply term.wf_shift'.
      now rewrite map_length in HA.
    - forward IHG.
      rewrite globalize_0.
      rewrite Forall_map.
      eapply Forall_impl; [|eassumption].
      clear.
      intros [|ty]; cbn; intros WF; auto using term.wf_shift'.
  Qed.
End tele.

Module has_type.
  Import ctx_ent.exports.

  Inductive t : tele.t -> term.t -> term.t -> Prop :=
  | var : forall G x ty,
      tele.lookup_exvar G x ty ->
      t G (term.var x) ty
  | abs : forall G ty1 ty2 ty2' e,
      wc.t (tele.to_cat_ctx G) ty1 cat.TYPE ->
      t (EXVAR ty1 :: G) e ty2 ->
      ty2 = term.shift 0 1 ty2' ->
      t G (term.abs ty1 e) (term.arrow ty1 ty2')
  | app : forall G ty1 ty2 e1 e2,
      t G e1 (term.arrow ty1 ty2) ->
      t G e2 ty1 ->
      t G (term.app e1 e2) ty2
  | tyabs : forall G e ty,
      t (TYVAR :: G) e ty ->
      t G (term.tyabs e) (term.all ty)
  | tyapp : forall G e ty_body ty,
      wc.t (tele.to_cat_ctx G) ty cat.TYPE ->
      t G e (term.all ty_body) ->
      t G (term.tyapp e ty) (term.subst (ty :: term.identity_subst (length G)) ty_body)
  | tt : forall G,
      t G term.tt term.bool
  | ff : forall G,
      t G term.ff term.bool
  | If : forall G e1 e2 e3 ty,
      t G e1 term.bool ->
      t G e2 ty ->
      t G e3 ty ->
      t G (term.If e1 e2 e3) ty
  .
  Global Hint Constructors t : core.

  Lemma t_wc_e :
    forall G e ty,
      t G e ty ->
      tele.wf G ->
      wc.t (tele.to_cat_ctx G) e cat.EXPR.
  Proof.
    induction 1; cbn in *; intros TWF; auto.
    constructor.
    destruct (tele.lookup_exvar_nth_error _ _ _ H) as [ty' NE].
    now erewrite map_nth_error by eassumption.
  Qed.

  Lemma t_wc_ty :
    forall G e ty,
      t G e ty ->
      tele.wf G ->
      wc.t (map ctx_ent.to_cat G) ty cat.TYPE.
  Proof.
    induction 1; cbn in *; intros TWF; auto.
    - destruct (tele.lookup_exvar_nth_error _ _ _ H) as [ty' NE].
      eauto using tele.lookup_exvar_wc.
    - constructor; auto.
      forward IHt.
      subst ty2.
      eauto using wc.shift_cons_inv.
    - forward IHt1.
      now invc IHt1.
    - forward IHt.
      invc IHt.
      eapply wc.subst; eauto.
      constructor; [assumption|].
      apply wc.Forall2_identity_subst.
      now rewrite map_length.
  Qed.

  Lemma shift :
  forall G1 G2 G3 e ty,
    tele.wf (G1 ++ G3) ->
    has_type.t (G1 ++ G3) e ty ->
    has_type.t (tele.shift (length G1) (length G2) G1 ++ G2 ++ G3)
               (term.shift (length G1) (length G2) e)
               (term.shift (length G1) (length G2) ty).
  Proof.
    intros G1 G2 G3 e ty WF HT.
    revert G2.
    remember (G1 ++ G3) as G eqn:EG in *.
    revert WF G1 G3 EG.
    induction HT; intros WF G1 G3 EG G2; subst G; cbn [term.shift]; eauto.
    - constructor.
      now rewrite tele.lookup_exvar_shift.
    - econstructor; [| |reflexivity].
      + rewrite !map_app in *.
        apply wc.shift with (C2 := map ctx_ent.to_cat G2) in H.
        eqapply H.
        * now rewrite !map_length.
        * now rewrite tele.to_cat_shift.
      + rewrite term.shift_shift with (c2 := 0) by lia.
        forward IHHT.
        specialize (IHHT (_ :: _) _ eq_refl G2).
        subst ty2.
        eqapply IHHT.
        f_equal. cbn. lia.
    - econstructor.
      forward IHHT.
      eapply (IHHT (_ :: _) _ eq_refl).
    - specialize (IHHT ltac:(auto) _ _ eq_refl G2).
      assert (term.wf (length (ty :: term.identity_subst (length (G1 ++ G3)))) ty_body).
      {
        cbn. rewrite term.identity_subst_length.
        apply t_wc_ty in HT; [|assumption].
        apply wc.t_wf in HT.
        rewrite map_length in HT.
        apply HT.
      }
      rewrite term.shift_subst by assumption.
      cbn [term.shift] in IHHT.
      eapply tyapp in IHHT.
      eqapply IHHT.
      + rewrite !app_length, tele.shift_length.
        rewrite term.identity_subst_app.
        rewrite term.SIS_app.
        rewrite app_comm_cons.
        rewrite term.subst_shift.
        * cbn. f_equal. f_equal.
          rewrite term.identity_subst_app, map_app.
          rewrite term.map_shift_identity_subst'.
          f_equal.
          rewrite term.SIS_merge by lia.
          f_equal.
          lia.
        * rewrite ?app_length, ?term.SIS_length in *.
          cbn in *.
          now rewrite term.identity_subst_length in *.
        * cbn.
          now rewrite term.identity_subst_length in *.
        * now rewrite term.SIS_length.
      + rewrite !map_app in *.
        rewrite tele.to_cat_shift.
        eapply wc.shift in H.
        eqapply H.
        now rewrite !map_length.
  Qed.

  Lemma shift' :
    forall G e ty G',
      tele.wf G ->
      t G e ty ->
      t (G' ++ G) (term.shift 0 (List.length G') e) (term.shift 0 (List.length G') ty).
  Proof.
    intros.
    now apply shift with (G1 := []).
  Qed.

  Lemma shift_cons :
  forall G e ty ty',
    tele.wf G ->
    has_type.t G e ty ->
    has_type.t (ty' :: G) (term.shift 0 1 e) (term.shift 0 1 ty).
  Proof.
    intros G e ty ty' WF HT.
    now apply shift' with (G' := [ty']).
  Qed.

  Definition t_ctx_ent G e ce :=
    match ce with
    | TYVAR => wc.t (tele.to_cat_ctx G) e cat.TYPE
    | EXVAR ty => t G e ty
    end.

  Lemma Forall2_t_ctx_ent_wc :
    forall G es tys,
      tele.wf G ->
      Forall2 (t_ctx_ent G) es tys ->
      Forall2 (wc.t (tele.to_cat_ctx G)) es (map ctx_ent.to_cat tys).
  Proof.
    intros G es tys WF F.
    apply Forall2_map_r.
    eapply Forall2_impl; [|eassumption].
    intros.
    destruct b; cbn in *.
    - assumption.
    - eapply t_wc_e; eauto.
  Qed.

  Lemma subst :
    forall G e ty,
      t G e ty ->
      tele.wf G ->
      forall G' rho,
        tele.wf G' ->
        List.Forall2 (t_ctx_ent G') rho
                     (map (ctx_ent.map (term.subst rho)) (tele.globalize 0 G)) ->
        t G' (term.subst rho e) (term.subst rho ty).
  Proof.
    induction 1; intros WFG G' rho WFG' F; cbn [term.subst]; eauto;
      assert (length G = length rho) as L
        by (apply Forall2_length in F;
            rewrite map_length, tele.globalize_length in F;
            congruence).
    - pose proof (tele.lookup_exvar_globalize _ _ _ ltac:(eassumption)).
      pose proof (map_nth_error (ctx_ent.map (term.subst rho)) _ _ H0).
      destruct (Forall2_nth_error2 F ltac:(eassumption)) as [z [Hz Ht]].
      cbn.
      unfold term.t in *. (* ugh *)
      now rewrite Hz.
    - apply abs with (ty2 := term.subst (term.descend 1 rho) ty2).
      + eapply wc.subst.
        eassumption.
        apply Forall2_t_ctx_ent_wc in F; [|assumption].
        eqapply F.
        now rewrite tele.to_cat_ctx_subst, tele.to_cat_ctx_globalize.
      + forward IHt.
        apply IHt.
        {
          cbn; split; [assumption|].
          eapply wc.subst; [eassumption|].
          apply Forall2_t_ctx_ent_wc in F; [|assumption].
          now rewrite tele.to_cat_ctx_subst, tele.to_cat_ctx_globalize in F.
        }
        {
          cbn.
          constructor.
          - unfold t_ctx_ent.
            constructor.
            eexists.
            cbn.
            split;[reflexivity|].
            assert (term.wf (length rho) ty1).
            {
              apply wc.t_wf in H.
              rewrite map_length in H.
              congruence.
            }
            rewrite term.shift_subst by assumption.
            now rewrite term.subst_shift_cons by now rewrite map_length.
          - assert (Forall2
                      (t_ctx_ent (EXVAR (term.subst rho ty1) :: G'))
                      (List.map (term.shift 0 1) rho)
                      (List.map
                         (ctx_ent.map (term.shift 0 1))
                         (List.map (ctx_ent.map (term.subst rho)) (tele.globalize 0 G))))
              as F'.
            {
              (* basically apply shift_cons in F. *)
              rewrite map_map.
              rewrite Forall2_map.
              rewrite Forall2_map_r_iff in F.
              eapply Forall2_impl; [|eassumption].
              cbn.
              (* this should be a lemma *)
              intros a [|ty]; cbn; intros Hty.
              - auto using wc.shift_cons.
              - auto using shift_cons.
            }

            eqapply F'.
            rewrite tele.globalize_0 with (i := 1).
            rewrite !map_map.
            apply tele.wf_globalize in WFG.
            apply map_ext_Forall.
            eapply Forall_impl; [|eassumption].
            clear -L.
            intros [|ty] WF; cbn in *; [reflexivity|f_equal].
            rewrite term.shift_subst by congruence.
            now rewrite term.subst_shift_cons by (rewrite map_length; congruence).
        }
      + subst ty2.
        apply term.subst_descend_shift_shift_subst.
        apply t_wc_ty in H0.
        apply wc.t_wf in H0.
        rewrite map_length in *.
        cbn [length] in H0.
        apply term.wf_shift_inv' in H0.
        congruence.
        cbn. split; auto.
    - econstructor.
      apply IHt; cbn; auto.
      constructor; [now cbn; auto|].
      rewrite Forall2_map_r_iff in F.
      rewrite tele.globalize_0.
      rewrite map_map.
      apply Forall2_map.
      eapply Forall_Forall2_and_r in F; [|apply tele.wf_globalize; assumption].
      eapply Forall2_impl; [|eassumption].
      cbn.
      intros a [|tyb] [HT WF]; cbn in *.
      + auto using wc.shift_cons.
      + rewrite term.subst_cons_shift_shift_subst_1 by congruence.
        now apply shift_cons; auto.
    - forward IHt.
      specialize (IHt G' rho ltac:(assumption) ltac:(assumption)).
      cbn in IHt.
      apply tyapp with (ty := term.subst rho ty) in IHt.
      2: {
        eapply wc.subst; eauto.
        apply Forall2_t_ctx_ent_wc in F; [|assumption].
        eqapply F.
        now rewrite tele.to_cat_ctx_subst, tele.to_cat_ctx_globalize.
      }
      eqapply IHt.
      rewrite !term.subst_subst.
      + f_equal. cbn. f_equal.
        rewrite map_map.
        rewrite L.
        rewrite term.map_subst_identity_subst.
        erewrite map_ext_Forall; [now apply map_id|].
        apply Forall2_t_ctx_ent_wc in F; [|assumption].
        apply wc.Forall2_t_Forall_wf in F.
        rewrite map_length in F.
        eapply Forall_impl; [|eassumption].
        intros a WF.
        rewrite term.subst_shift_cons by now rewrite term.identity_subst_length.
        now rewrite term.subst_identity.
      + cbn. rewrite term.identity_subst_length.
        (* this should be a lemma *)
        apply t_wc_ty in H0; [|assumption].
        apply wc.t_wf in H0.
        rewrite map_length in H0.
        apply H0.
      + constructor; auto.
        apply wc.t_wf in H.
        rewrite map_length in H.
        congruence.
        rewrite L.
        apply term.wf_identity_subst.
      + cbn.
        apply t_wc_ty in H0; [|assumption].
        apply wc.t_wf in H0.
        rewrite !map_length in *.
        rewrite L in H0.
        apply H0.
      + constructor; auto.
        * cbn. lia.
        * apply Forall_map.
          apply Forall2_t_ctx_ent_wc in F; [|assumption].
          apply wc.Forall2_t_Forall_wf in F.
          eapply Forall_impl; [|eassumption].
          intros a.
          cbn.
          rewrite map_length.
          rewrite term.identity_subst_length.
          auto using term.wf_shift'.
  Qed.
End has_type.
Print Assumptions has_type.subst.
