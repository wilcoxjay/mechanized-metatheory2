From mm Require Import util.
Set Implicit Arguments.

Module Type MAP.
  Parameter key : Type.
  Parameter key_eq_dec : forall (k1 k2 : key), {k1 = k2} + {k1 <> k2}.

  Parameter t : Type -> Type.

  Parameter empty : forall {V}, t V.
  Parameter get : forall V, key -> t V -> option V.
  Parameter set : forall V, key -> V -> t V -> t V.
  Parameter rem : forall V, key -> t V -> t V.
  Parameter fresh : forall V, t V -> key.

  Parameter ge : forall V k, get(V:=V) k empty = None.

  Parameter gr : forall V (m : t V) (k1 k2 : key),
      get k2 (rem k1 m) = if key_eq_dec k2 k1 then None else get k2 m.

  Parameter gss : forall V (k : key) (v : V) m, get k (set k v m) = Some v.
  Parameter gso : forall V (k1 k2 : key) (v : V) m, k1 <> k2 -> get k2 (set k1 v m) = get k2 m.

  Parameter gs : forall V (m : t V) (k1 k2 : key) (v : V),
      get k2 (set k1 v m) = if key_eq_dec k2 k1 then Some v else get k2 m.

  Parameter grs : forall V (k : key) (m : t V), get k (rem k m) = None.
  Parameter gro : forall V (k1 k2 : key) (m : t V), k1 <> k2 -> get k2 (rem k1 m) = get k2 m.

  Parameter gf : forall V (m : t V), get (fresh m) m = None.

  Parameter ext : forall V (m1 m2 : t V), (forall k, get k m1 = get k m2) -> m1 = m2.
End MAP.

Module Type OrderedType.
  Parameter t : Type.
  Parameter lt : t -> t -> Prop.
  Parameter irrefl : forall x, ~ lt x x.
  Parameter trans : forall x y z, lt x y -> lt y z -> lt x z.
  Parameter trich_dec : forall x y, {lt x y} + {x = y} + {lt y x}.
  Parameter eq_dec : forall (k1 k2 : t), {k1 = k2} + {k1 <> k2}.

  Parameter init : t.

  Parameter bigger : t -> t.
  Parameter bigger_lt : forall x, lt x (bigger x).

  Parameter lt_irrelevant : forall x y (pf1 pf2 : lt x y), pf1 = pf2.
End OrderedType.

Module NatOrderedType : OrderedType with Definition t := nat.
  Definition t := nat.
  Definition lt := Peano.lt.

  Definition irrefl : forall x, ~ lt x x := Nat.lt_irrefl.
  Definition trans : forall x y z, lt x y -> lt y z -> lt x z := Nat.lt_trans.
  Definition trich_dec : forall x y, {lt x y} + {x = y} + {lt y x} := lt_eq_lt_dec.
  Definition eq_dec : forall (k1 k2 : t), {k1 = k2} + {k1 <> k2} := Nat.eq_dec.

  Definition init := 0.

  Definition bigger := S.
  Definition bigger_lt : forall x, lt x (bigger x) := Nat.lt_succ_diag_r.

  Fixpoint le_irrelevant x y (pf1 : Peano.le x y) : forall pf2 : Peano.le x y, pf1 = pf2.
    refine match pf1 with
           | le_n _ => _
           | le_S _ _ _ => _
           end; clear pf1.
    - clear le_irrelevant.
      assert (forall (y : nat) (pf : x <= y) (e : y = x),
                 le_n x = eq_rect y (fun z : nat => x <= z) pf x e).
      {
        clear y.
        intros y pf.
        destruct pf; intros e.
        - now rewrite Eqdep_dec.UIP_refl_nat with (x := e).
        - exfalso. subst. lia.
      }
      intros pf2.
      apply (H x pf2 eq_refl).
    - intros pf2.
      generalize (fun l2 => le_irrelevant _ _ l l2).
      revert l.
      refine (match pf2 as pf20 in _ <= n0
                   return match n0 with
                          | 0 => fun _ => True
                          | S n1 => fun pf21 => forall (l : x <= n1), (forall l2 : x <= n1, l = l2) ->
                                                             le_S x n1 l = pf21
                          end pf20
             with
             | le_n _ => _
             | le_S _ _ l2 => _
             end).
      + destruct x.
        * exact I.
        * intros l1 IH. exfalso. lia.
      + intros l1 IH.
        f_equal.
        apply IH.
  Defined.

  Definition lt_irrelevant : forall x y (pf1 pf2 : lt x y), pf1 = pf2.
    intros.
    apply le_irrelevant.
  Defined.
  Print Assumptions lt_irrelevant.
End NatOrderedType.

Module SortedMap (K : OrderedType) : MAP with Definition key := K.t.
  Definition key := K.t.

  Definition key_eq_dec := K.eq_dec.

  Module Type INTERNAL.
    Parameter t : Type -> Type.
    Parameter wf : forall V, t V -> Prop.

    Parameter empty : forall {V}, t V.
    Parameter get : forall V, key -> t V -> option V.
    Parameter set : forall V, key -> V -> t V -> t V.
    Parameter rem : forall V, key -> t V -> t V.
    Parameter fresh : forall V, t V -> key.

    Parameter wf_empty :
      forall V,
        wf empty(V:=V).

    Parameter wf_set :
      forall V k (v : V) m,
        wf m ->
        wf (set k v m).

    Parameter wf_rem :
      forall V k (m : t V),
        wf m ->
        wf (rem k m).

    Parameter wf_irrelevant :
      forall V (m : t V) (pf1 pf2 : wf m),
        pf1 = pf2.

    Parameter ge : forall V k, get(V:=V) k empty = None.

    Parameter gs : forall V (m : t V) (k1 k2 : key) (v : V),
        wf m ->
        get k2 (set k1 v m) = if K.eq_dec k2 k1 then Some v else get k2 m.

    Parameter gss : forall V (k : key) (v : V) m, wf m -> get k (set k v m) = Some v.
    Parameter gso : forall V (k1 k2 : key) (v : V) m,
        wf m -> k1 <> k2 -> get k2 (set k1 v m) = get k2 m.

    Parameter gr : forall V (m : t V) (k1 k2 : key),
        wf m ->
        get k2 (rem k1 m) = if K.eq_dec k2 k1 then None else get k2 m.

    Parameter grs : forall V (k : key) (m : t V), wf m -> get k (rem k m) = None.
    Parameter gro : forall V (k1 k2 : key) (m : t V),
        wf m -> k1 <> k2 -> get k2 (rem k1 m) = get k2 m.

    Parameter gf : forall V (m : t V), wf m -> get (fresh m) m = None.

    Parameter ext : forall V (m1 m2 : t V),
        wf m1 -> wf m2 -> (forall k, get k m1 = get k m2) -> m1 = m2.
  End INTERNAL.

  Module Internal : INTERNAL.
    Definition t V := list (key * V).

    Fixpoint wf_aux V (k : key) (m : t V) : Prop :=
      match m with
      | [] => True
      | (k1,_) :: m =>
        K.lt k k1 /\ wf_aux k1 m
      end.
    Definition wf V (m : t V) : Prop :=
      match m with
      | [] => True
      | (k1, _) :: m =>
        wf_aux k1 m
      end.

    Lemma wf_aux_irrelevant :
      forall V (m : t V) k (pf1 pf2 : wf_aux k m),
        pf1 = pf2.
    Proof.
      induction m as [|[k1 v1] m]; simpl; intros k [] [].
      - reflexivity.
      - f_equal.
        + apply K.lt_irrelevant.
        + apply IHm.
    Qed.

    Lemma wf_irrelevant :
      forall V (m : t V) (pf1 pf2 : wf m),
        pf1 = pf2.
    Proof.
      unfold wf.
      intros V [|[k1 v1] m].
      - intros [][]. reflexivity.
      - apply wf_aux_irrelevant.
    Qed.

    Definition wf' V (m : t V) : Prop :=
      forall i j k1 k2 v1 v2,
        i < j ->
        nth_error m i = Some (k1, v1) ->
        nth_error m j = Some (k2, v2) ->
        K.lt k1 k2.

    Definition empty {V} : t V := [].

    Fixpoint get V (k : key) (m : t V) : option V :=
      match m with
      | [] => None
      | (k1, v1) :: m =>
        if K.eq_dec k k1 then Some v1
        else get k m
      end.

    Fixpoint set V (k : key) (v : V) (m : t V) : t V :=
      match m with
      | [] => [(k, v)]
      | (k1, v1) :: m =>
        match K.trich_dec k k1 with
        | inleft (left LT) => (k, v) :: (k1, v1) :: m
        | inleft (right EQ) => (k, v) :: m
        | inright GT => (k1, v1) :: set k v m
        end
      end.

    Fixpoint rem V (k : key) (m : t V) : t V :=
      match m with
      | [] => []
      | (k1, v1) :: m =>
        if K.eq_dec k k1 then m
        else (k1, v1) :: rem k m
      end.

    Fixpoint max_key V (acc : key) (m : t V) : key :=
      match m with
      | [] => acc
      | (k, _) :: m =>
        max_key (if K.trich_dec k acc then acc else k) m
      end.

    Definition fresh V (m : t V) : key :=
      match m with
      | [] => K.init
      | (k, _) :: m => K.bigger (max_key k m)
      end.

    Lemma wf_empty :
      forall V,
        wf empty(V:=V).
    Proof.
      unfold wf, empty.
      intros.
      exact I.
    Qed.

    Lemma wf_aux_set :
      forall V m k (v : V) k0,
        wf_aux k0 m ->
        K.lt k0 k ->
        wf_aux k0 (set k v m).
    Proof.
      induction m as [|[]]; simpl; intros k1 v1 acc.
      + intuition.
      + intros [LT WF] GT.
        destruct (K.trich_dec k1 k) as [[|]|]; simpl.
        * intuition.
        * subst. intuition.
        * intuition.
    Qed.

    Lemma wf_set :
      forall V k (v : V) m,
        wf m ->
        wf (set k v m).
    Proof.
      unfold wf.
      intros V k v m.
      destruct m as [|[]]; simpl; auto.
      intros WF.
      destruct (K.trich_dec k k0) as [[LT|EQ]|GT]; simpl.
      - auto.
      - subst. auto.
      - auto using wf_aux_set.
    Qed.

    Lemma wf_aux_lt :
      forall V (m : t V) k1 k2,
        K.lt k1 k2 ->
        wf_aux k2 m ->
        wf_aux k1 m.
    Proof.
      induction m as [|[k v] m]; simpl; auto; intros k1 k2 LT12 [LT2 WF].
      split; eauto using K.trans.
    Qed.

    Lemma wf_aux_rem :
      forall V (m : t V) k k0,
        wf_aux k0 m ->
        wf_aux k0 (rem k m).
    Proof.
      induction m as [|[k1 v1] m]; simpl; intros k k0.
      - auto.
      - intros [LT WF].
        destruct (K.eq_dec k k1).
        + subst. eauto using wf_aux_lt.
        + simpl. auto.
    Qed.

    Lemma wf_rem :
      forall V k (m : t V),
        wf m ->
        wf (rem k m).
    Proof.
      unfold wf.
      intros V k m.
      destruct m as [|[]]; simpl; auto.
      intros WF.
      destruct (K.eq_dec k k0).
      - subst. destruct m as [|[]].
        + exact I.
        + simpl in WF. intuition.
      - auto using wf_aux_rem.
    Qed.

    Lemma ge : forall V k, get(V:=V) k empty = None.
    Proof.
      intros.
      reflexivity.
    Qed.

    Lemma key_eq_dec_yes :
      forall A k1 k2 (x y : A),
        k1 = k2 ->
        (if K.eq_dec k1 k2 then x else y) = x.
    Proof.
      intros.
      destruct K.eq_dec; congruence.
    Qed.

    Lemma key_eq_dec_no :
      forall A k1 k2 (x y : A),
        k1 <> k2 ->
        (if K.eq_dec k1 k2 then x else y) = y.
    Proof.
      intros.
      destruct K.eq_dec; congruence.
    Qed.

    Lemma lt_neq :
      forall k1 k2,
        K.lt k1 k2 ->
        k1 <> k2.
    Proof.
      intros k1 k2 H E.
      subst.
      eapply K.irrefl; eauto.
    Qed.

    Lemma gs_aux : forall V (m : t V) (k1 k2 k' : key) (v : V),
        wf_aux k' m ->
        get k2 (set k1 v m) = if K.eq_dec k2 k1 then Some v else get k2 m.
    Proof.
      induction m as [|[k3 v3] m]; simpl; intros k1 k2 k' v.
      - auto.
      - intros [LT WF].
        destruct K.trich_dec as [[|]|]; simpl.
        + reflexivity.
        + subst.
          now destruct K.eq_dec.
        + apply lt_neq in LT.
          apply lt_neq in l.
          erewrite IHm by eassumption.
          repeat destruct K.eq_dec; congruence.
    Qed.

    Lemma gs : forall V (m : t V) (k1 k2 : key) (v : V),
        wf m ->
        get k2 (set k1 v m) = if K.eq_dec k2 k1 then Some v else get k2 m.
    Proof.
      intros V m k1 k2 v.
      destruct m as [|[]]; simpl.
      - reflexivity.
      - intros WF.
        destruct K.trich_dec as [[|]|]; simpl.
        + reflexivity.
        + subst.
          now destruct K.eq_dec.
        + apply lt_neq in l.
          erewrite gs_aux by eassumption.
          repeat destruct K.eq_dec; try congruence.
    Qed.

    Lemma gss : forall V (k : key) (v : V) (m : t V), wf m -> get k (set k v m) = Some v.
    Proof.
      intros V k v m WF.
      now rewrite gs, key_eq_dec_yes.
    Qed.

    Lemma gso : forall V (k1 k2 : key) (v : V) (m : t V),
        wf m ->
        k1 <> k2 ->
        get k2 (set k1 v m) = get k2 m.
    Proof.
      intros V k1 k2 v m WF NE.
      now rewrite gs, key_eq_dec_no; auto using not_eq_sym.
    Qed.

    Lemma get_wf_aux_lt_None :
      forall V (m : t V) (k1 k2 : key),
        K.lt k1 k2 ->
        wf_aux k2 m ->
        get k1 m = None.
    Proof.
      induction m as [|[k3 v3] m]; simpl; intros k1 k2.
      - reflexivity.
      - intros LT12 [LT23 WF].
        rewrite key_eq_dec_no; eauto using K.trans, lt_neq.
    Qed.

    Lemma get_wf_aux_None :
      forall V (m : t V) k,
        wf_aux k m ->
        get k m = None.
    Proof.
      destruct m as [|[k1 v1] m]; simpl.
      - reflexivity.
      - intros k [LT WF].
        rewrite key_eq_dec_no by auto using lt_neq.
        now eauto using get_wf_aux_lt_None.
    Qed.

    Lemma gr_aux : forall V (m : t V) (k1 k2 k' : key),
        wf_aux k' m ->
        get k2 (rem k1 m) = if K.eq_dec k2 k1 then None else get k2 m.
    Proof.
      induction m as [|[k3 v3] m]; simpl; intros k1 k2 k'.
      - destruct K.eq_dec; auto.
      - intros [LT WF].
        destruct K.eq_dec; simpl.
        + subst.
          destruct K.eq_dec.
          * subst.
            auto using get_wf_aux_None.
          * auto.
        + erewrite IHm by eassumption.
          repeat destruct K.eq_dec; congruence.
    Qed.

    Lemma gr : forall V (m : t V) (k1 k2 : key),
        wf m ->
        get k2 (rem k1 m) = if K.eq_dec k2 k1 then None else get k2 m.
    Proof.
      destruct m as [|[k3 v3] m]; intros k1 k2; simpl.
      - destruct K.eq_dec; reflexivity.
      - intros WF.
        destruct K.eq_dec; simpl.
        + subst.
          destruct K.eq_dec.
          * subst.
            auto using get_wf_aux_None.
          * auto.
        + erewrite gr_aux by eassumption.
          repeat destruct K.eq_dec; congruence.
    Qed.

    Lemma grs : forall V (k : key) (m : t V), wf m -> get k (rem k m) = None.
    Proof.
      intros.
      now rewrite gr, key_eq_dec_yes.
    Qed.

    Lemma gro : forall V (k1 k2 : key) (m : t V),
        wf m ->
        k1 <> k2 ->
        get k2 (rem k1 m) = get k2 m.
    Proof.
      intros.
      rewrite gr, key_eq_dec_no; auto using not_eq_sym.
    Qed.

    Lemma lt_max_key_inv :
      forall V (m : t V) k1 k2,
        K.lt (max_key k1 m) k2 ->
        K.lt k1 k2.
    Proof.
      induction m as [|[k3 v3] m]; simpl; intros k1 k2 LT.
      - auto.
      - destruct K.trich_dec as [[|]|]; eauto using K.trans.
    Qed.

    Lemma get_max_key_None :
      forall V (m : t V) k1 k2,
        K.lt (max_key k1 m) k2 ->
        get k2 m = None.
    Proof.
      induction m as [|[k3 v3] m]; simpl; intros k1 k2 LT.
      - reflexivity.
      - rewrite key_eq_dec_no
          by (apply not_eq_sym; apply lt_neq;
              destruct K.trich_dec as [[|]|]; subst; eauto using K.trans, lt_max_key_inv).
        eauto.
    Qed.


    Definition le (k1 k2 : key) : Prop :=
      K.lt k1 k2 \/ k1 = k2.

    Lemma le_lt_trans :
      forall k1 k2 k3,
        le k1 k2 ->
        K.lt k2 k3 ->
        K.lt k1 k3.
    Proof.
      unfold le.
      intros k1 k2 k3 LT12 LT23.
      intuition; subst; eauto using K.trans.
    Qed.

    Lemma lt_le_trans :
      forall k1 k2 k3,
        K.lt k1 k2 ->
        le k2 k3 ->
        K.lt k1 k3.
    Proof.
      unfold le.
      intros k1 k2 k3 LT12 LT23.
      intuition; subst; eauto using K.trans.
    Qed.

    Lemma max_key_le_acc :
      forall V (m : t V) k,
        le k (max_key k m).
    Proof.
      induction m as [|[k1 v1] m]; simpl; intros k.
      - right. reflexivity.
      - destruct K.trich_dec.
        + auto.
        + left.
          eauto using lt_le_trans.
    Qed.

    Lemma gf : forall V (m : t V), wf m -> get (fresh m) m = None.
    Proof.
      unfold wf, fresh.
      destruct m as [|[k1 v1] m].
      - reflexivity.
      - intros WF.
        simpl.
        rewrite key_eq_dec_no
        by (apply not_eq_sym;
            apply lt_neq;
            eapply le_lt_trans; [|apply K.bigger_lt];
            apply max_key_le_acc).
        now eauto using get_max_key_None, K.bigger_lt.
    Qed.

    Lemma ext_aux : forall V (m1 m2 : t V) k,
        wf_aux k m1 ->
        wf_aux k m2 ->
        (forall k, get k m1 = get k m2) ->
        m1 = m2.
    Proof.
      induction m1 as [|[k1 v1] m1]; destruct m2 as [|[k2 v2] m2]; simpl; intros k.
      - reflexivity.
      - intros _ _ E.
        specialize (E k2).
        rewrite key_eq_dec_yes in E by reflexivity.
        discriminate.
      - intros _ _ E.
        specialize (E k1).
        rewrite key_eq_dec_yes in E by reflexivity.
        discriminate.
      - intros [LT1 WF1] [LT2 WF2] E.
        destruct (K.trich_dec k1 k2) as [[|]|].
        + pose proof E k1.
          rewrite key_eq_dec_yes in H by reflexivity.
          rewrite key_eq_dec_no in H by auto using lt_neq.
          erewrite get_wf_aux_lt_None in H by eauto.
          discriminate.
        + subst k2.
          assert (v1 = v2).
          {
            specialize (E k1).
            rewrite !key_eq_dec_yes in E by auto.
            congruence.
          }
          subst v2.
          f_equal.
          eapply IHm1; eauto.
          intros k0.
          specialize (E k0).
          destruct K.eq_dec.
          * subst k0. clear E.
            now rewrite !get_wf_aux_None by assumption.
          * auto.
        + pose proof E k2.
          rewrite key_eq_dec_yes with (k2 := k2) in H by reflexivity.
          rewrite key_eq_dec_no in H by auto using lt_neq.
          erewrite get_wf_aux_lt_None in H by eauto.
          discriminate.
    Qed.

    Lemma ext : forall V (m1 m2 : t V),
        wf m1 ->
        wf m2 ->
        (forall k, get k m1 = get k m2) ->
        m1 = m2.
    Proof.
      intros V m1 m2 WF1 WF2 E.
      destruct m1 as [|[k1 v1] m1], m2 as [|[k2 v2]].
      - auto.
      - specialize (E k2). simpl in *. rewrite key_eq_dec_yes in * by auto. discriminate.
      - specialize (E k1). simpl in *. rewrite key_eq_dec_yes in * by auto. discriminate.
      - unfold wf in *.
        simpl in *.
        destruct (K.trich_dec k1 k2) as [[|]|].
        + pose proof E k1.
          rewrite key_eq_dec_yes in H by reflexivity.
          rewrite key_eq_dec_no in H by auto using lt_neq.
          erewrite get_wf_aux_lt_None in H by eauto.
          discriminate.
        + subst k2.
          pose proof (E k1).
          rewrite !key_eq_dec_yes in * by reflexivity.
          invc H.
          f_equal.
          eapply ext_aux; eauto.
          intros k.
          specialize (E k).
          destruct K.eq_dec.
          * subst k. clear E.
            now rewrite !get_wf_aux_None by assumption.
          * auto.
        + pose proof E k2.
          rewrite key_eq_dec_yes with (k2 := k2) in H by reflexivity.
          rewrite key_eq_dec_no in H by auto using lt_neq, not_eq_sym.
          erewrite get_wf_aux_lt_None in H by eauto.
          discriminate.
    Qed.
  End Internal.

  Definition t V := { m : Internal.t V | Internal.wf m }.

  Definition empty {V} : t V :=
    exist _ Internal.empty (Internal.wf_empty _).

  Definition get V (k : key) (m : t V) : option V :=
    let (i, _) := m in
    Internal.get k i.

  Definition set V (k : key) (v : V) (m : t V) : t V :=
    let (i, pf) := m in
    exist _ (Internal.set k v i) (Internal.wf_set k v pf).

  Definition rem V (k : key) (m : t V) : t V :=
    let (i, pf) := m in
    exist _ (Internal.rem k i) (Internal.wf_rem k pf).

  Definition fresh V (m : t V) : key :=
    let (i, _) := m in
    Internal.fresh i.

  Lemma ge : forall V k, get(V:=V) k empty = None.
  Proof.
    unfold empty, get, set, rem, fresh.
    intros V k.
    apply Internal.ge.
  Qed.

  Lemma gs : forall V (m : t V) (k1 k2 : key) (v : V),
      get k2 (set k1 v m) = if K.eq_dec k2 k1 then Some v else get k2 m.
  Proof.
    unfold empty, get, set, rem, fresh.
    intros V [i pf] k1 k2 v.
    now apply Internal.gs.
  Qed.

  Lemma gss : forall V (k : key) (v : V) m, get k (set k v m) = Some v.
  Proof.
    unfold empty, get, set, rem, fresh.
    intros V k v [i pf].
    now apply Internal.gss.
  Qed.

  Lemma gso : forall V (k1 k2 : key) (v : V) m, k1 <> k2 -> get k2 (set k1 v m) = get k2 m.
  Proof.
    unfold empty, get, set, rem, fresh.
    intros V k1 k2 v [i pf] NE.
    now apply Internal.gso.
  Qed.

  Lemma gr : forall V (m : t V) (k1 k2 : key),
      get k2 (rem k1 m) = if K.eq_dec k2 k1 then None else get k2 m.
  Proof.
    unfold empty, get, set, rem, fresh.
    intros V [i pf] k1 k2.
    now apply Internal.gr.
  Qed.

  Lemma grs : forall V (k : key) (m : t V), get k (rem k m) = None.
  Proof.
    unfold empty, get, set, rem, fresh.
    intros V k [i pf].
    now apply Internal.grs.
  Qed.

  Lemma gro : forall V (k1 k2 : key) (m : t V), k1 <> k2 -> get k2 (rem k1 m) = get k2 m.
  Proof.
    unfold empty, get, set, rem, fresh.
    intros V k1 k2 [i pf] NE.
    now apply Internal.gro.
  Qed.

  Lemma gf : forall V (m : t V), get (fresh m) m = None.
  Proof.
    unfold empty, get, set, rem, fresh.
    intros V [i pf].
    now apply Internal.gf.
  Qed.

  Lemma ext : forall V (m1 m2 : t V), (forall k, get k m1 = get k m2) -> m1 = m2.
  Proof.
    unfold empty, get, set, rem, fresh.
    intros V [i1 pf1] [i2 pf2] Hext.
    assert (i1 = i2) by now apply Internal.ext.
    subst.
    f_equal.
    apply Internal.wf_irrelevant.
  Qed.
End SortedMap.

Module NatMap := SortedMap NatOrderedType.
