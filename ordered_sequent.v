From mm Require Import util.
Set Implicit Arguments.

Module prop.
  Inductive t :=
  | under : t -> t -> t
(*
  | over : t -> t -> t
  | fuse : t -> t -> t
  | twist : t -> t -> t
  | ichoose : t -> t -> t
  | uchoose : t -> t -> t
*)
  | one : t
  .

  Fixpoint size (A : t) : nat :=
    match A with
    | one => 1
    | under A1 A2 => S (size A1 + size A2)
    end.
End prop.

Module expr.
    Inductive t :=
    | var : t
    | tt : t
    | lettt : t -> t
    | underabs : t -> t
    | underapp : t -> t -> t
    .

    Fixpoint size (e : t) : nat :=
      match e with
      | var => 1
      | tt => 1
      | lettt e' => S (size e')
      | underabs e' => S (size e')
      | underapp e1 e2 => S (size e1 + size e2)
      end.
End expr.

Module cf_sequent.
  (* cut-free sequent calculus with proof terms *)

  Inductive t : list prop.t -> expr.t -> prop.t -> Prop :=
  | id : forall A, t [A] expr.var A
  | under_R : forall Ω A B e,
      t (B :: Ω) e A ->
      t Ω (expr.underabs e) (prop.under B A)
  | under_L : forall Ω_L Ω' Ω_R A B C e1 e2,
      t Ω' e1 B ->
      t (Ω_L ++ A :: Ω_R) e2 C ->
      t (Ω_L ++ Ω' ++ prop.under B A :: Ω_R) (expr.underapp e1 e2) C

  | one_R : t [] expr.tt prop.one
  | one_L : forall Ω_L Ω_R e C,
      t (Ω_L ++ Ω_R) e C ->
      t (Ω_L ++ prop.one :: Ω_R) (expr.lettt e) C
  .

  Lemma cut_admissible' :
    forall n e1 e2 A Ω Ω_L Ω_R C,
      prop.size A + expr.size e1 + expr.size e2 < n ->
      t Ω e1 A ->
      t (Ω_L ++ A :: Ω_R) e2 C ->
      exists e, t (Ω_L ++ Ω ++ Ω_R) e C /\ expr.size e <= expr.size e1 + expr.size e2.
  Proof.
    induction n; intros e1 e2 A Ω Ω_L Ω_R C LT SA SC.
    - omega.
    - invc SC.
      + apply app_singleton_middle_inv in H0.
        invc H0.
        rewrite app_nil_r.
        exists e1. split. auto. omega.
      + rewrite app_comm_cons in H.
        eapply IHn with (e2 := e) (e1 := e1) in H; eauto.
        2: simpl in *; omega.
        destruct H as [e' [? ?]].
        eexists.
        split.
        econstructor.
        exact H.
        simpl in *. omega.
      + simpl in *.
        rewrite <- app_ass in H.
        apply app_middle_inv in H.
        destruct H as [[? ? ?]|[W [? ?]]|[W [? ?]]]; subst.
        * invc SA.
          -- eexists. split.
             rewrite app_ass.
             simpl.
             apply under_L; eauto.
             simpl in *. omega.
          -- simpl in *.
             eapply IHn with (e1 := e0) (e2 := e) (Ω_L := []) in H4; eauto.
             2: omega.
             destruct H4 as [e' [He' Size']].
             simpl in *.
             eapply IHn with (e2 := e3)(e1 := e') in H1; eauto.
             2: omega.
             destruct H1 as [e'' [He'' Size'']].
             rewrite app_ass in *.
             eexists. split. eauto.
             omega.
          -- simpl in *.
             eapply under_L with (A := A0) in H0; eauto.
             rewrite <- app_ass in H0.
             eapply IHn with (A := prop.under B A0) in H0; eauto.
             2: simpl in *; omega.
             destruct H0 as [? [??]].
             rewrite !app_ass in *.
             rewrite <- app_ass in H0.
             rewrite <- app_ass in H0.
             simpl in H0.
             eapply under_L with (B := B0) in H0; eauto.
             rewrite !app_ass in *.
             eexists.
             split.
             eauto.
             simpl in *. omega.
          -- eapply under_L with (B := B)(A := A0) in H1; eauto.
             rewrite <- app_ass in H1.
             eapply IHn in H1; [| |eassumption].
             2: simpl in*; omega.
             destruct H1 as [?[??]].
             eexists. split.
             rewrite !app_ass.
             rewrite <- app_ass.
             rewrite <- app_ass.
             simpl.
             apply one_L.
             rewrite !app_ass in *.
             eassumption.
             simpl in *. omega.
        * apply app_inv in H.
          destruct H as [[W' [? ?]]|[W' [? ?]]]; subst.
          -- apply app_cons_inv in H2.
             destruct H2 as [[? ?]|[W1 [? ?]]]; subst.
             ++ rewrite app_nil_r in *.
                eapply IHn with (A := A) (Ω_L := []) in H0; [| |eassumption].
                2: omega.
                destruct H0 as [e' [S' Size']].
                simpl in S'.
                eapply under_L with (A := A0) (B := B) in H1; eauto.
                rewrite !app_ass in *.
                eexists.
                split. eauto.
                simpl in *; omega.
             ++ rewrite !app_ass in *.
                simpl in *.
                eapply IHn with (A := A) in H1; eauto.
                2: omega.
                destruct H1 as [e' [S' Size']].
                rewrite <- app_ass in S'.
                rewrite <- app_ass in S'.
                eapply under_L with (B := B) in S'; eauto.
                rewrite !app_ass in *.
                eexists. split. eauto.
                simpl in *. omega.
          -- eapply IHn with (A := A) in H0; eauto.
             2: omega.
             destruct H0 as [e' [S' Size']].
             eapply under_L with (B := B) in H1; eauto.
             rewrite !app_ass in *.
             eexists. split. eauto.
             simpl in *. omega.
        * rewrite app_comm_cons' in H1.
          rewrite <- app_ass in H1.
          eapply IHn with (A := A) in H1; eauto.
          2: omega.
          destruct H1 as [e' [S' Size']].
          rewrite !app_ass in *.
          simpl in *.
          eapply under_L with (B := B) in S'; eauto.
          eexists. split. eauto.
          simpl in *. omega.
      + destruct Ω_L; discriminate.
      + apply app_middle_inv in H.
        destruct H as [[? ? ?]|[W [? ?]]|[W [? ?]]]; subst.
        * invc SA.
          -- eexists. split.
             apply one_L. eauto.
             simpl in *. omega.
          -- apply one_L in H0.
             eapply IHn with (A := prop.one) in H0; [| |eassumption].
             2: simpl in *; omega.
             destruct H0 as [e' [S' Size']].
             rewrite !app_ass in *.
             simpl in *.
             rewrite <- app_ass in S'.
             eapply under_L with (B := B) in S'; eauto.
             rewrite !app_ass in *.
             eexists. split. eauto.
             simpl in *. omega.
          -- eexists. split. eauto.
             simpl in *. omega.
          -- rewrite app_ass. simpl.
             rewrite <- app_ass.

             eapply IHn with (e1 := e0)(e2 := expr.lettt e) in H.
             3: apply one_L; eassumption.
             2: simpl in *; omega.

             destruct H as [e' [He' Size']].
             eexists. split.
             apply one_L.
             rewrite !app_ass in *.
             eauto.
             simpl in *. omega.
        * rewrite app_ass in *.
          simpl in *.
          eapply IHn with (e2 := e) (e1 := e1) in H0; eauto.
          2: omega.
          destruct H0 as [? [? ?]].
          eexists. split.
          rewrite <- app_ass.
          rewrite <- app_ass.
          apply one_L.
          rewrite !app_ass.
          eauto.
          simpl in *. omega.
        * rewrite <- app_ass in H0.
          eapply IHn with (e1 := e1) (e2 := e) in H0; eauto.
          2: simpl in *; omega.
          destruct H0 as [? [? ?]].
          eexists. split.
          rewrite !app_ass in *.
          simpl.
          apply one_L.
          eauto.
          simpl in *. omega.
  Qed.

  Theorem cut_admissible :
    forall A e2 Ω e1 Ω_L Ω_R C,
      t Ω e1 A ->
      t (Ω_L ++ A :: Ω_R) e2 C ->
      exists e, t (Ω_L ++ Ω ++ Ω_R) e C.
  Proof.
    intros A e2 Ω e1 Ω_L Ω_R C SA SC.
    eapply cut_admissible' in SC; eauto.
    destruct SC as [? [? _]].
    eauto.
  Qed.
  Print Assumptions cut_admissible.
End cf_sequent.

Module sequent.

  Inductive t : list prop.t -> prop.t -> Prop :=
  | id : forall A, t [A] A
  | under_R : forall Ω A B,
      t (B :: Ω) A ->
      t Ω (prop.under B A)
  | under_L : forall Ω_L Ω' Ω_R A B C,
      t Ω' B ->
      t (Ω_L ++ A :: Ω_R) C ->
      t (Ω_L ++ Ω' ++ prop.under B A :: Ω_R) C

  | one_R : t [] prop.one
  | one_L : forall Ω_L Ω_R C,
      t (Ω_L ++ Ω_R) C ->
      t (Ω_L ++ prop.one :: Ω_R) C

  | cut : forall Ω_L Ω Ω_R A B,
      t Ω A ->
      t (Ω_L ++ A :: Ω_R) B ->
      t (Ω_L ++ Ω ++ Ω_R) B
  .

  Theorem cut_elim :
    forall Ω A,
      t Ω A ->
      exists e, cf_sequent.t Ω e A.
  Proof.
    induction 1.
    - eexists. constructor.
    - destruct IHt. eexists. econstructor. eauto.
    - destruct IHt1, IHt2. eexists.
      econstructor; eauto.
    - eexists. constructor.
    - destruct IHt.
      eexists. econstructor. eauto.
    - destruct IHt1, IHt2.
      eapply cf_sequent.cut_admissible; eauto.
  Qed.
End sequent.