Set Implicit Arguments.

Require Import Coq.Program.Equality String.
Require Import Binding CanonicalForms Definitions GeneralToTight InvertibleTyping Narrowing
            OperationalSemantics PreciseTyping RecordAndInertTypes Substitution Weakening.
Require Import ConstrLangAlt ConstrEntailment ConstrInterp ConstrTyping.
Require Import EntailmentLaws ConstrSubtypingLaws.
Require Import TightConstrInterp TightConstrEntailment TightConstrTyping.
Require Import PreciseConstrTyping.
Require Import ConstrWeakening ConstrNarrowing.
Require Import ConstrBinding.
Require Import InvertibleConstrTyping.
Require Import ConstrSubstitution.
Require Import ConstrCanonicalForms.

(** The typing of a term with a stack *)
Inductive constr_sta_trm_typ : sta * trm -> typ -> Prop :=
| constr_sta_trm_typ_c : forall C G s t T,
    inert G ->
    G ⊨ C ->
    constr_well_typed C G s ->
    (C, G) ⊢c t : T ->
    constr_sta_trm_typ (s, t) T.

Hint Constructors constr_sta_trm_typ.

Notation "'⊢c' t ':' T" := (constr_sta_trm_typ t T) (at level 40, t at level 59).

(** * Preservation *)

(** If a value [v] has type [T], then [v] has a precise type [T']
    that is a subtype of [T].
    This lemma corresponds to Lemma 3.15 in the paper. *)
Lemma constr_val_typing: forall C G v T,
  (C, G) ⊢c trm_val v : T ->
  exists T', (C, G) ⊢c!v v : T' /\
        (C, G) ⊢c T' <: T.
Proof.
  introv H. dependent induction H; eauto using csubtyp_refl.
  destruct (IHcty_trm _ _ _ eq_refl eq_refl). destruct_all.
  eauto using constr_subtyping_trans.
Qed.

Ltac binds_eq :=
  match goal with
  | [Hb1: binds ?x _ ?G,
     Hb2: binds ?x _ ?G |- _] =>
     apply (binds_functional Hb1) in Hb2; inversions Hb2
  end.

Ltac invert_red :=
  match goal with
  | [Hr: (_, _) |-> (_, _) |- _] => inversions Hr
  end.


(** [s: G]                  #<br>#
    [inert [G]              #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [G ⊢ t: T]              #<br>#
    [―――――――――――――――――――]   #<br>#
    [exists G', inert G']        #<br>#
    [s': G, G']             #<br>#
    [G, G' ⊢ t': T]         *)
Lemma constr_preservation_helper: forall C G s t s' t' T,
    constr_well_typed C G s ->
    inert G ->
    G ⊨ C ->
    (s, t) |-> (s', t') ->
    (C, G) ⊢c t : T ->
    exists G', inert G' /\
          (G & G') ⊨ C /\
          constr_well_typed C (G & G') s' /\
          (C, G & G') ⊢c t' : T.
Proof.
  introv Hwf Hin Hsat Hred Ht. gen t'.
  dependent induction Ht; intros; try solve [invert_red].
  - Case "ty_all_elim"%string.
    match goal with
    | [Hx: _ ⊢c trm_var (avar_f _) : typ_all _ _ |- _] =>
        pose proof (constr_canonical_forms_fun Hin Hsat Hwf Hx) as [L [T' [t [Bis [Hsub Hty]]]]];
        inversions Hred;
        binds_eq
    end.
    exists (@empty typ). rewrite concat_empty_r. repeat_split_right; auto.
    pick_fresh_gen (fv_ctx_types G \u fv_typ S \u fv_typ T \u fv_trm t0 \u fv_constr C \u L \u dom G) y.
    assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    apply* renaming_ctyp; eauto.
  - Case "ty_new_elim"%string.
    pose proof (constr_canonical_forms_obj Hin Hsat Hwf Ht) as [S [ds [t [Bis [Has Ty]]]]].
    invert_red. binds_eq.
    exists (@empty typ). rewrite concat_empty_r. repeat_split_right; auto.
    rewrite* <- (defs_has_inv Has H5).
  - Case "ty_let"%string.

    Ltac solve_IH :=
      match goal with
      | [IH: forall G, inert _ ->
            forall C, constr_well_typed _ _ _ ->
            _ ⊨ _ ->
            _ = _ ->
            forall t', (_, _) |-> (_, _) -> _,
          In: inert _,
          Wf: constr_well_typed _ _ _,
          Sat: _ ⊨ _,
          Hr: (_, _) |-> (_, ?t') |- _] =>
        idtac IH;
        specialize (IH _ In _ Wf Sat eq_refl _ Hr); destruct_all
      end;
      match goal with
      | [Hi: (_, _ & ?G') ⊢c _ : _ |- _] =>
        exists G'; repeat_split_right; auto
      end.

    Ltac solve_let :=
      invert_red; solve_IH; constr_fresh_constructor; eauto; try apply* weaken_constr_typing.

    destruct t; try solve [solve_let].
    + SCase "[t = (let x = a in u)] where a is a variable".
      repeat invert_red.
      exists (@empty typ). rewrite concat_empty_r. repeat_split_right; auto.
      apply* constr_renaming_fresh.
    + SCase "[t = (let x = v in u)] where v is a value".
      repeat invert_red.
      match goal with
        | [Hn: ?x # ?s |- _] =>
          pose proof (constr_well_typed_notin_dom Hwf Hn) as Hng
      end.
      pose proof (constr_val_typing Ht) as [V [Hv Hs]].
      exists (x ~ V). repeat_split_right.
      ** rewrite <- concat_empty_l. constructor~. apply (constr_precise_inert_typ Hv).
      ** apply~ constr_satisfiable_push.
      ** apply~ constr_well_typed_push. apply (constr_precise_to_general_v Hv).
      ** eapply constr_renaming_fresh with (L:=L \u dom G \u \{x}). apply* ok_push.
         intros. apply* weaken_constr_typing. apply cty_sub with (T:=V); auto. apply* weaken_csubtyp.
  - Case "ty_sub"%string.
    solve_IH.
    match goal with
    | [Hs: _ ⊢c _ <: _,
       Hg: (_, _ & ?G') ⊢c _: _ |- _] =>
      apply weaken_csubtyp with (G2:=G') in Hs;
      eauto
    end.
Qed.

(** ** Preservation Theorem *)

(** [⊢ (s, t): T]           #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [―――――――――――――――――――]   #<br>#
    [⊢ (s', t'): T]         *)
Theorem constr_preservation : forall s s' t t' T,
    ⊢c (s, t) : T ->
    (s, t) |-> (s', t') ->
    ⊢c (s', t') : T.
Proof.
  introv Ht Hr. destruct Ht as [* Hi Hsat Hwf Ht].
  lets Hp: (constr_preservation_helper Hwf Hi Hsat Hr Ht). destruct Hp as [G' [Hi' [Hsat' [Hwf' Ht']]]].
  apply constr_sta_trm_typ_c with (C:=C) (G:=G & G'); auto. apply* inert_concat.
Qed.

(** * Progress *)

(** ** Progress Theorem *)

(** [⊢ (s, t): T]           #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [―――――――――――――――――――]   #<br>#
    [t] is in normal form   #<br>#
    or [exists s', t'] such that [(s, t) |-> (s', t')] *)
Theorem progress: forall s t T,
    ⊢c (s, t) : T ->
    norm_form t \/ exists s' t', (s, t) |-> (s', t').
Proof.
  introv Ht. inversion Ht as [C G s' t' T' Hi Hsat Hwt HT]. subst.
  dependent induction HT; eauto.
  - Case "ty_all_elim"%string.
    pose proof (constr_canonical_forms_fun Hi Hsat Hwt HT1). destruct_all. right*.
  - Case "ty_new_elim"%string.
    pose proof (constr_canonical_forms_obj Hi Hsat Hwt HT). destruct_all. right*.
  - Case "ty_let"%string.
    Ltac solve_let_prog :=
      match goal with
      | [IH: forall G, inert _ ->
             forall C, _ ⊨ _ ->
             constr_well_typed _ _ _ ->
             ⊢c (?s, ?t) : ?T ->
             _ = _ -> _,
         Hi: inert _,
         Hsat: _ ⊨ _,
         Hwt: constr_well_typed _ _ _ |- _] =>
        idtac IH;
        assert (⊢c (s, t): T) as Hs by eauto;
        specialize (IH _ Hi _ Hsat Hwt Hs eq_refl) as [IH | [s' [t' Hr]]];
        eauto; inversion IH
      end.
    right. destruct t; try solve [solve_let_prog].
    + pose proof (constr_var_typing_implies_avar_f HT) as [x A]. subst*.
    + constr_pick_fresh x. exists (s & x ~ v) (open_trm x u). auto.
Qed.
