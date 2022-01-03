(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import String.
Require Import Coq.Program.Equality.
Require Import Definitions Binding Weakening Substitution.
Require Import RecordAndInertTypes.
Require Import ConstrLangAlt ConstrTyping ConstrNarrowing ConstrInterp.
Require Import ConstrBinding ConstrEntailment ConstrWeakening.
Require Import ConstrSubtypingLaws EntailmentLaws.
Require Import StrengtheningConstr.

Inductive simple_formed_constr : constr -> Prop :=

| sf_true : simple_formed_constr ⊤

| sf_false : simple_formed_constr ⊥

| sf_and : forall C1 C2,
    simple_formed_constr C1 ->
    simple_formed_constr C2 ->
    simple_formed_constr (C1 ⋏ C2)

| sf_or : forall C1 C2,
    simple_formed_constr C1 ->
    simple_formed_constr C2 ->
    simple_formed_constr (C1 ⋎ C2)

| sf_sub : forall s t S T,
    s ⩭ S ->
    t ⩭ T ->
    simple_formed_constr (s <⦂ t)

| sf_typ : forall x t T,
    t ⩭ T ->
    simple_formed_constr (ctrm_cvar (cvar_x (avar_f x)) ⦂ t)

.

Lemma simple_constr_empty_mapping : forall tm vm G C,
    simple_formed_constr C ->
    (tm, vm, G) ⊧ C ->
    (empty, empty, G) ⊧ C.
Proof.
  introv Hsf Hsat.
  dependent induction Hsf; eauto; inversions Hsat; eauto.
  - lets Heqs: (map_iso_ctyp tm vm H).
    lets Heqt: (map_iso_ctyp tm vm H0).
    lets Heqs1: (map_ctyp_unique_typ H5 Heqs).
    lets Heqt1: (map_ctyp_unique_typ H7 Heqt).
    subst. clear Heqs Heqt.
    lets Heqs: (map_iso_ctyp empty empty H).
    lets Heqt: (map_iso_ctyp empty empty H0).
    eauto.
  - lets Heqt: (map_iso_ctyp tm vm H).
    lets Heqt1: (map_ctyp_unique_typ H6 Heqt).
    clear Heqt.
    subst.
    lets Heqt: (map_iso_ctyp empty empty H).
    inversions H4. inversions H5.
    eapply sat_typ; try eassumption.
    constructor. constructor.
Qed.

Lemma subst_satisfy_aux1 : forall x y T G C,
    simple_formed_constr C ->
    binds x T G ->
    y # G ->
    (empty, empty, G) ⊧ C ->
    (empty, empty, G & y ~ T) ⊧ subst_constr x y C.
Proof.
  introv Hsf Hb HyG Hsat.
  dependent induction Hsf; eauto.
  - inversions Hsat.
  - inversions Hsat. simpl. eauto.
  - inversions Hsat; simpl; eauto.
  - admit.
  - inversions Hsat. inversions H4. inversions H5.
    simpl. cases_if.
    --

