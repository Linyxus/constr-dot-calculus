(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import TLC.LibLN.
Require Import String.
Require Import Coq.Program.Equality.

Require Import Definitions RecordAndInertTypes Decompose ConstrLangAlt ConstrInterp.
Require Import TightTyping GeneralToTight.

(** * Tight Interpretation of Constraints *)

Reserved Notation "e '⊧#' C" (at level 40).

Inductive satisfy_constr_t : (tctx * vctx * ctx) -> constr -> Prop :=

| sat_true_t : forall tm vm G,
    (tm, vm, G) ⊧# ⊤

| sat_and_t : forall tm vm G C1 C2,
    (tm, vm, G) ⊧# C1 ->
    (tm, vm, G) ⊧# C2 ->
    (tm, vm, G) ⊧# C1 ⋏ C2

| sat_or1_t : forall tm vm G C1 C2,
    (tm, vm, G) ⊧# C1 ->
    (tm, vm, G) ⊧# C1 ⋎ C2

| sat_or2_t : forall tm vm G C1 C2,
    (tm, vm, G) ⊧# C2 ->
    (tm, vm, G) ⊧# C1 ⋎ C2

| sat_exists_typ_t : forall L tm vm G T C,
    (forall x, x \notin L -> (tm & x ~ T, vm, G) ⊧# C ^^t x) ->
    (tm, vm, G) ⊧# (∃t C)

| sat_exists_var_t : forall L tm vm G u C,
    (forall x, x \notin L -> (tm, vm & x ~ u, G) ⊧# C ^^v x) ->
    (tm, vm, G) ⊧# (∃v C)

| sat_typ_t : forall tm vm G t t' T T',
    (tm, vm) ⊢v t ⪯ t' ->
    (tm, vm) ⊢t T ⪯ T' ->
    G ⊢# t' : T' ->
    (tm, vm, G) ⊧# t ⦂ T

| sat_sub_t : forall tm vm G S S' T T',
    (tm, vm) ⊢t S ⪯ S' ->
    (tm, vm) ⊢t T ⪯ T' ->
    G ⊢# S' <: T' ->
    (tm, vm, G) ⊧# S <⦂ T

where "e '⊧#' C" := (satisfy_constr_t e C).

Hint Constructors satisfy_constr_t.

Theorem tight_to_general_interp : forall tm vm G C,
    (tm, vm, G) ⊧# C ->
    (tm, vm, G) ⊧ C.
Proof.
  introv Ht.
  dependent induction Ht; eauto.
  - apply* sat_typ. apply~ tight_to_general.
  - apply* sat_sub. apply~ tight_to_general.
Qed.

Theorem general_to_tight_interp : forall tm vm G C,
    inert G ->
    (tm, vm, G) ⊧ C ->
    (tm, vm, G) ⊧# C.
Proof.
  introv Hi Hg.
  dependent induction Hg; eauto.
  - apply* sat_typ_t. apply* general_to_tight.
  - apply* sat_sub_t. apply* general_to_tight.
Qed.
