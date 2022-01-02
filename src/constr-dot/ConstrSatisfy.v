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

