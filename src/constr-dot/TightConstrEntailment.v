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
Require Import ConstrEntailment.
Require Import TightConstrInterp.

(** * Tight Entailment for Constraints *)

(** ** Definition of tight entailment *)
Definition constr_entail_t (C1 C2 : constr) :=
  forall tm vm G,
    inert G ->
    (tm, vm, G) ⊧# C1 -> (tm, vm, G) ⊧# C2.

Notation "C '⊩#' D" := (constr_entail_t C D) (at level 50).

(** * Equivalence Theorems *)

Theorem tight_to_general_entailment : forall C1 C2,
    C1 ⊩# C2 -> C1 ⊩ C2.
Proof.
  introv Ht. introe.
  apply* tight_to_general_interp.
  apply* Ht.
  apply* general_to_tight_interp.
Qed.

Theorem general_to_tight_entailment : forall C1 C2,
    C1 ⊩ C2 -> C1 ⊩# C2.
Proof.
  introv Ht. introe.
  apply* general_to_tight_interp.
  apply* Ht.
  apply* tight_to_general_interp.
Qed.
