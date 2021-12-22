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
Require Import ConstrCanonicalForms.

(** The typing of a term with a stack *)
Inductive constr_sta_trm_typ : sta * trm -> typ -> Prop :=
| constr_sta_trm_typ_c : forall G s t T,
    inert G ->
    G ⊨ C ->
    well_typed G s ->
    G ⊢ t : T ->
    sta_trm_typ (s, t) T.

