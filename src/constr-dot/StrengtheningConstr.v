(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Program.Equality String.
Require Import Definitions Weakening Narrowing.
Require Import ConstrLangAlt ConstrTyping ConstrWeakening ConstrSubenvironments.
Require Import ConstrEntailment.
Require Import ConstrSubtypingLaws.


Lemma strengthen_constr_general_typing : forall C1 C2 G t T,
  C1 ⊩ C2 ->
  (C2, G) ⊢c t : T ->
  (C1, G) ⊢c t : T
with strengthen_constr_general_typing_def : forall C1 C2 G d D,
  C1 ⊩ C2 ->
  (C2, G) /-c d : D ->
  (C1, G) /-c d : D
with strengthen_constr_general_typing_defs : forall C1 C2 G ds D,
  C1 ⊩ C2 ->
  (C2, G) /-c ds :: D ->
  (C1, G) /-c ds :: D
with strengthen_constr_general_subtyping : forall C1 C2 G T U,
  C1 ⊩ C2 ->
  (C2, G) ⊢c T <: U ->
  (C1, G) ⊢c T <: U.
Proof.
  all: introv He Ht.
  - gen C1. dependent induction Ht; introv He.
    -- constructor. assumption.
    -- pick_fresh x.
       apply cty_all_intro with L. introv Hne0.
       apply* H0.
    -- apply* cty_all_elim.
    -- apply cty_new_intro with L.
       introv Hn. specialize (H x Hn). apply* strengthen_constr_general_typing_defs.
    -- apply cty_new_elim. apply* IHHt.
    -- apply cty_let with L T. apply* IHHt.
       introv Hne. specialize (H0 x Hne). apply* H0.
    -- apply cty_rec_intro. apply* IHHt.
    -- apply cty_rec_elim. apply* IHHt.
    -- apply cty_and_intro; try apply* IHHt1; try apply* IHHt2.
    -- apply cty_sub with T. apply* IHHt. apply* strengthen_constr_general_subtyping.
  - gen C1. dependent induction Ht; introv He.
    -- constructor.
    -- constructor. apply* strengthen_constr_general_typing.
  - gen C1. dependent induction Ht; introv He.
    -- constructor. apply* strengthen_constr_general_typing_def.
    -- constructor. apply* IHHt. apply* strengthen_constr_general_typing_def.
       exact H0.
  - gen C1. dependent induction Ht; introv He.
    -- apply csubtyp_intro with x S S'; try assumption.
       apply* IHHt. apply* ent_cong_and.
    -- apply* csubtyp_inst. apply* ent_trans.
Qed.
