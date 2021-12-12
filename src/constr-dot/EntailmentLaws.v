(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Definitions RecordAndInertTypes.
Require Import ConstrLangAlt ConstrTyping ConstrInterp ConstrEntailment.
Require Import Coq.Program.Equality.

Lemma ent_trivial : forall C D,
    ⊤ ⊩ C ->
    D ⊩ C.
Proof.
  introv HC. introe. eauto.
Qed.

Lemma ent_sub_refl : forall T T',
    T ⩭ T' ->
    ⊤ ⊩ T <⦂ T.
Proof.
  introv Hiso. introe.
  econstructor; try apply* map_iso_ctyp. eauto.
Qed.

Lemma ent_sub_refl' : forall C T T',
    T ⩭ T' ->
    C ⊩ T <⦂ T.
Proof.
  introv Hiso. apply ent_trivial. apply* ent_sub_refl.
Qed.


