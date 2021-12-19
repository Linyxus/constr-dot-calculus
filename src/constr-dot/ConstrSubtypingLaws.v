(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Definitions RecordAndInertTypes.
Require Import ConstrLangAlt ConstrTyping ConstrInterp ConstrEntailment.
Require Import EntailmentLaws.
Require Import Coq.Program.Equality.

Lemma csubtyp_refl : forall C G T,
    (C, G) ⊢c T <: T.
Proof.
  introv.
  destruct (iso_ctyp_exists T) as [T' Ht].
  eapply csubtyp_inst; try eassumption. apply* ent_sub_refl'.
Qed.

