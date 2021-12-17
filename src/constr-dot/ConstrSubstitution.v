(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import String.
Require Import Coq.Program.Equality.
Require Import Definitions Binding Weakening.
Require Import ConstrLangAlt ConstrTyping ConstrNarrowing.
Require Import ConstrBinding ConstrEntailment.

Lemma subst_csubtyp : forall x y S C G1 G2 G T U,
    G = G1 & x ~ S & G2 ->
    (C, G) ⊢c T <: U ->
    ok G ->
    x \notin fv_ctx_types G1 ->
    (subst_constr x y C, G1 & (subst_ctx x y G2)) ⊢c trm_var (avar_f y) : subst_typ x y S ->
    (subst_constr x y C, G1 & (subst_ctx x y G2)) ⊢c subst_typ x y T <: subst_typ x y U.
Proof.
  introv Heq HTU Hok Hx Hsub. subst.
  dependent induction HTU.
  - admit.
  -

  destruct (min_complete_exists (G1 & x ~ S & G2)) as [rG Hr].
  destruct (iso_ctyp_exists T) as [T' HT].
  destruct (iso_ctyp_exists U) as [U' HU].
  eapply subtyp_imply_ent in HTU; try eassumption.
