(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Definitions.
Require Import ConstrLangAlt ConstrTyping.

Require Import Coq.Program.Equality.

Lemma weaken_constr_subtyping : forall C G1 G2 G3 T U,
    ok (G1 & G2 & G3) ->
    (C, G1 & G3) ⊢c T <: U ->
    (C, G1 & G2 & G3) ⊢c T <: U.
Proof.
  introv Hok Hsub.
  dependent induction Hsub.
  - specialize (IHHsub (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S) G1 G3 Hok).
    eapply csubtyp_intro. exact H. apply* binds_weaken.
    apply* IHHsub.
  - eapply csubtyp_inst. exact H. exact H0. exact H1.
Qed.

Lemma weaken_constr_typing : forall C G1 G2 G3 t T,
    ok (G1 & G2 & G3) ->
    (C, G1 & G3) ⊢c t : T ->
    (C, G1 & G2 & G3) ⊢c t : T
with weaken_constr_typing_def : forall C G1 G2 G3 d D,
    ok (G1 & G2 & G3) ->
    (C, G1 & G3) /-c d : D ->
    (C, G1 & G2 & G3) /-c d : D
with weaken_constr_typing_defs : forall C G1 G2 G3 ds D,
    ok (G1 & G2 & G3) ->
    (C, G1 & G3) /-c ds :: D ->
    (C, G1 & G2 & G3) /-c ds :: D.
Proof.
  all: introv Hok HT.
  - dependent induction HT.
    -- constructor. apply* binds_weaken.
    -- apply_fresh cty_all_intro as z.
       assert (Hne : z \notin L) by eauto.
       assert (Hok1 : ok (G1 & G2 & (G3 & z ~ T))). {
         rewrite -> concat_assoc. eauto.
       }
       specialize (H0 z Hne C G1 (G3 & z ~ T) Hok1).
       rewrite <- concat_assoc. apply H0. rewrite -> concat_assoc.
       exact JMeq_refl.
    -- eapply cty_all_elim. apply* IHHT1. apply* IHHT2.
    -- apply_fresh cty_new_intro as z. rewrite <- concat_assoc.
       apply* weaken_constr_typing_defs. rewrite -> concat_assoc. eauto.
       rewrite -> concat_assoc. apply* H.
    -- apply cty_new_elim. apply* IHHT.
    -- apply_fresh cty_let as z. apply* IHHT.
       rewrite <- concat_assoc. apply* H0. rewrite -> concat_assoc. eauto.
       rewrite -> concat_assoc. eauto.
    -- apply cty_rec_intro. apply* IHHT.
    -- apply cty_rec_elim. apply* IHHT.
    -- apply cty_and_intro. apply* IHHT1. apply* IHHT2.
    -- eapply cty_sub. apply* IHHT. apply* weaken_constr_subtyping.
  - dependent induction HT.
    -- constructor.
    -- constructor. apply* weaken_constr_typing.
  - dependent induction HT.
    -- constructor. apply* weaken_constr_typing_def.
    -- constructor. apply* weaken_constr_typing_defs. apply* weaken_constr_typing_def.
       assumption.
Qed.

Theorem subtyping_weaken_constr : forall x S S' C G T U,
    S ⩭ S' ->
    binds x S' G ->
    (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S, G) ⊢c T <: U ->
    (C, G) ⊢c T <: U.
Proof.
  introv Hiso Hx HT.
  eapply csubtyp_intro. exact Hiso. exact Hx. exact HT.
Qed.

Theorem typing_weaken_constr : forall x S S' C G t T,
    S ⩭ S' ->
    binds x S' G ->
    (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S, G) ⊢c t : T ->
    (C, G) ⊢c t : T
with typing_def_weaken_constr : forall x S S' C G d D,
    S ⩭ S' ->
    binds x S' G ->
    (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S, G) /-c d : D ->
    (C, G) /-c d : D
with typing_defs_weaken_constr : forall x S S' C G ds D,
    S ⩭ S' ->
    binds x S' G ->
    (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S, G) /-c ds :: D ->
    (C, G) /-c ds :: D.
Proof.
  all: introv Hiso Hb HT.
  - dependent induction HT.
    -- constructor. exact H.
    -- apply cty_all_intro with (L \u \{x}). eauto.
    -- apply cty_all_elim with S0. apply* IHHT1.
       apply* IHHT2.
    -- apply cty_new_intro with (L \u \{x}). intros y Hne.
       eapply typing_defs_weaken_constr.
       apply Hiso.
       assert (Hb' : binds x S' (G & y ~ open_typ y T)) by eauto.
       exact Hb'. apply~ H.
    -- apply cty_new_elim. apply* IHHT.
    -- apply cty_let with (L \u \{x}) T. apply* IHHT. intros y Hne.
       apply~ H0. exact Hiso. eauto.
    -- apply cty_rec_intro. apply* IHHT.
    -- apply cty_rec_elim. apply* IHHT.
    -- apply cty_and_intro. apply* IHHT1. apply* IHHT2.
    -- apply cty_sub with T. apply* IHHT. eapply subtyping_weaken_constr.
       apply Hiso. apply Hb. apply H.
  - dependent induction HT.
    -- apply cty_def_typ.
    -- apply cty_def_trm. eapply typing_weaken_constr.
       exact Hiso. exact Hb. exact H.
  - dependent induction HT.
    -- apply cty_defs_one. eapply typing_def_weaken_constr.
       exact Hiso. exact Hb. exact H.
    -- apply cty_defs_cons. apply* IHHT. eapply typing_def_weaken_constr; eassumption.
       exact H0.
Qed.
