(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Program.Equality String.
Require Import Definitions Weakening Narrowing.
Require Import ConstrLangAlt ConstrTyping ConstrWeakening ConstrSubenvironments.
Require Import ConstrSubtypingLaws.

Lemma narrow_constr_subtyping : forall C G G' T U,
    (C, G) ⊢c T <: U ->
    C ⊩e G' ⪯ G ->
    (C, G') ⊢c T <: U.
Proof.
  introv HTU Hsub. gen G'. dependent induction HTU; introv Hsub.
  - specialize (IHHTU _ _ eq_refl).
    dependent induction Hsub.
    -- apply binds_empty_inv in H0. destruct H0.
    -- 
Admitted.

Lemma narrow_constr_typing : forall C G G' t T,
    (C, G) ⊢c t : T ->
    C ⊩e G' ⪯ G ->
    (C, G') ⊢c t : T
with narrow_constr_typing_def : forall C G G' d D,
    (C, G) /-c d : D ->
    C ⊩e G' ⪯ G ->
    (C, G') /-c d : D
with narrow_constr_typing_defs : forall C G G' ds D,
    (C, G) /-c ds :: D ->
    C ⊩e G' ⪯ G ->
    (C, G') /-c ds :: D.
Proof.
  all: introv HT Hsub.
  - gen G'. dependent induction HT; introv Hsub.
    -- dependent induction Hsub.
       + apply binds_empty_inv in H. destruct H.
       + apply binds_push_inv in H. destruct_all.
         ++ subst. eapply cty_sub. apply cty_var. eauto.
            replace (G & x0 ~ T0) with (G & x0 ~ T0 & empty).
            eapply weaken_constr_subtyping. rewrite -> concat_empty_r. exact H0.
            rewrite -> concat_empty_r. exact H1. apply concat_empty_r.
         ++ replace (G & x0 ~ T0) with (G & x0 ~ T0 & empty); try apply concat_empty_r.
            eapply weaken_constr_typing. rewrite -> concat_empty_r. assumption.
            rewrite -> concat_empty_r. apply IHHsub. assumption.
    -- apply_fresh cty_all_intro as z. apply* H0. apply csubenv_grow; try assumption. eauto.
       apply csubtyp_refl.
    -- eapply cty_all_elim. apply* IHHT1. apply* IHHT2.
    -- apply_fresh cty_new_intro as z. apply* narrow_constr_typing_defs.
       eauto using csubtyp_refl.
    -- eapply cty_new_elim. apply* IHHT.
    -- apply_fresh cty_let as z. apply* IHHT. apply* H0.
       eauto using csubtyp_refl.
    -- eapply cty_rec_intro. apply* IHHT.
    -- eapply cty_rec_elim. apply* IHHT.
    -- eapply cty_and_intro. apply* IHHT1. apply* IHHT2.
  - dependent induction HT; constructor. apply* narrow_constr_typing.
  - dependent induction HT; constructor; try apply* narrow_constr_typing_def.
    apply* IHHT. assumption.
Qed.
