(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Program.Equality String.
Require Import Definitions Weakening Narrowing RecordAndInertTypes.
Require Import ConstrLangAlt ConstrTyping ConstrWeakening ConstrSubenvironments.
Require Import ConstrInterp ConstrEntailment.
Require Import ConstrSubtypingLaws.
Require Import StrengtheningConstr.

Lemma weaken_constr_subenv : forall C D G G',
    C ⊩ D ->
    D ⊩e G ⪯ G' ->
    C ⊩e G ⪯ G'.
Proof.
  introv HCD Hsub. gen C.
  dependent induction Hsub; introv HCD; eauto 1.
  eapply csubenv_grow. apply* IHHsub. assumption.
  eapply strengthen_constr_general_subtyping. exact HCD.
  exact H0.
Qed.

Lemma csubenv_binds_inv : forall C x T G' G,
    binds x T G ->
    C ⊩e G' ⪯ G ->
    (exists T', binds x T' G' /\ (C, G') ⊢c T' <: T).
Proof.
  introv Hb Hsub.
  dependent induction Hsub.
  - destruct (binds_empty_inv Hb).
  - apply binds_push_inv in Hb as Hb1. destruct_all.
    -- subst. exists T0. split; eauto 1.
       replace (G & x0 ~ T0) with (G & x0 ~ T0 & empty).
       apply weaken_constr_subtyping. rewrite -> concat_empty_r. assumption.
       rewrite -> concat_empty_r. assumption. apply concat_empty_r.
    -- specialize (IHHsub H2). destruct IHHsub as [t [Hbt Ht]].
       exists t. split; eauto 2. pose proof (concat_empty_r (G & x0 ~ T0)) as Heq.
       rewrite <- Heq. apply weaken_constr_subtyping. rewrite -> concat_empty_r.
       eauto. rewrite -> concat_empty_r. assumption.
Qed.

Lemma extended_constr_satisfy : forall tm vm G C x T T',
    T ⩭ T' ->
    (tm, vm, G) ⊧ C ->
    binds x T' G ->
    (tm, vm, G) ⊧ C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ T.
Proof.
  introv Hiso Hsat Hx.
  eapply sat_and; auto. apply sat_typ with (trm_var (avar_f x)) T'.
  apply map_ctrm_cvar. constructor.
  apply map_iso_ctyp; auto. eauto.
Qed.

Lemma constr_to_subtyping : forall C G T U,
    inert G ->
    G ⊨ C ->
    (C, G) ⊢c T <: U ->
    G ⊢ T <: U.
Proof.
  introv Hi Hsat Hsub. destruct Hsat as [tm [vm Hsat]].
  dependent induction Hsub.
  - specialize (IHHsub G Hi (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S)).
    apply~ IHHsub. apply* extended_constr_satisfy.
  - assert (Hsat2 : (tm, vm, G) ⊧ S <⦂ T) by eauto.
    inversion Hsat2; subst.
    assert (Heqs : S' = S'0) by apply* map_iso_ctyp_eq.
    assert (Heqt : T' = T'0) by apply* map_iso_ctyp_eq.
    subst. assumption.
Qed.

Lemma narrow_constr_subtyping : forall C G G' T U,
    (C, G) ⊢c T <: U ->
    C ⊩e G' ⪯ G ->
    (C, G') ⊢c T <: U.
Proof.
  introv HTU Hsub. gen G'. dependent induction HTU; introv Hsub.
    - specialize (IHHTU _ _ eq_refl).
      assert (Hent1 : C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S ⊩e G' ⪯ G). {
        apply* weaken_constr_subenv. apply* ent_and_left.
      }
      specialize (IHHTU _ Hent1).
      destruct (csubenv_binds_inv H0 Hsub) as [t [Hbt Ht]].
      destruct (iso_ctyp_exists t) as [t' Hiso].
      eapply csubtyp_intro. exact Hiso. exact Hbt.
      eapply strengthen_constr_general_subtyping; try apply IHHTU.
    - eauto.
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
