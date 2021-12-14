(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import TLC.LibList.
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

Inductive min_complete : constr -> ctx -> Prop :=
| min_complete_nil : min_complete ⊤ nil
| min_complete_grow : forall x T T' C G,
    T ⩭ T' ->
    min_complete C G ->
    min_complete (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ T) (G & x ~ T').

Hint Constructors min_complete.

Lemma min_complete_exists : forall G,
    exists C, min_complete C G.
Proof.
  introv. dependent induction G; eauto. destruct a as [x T].
  destruct (iso_ctyp_exists T) as [T' HT].
  destruct IHG as [C IH].
  exists (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ T').
  replace ((x, T) :: G) with (G & x ~ T). eauto.
  rew_env_defs. rewrite -> app_cons_l. rewrite -> app_nil_l.
  auto.
Qed.

Inductive compatible : constr -> ctx -> Prop :=
| partly_compatible_true : forall G, compatible ⊤ G
| partly_compatible_grow : forall x T T' C G,
    T ⩭ T' ->
    binds x T' G ->
    compatible C G ->
    compatible (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ T) G.

Inductive subconstr : constr -> constr -> Prop :=
| subconstr_empty : subconstr ⊤ ⊤
| subconstr_grow_one : forall C C' F,
    subconstr C C' ->
    subconstr C (C' ⋏ F)
| subconstr_grow_both : forall C C' F,
    subconstr C C' ->
    subconstr (C' ⋏ F) (C' ⋏ F)
.
Lemma min_complete_ent_bound : forall rG G x T T',
    min_complete rG G ->
    T ⩭ T' ->
    binds x T' G ->
    rG ⊩ ctrm_cvar (cvar_x (avar_f x)) ⦂ T.
Proof.
  introv Hr Hiso Hb. dependent induction Hr.
  - rewrite <- empty_def in Hb. destruct (binds_empty_inv Hb).
  - specialize (IHHr Hiso). pose proof (binds_push_inv Hb). destruct_all.
    -- subst. pose proof (iso_ctyp_unique H Hiso) as Heq. subst.
       apply ent_and_right.
    -- specialize (IHHr H1). eapply ent_trans. eapply ent_and_left. assumption.
Qed.

Lemma ent_and_combine : forall C D1 D2,
    C ⊩ D1 ->
    C ⊩ D2 ->
    C ⊩ D1 ⋏ D2.
Proof.
  introv H1 H2. introe. eauto.
Qed.

Lemma ent_and_assoc2 : forall C1 C2 C3,
    C1 ⋏ (C2 ⋏ C3) ⊩ (C1 ⋏ C2) ⋏ C3 .
Proof.
  introe. inversion H; subst. inversion H7; subst.
  eauto.
Qed.

Lemma ent_imply_subtyp_aux : forall rG G C T T' U U',
    compatible rG G ->
    T ⩭ T' ->
    U ⩭ U' ->
    C ⋏ rG ⊩ T <⦂ U ->
    (C, G) ⊢c T' <: U'.
Proof.
  introv Hc HT HU HTU. gen C.
  dependent induction Hc; introv HTU.
  - eapply csubtyp_inst; eauto 1. eapply ent_trans.
    eapply ent_and_intro. apply ent_tautology. assumption.
  - specialize (IHHc HT HU). eapply csubtyp_intro. exact H.
    exact H0. apply IHHc. unfold constr_entail. introv Hi Hsat.
    apply HTU; auto. inversion Hsat; subst. inversion H3; subst.
    eauto.
Qed.

Lemma compatible_push_env : forall C G x T,
    ok (G & x ~ T) ->
    compatible C G ->
    compatible C (G & x ~ T).
Proof.
  introv Hg Hc. dependent induction Hc.
  - constructor.
  - specialize (IHHc Hg).
    econstructor. exact H. apply binds_concat_left_ok; auto.
    assumption.
Qed.

Lemma min_complete_imply_compatible : forall C G,
    ok G ->
    min_complete C G ->
    compatible C G.
Proof.
  introv Hg Hr.
  dependent induction Hr; try constructor.
  econstructor. exact H. apply* binds_push_eq. apply* compatible_push_env.
Qed.

Lemma ent_imply_subtyp : forall rG G C T T' U U',
    ok G ->
    min_complete rG G ->
    T ⩭ T' ->
    U ⩭ U' ->
    C ⋏ rG ⊩ T <⦂ U ->
    (C, G) ⊢c T' <: U'.
Proof.
  introv Hg Hr HT HU Hent. apply* ent_imply_subtyp_aux.
  apply* min_complete_imply_compatible.
Qed.

Lemma subtyp_imply_ent : forall rG G C T T' U U',
    min_complete rG G ->
    T ⩭ T' ->
    U ⩭ U' ->
    (C, G) ⊢c T' <: U' ->
    C ⋏ rG ⊩ T <⦂ U.
Proof.
  introv Hr HT HU HTU.
  dependent induction HTU.
  - specialize (IHHTU _ _ Hr HT HU eq_refl). eapply ent_trans; try apply IHHTU.
    eapply ent_and_combine; try apply ent_and_right.
    eapply ent_and_combine; try apply ent_and_left.
    eapply ent_trans. apply ent_and_right.
    apply* min_complete_ent_bound.
  - eapply ent_trans. apply ent_and_left.
    pose proof (iso_ctyp_unique H HT) as Heq; subst.
    pose proof (iso_ctyp_unique H0 HU) as Heq; subst.
    eauto.
Qed.

Lemma ent_csubtyp_equiv : forall D G C T T' U U',
    ok G ->
    min_complete D G ->
    T ⩭ T' ->
    U ⩭ U' ->
    (C ⋏ D ⊩ T <⦂ U <-> (C, G) ⊢c T' <: U').
Proof.
  introv Hok Hr HT HU. split; intros.
  apply* ent_imply_subtyp.
  apply* subtyp_imply_ent.
Qed.

Lemma ent_typ_sub : forall t S T,
    t ⦂ S ⋏ S <⦂ T ⊩ t ⦂ T.
Proof.
  introe. inv_sat. inv_sat. inv_sat.
  pose proof (map_ctyp_unique_typ H5 H10) as Heq. subst.
  apply* sat_typ.
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
      destruct (iso_ctyp_exists T) as [T' HT].
      destruct (iso_ctyp_exists U) as [U' HU].
      destruct (min_complete_exists G') as [rG' Hr'].
      apply* ent_imply_subtyp.
      apply (subtyp_imply_ent Hr' HT HU) in IHHTU.
      apply (subtyp_imply_ent Hr' Hiso H) in Ht.
      unfold constr_entail. introv Hi Hsat.
      apply* IHHTU. inv_sat. apply* sat_and.
      inv_sat. apply* sat_and. apply* ent_typ_sub.
    - eauto.
Qed.

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
    -- eapply cty_sub. apply* IHHT. apply* narrow_constr_subtyping.
  - dependent induction HT; constructor. apply* narrow_constr_typing.
  - dependent induction HT; constructor; try apply* narrow_constr_typing_def.
    apply* IHHT. assumption.
Qed.
