(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import TLC.LibList.
Require Import Coq.Program.Equality String.
Require Import Definitions Weakening Narrowing RecordAndInertTypes.
Require Import ConstrLangAlt ConstrTyping.
Require Import ConstrInterp ConstrEntailment.
Require Import Stricting.

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

Lemma min_complete_to_stricter : forall rG G tm vm G',
    min_complete rG G ->
    ok G' ->
    inert G' ->
    (tm, vm, G') ⊧ rG ->
    stricter_env G G'.
Proof.
  introv Hr Hok Hi Hs. unfold stricter_env.
  introv HB.
  destruct (iso_ctyp_exists T) as [t Ht].
  lets Hsb: (min_complete_ent_bound Hr Ht HB).
  apply Hsb in Hs; eauto. inversions Hs.
  lets Hmt: (map_iso_ctyp tm vm Ht).
  lets Heqt: (map_ctyp_unique_typ H5 Hmt). subst T'.
  inversions H3. inversions H4. assumption.
Qed.

Lemma min_complete_entails_sub : forall rG G s t S T,
    min_complete rG G ->
    s ⩭ S ->
    t ⩭ T ->
    G ⊢ S <: T ->
    rG ⊩ s <⦂ t.
Proof.
  introv Hr His Hit HST. introe.
  lets Hse: (min_complete_to_stricter Hr Hok H0 H).
  lets HST0: (subtyp_strict Hse Hok HST).
  lets Hms: (map_iso_ctyp tm vm His).
  lets Hmt: (map_iso_ctyp tm vm Hit).
  eapply sat_sub. exact Hms. exact Hmt.
  assumption.
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
    exact H0. apply IHHc. unfold constr_entail. introv Hi Hok Hsat.
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

Lemma ent_and_combine : forall C D1 D2,
    C ⊩ D1 ->
    C ⊩ D2 ->
    C ⊩ D1 ⋏ D2.
Proof.
  introv H1 H2. introe. eauto.
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
