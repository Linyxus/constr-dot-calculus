(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Definitions RecordAndInertTypes.
Require Import ConstrLangAlt ConstrTyping ConstrInterp ConstrEntailment.
Require Import Weakening.
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

Lemma ent_cong_and_right : forall C D1 D2,
    D1 ⊩ D2 ->
    C ⋏ D1 ⊩ C ⋏ D2.
Proof.
  introv Hent. introe.
  inv_sat. constructor*.
Qed.

Lemma ent_and_true_intro2 : forall C,
    C ⊩ C ⋏ ⊤.
Proof.
  introe. constructor*.
Qed.

(** * Type System Laws *)

Lemma ent_sub_top : forall C T T',
    T ⩭ T' ->
    C ⊩ T <⦂ ctyp_top.
Proof.
  introv Hiso. apply ent_trivial. introe.
  lets Hm: (map_iso_ctyp tm vm Hiso).
  eapply sat_sub. exact Hm. constructor.
  eauto.
Qed.

Lemma ent_sub_bot : forall C T T',
    T ⩭ T' ->
    C ⊩ ctyp_bot <⦂ T.
Proof.
  introv Hiso. apply ent_trivial. introe.
  lets Hm: (map_iso_ctyp tm vm Hiso).
  eapply sat_sub. constructor. exact Hm.
  eauto.
Qed.

Lemma ent_sub_refl' : forall C T T',
    T ⩭ T' ->
    C ⊩ T <⦂ T.
Proof.
  introv Hiso. apply ent_trivial. apply* ent_sub_refl.
Qed.

Lemma ent_sub_trans' : forall C s t u,
    C ⊩ s <⦂ t ->
    C ⊩ t <⦂ u ->
    C ⊩ s <⦂ u.
Proof.
  introv Hst Htu. introe.
  apply Hst in H as Hsst; eauto.
  apply Htu in H as Hstu; eauto.
  inversions Hstu. inversions Hsst.
  lets Heqs: (map_ctyp_unique_typ H5 H10). subst. clear H10.
  eapply sat_sub. exact H6. exact H7. eauto.
Qed.

Lemma ent_sub_fld : forall C a t T u U,
    t ⩭ T ->
    u ⩭ U ->
    C ⊩ t <⦂ u ->
    C ⊩ ctyp_rcd (cdec_trm a t) <⦂ ctyp_rcd (cdec_trm a u).
Proof.
  introv Ht Hu Htu. introe. apply Htu in H; eauto. inversions H.
  lets Hmt: (map_iso_ctyp tm vm Ht).
  lets Heqm: (map_ctyp_unique_typ H5 Hmt). subst. clear H5.
  lets Hmu: (map_iso_ctyp tm vm Hu).
  lets Hequ: (map_ctyp_unique_typ H7 Hmu). subst. clear H7.
  eapply sat_sub; try apply map_ctyp_rcd; try apply map_cdec_trm; try eassumption.
  eauto.
Qed.

Lemma satisfy_weaken : forall tm vm G C x T,
    ok G ->
    (tm, vm, G) ⊧ C ->
    x # G ->
    (tm, vm, G & x ~ T) ⊧ C.
Proof.
  introv Hok Hsat HxG. gen x.
  dependent induction Hsat; introv HxG; eauto.
  - assert (Hok1: ok (G & x ~ T)) by eauto.
    eapply sat_typ; try eassumption. apply* weaken_ty_trm.
  - assert (Hok1: ok (G & x ~ T)) by eauto.
    eapply sat_sub; try eassumption. apply* weaken_subtyp.
Qed.

Lemma ent_sub_all : forall L C s1 t1 s2 t2 S1 T1 S2 T2,
    s1 ⩭ S1 ->
    s2 ⩭ S2 ->
    t1 ⩭ T1 ->
    t2 ⩭ T2 ->
    C ⊩ s2 <⦂ s1 ->
    (forall x t1' t2', x \notin L ->
      t1' ⩭ open_typ x T1 ->
      t2' ⩭ open_typ x T2 ->
      C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ s2 ⊩ t1' <⦂ t2') ->
    C ⊩ ctyp_all s1 t1 <⦂ ctyp_all s2 t2.
Proof.
  introv Hs1 Hs2 Ht1 Ht2 HS HT. introe.
  pose proof (map_iso_ctyp tm vm Hs1) as Hms1.
  pose proof (map_iso_ctyp tm vm Hs2) as Hms2.
  pose proof (map_iso_ctyp tm vm Ht1) as Hmt1.
  pose proof (map_iso_ctyp tm vm Ht2) as Hmt2.
  apply HS in H as HS1; try assumption. inversions HS1.
  lets Heqs1: (map_ctyp_unique_typ Hms1 H7). subst T'. clear H7.
  lets Heqs2: (map_ctyp_unique_typ Hms2 H5). subst S'. clear H5.
  eapply sat_sub; try apply map_ctyp_all; try eassumption.
  apply subtyp_all with (L:=L \u dom G). assumption.
  introv Hx.
  destruct (iso_ctyp_exists (open_typ x T1)) as [u1 Hu1].
  destruct (iso_ctyp_exists (open_typ x T2)) as [u2 Hu2].
  assert (HxL: x \notin L) by eauto. specialize (HT x u1 u2 HxL Hu1 Hu2).
  assert (Hsat: (tm, vm, G & x ~ S2) ⊧ C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ s2).
  { admit. }
  apply HT in Hsat; try assumption.
Admitted.


Lemma ent_ty_rec_intro : forall x T T1 T2,
    T1 ⩭ open_typ x T ->
    T2 ⩭ typ_bnd T ->
    ctrm_cvar (cvar_x (avar_f x)) ⦂ T1 ⊩ ctrm_cvar (cvar_x (avar_f x)) ⦂ T2.
Proof.
  introv Hiso1 Hiso2. introe.
  inv_sat. inversion H5; subst. inversion H4; subst; clear H4.
  pose proof (map_iso_ctyp tm vm Hiso1) as Hi.
  pose proof (map_ctyp_unique_typ H7 Hi) as Heq1. subst.
  eapply sat_typ. exact H5. apply* map_iso_ctyp. eauto.
Qed.

Lemma ent_ty_rec_elim : forall x T T1 T2,
    T1 ⩭ typ_bnd T ->
    T2 ⩭ open_typ x T ->
    ctrm_cvar (cvar_x (avar_f x)) ⦂ T1 ⊩ ctrm_cvar (cvar_x (avar_f x)) ⦂ T2.
Proof.
  introv Hiso1 Hiso2. introe.
  inv_sat.
  inversion H5; subst. inversion H4; subst; clear H4.
  pose proof (map_iso_ctyp tm vm Hiso1) as Hi.
  pose proof (map_ctyp_unique_typ H7 Hi) as Heq1. subst.
  eapply sat_typ. exact H5. apply* map_iso_ctyp.
  eauto.
Qed.

Lemma ent_ty_and_intro : forall x t u and T U,
    t ⩭ T ->
    u ⩭ U ->
    and ⩭ typ_and T U ->
    ctrm_cvar (cvar_x (avar_f x)) ⦂ t ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ u
      ⊩ ctrm_cvar (cvar_x (avar_f x)) ⦂ and.
Proof.
  introv Hit Hiu Hi. introe.
  inv_sat. inv_sat_all.
  inversion H5; subst. inversion H4; subst; clear H4.
  inversion H6; subst. inversion H4; subst; clear H4. clear H5.
  pose proof (map_iso_ctyp tm vm Hit) as Ht.
  pose proof (map_iso_ctyp tm vm Hiu) as Hu.
  pose proof (map_ctyp_unique_typ H8 Hu) as Heq. subst.
  pose proof (map_ctyp_unique_typ H10 Ht) as Heq. subst.
  eapply sat_typ. exact H6. apply* map_iso_ctyp.
  eauto.
Qed.
