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

Lemma ent_sub_refl' : forall C T T',
    T ⩭ T' ->
    C ⊩ T <⦂ T.
Proof.
  introv Hiso. apply ent_trivial. apply* ent_sub_refl.
Qed.

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
