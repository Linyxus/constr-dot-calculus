(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import TLC.LibLN.
Require Import String.

Require Import Definitions RecordAndInertTypes Decompose ConstrLangAlt ConstrInterp.

(** * Constraint Entailment *)

(** ** Definition of entailment *)
Definition constr_entail (C1 C2 : constr) :=
  forall tm vm G,
    inert G ->
    ok G ->
    (tm, vm, G) ⊧ C1 -> (tm, vm, G) ⊧ C2.

Notation "C '⊩' D" := (constr_entail C D) (at level 50).

(** ** Tactics *)

Ltac introe := introv H0 Hok H.

Ltac inv_sat :=
  match goal with
  | H : _ ⊧ (_ _) |- _ => idtac H; inversion H; subst; clear H
  | H : _ ⊧ (_ _ _) |- _ => idtac H; inversion H; subst; clear H
  | H : _ ⊧ ⊥ |- _ => idtac H; inversion H; subst; clear H
  end.

Ltac inv_sat_all := repeat inv_sat.

Ltac simpl_open_ctyp :=
  unfold open_ctyp_typ, open_cdec_typ, open_ctyp_var, open_cdec_var; simpl.

Ltac simpl_open_constr :=
  unfold open_constr_typ, open_constr_var in *; simpl in *; try case_if.

(** ** Entailment Laws *)

(** ∀ C, ⊥ ⊩ C
    From false follows everything. *)
Theorem ent_absurd : forall C,
    ⊥ ⊩ C.
Proof.
  introe. inversion H.
Qed.

(** ∀ C, C ⊩ ⊤
    Obtaining True is trivial. *)
Theorem ent_tautology : forall C,
    C ⊩ ⊤.
Proof. introe. eauto. Qed.

(** ∀ C, C ⊩ C *)
Lemma ent_refl : forall C,
    C ⊩ C.
Proof.
  introe. auto.
Qed.

(** If C1 ⊩ C2 and C2 ⊩ C3, then C1 ⊩ C3. *)
Theorem ent_trans : forall C1 C2 C3,
    C1 ⊩ C2 ->
    C2 ⊩ C3 ->
    C1 ⊩ C3.
Proof.
  introv H12 H23.
  introe.
  eauto.
Qed.

Theorem ent_cong_and : forall C C' D,
    C ⊩ C' ->
    C ⋏ D ⊩ C' ⋏ D.
Proof.
  introv He. introe. inv_sat.
  eauto.
Qed.

Theorem ent_and_comm : forall C D,
    C ⋏ D ⊩ D ⋏ C.
Proof.
  introe. inv_sat. eauto.
Qed.

Theorem ent_and_left : forall C D,
    C ⋏ D ⊩ C.
Proof. introe. inversion H; subst. eauto. Qed.

Theorem ent_and_right : forall C D,
    C ⋏ D ⊩ D.
Proof. introe. inversion H; subst. eauto. Qed.

Theorem ent_and_intro : forall C D,
    C ⊩ D ->
    C ⊩ C ⋏ D.
Proof.
  introv Hcd. introe.
  constructor*.
Qed.

Lemma ent_and_assoc : forall C1 C2 C3,
    (C1 ⋏ C2) ⋏ C3 ⊩ C1 ⋏ (C2 ⋏ C3).
Proof.
  introe. inv_sat. inv_sat. eauto.
Qed.

Lemma ent_or_comm : forall C D,
    C ⋎ D ⊩ D ⋎ C.
Proof.
  introe. inv_sat; eauto.
Qed.

Lemma ent_or_assoc : forall C1 C2 C3,
    (C1 ⋎ C2) ⋎ C3 ⊩ C1 ⋎ (C2 ⋎ C3).
Proof.
  introe. inv_sat; try inv_sat. all: eauto.
Qed.

Lemma ent_or_true : forall C,
    ⊤ ⊩ C ⋎ ⊤.
Proof.
  introe. eauto.
Qed.

Lemma ent_or_false : forall C,
    C ⋎ ⊥ ⊩ C.
Proof.
  introe. inv_sat; eauto. inv_sat.
Qed.

Lemma ent_or_dist_and : forall C D1 D2,
    C ⋎ (D1 ⋏ D2) ⊩ (C ⋎ D1) ⋏ (C ⋎ D2).
Proof.
  introe. inv_sat; try inv_sat; eauto.
Qed.

Lemma ent_and_dist_or : forall C D1 D2,
    C ⋏ (D1 ⋎ D2) ⊩ (C ⋏ D1) ⋎ (C ⋏ D2).
Proof.
  introe. inv_sat; try inv_sat; eauto.
Qed.

(** If C ⊩ D, then ∃ x. C ⊩ ∃ x. D *)
Lemma ent_cong_exists_v : forall C D,
    (forall x L, x \notin L -> C ^^v x ⊩ D ^^v x) ->
    ∃v C ⊩ ∃v D.
Proof.
  introv Hent. introe. inv_sat.
  apply sat_exists_var with (u := u) (L := L).
  introv Hn. apply* Hent.
Qed.

Lemma open_ctyp_typ_unchanged : forall u T,
    ~ ctyp_ref_bound_tvar T 0 ->
    open_ctyp_typ u T = T
with open_cdec_typ_unchanged : forall u D,
    ~ cdec_ref_bound_tvar D 0 ->
    open_cdec_typ u D = D.
Proof.
  all: introv Hnr.
  - induction T; try reflexivity; simpl_open_ctyp.
    -- destruct t. reflexivity. simpl. case_if.
      + subst. contradiction Hnr. constructor.
      + reflexivity.
    -- f_equal. apply* open_cdec_typ_unchanged. introv Hf.
       apply Hnr. constructor*.
    -- f_equal; try apply IHT1; try apply IHT2; introv Hf; apply Hnr.
       + apply ctyp_and1_rbt. auto.
       + apply ctyp_and2_rbt. auto.
    -- f_equal. apply IHT. introv Hf. apply Hnr. constructor*.
    -- f_equal; try apply IHT1; try apply IHT2; introv Hf; apply Hnr.
       + apply* ctyp_all1_rbt.
       + apply* ctyp_all2_rbt.
  - induction D; unfold open_cdec_typ; simpl; f_equal.
    -- apply open_ctyp_typ_unchanged. introv Hf. apply Hnr. constructor*.
    -- apply open_ctyp_typ_unchanged. introv Hf. apply Hnr. apply* cdec_typ2_rbt.
    -- apply open_ctyp_typ_unchanged. introv Hf. apply Hnr. constructor*.
Qed.

Lemma ent_sub_trans : forall S T,
    ~ ctyp_ref_bound_tvar S 0 -> ~ ctyp_ref_bound_tvar T 0 ->
    ∃t (S <⦂ (ctyp_tvar (tvar_b 0)) ⋏ (ctyp_tvar (tvar_b 0)) <⦂ T) ⊩ S <⦂ T.
Proof.
  introv Hs Ht. introe. inv_sat. simpl_open_constr.
  pick_fresh_gen (L \u ftv_ctyp S \u ftv_ctyp T) x. assert (x \notin L) as Hx by auto.
  specialize (H2 x Hx).
  pose proof (open_ctyp_typ_unchanged x Hs) as Heqs.
  unfold open_ctyp_typ in Heqs. rewrite -> Heqs in *.
  pose proof (open_ctyp_typ_unchanged x Ht) as Heqt.
  unfold open_ctyp_typ in Heqt. rewrite -> Heqt in *.
  inv_sat. inv_sat. inv_sat.
  apply map_tvar_tail_eq in H5. apply map_tvar_tail_eq in H10.
  subst S' T'0. assert (G ⊢ S'0 <: T') as Hsub. eauto.
  apply sat_sub with (S' := S'0) (T' := T'); try apply* strengthen_map_ctyp. auto.
Qed.

Lemma ent_ty_var_sub : forall x S T s t,
    s ⩭ S ->
    t ⩭ T ->
    ctrm_cvar (cvar_x (avar_f x)) ⦂ s ⋏ s <⦂ t ⊩ ctrm_cvar (cvar_x (avar_f x)) ⦂ t.
Proof.
  introv Hs Ht. introe.
  inv_sat. inv_sat. inv_sat.
  inversion H6; subst. inversions H4.
  lets Hs1: (map_iso_ctyp tm vm Hs).
  lets Ht1: (map_iso_ctyp tm vm Ht).
  lets Heq1: (map_ctyp_unique_typ H5 Hs1).
  lets Heq2: (map_ctyp_unique_typ H10 Hs1). subst.
  lets Heq: (map_ctyp_unique_typ H8 Ht1). subst.
  apply* sat_typ.
Qed.
