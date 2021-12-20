(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import String.
Require Import Coq.Program.Equality.
Require Import Definitions Binding Weakening Substitution.
Require Import RecordAndInertTypes.
Require Import ConstrLangAlt ConstrTyping ConstrNarrowing ConstrInterp.
Require Import ConstrBinding ConstrEntailment ConstrWeakening.
Require Import ConstrSubtypingLaws EntailmentLaws.
Require Import StrengtheningConstr.

Ltac constr_fresh_constructor :=
  match goal with
  | [ |- _ ⊢c trm_val (val_new _ _) : typ_bnd _ ] =>
    apply_fresh cty_new_intro as z
  | [ |- _ ⊢c trm_val (val_lambda _ _) : typ_all _ _ ] =>
    apply_fresh cty_all_intro as z
  | [ |- _ ⊢c trm_let _ _ : _ ] =>
    apply_fresh cty_let as z
  end; auto.

Ltac inversion_pair_eq :=
  match goal with
  | H : (_, _) = (_, _) |- _ => inversion H; subst
  end.

Ltac constr_subst_solver :=
    constr_fresh_constructor;
    subst_open_fresh;
    match goal with
    | [ H: forall z, z \notin ?L -> forall G, _
        |- context [ _ & subst_ctx ?x ?y ?G2 & ?z ~ subst_typ ?x ?y ?V] ] =>
        rewrite <- concat_assoc; rewrite subst_ctx_push;
        apply H; try rewrite <- subst_ctx_push; try rewrite concat_assoc;
        unfold subst_ctx; auto using weaken_cty_trm
    end.

Lemma general_subtyping_weaken_constr : forall C1 C2 G x S S' T U,
    S' ⩭ S ->
    (C1, G) ⊢c trm_var (avar_f x) : S ->
    (C1 ⋏ C2 ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S', G) ⊢c T <: U ->
    (C1 ⋏ C2, G) ⊢c T <: U.
Proof.
  introv Hiso HS HTU. gen T U S' C2.
  dependent induction HS; introv Hiso; introv HTU; eauto 2.
  - specialize (IHHS _ _ _ eq_refl eq_refl).
    destruct (iso_ctyp_exists (open_typ x T)) as [s Hs].
    specialize (IHHS T0 U _ Hs). apply IHHS.
    eapply strengthen_constr_general_subtyping; try apply HTU.
    admit.
  - specialize (IHHS _ _ _ eq_refl eq_refl).
    destruct (iso_ctyp_exists (typ_bnd T)) as [s Hs].
    specialize (IHHS T0 U _ Hs). apply IHHS.
    admit.
  - specialize (IHHS1 _ _ _ eq_refl eq_refl).
    specialize (IHHS2 _ _ _ eq_refl eq_refl).
    destruct (iso_ctyp_exists T) as [t Ht].
    destruct (iso_ctyp_exists U) as [u Hu].
    specialize (IHHS1 T0 U0 _ Ht).
    specialize (IHHS2 T0 U0 _ Hu).
    apply IHHS1.
    eapply strengthen_constr_general_subtyping. apply ent_and_assoc.
    apply IHHS2.
    admit.
  - specialize (IHHS _ _ _ eq_refl eq_refl).
    destruct (iso_ctyp_exists T) as [t Ht].
    specialize (IHHS T0 U0 _ Ht). apply IHHS.
    admit.
Admitted.

Lemma general_csubtyp_weaken_constr : forall C G x S S' T U,
    S' ⩭ S ->
    (C, G) ⊢c trm_var (avar_f x) : S ->
    (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S', G) ⊢c T <: U ->
    (C, G) ⊢c T <: U.
Proof.
Admitted.

Lemma subst_csubtyp_aux1 : forall C1 C2 G x S S' y T,
    S' ⩭ S ->
    (C1, G) ⊢c trm_var (avar_f x) : S ->
    (C1 ⋏ C2 ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S', G) ⊢c trm_var (avar_f y) : T ->
    (C1 ⋏ C2, G) ⊢c trm_var (avar_f y) : T.
Proof.
  introv Hiso HS HT.
  dependent induction HT; eauto 4.
  specialize (IHHT _ _ _ _ _ _ Hiso HS eq_refl eq_refl).
  eapply cty_sub. exact IHHT. eapply general_subtyping_weaken_constr.
  exact Hiso. exact HS. exact H.
Qed.

Lemma ent_subst_comm : forall x y C D,
    C ⊩ D ->
    subst_constr x y C ⊩ subst_constr x y D.
Proof.
  introv Hent. introe. gen D.
  dependent induction H; introv Hent.
  - admit.
  - admit.
Admitted.

Lemma subst_csubtyp : forall x y S C G1 G2 G T U,
    G = G1 & x ~ S & G2 ->
    (C, G) ⊢c T <: U ->
    ok G ->
    x \notin fv_ctx_types G1 ->
    (subst_constr x y C, G1 & (subst_ctx x y G2)) ⊢c trm_var (avar_f y) : subst_typ x y S ->
    (subst_constr x y C, G1 & (subst_ctx x y G2)) ⊢c subst_typ x y T <: subst_typ x y U.
Proof.
  introv Heq HTU Hok Hx HS. subst.
  dependent induction HTU.
  - specialize (IHHTU G2 G1 (C ⋏ ctrm_cvar (cvar_x (avar_f x0)) ⦂ S0) S x).
    specialize (IHHTU Hok JMeq_refl Hx).
    assert (H1 : (subst_constr x y (C ⋏ ctrm_cvar (cvar_x (avar_f x0)) ⦂ S0), G1 & subst_ctx x y G2) ⊢c trm_var (avar_f y) : subst_typ x y S). {
      simpl. cases_if.
      - eapply strengthen_constr_general_typing.
        apply ent_and_left. exact HS.
      - eapply strengthen_constr_general_typing.
        apply ent_and_left. exact HS.
    }
    specialize (IHHTU H1). simpl in IHHTU. cases_if.
    -- assert (Hiso' : subst_ctyp x y S0 ⩭ subst_typ x y S). { admit. }
       eapply general_csubtyp_weaken_constr. exact Hiso'.
       exact HS. exact IHHTU.
    -- assert (B : binds x0 (subst_typ x y S') (G1 & subst_ctx x y G2)). { admit. }
       assert (Hiso' : subst_ctyp x y S0 ⩭ subst_typ x y S'). { admit. }
       eapply csubtyp_intro. exact Hiso'. exact B.
       exact IHHTU.
  - assert (Hs : subst_ctyp x y S0 ⩭ subst_typ x y S'). {admit.}
    assert (Ht : subst_ctyp x y T ⩭ subst_typ x y T'). {admit.}
Admitted.

(** The proof is by mutual induction on term typing, definition typing, and subtyping. *)
Lemma constr_subst_rules: forall y S,
  (forall e t T, e ⊢c t : T -> forall C G1 G2 x,
    e = (C, G1 & x ~ S & G2) ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    (subst_constr x y C, G1 & (subst_ctx x y G2)) ⊢c trm_var (avar_f y) : subst_typ x y S ->
    (subst_constr x y C, G1 & (subst_ctx x y G2)) ⊢c subst_trm x y t : subst_typ x y T) /\
  (forall e d D, e /-c d : D -> forall C G1 G2 x,
    e = (C, G1 & x ~ S & G2) ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    (subst_constr x y C, G1 & (subst_ctx x y G2)) ⊢c trm_var (avar_f y) : subst_typ x y S ->
    (subst_constr x y C, G1 & (subst_ctx x y G2)) /-c subst_def x y d : subst_dec x y D) /\
  (forall e ds T, e /-c ds :: T -> forall C G1 G2 x,
    e = (C, G1 & x ~ S & G2) ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    (subst_constr x y C, G1 & (subst_ctx x y G2)) ⊢c trm_var (avar_f y) : subst_typ x y S ->
    (subst_constr x y C, G1 & (subst_ctx x y G2)) /-c subst_defs x y ds :: subst_typ x y T) /\
  (forall e T U, e ⊢c T <: U -> forall C G1 G2 x,
    e = (C, G1 & x ~ S & G2) ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    (subst_constr x y C, G1 & (subst_ctx x y G2)) ⊢c trm_var (avar_f y) : subst_typ x y S ->
    (subst_constr x y C, G1 & (subst_ctx x y G2)) ⊢c subst_typ x y T <: subst_typ x y T).
Proof.
  introv. apply crules_mutind; intros; try inversion_pair_eq; subst; simpl;
            try (constr_subst_solver || rewrite subst_open_commut_typ);
            simpl in *; eauto 4 using subst_csubtyp, csubtyp_refl.
  - Case "ty_var"%string.
    cases_if.
    + apply binds_middle_eq_inv in b; subst; assumption.
    + eapply subst_fresh_ctx in H1.
      apply binds_subst in b; auto.
      constructor. rewrite <- H1.
      unfold subst_ctx. rewrite <- map_concat.
      apply binds_map; auto.
  - Case "ty_rec_intro"%string.
    apply cty_rec_intro. fold_subst.
    rewrite subst_open_commut_typ. auto. eauto.
  - Case "ty_defs_cons"%string.
    constructor*. rewrite <- subst_label_of_def. apply* subst_defs_hasnt.
Qed.
