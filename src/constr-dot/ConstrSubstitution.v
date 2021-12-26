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
    ok G ->
    S' ⩭ S ->
    (C1, G) ⊢c trm_var (avar_f x) : S ->
    (C1 ⋏ C2 ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S', G) ⊢c T <: U ->
    (C1 ⋏ C2, G) ⊢c T <: U.
Proof.
  introv Hok Hiso HS HTU. gen T U S' C2.
  dependent induction HS; introv Hiso; introv HTU; eauto 2.
  - specialize (IHHS _ _ Hok _ JMeq_refl eq_refl).
    destruct (iso_ctyp_exists (open_typ x T)) as [s Hs].
    specialize (IHHS T0 U _ Hs). apply IHHS.
    eapply strengthen_constr_general_subtyping; try apply HTU.
    apply ent_cong_and_right. apply* ent_ty_rec_intro.
  - specialize (IHHS _ _ Hok _ JMeq_refl eq_refl).
    destruct (iso_ctyp_exists (typ_bnd T)) as [s Hs].
    specialize (IHHS T0 U _ Hs). apply IHHS.
    eapply strengthen_constr_general_subtyping; try apply HTU.
    apply ent_cong_and_right. apply* ent_ty_rec_elim.
  - specialize (IHHS1 _ _ Hok _ JMeq_refl eq_refl).
    specialize (IHHS2 _ _ Hok _ JMeq_refl eq_refl).
    destruct (iso_ctyp_exists T) as [t Ht].
    destruct (iso_ctyp_exists U) as [u Hu].
    specialize (IHHS1 T0 U0 _ Ht).
    specialize (IHHS2 T0 U0 _ Hu).
    apply IHHS1.
    eapply strengthen_constr_general_subtyping. apply ent_and_assoc.
    apply IHHS2.
    eapply strengthen_constr_general_subtyping; try apply HTU.
    introe. inv_sat. inversion H3; subst. inversion H8; subst.
    clear H3 H8. apply sat_and. constructor*.
    eapply ent_ty_and_intro. apply Ht. apply Hu. apply Hiso. assumption.
    constructor*.
  - specialize (IHHS _ _ Hok _ JMeq_refl eq_refl).
    destruct (iso_ctyp_exists T) as [t Ht].
    specialize (IHHS T0 U0 _ Ht). apply IHHS.
    (** --TODO: non-trivial case is here! *)
    (* eapply strengthen_constr_general_subtyping; try apply HTU. *)
    destruct (min_complete_exists G) as [rG Hr].
    Check subtyp_imply_ent.
    lets Hsub: (subtyp_imply_ent Hr Ht Hiso H).
    destruct (iso_ctyp_exists T0) as [t0 Ht0].
    destruct (iso_ctyp_exists U0) as [u0 Hu0].
    apply* ent_imply_subtyp.
    lets Hsub2: (subtyp_imply_ent Hr Ht0 Hu0 HTU).
    Check ent_and_intro.
    eapply ent_trans.
      eapply ent_and_intro.
    assert (He1: ((C1 ⋏ C2) ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ t) ⋏ rG ⊩ t <⦂ S'). {
      intros tm vm G0 HG Hsat. inversions Hsat.
      inversions H2. inversions H3. apply Hsub; auto.
    }
    exact He1.
    eapply ent_trans; try exact Hsub2.
    intros tm vm G0 Hi Hsat.
    inversions Hsat. inversions H2. inversions H3.
    apply* sat_and. apply* sat_and.
    eapply ent_ty_var_sub. exact Ht. exact Hiso. assumption.
    apply* sat_and.
Qed.

(** This lemma is a trivial corollary of the [[general_subtyping_weaken_constr]] theorem. *)
Lemma general_csubtyp_weaken_constr : forall C G x S S' T U,
    ok G ->
    S' ⩭ S ->
    (C, G) ⊢c trm_var (avar_f x) : S ->
    (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S', G) ⊢c T <: U ->
    (C, G) ⊢c T <: U.
Proof.
  introv Hok Hiso HS HTU.
  apply strengthen_constr_general_subtyping with (C2:=C ⋏ ⊤).
  apply ent_and_true_intro2.
  eapply general_subtyping_weaken_constr; try eassumption.
  apply* strengthen_constr_general_subtyping.
  apply ent_cong_and. apply ent_and_left.
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
    -- lets Hiso': (subst_iso_ctyp x y H).
       (** --TODO: Prove lemma: S ⩭ T implies [y/x] S ⩭ [y/x] T. *)
       lets B1: (binds_push_eq x S G1).
       lets B2: (binds_concat_left_ok Hok B1).
       lets Heq: (binds_functional H0 B2). subst.
       eapply general_csubtyp_weaken_constr.
       unfold subst_ctx. apply* ok_concat_map.
       exact Hiso'.
       exact HS. exact IHHTU.
    -- assert (B : binds x0 (subst_typ x y S') (G1 & subst_ctx x y G2)). { eauto. }
       assert (Hiso' : subst_ctyp x y S0 ⩭ subst_typ x y S'). { admit. }
       eapply csubtyp_intro. exact Hiso'. exact B.
       exact IHHTU.
Admitted.
(*   - assert (Hs : subst_ctyp x y S0 ⩭ subst_typ x y S'). {admit.} *)
(*     assert (Ht : subst_ctyp x y T ⩭ subst_typ x y T'). {admit.} *)
(* Admitted. *)

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

(** The substitution lemma for term typing.
    This lemma corresponds to Lemma 3.19 in the paper. *)
Lemma subst_cty_trm: forall y S C G x t T,
    (C, G & x ~ S) ⊢c t : T ->
    ok (G & x ~ S) ->
    x \notin (fv_ctx_types G \u fv_constr C) ->
    (C, G) ⊢c trm_var (avar_f y) : subst_typ x y S ->
    (C, G) ⊢c subst_trm x y t : subst_typ x y T.
Proof.
  intros.
  lets Hrules: (constr_subst_rules y S). destruct Hrules as [Hrule _].
  apply Hrule with (C:=C) (G1:=G) (G2:=empty) (x:=x) in H;
  unfold subst_ctx in *; try rewrite map_empty in *; try rewrite concat_empty_r in *; auto.
  lets Heq: (subst_fresh_constr). specialize (Heq x y C).
  rewrite* Heq in H.
  lets Heq: (subst_fresh_constr). specialize (Heq x y C).
  rewrite* Heq.
Qed.

(** The substitution lemma for definition typing. *)
Lemma subst_cty_defs: forall y S C G x ds T,
    (C, G & x ~ S) /-c ds :: T ->
    ok (G & x ~ S) ->
    x \notin (fv_ctx_types G \u fv_constr C) ->
    (C, G) ⊢c trm_var (avar_f y) : subst_typ x y S ->
    (C, G) /-c subst_defs x y ds :: subst_typ x y T.
Proof.
  intros.
  lets Hrules: (constr_subst_rules y S). destruct Hrules as [_ [_ [Hrule _]]].
  apply Hrule with (C:=C) (G1:=G) (G2:=empty) (x:=x) in H;
    unfold subst_ctx in *; try rewrite map_empty in *;
    try rewrite concat_empty_r in *; auto.
  lets Heq: (subst_fresh_constr). specialize (Heq x y C).
  rewrite* Heq in H.
  lets Heq: (subst_fresh_constr). specialize (Heq x y C).
  rewrite* Heq.
Qed.

(** * Renaming  *)

(** Renaming the name of the opening variable for definition typing.  #<br>#

    [ok G]                   #<br>#
    [z] fresh                #<br>#
    [G, z: T^z ⊢ ds^z : T^z] #<br>#
    [G ⊢ x: T^x]             #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ ds^x : T^x]         *)
Lemma renaming_cdef: forall C G z T ds x,
    ok G ->
    z # G ->
    z \notin (fv_ctx_types G \u fv_defs ds \u fv_typ T \u fv_constr C) ->
    (C, G & z ~ open_typ z T) /-c open_defs z ds :: open_typ z T ->
    (C, G) ⊢c trm_var (avar_f x) : open_typ x T ->
    (C, G) /-c open_defs x ds :: open_typ x T.
Proof.
  introv Hok Hnz Hnz' Hz Hx. rewrite subst_intro_typ with (x:=z). rewrite subst_intro_defs with (x:=z).
  eapply subst_cty_defs; auto. eapply Hz. rewrite <- subst_intro_typ. all: auto.
Qed.

(** Renaming the name of the opening variable for term typing. #<br>#
    [ok G]                   #<br>#
    [z] fresh                #<br>#
    [G, z: U ⊢ t^z : T^z]    #<br>#
    [G ⊢ x: U]               #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ t^x : T^x]         *)
Lemma renaming_ctyp: forall C G z T U t x,
    ok G ->
    z # G ->
    z \notin (fv_ctx_types G \u fv_typ U \u fv_typ T \u fv_trm t \u fv_constr C) ->
    (C, G & z ~ U) ⊢c open_trm z t : open_typ z T ->
    (C, G) ⊢c trm_var (avar_f x) : U ->
    (C, G) ⊢c open_trm x t : open_typ x T.
Proof.
  introv Hok Hnz Hnz' Hz Hx. rewrite subst_intro_typ with (x:=z). rewrite subst_intro_trm with (x:=z).
  eapply subst_cty_trm; auto. eapply Hz. rewrite subst_fresh_typ. all: auto.
Qed.

(** Renaming the name of the opening variable for term typing. #<br>#
    [ok G]                   #<br>#
    [z] fresh                #<br>#
    [G, z: U ⊢ t^z : T^z]    #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ t^x : T^x]         *)
Lemma constr_renaming_fresh : forall L C G T u U x,
    ok G ->
    (forall x : var, x \notin L -> (C, G & x ~ T) ⊢c open_trm x u : U) ->
    (C, G) ⊢c trm_var (avar_f x) : T ->
    (C, G) ⊢c open_trm x u : U.
Proof.
  introv Hok Hu Hx. constr_pick_fresh y.
  rewrite subst_intro_trm with (x:=y); auto.
  rewrite <- subst_fresh_typ with (x:=y) (y:=x); auto.
  apply~ subst_cty_trm. rewrite~ subst_fresh_typ.
Qed.
