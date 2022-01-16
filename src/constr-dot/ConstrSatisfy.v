(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import String.
Require Import Coq.Program.Equality.
Require Import Definitions Binding Weakening Substitution.
Require Import CanonicalForms PreciseTyping.
Require Import RecordAndInertTypes.
Require Import ConstrLangAlt ConstrTyping ConstrNarrowing ConstrInterp.
Require Import ConstrBinding ConstrEntailment ConstrWeakening.
Require Import ConstrSubtypingLaws EntailmentLaws.
Require Import StrengtheningConstr.

Inductive simple_formed_constr : constr -> Prop :=

| sf_true : simple_formed_constr ⊤

| sf_false : simple_formed_constr ⊥

| sf_and : forall C1 C2,
    simple_formed_constr C1 ->
    simple_formed_constr C2 ->
    simple_formed_constr (C1 ⋏ C2)

| sf_or : forall C1 C2,
    simple_formed_constr C1 ->
    simple_formed_constr C2 ->
    simple_formed_constr (C1 ⋎ C2)

| sf_sub : forall s t S T,
    s ⩭ S ->
    t ⩭ T ->
    simple_formed_constr (s <⦂ t)

| sf_typ : forall x t T,
    t ⩭ T ->
    simple_formed_constr (ctrm_cvar (cvar_x (avar_f x)) ⦂ t)
.

Inductive prepl_avar : var -> var -> avar -> avar -> Prop :=
| prepl_avar_unchanged : forall x y z,
    prepl_avar x y z z
| prepl_avar_replaced : forall x y,
    prepl_avar x y (avar_f x) (avar_f y)
.

Inductive prepl_typ : var -> var -> typ -> typ -> Prop :=
| prepl_typ_top : forall x y,
    prepl_typ x y typ_top typ_top

| prepl_typ_bot : forall x y,
    prepl_typ x y typ_bot typ_bot

| prepl_typ_rcd_typ : forall x y A T T' U U',
    prepl_typ x y T T' ->
    prepl_typ x y U U' ->
    prepl_typ x y (typ_rcd (dec_typ A T U)) (typ_rcd (dec_typ A T' U'))

| prepl_typ_rcd_trm : forall x y a T T',
    prepl_typ x y T T' ->
    prepl_typ x y (typ_rcd (dec_trm a T)) (typ_rcd (dec_trm a T'))

| prepl_typ_and : forall x y S S' T T',
    prepl_typ x y S S' ->
    prepl_typ x y T T' ->
    prepl_typ x y (typ_and S T) (typ_and S' T')

| prepl_typ_sel : forall x y z z' T,
    prepl_avar x y z z' ->
    prepl_typ x y (typ_sel z T) (typ_sel z' T)

| prepl_typ_bnd : forall x y T T',
    prepl_typ x y T T' ->
    prepl_typ x y (typ_bnd T) (typ_bnd T')

| prepl_typ_all : forall x y S S' T T',
    prepl_typ x y S S' ->
    prepl_typ x y T T' ->
    prepl_typ x y (typ_all S T) (typ_all S T)
.

Inductive prepl_cvar : var -> var -> cvar -> cvar -> Prop :=
| prepl_cvar_unchanged : forall x y z,
    prepl_cvar x y z z
| prepl_cvar_replaced : forall x y,
    prepl_cvar x y (cvar_x (avar_f x)) (cvar_x (avar_f y))
.

Inductive prepl_ctyp : var -> var -> ctyp -> ctyp -> Prop :=

| prepl_ctyp_top : forall x y,
    prepl_ctyp x y ctyp_top ctyp_top

| prepl_ctyp_bot : forall x y,
    prepl_ctyp x y ctyp_bot ctyp_bot

| prepl_ctyp_tvar : forall x y tv,
    prepl_ctyp x y (ctyp_tvar tv) (ctyp_tvar tv)

| prepl_ctyp_rcd: forall x y D D',
    prepl_cdec x y D D' ->
    prepl_ctyp x y (ctyp_rcd D) (ctyp_rcd D')

| prepl_ctyp_and: forall x y S S' T T',
    prepl_ctyp x y S S' ->
    prepl_ctyp x y T T' ->
    prepl_ctyp x y (ctyp_and S T) (ctyp_and S' T')

| prepl_ctyp_sel : forall x y z z' T,
    prepl_cvar x y z z' ->
    prepl_ctyp x y (ctyp_sel z T) (ctyp_sel z' T)

| prepl_ctyp_bnd : forall x y T T',
    prepl_ctyp x y T T' ->
    prepl_ctyp x y (ctyp_bnd T) (ctyp_bnd T')

with prepl_cdec : var -> var -> cdec -> cdec -> Prop :=

| prepl_cdec_typ : forall x y A T T' U U',
    prepl_ctyp x y T T' ->
    prepl_ctyp x y U U' ->
    prepl_cdec x y (cdec_typ A T U) (cdec_typ A T' U')

| prepl_cdec_trm : forall x y a T T',
    prepl_ctyp x y T T' ->
    prepl_cdec x y (cdec_trm a T) (cdec_trm a T')
.

Inductive prepl_ctrm : var -> var -> ctrm -> ctrm -> Prop :=

| prepl_ctrm_cvar : forall x y z z',
    prepl_cvar x y z z' ->
    prepl_ctrm x y (ctrm_cvar z) (ctrm_cvar z')

| prepl_ctrm_val : forall x y v v',
    prepl_cval x y v v' ->
    prepl_ctrm x y (ctrm_val v) (ctrm_val v')

| prepl_ctrm_sel : forall x y z z' a,
    prepl_cvar x y z z' ->
    prepl_ctrm x y (ctrm_sel z a) (ctrm_sel z' a)

| prepl_ctrm_app : forall x y t1 t1' t2 t2',
    prepl_cvar x y t1 t1' ->
    prepl_cvar x y t2 t2' ->
    prepl_ctrm x y (ctrm_app t1 t2) (ctrm_app t1' t2')

| prepl_ctrm_let : forall x y t1 t1' t2 t2',
    prepl_ctrm x y t1 t1' ->
    prepl_ctrm x y t2 t2' ->
    prepl_ctrm x y (ctrm_let t1 t2) (ctrm_let t1' t2')

with prepl_cval : var -> var -> cval -> cval -> Prop :=

| prepl_cval_new : forall x y T T' ds ds',
    prepl_ctyp x y T T' ->
    prepl_cdefs x y ds ds' ->
    prepl_cval x y (cval_new T ds) (cval_new T' ds')

| prepl_cval_lambda : forall x y T T' t t',
    prepl_ctyp x y T T' ->
    prepl_ctrm x y t t' ->
    prepl_cval x y (cval_lambda T t) (cval_lambda T' t')

with prepl_cdef : var -> var -> cdef -> cdef -> Prop :=

| prepl_cdef_typ : forall x y A T T',
    prepl_ctyp x y T T' ->
    prepl_cdef x y (cdef_typ A T) (cdef_typ A T')

| prepl_cdef_trm : forall x y a t t',
    prepl_ctrm x y t t' ->
    prepl_cdef x y (cdef_trm a t) (cdef_trm a t')

with prepl_cdefs : var -> var -> cdefs -> cdefs -> Prop :=

| prepl_cdefs_nil : forall x y,
    prepl_cdefs x y cdefs_nil cdefs_nil

| prepl_cdefs_cons : forall x y ds ds' d d',
    prepl_cdefs x y ds ds' ->
    prepl_cdef x y d d' ->
    prepl_cdefs x y (cdefs_cons ds d) (cdefs_cons ds' d')

.

Inductive prepl_constr : var -> var -> constr -> constr -> Prop :=
| prepl_true : forall x y,
    prepl_constr x y ⊤ ⊤

| prepl_false : forall x y,
    prepl_constr x y ⊥ ⊥

| prepl_and : forall x y C C' D D',
    prepl_constr x y C C' ->
    prepl_constr x y D D' ->
    prepl_constr x y (C ⋏ D) (C' ⋏ D')

| prepl_or : forall x y C C' D D',
    prepl_constr x y C C' ->
    prepl_constr x y D D' ->
    prepl_constr x y (C ⋎ D) (C' ⋎ D')

| prepl_exists_typ : forall x y C C',
    prepl_constr x y C C' ->
    prepl_constr x y (∃t C) (∃t C')

| prepl_exists_var : forall x y C C',
    prepl_constr x y C C' ->
    prepl_constr x y (∃v C) (∃v C')

| prepl_constr_sub : forall x y S S' T T',
    prepl_ctyp x y S S' ->
    prepl_ctyp x y T T' ->
    prepl_constr x y (S <⦂ T) (S' <⦂ T')

| prepl_constr_typ : forall x y t t' T T',
    prepl_ctrm x y t t' ->
    prepl_ctyp x y T T' ->
    prepl_constr x y (t ⦂ T) (t' ⦂ T')
.

Inductive well_formed_typ : ctx -> typ -> Prop :=

| well_formed_typ_top : forall G,
    well_formed_typ G typ_top

| well_formed_typ_bot : forall G,
    well_formed_typ G typ_bot

| well_formed_typ_rcd_typ : forall G A T U,
    well_formed_typ G T ->
    well_formed_typ G U ->
    well_formed_typ G (typ_rcd (dec_typ A T U))

| well_formed_typ_rcd_trm : forall G a T,
    well_formed_typ G T ->
    well_formed_typ G (typ_rcd (dec_trm a T))

| well_formed_typ_and : forall G T U,
    well_formed_typ G T ->
    well_formed_typ G U ->
    well_formed_typ G (typ_and T U)

| well_formed_typ_sel : forall G x A S T,
    G ⊢ trm_var (avar_f x) : typ_rcd (dec_typ A S T) ->
    well_formed_typ G (typ_sel (avar_f x) A)

| well_formed_typ_bnd : forall L G T,
    (forall x, x \notin L ->
          well_formed_typ (G & x ~ open_typ x T) (open_typ x T)) ->
    well_formed_typ G (typ_bnd T)

| well_formed_typ_all : forall L G T U,
    well_formed_typ G T ->
    (forall x, x \notin L ->
        well_formed_typ (G & x ~ T) (open_typ x U)) ->
    well_formed_typ G (typ_all T U)

.

Lemma simple_constr_empty_mapping : forall tm vm G C,
    simple_formed_constr C ->
    (tm, vm, G) ⊧ C ->
    (empty, empty, G) ⊧ C.
Proof.
  introv Hsf Hsat.
  dependent induction Hsf; eauto; inversions Hsat; eauto.
  - lets Heqs: (map_iso_ctyp tm vm H).
    lets Heqt: (map_iso_ctyp tm vm H0).
    lets Heqs1: (map_ctyp_unique_typ H5 Heqs).
    lets Heqt1: (map_ctyp_unique_typ H7 Heqt).
    subst. clear Heqs Heqt.
    lets Heqs: (map_iso_ctyp empty empty H).
    lets Heqt: (map_iso_ctyp empty empty H0).
    eauto.
  - lets Heqt: (map_iso_ctyp tm vm H).
    lets Heqt1: (map_ctyp_unique_typ H6 Heqt).
    clear Heqt.
    subst.
    lets Heqt: (map_iso_ctyp empty empty H).
    inversions H4. inversions H5.
    eapply sat_typ; try eassumption.
    constructor. constructor.
Qed.

Lemma subtyp_and_and : forall G T U T' U',
    G ⊢ T <: T' ->
    G ⊢ U <: U' ->
    G ⊢ typ_and T U <: typ_and T' U'.
Proof.
  introv HT HU. apply subtyp_and2.
  - eapply subtyp_trans. apply subtyp_and11. assumption.
  - eapply subtyp_trans. apply subtyp_and12. assumption.
Qed.

Lemma pf_record_has_dec : forall x G U T D,
    G ⊢! x: U ⪼ T ->
    record_has T D ->
    G ⊢! x: U ⪼ typ_rcd D.
Proof.
  introv HG Hr.
  dependent induction Hr.
  - assumption.
  - apply IHHr. eapply pf_and1. exact HG.
  - apply IHHr. eapply pf_and2. exact HG.
Qed.

Lemma binds_record_has_pf : forall x G S D,
    binds x (typ_bnd S) G ->
    record_has (open_typ x S) D ->
    G ⊢! x : (typ_bnd S) ⪼ typ_rcd D.
Proof.
  introv HB Hr.
  eapply pf_record_has_dec.
  eapply pf_open. eapply pf_bind. assumption. assumption.
Qed.

Lemma prepl_typ_subtyp_aux1 : forall x y G T T' U,
    inert G ->
    well_formed_typ G T ->
    x \notin fv_typ T ->
    prepl_typ y x T T' ->
    binds y U G ->
    ((G & x ~ U) ⊢ T' <: T /\ (G & x ~ U) ⊢ T <: T').
Proof.
  introv HG Hwf HxT Hpr HxG.
  dependent induction Hpr; eauto 2.
  - inversions Hwf. simpl in HxT. split; constructor.
    apply* IHHpr1. apply* IHHpr2. apply* IHHpr1. apply* IHHpr2.
  - inversions Hwf. simpl in HxT. split; constructor. apply* IHHpr. apply* IHHpr.
  - inversions Hwf. simpl in HxT. split; apply subtyp_and_and; try apply* IHHpr1; try apply* IHHpr2.
  - inversions Hwf. inversions H.
    -- eauto.
    -- lets Hinv: (var_typ_rcd_typ_to_binds HG H2).
       destruct Hinv as [S0 [T' [U' [Hx0 [Hrec [HST HUT]]]]]].
       lets Heq: (binds_functional HxG Hx0). subst. clear Hx0.
       lets HyG: (binds_push_eq y (typ_bnd S0) G).
       (* lets Hpf: (binds_record_has_pf HyG Hrec). *)
       admit.
Admitted.

Lemma prepl_constr_satisfy : forall x y T tm vm G C C',
    simple_formed_constr C ->
    well_formed_typ G T ->
    prepl_constr x y C C' ->
    (tm, vm, G) ⊧ C ->
    x \notin fv_constr C ->
    binds y T G ->
    (tm, vm, G & x ~ T) ⊧ C'.
Proof.
  introv Hsf Hwf Hpr HGC HxC HyT.
  dependent induction Hpr; eauto.
  - inversions HGC.
  - inversions Hsf. inversions HGC. simpl in HxC.
    constructor; eauto.
  - inversions Hsf. inversions HGC; simpl in HxC. constructor*.
    apply sat_or2. eauto.
  - inversions Hsf.
  - inversions Hsf.
  - inversions Hsf. inversions HGC.
Admitted.

Lemma subst_satisfy_aux1 : forall x y T G C,
    simple_formed_constr C ->
    binds x T G ->
    y # G ->
    (empty, empty, G) ⊧ C ->
    (empty, empty, G & y ~ T) ⊧ subst_constr x y C.
Proof.
  introv Hsf Hb HyG Hsat.
  dependent induction Hsf; eauto.
  - inversions Hsat.
  - inversions Hsat. simpl. eauto.
  - inversions Hsat; simpl; eauto.
  - admit.
  - inversions Hsat. inversions H4. inversions H5.
    simpl. cases_if.
Admitted.

