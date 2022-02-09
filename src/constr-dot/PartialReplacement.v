(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import String.
Require Import Coq.Program.Equality.
Require Import Definitions ConstrLangAlt.


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
    prepl_cvar x y (cvar_f x) (cvar_f y)
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

Hint Constructors prepl_cvar prepl_ctyp prepl_cdec
     prepl_ctrm prepl_cval prepl_cdef prepl_cdefs
     prepl_constr.

Scheme prepl_ctyp_mut := Induction for prepl_ctyp Sort Prop
with   prepl_cdec_mut := Induction for prepl_cdec Sort Prop.
Combined Scheme prepl_ctyp_mutind from prepl_ctyp_mut, prepl_cdec_mut.

Scheme prepl_ctrm_mut  := Induction for prepl_ctrm  Sort Prop
with   prepl_cval_mut  := Induction for prepl_cval Sort Prop
with   prepl_cdef_mut  := Induction for prepl_cdef  Sort Prop
with   prepl_cdefs_mut := Induction for prepl_cdefs Sort Prop.
Combined Scheme prepl_ctrm_mutind from prepl_ctrm_mut, prepl_cval_mut, prepl_cdef_mut, prepl_cdefs_mut.

(** * Properties of partial replacement *)

Lemma open_ctyp_typ_prepl_rules :
  (forall y x T T', prepl_ctyp y x T T' ->
    forall k u, prepl_ctyp y x (open_rec_ctyp_typ k u T) (open_rec_ctyp_typ k u T')) /\
  (forall y x D D', prepl_cdec y x D D' ->
    forall k u, prepl_cdec y x (open_rec_cdec_typ k u D) (open_rec_cdec_typ k u D')).
Proof.
  apply prepl_ctyp_mutind; intros; simpl in *; eauto.
Qed.

Definition open_ctyp_typ_prepl := (proj21 open_ctyp_typ_prepl_rules).

Lemma open_ctrm_typ_prepl_rules :
  (forall y x t t', prepl_ctrm y x t t' ->
    forall k u, prepl_ctrm y x (open_rec_ctrm_typ k u t) (open_rec_ctrm_typ k u t')) /\
  (forall y x v v', prepl_cval y x v v' ->
    forall k u, prepl_cval y x (open_rec_cval_typ k u v) (open_rec_cval_typ k u v')) /\
  (forall y x d d', prepl_cdef y x d d' ->
    forall k u, prepl_cdef y x (open_rec_cdef_typ k u d) (open_rec_cdef_typ k u d')) /\
  (forall y x ds ds', prepl_cdefs y x ds ds' ->
    forall k u, prepl_cdefs y x (open_rec_cdefs_typ k u ds) (open_rec_cdefs_typ k u ds')).
Proof.
  apply prepl_ctrm_mutind; intros; simpl in *; eauto using open_ctyp_typ_prepl.
Qed.

Definition open_ctrm_typ_prepl := proj41 open_ctrm_typ_prepl_rules.

Lemma open_constr_typ_prepl :
  forall y x C C', prepl_constr y x C C' ->
    forall k u, prepl_constr y x (open_rec_constr_typ k u C) (open_rec_constr_typ k u C').
Proof.
  introv Hpr. introv.
  dependent induction Hpr; simpl in *; eauto using open_ctyp_typ_prepl, open_ctrm_typ_prepl.
Qed.

Lemma open_cvar_prepl : forall y x c c' k u,
    prepl_cvar y x c c' ->
    prepl_cvar y x (open_rec_cvar k u c) (open_rec_cvar k u c').
Proof.
  introv Hp. inversions Hp; eauto.
  simpl. eauto.
Qed.

Lemma open_ctyp_var_prepl_rules :
  (forall y x T T', prepl_ctyp y x T T' ->
    forall k u, prepl_ctyp y x (open_rec_ctyp_var k u T) (open_rec_ctyp_var k u T')) /\
  (forall y x D D', prepl_cdec y x D D' ->
    forall k u, prepl_cdec y x (open_rec_cdec_var k u D) (open_rec_cdec_var k u D')).
Proof.
  apply prepl_ctyp_mutind; intros; simpl in *; eauto using open_cvar_prepl.
Qed.

Definition open_ctyp_var_prepl := proj21 open_ctyp_var_prepl_rules.

Lemma open_ctrm_var_prepl_rules :
  (forall y x t t', prepl_ctrm y x t t' ->
    forall k u, prepl_ctrm y x (open_rec_ctrm_var k u t) (open_rec_ctrm_var k u t')) /\
  (forall y x v v', prepl_cval y x v v' ->
    forall k u, prepl_cval y x (open_rec_cval_var k u v) (open_rec_cval_var k u v')) /\
  (forall y x d d', prepl_cdef y x d d' ->
    forall k u, prepl_cdef y x (open_rec_cdef_var k u d) (open_rec_cdef_var k u d')) /\
  (forall y x ds ds', prepl_cdefs y x ds ds' ->
    forall k u, prepl_cdefs y x (open_rec_cdefs_var k u ds) (open_rec_cdefs_var k u ds')).
Proof.
  apply prepl_ctrm_mutind; intros; simpl in *; eauto using open_ctyp_var_prepl, open_cvar_prepl.
Qed.

Definition open_ctrm_var_prepl := proj41 open_ctrm_var_prepl_rules.

Lemma open_constr_var_prepl :
  forall y x C C', prepl_constr y x C C' ->
    forall k u, prepl_constr y x (open_rec_constr_var k u C) (open_rec_constr_var k u C').
Proof.
  introv Hpr. introv.
  dependent induction Hpr; simpl in *; eauto using open_ctyp_var_prepl, open_ctrm_var_prepl.
Qed.
