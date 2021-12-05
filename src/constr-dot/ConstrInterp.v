(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import TLC.LibLN.
Require Import String.

Require Import Definitions RecordAndInertTypes Decompose ConstrLangAlt.

(** * Constraint Interpretation *)

(** ** Ground assignments *)

Definition tctx := env typ.
Definition vctx := env var.

Reserved Notation "e '⊧' C" (at level 40).
Reserved Notation "es '⊢t' T1 '⪯' T2" (at level 40, T1 at level 59, T2 at level 59).
Reserved Notation "es '⊢d' d1 '⪯' d2" (at level 40, d1 at level 59, d2 at level 59).
Reserved Notation "es '⊢v' x '⪯' y" (at level 40, x at level 59, y at level 59).
Reserved Notation "es '⊢vv' x '⪯' y" (at level 40, x at level 59, y at level 59).
Reserved Notation "es '⊢vd' x '⪯' y" (at level 40, x at level 59, y at level 59).
Reserved Notation "es '⊢vds' x '⪯' y" (at level 40, x at level 59, y at level 59).

(** *** Mapping with ground assignments *)

(** Map a constraint variable to concrete variable. *)
Inductive map_cvar : vctx -> cvar -> var -> Prop :=
| map_cvar_f : forall vm x y,
    binds x y vm ->
    map_cvar vm (cvar_f x) y
| map_cvar_x : forall vm x,
    map_cvar vm (cvar_x x) x
.

(** Map a type containing type variables to a concrete type. *)
Inductive map_ctyp : (tctx * vctx) -> ctyp -> typ -> Prop :=

| map_ctyp_top : forall tm vm,
    (tm, vm) ⊢t ctyp_top ⪯ typ_top

| map_ctyp_bot : forall tm vm,
    (tm, vm) ⊢t ctyp_bot ⪯ typ_bot

| map_ctyp_tvar : forall tm vm x T,
    binds x T tm ->
    (tm, vm) ⊢t ctyp_tvar (tvar_f x) ⪯ T

| map_ctyp_rcd : forall tm vm D D',
    (tm, vm) ⊢d D ⪯ D' ->
    (tm, vm) ⊢t ctyp_rcd D ⪯ typ_rcd D'

| map_ctyp_and : forall tm vm T T' U U',
    (tm, vm) ⊢t T ⪯ T' ->
    (tm, vm) ⊢t U ⪯ U' ->
    (tm, vm) ⊢t ctyp_and T U ⪯ typ_and T' U'

| map_ctyp_sel : forall tm vm x y T,
    map_cvar vm x y ->
    (tm, vm) ⊢t ctyp_sel x T ⪯ typ_sel (avar_f y) T

| map_ctyp_bnd : forall tm vm T T',
    (tm, vm) ⊢t T ⪯ T' ->
    (tm, vm) ⊢t ctyp_bnd T ⪯ typ_bnd T'

| map_ctyp_all : forall tm vm T T' U U',
    (tm, vm) ⊢t T ⪯ T' ->
    (tm, vm) ⊢t U ⪯ U' ->
    (tm, vm) ⊢t ctyp_all T U ⪯ typ_all T' U'

where "es '⊢t' T1 '⪯' T2" := (map_ctyp es T1 T2)
with map_cdec : (tctx * vctx) -> cdec -> dec -> Prop :=
| map_cdec_typ : forall tm vm A S S' T T',
    (tm, vm) ⊢t S ⪯ S' ->
    (tm, vm) ⊢t T ⪯ T' ->
    (tm, vm) ⊢d cdec_typ A S T ⪯ dec_typ A S' T'
| map_cdec_trm : forall tm vm a T T',
    (tm, vm) ⊢t T ⪯ T' ->
    (tm, vm) ⊢d cdec_trm a T ⪯ dec_trm a T'
where "es '⊢d' D1 '⪯' D2" := (map_cdec es D1 D2).

Inductive map_ctrm : (tctx * vctx) -> ctrm -> trm -> Prop :=
| map_ctrm_cvar : forall tm vm x y,
    map_cvar vm x y ->
    (tm, vm) ⊢v ctrm_cvar x ⪯ trm_var (avar_f y)
| map_ctrm_val : forall tm vm v v',
    map_cval (tm, vm) v v' ->
    (tm, vm) ⊢v ctrm_val v ⪯ trm_val v'
where "es '⊢v' t1 '⪯' t2" := (map_ctrm es t1 t2)
with map_cval : (tctx * vctx) -> cval -> val -> Prop :=
| map_cval_new : forall tm vm T T' ds ds',
    (tm, vm) ⊢t T ⪯ T' ->
    (tm, vm) ⊢vds ds ⪯ ds' ->
    (tm, vm) ⊢vv cval_new T ds ⪯ val_new T' ds'
| map_cval_lambda : forall tm vm T T' t t',
    (tm, vm) ⊢t T ⪯ T' ->
    (tm, vm) ⊢v t ⪯ t' ->
    (tm, vm) ⊢vv cval_lambda T t ⪯ val_lambda T' t'
where "es '⊢vv' t1 '⪯' t2" := (map_cval es t1 t2)
with map_cdef : (tctx * vctx) -> cdef -> def -> Prop :=
| map_cdef_typ : forall tm vm A T T',
    (tm, vm) ⊢t T ⪯ T' ->
    (tm, vm) ⊢vd cdef_typ A T ⪯ def_typ A T'
| map_cdef_trm : forall tm vm a t t',
    (tm, vm) ⊢v t ⪯ t' ->
    (tm, vm) ⊢vd cdef_trm a t ⪯ def_trm a t'
where "es '⊢vd' t1 '⪯' t2" := (map_cdef es t1 t2)
with map_cdefs : (tctx * vctx) -> cdefs -> defs -> Prop :=
| map_cdefs_nil : forall tm vm,
    (tm, vm) ⊢vds cdefs_nil ⪯ defs_nil
| map_cdefs_cons : forall tm vm ds ds' d d',
    (tm, vm) ⊢vds ds ⪯ ds' ->
    (tm, vm) ⊢vd d ⪯ d' ->
    (tm, vm) ⊢vds cdefs_cons ds d ⪯ defs_cons ds' d'
where "es '⊢vds' t1 '⪯' t2" := (map_cdefs es t1 t2).

Scheme map_ctyp_mut    := Induction for map_ctyp Sort Prop
with   map_cdec_mut    := Induction for map_cdec Sort Prop.
Combined Scheme map_ctyp_mutind from map_ctyp_mut, map_cdec_mut.

Scheme map_ctrm_mut     := Induction for map_ctrm Sort Prop
with   map_cval_mut     := Induction for map_cval Sort Prop
with   map_cdef_mut     := Induction for map_cdef Sort Prop
with   map_cdefs_mut    := Induction for map_cdefs Sort Prop.
Combined Scheme map_ctrm_mutind from map_ctrm_mut, map_cval_mut, map_cdef_mut, map_cdefs_mut.

(** *** Properties of mapping *)

Lemma map_tvar_tail : forall tm vm x T,
    (tm & x ~ T, vm) ⊢t ctyp_tvar (tvar_f x) ⪯ T.
Proof.
  introv. constructor. apply binds_push_eq.
Qed.

Lemma map_tvar_tail_eq : forall tm vm x T T',
    (tm & x ~ T, vm) ⊢t ctyp_tvar (tvar_f x) ⪯ T' ->
    T = T'.
Proof.
  introv Hmx. inversion Hmx; subst.
  symmetry. eapply binds_push_eq_inv. eauto.
Qed.

Lemma strengthen_map_ctyp : forall tm vm x T S S',
    (tm & x ~ T, vm) ⊢t S ⪯ S' ->
    x \notin ftv_ctyp S ->
    (tm, vm) ⊢t S ⪯ S'
with strengthen_map_cdec : forall tm vm x T D D',
    (tm & x ~ T, vm) ⊢d D ⪯ D' ->
    x \notin ftv_cdec D ->
    (tm, vm) ⊢d D ⪯ D'.
Proof.
  all: introv Hmx Hn.
  - induction S;
      try (inversion Hmx; subst; constructor*);
      try (apply* strengthen_map_ctyp; simpl in Hn; auto).
    -- apply binds_concat_left_inv with (E2 := x ~ T); auto.
       unfold notin. introv Hin. rewrite dom_single in Hin.
       rewrite in_singleton in Hin. subst x0. simpl in Hn.
       apply Hn. rewrite -> in_singleton. trivial.
   - induction D; inversion Hmx; subst;
       simpl in Hn; constructor; apply* strengthen_map_ctyp.
Qed.

Inductive satisfy_constr : (tctx * vctx * ctx) -> constr -> Prop :=

| sat_true : forall tm vm G,
    (tm, vm, G) ⊧ ⊤

| sat_and : forall tm vm G C1 C2,
    (tm, vm, G) ⊧ C1 ->
    (tm, vm, G) ⊧ C2 ->
    (tm, vm, G) ⊧ C1 ⋏ C2

| sat_or1 : forall tm vm G C1 C2,
    (tm, vm, G) ⊧ C1 ->
    (tm, vm, G) ⊧ C1 ⋎ C2

| sat_or2 : forall tm vm G C1 C2,
    (tm, vm, G) ⊧ C2 ->
    (tm, vm, G) ⊧ C1 ⋎ C2

| sat_exists_typ : forall L tm vm G T C,
    (forall x, x \notin L -> (tm & x ~ T, vm, G) ⊧ C ^^t x) ->
    (tm, vm, G) ⊧ (∃t C)

| sat_exists_var : forall L tm vm G u C,
    (forall x, x \notin L -> (tm, vm & x ~ u, G) ⊧ C ^^v x) ->
    (tm, vm, G) ⊧ (∃v C)

| sat_typ : forall tm vm G t t' T T',
    (tm, vm) ⊢v t ⪯ t' ->
    (tm, vm) ⊢t T ⪯ T' ->
    G ⊢ t' : T' ->
    (tm, vm, G) ⊧ t ⦂ T

| sat_sub : forall tm vm G S S' T T',
    (tm, vm) ⊢t S ⪯ S' ->
    (tm, vm) ⊢t T ⪯ T' ->
    G ⊢ S' <: T' ->
    (tm, vm, G) ⊧ S <⦂ T

where "e '⊧' C" := (satisfy_constr e C).

Hint Constructors satisfy_constr constr.
