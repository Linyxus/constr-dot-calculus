(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Definitions RecordAndInertTypes Decompose.

(** * Abstract Syntax for Constraint Language *)

(** ** Type and Term with constraint-bound variables *)

(** *** Variables
    Variables can either be free or bound.  *)
Inductive cvar : Set :=
  | cvar_f : var -> cvar
  | cvar_b : nat -> cvar
  | cvar_x : var -> cvar.

Inductive tvar : Set :=
  | tvar_f : var -> tvar
  | tvar_b : nat -> tvar.

(** *** Type with type variables
    All constructors are the same as those in [typ], except for one additional
    constructor for type variables.
    [ctyp_tvar] represents the reference to a type variable bound by
    the constraint (∃t), represented by de Bruijn indices.  *)
Inductive ctyp : Set :=
  | ctyp_top  : ctyp
  | ctyp_bot  : ctyp
  | ctyp_tvar : tvar -> ctyp
  | ctyp_rcd  : cdec -> ctyp
  | ctyp_and  : ctyp -> ctyp -> ctyp
  | ctyp_sel  : cvar -> typ_label -> ctyp
  | ctyp_bnd  : ctyp -> ctyp
  | ctyp_all  : ctyp -> ctyp -> ctyp
with cdec : Set :=
  | cdec_typ  : typ_label -> ctyp -> ctyp -> cdec
  | cdec_trm  : trm_label -> ctyp -> cdec.

(** *** Terms with variables bound by constraints. *)
Inductive ctrm : Set :=
  | ctrm_cvar  : cvar -> ctrm
  | ctrm_val  : cval -> ctrm
  | ctrm_sel  : cvar -> trm_label -> ctrm
  | ctrm_app  : cvar -> cvar -> ctrm
  | ctrm_let  : ctrm -> ctrm -> ctrm
with cval : Set :=
  | cval_new  : ctyp -> cdefs -> cval
  | cval_lambda : ctyp -> ctrm -> cval
with cdef : Set :=
  | cdef_typ  : typ_label -> ctyp -> cdef
  | cdef_trm  : trm_label -> ctrm -> cdef
with cdefs : Set :=
  | cdefs_nil : cdefs
  | cdefs_cons : cdefs -> cdef -> cdefs.

Scheme ctyp_mut := Induction for ctyp Sort Prop
with   cdec_mut := Induction for cdec Sort Prop.
Combined Scheme ctyp_mutind from ctyp_mut, cdec_mut.

Scheme ctrm_mut  := Induction for ctrm  Sort Prop
with   cval_mut  := Induction for cval Sort Prop
with   cdef_mut  := Induction for cdef  Sort Prop
with   cdefs_mut := Induction for cdefs Sort Prop.
Combined Scheme ctrm_mutind from ctrm_mut, cval_mut, cdef_mut, cdefs_mut.

(** ** Constraint Language *)
Inductive constr : Set :=
(** ⊤ *)
| constr_true : constr
(** ⊥ *)
| constr_false : constr
(** C ⋏ D *)
| constr_and : constr -> constr -> constr
(** C ⋎ D *)
| constr_or : constr -> constr -> constr
(** ∃X. C *)
| constr_exists_typ : constr -> constr
(** ∃x. C *)
| constr_exists_var : constr -> constr
(** S <: T *)
| constr_sub : ctyp -> ctyp -> constr
(** t : T *)
| constr_typ : ctrm -> ctyp -> constr
.

(** - true constraint *)
Notation "⊤" := constr_true.
(** - false constraint *)
Notation "⊥" := constr_false.
(** - and constraint *)
Notation "C '⋏' D" := (constr_and C D) (at level 30).
(** - or constraint *)
Notation "C '⋎' D" := (constr_or C D) (at level 30).
(** - type existence constraint *)
Notation "'∃t' C" := (constr_exists_typ C) (at level 30).
(** - variable existence constraint *)
Notation "'∃v' C" := (constr_exists_var C) (at level 30).
(** - typing constraint *)
Notation "x '⦂' T" := (constr_typ x T) (at level 29).
(** - subtyping constraint *)
Notation "S '<⦂' T" := (constr_sub S T) (at level 29).

(** Syntax sugars *)
(** - type equality constraint *)
Notation "S '=⦂=' T" := (S <⦂ T ⋏ T <⦂ S) (at level 29).

(** ** Opening *)

Definition open_rec_tvar (k : nat) (u : var) (tv : tvar) : tvar :=
  match tv with
  | tvar_b i => If k = i then tvar_f u else tvar_b i
  | tvar_f x => tvar_f x
  end.

Fixpoint open_rec_ctyp_typ (k : nat) (u : var) (T : ctyp) : ctyp :=
  match T with
  | ctyp_top => ctyp_top
  | ctyp_bot => ctyp_bot
  | ctyp_tvar tv => ctyp_tvar (open_rec_tvar k u tv)
  | ctyp_rcd D => ctyp_rcd (open_rec_cdec_typ k u D)
  | ctyp_and T U => ctyp_and (open_rec_ctyp_typ k u T) (open_rec_ctyp_typ k u U)
  | ctyp_sel x T => ctyp_sel x T
  | ctyp_bnd T => ctyp_bnd (open_rec_ctyp_typ k u T)
  | ctyp_all T U => ctyp_all (open_rec_ctyp_typ k u T) (open_rec_ctyp_typ k u U)
  end
with open_rec_cdec_typ (k : nat) (u : var) (D : cdec) : cdec :=
  match D with
  | cdec_typ A T U => cdec_typ A (open_rec_ctyp_typ k u T) (open_rec_ctyp_typ k u U)
  | cdec_trm a T => cdec_trm a (open_rec_ctyp_typ k u T)
  end.

Definition open_rec_cvar (k : nat) (u : var) (v : cvar) : cvar :=
  match v with
  | cvar_f x => cvar_f x
  | cvar_x x => cvar_x x
  | cvar_b i => If k = i then cvar_f u else cvar_b i
  end.

Fixpoint open_rec_ctyp_var (k : nat) (u : var) (T : ctyp) : ctyp :=
  match T with
  | ctyp_top => ctyp_top
  | ctyp_bot => ctyp_bot
  | ctyp_tvar i => ctyp_tvar i
  | ctyp_rcd D => ctyp_rcd (open_rec_cdec_var k u D)
  | ctyp_and T U => ctyp_and (open_rec_ctyp_var k u T) (open_rec_ctyp_var k u U)
  | ctyp_sel x T => ctyp_sel (open_rec_cvar k u x) T
  | ctyp_bnd T => ctyp_bnd (open_rec_ctyp_var k u T)
  | ctyp_all T U => ctyp_all (open_rec_ctyp_var k u T) (open_rec_ctyp_var k u U)
  end
with open_rec_cdec_var (k : nat) (u : var) (D : cdec) : cdec :=
  match D with
  | cdec_typ A T U => cdec_typ A (open_rec_ctyp_var k u T) (open_rec_ctyp_var k u U)
  | cdec_trm a T => cdec_trm a (open_rec_ctyp_var k u T)
  end.

Fixpoint open_rec_ctrm_typ (k : nat) (u : var) (t : ctrm) : ctrm :=
  match t with
  | ctrm_cvar x => ctrm_cvar x
  | ctrm_val v => ctrm_val (open_rec_cval_typ k u v)
  | ctrm_sel x T => ctrm_sel x T
  | ctrm_app x y => ctrm_app x y
  | ctrm_let t1 t2 => ctrm_let (open_rec_ctrm_typ k u t1) (open_rec_ctrm_typ k u t2)
  end
with open_rec_cval_typ (k : nat) (u : var) (v : cval) : cval :=
  match v with
  | cval_new T ds => cval_new (open_rec_ctyp_typ k u T) (open_rec_cdefs_typ k u ds)
  | cval_lambda T t => cval_lambda (open_rec_ctyp_typ k u T) (open_rec_ctrm_typ k u t)
  end
with open_rec_cdef_typ (k : nat) (u : var) (d : cdef) : cdef :=
  match d with
  | cdef_typ A T => cdef_typ A (open_rec_ctyp_typ k u T)
  | cdef_trm a t => cdef_trm a (open_rec_ctrm_typ k u t)
  end
with open_rec_cdefs_typ (k : nat) (u : var) (ds : cdefs) : cdefs :=
  match ds with
  | cdefs_nil => cdefs_nil
  | cdefs_cons ds d => cdefs_cons (open_rec_cdefs_typ k u ds) (open_rec_cdef_typ k u d)
  end.

Fixpoint open_rec_ctrm_var (k : nat) (u : var) (t : ctrm) : ctrm :=
  match t with
  | ctrm_cvar x => ctrm_cvar (open_rec_cvar k u x)
  | ctrm_val v => ctrm_val (open_rec_cval_var k u v)
  | ctrm_sel x T => ctrm_sel (open_rec_cvar k u x) T
  | ctrm_app x y => ctrm_app (open_rec_cvar k u x) (open_rec_cvar k u y)
  | ctrm_let t1 t2 => ctrm_let (open_rec_ctrm_var k u t1) (open_rec_ctrm_var k u t2)
  end
with open_rec_cval_var (k : nat) (u : var) (v : cval) : cval :=
  match v with
  | cval_new T ds => cval_new (open_rec_ctyp_var k u T) (open_rec_cdefs_var k u ds)
  | cval_lambda T t => cval_lambda (open_rec_ctyp_var k u T) (open_rec_ctrm_var k u t)
  end
with open_rec_cdef_var (k : nat) (u : var) (d : cdef) : cdef :=
  match d with
  | cdef_typ A T => cdef_typ A (open_rec_ctyp_var k u T)
  | cdef_trm a t => cdef_trm a (open_rec_ctrm_var k u t)
  end
with open_rec_cdefs_var (k : nat) (u : var) (ds : cdefs) : cdefs :=
  match ds with
  | cdefs_nil => cdefs_nil
  | cdefs_cons ds d => cdefs_cons (open_rec_cdefs_var k u ds) (open_rec_cdef_var k u d)
  end.

Fixpoint open_rec_constr_typ (k : nat) (u : var) (C : constr) : constr :=
  match C with
  | constr_true => constr_true
  | constr_false => constr_false
  | constr_and C1 C2 => constr_and (open_rec_constr_typ k u C1) (open_rec_constr_typ k u C2)
  | constr_or C1 C2 => constr_or (open_rec_constr_typ k u C1) (open_rec_constr_typ k u C2)
  | constr_exists_typ C => constr_exists_typ (open_rec_constr_typ (S k) u C)
  | constr_exists_var C => constr_exists_var (open_rec_constr_typ k u C)
  | constr_sub T1 T2 => constr_sub (open_rec_ctyp_typ k u T1) (open_rec_ctyp_typ k u T2)
  | constr_typ t T0 => constr_typ (open_rec_ctrm_typ k u t) (open_rec_ctyp_typ k u T0)
  end.

Fixpoint open_rec_constr_var (k : nat) (u : var) (C : constr) : constr :=
  match C with
  | constr_true => constr_true
  | constr_false => constr_false
  | constr_and C1 C2 => constr_and (open_rec_constr_var k u C1) (open_rec_constr_var k u C2)
  | constr_or C1 C2 => constr_or (open_rec_constr_var k u C1) (open_rec_constr_var k u C2)
  | constr_exists_typ C => constr_exists_typ (open_rec_constr_var k u C)
  | constr_exists_var C => constr_exists_var (open_rec_constr_var (S k) u C)
  | constr_sub T1 T2 => constr_sub (open_rec_ctyp_var k u T1) (open_rec_ctyp_var k u T2)
  | constr_typ t T0 => constr_typ (open_rec_ctrm_var k u t) (open_rec_ctyp_var k u T0)
  end.

Definition open_ctyp_typ (u : var) (T : ctyp) : ctyp := open_rec_ctyp_typ 0 u T.
Definition open_cdec_typ (u : var) (D : cdec) : cdec := open_rec_cdec_typ 0 u D.
Definition open_ctyp_var (u : var) (T : ctyp) : ctyp := open_rec_ctyp_var 0 u T.
Definition open_cdec_var (u : var) (D : cdec) : cdec := open_rec_cdec_var 0 u D.
Definition open_constr_typ (u : var) (C : constr) : constr := open_rec_constr_typ 0 u C.
Definition open_constr_var (u : var) (C : constr) : constr := open_rec_constr_var 0 u C.

Notation "C '^^t' u" := (open_constr_typ u C) (at level 30).
Notation "C '^^v' u" := (open_constr_var u C) (at level 30).

(** * Constraint Interpretation *)

(** ** Ground assignments *)

Definition tctx := env typ.
Definition vctx := env var.

Reserved Notation "e '⊧' C" (at level 40).
Reserved Notation "es '⊢t' T1 '::' T2" (at level 40, T1 at level 59, T2 at level 59).
Reserved Notation "es '⊢d' d1 '::' d2" (at level 40, d1 at level 59, d2 at level 59).
Reserved Notation "es '⊢v' x '::' y" (at level 40, x at level 59, y at level 59).

Inductive map_cvar_to : vctx -> cvar -> var -> Prop :=
| map_cvar_f : forall vm x y,
    binds x y vm ->
    map_cvar_to vm (cvar_f x) y
| map_cvar_x : forall vm x,
    map_cvar_to vm (cvar_x x) x
.

Inductive map_ctyp_to : (tctx * vctx) -> ctyp -> typ -> Prop :=

| map_top_to : forall tm vm,
    (tm, vm) ⊢t ctyp_top :: typ_top

| map_bot_to : forall tm vm,
    (tm, vm) ⊢t ctyp_bot :: typ_bot

| map_tvar_to : forall tm vm x T,
    binds x T tm ->
    (tm, vm) ⊢t ctyp_tvar (tvar_f x) :: T

| map_rcd_to : forall tm vm D D',
    (tm, vm) ⊢d D :: D' ->
    (tm, vm) ⊢t ctyp_rcd D :: typ_rcd D'

| map_and_to : forall tm vm T T' U U',
    (tm, vm) ⊢t T :: T' ->
    (tm, vm) ⊢t U :: U' ->
    (tm, vm) ⊢t ctyp_and T U :: typ_and T' U'

| map_sel_to : forall tm vm x y T,
    map_cvar_to vm x y ->
    (tm, vm) ⊢t ctyp_sel x T :: typ_sel (avar_f y) T

| map_bnd_to : forall tm vm T T',
    (tm, vm) ⊢t T :: T' ->
    (tm, vm) ⊢t ctyp_bnd T :: typ_bnd T'

| map_all_to : forall tm vm T T' U U',
    (tm, vm) ⊢t T :: T' ->
    (tm, vm) ⊢t U :: U' ->
    (tm, vm) ⊢t ctyp_all T U :: typ_all T' U'

where "es '⊢t' T1 '::' T2" := (map_ctyp_to es T1 T2)
with map_cdec_to : (tctx * vctx) -> cdec -> dec -> Prop :=
| map_cdec_typ_to : forall tm vm A S S' T T',
    (tm, vm) ⊢t S :: S' ->
    (tm, vm) ⊢t T :: T' ->
    (tm, vm) ⊢d cdec_typ A S T :: dec_typ A S' T'
| map_cdec_trm_to : forall tm vm a T T',
    (tm, vm) ⊢t T :: T' ->
    (tm, vm) ⊢d cdec_trm a T :: dec_trm a T'
where "es '⊢d' D1 '::' D2" := (map_cdec_to es D1 D2).

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
    (forall x, x \notin L -> (tm, vm & x ~ u, G) ⊧ C ^^v u) ->
    (tm, vm, G) ⊧ (∃v C)

(* | sat_typ : forall tm vm G t t' T T', *)
(*     ctrm_closed t t' -> *)
(*     ctyp_closed T T' -> *)
(*     G ⊢ t' : T' -> *)
(*     G ⊧ t ⦂ T *)

| sat_sub : forall tm vm G S S' T T',
    (tm, vm) ⊢t S :: S' ->
    (tm, vm) ⊢t T :: T' ->
    G ⊢ S' <: T' ->
    (tm, vm, G) ⊧ S <⦂ T

where "e '⊧' C" := (satisfy_constr e C).
