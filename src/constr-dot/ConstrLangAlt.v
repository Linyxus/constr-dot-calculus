(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import Definitions RecordAndInertTypes Decompose.

(** * Abstract Syntax for Constraint Language *)

(** ** Type and Term with constraint-bound variables *)

(** *** Variables
    Variables can either be free or bound.  *)
Inductive cvar : Set :=
  | cvar_f : var -> cvar
  | cvar_b : nat -> cvar
  | cvar_x : avar -> cvar.

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

(** ** Reference to Bound Variables *)

Inductive ctyp_ref_bound_tvar : ctyp -> nat -> Prop :=
  | ctyp_tvar_rbt : forall n, ctyp_ref_bound_tvar (ctyp_tvar (tvar_b n)) n
  | ctyp_rcd_rbt : forall n D,
      cdec_ref_bound_tvar D n ->
      ctyp_ref_bound_tvar (ctyp_rcd D) n
  | ctyp_and1_rbt : forall n S T,
      ctyp_ref_bound_tvar S n ->
      ctyp_ref_bound_tvar (ctyp_and S T) n
  | ctyp_and2_rbt : forall n S T,
      ctyp_ref_bound_tvar T n ->
      ctyp_ref_bound_tvar (ctyp_and S T) n
  | ctyp_bnd_rbt : forall n T,
      ctyp_ref_bound_tvar T n ->
      ctyp_ref_bound_tvar (ctyp_bnd T) n
  | ctyp_all1_rbt : forall n S T,
      ctyp_ref_bound_tvar S n ->
      ctyp_ref_bound_tvar (ctyp_all S T) n
  | ctyp_all2_rbt : forall n S T,
      ctyp_ref_bound_tvar T n ->
      ctyp_ref_bound_tvar (ctyp_all S T) n
with cdec_ref_bound_tvar : cdec -> nat -> Prop :=
  | cdec_typ1_rbt : forall n A S T,
      ctyp_ref_bound_tvar S n ->
      cdec_ref_bound_tvar (cdec_typ A S T) n
  | cdec_typ2_rbt : forall n A S T,
      ctyp_ref_bound_tvar T n ->
      cdec_ref_bound_tvar (cdec_typ A S T) n
  | cdec_trm_rbt : forall n a T,
      ctyp_ref_bound_tvar T n ->
      cdec_ref_bound_tvar (cdec_trm a T) n
.

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

(** ** Free variables *)

(** *** Functions for caculuating free type variables *)

(** Free type variables in a type variable. *)
Definition ftv_tvar (tv : tvar) : fset var :=
  match tv with
  | tvar_b _ => \{}
  | tvar_f x => \{x}
  end.

Fixpoint ftv_ctyp (T : ctyp) : fset var :=
  match T with
  | ctyp_top => \{}
  | ctyp_bot => \{}
  | ctyp_tvar tv => ftv_tvar tv
  | ctyp_rcd D => ftv_cdec D
  | ctyp_and T U => ftv_ctyp T \u ftv_ctyp U
  | ctyp_sel x T => \{}
  | ctyp_bnd T => ftv_ctyp T
  | ctyp_all T U => ftv_ctyp T \u ftv_ctyp U
  end
with ftv_cdec (D : cdec) : fset var :=
  match D with
  | cdec_typ A T U => ftv_ctyp T \u ftv_ctyp U
  | cdec_trm a T => ftv_ctyp T
  end.

(** ** Isomorphism between concrete types *)

Reserved Notation "S ⩭ T" (at level 29).

Inductive iso_ctyp_typ : ctyp -> typ -> Prop :=
| iso_ctyp_top : ctyp_top ⩭ typ_top
| iso_ctyp_bot : ctyp_bot ⩭ typ_bot
| iso_ctyp_rcd : forall D D',
    iso_cdec_dec D D' ->
    ctyp_rcd D ⩭ typ_rcd D'
| iso_ctyp_and : forall T U T' U',
    T ⩭ T' ->
    U ⩭ U' ->
    ctyp_and T U ⩭ typ_and T' U'
| iso_ctyp_sel : forall x A,
    ctyp_sel (cvar_x x) A ⩭ typ_sel x A
| iso_ctyp_bnd : forall T T',
    T ⩭ T' ->
    ctyp_bnd T ⩭ typ_bnd T'
| iso_ctyp_all : forall S T S' T',
    S ⩭ S' ->
    T ⩭ T' ->
    ctyp_all S T ⩭ typ_all S' T'
where "S ⩭ T" := (iso_ctyp_typ S T)
with iso_cdec_dec : cdec -> dec -> Prop :=
| iso_cdec_typ : forall A S T S' T',
    S ⩭ S' ->
    T ⩭ T' ->
    iso_cdec_dec (cdec_typ A S T) (dec_typ A S' T')
| iso_cdec_trm : forall a T T',
    T ⩭ T' ->
    iso_cdec_dec (cdec_trm a T) (dec_trm a T')
.

Hint Constructors iso_ctyp_typ iso_cdec_dec.

Theorem iso_ctyp_exists : forall T', exists T, T ⩭ T'
with iso_cdec_exists : forall D', exists D, iso_cdec_dec D D'.
Proof.
  all: introv.
  - dependent induction T'.
    -- exists ctyp_top. eauto.
    -- exists ctyp_bot. eauto.
    -- destruct (iso_cdec_exists d) as [ d' Hd ].
       exists (ctyp_rcd d'). eauto.
    -- destruct IHT'1 as [t1 H1].
       destruct IHT'2 as [t2 H2].
       exists (ctyp_and t1 t2). eauto.
    -- exists (ctyp_sel (cvar_x a) t). eauto.
    -- destruct IHT' as [t' H]. exists (ctyp_bnd t'). eauto.
    -- destruct IHT'1 as [t1 H1].
       destruct IHT'2 as [t2 H2].
       exists (ctyp_all t1 t2). eauto.
  - dependent induction D'.
    -- destruct (iso_ctyp_exists t0) as [ T0 H0 ].
       destruct (iso_ctyp_exists t1) as [ T1 H1 ].
       exists (cdec_typ t T0 T1). eauto.
    -- destruct (iso_ctyp_exists t0) as [ T0 H0 ].
       exists (cdec_trm t T0). eauto.
Qed.

Lemma iso_ctyp_unique : forall T T1 T2,
    T1 ⩭ T ->
    T2 ⩭ T ->
    T1 = T2
with iso_cdec_unique : forall D D1 D2,
    iso_cdec_dec D1 D ->
    iso_cdec_dec D2 D ->
    D1 = D2.
Proof.
  all: introv Hiso1 Hiso2.
  - dependent induction T; inversion Hiso1; inversion Hiso2; trivial; subst.
    -- f_equal. apply* iso_cdec_unique.
    -- f_equal. apply* IHT1. apply* IHT2.
    -- f_equal. apply* IHT.
    -- f_equal. apply* IHT1. apply* IHT2.
  - dependent induction D; inversion Hiso1; inversion Hiso2; subst; f_equal; apply* iso_ctyp_unique.
Qed.

Definition fv_cvar (x: cvar) : vars :=
  match x with
  | cvar_f x => \{}
  | cvar_b i => \{}
  | cvar_x x => fv_avar x
  end.

Fixpoint fv_ctyp (T: ctyp) : vars :=
  match T with
  | ctyp_top        => \{}
  | ctyp_bot        => \{}
  | ctyp_tvar tv    => \{}
  | ctyp_rcd D      => (fv_cdec D)
  | ctyp_and T U    => (fv_ctyp T) \u (fv_ctyp U)
  | ctyp_sel x L    => (fv_cvar x)
  | ctyp_bnd T      => (fv_ctyp T)
  | ctyp_all T1 T2  => (fv_ctyp T1) \u (fv_ctyp T2)
  end
with fv_cdec (D: cdec) : vars :=
  match D with
  | cdec_typ L T U => (fv_ctyp T) \u (fv_ctyp U)
  | cdec_trm m T   => (fv_ctyp T)
  end.

(** Free variables in a term, value, or definition. *)
Fixpoint fv_ctrm (t: ctrm) : vars :=
  match t with
  | ctrm_cvar a       => (fv_cvar a)
  | ctrm_val v        => (fv_cval v)
  | ctrm_sel x m      => (fv_cvar x)
  | ctrm_app f a      => (fv_cvar f) \u (fv_cvar a)
  | ctrm_let t1 t2    => (fv_ctrm t1) \u (fv_ctrm t2)
  end
with fv_cval (v: cval) : vars :=
  match v with
  | cval_new T ds    => (fv_ctyp T) \u (fv_cdefs ds)
  | cval_lambda T e  => (fv_ctyp T) \u (fv_ctrm e)
  end
with fv_cdef (d: cdef) : vars :=
  match d with
  | cdef_typ _ T     => (fv_ctyp T)
  | cdef_trm _ t     => (fv_ctrm t)
  end
with fv_cdefs(ds: cdefs) : vars :=
  match ds with
  | cdefs_nil         => \{}
  | cdefs_cons tl d   => (fv_cdefs tl) \u (fv_cdef d)
  end.

Fixpoint fv_constr (C: constr) : vars :=
  match C with
  | ⊤ => \{}
  | ⊥ => \{}
  | C1 ⋏ C2 => fv_constr C1 \u fv_constr C2
  | C1 ⋎ C2 => fv_constr C1 \u fv_constr C2
  | ∃t C => fv_constr C
  | ∃v C => fv_constr C
  | t ⦂ T => fv_ctrm t \u fv_ctyp T
  | T <⦂ U => fv_ctyp T \u fv_ctyp U
  end.

Ltac constr_gather_vars :=
  let A := gather_vars_with (fun x : vars      => x          ) in
  let B := gather_vars_with (fun x : var       => \{ x }     ) in
  let C := gather_vars_with (fun x : ctx       => (dom x) \u (fv_ctx_types x)) in
  let D := gather_vars_with (fun x : sta       => dom x \u fv_sta_vals x) in
  let E := gather_vars_with (fun x : avar      => fv_avar   x) in
  let F := gather_vars_with (fun x : trm       => fv_trm    x) in
  let G := gather_vars_with (fun x : val       => fv_val    x) in
  let H := gather_vars_with (fun x : def       => fv_def    x) in
  let I := gather_vars_with (fun x : defs      => fv_defs   x) in
  let J := gather_vars_with (fun x : typ       => fv_typ    x) in
  let K := gather_vars_with (fun x : constr    => fv_constr x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J \u K).

Ltac constr_pick_fresh x :=
  let L := constr_gather_vars in (pick_fresh_gen L x).

