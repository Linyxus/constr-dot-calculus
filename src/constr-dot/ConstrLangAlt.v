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
  (** Variables bound by DOT language. *)
  | cvar_b_l : nat -> cvar
  (** Variables bound by constraint language. *)
  | cvar_b_c : nat -> cvar.

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
  | cvar_b_c i => If k = i then cvar_f u else cvar_b_c i
  | cvar_b_l i => cvar_b_l i
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

(** ** Local closure *)

Inductive ctype : ctyp -> Prop :=
  | ctype_top  : ctype ctyp_top
  | ctype_bot  : ctype ctyp_bot
  | ctype_tvar : forall x, ctype (ctyp_tvar (tvar_f x))
  | ctype_rcd  : forall D, cdecl D -> ctype (ctyp_rcd D)
  | ctype_and  : forall T U,
      ctype T ->
      ctype U ->
      ctype (ctyp_and T U)
  | ctype_sel  : forall x T,
      ctype (ctyp_sel (cvar_f x) T)
  | ctype_bnd  : forall L T,
      (forall x, x \notin L -> ctype (open_ctyp_var x T)) ->
      ctype (ctyp_bnd T)
  | ctype_all  : forall L T U,
      ctype T ->
      (forall x, x \notin L -> ctype (open_ctyp_var x U)) ->
      ctype (ctyp_all T U)
with cdecl : cdec -> Prop :=
  | cdecl_typ : forall A T U,
      ctype T ->
      ctype U ->
      cdecl (cdec_typ A T U)
  | cdecl_trm : forall a T,
      ctype T ->
      cdecl (cdec_trm a T)
.

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

Inductive iso_cvar_avar : cvar -> avar -> Prop :=
  | iso_cvar_f : forall x,
      iso_cvar_avar (cvar_f x) (avar_f x)
  | iso_cvar_b_l : forall i,
      iso_cvar_avar (cvar_b_l i) (avar_b i).

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
| iso_ctyp_sel : forall x x' A,
    iso_cvar_avar x x' ->
    ctyp_sel x A ⩭ typ_sel x' A
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

Hint Constructors iso_cvar_avar iso_ctyp_typ iso_cdec_dec.

Theorem iso_cvar_exists : forall a, exists c, iso_cvar_avar c a.
Proof.
  destruct a.
  - exists (cvar_b_l n). eauto.
  - exists (cvar_f v). eauto.
Qed.

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
    -- destruct (iso_cvar_exists a).
       exists (ctyp_sel x t). eauto.
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

Lemma iso_cvar_unique : forall a c1 c2,
    iso_cvar_avar c1 a ->
    iso_cvar_avar c2 a ->
    c1 = c2.
Proof.
  introv H1 H2.
  inversion H1; inversion H2; subst; try inversion H4; eauto.
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
    -- lets Heq: (iso_cvar_unique H1 H5). subst. trivial.
    -- f_equal. apply* IHT.
    -- f_equal. apply* IHT1. apply* IHT2.
  - dependent induction D; inversion Hiso1; inversion Hiso2; subst; f_equal; apply* iso_ctyp_unique.
Qed.

Definition fv_cvar (x: cvar) : vars :=
  match x with
  | cvar_f x => \{x}
  | cvar_b_l i => \{}
  | cvar_b_c i => \{}
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

(** * Properties of opening *)

Lemma open_ctyp_typ_fv_rules :
  (forall T k u, fv_ctyp T = fv_ctyp (open_rec_ctyp_typ k u T)) /\
  (forall D k u, fv_cdec D = fv_cdec (open_rec_cdec_typ k u D)).
Proof.
  apply ctyp_mutind;
    intros; eauto;
    simpl; try solve [f_equal; eauto];
    eauto.
Qed.

Lemma open_ctyp_typ_fv : forall T k u,
    fv_ctyp T = fv_ctyp (open_rec_ctyp_typ k u T).
Proof.
  exact (proj21 open_ctyp_typ_fv_rules).
Qed.

Lemma open_ctrm_typ_fv_rules :
  (forall t k u, fv_ctrm t = fv_ctrm (open_rec_ctrm_typ k u t)) /\
  (forall v k u, fv_cval v = fv_cval (open_rec_cval_typ k u v)) /\
  (forall d k u, fv_cdef d = fv_cdef (open_rec_cdef_typ k u d)) /\
  (forall ds k u, fv_cdefs ds = fv_cdefs (open_rec_cdefs_typ k u ds)).
Proof.
  apply ctrm_mutind; intros; simpl in *; eauto;
    try solve [f_equal; eauto using open_ctyp_typ_fv].
  apply~ open_ctyp_typ_fv.
Qed.

Lemma open_ctrm_typ_fv : forall t k u,
    fv_ctrm t = fv_ctrm (open_rec_ctrm_typ k u t).
Proof.
  exact (proj41 open_ctrm_typ_fv_rules).
Qed.

Lemma open_constr_typ_fv : forall C k u,
    fv_constr C = fv_constr (open_rec_constr_typ k u C).
Proof.
  introv.
  dependent induction C; simpl in *; eauto;
    try solve [f_equal; eauto using open_ctyp_typ_fv, open_ctrm_typ_fv].
Qed.

Lemma open_cvar_fv : forall k u cv,
    fv_cvar cv = fv_cvar (open_rec_cvar k u cv) \/
    \{u} = fv_cvar (open_rec_cvar k u cv).
Proof.
  introv. unfold open_rec_cvar.
  destruct cv; simpl.
  - left. eauto.
  - left. eauto.
  - cases_if; eauto.
Qed.

Lemma open_ctyp_var_fv_rules :
  (forall T k u, fv_ctyp T = fv_ctyp (open_rec_ctyp_var k u T) \/
            fv_ctyp T \u \{u} = fv_ctyp (open_rec_ctyp_var k u T)) /\
  (forall D k u, fv_cdec D = fv_cdec (open_rec_cdec_var k u D) \/
            fv_cdec D \u \{u} = fv_cdec (open_rec_cdec_var k u D)).
Proof.
  apply ctyp_mutind;
    intros; eauto;
    simpl; try solve [f_equal; eauto using open_cvar_fv];
    eauto using open_cvar_fv.
  - specialize (H k u). specialize (H0 k u).
    destruct H; destruct H0; rewrite <- H0; rewrite <- H; eauto using union_assoc.
    + right. rewrite union_comm. rewrite union_comm_assoc. rewrite <- union_assoc. now trivial.
    + right. rewrite <- union_assoc. rewrite <- union_assoc.
      replace (\{u} \u fv_ctyp c0 \u \{u}) with (fv_ctyp c0 \u (\{u} \u \{u})).
      rewrite union_same. now trivial.
      rewrite union_comm_assoc. now trivial.
  - destruct c; unfold open_rec_cvar; try cases_if; eauto.
    simpl. right. rewrite union_empty_l. eauto.
  - specialize (H k u). specialize (H0 k u).
    destruct H; destruct H0; rewrite <- H; rewrite <- H0; eauto.
    + right. rewrite union_assoc. eauto.
    + right. rewrite <- union_assoc. rewrite (union_comm (fv_ctyp c0) \{u}).
      rewrite -> union_assoc. now trivial.
    + right. rewrite (union_comm (fv_ctyp c0) \{u}).
      rewrite union_assoc. rewrite <- (union_assoc _ \{u} \{u}).
      rewrite union_same. rewrite <- union_assoc. rewrite <- union_assoc.
      rewrite (union_comm \{u} _). now reflexivity.
  - specialize (H k u). specialize (H0 k u).
    destruct H; destruct H0; rewrite <- H; rewrite <- H0; eauto.
    + right. now rewrite <- union_assoc.
    + right. rewrite <- union_assoc. rewrite (union_comm (fv_ctyp c0) \{u}).
      now rewrite <- union_assoc.
    + right. rewrite (union_comm (fv_ctyp c0) \{u}).
      rewrite union_assoc. rewrite <- (union_assoc _ \{u} \{u}).
      rewrite union_same. rewrite <- union_assoc. rewrite <- union_assoc.
      now rewrite (union_comm \{u} _).
Qed.

Lemma open_ctrm_var_fv_rules :
  (forall t k u, fv_ctrm t = fv_ctrm (open_rec_ctrm_var k u t) \/
            fv_ctrm t \u \{u} = fv_ctrm (open_rec_ctrm_var k u t)) /\
  (forall v k u, fv_cval v = fv_cval (open_rec_cval_var k u v) \/
            fv_cval v \u \{u} = fv_cval (open_rec_cval_var k u v)) /\
  (forall d k u, fv_cdef d = fv_cdef (open_rec_cdef_var k u d) \/
            fv_cdef d \u \{u} = fv_cdef (open_rec_cdef_var k u d)) /\
  (forall ds k u, fv_cdefs ds = fv_cdefs (open_rec_cdefs_var k u ds) \/
             fv_cdefs ds \u \{u} = fv_cdefs (open_rec_cdefs_var k u ds)).
Proof.
  apply ctrm_mutind;
    intros; eauto;
    simpl; try solve [f_equal; eauto using open_cvar_fv];
    eauto using open_cvar_fv.
  - lets H: (open_cvar_fv k u c). destruct H; rewrite <- H; eauto.
    destruct c; simpl in *; eauto.
    right. now rewrite union_empty_l.
  - lets H: (open_cvar_fv k u c). destruct H; rewrite <- H; eauto.
    destruct c; simpl in *; eauto.
    right. now rewrite union_empty_l.
  - lets H: (open_cvar_fv k u c). destruct H; rewrite <- H; eauto.
    lets H0: (open_cvar_fv k u c0). destruct H0; rewrite <- H0; eauto.
    destruct c; destruct c0; simpl in *; eauto;
      try solve [left; now f_equal];
      try solve [right; now rewrite union_empty_r].
    + lets H0: (open_cvar_fv k u c0). destruct H0; rewrite <- H0; eauto.
      destruct c; destruct c0; simpl in *; eauto;
        try solve [left; now f_equal];
        try solve [right; now rewrite union_empty_r].
      right. rewrite union_empty_l. now rewrite union_comm.
      right. rewrite union_same. now rewrite union_comm.
      right. rewrite union_same. now rewrite union_comm.

      destruct c; destruct c0; simpl in *; eauto;
        try solve [left; now f_equal];
        try solve [right; now rewrite union_empty_r];
        try solve [left; rewrite union_same; now rewrite union_empty_r].
        try solve [left; rewrite union_same; now rewrite union_empty_l].
        right. repeat rewrite union_same. now rewrite union_empty_l.
  - specialize (H k u); specialize (H0 k u);
      destruct H; destruct H0;
      rewrite <- H; rewrite <- H0; eauto.
    + right. now rewrite union_assoc.
    + right. rewrite <- union_assoc. rewrite (union_comm (fv_ctrm c0) \{u}).
      now rewrite union_assoc.
    + right. rewrite (union_comm (fv_ctrm c0) \{u}). rewrite <- union_assoc.
      rewrite <- union_assoc. rewrite (union_assoc \{u} \{u} _).
      rewrite union_same. now rewrite (union_comm \{u} (fv_ctrm c0)).
  - specialize (H k u).
    lets H0: ((proj21 open_ctyp_var_fv_rules) c k u).
    destruct H; destruct H0;
      rewrite <- H; rewrite <- H0;
      simpl in *; eauto.
    + right. repeat rewrite <- union_assoc.
      now rewrite (union_comm _ \{u}).
    + right. repeat rewrite <- union_assoc.
      now rewrite (union_comm _ \{u}).
    + right. rewrite (union_comm (fv_cdefs c0) \{u}). rewrite <- union_assoc.
      rewrite <- union_assoc. rewrite (union_assoc \{u} \{u} _).
      rewrite union_same. now rewrite (union_comm \{u} (fv_cdefs c0)).
  - specialize (H k u).
    lets H0: ((proj21 open_ctyp_var_fv_rules) c k u).
    destruct H; destruct H0;
      rewrite <- H; rewrite <- H0;
      simpl in *; eauto.
    + right. repeat rewrite <- union_assoc.
      now rewrite (union_comm _ \{u}).
    + right. repeat rewrite <- union_assoc.
      now rewrite (union_comm _ \{u}).
    + right. rewrite (union_comm (fv_ctrm c0) \{u}). rewrite <- union_assoc.
      rewrite <- union_assoc. rewrite (union_assoc \{u} \{u} _).
      rewrite union_same. now rewrite (union_comm \{u} (fv_ctrm c0)).
  - lets H: ((proj21 open_ctyp_var_fv_rules) c k u).
    destruct H; rewrite <- H; simpl in *; eauto.
  - specialize (H k u). specialize (H0 k u).
    destruct H; destruct H0;
      rewrite <- H; rewrite <- H0;
      simpl in *; eauto.
    + right. repeat rewrite <- union_assoc.
      now rewrite (union_comm _ \{u}).
    + right. repeat rewrite <- union_assoc.
      now rewrite (union_comm _ \{u}).
    + right. rewrite (union_comm (fv_cdef c0) \{u}). rewrite <- union_assoc.
      rewrite <- union_assoc. rewrite (union_assoc \{u} \{u} _).
      rewrite union_same. now rewrite (union_comm \{u} (fv_cdef c0)).
Qed.

Definition open_ctyp_var_fv := proj21 open_ctyp_var_fv_rules.

Definition open_ctrm_var_fv := proj41 open_ctrm_var_fv_rules.

Lemma open_constr_var_fv : forall C k u,
    fv_constr C = fv_constr (open_rec_constr_var k u C) \/
    fv_constr C \u \{u} = fv_constr (open_rec_constr_var k u C).
Proof.
  introv.
  dependent induction C; simpl in *; eauto;
    try solve [f_equal; eauto using open_ctyp_var_fv, open_ctrm_var_fv];
    try specialize (IHC1 k u); try specialize (IHC2 k u);
    try destruct IHC1; try destruct IHC2; try rewrite <- H; try rewrite <- H0;
    eauto 10 using union_comm, union_assoc, union_comm_assoc;
    try solve [right; repeat rewrite <- union_assoc; now rewrite (union_comm \{u} _)].
  - right. rewrite (union_comm (fv_constr C2) \{u}). rewrite <- union_assoc.
    rewrite <- union_assoc. rewrite (union_assoc \{u} \{u} _).
    rewrite union_same. now rewrite (union_comm \{u} (fv_constr C2)).
  - right. rewrite (union_comm (fv_constr C2) \{u}). rewrite <- union_assoc.
    rewrite <- union_assoc. rewrite (union_assoc \{u} \{u} _).
    rewrite union_same. now rewrite (union_comm \{u} (fv_constr C2)).
  - lets H: (open_ctyp_var_fv c k u).
    lets H0: (open_ctyp_var_fv c0 k u).
    destruct H; destruct H0;
      rewrite <- H; rewrite <- H0;
      simpl in *; eauto.
    + right. repeat rewrite <- union_assoc.
      now rewrite (union_comm _ \{u}).
    + right. repeat rewrite <- union_assoc.
      now rewrite (union_comm _ \{u}).
    + right. rewrite (union_comm (fv_ctyp c0) \{u}). rewrite <- union_assoc.
      rewrite <- union_assoc. rewrite (union_assoc \{u} \{u} _).
      rewrite union_same. now rewrite (union_comm \{u} (fv_ctyp c0)).
  - lets H: (open_ctrm_var_fv c k u).
    lets H0: (open_ctyp_var_fv c0 k u).
    destruct H; destruct H0;
      rewrite <- H; rewrite <- H0;
      simpl in *; eauto.
    + right. repeat rewrite <- union_assoc.
      now rewrite (union_comm _ \{u}).
    + right. repeat rewrite <- union_assoc.
      now rewrite (union_comm _ \{u}).
    + right. rewrite (union_comm (fv_ctyp c0) \{u}). rewrite <- union_assoc.
      rewrite <- union_assoc. rewrite (union_assoc \{u} \{u} _).
      rewrite union_same. now rewrite (union_comm \{u} (fv_ctyp c0)).
Qed.
