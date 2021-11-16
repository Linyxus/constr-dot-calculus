(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import TLC.LibLN.
Require Import String.

Require Import Definitions RecordAndInertTypes Decompose.

(** * Abstract Syntax for Constraint Language *)

(** ** Type and Term with constraint-bound variables *)

(** *** Variables
    The variables can either be bound by the core calculus (∀, let),
    or by the constraint (∃ X. C).  *)
Inductive cvar : Set :=
  | cvar_avar : avar -> cvar
  | cvar_cvar : nat -> cvar.

(** *** Type with type variables
    All constructors are the same as those in [typ], except for one additional
    constructor for type variables.
    [ctyp_tvar] represents the reference to a type variable bound by
    the constraint (∃t), represented by de Bruijn indices.  *)
Inductive ctyp : Set :=
  | ctyp_top  : ctyp
  | ctyp_bot  : ctyp
  | ctyp_tvar : nat -> ctyp
  | ctyp_typ : typ -> ctyp
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
  | ctrm_var  : cvar -> ctrm
  | ctrm_trm  : trm -> ctrm
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

(** Coercions *)
Coercion ctyp_typ : typ >-> ctyp.
Coercion ctrm_trm : trm >-> ctrm.

(** *** Closeness
    A type or term is closed, if it does not refer to variables bound
    by the existential qualifier of the constraint language.

    In other words, all type variables and term variables are substituted
    to concrete types and variables.  *)
Inductive ctyp_closed : ctyp -> typ -> Prop :=
| ctyp_top_closed : ctyp_closed ctyp_top typ_top
| ctyp_bot_closed : ctyp_closed ctyp_bot typ_bot
| ctyp_typ_closed : forall T,
    ctyp_closed (ctyp_typ T) T
| ctyp_rcd_closed : forall D D',
    cdec_closed D D' ->
    ctyp_closed (ctyp_rcd D) (typ_rcd D')
| ctyp_and_closed : forall T T' U U',
    ctyp_closed T T' ->
    ctyp_closed U U' ->
    ctyp_closed (ctyp_and T U) (typ_and T' U')
| ctyp_sel_closed : forall x T,
    ctyp_closed (ctyp_sel (cvar_avar x) T) (typ_sel x T)
| ctyp_bnd_closed : forall T T',
    ctyp_closed T T' -> ctyp_closed (ctyp_bnd T) (typ_bnd T')
| ctyp_all_closed : forall S S' T T',
    ctyp_closed S S' ->
    ctyp_closed T T' ->
    ctyp_closed (ctyp_all S T) (typ_all S' T')
with cdec_closed : cdec -> dec -> Prop :=
| cdec_typ_closed : forall A S S' T T',
    ctyp_closed S S' ->
    ctyp_closed T T' ->
    cdec_closed (cdec_typ A S T) (dec_typ A S' T')
| cdec_trm_closed : forall a T T',
    ctyp_closed T T' ->
    cdec_closed (cdec_trm a T) (dec_trm a T')
.

Scheme ctyp_closed_mut    := Induction for ctyp_closed Sort Prop
with   cdec_closed_mut    := Induction for cdec_closed Sort Prop.
Combined Scheme ctyp_closed_mutind from ctyp_closed_mut, cdec_closed_mut.

Inductive ctrm_closed : ctrm -> trm -> Prop :=
| ctrm_cvar_closed : forall x,
    ctrm_closed (ctrm_var (cvar_avar x)) (trm_var x)
| ctrm_trm_closed : forall t,
    ctrm_closed (ctrm_trm t) t
| ctrm_val_closed : forall v v',
    cval_closed v v' ->
    ctrm_closed (ctrm_val v) (trm_val v')
| ctrm_sel_closed : forall x T,
    ctrm_closed (ctrm_sel (cvar_avar x) T) (trm_sel x T)
| ctrm_app_closed : forall x y,
    ctrm_closed (ctrm_app (cvar_avar x) (cvar_avar y)) (trm_app x y)
| ctrm_let_closed : forall t t' u u',
    ctrm_closed t t' ->
    ctrm_closed u u' ->
    ctrm_closed (ctrm_let t u) (trm_let t' u')
with cval_closed : cval -> val -> Prop :=
| cval_new_closed : forall T T' ds ds',
    ctyp_closed T T' ->
    cdefs_closed ds ds' ->
    cval_closed (cval_new T ds) (val_new T' ds')
| cval_lambda_closed : forall T T' t t',
    ctyp_closed T T' ->
    ctrm_closed t t' ->
    cval_closed (cval_lambda T t) (val_lambda T' t')
with cdef_closed : cdef -> def -> Prop :=
| cdef_typ_closed : forall A T T',
    ctyp_closed T T' ->
    cdef_closed (cdef_typ A T) (def_typ A T')
| cdef_trm_closed : forall a t t',
    ctrm_closed t t' ->
    cdef_closed (cdef_trm a t) (def_trm a t')
with cdefs_closed : cdefs -> defs -> Prop :=
| cdefs_nil_closed : cdefs_closed cdefs_nil defs_nil
| cdefs_cons_closed : forall d d' ds ds',
    cdef_closed d d' ->
    cdefs_closed ds ds' ->
    cdefs_closed (cdefs_cons ds d) (defs_cons ds' d')
.

Lemma ctyp_closed_unique : forall T T1 T2,
    ctyp_closed T T1 ->
    ctyp_closed T T2 ->
    T1 = T2
with cdec_closed_unique : forall D D1 D2,
    cdec_closed D D1 ->
    cdec_closed D D2 ->
    D1 = D2.
Proof.
  all: introv Hc1 Hc2.
  - induction Hc1; inversion Hc2; subst; auto;
      try (f_equal; apply* cdec_closed_unique);
      try (f_equal; apply* ctyp_closed_unique).
  - induction Hc1; inversion Hc2; subst; auto;
      try (f_equal; apply* ctyp_closed_unique).
Qed.

Lemma ctrm_closed_unique : forall t t1 t2,
    ctrm_closed t t1 ->
    ctrm_closed t t2 ->
    t1 = t2
with cval_closed_unique : forall v v1 v2,
    cval_closed v v1 ->
    cval_closed v v2 ->
    v1 = v2
with cdef_closed_unique : forall d d1 d2,
    cdef_closed d d1 ->
    cdef_closed d d2 ->
    d1 = d2
with cdefs_closed_unique : forall ds ds1 ds2,
    cdefs_closed ds ds1 ->
    cdefs_closed ds ds2 ->
    ds1 = ds2.
Proof.
  all: introv Hc1 Hc2; induction Hc1;
    inversion Hc2; subst; auto;
    try (f_equal; eauto);
    try apply* ctyp_closed_unique.
Qed.

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

(** ** Opening *)

Fixpoint open_rec_ctyp_typ (k : nat) (t : typ) (T : ctyp) : ctyp :=
  match T with
  | ctyp_top => ctyp_top
  | ctyp_bot => ctyp_bot
  | ctyp_tvar i => If k = i then ctyp_typ t else ctyp_tvar i
  | ctyp_typ u => ctyp_typ u
  | ctyp_rcd D => ctyp_rcd (open_rec_cdec_typ k t D)
  | ctyp_and T U => ctyp_and (open_rec_ctyp_typ k t T) (open_rec_ctyp_typ k t U)
  | ctyp_sel x T => ctyp_sel x T
  | ctyp_bnd T => ctyp_bnd (open_rec_ctyp_typ k t T)
  | ctyp_all T U => ctyp_all (open_rec_ctyp_typ k t T) (open_rec_ctyp_typ k t U)
  end
with open_rec_cdec_typ (k : nat) (t : typ) (D : cdec) : cdec :=
  match D with
  | cdec_typ A T U => cdec_typ A (open_rec_ctyp_typ k t T) (open_rec_ctyp_typ k t U)
  | cdec_trm a T => cdec_trm a (open_rec_ctyp_typ k t T)
  end.

Definition open_rec_cvar (k : nat) (u : var) (v : cvar) : cvar :=
  match v with
  | cvar_avar x => cvar_avar x
  | cvar_cvar i => If k = i then cvar_avar (avar_f u) else cvar_cvar i
  end.

Fixpoint open_rec_ctyp_var (k : nat) (u : var) (T : ctyp) : ctyp :=
  match T with
  | ctyp_top => ctyp_top
  | ctyp_bot => ctyp_bot
  | ctyp_tvar i => ctyp_tvar i
  | ctyp_typ u => ctyp_typ u
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

Fixpoint open_rec_ctrm_typ (k : nat) (t : typ) (u : ctrm) : ctrm :=
  match u with
  | ctrm_var x => ctrm_var x
  | ctrm_trm t => ctrm_trm t
  | ctrm_val v => ctrm_val (open_rec_cval_typ k t v)
  | ctrm_sel x T => ctrm_sel x T
  | ctrm_app x y => ctrm_app x y
  | ctrm_let t1 t2 => ctrm_let (open_rec_ctrm_typ k t t1) (open_rec_ctrm_typ k t t2)
  end
with open_rec_cval_typ (k : nat) (t : typ) (v : cval) : cval :=
  match v with
  | cval_new T ds => cval_new (open_rec_ctyp_typ k t T) (open_rec_cdefs_typ k t ds)
  | cval_lambda T u => cval_lambda (open_rec_ctyp_typ k t T) (open_rec_ctrm_typ k t u)
  end
with open_rec_cdef_typ (k : nat) (t : typ) (d : cdef) : cdef :=
  match d with
  | cdef_typ A T => cdef_typ A (open_rec_ctyp_typ k t T)
  | cdef_trm a u => cdef_trm a (open_rec_ctrm_typ k t u)
  end
with open_rec_cdefs_typ (k : nat) (t : typ) (ds : cdefs) : cdefs :=
  match ds with
  | cdefs_nil => cdefs_nil
  | cdefs_cons ds d => cdefs_cons (open_rec_cdefs_typ k t ds) (open_rec_cdef_typ k t d)
  end.

Fixpoint open_rec_ctrm_var (k : nat) (u : var) (t : ctrm) : ctrm :=
  match t with
  | ctrm_var x => ctrm_var (open_rec_cvar k u x)
  | ctrm_trm t => ctrm_trm t
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

Fixpoint open_rec_constr_typ (k : nat) (T : typ) (C : constr) : constr :=
  match C with
  | constr_true => constr_true
  | constr_false => constr_false
  | constr_and C1 C2 => constr_and (open_rec_constr_typ k T C1) (open_rec_constr_typ k T C2)
  | constr_or C1 C2 => constr_or (open_rec_constr_typ k T C1) (open_rec_constr_typ k T C2)
  | constr_exists_typ C => constr_exists_typ (open_rec_constr_typ (S k) T C)
  | constr_exists_var C => constr_exists_var (open_rec_constr_typ k T C)
  | constr_sub T1 T2 => constr_sub (open_rec_ctyp_typ k T T1) (open_rec_ctyp_typ k T T2)
  | constr_typ t T0 => constr_typ (open_rec_ctrm_typ k T t) (open_rec_ctyp_typ k T T0)
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

Definition open_ctyp_typ (S : typ) (T : ctyp) : ctyp := open_rec_ctyp_typ 0 S T.
Definition open_cdec_typ (S : typ) (D : cdec) : cdec := open_rec_cdec_typ 0 S D.
Definition open_ctyp_var (u : var) (T : ctyp) : ctyp := open_rec_ctyp_var 0 u T.
Definition open_cdec_var (u : var) (D : cdec) : cdec := open_rec_cdec_var 0 u D.
Definition open_constr_typ (T : typ) (C : constr) : constr := open_rec_constr_typ 0 T C.
Definition open_constr_var (u : var) (C : constr) : constr := open_rec_constr_var 0 u C.

Notation "C '^^' T" := (open_constr_typ C T) (at level 30).
Notation "C '^^' u" := (open_constr_var C u) (at level 30).

(** ** Lemmas on openning and closed types *)

Ltac invsc H := inversion H; subst; clear H.
Ltac invs H := inversion H; subst.

Ltac open_closed_eq_aux :=
  match goal with
  | |- (?P ?L) = (?P ?R) =>
      assert (L = R) as ?H by eauto
  | |- (?P ?L1 ?L2) = (?P ?R1 ?R2) =>
      assert (L1 = R1) as ?H by eauto
  end.

Ltac simpl_open_ctyp :=
  unfold open_ctyp_typ, open_cdec_typ, open_ctyp_var, open_cdec_var; simpl.

Ltac solve_cong_eq :=
  solve [
    f_equal; eauto
  ].

Lemma open_closed_ctyp_typ_unchanged : forall S T T',
    ctyp_closed T T' ->
    open_ctyp_typ S T = T
with open_closed_cdec_typ_unchanged : forall S D D',
    cdec_closed D D' ->
    open_cdec_typ S D = D.
Proof.
  all: introv Hc; induction Hc; auto; simpl_open_ctyp; try solve_cong_eq.
Qed.

Lemma open_closed_ctyp_var_unchanged : forall S T T',
    ctyp_closed T T' ->
    open_ctyp_var S T = T
with open_closed_cdec_var_unchanged : forall S D D',
    cdec_closed D D' ->
    open_cdec_var S D = D.
Proof.
  all: introv Hc; induction Hc; auto; simpl_open_ctyp; try solve_cong_eq.
Qed.

Definition is_closed_ctyp (T : ctyp) := exists T', ctyp_closed T T'.

Lemma open_closed_ctyp_typ_unchanged' : forall S T,
    is_closed_ctyp T ->
    open_ctyp_typ S T = T.
Proof.
  introv [T' Hc]. apply* open_closed_ctyp_typ_unchanged.
Qed.

Lemma open_closed_ctyp_var_unchanged' : forall u T,
    is_closed_ctyp T ->
    open_ctyp_var u T = T.
Proof.
  introv [T' Hc]. apply* open_closed_ctyp_var_unchanged.
Qed.

(** * Constraint Interpretation *)

Reserved Notation "G '⊧' C" (at level 40).

Inductive satisfy_constr : ctx -> constr -> Prop :=

| sat_true : forall G,
    G ⊧ ⊤

| sat_and : forall G C1 C2,
    G ⊧ C1 ->
    G ⊧ C2 ->
    G ⊧ C1 ⋏ C2

| sat_or1 : forall G C1 C2,
    G ⊧ C1 ->
    G ⊧ C1 ⋎ C2

| sat_or2 : forall G C1 C2,
    G ⊧ C2 ->
    G ⊧ C1 ⋎ C2

| sat_exists_typ : forall G T C,
    G ⊧ open_constr_typ T C ->
    G ⊧ (∃t C)

| sat_exists_var : forall G u C,
    G ⊧ open_constr_var u C ->
    G ⊧ (∃v C)

| sat_typ : forall G t t' T T',
    ctrm_closed t t' ->
    ctyp_closed T T' ->
    G ⊢ t' : T' ->
    G ⊧ t ⦂ T

| sat_sub : forall G S S' T T',
    ctyp_closed S S' ->
    ctyp_closed T T' ->
    G ⊢ S' <: T' ->
    G ⊧ S <⦂ T

where "G '⊧' C" := (satisfy_constr G C).

Hint Constructors satisfy_constr constr.

(** * Constraint Entailment *)

(** ** Definition of entailment *)
Definition constr_entail (C1 C2 : constr) :=
  forall G,
    inert G ->
    satisfy_constr G C1 -> satisfy_constr G C2.

Notation "C '⊩' D" := (constr_entail C D) (at level 50).

(** ** Tactics *)

Ltac introe := introv H0 H.

Ltac inv_sat :=
  match goal with
  | H : _ ⊧ _ |- _ => idtac H; inversion H; subst; clear H
  end.

Ltac inv_sat_all := repeat inv_sat.

Ltac inv_closed :=
  match goal with
  | H : ctyp_closed (_ _) _ |- _ => idtac H; inversion H; subst; clear H
  | H : ctyp_closed (_ _ _) _ |- _ => idtac H; inversion H; subst; clear H
  | H : ctrm_closed (_ _) _ |- _ => idtac H; inversion H; subst; clear H
  | H : ctrm_closed (_ _ _) _ |- _ => idtac H; inversion H; subst; clear H
  end.

Ltac inv_closed_all := repeat inv_closed.

Ltac simpl_open_constr :=
  unfold open_constr_typ, open_constr_var in *; simpl in *; try case_if.

Ltac solve_open_closed_ctyp_eq T0 T :=
  match goal with
  | Hc : is_closed_ctyp T |- _ =>
      try replace (open_rec_ctyp_typ 0 T0 T) with T in * by
        (symmetry; apply* open_closed_ctyp_typ_unchanged');
      try replace (open_rec_ctyp_var 0 T0 T) with T in * by
        (symmetry; apply* open_closed_ctyp_var_unchanged')
  | Hc : ctyp_closed T _ |- _ =>
      idtac Hc;
      try replace (open_rec_ctyp_typ 0 T0 T) with T in * by
        (symmetry; apply* open_closed_ctyp_typ_unchanged);
      try replace (open_rec_ctyp_var 0 T0 T) with T in * by
        (symmetry; apply* open_closed_ctyp_var_unchanged)
  end.

Ltac solve_ctyp_closed_unique T1 T2 :=
  match goal with
  | |- _ => replace T1 with T2 in * by apply* ctyp_closed_unique
  end.

Ltac solve_ctrm_closed_unique t1 t2 :=
  match goal with
  | |- _ => replace t1 with t2 in * by apply* ctrm_closed_unique
  end.

Ltac solve_trivial_sub :=
  match goal with
  | H : ?G ⊢ ?S <: ?T |- ?G ⊧ (ctyp_typ ?S) <⦂ (ctyp_typ ?T) =>
    idtac G; idtac S; idtac T;
    apply sat_sub with (S' := S) (T' := T); try assumption; try apply ctyp_typ_closed
  end.

(** ** Entailment Laws *)

(** ∀ C, ⊥ ⊩ C
    From false follows everything. *)
Theorem ent_absurd : forall C,
    ⊥ ⊩ C.
Proof.
  introe. inversion H.
Qed.

(** ∀ C, C ⊩ ⊤ *)
Theorem ent_tautology : forall C,
    C ⊩ ⊤.
Proof. introe. eauto. Qed.

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
  introv He. introe. inversion H; subst.
  eauto.
Qed.

Theorem ent_and_left : forall C D,
    C ⋏ D ⊩ C.
Proof. introe. inversion H; subst. eauto. Qed.

Theorem ent_and_right : forall C D,
    C ⋏ D ⊩ D.
Proof. introe. inversion H; subst. eauto. Qed.

(** If U is fresh for S and T, then
    ∃ U. (S <: U ⋏ U <: T) ⊩ S <: T
 *)
Theorem ent_sub_trans : forall S T,
    is_closed_ctyp S -> is_closed_ctyp T ->
    ∃t (S <⦂ (ctyp_tvar 0) ⋏ (ctyp_tvar 0) <⦂ T) ⊩ S <⦂ T.
Proof.
  introv Hs Ht.
  introe. inv_sat.
  simpl_open_constr. inv_sat.
  solve_open_closed_ctyp_eq T0 T.
  solve_open_closed_ctyp_eq T0 S.
  inv_sat_all. apply sat_sub with (S' := S'0) (T' := T'); auto.
  solve_ctyp_closed_unique S' T'0.
  eauto.
Qed.

Theorem ent_and_true : forall C,
    C ⋏ ⊤ ⊩ C.
Proof.
  introv. introe.
  inversion_clear H; subst; auto.
Qed.

Theorem ent_and_false : forall C,
    C ⋎ ⊥ ⊩ C.
Proof.
  introe. inversion H; subst; try assumption.
  inversion H3.
Qed.

(** x: T ⊩ ∃y. y: T *)
Lemma ent_exists_v_i : forall x T,
    ctrm_var (cvar_avar (avar_f x)) ⦂ T ⊩ ∃v ctrm_var (cvar_cvar 0) ⦂ T.
Proof.
  introv. introe.
  inv_sat.
  inversion H3; subst.
  apply sat_exists_var with (u := x).
  simpl_open_constr. apply* sat_typ.
  solve_open_closed_ctyp_eq x T. auto.
Qed.

(** ∃x. (x: {A:S1..T1} ⋏ x: {A:S2..T2}) ⊩ S1 <: T2 ⋏ S2 <: T1 *)
Lemma ent_bound_sub : forall A S1 T1 S2 T2,
    ∃v (ctrm_var (cvar_cvar 0) ⦂ typ_rcd (dec_typ A S1 T1) ⋏
        ctrm_var (cvar_cvar 0) ⦂ typ_rcd (dec_typ A S2 T2)) ⊩
    S1 <⦂ T2 ⋏ S2 <⦂ T1.
Proof.
  introv. introe.
  inv_sat. simpl_open_constr.
  inv_sat_all.
  solve_ctrm_closed_unique t' t'0.
  inv_closed_all.
  assert (G ⊢ S1 <: T2 /\ G ⊢ S2 <: T1) as [Hs1 Hs2] by apply* typ_bounds_subtyping.
  apply* sat_and; solve_trivial_sub.
Qed.

(** x: S ⋏ S <: T ⊩ x: T *)
Lemma ent_typ_subsume : forall x S T,
    trm_var (avar_f x) ⦂ S ⋏ S <⦂ T ⊩ trm_var (avar_f x) ⦂ T.
Proof.
  introe. inv_sat_all. inversion H3; subst.
  apply* sat_typ.
  solve_ctyp_closed_unique S' T'0. eauto.
Qed.

(** U1 /\ U2 <: {A: S..T} ⊩ U1 <: {A: S..T} \/ U2 <: {A: S..T}
 *)
Theorem ent_sub_and_rcd_or : forall U1 U2 A S T,
    typ_and U1 U2 <⦂ typ_rcd (dec_typ A S T) ⊩
        U1 <⦂ typ_rcd (dec_typ A S T) ⋎ U2 <⦂ typ_rcd (dec_typ A S T).
Proof.
  introv. introe.
  inv_sat. inv_closed_all.
  match goal with
  | H : G ⊢ _ <: _ |- _ =>
    apply invert_subtyp_and1_rcd in H as [?H1 | ?H2]; try assumption;
      try (apply sat_or1; solve_trivial_sub);
      try (apply sat_or2; solve_trivial_sub)
  end.
Qed.

(** {A: S1..T1} <: {A: S2..T2} ⊩ S2 <: S1 ⋏ T1 <: T2 *)
Theorem ent_inv_subtyp_typ : forall A S1 T1 S2 T2,
    typ_rcd (dec_typ A S1 T1) <⦂ typ_rcd (dec_typ A S2 T2) ⊩
        S2 <⦂ S1 ⋏ T1 <⦂ T2.
Proof.
  introv. introe. inv_sat. inv_closed_all.
  match goal with
  | H : G ⊢ _ <: _ |- _ =>
    apply invert_subtyp_typ in H as [Hs1 Hs2]; try assumption
  end.
  constructor; solve_trivial_sub.
Qed.

(** If A ≠ B,
    then {A:S1..T1} <: {B:S2..T2} ⊩ ⊥  *)
Theorem ent_subtyp_typ_label_neq_false : forall A S1 T1 B S2 T2,
    A <> B ->
    typ_rcd (dec_typ A S1 T1) <⦂ typ_rcd (dec_typ B S2 T2) ⊩ ⊥.
Proof.
  introv Hne. introe. inv_sat. inv_closed_all.
  apply invert_subtyp_typ_label_neq_false in H6; try assumption.
  contradiction.
Qed.

(** S <: T ∧ U ⊩ S <: T ⋏ S <: U *)
Lemma ent_sub_and_and : forall S T U,
    S <⦂ typ_and T U ⊩ S <⦂ T ⋏ S <⦂ U.
Proof.
  introe. inv_sat. inv_closed.
  assert (G ⊢ S' <: T /\ G ⊢ S' <: U) as [Hs1 Hs2] by apply* invert_subtyp_and2.
  apply* sat_and; eapply sat_sub with (S' := S');
    try assumption;
    try apply ctyp_typ_closed;
    try assumption.
Qed.

