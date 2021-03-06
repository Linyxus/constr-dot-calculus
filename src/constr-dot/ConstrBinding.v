(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module defines various helper lemmas about opening, closing, and local closure. *)

Set Implicit Arguments.

Require Import TLC.LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions ConstrLangAlt ConstrTyping Binding.

(** * Substitution Definitions *)

Definition subst_cvar (z: var) (u: var) (c: cvar) : cvar :=
  match c with
  | cvar_x x => cvar_x (subst_avar z u x)
  | cvar_b i => cvar_b i
  | cvar_f x => cvar_f x
  end.

(** Substitution on types and declarations: [T[u/z]] and [D[u/z]]. *)
Fixpoint subst_ctyp (z: var) (u: var) (T: ctyp) { struct T } : ctyp :=
  match T with
  | ctyp_top        => ctyp_top
  | ctyp_bot        => ctyp_bot
  | ctyp_tvar tv    => ctyp_tvar tv
  | ctyp_rcd D      => ctyp_rcd (subst_cdec z u D)
  | ctyp_and T1 T2  => ctyp_and (subst_ctyp z u T1) (subst_ctyp z u T2)
  | ctyp_sel x L    => ctyp_sel (subst_cvar z u x) L
  | ctyp_bnd T      => ctyp_bnd (subst_ctyp z u T)
  | ctyp_all T U    => ctyp_all (subst_ctyp z u T) (subst_ctyp z u U)
  end
with subst_cdec (z: var) (u: var) (D: cdec) { struct D } : cdec :=
  match D with
  | cdec_typ L T U  => cdec_typ L (subst_ctyp z u T) (subst_ctyp z u U)
  | cdec_trm L U    => cdec_trm L (subst_ctyp z u U)
  end.

(** Substitution on terms, values, and definitions:
    [t[u/z]], [v[u/z]], [d[u/z]]. *)
Fixpoint subst_ctrm (z: var) (u: var) (t: ctrm) : ctrm :=
  match t with
  | ctrm_cvar x       => ctrm_cvar (subst_cvar z u x)
  | ctrm_val v        => ctrm_val (subst_cval z u v)
  | ctrm_sel x1 L     => ctrm_sel (subst_cvar z u x1) L
  | ctrm_app x1 x2    => ctrm_app (subst_cvar z u x1) (subst_cvar z u x2)
  | ctrm_let t1 t2    => ctrm_let (subst_ctrm z u t1) (subst_ctrm z u t2)
  end
with subst_cval (z: var) (u: var) (v: cval) : cval :=
  match v with
  | cval_new T ds     => cval_new (subst_ctyp z u T) (subst_cdefs z u ds)
  | cval_lambda T t   => cval_lambda (subst_ctyp z u T) (subst_ctrm z u t)
  end
with subst_cdef (z: var) (u: var) (d: cdef) : cdef :=
  match d with
  | cdef_typ L T => cdef_typ L (subst_ctyp z u T)
  | cdef_trm L t => cdef_trm L (subst_ctrm z u t)
  end
with subst_cdefs (z: var) (u: var) (ds: cdefs) : cdefs :=
  match ds with
  | cdefs_nil => cdefs_nil
  | cdefs_cons rest d => cdefs_cons (subst_cdefs z u rest) (subst_cdef z u d)
  end.

Fixpoint subst_constr (z: var) (u: var) (C: constr): constr :=
  match C with
  | ⊤ => ⊤
  | ⊥ => ⊥
  | C1 ⋏ C2 => subst_constr z u C1 ⋏ subst_constr z u C2
  | C1 ⋎ C2 => subst_constr z u C1 ⋎ subst_constr z u C2
  | ∃t C0 => ∃t (subst_constr z u C0)
  | ∃v C0 => ∃v (subst_constr z u C0)
  | t ⦂ T => subst_ctrm z u t ⦂ subst_ctyp z u T
  | T <⦂ U => subst_ctyp z u T <⦂ subst_ctyp z u U
  end.

Lemma subst_constr_and : forall x y C1 C2,
    subst_constr x y C1 ⋏ subst_constr x y C2 = subst_constr x y (C1 ⋏ C2).
Proof.
  introv. reflexivity.
Qed.

(** * Variable Substitution Lemmas *)

(** The following [subst_fresh_XYZ] lemmas state that if [x] is not free
    in a symbol [Y], then [Y[z/x] = Y]. *)

(** Fresh substitution
    - in variables *)
Lemma subst_fresh_cvar: forall x y,
  (forall c: cvar, x \notin fv_cvar c -> subst_cvar x y c = c).
Proof.
  intros. destruct* c. simpl. rewrite subst_fresh_avar; auto.
Qed.

(** - in types and declarations *)
Lemma subst_fresh_ctyp_cdec: forall x y,
  (forall T : ctyp , x \notin fv_ctyp  T  -> subst_ctyp  x y T  = T ) /\
  (forall D : cdec , x \notin fv_cdec  D  -> subst_cdec  x y D  = D ).
Proof.
  intros x y. apply ctyp_mutind; intros; simpls; f_equal*.
  apply* subst_fresh_cvar.
Qed.

Definition subst_fresh_ctyp(x y: var) := proj1 (subst_fresh_ctyp_cdec x y).

(** - in terms, values, and definitions *)
Lemma subst_fresh_ctrm_cval_cdef_cdefs: forall x y,
  (forall t : ctrm , x \notin fv_ctrm  t  -> subst_ctrm  x y t  = t ) /\
  (forall v : cval , x \notin fv_cval  v  -> subst_cval  x y v  = v ) /\
  (forall d : cdef , x \notin fv_cdef  d  -> subst_cdef  x y d  = d ) /\
  (forall ds: cdefs, x \notin fv_cdefs ds -> subst_cdefs x y ds = ds).
Proof.
  intros x y. apply ctrm_mutind; intros; simpls; f_equal*;
    (apply* subst_fresh_cvar || apply* subst_fresh_ctyp_cdec).
Qed.

Lemma subst_fresh_constr: forall x y,
    (forall C, x \notin fv_constr C -> subst_constr x y C = C).
Proof.
  intros.
  dependent induction C; unfold fv_constr; simpl in *; eauto; f_equal;
    eauto using subst_fresh_ctyp, subst_fresh_ctrm_cval_cdef_cdefs.
  apply* subst_fresh_ctrm_cval_cdef_cdefs.
Qed.

(** If a variable has a type, then it is a named variable. *)
Lemma constr_var_typing_implies_avar_f: forall C G a T,
    (C, G) ⊢c trm_var a : T ->
    exists x, a = avar_f x.
Proof.
  introv H; dependent induction H; eauto.
Qed.

Lemma subst_iso_ctyp : forall x y t T,
    t ⩭ T ->
    subst_ctyp x y t ⩭ subst_typ x y T
with subst_iso_cdec : forall x y d D,
    iso_cdec_dec d D ->
    iso_cdec_dec (subst_cdec x y d) (subst_dec x y D).
Proof.
  all: introv Hiso.
  - dependent induction Hiso; try constructor*.
  - dependent induction Hiso; try constructor*.
Qed.
