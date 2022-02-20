(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module defines various helper lemmas about opening, closing, and local closure. *)


Set Implicit Arguments.

Require Import TLC.LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions ConstrLangAlt ConstrEntailment ConstrTyping Binding.
Require Import PartialReplacement.
Require Import ConstrInterp.

(** * Substitution Definitions *)

Definition subst_cvar (z: var) (u: var) (c: cvar) : cvar :=
  match c with
  (* | cvar_x x => cvar_x (subst_avar z u x) *)
  | cvar_b i => cvar_b i
  (* | cvar_b_l i => cvar_b_l i *)
  | cvar_f x => cvar_f (If x = z then u else x)
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
  | t ⦂ T => subst_cvar z u t ⦂ subst_ctyp z u T
  | T <⦂ U => subst_ctyp z u T <⦂ subst_ctyp z u U
  end.

Lemma subst_to_prepl_cvar : forall c x y,
    prepl_cvar y x (subst_cvar x y c) c.
Proof.
  introv. destruct c.
  - simpl. cases_if; constructor.
  - simpl. constructor.
Qed.

Lemma subst_to_prepl_ctyp_rules :
  (forall T x y,
    prepl_ctyp y x (subst_ctyp x y T) T) /\
  (forall D x y,
    prepl_cdec y x (subst_cdec x y D) D).
Proof.
  apply ctyp_mutind; intros; eauto;
    simpl in *; eauto using subst_to_prepl_cvar.
Qed.

Lemma subst_to_prepl_constr : forall C x y,
    prepl_constr y x (subst_constr x y C) C.
Proof.
  introv.
  dependent induction C; eauto;
    try solve [simpl; constructor; eauto].
  - simpl. constructor; apply* subst_to_prepl_ctyp_rules.
  - simpl. constructor.
    apply* subst_to_prepl_cvar.
    apply* subst_to_prepl_ctyp_rules.
Qed.

Lemma subst_open_ctyp_typ_commute :
  (forall T x y k u,
    subst_ctyp x y (open_rec_ctyp_typ k u T) = open_rec_ctyp_typ k u (subst_ctyp x y T)) /\
  (forall D x y k u,
    subst_cdec x y (open_rec_cdec_typ k u D) = open_rec_cdec_typ k u (subst_cdec x y D)).
Proof.
  apply ctyp_mutind; intros; eauto;
    simpl in *; eauto;
    try solve [f_equal; eauto].
Qed.

Lemma subst_open_cvar_commute : forall c x y k u,
    u <> x ->
    subst_cvar x y (open_rec_cvar k u c) = open_rec_cvar k u (subst_cvar x y c).
Proof.
  introv Hne. destruct c.
  - simpl. cases_if; eauto.
  - simpl. cases_if; eauto.
    simpl. cases_if. eauto.
Qed.

Lemma subst_open_ctyp_var_commute :
  (forall T x y k u,
    u <> x ->
    subst_ctyp x y (open_rec_ctyp_var k u T) = open_rec_ctyp_var k u (subst_ctyp x y T)) /\
  (forall D x y k u,
    u <> x ->
    subst_cdec x y (open_rec_cdec_var k u D) = open_rec_cdec_var k u (subst_cdec x y D)).
Proof.
  apply ctyp_mutind; intros; eauto;
    simpl in *; eauto;
    try solve [f_equal; eauto using subst_open_cvar_commute].
Qed.

Lemma subst_open_ctrm_typ_commute :
  (forall t x y k u,
    subst_ctrm x y (open_rec_ctrm_typ k u t) = open_rec_ctrm_typ k u (subst_ctrm x y t)) /\
  (forall v x y k u,
    subst_cval x y (open_rec_cval_typ k u v) = open_rec_cval_typ k u (subst_cval x y v)) /\
  (forall d x y k u,
    subst_cdef x y (open_rec_cdef_typ k u d) = open_rec_cdef_typ k u (subst_cdef x y d)) /\
  (forall ds x y k u,
    subst_cdefs x y (open_rec_cdefs_typ k u ds) = open_rec_cdefs_typ k u (subst_cdefs x y ds)).
Proof.
  apply ctrm_mutind; intros; eauto;
    simpl in *; eauto;
    try solve [f_equal; eauto using subst_open_ctyp_typ_commute].
  - f_equal.
    + apply* subst_open_ctyp_typ_commute.
    + apply* H.
  - f_equal; try apply* subst_open_ctyp_typ_commute.
    now apply* H.
  - f_equal; apply* subst_open_ctyp_typ_commute.
Qed.

Lemma subst_open_constr_typ_commute : forall x y C k u,
    subst_constr x y (open_rec_constr_typ k u C) = open_rec_constr_typ k u (subst_constr x y C).
Proof.
  dependent induction C; eauto;
    intros; simpl in *; eauto;
    try solve [ unfold open_constr_typ; simpl in *; f_equal; eauto ].
  - f_equal; apply* subst_open_ctyp_typ_commute.
  - f_equal. apply* subst_open_ctyp_typ_commute.
Qed.

Lemma subst_open_constr_var_commute : forall x y C k u,
    u <> x ->
    subst_constr x y (open_rec_constr_var k u C) = open_rec_constr_var k u (subst_constr x y C).
Proof.
  dependent induction C; eauto;
    intros; simpl in *; eauto;
    try solve [ unfold open_constr_typ; simpl in *; f_equal; eauto ].
  - f_equal; apply* subst_open_ctyp_var_commute.
  - f_equal. apply* subst_open_cvar_commute. apply* subst_open_ctyp_var_commute.
Qed.

Lemma map_cvar_subst_aux : forall vm1 vm2 x y z c a,
    map_cvar (vm1 & x ~ z & vm2) c a ->
    x # vm2 ->
    map_cvar (vm1 & vm2) (cvar_f y) (avar_f z) ->
    map_cvar (vm1 & vm2) (subst_cvar x y c) a.
Proof.
  introv Hm Hx Hyz.
  inversion Hm.
  - subst. simpl. cases_if.
    + lets Hb: (binds_middle_eq vm1 z Hx).
      lets Heq: (binds_functional H Hb). now subst.
    + apply map_cvar_f_in. apply binds_remove with (E2:=x~z); eauto.
  - subst.
    rewrite dom_concat in H. rewrite dom_concat in H.
    rewrite dom_single in H.
    assert (Hneq: x0 <> x) by eauto.
    simpl. cases_if. apply map_cvar_f_notin. eauto.
Qed.

Lemma map_cvar_subst : forall vm x y z c a,
    map_cvar (vm & x ~ z) c a ->
    map_cvar vm (cvar_f y) (avar_f z) ->
    map_cvar vm (subst_cvar x y c) a.
Proof.
  introv Hm Hyz.
  inversion Hm.
  - subst. simpl. cases_if.
    + apply binds_push_eq_inv in H as Heq. now subst.
    + constructor. eapply binds_push_neq_inv. exact H. exact C.
  - subst. rewrite dom_concat in H.
    rewrite dom_single in H.
    assert (Hneq: x0 <> x). {
      eauto.
    }
    simpl. cases_if. apply map_cvar_f_notin. eauto.
Qed.

Lemma map_ctyp_subst_rules_aux :
  (forall e t T, e ⊢t t ⪯ T ->
    forall tm vm1 vm2 x y z,
      map_cvar (vm1 & vm2) (cvar_f y) (avar_f z) ->
      e = (tm, vm1 & x ~ z & vm2) ->
      x # vm2 ->
      (tm, vm1 & vm2) ⊢t (subst_ctyp x y t) ⪯ T) /\
  (forall e d D, e ⊢d d ⪯ D ->
    forall tm vm1 vm2 x y z,
      map_cvar (vm1 & vm2) (cvar_f y) (avar_f z) ->
      e = (tm, vm1 & x ~ z & vm2) ->
      x # vm2 ->
      (tm, vm1 & vm2) ⊢d (subst_cdec x y d) ⪯ D).
Proof.
  apply map_ctyp_mutind; intros; eauto;
    simpl in *; eauto.
  - inversions H0. simpl. now constructor.
  - inversions H0. constructor. apply* map_cvar_subst_aux.
Qed.

Lemma map_ctyp_subst_rules :
  (forall e t T, e ⊢t t ⪯ T ->
    forall tm vm x y z,
      map_cvar vm (cvar_f y) (avar_f z) ->
      e = (tm, vm & x ~ z) ->
      (tm, vm) ⊢t (subst_ctyp x y t) ⪯ T) /\
  (forall e d D, e ⊢d d ⪯ D ->
    forall tm vm x y z,
      map_cvar vm (cvar_f y) (avar_f z) ->
      e = (tm, vm & x ~ z) ->
      (tm, vm) ⊢d (subst_cdec x y d) ⪯ D).
Proof.
  apply map_ctyp_mutind; intros; eauto;
    simpl in *; eauto.
  - inversions H0. simpl. now constructor.
  - inversions H0. constructor. apply* map_cvar_subst.
Qed.

Lemma map_cvar_push_neq : forall vm x z0 y z,
    map_cvar vm (cvar_f y) (avar_f z) ->
    x <> y ->
    map_cvar (vm & x ~ z0) (cvar_f y) (avar_f z).
Proof.
  introv Hm Hneq. inversion Hm; subst; eauto.
Qed.

Lemma subst_constr_satisfy_aux : forall x y z tm vm1 vm2 G C,
    (tm, vm1 & x ~ z & vm2, G) ⊧ C ->
    x # vm2 ->
    map_cvar (vm1 & vm2) (cvar_f y) (avar_f z) ->
    (tm, vm1 & vm2, G) ⊧ subst_constr x y C.
Proof.
  introv HC Hx Hm.
  dependent induction HC; eauto.
  - simpl. constructor. apply* IHHC1. apply* IHHC2.
  - simpl. apply sat_or1. apply* IHHC.
  - simpl. apply sat_or2. apply* IHHC.
  - simpl. apply sat_exists_typ with (L:=L) (T:=T). introv HxL.
    specialize (H0 x0 HxL _ _ _ _ _ _ JMeq_refl Hx Hm).
    lets Heq: (subst_open_constr_typ_commute x y C 0 x0).
    unfold open_constr_typ in *. now rewrite <- Heq.
  - simpl. apply sat_exists_var with (L:=L \u \{x} \u \{y}) (u:=u).
    introv Hx0. assert (HxL: x0 \notin L) by eauto.
    assert (Heq: (tm, vm1 & x ~ z & vm2 & x0 ~ u, G) ~= (tm, vm1 & x ~ z & (vm2 & x0 ~ u), G)).
    {
      now rewrite concat_assoc.
    }
    specialize (H0 x0 HxL _ _ _ vm1 (vm2 & x0 ~ u) _ Heq).
    assert (Hxn: x # vm2 & x0 ~ u). {
      rewrite dom_concat. eauto.
    }
    specialize (H0 Hxn).
    assert (Hm1: map_cvar (vm1 & (vm2 & x0 ~ u)) (cvar_f y) (avar_f z)).
    {
      rewrite concat_assoc. apply~ map_cvar_push_neq.
    }
    specialize (H0 Hm1). rewrite <- concat_assoc.
    lets Heq1: subst_open_constr_var_commute.
    specialize (Heq1 x y C 0 x0).
    assert (Hneq0: x0 <> x) by eauto.
    specialize (Heq1 Hneq0). unfold open_constr_var in *.
    now rewrite <- Heq1.
  - simpl in *.
    apply sat_typ with (t':=t') (T':=T'); eauto.
    apply* map_cvar_subst_aux. apply* map_ctyp_subst_rules_aux.
  - simpl.
    apply sat_sub with (S':=S') (T':=T'); eauto; apply* map_ctyp_subst_rules_aux.
Qed.

Lemma subst_constr_satisfy : forall x y z tm vm G C,
    (tm, vm & x ~ z, G) ⊧ C ->
    map_cvar vm (cvar_f y) (avar_f z) ->
    (tm, vm, G) ⊧ subst_constr x y C.
Proof.
  introv Hm Hyz.
  lets Heq1: concat_empty_r vm. rewrite <- Heq1.
  rewrite <- (concat_empty_r (vm & x ~ z)) in Hm.
  apply* subst_constr_satisfy_aux.
  now rewrite -> concat_empty_r.
Qed.

Lemma map_cvar_exists : forall vm x,
    exists y, map_cvar vm (cvar_f x) (avar_f y).
Proof.
  introv.
  induction vm using env_ind.
  - exists x. apply map_cvar_f_notin.
    rewrite dom_empty. apply notin_empty.
  - destruct IHvm as [y IH]. inversion IH.
    + subst.
      assert (Hx: x \in dom (vm & x0 ~ v)). {
        rewrite dom_concat. rewrite in_union. left.
        now apply get_some_inv in H2.
      }
      lets Hv: (get_some Hx). destruct Hv as [v0 Hv].
      exists v0. now apply map_cvar_f_in.
    + subst.
      lets Hg: get_push y x0 v vm. cases_if.
      * exists v. now apply map_cvar_f_in.
      * assert (Hgn1: get y vm = None). {
          apply~ get_none.
        }
        rewrite Hgn1 in Hg.
        apply get_none_inv in Hg.
        exists y.
        now apply map_cvar_f_notin.
Qed.

Lemma subst_cvar_fresh : forall x y c,
    x <> y ->
    x \notin fv_cvar (subst_cvar x y c).
Proof.
  introv Hneq. destruct c.
  - simpl. cases_if; eauto.
  - simpl. eauto.
Qed.

Lemma subst_ctyp_fresh_rules :
  (forall T x y, x <> y -> x \notin fv_ctyp (subst_ctyp x y T)) /\
  (forall D x y, x <> y -> x \notin fv_cdec (subst_cdec x y D)).
Proof.
  apply ctyp_mutind; intros;
    simpl in *; eauto using subst_cvar_fresh.
Qed.

Definition subst_ctyp_fresh := proj21 subst_ctyp_fresh_rules.

Lemma subst_constr_fresh : forall C x y,
    x <> y ->
    x \notin fv_constr (subst_constr x y C).
Proof.
  introv Hneq.
  dependent induction C;
    simpl in *; eauto using subst_ctyp_fresh, subst_cvar_fresh.
Qed.

Lemma subst_constr_entail : forall x y C D,
    x <> y ->
    C ⊩ D ->
    subst_constr x y C ⊩ subst_constr x y D.
Proof.
  introv Hneq Hent. introe.
  destruct (map_cvar_exists vm y) as [z Hm].
  lets Hfrx: (subst_constr_fresh C Hneq).
  lets Hpr: (subst_to_prepl_constr C x y).
  lets Hsat1: prepl_constr_satisfy.
  specialize (Hsat1 x y z tm vm G (subst_constr x y C) C).
  specialize (Hsat1 H Hpr Hm Hfrx).
  apply Hent in Hsat1 as Hsat2; eauto.
  now apply subst_constr_satisfy with (z:=z).
Qed.

Lemma subst_cvar_same : forall x c,
    subst_cvar x x c = c.
Proof.
  introv. destruct c; eauto.
  simpl. cases_if; eauto.
Qed.

Lemma subst_ctyp_same_rules :
  (forall T x, subst_ctyp x x T = T) /\
  (forall D x, subst_cdec x x D = D).
Proof.
  apply ctyp_mutind; intros;
    simpl in *; eauto;
    try solve [f_equal; eauto using subst_cvar_same].
Qed.

Definition subst_ctyp_same := proj21 subst_ctyp_same_rules.

Lemma subst_constr_same : forall C x,
    subst_constr x x C = C.
Proof.
  introv.
  dependent induction C; simpl in *; eauto;
    try solve [f_equal; eauto using subst_ctyp_same, subst_cvar_same].
Qed.

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
  intros. destruct* c. simpl. cases_if.
  simpl in H. apply notin_same in H. destruct H.
  trivial.
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
  apply* subst_fresh_cvar.
Qed.

(** If a variable has a type, then it is a named variable. *)
Lemma constr_var_typing_implies_avar_f: forall C G a T,
    (C, G) ⊢c trm_var a : T ->
    exists x, a = avar_f x.
Proof.
  introv H; dependent induction H; eauto.
Qed.

(* Lemma subst_iso_ctyp : forall x y t T, *)
(*     t ⩭ T -> *)
(*     subst_ctyp x y t ⩭ subst_typ x y T *)
(* with subst_iso_cdec : forall x y d D, *)
(*     iso_cdec_dec d D -> *)
(*     iso_cdec_dec (subst_cdec x y d) (subst_dec x y D). *)
(* Proof. *)
(*   all: introv Hiso. *)
(*   - dependent induction Hiso; try constructor*. *)
(*   - dependent induction Hiso; try constructor*. *)
(* Qed. *)

