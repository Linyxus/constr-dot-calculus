(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import TLC.LibLN.
Require Import String.

Require Import Coq.Program.Equality.

Require Import Definitions RecordAndInertTypes Decompose ConstrLangAlt.
Require Import PartialReplacement.

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
Inductive map_cvar : vctx -> cvar -> avar -> Prop :=
| map_cvar_f_in : forall vm x y,
    binds x y vm ->
    map_cvar vm (cvar_f x) (avar_f y)
| map_cvar_f_notin : forall vm x,
    x # vm ->
    map_cvar vm (cvar_f x) (avar_f x)
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
    (tm, vm) ⊢t ctyp_sel x T ⪯ typ_sel y T

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
    (tm, vm) ⊢v ctrm_cvar x ⪯ trm_var y
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

Hint Constructors map_cvar map_ctyp map_cdec
     map_ctrm map_cval map_cdef map_cdefs.

(** *** Properties of mapping *)

Lemma map_cvar_unique_avar : forall vm c a1 a2,
    map_cvar vm c a1 ->
    map_cvar vm c a2 ->
    a1 = a2.
Proof.
  introv Ha1 Ha2.
  inversion Ha1; inversion Ha2; subst; inversion H5; subst; eauto.
  - lets Heq: (binds_functional H H3). subst. trivial.
  - apply get_none in H3. rewrite H in H3. inversion H3.
  - apply get_none in H. rewrite H3 in H. inversion H.
Qed.

Lemma map_ctyp_unique_typ : forall tm vm T T1 T2,
    (tm, vm) ⊢t T ⪯ T1 ->
    (tm, vm) ⊢t T ⪯ T2 ->
    T1 = T2
with map_cdec_unique_dec : forall tm vm D D1 D2,
    (tm, vm) ⊢d D ⪯ D1 ->
    (tm, vm) ⊢d D ⪯ D2 ->
    D1 = D2.
Proof.
  all: introv Hm1 Hm2.
  - dependent induction T; inversion Hm1; inversion Hm2; subst; trivial; try f_equal.
    -- inversion H7; subst. eapply binds_functional; eassumption.
    -- apply~ map_cdec_unique_dec; eassumption.
    -- specialize (IHT1 _ _ H4 H11). specialize (IHT2 _ _ H5 H12). subst. trivial.
    -- specialize (IHT1 _ _ H4 H11). specialize (IHT2 _ _ H5 H12). subst. trivial.
    -- destruct c.
       + lets Heqy: (map_cvar_unique_avar H4 H10). eauto.
       + inversion H4; inversion H10; subst.
       (* + lets Heqy: (map_cvar_unique_avar H4 H10). eauto. *)
    -- apply~ IHT.
    -- specialize (IHT1 _ _ H4 H11). specialize (IHT2 _ _ H5 H12). subst. trivial.
    -- specialize (IHT1 _ _ H4 H11). specialize (IHT2 _ _ H5 H12). subst. trivial.
  - dependent induction D; inversion Hm1; inversion Hm2; subst; f_equal.
    -- eapply map_ctyp_unique_typ; eassumption.
    -- eapply map_ctyp_unique_typ; eassumption.
    -- eapply map_ctyp_unique_typ; eassumption.
Qed.

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

(* Lemma map_iso_ctyp : forall tm vm T T', *)
(*     T ⩭ T' -> *)
(*     (tm, vm) ⊢t T ⪯ T' *)
(* with map_iso_cdec : forall tm vm D D', *)
(*     iso_cdec_dec D D' -> *)
(*     (tm, vm) ⊢d D ⪯ D'. *)
(* Proof. *)
(*   all: introv Hc. *)
(*   - dependent induction Hc; try constructor; try apply IHHc1; try apply IHHc2; *)
(*       try apply IHHc. *)
(*     -- apply* map_iso_cdec. *)
(*     -- constructor. *)
(*   - dependent induction Hc; try constructor; try apply IHHc; *)
(*       try apply* map_iso_ctyp. *)
(* Qed. *)

(* Lemma map_iso_ctyp_eq : forall tm vm T T1 T2, *)
(*     T ⩭ T1 -> *)
(*     (tm, vm) ⊢t T ⪯ T2 -> *)
(*     T1 = T2 *)
(* with map_iso_cdec_eq : forall tm vm D D1 D2, *)
(*     iso_cdec_dec D D1 -> *)
(*     (tm, vm) ⊢d D ⪯ D2 -> *)
(*     D1 = D2. *)
(* Proof. *)
(*   all: introv Hc Hm. *)
(*   - gen T2. dependent induction Hc; introv Hm. *)
(*     -- inversion Hm; subst. reflexivity. *)
(*     -- inversion Hm; subst. reflexivity. *)
(*     -- inversion Hm; subst. f_equal. apply* map_iso_cdec_eq. *)
(*     -- inversion Hm; subst. f_equal; try apply* IHHc1. apply* IHHc2. *)
(*     -- inversion Hm; subst. f_equal. inversion H4; subst. reflexivity. *)
(*     -- inversion Hm; subst. f_equal. apply* IHHc. *)
(*     -- inversion Hm; subst. f_equal. apply* IHHc1. apply* IHHc2. *)
(*   - gen D2. dependent induction Hc; introv Hm. *)
(*     -- inversion Hm; subst. f_equal; apply* map_iso_ctyp_eq. *)
(*     -- inversion Hm; subst. f_equal. apply* map_iso_ctyp_eq. *)
(* Qed. *)

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
    map_cvar vm t t' ->
    (tm, vm) ⊢t T ⪯ T' ->
    G ⊢ trm_var t' : T' ->
    (tm, vm, G) ⊧ t ⦂ T

| sat_sub : forall tm vm G S S' T T',
    (tm, vm) ⊢t S ⪯ S' ->
    (tm, vm) ⊢t T ⪯ T' ->
    G ⊢ S' <: T' ->
    (tm, vm, G) ⊧ S <⦂ T

where "e '⊧' C" := (satisfy_constr e C).

Hint Constructors satisfy_constr constr.

Definition constr_satisfiable (C : constr) (G : ctx) :=
  exists tm vm, (tm, vm, G) ⊧ C.

Notation "G '⊨' C" := (constr_satisfiable C G) (at level 40).

(** * Substitution Lemma for Constraint Interpretation *)

Lemma ok_concat_swap : forall A (G1 : env A) G2,
    ok (G1 & G2) -> ok (G2 & G1).
Proof.
  introv Hok.
  induction G1 using env_ind.
  - rewrite concat_empty_l in *. now rewrite concat_empty_r.
  - apply ok_remove in Hok as Hok12. specialize (IHG1 Hok12).
    rewrite concat_assoc. constructor; eauto.
    apply ok_middle_inv in Hok. destruct Hok as [Hn1 Hn2].
    eauto.
Qed.

Lemma binds_concat_swap : forall A G1 G2 x (T : A),
    ok (G1 & G2) ->
    binds x T (G1 & G2) ->
    binds x T (G2 & G1).
Proof using.
  induction G1 using env_ind; introv Hok HB.
  - rewrite concat_empty_l in *. now rewrite concat_empty_r.
  - apply binds_middle_inv in HB. destruct_all.
    + rewrite concat_assoc. rewrite <- concat_assoc.
      specialize (IHG1 G2 x0 T).
      apply ok_remove in Hok as Hok12. specialize (IHG1 Hok12).
      rewrite concat_assoc. apply* binds_push_neq.
      apply ok_middle_inv_r in Hok. apply get_some_inv in H.
      introv Heq. now subst.
    + subst. rewrite concat_assoc. apply binds_push_eq.
    + rewrite concat_assoc. apply binds_push_neq; eauto.
Qed.

Lemma map_cvar_vm_swap : forall vm1 vm2 vm3 vm4 c x,
    ok (vm2 & vm3) ->
    map_cvar (vm1 & vm2 & vm3 & vm4) c x ->
    map_cvar (vm1 & vm3 & vm2 & vm4) c x.
Proof.
  introv Hok Hm. inversion Hm.
  - subst. rewrite <- (concat_assoc vm1 vm2 vm3) in H.
    apply binds_concat_inv in H. destruct H.
    + constructor. eauto.
    + destruct H as [Hx H].
      apply binds_concat_inv in H; destruct H.
      * constructor. rewrite <- (concat_assoc vm1 vm3 vm2).
        apply binds_concat_left; eauto.
        apply binds_concat_swap in H; eauto using ok_concat_swap.
      * destruct H as [Hx0 H]. rewrite dom_concat in Hx0.
        constructor. repeat apply binds_concat_left; eauto.
  - apply map_cvar_f_notin. eauto.
Qed.

Lemma map_ctyp_vm_swap_rules :
  (forall e t T, e ⊢t t ⪯ T ->
    forall tm vm1 vm2 vm3 vm4,
      e = (tm, vm1 & vm2 & vm3 & vm4) ->
      ok (vm2 & vm3) ->
      (tm, vm1 & vm3 & vm2 & vm4) ⊢t t ⪯ T) /\
  (forall e d D, e ⊢d d ⪯ D ->
    forall tm vm1 vm2 vm3 vm4,
      e = (tm, vm1 & vm2 & vm3 & vm4) ->
      ok (vm2 & vm3) ->
      (tm, vm1 & vm3 & vm2 & vm4) ⊢d d ⪯ D).
Proof.
  apply map_ctyp_mutind; intros; subst; eauto;
    try solve [inversions H0; eauto].
  - inversions H. eauto.
  - inversions H. constructor. apply* map_cvar_vm_swap.
Qed.

Lemma map_ctrm_vm_swap_rules :
  (forall e ct t, e ⊢v ct ⪯ t ->
    forall tm vm1 vm2 vm3 vm4,
      e = (tm, vm1 & vm2 & vm3 & vm4) ->
      ok (vm2 & vm3) ->
      (tm, vm1 & vm3 & vm2 & vm4) ⊢v ct ⪯ t) /\
  (forall e v T, e ⊢vv v ⪯ T ->
    forall tm vm1 vm2 vm3 vm4,
      e = (tm, vm1 & vm2 & vm3 & vm4) ->
      ok (vm2 & vm3) ->
      (tm, vm1 & vm3 & vm2 & vm4) ⊢vv v ⪯ T) /\
  (forall e d D, e ⊢vd d ⪯ D ->
    forall tm vm1 vm2 vm3 vm4,
      e = (tm, vm1 & vm2 & vm3 & vm4) ->
      ok (vm2 & vm3) ->
      (tm, vm1 & vm3 & vm2 & vm4) ⊢vd d ⪯ D) /\
  (forall e ds T, e ⊢vds ds ⪯ T ->
    forall tm vm1 vm2 vm3 vm4,
      e = (tm, vm1 & vm2 & vm3 & vm4) ->
      ok (vm2 & vm3) ->
      (tm, vm1 & vm3 & vm2 & vm4) ⊢vds ds ⪯ T).
Proof.
  apply map_ctrm_mutind; intros; subst; eauto.
  - inversions H. constructor. apply* map_cvar_vm_swap.
  - inversions H0. constructor. apply* map_ctyp_vm_swap_rules.
    apply* H.
  - inversions H0. constructor. apply* map_ctyp_vm_swap_rules.
    apply* H.
  - inversions H. constructor. apply* map_ctyp_vm_swap_rules.
Qed.

Lemma satisfy_vm_swap : forall tm vm1 vm2 vm3 vm4 G C,
    ok (vm2 & vm3) ->
    (tm, vm1 & vm2 & vm3 & vm4, G) ⊧ C ->
    (tm, vm1 & vm3 & vm2 & vm4, G) ⊧ C.
Proof.
  introv Hneq HC.
  dependent induction HC; eauto.
  - apply sat_exists_var with (L:=L) (u:=u). introv Hx.
    specialize (H0 x Hx G (vm4 & x ~ u) vm3 vm2 Hneq).
    rewrite <- concat_assoc.
    apply* H0.
    rewrite -> concat_assoc. eauto.
  - apply sat_typ with (t':=t') (T':=T').
    apply* map_cvar_vm_swap.
    apply* map_ctyp_vm_swap_rules. eauto.
  - apply sat_sub with (S':=S') (T':=T'); eauto; apply* map_ctyp_vm_swap_rules.
Qed.

(** ** Properties of partial replacement and interpretation *)

Lemma map_cvar_prepl : forall vm c c' a x y z,
    x \notin fv_cvar c ->
    map_cvar vm c a ->
    map_cvar vm (cvar_f y) (avar_f z) ->
    prepl_cvar y x c c' ->
    map_cvar (vm & x ~ z) c' a.
Proof.
  introv Hx Hm Hy Hp.
  inversions Hm; inversions Hp; eauto.
  - simpl in Hx. rewrite notin_singleton in Hx.
    apply map_cvar_f_in. eapply binds_push_neq; eauto.
  - simpl in Hx. rewrite notin_singleton in Hx.
    inversions Hy.
    -- apply map_cvar_f_in.
       lets Heq: (binds_functional H H3).
       subst. eauto.
    -- apply get_some_inv in H. unfold notin in H3.
       apply H3 in H. destruct H.
  - simpl in Hx. rewrite notin_singleton in Hx.
    eauto.
  - simpl in Hx. rewrite notin_singleton in Hx.
    inversions Hy.
    -- apply get_some_inv in H3. contradiction.
    -- eauto.
Qed.

Lemma map_ctyp_prepl_rules :
  (forall e t T, e ⊢t t ⪯ T ->
    forall tm vm x y z t',
      e = (tm, vm) ->
      map_cvar vm (cvar_f y) (avar_f z) ->
      prepl_ctyp y x t t' ->
      x \notin fv_ctyp t ->
      (tm, vm & x ~ z) ⊢t t' ⪯ T) /\
  (forall e d D, e ⊢d d ⪯ D ->
    forall tm vm x y z d',
      e = (tm, vm) ->
      map_cvar vm (cvar_f y) (avar_f z) ->
      prepl_cdec y x d d' ->
      x \notin fv_cdec d ->
      (tm, vm & x ~ z) ⊢d d' ⪯ D).
Proof.
  apply map_ctyp_mutind; intros; subst; eauto;
    try solve [inversions H0; eauto].
  - inversions H. inversions H1. eauto.
  - inversions H. inversions H1. eauto.
  - inversions H1. inversions H. eauto.
  - inversions H2. inversions H0.
    eauto.
  - inversions H1. inversions H3. simpl in H4.
    eauto.
  - inversions H. inversion H1. subst. constructor.
    simpl in H2.
    eapply map_cvar_prepl. exact H2.
    exact m. exact H0. exact H7.
  - inversions H0. inversion H2; subst. simpl in H3.
    eauto.
  - inversions H1. inversions H3.
  - inversions H1. inversions H3. simpl in H4.
    eauto.
  - inversions H0. inversions H2. simpl in H3.
    eauto.
Qed.

Lemma map_ctyp_prepl : forall tm vm x y z t t' T,
    (tm, vm) ⊢t t ⪯ T ->
    map_cvar vm (cvar_f y) (avar_f z) ->
    prepl_ctyp y x t t' ->
    x \notin fv_ctyp t ->
    (tm, vm & x ~ z) ⊢t t' ⪯ T.
Proof.
  introv m p Hx.
  lets H: (proj21 map_ctyp_prepl_rules). apply* H.
Qed.

Lemma map_ctrm_prepl_rules :
  (forall e ct t, e ⊢v ct ⪯ t ->
    forall tm vm x y z ct',
      e = (tm, vm) ->
      map_cvar vm (cvar_f y) (avar_f z) ->
      prepl_ctrm y x ct ct' ->
      x \notin fv_ctrm ct ->
      (tm, vm & x ~ z) ⊢v ct' ⪯ t) /\
  (forall e cv v, e ⊢vv cv ⪯ v ->
    forall tm vm x y z cv',
      e = (tm, vm) ->
      map_cvar vm (cvar_f y) (avar_f z) ->
      prepl_cval y x cv cv' ->
      x \notin fv_cval cv ->
      (tm, vm & x ~ z) ⊢vv cv' ⪯ v) /\
  (forall e cd d, e ⊢vd cd ⪯ d ->
    forall tm vm x y z cd',
      e = (tm, vm) ->
      map_cvar vm (cvar_f y) (avar_f z) ->
      prepl_cdef y x cd cd' ->
      x \notin fv_cdef cd ->
      (tm, vm & x ~ z) ⊢vd cd' ⪯ d) /\
  (forall e cds ds, e ⊢vds cds ⪯ ds ->
    forall tm vm x y z cds',
      e = (tm, vm) ->
      map_cvar vm (cvar_f y) (avar_f z) ->
      prepl_cdefs y x cds cds' ->
      x \notin fv_cdefs cds ->
      (tm, vm & x ~ z) ⊢vds cds' ⪯ ds).
Proof.
  Ltac solver_step1 :=
    match goal with
    | H : (_, _) = (_, _) |- _ => inversions H
    end.

  Ltac solver_step2 :=
    match goal with
    | H : prepl_ctrm _ _ _ _ |- _ => inversion H; subst
    | H : prepl_cval _ _ _ _ |- _ => inversion H; subst
    | H : prepl_cdef _ _ _ _ |- _ => inversion H; subst
    | H : prepl_cdefs _ _ _ _ |- _ => inversion H; subst
    end.

  Ltac solver_step3 :=
    match goal with
    | H : _ \notin _ |- _ => simpl in H
    end.

  Ltac the_solver :=
    solver_step1; solver_step2; solver_step3;
    constructor; eauto using map_ctyp_prepl, map_cvar_prepl.

  apply map_ctrm_mutind; intros; subst; eauto; try the_solver.
Qed.

Lemma map_ctrm_prepl : forall tm vm x y z ct ct' t,
    (tm, vm) ⊢v ct ⪯ t ->
    map_cvar vm (cvar_f y) (avar_f z) ->
    prepl_ctrm y x ct ct' ->
    x \notin fv_ctrm ct ->
    (tm, vm & x ~ z) ⊢v ct' ⪯ t.
Proof.
  introv m p Hx.
  lets H: (proj41 map_ctrm_prepl_rules). eauto.
Qed.

Lemma map_cvar_elim_tail : forall vm x u y z,
    map_cvar vm (cvar_f y) (avar_f z) ->
    x <> y ->
    map_cvar (vm & x ~ u) (cvar_f y) (avar_f z).
Proof.
  introv Hm Hneq.
  inversion Hm.
  - subst. constructor. apply binds_push_neq; eauto.
  - subst. apply map_cvar_f_notin. eauto.
Qed.

Lemma prepl_constr_satisfy : forall x y z tm vm G C C',
    (tm, vm, G) ⊧ C ->
    prepl_constr y x C C' ->
    map_cvar vm (cvar_f y) (avar_f z) ->
    x \notin fv_constr C ->
    (tm, vm & x ~ z, G) ⊧ C'.
Proof.
  introv HC Hpr Hm Hx. gen C'.
  dependent induction HC; introv Hpr.
  - inversions Hpr. eauto.
  - inversions Hpr. simpl in Hx. constructor; eauto.
  - inversions Hpr. simpl in Hx. apply sat_or1. eauto.
  - inversions Hpr. simpl in Hx. apply sat_or2. eauto.
  - inversions Hpr. simpl in Hx. apply sat_exists_typ with (L:=L) (T:=T).
    introv Hx0.
    apply~ H0; eauto.
    lets Heq: (open_constr_typ_fv C 0 x0). unfold open_constr_typ.
    rewrite <- Heq. eauto.
    apply~ open_constr_typ_prepl.
  - inversions Hpr. simpl in Hx. apply sat_exists_var with (L:=L \u \{x} \u \{y}) (u:=u).
    introv Hx0.
    assert (HxL: x0 \notin L) by eauto.
    specialize (H0 x0 HxL).
    specialize (H0 _ _ _ eq_refl).
    rewrite <- (concat_empty_r (vm & x ~ z & x0 ~ u)).
    apply satisfy_vm_swap; eauto.
    + assert (Hxu: x0 \notin \{x}) by eauto. constructor.
      rewrite <- concat_empty_l. eauto.
      rewrite dom_single. eauto.
    + rewrite concat_empty_r.
      assert (Hm1: map_cvar (vm & x0 ~ u) (cvar_f y) (avar_f z)). {
        apply* map_cvar_elim_tail.
      }
      specialize (H0 Hm1).
      assert (Hx1: x \notin fv_constr (C ^^v x0)). {
        unfold open_constr_var.
        lets Hfv: (open_constr_var_fv C 0 x0). destruct Hfv as [Hfv | Hfv].
        - rewrite <- Hfv. eauto.
        - rewrite <- Hfv. eauto.
      }
      specialize (H0 Hx1).
      apply~ H0.
      apply~ open_constr_var_prepl.
  - inversions Hpr. simpl in Hx. econstructor.
    + eapply map_cvar_prepl with (c:=t). eauto.
      exact H. exact Hm. eauto.
    + eapply map_ctyp_prepl. exact H0. exact Hm. exact H8. eauto.
    + eauto.
  - inversions Hpr. simpl in Hx. econstructor.
    + eapply map_ctyp_prepl. exact H. exact Hm. exact H6. eauto.
    + eapply map_ctyp_prepl. exact H0. exact Hm. exact H8. eauto.
    + eauto.
Qed.

