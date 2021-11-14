(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This proof uses the
    #<a href="http://www.chargueraud.org/softs/tlc/">TLC</a>#
    Coq library by Arthur Chargueraud. *)

Set Implicit Arguments.

Require Import TLC.LibLN.
Require Import String.

Require Import Definitions RecordAndInertTypes.


Inductive tvar : Set :=
  | tvar_b : nat -> tvar
  | tvar_f : var -> tvar.


Inductive ctyp : Set :=
  | ctyp_tvar : tvar -> ctyp
  | ctyp_typ : typ -> ctyp.


Inductive constr : Set :=
| constr_true : constr
| constr_false : constr
| constr_and : constr -> constr -> constr
| constr_or : constr -> constr -> constr
| constr_exists_typ : constr -> constr
| constr_sub : ctyp -> ctyp -> constr
| constr_typ : trm -> ctyp -> constr
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

Notation "x '⦂' T" := (constr_typ x T) (at level 29).

Notation "S '<⦂' T" := (constr_sub S T) (at level 29).

Definition open_rec_tvar (k : nat) (u : var) (tv : tvar) : tvar :=
  match tv with
  | tvar_b i => If k = i then tvar_f u else tvar_b i
  | tvar_f x => tvar_f x
  end.


Definition open_rec_ctyp (k : nat) (u : var) (T : ctyp) : ctyp :=
  match T with
  | ctyp_tvar tv => ctyp_tvar (open_rec_tvar k u tv)
  | ctyp_typ T0 => ctyp_typ T0
  end.

Fixpoint open_rec_constr (k : nat) (u : var) (C : constr) : constr :=
  match C with
  | constr_true => constr_true
  | constr_false => constr_false
  | constr_and C1 C2 => constr_and (open_rec_constr k u C1) (open_rec_constr k u C2)
  | constr_or C1 C2 => constr_or (open_rec_constr k u C1) (open_rec_constr k u C2)
  | constr_exists_typ C => constr_exists_typ (open_rec_constr (S k) u C)
  | constr_sub T1 T2 => constr_sub (open_rec_ctyp k u T1) (open_rec_ctyp k u T2)
  | constr_typ t T => constr_typ t (open_rec_ctyp k u T)
  end.


Definition open_tvar (u : var) (tv : tvar) : tvar := open_rec_tvar 0 u tv.
Definition open_ctyp (u : var) (T : ctyp) : ctyp := open_rec_ctyp 0 u T.
Definition open_constr (u : var) (C : constr) : constr := open_rec_constr 0 u C.


Fixpoint fv_tvar (tv : tvar) :=
  match tv with
  | tvar_b i => \{}
  | tvar_f x => \{x}
  end.


Fixpoint fv_ctyp (T : ctyp) :=
  match T with
  | ctyp_tvar tv => fv_tvar tv
  | ctyp_typ T => \{}
  end.


Inductive ctyp_lc : ctyp -> Prop :=

| ctyp_typ_lc : forall T, ctyp_lc (ctyp_typ T)

| ctyp_tvar_f_lc : forall x, ctyp_lc (ctyp_tvar (tvar_f x))

.


Inductive constr_lc : constr -> Prop :=

| constr_true_lc: constr_lc ⊤

| constr_false_lc: constr_lc ⊥

| constr_and_lc : forall C1 C2,
    constr_lc C1 ->
    constr_lc C2 ->
    constr_lc (C1 ⋏ C2)

| constr_or_lc : forall C1 C2,
    constr_lc C1 ->
    constr_lc C2 ->
    constr_lc (C1 ⋎ C2)

| constr_exists_typ_lc : forall L C,
    (forall x, x \notin L -> constr_lc (open_constr x C)) ->
    constr_lc (∃t C)

| constr_sub_lc : forall S T,
    ctyp_lc S ->
    ctyp_lc T ->
    constr_lc (S <⦂ T)

| constr_typ_lc : forall t T,
    ctyp_lc T ->
    constr_lc (t ⦂ T)

.

Lemma lc_ctyp_open_unchanged : forall u T,
    ctyp_lc T ->
    open_ctyp u T = T.
Proof.
  introv Hc.
  induction Hc; eauto.
Qed.

Definition tmap := env typ.

Inductive map_ctyp : tmap -> ctyp -> typ -> Prop :=

  | map_ctyp_tvar : forall tm a T,
      binds a T tm ->
      map_ctyp tm (ctyp_tvar (tvar_f a)) T

  | map_ctyp_typ : forall tm T,
      map_ctyp tm (ctyp_typ T) T

.

Lemma map_bound_tvar : forall tm x T T',
    binds x T tm ->
    map_ctyp tm (ctyp_tvar (tvar_f x)) T' ->
    T = T'.
Proof.
  introv Hb Hm. inversion Hm; subst.
  eapply binds_functional.
  - apply Hb.
  - apply H1.
Qed.


Lemma map_ctyp_fresh_extend : forall tm X T S S',
    map_ctyp tm S S' ->
    X \notin fv_ctyp S ->
    map_ctyp (tm & X ~ T) S S'.
Proof.
  introv Hm Hn.
  inversion Hm; subst.
  - apply* map_ctyp_tvar.


Inductive satisfy_constr : tmap -> ctx -> constr -> Prop :=

| sat_true : forall tm G,
    satisfy_constr tm G constr_true

| sat_and : forall tm G C1 C2,
    satisfy_constr tm G C1 ->
    satisfy_constr tm G C2 ->
    satisfy_constr tm G (C1 ⋏ C2)

| sat_or1 : forall tm G C1 C2,
    satisfy_constr tm G C1 ->
    satisfy_constr tm G (C1 ⋎ C2)

| sat_or2 : forall tm G C1 C2,
    satisfy_constr tm G C2 ->
    satisfy_constr tm G (C1 ⋎ C2)

| sat_exists_typ : forall tm G T L C,
    (forall X, X \notin L ->
      satisfy_constr (tm & X ~ T) G (open_constr X C)) ->
    satisfy_constr tm G (∃t C)

| sat_typ : forall tm G t T T',
    map_ctyp tm T T' ->
    G ⊢ t : T' ->
    satisfy_constr tm G (t ⦂ T)

| sat_sub : forall tm G S S' T T',
    map_ctyp tm S S' ->
    map_ctyp tm T T' ->
    G ⊢ S' <: T' ->
    satisfy_constr tm G (constr_sub S T)

.

Hint Constructors satisfy_constr constr.

Definition constr_entail (C1 C2 : constr) :=
  forall tm G,
    inert G ->
    satisfy_constr tm G C1 -> satisfy_constr tm G C2.


Notation "C '⊩' D" := (constr_entail C D) (at level 50).

Ltac introe := introv H0 H.

Theorem ent_absurd : forall C,
    ⊥ ⊩ C.
Proof.
  introe. inversion H.
Qed.


Theorem ent_tautology : forall C,
    C ⊩ ⊤.
Proof. introe. eauto. Qed.

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

Definition ctyp_b (i : nat) := ctyp_tvar (tvar_b i).

(** ∃ U. (S <: U ⋏ U <: T) ⊩ S <: T *)
Theorem ent_sub_trans : forall S T,
    ctyp_lc S -> ctyp_lc T ->
    ∃t (S <⦂ (ctyp_b 0) ⋏ (ctyp_b 0) <⦂ T) ⊩ S <⦂ T.
Proof.
  introv Hs Ht.
  introe. inversion H; subst.
  unfold open_constr in H4. simpl in H4.
  case_if. clear C.
  pick_fresh_gen (L \u fv_ctyp S \u fv_ctyp T) X.
  specialize (H4 X). assert (X \notin L) as Hnl. { eauto. }
  specialize (H4 Hnl).
  inversion H4; subst.
  pose proof (lc_ctyp_open_unchanged X Hs) as Hsu.
  unfold open_ctyp in Hsu. rewrite -> Hsu in H6.
  pose proof (lc_ctyp_open_unchanged X Ht) as Hst.
  unfold open_ctyp in Hst. rewrite -> Hst in H7.
  inversion H6; subst.
  inversion H7; subst.
  assert (T0 = T') as Heq1.
  {
    apply* map_bound_tvar.
  }
  assert (T0 = S'0) as Heq2.
  {
    apply* map_bound_tvar.
  }
  subst.
  apply sat_sub with (S' := S') (T' := T'0).
  - 

