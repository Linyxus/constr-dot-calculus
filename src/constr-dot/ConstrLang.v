(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import TLC.LibLN.
Require Import String.

Require Import Definitions RecordAndInertTypes Decompose.


Inductive ctyp : Set :=
  | ctyp_tvar_b : nat -> ctyp
  | ctyp_typ : typ -> ctyp.

Inductive ctrm : Set :=
  | ctrm_var_b : nat -> ctrm
  | ctrm_trm : trm -> ctrm.

Coercion ctyp_typ : typ >-> ctyp.
Coercion ctrm_trm : trm >-> ctrm.

Inductive constr : Set :=
| constr_true : constr
| constr_false : constr
| constr_and : constr -> constr -> constr
| constr_or : constr -> constr -> constr
| constr_exists_typ : constr -> constr
| constr_exists_var : constr -> constr
| constr_sub : ctyp -> ctyp -> constr
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


Definition open_rec_ctyp (k : nat) (S : typ) (T : ctyp) : ctyp :=
  match T with
  | ctyp_tvar_b i => If k = i then ctyp_typ S else ctyp_tvar_b i
  | ctyp_typ T0 => ctyp_typ T0
  end.

Definition open_rec_ctrm (k : nat) (u : var) (t : ctrm) : ctrm :=
  match t with
  | ctrm_var_b i => If k = i then ctrm_trm (trm_var (avar_f u)) else ctrm_var_b i
  | ctrm_trm t => ctrm_trm t
  end.

Fixpoint open_rec_constr_typ (k : nat) (T : typ) (C : constr) : constr :=
  match C with
  | constr_true => constr_true
  | constr_false => constr_false
  | constr_and C1 C2 => constr_and (open_rec_constr_typ k T C1) (open_rec_constr_typ k T C2)
  | constr_or C1 C2 => constr_or (open_rec_constr_typ k T C1) (open_rec_constr_typ k T C2)
  | constr_exists_typ C => constr_exists_typ (open_rec_constr_typ (S k) T C)
  | constr_exists_var C => constr_exists_var (open_rec_constr_typ (S k) T C)
  | constr_sub T1 T2 => constr_sub (open_rec_ctyp k T T1) (open_rec_ctyp k T T2)
  | constr_typ t T0 => constr_typ t (open_rec_ctyp k T T0)
  end.

Fixpoint open_rec_constr_var (k : nat) (u : var) (C : constr) : constr :=
  match C with
  | constr_true => constr_true
  | constr_false => constr_false
  | constr_and C1 C2 => constr_and (open_rec_constr_var k u C1) (open_rec_constr_var k u C2)
  | constr_or C1 C2 => constr_or (open_rec_constr_var k u C1) (open_rec_constr_var k u C2)
  | constr_exists_typ C => constr_exists_typ (open_rec_constr_var (S k) u C)
  | constr_exists_var C => constr_exists_var (open_rec_constr_var (S k) u C)
  | constr_sub T1 T2 => constr_sub T1 T2
  | constr_typ t T0 => constr_typ (open_rec_ctrm k u t) T0
  end.


Definition open_ctyp (S : typ) (T : ctyp) : ctyp := open_rec_ctyp 0 S T.
Definition open_constr_typ (T : typ) (C : constr) : constr := open_rec_constr_typ 0 T C.


Inductive ctyp_lc : ctyp -> Prop :=
| ctyp_typ_lc : forall T, ctyp_lc (ctyp_typ T)
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
    (forall x, x \notin L -> constr_lc (open_constr_typ x C)) ->
    constr_lc (∃t C)
| constr_sub_lc : forall S T,
    ctyp_lc S ->
    ctyp_lc T ->
    constr_lc (S <⦂ T)
| constr_typ_lc : forall t T,
    ctyp_lc T ->
    constr_lc (t ⦂ T)
.

Lemma lc_ctyp_open_unchanged : forall S T,
    ctyp_lc T ->
    open_ctyp S T = T.
Proof.
  introv Hc.
  induction Hc; eauto.
Qed.

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

| sat_typ : forall G t T,
    G ⊢ t : T ->
    G ⊧ t ⦂ ctyp_typ T

| sat_sub : forall G S T,
    G ⊢ S <: T ->
    G ⊧ ctyp_typ S <⦂ ctyp_typ T

where "G '⊧' C" := (satisfy_constr G C).

Hint Constructors satisfy_constr constr.

Definition constr_entail (C1 C2 : constr) :=
  forall G,
    inert G ->
    satisfy_constr G C1 -> satisfy_constr G C2.


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

(** If U is fresh for S and T, then
    ∃ U. (S <: U ⋏ U <: T) ⊩ S <: T
 *)
Theorem ent_sub_trans : forall S T,
    ctyp_lc S -> ctyp_lc T ->
    ∃t (S <⦂ (ctyp_tvar_b 0) ⋏ (ctyp_tvar_b 0) <⦂ T) ⊩ S <⦂ T.
Proof.
  introv Hs Ht.
  introe. inversion H; subst.
  unfold open_constr_typ in H3. simpl in H3.
  case_if. clear C.
  pose proof (lc_ctyp_open_unchanged T0 Hs) as Hsu.
  unfold open_ctyp in Hsu. rewrite -> Hsu in H3.
  pose proof (lc_ctyp_open_unchanged T0 Ht) as Hst.
  unfold open_ctyp in Hst. rewrite -> Hst in H3.
  clear Hsu Hst.
  inversion H3; subst. clear H3.
  inversion H5; clear H5; subst.
  inversion H6; clear H6; subst.
  apply* sat_sub.
Qed.

Theorem ent_and_true : forall C,
    C ⋏ ⊤ ⊩ C.
Proof.
  introv. introe.
  inversion H; subst; clear H. auto.
Qed.

Theorem ent_and_false : forall C,
    C ⋎ ⊥ ⊩ C.
Proof.
  introe. inversion H; subst; try assumption.
  inversion H3.
Qed.

(** U1 /\ U2 <: {A: S..T} ⊩ U1 <: {A: S..T} \/ U2 <: {A: S..T}
 *)
Theorem ent_sub_and_rcd_or : forall U1 U2 A S T,
    typ_and U1 U2 <⦂ typ_rcd (dec_typ A S T) ⊩
        U1 <⦂ typ_rcd (dec_typ A S T) ⋎ U2 <⦂ typ_rcd (dec_typ A S T).
Proof.
  introv. introe.
  inversion H; subst; clear H.
  apply invert_subtyp_and1_rcd in H3 as [H3 | H3]; try assumption.
  - constructor. constructor. assumption.
  - apply sat_or2. constructor. assumption.
Qed.

(** {A: S1..T1} <: {A: S2..T2} ⊩ S2 <: S1 ⋏ T1 <: T2 *)
Theorem ent_inv_subtyp_typ : forall A S1 T1 S2 T2,
    typ_rcd (dec_typ A S1 T1) <⦂ typ_rcd (dec_typ A S2 T2) ⊩
        S2 <⦂ S1 ⋏ T1 <⦂ T2.
Proof.
  introv. introe.
  inversion H; subst; clear H.
  apply invert_subtyp_typ in H3 as [Hs1 Hs2]; try assumption.
  constructor; constructor; auto.
Qed.

Theorem ent_subtyp_typ_label_neq_false : forall A S1 T1 B S2 T2,
    A <> B ->
    typ_rcd (dec_typ A S1 T1) <⦂ typ_rcd (dec_typ B S2 T2) ⊩ ⊥.
Proof.
  introv Hne. introe. inversion H; subst; clear H.
  apply invert_subtyp_typ_label_neq_false in H3; try assumption.
  destruct H3.
Qed.

