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

Require Import Definitions RecordAndInertTypes Decompose.


Inductive ctyp : Set :=
  | ctyp_tvar_b : nat -> ctyp
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

(** - typing constraint *)
Notation "x '⦂' T" := (constr_typ x T) (at level 29).

(** - subtyping constraint *)
Notation "S '<⦂' T" := (constr_sub S T) (at level 29).


Definition open_rec_ctyp (k : nat) (S : typ) (T : ctyp) : ctyp :=
  match T with
  | ctyp_tvar_b i => If k = i then ctyp_typ S else ctyp_tvar_b i
  | ctyp_typ T0 => ctyp_typ T0
  end.

Fixpoint open_rec_constr (k : nat) (T : typ) (C : constr) : constr :=
  match C with
  | constr_true => constr_true
  | constr_false => constr_false
  | constr_and C1 C2 => constr_and (open_rec_constr k T C1) (open_rec_constr k T C2)
  | constr_or C1 C2 => constr_or (open_rec_constr k T C1) (open_rec_constr k T C2)
  | constr_exists_typ C => constr_exists_typ (open_rec_constr (S k) T C)
  | constr_sub T1 T2 => constr_sub (open_rec_ctyp k T T1) (open_rec_ctyp k T T2)
  | constr_typ t T0 => constr_typ t (open_rec_ctyp k T T0)
  end.


Definition open_ctyp (S : typ) (T : ctyp) : ctyp := open_rec_ctyp 0 S T.
Definition open_constr (T : typ) (C : constr) : constr := open_rec_constr 0 T C.


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
    G ⊧ open_constr T C ->
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
  unfold open_constr in H3. simpl in H3.
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

Theorem ent_inv_subtyp_typ : forall A S1 T1 S2 T2,
    ctyp_typ (typ_rcd (dec_typ A S1 T1)) <⦂ ctyp_typ (typ_rcd (dec_typ A S2 T2)) ⊩
        ctyp_typ S2 <⦂ ctyp_typ S1 ⋏ ctyp_typ T1 <⦂ ctyp_typ T2.
Proof.
  introv. introe.
  inversion H; subst; clear H.
  apply invert_subtyp_typ in H3 as [Hs1 Hs2]; try assumption.
  constructor; constructor; auto.
Qed.

