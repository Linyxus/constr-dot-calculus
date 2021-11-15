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

Scheme ctyp_mut := Induction for ctyp Sort Prop
with   cdec_mut := Induction for cdec Sort Prop.
Combined Scheme ctyp_mutind from ctyp_mut, cdec_mut.

Coercion ctyp_typ : typ >-> ctyp.

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

Inductive ctrm : Set :=
  | ctrm_var_b : nat -> ctrm
  | ctrm_trm : trm -> ctrm.

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


(** ** Opening *)

Fixpoint open_rec_ctyp (k : nat) (t : typ) (T : ctyp) : ctyp :=
  match T with
  | ctyp_top => ctyp_top
  | ctyp_bot => ctyp_bot
  | ctyp_tvar i => If k = i then ctyp_typ t else ctyp_tvar i
  | ctyp_typ u => ctyp_typ u
  | ctyp_rcd D => ctyp_rcd (open_rec_cdec k t D)
  | ctyp_and T U => ctyp_and (open_rec_ctyp k t T) (open_rec_ctyp k t U)
  | ctyp_sel x T => ctyp_sel x T
  | ctyp_bnd T => ctyp_bnd (open_rec_ctyp k t T)
  | ctyp_all T U => ctyp_all (open_rec_ctyp k t T) (open_rec_ctyp k t U)
  end
with open_rec_cdec (k : nat) (t : typ) (D : cdec) : cdec :=
  match D with
  | cdec_typ A T U => cdec_typ A (open_rec_ctyp k t T) (open_rec_ctyp k t U)
  | cdec_trm a T => cdec_trm a (open_rec_ctyp k t T)
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
Definition open_cdec (S : typ) (D : cdec) : cdec := open_rec_cdec 0 S D.
Definition open_constr_typ (T : typ) (C : constr) : constr := open_rec_constr_typ 0 T C.

(** ** Lemmas on openning and closed types *)

Lemma open_closed_ctyp_unchanged : forall S T T',
    ctyp_closed T T' ->
    open_ctyp S T = T
with open_closed_cdec_unchanged : forall S D D',
    cdec_closed D D' ->
    open_cdec S D = D.
Proof.
  - introv Hc. induction Hc.
    -- auto.
    -- auto.
    -- auto.
    -- assert (open_cdec S D = D) as Heq.
       {
         apply* open_closed_cdec_unchanged.
       }
       replace (open_ctyp S (ctyp_rcd D)) with (ctyp_rcd (open_rec_cdec 0 S D)).
       {
         unfold open_cdec in Heq. rewrite -> Heq. trivial.
       }
       reflexivity.
    -- replace (open_ctyp S (ctyp_and T U)) with (ctyp_and (open_rec_ctyp 0 S T) (open_rec_ctyp 0 S U)).
       {
         unfold open_ctyp in IHHc1. rewrite -> IHHc1.
         unfold open_ctyp in IHHc2. rewrite -> IHHc2. trivial.
       }
       reflexivity.
     -- reflexivity.
     -- replace (open_ctyp S (ctyp_bnd T)) with (ctyp_bnd (open_rec_ctyp 0 S T)).
        {
          unfold open_ctyp in IHHc. rewrite -> IHHc. auto.
        } auto.
     -- replace (open_ctyp S (ctyp_all S0 T)) with (ctyp_all (open_rec_ctyp 0 S S0) (open_rec_ctyp 0 S T)).
        {
          unfold open_ctyp in IHHc1. rewrite -> IHHc1.
          unfold open_ctyp in IHHc2. rewrite -> IHHc2. trivial.
        }
        auto.
  - introv Hc. induction Hc.
    -- unfold open_cdec. simpl.
       assert (open_ctyp S S0 = S0).
       {
         apply* open_closed_ctyp_unchanged.
       }
       assert (open_ctyp S T = T).
       {
         apply* open_closed_ctyp_unchanged.
       }
       unfold open_ctyp in H1, H2. rewrite -> H1, H2. auto.
    -- unfold open_cdec. simpl.
       assert (open_ctyp S T = T); try apply* open_closed_ctyp_unchanged.
       unfold open_ctyp in H0; rewrite H0; reflexivity.
Qed.

Definition is_closed_ctyp (T : ctyp) := exists T', ctyp_closed T T'.

Lemma open_closed_ctyp_unchanged' : forall S T,
    is_closed_ctyp T ->
    open_ctyp S T = T.
Proof.
  introv [T' Hc]. apply* open_closed_ctyp_unchanged.
Qed.

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
    is_closed_ctyp S -> is_closed_ctyp T ->
    ∃t (S <⦂ (ctyp_tvar 0) ⋏ (ctyp_tvar 0) <⦂ T) ⊩ S <⦂ T.
Proof.
  introv Hs Ht.
  introe. inversion H; subst.
  unfold open_constr_typ in H3. simpl in H3.
  case_if. clear C.
  pose proof (open_closed_ctyp_unchanged' T0 Hs) as Hsu.
  unfold open_ctyp in Hsu. rewrite -> Hsu in H3.
  pose proof (open_closed_ctyp_unchanged' T0 Ht) as Htu.
  unfold open_ctyp in Htu. rewrite -> Htu in H3.
  clear Hsu Htu.
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

