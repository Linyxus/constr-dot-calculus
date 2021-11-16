(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module reasons about the precise types of variables in inert contexts. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import Definitions RecordAndInertTypes TightTyping SemanticSubtyping.
Require Import Binding GeneralToTight.


Lemma prec_to_general : forall G S T,
    G ⊢! S <: T ->
    G ⊢ S <: T.
Proof.
  introv Hp.
  destruct tight_to_general as [_ Ht].
  apply Ht. apply* prec_to_tight.
Qed.

Lemma general_to_prec : forall G S T,
    inert G ->
    G ⊢ S <: T ->
    G ⊢! S <: T.
Proof.
  introv H0 Hg.
  apply* tight_to_prec.
  apply* general_to_tight.
Qed.


Theorem invert_subtyp_typ_t : forall G0,
    inert G0 ->
    (forall A S1 T1 S2 T2,
        G0 ⊢# typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2) ->
        G0 ⊢# S2 <: S1 /\ G0 ⊢# T1 <: T2).
Proof.
  eauto.
Qed.

Theorem invert_subtyp_typ : forall G0 A S1 T1 S2 T2,
    inert G0 ->
    G0 ⊢ typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2) ->
    G0 ⊢ S2 <: S1 /\ G0 ⊢ T1 <: T2.
Proof.
  introv H0 Hs.
  apply general_to_prec in Hs; try assumption.
  apply destruct_subtyp_typ_p in Hs as [Hs1 Hs2]; try assumption.
  split; apply* tight_to_general.
Qed.

Lemma invert_subtyp_and1_rcd_p : forall G U1 U2 A S T,
    G ⊢! typ_and U1 U2 <: typ_rcd (dec_typ A S T) ->
    G ⊢! U1 <: typ_rcd (dec_typ A S T) \/ G ⊢! U2 <: typ_rcd (dec_typ A S T).
Proof.
  intros G U1 U2 A S T H.
  inversion H.
  - auto.
  - auto.
Qed.

Lemma invert_subtyp_and1_rcd : forall G U1 U2 A S T,
    inert G ->
    G ⊢ typ_and U1 U2 <: typ_rcd (dec_typ A S T) ->
    G ⊢ U1 <: typ_rcd (dec_typ A S T) \/ G ⊢ U2 <: typ_rcd (dec_typ A S T).
Proof.
  introv H0 Hg.
  apply (general_to_prec H0) in Hg.
  apply invert_subtyp_and1_rcd_p in Hg as [Hg | Hg].
  - left. apply* prec_to_general.
  - right. apply* prec_to_general.
Qed.

Lemma invert_subtyp_typ_label_neq_false : forall G A S1 T1 B S2 T2,
    inert G ->
    G ⊢ typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ B S2 T2) ->
    A <> B ->
    False.
Proof.
  introv H0 Hs Heq.
  apply Heq. apply general_to_prec in Hs; try assumption.
  apply* destruct_subtyp_typ_p_label.
Qed.

Lemma typ_bounds_subtyping : forall G x A S1 T1 S2 T2,
    G ⊢ trm_var (avar_f x) : typ_rcd (dec_typ A S1 T1) ->
    G ⊢ trm_var (avar_f x) : typ_rcd (dec_typ A S2 T2) ->
    G ⊢ S1 <: T2 /\ G ⊢ S2 <: T1.
Proof.
  introv Hs1 Hs2.
  split;
    apply subtyp_trans with (T := typ_sel (avar_f x) A);
    eauto.
Qed.

Lemma invert_subtyp_and2_p : forall G S T U,
    G ⊢! S <: typ_and T U ->
    G ⊢! S <: T /\ G ⊢! S <: U.
Proof.
  introv Hsub.
  remember (typ_and T U) as and2. gen T U.
  induction Hsub; subst; introv Heq; try inversion Heq; eauto; try (specialize (IHHsub _ _ Heq) as [IH1 IH2]; eauto).
  subst. eauto.
Qed.

Lemma invert_subtyp_and2 : forall G S T U,
    inert G ->
    G ⊢ S <: typ_and T U ->
    G ⊢ S <: T /\ G ⊢ S <: U.
Proof.
  introv H0 Hs.
  assert (G ⊢! S <: T /\ G ⊢! S <: U) as [Hs1 Hs2]
      by (apply~ invert_subtyp_and2_p; apply~ general_to_prec).
  split; apply* prec_to_general.
Qed.

