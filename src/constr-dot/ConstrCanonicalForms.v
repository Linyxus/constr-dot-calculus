(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module proves the Canonical Forms Lemmas, which allow us
    to retrieve the shape of a value given its type. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import TLC.LibLN.
Require Import Definitions RecordAndInertTypes PreciseTyping TightTyping InvertibleTyping
        GeneralToTight Subenvironments Weakening Narrowing Substitution.
Require Import ConstrLangAlt ConstrEntailment ConstrInterp ConstrTyping.
Require Import EntailmentLaws ConstrSubtypingLaws.
Require Import TightConstrInterp TightConstrEntailment TightConstrTyping.
Require Import PreciseConstrTyping.
Require Import ConstrWeakening ConstrNarrowing.
Require Import ConstrBinding.
Require Import InvertibleConstrTyping.
Require Import CanonicalForms.

(** * Simple Implications of Typing *)

(** If a variable can be typed in an environment,
    then it is bound in that environment. *)
Lemma constr_typing_implies_bound: forall C G x T,
  (C, G) ⊢c trm_var (avar_f x) : T ->
  exists S, binds x S G.
Proof.
  introv Ht. dependent induction Ht; eauto.
Qed.

(** [G ⊢ ds :: ... /\ D /\ ...]       #<br>#
    [―――――――――――――――――――――――]       #<br>#
    [exists d, ds = ... /\ d /\ ...]       #<br>#
    [G ⊢ d: D]                      *)
Lemma record_has_ty_defs: forall C G T ds D,
  (C, G) /-c ds :: T ->
  record_has T D ->
  exists d, defs_has ds d /\ (C, G) /-c d : D.
Proof.
  introv Hdefs Hhas. induction Hdefs.
  - inversion Hhas; subst. exists d. split.
    + unfold defs_has. simpl. rewrite If_l; reflexivity.
    + assumption.
  - inversion Hhas; subst.
    + destruct (IHHdefs H4) as [d' [H1 H2]].
      exists d'. split.
      * unfold defs_has. simpl. rewrite If_r. apply H1.
        apply not_eq_sym. eapply defs_has_hasnt_neq; eauto.
      * assumption.
    + exists d. split.
      * unfold defs_has. simpl. rewrite If_l; reflexivity.
      * inversions* H4.
Qed.

(** * Functions under Inert Contexts *)
(** This lemma corresponds to Lemma 3.7 ([forall] to [G(x)]) in the paper.

    [inert G]            #<br>#
    [G ⊢ x: forall(T)U]       #<br>#
    [――――――――――――――-]    #<br>#
    [exists T', U',]          #<br>#
    [G(x) = forall(T')U']     #<br>#
    [G ⊢ T <: T']        #<br>#
    [forall fresh y, G, y: T ⊢ U'^y <: U^y] *)
Lemma var_typ_all_to_binds: forall C G x T U,
    inert G ->
    G ⊨ C ->
    (C, G) ⊢c trm_var (avar_f x) : typ_all T U ->
    (exists L T' U',
        binds x (typ_all T' U') G /\
        (C, G) ⊢c T <: T' /\
        (forall y, y \notin L -> (C, G & y ~ T) ⊢c (open_typ y U') <: (open_typ y U))).
Proof.
  introv Hin Hs Ht.
  destruct general_to_tight_constr_typing as [general_to_tight_constr_typ _].
  lets Htt: (general_to_tight_constr_typ _ _ _ Ht).
  lets Hs': (general_to_tight_satisfiable Hin Hs).
  lets Hinv: (tight_to_invertible_constr_typing Hin Hs' Htt).
  destruct (constr_invertible_to_precise_typ_all (inert_ok Hin) Hinv) as [T' [U' [V' [L [Htp [Hs1 Hs2]]]]]].
  exists L T' U'. repeat split.
  - apply* inert_precise_all_inv.
  - apply~ tight_to_general_constr_typing.
  - assumption.
Qed.

(** This lemma corresponds to Lemma 3.8 ([forall] to [lambda]) in the paper.

    [inert G]                       #<br>#
    [G ⊢ v: forall(T)U]                  #<br>#
    [――――――――――――]                  #<br>#
    [exists T', t,]                       #<br>#
    [v = lambda(T')t]              #<br>#
    [G ⊢ T <: T']                   #<br>#
    [forall fresh y, G, y: T ⊢ t^y: U^y] *)
Lemma constr_val_typ_all_to_lambda: forall C G v T U,
    inert G ->
    G ⊨ C ->
    (C, G) ⊢c trm_val v : typ_all T U ->
    (exists L T' t,
        v = val_lambda T' t /\
        (C, G) ⊢c T <: T' /\
        (forall y, y \notin L -> (C, G & y ~ T) ⊢c (open_trm y t) : open_typ y U)).
Proof.
  introv Hin Hsat Ht.
  destruct general_to_tight_constr_typing as [general_to_tight_constr_typ _].
  lets Htt: (general_to_tight_constr_typ _ _ _ Ht).
  lets Hsat': (general_to_tight_satisfiable Hin Hsat).
  lets Hinv: (tight_to_invertible_constr_typing_v Hin Hsat' Htt).
  destruct (constr_invertible_val_to_precise_lambda Hin Hinv) as [L [T' [U' [Htp [Hs1 Hs2]]]]].
  inversions Htp.
  exists (L0 \u L \u (dom G)) T' t. repeat split~.
  intros. assert (HL: y \notin L) by auto. assert (HL0: y \notin L0) by auto.
  specialize (Hs2 y HL).
  specialize (H2 y HL0).
  eapply cty_sub; eauto. eapply narrow_constr_typing in H2; eauto.
Qed.

(** * Objects under Inert Contexts *)
(** This lemma corresponds to Lemma 3.9 ([mu] to [G(x)]) in the paper.

    [inert G]                    #<br>#
    [G ⊢ x: {a: T}]              #<br>#
    [―――――――――――――――――――――――]    #<br>#
    [exists S, T', G(x) = mu(S)]       #<br>#
    [S^x = ... /\ {a: T'} /\ ...]  #<br>#
    [G ⊢ T' <: T]                *)
Lemma constr_var_typ_rcd_to_binds: forall C G x a T,
    inert G ->
    G ⊨ C ->
    (C, G) ⊢c trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
    (exists S T',
        binds x (typ_bnd S) G /\
        record_has (open_typ x S) (dec_trm a T') /\
        (C, G) ⊢c T' <: T).
Proof.
  introv Hin Hsat Ht.
  destruct (constr_typing_implies_bound Ht) as [S BiG].
  destruct general_to_tight_constr_typing as [general_to_tight_constr_typ _].
  lets Htt: (general_to_tight_constr_typ _ _ _ Ht).
  lets Hsat': (general_to_tight_satisfiable Hin Hsat).
  lets Hinv: (tight_to_invertible_constr_typing Hin Hsat' Htt).
  destruct (constr_invertible_to_precise_trm_dec Hinv) as [T' [U [Htp Hs]]].
  destruct (pf_inert_rcd_U Hin Htp) as [U' Hr]. subst.
  lets Hr': (precise_flow_record_has Hin Htp). apply pf_binds in Htp.
  exists U' T'. split. assumption. split. assumption. apply* tight_to_general_constr_typing.
Qed.

(** This lemma corresponds to Lemma 3.10 ([mu] to [nu]) in the paper.

    [inert G]                  #<br>#
    [G ⊢ v: mu(T)]             #<br>#
    [G ⊢ x: T^x]               #<br>#
    [T = ... /\ {a: U} /\ ...  ] #<br>#
    [――――――――――――――――――――――――] #<br>#
    [exists t, ds, v = nu(T)ds     ] #<br>#
    [ds^x = ... /\ {a = t} /\ ...] #<br>#
    [G ⊢ t: U] *)
Lemma constr_val_mu_to_new: forall C G v T U a x,
    inert G ->
    G ⊨ C ->
    (C, G) ⊢c trm_val v: typ_bnd T ->
    (C, G) ⊢c trm_var (avar_f x) : open_typ x T ->
    record_has (open_typ x T) (dec_trm a U) ->
    exists t ds,
      v = val_new T ds /\
      defs_has (open_defs x ds) (def_trm a t) /\
      (C, G) ⊢c t: U.
Proof.
  introv Hi Hsat Ht Hx Hr.
  destruct general_to_tight_constr_typing as [general_to_tight_constr_typ _].
  lets Htt: (general_to_tight_constr_typ _ _ _ Ht).
  lets Hsat': (general_to_tight_satisfiable Hi Hsat).
  lets Hinv: (tight_to_invertible_constr_typing_v Hi Hsat' Htt).
  inversions Hinv. inversions H3.
  pick_fresh z. assert (z \notin L) as Hz by auto.
  specialize (H2 z Hz).
  assert ((C, G) /-c open_defs x ds :: open_typ x T) as Hds. {
    apply* renaming_def; eauto.
  }
  destruct (record_has_ty_defs Hds Hr) as [d [Hh Hd]]. inversions Hd.
  exists t ds. split*.
Qed.
