(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module contains lemmas related to invertible typing
    ([ty_var_inv], [⊢##] and [ty_val_inv], [⊢##v]). *)

Set Implicit Arguments.

Require Import TLC.LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions Narrowing PreciseTyping RecordAndInertTypes Subenvironments.
Require Import ConstrNarrowing ConstrSubenvironments.
Require Import TightTyping.
Require Import ConstrLangAlt ConstrTyping TightConstrTyping PreciseConstrTyping.
Require Import TightConstrEntailment ConstrEntailment.
Require Import TightConstrInterp.
Require Import ConstrInterp.
Require Import MinimalComplete.

(** * Invertible Typing for Constraint-based System *)

(** ** Invertible typing of variables [G ⊢c## x: T] *)

Reserved Notation "e '⊢c##' x ':' T" (at level 40, x at level 59).

Inductive cty_var_inv : (constr * ctx) -> var -> typ -> Prop :=

(** [G ⊢! x: T]  #<br>#
    [―――――――――――] #<br>#
    [G ⊢## x: T]     *)
| cty_precise_inv : forall C G x T U,
  G ⊢! x: T ⪼ U ->
  (C, G) ⊢c## x : U

(** [G ⊢## x: {a: T}] #<br>#
    [G ⊢# T <: U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## x: {a: U}]     *)
| cty_dec_trm_inv : forall C G x a T U,
  (C, G) ⊢c## x : typ_rcd (dec_trm a T) ->
  (C, G) ⊢c# T <: U ->
  (C, G) ⊢c## x : typ_rcd (dec_trm a U)

(** [G ⊢## x: {A: T..U}]   #<br>#
    [G ⊢# T' <: T]         #<br>#
    [G ⊢# U <: U']         #<br>#
    [―――――――――――――――――――――] #<br>#
    [G ⊢## x: {A: T'..U'}]     *)
| cty_dec_typ_inv : forall C G x A T1 T2 U1 U2,
  (C, G) ⊢c## x : typ_rcd (dec_typ A T1 U1) ->
  (C, G) ⊢c# T2 <: T1 ->
  (C, G) ⊢c# U1 <: U2 ->
  (C, G) ⊢c## x : typ_rcd (dec_typ A T2 U2)

(** [G ⊢## x: T^x]   #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢## x: mu(T)] *)
| cty_bnd_inv : forall C G x T,
  (C, G) ⊢c## x : open_typ x T ->
  (C, G) ⊢c## x : typ_bnd T

(** [G ⊢## x: forall(S)T]          #<br>#
    [G ⊢# S' <: S]            #<br>#
    [G, y: S' ⊢ T^y <: T'^y]   #<br>#
    [y fresh]                  #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G ⊢## x: forall(S')T']            *)
| cty_all_inv : forall L C G x S T S' T',
  (C, G) ⊢c## x : typ_all S T ->
  (C, G) ⊢c# S' <: S ->
  (forall y, y \notin L ->
   (C, G & y ~ S') ⊢c open_typ y T <: open_typ y T') ->
  (C, G) ⊢c## x : typ_all S' T'

(** [G ⊢## x : T]     #<br>#
    [G ⊢## x : U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## x : T /\ U]      *)
| cty_and_inv : forall C G x S1 S2,
  (C, G) ⊢c## x : S1 ->
  (C, G) ⊢c## x : S2 ->
  (C, G) ⊢c## x : typ_and S1 S2

(** [G ⊢## x: S]        #<br>#
    [G ⊢! y: {A: S..S}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢## x: y.A           *)
| cty_sel_inv : forall C G x y A S U,
  (C, G) ⊢c## x : S ->
  G ⊢! y : U ⪼ typ_rcd (dec_typ A S S) ->
  (C, G) ⊢c## x : typ_sel (avar_f y) A

(** [G ⊢## x: T]   #<br>#
    [―――――――――――――] #<br>#
    [G ⊢## x: top]     *)
| cty_top_inv : forall C G x T,
  (C, G) ⊢c## x : T ->
  (C, G) ⊢c## x : typ_top
where "e '⊢c##' x ':' T" := (cty_var_inv e x T).

(** ** Invertible typing for values [G ⊢c##v v: T] *)

Reserved Notation "e '⊢c##v' v ':' T" (at level 40, v at level 59).

Inductive cty_val_inv : (constr * ctx) -> val -> typ -> Prop :=

(** [G ⊢! v: T]    #<br>#
    [―――――――――――――] #<br>#
    [G ⊢##v v: T] *)
| cty_precise_inv_v : forall C G v T,
  (C, G) ⊢c!v v : T ->
  (C, G) ⊢c##v v : T

(** [G ⊢##v v: forall(S)T]          #<br>#
    [G ⊢# S' <: S]             #<br>#
    [G, y: S' ⊢ T^y <: T'^y]    #<br>#
    [y fresh]                   #<br>#
    [――――――――――――――――――――――]    #<br>#
    [G ⊢##v v: forall(S')T']            *)
| cty_all_inv_v : forall L C G v S T S' T',
  (C, G) ⊢c##v v : typ_all S T ->
  (C, G) ⊢c# S' <: S ->
  (forall y, y \notin L ->
   (C, G & y ~ S') ⊢c open_typ y T <: open_typ y T') ->
  (C, G) ⊢c##v v : typ_all S' T'

(** [G ⊢##v v: S]       #<br>#
    [G ⊢! y: {A: S..S}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢##v v: y.A]         *)
| cty_sel_inv_v : forall C G v y A S U,
  (C, G) ⊢c##v v : S ->
  G ⊢! y : U ⪼ typ_rcd (dec_typ A S S) ->
  (C, G) ⊢c##v v : typ_sel (avar_f y) A

(** [G ⊢##v v : T]        #<br>#
    [G ⊢##v v : U]        #<br>#
    [―――――――――――――]        #<br>#
    [G ⊢##v v : T /\ U]        *)
| cty_and_inv_v : forall C G v T U,
  (C, G) ⊢c##v v : T ->
  (C, G) ⊢c##v v : U ->
  (C, G) ⊢c##v v : typ_and T U

(** [G ⊢##v v: T]   #<br>#
    [――――――――――――――] #<br>#
    [G ⊢##v v: top]     *)
| cty_top_inv_v : forall C G v T,
  (C, G) ⊢c##v v : T ->
  (C, G) ⊢c##v v : typ_top
where "e '⊢c##v' v ':' T" := (cty_val_inv e v T).

Hint Constructors cty_var_inv cty_val_inv.

(** ** Equivelence theorems *)

Lemma extended_constr_tight_satisfy : forall tm vm G C x T T',
    (* TODO change to correspond *)
    T ⩭ T' ->
    (tm, vm, G) ⊧# C ->
    binds x T' G ->
    (tm, vm, G) ⊧# C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ T.
Proof.
  introv Hiso Hsat Hx.
  eapply sat_and_t; auto. apply sat_typ_t with (trm_var (avar_f x)) T'.
  apply map_ctrm_cvar. constructor.
  apply map_iso_ctyp; auto. eauto.
Qed.

Lemma extended_constr_tight_satisfiable : forall G C x T T',
    T ⩭ T' ->
    G ⊨# C ->
    binds x T' G ->
    G ⊨# C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ T.
Proof.
  introv Hiso Hsat Hx.
  destruct Hsat as [tm [vm Hsat]].
  exists tm, vm. apply* extended_constr_tight_satisfy.
Qed.

Lemma constr_to_tight_subtyping : forall C G T U,
    inert G ->
    G ⊨# C ->
    (C, G) ⊢c# T <: U ->
    G ⊢# T <: U.
Proof.
  introv Hi Hsat Hsub. destruct Hsat as [tm [vm Hsat]].
  dependent induction Hsub.
  - specialize (IHHsub G Hi (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S)).
    apply~ IHHsub. apply* extended_constr_tight_satisfy.
  - assert (Hsat2 : (tm, vm, G) ⊧# S <⦂ T) by eauto.
    inversion Hsat2; subst.
    assert (Heqs : S' = S'0) by apply* map_iso_ctyp_eq.
    assert (Heqt : T' = T'0) by apply* map_iso_ctyp_eq.
    subst. assumption.
Qed.

Lemma general_ent_intro_and : forall C1 C2 D,
    C1 ⊩ C2 ->
    C1 ⋏ D ⊩ C2 ⋏ D.
Proof.
  introv He. introe.
  inversion H; subst. eauto.
Qed.

Lemma tight_ent_intro_and : forall C1 C2 D,
    C1 ⊩# C2 ->
    C1 ⋏ D ⊩# C2 ⋏ D.
Proof.
  introv He. introe.
  inversion H; subst. eauto.
Qed.

Lemma tight_ent_trans : forall C1 C2 C3,
    C1 ⊩# C2 ->
    C2 ⊩# C3 ->
    C1 ⊩# C3.
Proof.
  introv He1 He2. introe. eauto.
Qed.

Lemma strengthen_constr_general_typing : forall C1 C2 G t T,
  C1 ⊩ C2 ->
  (C2, G) ⊢c t : T ->
  (C1, G) ⊢c t : T
with strengthen_constr_general_typing_def : forall C1 C2 G d D,
  C1 ⊩ C2 ->
  (C2, G) /-c d : D ->
  (C1, G) /-c d : D
with strengthen_constr_general_typing_defs : forall C1 C2 G ds D,
  C1 ⊩ C2 ->
  (C2, G) /-c ds :: D ->
  (C1, G) /-c ds :: D
with strengthen_constr_general_subtyping : forall C1 C2 G T U,
  C1 ⊩ C2 ->
  (C2, G) ⊢c T <: U ->
  (C1, G) ⊢c T <: U.
Proof.
  all: introv He Ht.
  - gen C1. dependent induction Ht; introv He.
    -- constructor. assumption.
    -- pick_fresh x.
       apply cty_all_intro with L. introv Hne0.
       apply* H0.
    -- apply* cty_all_elim.
    -- apply cty_new_intro with L.
       introv Hn. specialize (H x Hn). apply* strengthen_constr_general_typing_defs.
    -- apply cty_new_elim. apply* IHHt.
    -- apply cty_let with L T. apply* IHHt.
       introv Hne. specialize (H0 x Hne). apply* H0.
    -- apply cty_rec_intro. apply* IHHt.
    -- apply cty_rec_elim. apply* IHHt.
    -- apply cty_and_intro; try apply* IHHt1; try apply* IHHt2.
    -- apply cty_sub with T. apply* IHHt. apply* strengthen_constr_general_subtyping.
  - gen C1. dependent induction Ht; introv He.
    -- constructor.
    -- constructor. apply* strengthen_constr_general_typing.
  - gen C1. dependent induction Ht; introv He.
    -- constructor. apply* strengthen_constr_general_typing_def.
    -- constructor. apply* IHHt. apply* strengthen_constr_general_typing_def.
       exact H0.
  - gen C1. dependent induction Ht; introv He.
    -- apply csubtyp_intro with x S S'; try assumption.
       apply* IHHt. apply* general_ent_intro_and.
    -- apply* csubtyp_inst. apply* ent_trans.
Qed.

Lemma strengthen_constr_tight_typing : forall C1 C2 G t T,
  C1 ⊩# C2 ->
  (C2, G) ⊢c# t : T ->
  (C1, G) ⊢c# t : T
with strengthen_constr_tight_subtyping : forall C1 C2 G T U,
  C1 ⊩# C2 ->
  (C2, G) ⊢c# T <: U ->
  (C1, G) ⊢c# T <: U.
Proof.
  all: introv He Ht.
  - gen C1. dependent induction Ht; introv He.
    -- constructor. assumption.
    -- pick_fresh x.
       apply cty_all_intro_t with L. introv Hne0.
       specialize (H x0 Hne0).
       eapply strengthen_constr_general_typing.
       apply tight_to_general_entailment in He.
       exact He. exact H.
    -- apply* cty_all_elim_t.
    -- apply cty_new_intro_t with L.
       introv Hn. specialize (H x Hn). apply* strengthen_constr_general_typing_defs.
       apply* tight_to_general_entailment.
    -- apply cty_new_elim_t. apply* IHHt.
    -- apply cty_let_t with L T. apply* IHHt.
       introv Hne. specialize (H x Hne).
       apply* strengthen_constr_general_typing.
       apply* tight_to_general_entailment.
    -- apply cty_rec_intro_t. apply* IHHt.
    -- apply cty_rec_elim_t. apply* IHHt.
    -- apply cty_and_intro_t; try apply* IHHt1; try apply* IHHt2.
    -- apply cty_sub_t with T. apply* IHHt. apply* strengthen_constr_tight_subtyping.
  - gen C1. dependent induction Ht; introv He.
    -- apply csubtyp_intro_t with x S S'; try assumption.
       apply* IHHt. apply* tight_ent_intro_and.
    -- apply* csubtyp_inst_t. apply* tight_ent_trans.
Qed.

Lemma strengthen_constr_invertible : forall C1 C2 G x U,
    C1 ⊩# C2 ->
    (C2, G) ⊢c## x : U ->
    (C1, G) ⊢c## x : U.
Proof.
  introv He Ht2.
  dependent induction Ht2; eauto.
  - apply cty_dec_trm_inv with T. apply* IHHt2.
    apply* strengthen_constr_tight_subtyping.
  - apply cty_dec_typ_inv with T1 U1;
      try apply* strengthen_constr_tight_subtyping.
    apply* IHHt2.
  - apply cty_all_inv with L S T.
    apply* IHHt2.
    apply* strengthen_constr_tight_subtyping.
    introv Hne. specialize (H0 y Hne). apply* strengthen_constr_general_subtyping.
    apply* tight_to_general_entailment.
Qed.

Theorem tight_ent_and_elim1 : forall C D,
    C ⋏ D ⊩# C.
Proof.
  introe. inversion H; subst. assumption.
Qed.

Theorem weaken_constr_tight_subtyping : forall x S S' C G T U,
    S ⩭ S' ->
    binds x S' G ->
    (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S, G) ⊢c# T <: U ->
    (C, G) ⊢c# T <: U.
Proof.
  introv Hiso Hx HT.
  eapply csubtyp_intro_t. exact Hiso. exact Hx. exact HT.
Qed.

Theorem weaken_constr_invertible_typing : forall x S S' C G y T,
    S ⩭ S' ->
    binds x S' G ->
    (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S, G) ⊢c## y : T ->
    (C, G) ⊢c## y : T.
Proof.
  introv Hiso Hb HT.
  dependent induction HT; eauto.
  specialize (IHHT x S C G Hiso Hb JMeq_refl).
  apply cty_all_inv with (L \u \{x}) S0 T; eauto.
Qed.

Theorem weaken_constr_subtyping : forall x S S' C G T U,
    S ⩭ S' ->
    binds x S' G ->
    (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S, G) ⊢c T <: U ->
    (C, G) ⊢c T <: U.
Proof.
  introv Hiso Hx HT.
  eapply csubtyp_intro. exact Hiso. exact Hx. exact HT.
Qed.

Theorem weaken_constr_general_typing : forall x S S' C G t T,
    S ⩭ S' ->
    binds x S' G ->
    (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S, G) ⊢c t : T ->
    (C, G) ⊢c t : T
with weaken_constr_general_typing_def : forall x S S' C G d D,
    S ⩭ S' ->
    binds x S' G ->
    (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S, G) /-c d : D ->
    (C, G) /-c d : D
with weaken_constr_general_typing_defs : forall x S S' C G ds D,
    S ⩭ S' ->
    binds x S' G ->
    (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S, G) /-c ds :: D ->
    (C, G) /-c ds :: D.
Proof.
  all: introv Hiso Hb HT.
  - dependent induction HT.
    -- constructor. exact H.
    -- apply cty_all_intro with (L \u \{x}). eauto.
    -- apply cty_all_elim with S0. apply* IHHT1.
       apply* IHHT2.
    -- apply cty_new_intro with (L \u \{x}). intros y Hne.
       eapply weaken_constr_general_typing_defs.
       apply Hiso.
       assert (Hb' : binds x S' (G & y ~ open_typ y T)) by eauto.
       exact Hb'. apply~ H.
    -- apply cty_new_elim. apply* IHHT.
    -- apply cty_let with (L \u \{x}) T. apply* IHHT. intros y Hne.
       apply~ H0. exact Hiso. eauto.
    -- apply cty_rec_intro. apply* IHHT.
    -- apply cty_rec_elim. apply* IHHT.
    -- apply cty_and_intro. apply* IHHT1. apply* IHHT2.
    -- apply cty_sub with T. apply* IHHT. eapply weaken_constr_subtyping.
       apply Hiso. apply Hb. apply H.
  - dependent induction HT.
    -- apply cty_def_typ.
    -- apply cty_def_trm. eapply weaken_constr_general_typing.
       exact Hiso. exact Hb. exact H.
  - dependent induction HT.
    -- apply cty_defs_one. eapply weaken_constr_general_typing_def.
       exact Hiso. exact Hb. exact H.
    -- apply cty_defs_cons. apply* IHHT. eapply weaken_constr_general_typing_def; eassumption.
       exact H0.
Qed.

Ltac csubtyp_t_to_ent :=
  match goal with
  | |- (?E, _) ⊢c# ?T <: ?U =>
    idtac E; idtac T; idtac U;
    destruct (iso_ctyp_exists T) as [?Tc ?HTc];
    destruct (iso_ctyp_exists U) as [?Uc ?HUc];
    apply* csubtyp_inst_t
  end.

Ltac solve_trivial_csubtyp_t :=
  match goal with
  | |- _ ⊩# ?S <: ?T => introe; eapply sat_sub_t
  end.

Lemma tight_constr_subtyping_trans_aux : forall C G S S' T T' U,
    S ⩭ S' ->
    T ⩭ T' ->
    C ⊩# S <⦂ T ->
    (C, G) ⊢c# T' <: U ->
    (C, G) ⊢c# S' <: U.
Proof.
  introv Hs Ht Hst Htu.
  dependent induction Htu.
  - eapply weaken_constr_tight_subtyping.
    apply H. eassumption.
    apply~ IHHtu.
    eapply tight_ent_trans.
    apply tight_ent_and_elim1. assumption.
  - specialize (iso_ctyp_unique H Ht) as Heq; subst.
    apply~ csubtyp_inst_t; try eassumption.
    introe_t. econstructor. apply map_iso_ctyp. eassumption.
    apply map_iso_ctyp. eassumption.
    apply H1 in He as He1; try assumption.
    apply Hst in He as He2; try assumption.
    inversion He1; subst. inversion He2; subst.
    pose proof (map_ctyp_unique_typ H6 H11). subst.
    pose proof (map_iso_ctyp tm vm Hs) as Hms.
    pose proof (map_iso_ctyp tm vm Ht) as Hmt.
    pose proof (map_iso_ctyp tm vm H0) as Hm0.
    pose proof (map_ctyp_unique_typ H7 Hms). subst.
    pose proof (map_ctyp_unique_typ H11 Hmt). subst.
    pose proof (map_ctyp_unique_typ H8 Hm0). subst.
    eauto.
Qed.

Lemma tight_constr_subtyping_trans : forall C G S T U,
    (C, G) ⊢c# S <: T ->
    (C, G) ⊢c# T <: U ->
    (C, G) ⊢c# S <: U.
Proof.
  introv Hst Htu.
  dependent induction Hst.
  - specialize (IHHst _ _ eq_refl).
    eapply weaken_constr_tight_subtyping. exact H. exact H0.
    apply IHHst. eapply strengthen_constr_tight_subtyping.
    apply tight_ent_and_elim1. exact Htu.
  - eapply tight_constr_subtyping_trans_aux; eassumption.
Qed.

Theorem tight_to_constr_subtyping : forall C G T U,
    G ⊢# T <: U ->
    (C, G) ⊢c# T <: U.
Proof.
Admitted.

Theorem general_to_constr_subtyping : forall C G T U,
    ok G ->
    G ⊢ T <: U ->
    (C, G) ⊢c T <: U.
Proof.
  introv Hok HTU.
  destruct (min_complete_exists G) as [rG Hr].
  destruct (iso_ctyp_exists T) as [t Ht].
  destruct (iso_ctyp_exists U) as [u Hu].
  eapply ent_imply_subtyp. assumption.
  exact Hr. exact Ht. exact Hu.
  eapply ent_trans. apply ent_and_right.
  eapply min_complete_entails_sub.
  exact Hr. exact Ht. exact Hu. exact HTU.
Qed.

Lemma constr_subtyping_trans : forall C G S T U,
    (C, G) ⊢c S <: T ->
    (C, G) ⊢c T <: U ->
    (C, G) ⊢c S <: U.
Admitted.

Theorem invertible_constr_typing_closure_tight_aux : forall C G x T U,
    inert G ->
    ok G ->
    (C, G) ⊢c## x : T ->
    G ⊢# T <: U ->
    (C, G) ⊢c## x : U.
Proof.
  introv Hi Hok HT Hsub.
  dependent induction Hsub; eauto using tight_to_constr_subtyping.
  - inversion HT; subst.
    destruct (pf_bot_false Hi H3).
  - inversion HT; subst; auto. apply pf_and1 in H3. apply* cty_precise_inv.
  - inversion HT; subst; auto. apply pf_and2 in H3. apply* cty_precise_inv.
  - inversions HT.
    + false* pf_psel_false.
    + lets Hu: (x_bound_unique H H6). subst.
      pose proof (pf_inert_unique_tight_bounds Hi H H6) as Hu. subst. assumption.
  - apply cty_all_inv with (L \u dom G) S1 T1; eauto.
    apply* tight_to_constr_subtyping.
    introv Hn. assert (HnL : y \notin L) by eauto. specialize (H y HnL).
    apply* general_to_constr_subtyping.
Qed.

Theorem invertible_constr_typing_closure_tight : forall C G x T U,
    inert G ->
    G ⊨# C ->
    (C, G) ⊢c## x : T ->
    (C, G) ⊢c# T <: U ->
    (C, G) ⊢c## x : U.
Proof.
  introv Hi Hs HT Hsub.
  dependent induction Hsub; eauto.
  - specialize (IHHsub G Hi (C ⋏ ctrm_cvar (cvar_x (avar_f x0)) ⦂ S)).
    assert (Hs' : G ⊨# C ⋏ ctrm_cvar (cvar_x (avar_f x0)) ⦂ S) by apply* extended_constr_tight_satisfiable.
    assert (Hent : C ⋏ ctrm_cvar (cvar_x (avar_f x0)) ⦂ S ⊩# C) by apply tight_ent_and_elim1.
    assert (HT' : (C ⋏ ctrm_cvar (cvar_x (avar_f x0)) ⦂ S, G) ⊢c## x : T) by apply* strengthen_constr_invertible.
    specialize (IHHsub Hs' HT' eq_refl).
    eapply weaken_constr_invertible_typing.
    exact H. exact H0. exact IHHsub.
  - assert (Hsub : G ⊢# S' <: T') by apply* constr_to_tight_subtyping.
    apply* invertible_constr_typing_closure_tight_aux.
Qed.

(** ** Tight to invertible theorem: |-c# to |-c## *)
Theorem tight_to_invertible_constr_typing : forall C G U x,
    inert G ->
    G ⊨# C ->
    (C, G) ⊢c# trm_var (avar_f x) : U ->
    (C, G) ⊢c## x : U.
Proof.
  introv Hi Hs Ht.
  dependent induction Ht; eauto.
  - specialize (IHHt x G Hi C Hs eq_refl eq_refl). inversion IHHt; subst; eauto.
  - specialize (IHHt x G Hi C Hs eq_refl eq_refl).
    apply* invertible_constr_typing_closure_tight.
Qed.

Lemma strengthen_constr_invertible_v : forall C1 C2 G v T,
    C1 ⊩# C2 ->
    (C2, G) ⊢c##v v : T ->
    (C1, G) ⊢c##v v : T.
Proof.
  introv He HT.
  dependent induction HT; eauto.
  - inversion H; subst; eauto.
    -- apply cty_precise_inv_v. apply cty_all_intro_p with L.
       introv Hne. apply* strengthen_constr_general_typing.
       apply* tight_to_general_entailment.
    -- apply cty_precise_inv_v. apply cty_new_intro_p with L.
       introv Hne. apply* strengthen_constr_general_typing_defs.
       apply* tight_to_general_entailment.
  - apply cty_all_inv_v with L S T.
    apply* IHHT.
    apply* strengthen_constr_tight_subtyping.
    introv Hne. apply* strengthen_constr_general_subtyping.
    apply* tight_to_general_entailment.
Qed.


Theorem weaken_constr_precise_typing : forall x S S' C G v T,
    S ⩭ S' ->
    binds x S' G ->
    (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S, G) ⊢c!v v : T ->
    (C, G) ⊢c!v v : T.
Proof.
  introv Hiso Hb HT.
  dependent induction HT.
  - apply cty_all_intro_p with (L \u \{x}). introv Hne.
    eapply weaken_constr_general_typing; eauto.
  - apply cty_new_intro_p with (L \u \{x}). intros y Hne.
    eapply weaken_constr_general_typing_defs; eauto.
Qed.

Theorem weaken_constr_invertible_typing_v : forall x S S' C G v T,
    S ⩭ S' ->
    binds x S' G ->
    (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S, G) ⊢c##v v : T ->
    (C, G) ⊢c##v v : T.
Proof.
  introv Hiso Hb HT.
  dependent induction HT; eauto.
  - inversion H; subst.
    -- apply cty_precise_inv_v.
       eapply weaken_constr_precise_typing. exact Hiso.
       exact Hb. assumption.
    -- apply cty_precise_inv_v.
       eapply weaken_constr_precise_typing. exact Hiso.
       exact Hb. assumption.
  -
  apply cty_all_inv_v with (L \u \{x}) S0 T; eauto.
Qed.

Theorem invertible_constr_typing_closure_tight_v_aux : forall C G v T U,
    inert G ->
    ok G ->
    (C, G) ⊢c##v v : T ->
    G ⊢# T <: U ->
    (C, G) ⊢c##v v : U.
Proof.
  introv Hi Hok HT Hsub.
  dependent induction Hsub; eauto.
  - inversions HT; subst.
    inversions H3.
  - inversion HT; subst; auto. inversion H3.
  - inversion HT; subst; auto. inversion H3.
  - inversions HT; subst. inversion H3.
  - inversions HT. inversions H3.
  - inversions HT.
    + inversions H4.
    + lets Hu: (x_bound_unique H H6). subst.
      pose proof (pf_inert_unique_tight_bounds Hi H H6) as Hu. subst. assumption.
  - apply cty_all_inv_v with (L \u dom G) S1 T1; eauto.
    apply* tight_to_constr_subtyping.
    introv Hn. assert (HnL: y \notin L) by eauto. specialize (H y HnL).
    apply* general_to_constr_subtyping.
Qed.

Theorem invertible_constr_typing_closure_tight_v : forall C G v T U,
    inert G ->
    G ⊨# C ->
    (C, G) ⊢c##v v : T ->
    (C, G) ⊢c# T <: U ->
    (C, G) ⊢c##v v : U.
Proof.
  introv Hi Hsat HT Hsub.
  dependent induction Hsub.
  - specialize (IHHsub G Hi (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S)).
    assert (Hsat' : G ⊨# C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S) by apply* extended_constr_tight_satisfiable.
    specialize (IHHsub Hsat').
    assert (HT' : (C ⋏ ctrm_cvar (cvar_x (avar_f x)) ⦂ S, G) ⊢c##v v : T). {
      apply* strengthen_constr_invertible_v.
      apply* tight_ent_and_elim1.
    }
    specialize (IHHsub HT' eq_refl).
    eapply weaken_constr_invertible_typing_v. exact H. exact H0. assumption.
  - apply* invertible_constr_typing_closure_tight_v_aux.
    apply* constr_to_tight_subtyping.
Qed.

Theorem tight_to_invertible_constr_typing_v : forall C G v T,
    inert G ->
    G ⊨# C ->
    (C, G) ⊢c# trm_val v : T ->
    (C, G) ⊢c##v v : T.
Proof.
  introv Hgd Hsat Hty.
  dependent induction Hty; eauto.
  specialize (IHHty v G Hgd C Hsat eq_refl eq_refl).
  apply* invertible_constr_typing_closure_tight_v.
Qed.

(** ** Invertible to Precise Typing [|-## to |-!] *)

(** Invertible-to-precise typing for field declarations: #<br>#
    [G ⊢## x: {a: T}]            #<br>#
    [――――――――――――――――――――――]      #<br>#
    [exists T', G ⊢! x: {a: T'}]      #<br>#
    [G ⊢# T' <: T]. *)
Lemma constr_invertible_to_precise_trm_dec : forall C G x a T,
    (C, G) ⊢c## x : typ_rcd (dec_trm a T) ->
    exists T' U,
      G ⊢! x : U ⪼ typ_rcd (dec_trm a T') /\
      (C, G) ⊢c# T' <: T.
Proof.
  introv Hinv.
  dependent induction Hinv.
  - exists T T0. split; auto 1.
    destruct (iso_ctyp_exists T).
    eapply csubtyp_inst_t; eauto. introv Hi Hok He.
    eapply sat_sub_t; try apply* map_iso_ctyp; eauto.
  - specialize (IHHinv _ _ _ _ eq_refl eq_refl).
    destruct IHHinv as [V [V' [Hx Hs]]].
    exists V V'. split; auto. apply* tight_constr_subtyping_trans.
Qed.

Lemma csubtyp_t_refl : forall C G T,
    (C, G) ⊢c# T <: T.
Proof.
  introv. destruct (iso_ctyp_exists T).
  eapply csubtyp_inst_t; eauto 1.
  introv Hi Hok He. eapply sat_sub_t; try apply* map_iso_ctyp; eauto.
Qed.

Lemma csubtyp_refl : forall C G T,
    (C, G) ⊢c T <: T.
Proof.
  introv. destruct (iso_ctyp_exists T).
  eapply csubtyp_inst; eauto 1.
  introv Hi Hok He. eapply sat_sub; try apply* map_iso_ctyp; eauto.
Qed.

Lemma csubtyp_all_t: forall L C G S1 T1 S2 T2,
    (C, G) ⊢c# S2 <: S1 ->
    (forall x, x \notin L ->
       (C, G & x ~ S2) ⊢c open_typ x T1 <: open_typ x T2) ->
    (C, G) ⊢c# typ_all S1 T1 <: typ_all S2 T2.
Admitted.

(** Invertible-to-precise typing for function types: #<br>#
    [ok G]                        #<br>#
    [G ⊢## x: forall(S)T]             #<br>#
    [――――――――――――――――――――――――――]  #<br>#
    [exists S', T'. G ⊢! x: forall(S')T']  #<br>#
    [G ⊢# S <: S']               #<br>#
    [G ⊢# T'^y <: T^y], where [y] is fresh. *)
Lemma constr_invertible_to_precise_typ_all: forall C G x S T,
  ok G ->
  (C, G) ⊢c## x : typ_all S T ->
  exists S' T' U L,
    G ⊢! x : U ⪼ typ_all S' T' /\
    (C, G) ⊢c# S <: S' /\
    (forall y,
        y \notin L ->
            (C, G & y ~ S) ⊢c open_typ y T' <: open_typ y T).
Proof.
  introv HG Hinv.
  dependent induction Hinv.
  - exists S T T0 (dom G). split; try split; eauto 2 using csubtyp_t_refl, csubtyp_refl.
  - specialize (IHHinv _ _ _ HG _ JMeq_refl eq_refl).
    destruct IHHinv as [S' [T' [V' [L' [Hpt [HSsub HTsub]]]]]].
    exists S' T' V' (dom G \u L \u L').
    split; eauto.
    assert (Hsub2 : (C, G) ⊢c# typ_all S0 T0 <: typ_all S T).
    { apply csubtyp_all_t with L; assumption. }
    split.
    + eapply tight_constr_subtyping_trans; eauto.
    + intros y Fr.
      assert (Hok: ok (G & y ~ S)) by auto using ok_push.
      apply tight_to_general_constr_typing in H; auto.
      assert (Hnarrow: (C, G & y ~ S) ⊢c open_typ y T' <: open_typ y T0).
      { eapply narrow_constr_subtyping; auto using subenv_last. }
      eapply constr_subtyping_trans. apply Hnarrow.
      apply* H0.
Qed.

(** [G ⊢##v v: forall(S)T]                 #<br>#
    [inert G]                          #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [exists S', T', G ⊢! v: forall(S')T']      #<br>#
    [G ⊢ S <: S']                      #<br>#
    [forall fresh y, G, y: S ⊢ T'^y <: T^y] *)
Lemma constr_invertible_val_to_precise_lambda: forall C G v S T,
    inert G ->
    (C, G) ⊢c##v v : typ_all S T ->
    exists L S' T',
      (C, G) ⊢c!v v : typ_all S' T' /\
      (C, G) ⊢c S <: S' /\
      (forall y, y \notin L ->
                 (C, G & y ~ S) ⊢c open_typ y T' <: open_typ y T).
Proof.
  introv Hi Ht. dependent induction Ht.
  - exists (dom G) S T. split; eauto using csubtyp_refl.
  - destruct (IHHt _ _ _ Hi _ eq_refl eq_refl) as [L' [S1 [T1 [Hp [Hss Hst]]]]].
    exists (L \u L' \u dom G) S1 T1. split. assumption. split. apply constr_subtyping_trans with (T:=S0).
    apply* tight_to_general_constr_typing. assumption. intros.
    assert (ok (G & y ~ S)) as Hok. {
      apply* ok_push.
    }
    apply constr_subtyping_trans with (T:=open_typ y T0).
    eapply narrow_constr_subtyping. apply* Hst. apply csubenv_last. apply* tight_to_general_constr_typing.
    assumption.
    apply* H0.
Qed.
