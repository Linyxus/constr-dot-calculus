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
Require Import ConstrLangAlt ConstrTyping TightConstrTyping PreciseConstrTyping.
Require Import TightConstrEntailment ConstrEntailment.

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
       apply* strengthen_constr_general_typing.
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
       apply* strengthen_constr_tight_typing.
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

Theorem invertible_constr_typing_closure_tight : forall C G x T U,
    inert G ->
    (C, G) ⊢c## x : T ->
    (C, G) ⊢c# T <: U ->
    (C, G) ⊢c## x : U.
Proof.
  introv Hi HT Hsub.
  dependent induction Hsub; eauto.
  - specialize (IHHsub G Hi (C ⋏ ctrm_cvar (cvar_x x0) ⦂ S)).

Theorem tight_to_invertible_constr_typing : forall C G U x,
    inert G ->
    (C, G) ⊢c# trm_var (avar_f x) : U ->
    (C, G) ⊢c## x : U.
Proof.
  introv Hi Ht.
  dependent induction Ht; eauto.
  - specialize (IHHt x G Hi C eq_refl eq_refl). inversion IHHt; subst; eauto.
  - 

