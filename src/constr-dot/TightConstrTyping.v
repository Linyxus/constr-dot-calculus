(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import ConstrLangAlt Definitions Subenvironments RecordAndInertTypes ConstrTyping.
Require Import TightConstrEntailment.

Require Import Coq.Program.Equality.

(** * Constraint Satisfactory based on Tight Subtyping *)

(** * Tight Typing Rules with Constraints *)

Reserved Notation "e '⊢c#' t ':' T" (at level 39, t at level 59).
Reserved Notation "e '⊢c#' T '<:' U" (at level 39, T at level 59).

(** ** Term typing [G ⊢c# t: T] *)
Inductive cty_trm_t : (constr * ctx) -> trm -> typ -> Prop :=

(** [G(x) = T]  #<br>#
    [――――――――]  #<br>#
    [C, G ⊢c x: T]  *)
| cty_var_t : forall C G x T,
    binds x T G ->
    (C, G) ⊢c# trm_var (avar_f x) : T

(** [C, (G, x: T) ⊢c t^x: U^x]     #<br>#
    [x fresh]                #<br>#
    [――――――――――――――――――――――] #<br>#
    [C, G ⊢c lambda(T)t: forall(T)U]      *)
| cty_all_intro_t : forall L C G T t U,
    (forall x, x \notin L ->
      (C, G & x ~ T) ⊢c open_trm x t : open_typ x U) ->
    (C, G) ⊢c# trm_val (val_lambda T t) : typ_all T U

(** [C, G ⊢c x: forall(S)T] #<br>#
    [C, G ⊢c z: S]     #<br>#
    [――――――――――――] #<br>#
    [C, G ⊢c x z: T^z]     *)
| cty_all_elim_t : forall C G x z S T,
    (C, G) ⊢c# trm_var (avar_f x) : typ_all S T ->
    (C, G) ⊢c# trm_var (avar_f z) : S ->
    (C, G) ⊢c# trm_app (avar_f x) (avar_f z) : open_typ z T

(** [C, (G, x: T^x) ⊢ ds^x :: T^x]  #<br>#
    [x fresh]                  #<br>#
    [―――――――――――――――――――――――]  #<br>#
    [C, G ⊢ nu(T)ds :: mu(T)]          *)
| cty_new_intro_t : forall L C G T ds,
    (forall x, x \notin L ->
      (C, G & (x ~ open_typ x T)) /-c open_defs x ds :: open_typ x T) ->
    (C, G) ⊢c# trm_val (val_new T ds) : typ_bnd T

(** [C, G ⊢c x: {a: T}] #<br>#
    [―――――――――――――] #<br>#
    [C, G ⊢c x.a: T]        *)
| cty_new_elim_t : forall C G x a T,
    (C, G) ⊢c# trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
    (C, G) ⊢c# trm_sel (avar_f x) a : T

(** [C, G ⊢c t: T]          #<br>#
    [C, G, x: T ⊢c u^x: U]  #<br>#
    [x fresh]           #<br>#
    [―――――――――――――――――] #<br>#
    [C, G ⊢c let t in u: U]     *)
| cty_let_t : forall L C G t u T U,
    (C, G) ⊢c# t : T ->
    (forall x, x \notin L ->
      (C, G & x ~ T) ⊢c open_trm x u : U) ->
    (C, G) ⊢c# trm_let t u : U

(** [C, G ⊢c x: T^x]   #<br>#
    [――――――――――――] #<br>#
    [C, G ⊢c x: mu(T)]     *)
| cty_rec_intro_t : forall C G x T,
    (C, G) ⊢c# trm_var (avar_f x) : open_typ x T ->
    (C, G) ⊢c# trm_var (avar_f x) : typ_bnd T

(** [C, G ⊢c x: mu(T)] #<br>#
    [――――――――――――] #<br>#
    [C, G ⊢c x: T^x]   *)
| cty_rec_elim_t : forall C G x T,
    (C, G) ⊢c# trm_var (avar_f x) : typ_bnd T ->
    (C, G) ⊢c# trm_var (avar_f x) : open_typ x T

(** [C, G ⊢c x: T]     #<br>#
    [C, G ⊢c x: U]     #<br>#
    [――――――――――――] #<br>#
    [C, G ⊢c x: T /\ U]     *)
| cty_and_intro_t : forall C G x T U,
    (C, G) ⊢c# trm_var (avar_f x) : T ->
    (C, G) ⊢c# trm_var (avar_f x) : U ->
    (C, G) ⊢c# trm_var (avar_f x) : typ_and T U

(** [C, G ⊢c t: T]   #<br>#
    [C ⊩ S <: T] #<br>#
    [――――――――――] #<br>#
    [C, G ⊢c t: U]   *)
| cty_sub_t : forall C G t T U,
    (C, G) ⊢c# t : T ->
    (C, G) ⊢c# T <: U ->
    (C, G) ⊢c# t : U
where "e '⊢c#' t ':' T" := (cty_trm_t e t T)
with csubtyp_t : (constr * ctx) -> typ -> typ -> Prop :=
(** [C, G ⊢c x: S]   #<br>#
    [C ⋏ x: S, G ⊢c T <: U] #<br>#
    [――――――――――] #<br>#
    [C, G ⊢c T <: U]   *)
| csubtyp_intro_t : forall C G x S S' T U,
    S ⩭ S' ->
    (C, G) ⊢c# trm_var (avar_f x) : S' ->
    (C ⋏ ctrm_cvar (cvar_x x) ⦂ S, G) ⊢c# T <: U ->
    (C, G) ⊢c# T <: U
(** [C ⊩ T <: U]   #<br>#
    [――――――――――] #<br>#
    [C, G ⊢c T <: U]   *)
| csubtyp_inst_t : forall C G S S' T T',
    S ⩭ S' ->
    T ⩭ T' ->
    C ⊩# S <⦂ T ->
    (C, G) ⊢c# S' <: T'
where "e '⊢c#' T '<:' U" := (csubtyp_t e T U).

Hint Constructors cty_trm_t csubtyp_t.

Scheme cts_ty_trm_t_mut := Induction for cty_trm_t Sort Prop
with   cts_subtyp_t     := Induction for csubtyp_t Sort Prop.
Combined Scheme cts_t_mutind from cts_ty_trm_t_mut, cts_subtyp_t.

(** * Equivalence Theorems *)

(** Tight typing implies general typing. *)
Lemma tight_to_general_constr_typing:
  (forall e t T,
     e ⊢c# t : T ->
     e ⊢c t : T) /\
  (forall e S U,
     e ⊢c# S <: U ->
     e ⊢c S <: U).
Proof.
  apply cts_t_mutind; intros; subst; eauto using tight_to_general_entailment.
Qed.

Theorem general_to_tight_constr_typing :
  (forall e t T,
     e ⊢c t : T ->
     e ⊢c# t : T) /\
  (forall e S U,
     e ⊢c S <: U ->
     e ⊢c# S <: U).
Proof.
  apply cts_mutind; intros; subst; eauto using general_to_tight_entailment.
Qed.
