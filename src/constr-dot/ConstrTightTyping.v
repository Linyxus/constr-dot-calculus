(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import ConstrLang Definitions Subenvironments RecordAndInertTypes ConstrTyping.

(** * Constraint Satisfactory based on Tight Subtyping *)

(** * Tight Typing Rules with Constraints *)

Reserved Notation "C ',' G '⊢c#' t ':' T" (at level 39, t at level 59).

(** ** Term typing [G ⊢c# t: T] *)
Inductive cty_trm_t : constr -> ctx -> trm -> typ -> Prop :=

(** [G(x) = T]  #<br>#
    [――――――――]  #<br>#
    [C, G ⊢c x: T]  *)
| ty_var : forall C G x T,
    binds x T G ->
    C, G ⊢c# trm_var (avar_f x) : T

(** [C, (G, x: T) ⊢c t^x: U^x]     #<br>#
    [x fresh]                #<br>#
    [――――――――――――――――――――――] #<br>#
    [C, G ⊢c lambda(T)t: forall(T)U]      *)
| ty_all_intro : forall L C G T t U,
    (forall x, x \notin L ->
      C, G & x ~ T ⊢c open_trm x t : open_typ x U) ->
    C, G ⊢c# trm_val (val_lambda T t) : typ_all T U

(** [C, G ⊢c x: forall(S)T] #<br>#
    [C, G ⊢c z: S]     #<br>#
    [――――――――――――] #<br>#
    [C, G ⊢c x z: T^z]     *)
| ty_all_elim : forall C G x z S T,
    C, G ⊢c# trm_var (avar_f x) : typ_all S T ->
    C, G ⊢c# trm_var (avar_f z) : S ->
    C, G ⊢c# trm_app (avar_f x) (avar_f z) : open_typ z T

(** [C, (G, x: T^x) ⊢ ds^x :: T^x]  #<br>#
    [x fresh]                  #<br>#
    [―――――――――――――――――――――――]  #<br>#
    [C, G ⊢ nu(T)ds :: mu(T)]          *)
| ty_new_intro : forall L C G T ds,
    (forall x, x \notin L ->
      C, G & (x ~ open_typ x T) /-c open_defs x ds :: open_typ x T) ->
    C, G ⊢c# trm_val (val_new T ds) : typ_bnd T

(** [C, G ⊢c x: {a: T}] #<br>#
    [―――――――――――――] #<br>#
    [C, G ⊢c x.a: T]        *)
| ty_new_elim : forall C G x a T,
    C, G ⊢c# trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
    C, G ⊢c# trm_sel (avar_f x) a : T

(** [C, G ⊢c t: T]          #<br>#
    [C, G, x: T ⊢c u^x: U]  #<br>#
    [x fresh]           #<br>#
    [―――――――――――――――――] #<br>#
    [C, G ⊢c let t in u: U]     *)
| ty_let : forall L C G t u T U,
    C, G ⊢c# t : T ->
    (forall x, x \notin L ->
      C, G & x ~ T ⊢c open_trm x u : U) ->
    C, G ⊢c# trm_let t u : U

(** [C, G ⊢c x: T^x]   #<br>#
    [――――――――――――] #<br>#
    [C, G ⊢c x: mu(T)]     *)
| ty_rec_intro : forall C G x T,
    C, G ⊢c# trm_var (avar_f x) : open_typ x T ->
    C, G ⊢c# trm_var (avar_f x) : typ_bnd T

(** [C, G ⊢c x: mu(T)] #<br>#
    [――――――――――――] #<br>#
    [C, G ⊢c x: T^x]   *)
| ty_rec_elim : forall C G x T,
    C, G ⊢c# trm_var (avar_f x) : typ_bnd T ->
    C, G ⊢c# trm_var (avar_f x) : open_typ x T

(** [C, G ⊢c x: T]     #<br>#
    [C, G ⊢c x: U]     #<br>#
    [――――――――――――] #<br>#
    [C, G ⊢c x: T /\ U]     *)
| ty_and_intro : forall C G x T U,
    C, G ⊢c# trm_var (avar_f x) : T ->
    C, G ⊢c# trm_var (avar_f x) : U ->
    C, G ⊢c# trm_var (avar_f x) : typ_and T U

(** [C, G ⊢c t: T]   #<br>#
    [C ⊩ S <: T] #<br>#
    [――――――――――] #<br>#
    [C, G ⊢c t: U]   *)
| ty_sub : forall C G t T U,
    C, G ⊢c# t : T ->
    C ⊩ ctyp_typ T <⦂ ctyp_typ U ->
    C, G ⊢c# t : U

(** [C, G ⊢c t: T]   #<br>#
    [C ⋏ t: T, G ⊢c u: U] #<br>#
    [――――――――――] #<br>#
    [C, G ⊢c u: U]   *)
| ty_constr_intro : forall C G t u T U,
    C, G ⊢c# t : T ->
    (C ⋏ t ⦂ T), G ⊢c# u : U ->
    C, G ⊢c# u : U
where "C ',' G '⊢c#' t ':' T" := (cty_trm_t C G t T).
