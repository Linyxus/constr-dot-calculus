(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module reasons about the precise types of variables in inert contexts. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import Definitions RecordAndInertTypes ConstrLangAlt ConstrTyping.
Require Import PreciseTyping.

Require Export PreciseTyping.

(** * Precise Typing for Constraints

    This is a replicate of original precise typing for the constraint-based type system.

    The precise flow relation defined for the original system
    simply retrieves type assignments from the environment.
    So we simply reuse the existing definition for the constraint-based system.
 *)

(** ** Precise typing for values *)
Reserved Notation "e '⊢c!v' v ':' T" (at level 40, v at level 59).

Inductive cty_val_p : (constr * ctx) -> val -> typ -> Prop :=

(** [G, x: T ⊢ t^x: U^x]       #<br>#
    [x fresh]                  #<br>#
    [――――――――――――――――――――――――] #<br>#
    [G ⊢! lambda(T)t: forall(T) U]     *)
| cty_all_intro_p : forall L C G T t U,
    (forall x, x \notin L ->
      (C, G & x ~ T) ⊢c open_trm x t : open_typ x U) ->
    (C, G) ⊢c!v val_lambda T t : typ_all T U

(** [G, x: T^x ⊢ ds^x :: T^x]   #<br>#
    [x fresh]                   #<br>#
    [―――――――――――――――――――――――]   #<br>#
    [G ⊢! nu(T)ds :: mu(T)]        *)
| cty_new_intro_p : forall L C G T ds,
    (forall x, x \notin L ->
      (C, G & (x ~ open_typ x T)) /-c open_defs x ds :: open_typ x T) ->
    (C, G) ⊢c!v val_new T ds : typ_bnd T

where "e '⊢c!v' v ':' T" := (cty_val_p e v T).

Hint Constructors cty_val_p.
