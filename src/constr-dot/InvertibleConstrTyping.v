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
Require Import ConstrLangAlt TightConstrTyping PreciseConstrTyping.

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
| cty_dec_trm_inv : forall C G x a T U T' U',
  T ⩭ T' ->
  U ⩭ U' ->
  (C, G) ⊢c## x : typ_rcd (dec_trm a T) ->
  C ⊩# T <⦂ U ->
  (C, G) ⊢c## x : typ_rcd (dec_trm a U)

(** [G ⊢## x: {A: T..U}]   #<br>#
    [G ⊢# T' <: T]         #<br>#
    [G ⊢# U <: U']         #<br>#
    [―――――――――――――――――――――] #<br>#
    [G ⊢## x: {A: T'..U'}]     *)
| cty_dec_typ_inv : forall C G x A T1 T2 U1 U2 T1' T2' U1' U2',
  T1 ⩭ T1' ->
  T2 ⩭ T2' ->
  U1 ⩭ U1' ->
  U2 ⩭ U2' ->
  (C, G) ⊢c## x : typ_rcd (dec_typ A T1' U1') ->
  C ⊩# T2 <⦂ T1 ->
  C ⊩# U1 <⦂ U2 ->
  G ⊢c## x : typ_rcd (dec_typ A T2' U2')

(** [G ⊢## x: T^x]   #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢## x: mu(T)] *)
| ty_bnd_inv : forall C G x T,
  (C, G) ⊢c## x : open_typ x T ->
  (C, G) ⊢c## x : typ_bnd T

(** [G ⊢## x: forall(S)T]          #<br>#
    [G ⊢# S' <: S]            #<br>#
    [G, y: S' ⊢ T^y <: T'^y]   #<br>#
    [y fresh]                  #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G ⊢## x: forall(S')T']            *)
| ty_all_inv : forall L C G x S T S' T',
  G ⊢c## x : typ_all S T ->
  G ⊢# S' <: S ->
  (forall y, y \notin L ->
   G & y ~ S' ⊢ open_typ y T <: open_typ y T') ->
  G ⊢## x : typ_all S' T'

(** [G ⊢## x : T]     #<br>#
    [G ⊢## x : U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## x : T /\ U]      *)
| ty_and_inv : forall G x S1 S2,
  G ⊢## x : S1 ->
  G ⊢## x : S2 ->
  G ⊢## x : typ_and S1 S2

(** [G ⊢## x: S]        #<br>#
    [G ⊢! y: {A: S..S}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢## x: y.A           *)
| ty_sel_inv : forall G x y A S U,
  G ⊢## x : S ->
  G ⊢! y : U ⪼ typ_rcd (dec_typ A S S) ->
  G ⊢## x : typ_sel (avar_f y) A

(** [G ⊢## x: T]   #<br>#
    [―――――――――――――] #<br>#
    [G ⊢## x: top]     *)
| ty_top_inv : forall G x T,
  G ⊢## x : T ->
  G ⊢## x : typ_top
where "G '⊢##' x ':' T" := (ty_var_inv G x T).

(** ** Invertible typing for values [G ⊢c##v v: T] *)

Reserved Notation "G '⊢c##v' v ':' T" (at level 40, v at level 59).

Inductive ty_val_inv : ctx -> val -> typ -> Prop :=

(** [G ⊢! v: T]    #<br>#
    [―――――――――――――] #<br>#
    [G ⊢##v v: T] *)
| ty_precise_inv_v : forall G v T,
  G ⊢!v v : T ->
  G ⊢##v v : T

(** [G ⊢##v v: forall(S)T]          #<br>#
    [G ⊢# S' <: S]             #<br>#
    [G, y: S' ⊢ T^y <: T'^y]    #<br>#
    [y fresh]                   #<br>#
    [――――――――――――――――――――――]    #<br>#
    [G ⊢##v v: forall(S')T']            *)
| ty_all_inv_v : forall L G v S T S' T',
  G ⊢##v v : typ_all S T ->
  G ⊢# S' <: S ->
  (forall y, y \notin L ->
   G & y ~ S' ⊢ open_typ y T <: open_typ y T') ->
  G ⊢##v v : typ_all S' T'

(** [G ⊢##v v: S]       #<br>#
    [G ⊢! y: {A: S..S}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢##v v: y.A]         *)
| ty_sel_inv_v : forall G v y A S U,
  G ⊢##v v : S ->
  G ⊢! y : U ⪼ typ_rcd (dec_typ A S S) ->
  G ⊢##v v : typ_sel (avar_f y) A

(** [G ⊢##v v : T]        #<br>#
    [G ⊢##v v : U]        #<br>#
    [―――――――――――――]        #<br>#
    [G ⊢##v v : T /\ U]        *)
| ty_and_inv_v : forall G v T U,
  G ⊢##v v : T ->
  G ⊢##v v : U ->
  G ⊢##v v : typ_and T U

(** [G ⊢##v v: T]   #<br>#
    [――――――――――――――] #<br>#
    [G ⊢##v v: top]     *)
| ty_top_inv_v : forall G v T,
  G ⊢##v v : T ->
  G ⊢##v v : typ_top
where "G '⊢##v' v ':' T" := (ty_val_inv G v T).

Hint Constructors ty_var_inv ty_val_inv.
