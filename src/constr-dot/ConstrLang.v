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

Require Import Definitions.


Inductive ctyp : Set :=
  | ctyp_var : avar -> ctyp
  | ctyp_typ : typ -> ctyp.


Inductive constr : Set :=
| constr_true : constr
| constr_false : constr
| constr_and : constr -> constr -> constr
| constr_or : constr -> constr -> constr
| constr_exists_typ : constr -> constr
| constr_exists_var : constr -> constr
| constr_sub : ctyp -> ctyp -> constr
| constr_typ : avar -> ctyp -> constr
.


