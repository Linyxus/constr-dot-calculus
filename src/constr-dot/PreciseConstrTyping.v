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

(** The precise type of a value is inert. *)
Lemma constr_precise_inert_typ : forall C G v T,
    (C, G) ⊢c!v v : T ->
    inert_typ T.
Proof.
  introv Ht. inversions Ht; constructor; rename T0 into T.
  constr_pick_fresh z. assert (Hz: z \notin L) by auto.
  match goal with
  | [H: forall x, _ \notin _ -> _,
     Hz: ?z \notin _ |- _] =>
    specialize (H z Hz);
      pose proof (cty_defs_record_type H);
      assert (Hz': z \notin fv_typ T) by auto;
      apply* record_type_open
  end.
Qed.

Lemma constr_precise_to_general_v: forall C G v T,
    (C, G) ⊢c!v v : T ->
    (C, G) ⊢c trm_val v: T.
Proof.
  intros. induction H; intros; subst; eauto.
Qed.
