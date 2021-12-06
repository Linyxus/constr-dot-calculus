(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import ConstrLangAlt ConstrInterp ConstrEntailment Definitions Subenvironments RecordAndInertTypes.

(** * Typing Rules *)

Reserved Notation "e '⊢c' t ':' T" (at level 39, t at level 59).
Reserved Notation "e '/-c' d : D" (at level 39, d at level 59).
Reserved Notation "e '/-c' ds :: D" (at level 39, ds at level 59).
Reserved Notation "e '⊢c' T '<:' U" (at level 39, T at level 59).

(** ** Term typing [G ⊢c t: T] *)
Inductive cty_trm : (constr * ctx) -> trm -> typ -> Prop :=

(** [G(x) = T]  #<br>#
    [――――――――]  #<br>#
    [C, G ⊢c x: T]  *)
| cty_var : forall C G x T,
    binds x T G ->
    (C, G) ⊢c trm_var (avar_f x) : T

(** [C, (G, x: T) ⊢c t^x: U^x]     #<br>#
    [x fresh]                #<br>#
    [――――――――――――――――――――――] #<br>#
    [C, G ⊢c lambda(T)t: forall(T)U]      *)
| cty_all_intro : forall L C G T t U,
    (forall x, x \notin L ->
      (C, G & x ~ T) ⊢c open_trm x t : open_typ x U) ->
    (C, G) ⊢c trm_val (val_lambda T t) : typ_all T U

(** [C, G ⊢c x: forall(S)T] #<br>#
    [C, G ⊢c z: S]     #<br>#
    [――――――――――――] #<br>#
    [C, G ⊢c x z: T^z]     *)
| cty_all_elim : forall C G x z S T,
    (C, G) ⊢c trm_var (avar_f x) : typ_all S T ->
    (C, G) ⊢c trm_var (avar_f z) : S ->
    (C, G) ⊢c trm_app (avar_f x) (avar_f z) : open_typ z T

(** [C, (G, x: T^x) ⊢ ds^x :: T^x]  #<br>#
    [x fresh]                  #<br>#
    [―――――――――――――――――――――――]  #<br>#
    [C, G ⊢ nu(T)ds :: mu(T)]          *)
| cty_new_intro : forall L C G T ds,
    (forall x, x \notin L ->
      (C, G & (x ~ open_typ x T)) /-c open_defs x ds :: open_typ x T) ->
    (C, G) ⊢c trm_val (val_new T ds) : typ_bnd T

(** [C, G ⊢c x: {a: T}] #<br>#
    [―――――――――――――] #<br>#
    [C, G ⊢c x.a: T]        *)
| cty_new_elim : forall C G x a T,
    (C, G) ⊢c trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
    (C, G) ⊢c trm_sel (avar_f x) a : T

(** [C, G ⊢c t: T]          #<br>#
    [C, G, x: T ⊢c u^x: U]  #<br>#
    [x fresh]           #<br>#
    [―――――――――――――――――] #<br>#
    [C, G ⊢c let t in u: U]     *)
| cty_let : forall L C G t u T U,
    (C, G) ⊢c t : T ->
    (forall x, x \notin L ->
      (C, G & x ~ T) ⊢c open_trm x u : U) ->
    (C, G) ⊢c trm_let t u : U

(** [C, G ⊢c x: T^x]   #<br>#
    [――――――――――――] #<br>#
    [C, G ⊢c x: mu(T)]     *)
| cty_rec_intro : forall C G x T,
    (C, G) ⊢c trm_var (avar_f x) : open_typ x T ->
    (C, G) ⊢c trm_var (avar_f x) : typ_bnd T

(** [C, G ⊢c x: mu(T)] #<br>#
    [――――――――――――] #<br>#
    [C, G ⊢c x: T^x]   *)
| cty_rec_elim : forall C G x T,
    (C, G) ⊢c trm_var (avar_f x) : typ_bnd T ->
    (C, G) ⊢c trm_var (avar_f x) : open_typ x T

(** [C, G ⊢c x: T]     #<br>#
    [C, G ⊢c x: U]     #<br>#
    [――――――――――――] #<br>#
    [C, G ⊢c x: T /\ U]     *)
| cty_and_intro : forall C G x T U,
    (C, G) ⊢c trm_var (avar_f x) : T ->
    (C, G) ⊢c trm_var (avar_f x) : U ->
    (C, G) ⊢c trm_var (avar_f x) : typ_and T U

(** [C, G ⊢c t: T]   #<br>#
    [C ⊩ S <: T] #<br>#
    [――――――――――] #<br>#
    [C, G ⊢c t: U]   *)
| cty_sub : forall C G t T U,
    (C, G) ⊢c t : T ->
    (C, G) ⊢c T <: U ->
    (C, G) ⊢c t : U
where "e '⊢c' t ':' T" := (cty_trm e t T)

(** ** Single-definition typing [G ⊢ d: D] *)
with cty_def : (constr * ctx) -> def -> dec -> Prop :=
(** [C, G ⊢c {A = T}: {A: T..T}]   *)
| cty_def_typ : forall C G A T,
    (C, G) /-c def_typ A T : dec_typ A T T

(** [C, G ⊢c t: T]            #<br>#
    [―――――――――――――――――――] #<br>#
    [C, G ⊢c {a = t}: {a: T}] *)
| cty_def_trm : forall C G a t T,
    (C, G) ⊢c t : T ->
    (C, G) /-c def_trm a t : dec_trm a T
where "e '/-c' d ':' D" := (cty_def e d D)

(** ** Multiple-definition typing [G ⊢ ds :: T] *)
with cty_defs : (constr * ctx) -> defs -> typ -> Prop :=
(** [C, G ⊢c d: D]              #<br>#
    [―――――――――――――――――――――] #<br>#
    [C, G ⊢c d ++ defs_nil : D] *)
| cty_defs_one : forall C G d D,
    (C, G) /-c d : D ->
    (C, G) /-c defs_cons defs_nil d :: typ_rcd D

(** [C, G ⊢c ds :: T]         #<br>#
    [C, G ⊢c d: D]            #<br>#
    [d \notin ds]         #<br>#
    [―――――――――――――――――――] #<br>#
    [C, G ⊢c ds ++ d : T /\ D] *)
| cty_defs_cons : forall C G ds d T D,
    (C, G) /-c ds :: T ->
    (C, G) /-c d : D ->
    defs_hasnt ds (label_of_def d) ->
    (C, G) /-c defs_cons ds d :: typ_and T (typ_rcd D)
where "e '/-c' ds '::' T" := (cty_defs e ds T)

with csubtyp : (constr * ctx) -> typ -> typ -> Prop :=
(** [C, G ⊢c x: S]   #<br>#
    [C ⋏ x: S, G ⊢c T <: U] #<br>#
    [――――――――――] #<br>#
    [C, G ⊢c T <: U]   *)
| csubtyp_intro : forall C G x S S' T U,
    S ⩭ S' ->
    (C, G) ⊢c trm_var (avar_f x) : S' ->
    (C ⋏ ctrm_cvar (cvar_x x) ⦂ S, G) ⊢c T <: U ->
    (C, G) ⊢c T <: U
(** [C ⊩ T <: U]   #<br>#
    [――――――――――] #<br>#
    [C, G ⊢c T <: U]   *)
| csubtyp_inst : forall C G S S' T T',
    S ⩭ S' ->
    T ⩭ T' ->
    C ⊩ S <⦂ T ->
    (C, G) ⊢c S' <: T'
where "e '⊢c' T '<:' U" := (csubtyp e T U).

Hint Constructors cty_trm cty_def cty_defs csubtyp.

Scheme cts_ty_trm_mut := Induction for cty_trm Sort Prop
with   cts_subtyp     := Induction for csubtyp Sort Prop.
Combined Scheme cts_mutind from cts_ty_trm_mut, cts_subtyp.

Scheme crules_trm_mut    := Induction for cty_trm Sort Prop
with   crules_def_mut    := Induction for cty_def Sort Prop
with   crules_defs_mut   := Induction for cty_defs Sort Prop
with   crules_subtyp     := Induction for csubtyp Sort Prop.
Combined Scheme crules_mutind from crules_trm_mut, crules_def_mut, crules_defs_mut, crules_subtyp.

(** ** Well-typed programs *)
Definition compatible_constr C G t T :=
  exists tm vm, (tm, vm, G) ⊧ C /\ (C, G) ⊢c t: T.

(* (** ⊤, (x: {A: {X: ⊥..T1}..{X: ⊥..T2}}, y: T1) ⊢c y: T2 *) *)
(* Lemma typing_example1 : forall G x y A X T1 T2, *)
(*     binds x *)
(*           (typ_rcd *)
(*              (dec_typ A *)
(*                       (typ_rcd (dec_typ X typ_bot T1)) *)
(*                       (typ_rcd (dec_typ X typ_bot T2)))) *)
(*           G -> *)
(*     binds y T1 G -> *)
(*     ⊤, G ⊢c trm_var (avar_f y) : T2. *)
(* Proof. *)
(*   introv Hx Hy. *)
(*   eapply ty_constr_intro with (t := trm_var (avar_f x)). *)
(*   - constructor*. *)
(*   - apply ty_sub with (T := T1). *)
(*     -- constructor*. *)
(*     -- eapply ent_trans. *)
(*        + apply ent_and_right. *)
(*        + eapply ent_trans. apply ent_exists_v_intro'. *)
(*          eapply ent_trans. apply ent_cong_exists_v. *)
(*          2: { *)
(*            eapply ent_trans. *)
(*            eapply ent_bound_sub. *)
(*            eapply ent_trans. apply ent_and_right. *)
(*            eapply ent_trans. eapply ent_inv_subtyp_typ. *)
(*            apply ent_and_right. *)
(*          } *)
(*          simpl_open_constr. introv Heqc Heqd. subst C' D'. *)
(*          eapply ent_and_intro. apply ent_refl. *)
(* Qed. *)

