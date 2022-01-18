(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import String.
Require Import Coq.Program.Equality.
Require Import Definitions Binding Weakening.

Definition stricter_env (G G' : ctx) := forall x T,
    binds x T G ->
    G' ⊢ trm_var (avar_f x) : T.

Lemma stricter_env_push : forall G1 G2 x T,
    ok (G2 & x ~ T) ->
    stricter_env G1 G2 ->
    stricter_env (G1 & x ~ T) (G2 & x ~ T).
Proof.
  introv Hok Hse. unfold stricter_env.
  introv HB. apply binds_concat_inv in HB.
  destruct HB as [HB | HB].
  - apply binds_single_inv in HB. destruct HB. subst.
    eauto.
  - destruct HB as [Hx HB]. apply Hse in HB.
    apply weaken_ty_trm. assumption. assumption.
Qed.

Lemma ty_trm_strict : forall G G' t T,
    stricter_env G G' ->
    ok G' ->
    G ⊢ t : T ->
    G' ⊢ t : T
with ty_def_strict : forall G G' d D,
    stricter_env G G' ->
    ok G' ->
    G /- d : D ->
    G' /- d : D
with ty_defs_strict : forall G G' ds T,
    stricter_env G G' ->
    ok G' ->
    G /- ds :: T ->
    G' /- ds :: T
with subtyp_strict : forall G G' T U,
    stricter_env G G' ->
    ok G' ->
    G ⊢ T <: U ->
    G' ⊢ T <: U.
Proof.
  all: introv Hse Hok H.
  - gen G'.
    dependent induction H; introv Hse Hok; unfold stricter_env in Hse.
    -- apply Hse in H. assumption.
    -- apply ty_all_intro with (L:=L \u dom G'). introv Hx. apply H0; try assumption. eauto.
       apply stricter_env_push. eauto. assumption. eauto.
    -- specialize (IHty_trm1 _ Hse Hok).
       specialize (IHty_trm2 _ Hse Hok).
       econstructor. exact IHty_trm1. assumption.
    -- apply ty_new_intro with (L:=L \u dom G'). introv Hx.
       apply ty_defs_strict with (G:=G & x ~ open_typ x T).
       apply stricter_env_push. eauto. assumption. eauto. apply H. eauto.
    -- apply ty_new_elim. apply IHty_trm. assumption. eauto.
    -- apply ty_let with (L:=L \u dom G') (T:=T). apply IHty_trm; assumption.
       introv Hx. apply H1; try assumption. eauto. apply stricter_env_push.
       eauto. assumption. eauto.
    -- apply ty_rec_intro. apply IHty_trm; assumption.
    -- apply ty_rec_elim. apply IHty_trm; assumption.
    -- apply ty_and_intro. apply IHty_trm1; assumption.
       apply IHty_trm2; assumption.
    -- eapply ty_sub. apply IHty_trm; assumption.
       eapply subtyp_strict. exact Hse. assumption. exact H0.
 - gen G'.
   dependent induction H; introv Hse Hok.
   -- apply ty_def_typ.
   -- apply ty_def_trm. eapply ty_trm_strict; try apply Hse; try assumption.
 - gen G'.
   dependent induction H; introv Hse Hok.
   -- apply ty_defs_one. eapply ty_def_strict; try apply Hse; assumption.
   -- apply ty_defs_cons. apply IHty_defs; assumption.
      eapply ty_def_strict. apply Hse. assumption. apply H0. assumption.
 - gen G'.
   dependent induction H; introv Hse Hok.
   -- apply subtyp_top.
   -- apply subtyp_bot.
   -- apply subtyp_refl.
   -- apply subtyp_trans with (T:=T). apply IHsubtyp1; assumption.
      apply IHsubtyp2; assumption.
   -- apply subtyp_and11.
   -- constructor.
   -- apply subtyp_and2. apply IHsubtyp1; assumption.
      apply IHsubtyp2; assumption.
   -- apply subtyp_fld. apply IHsubtyp; assumption.
   -- apply subtyp_typ. apply IHsubtyp1; assumption.
      apply IHsubtyp2; assumption.
   -- apply subtyp_sel2 with (T:=T). eapply ty_trm_strict; try exact Hse; try assumption.
   -- apply subtyp_sel1 with (S:=S). eapply ty_trm_strict; try exact Hse; assumption.
   -- apply subtyp_all with (L:=L \u dom G'). apply IHsubtyp; assumption.
      introv Hx. apply H1; try assumption. eauto.
      apply stricter_env_push. eauto. assumption. eauto.
Qed.
