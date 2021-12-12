(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import Definitions.
Require Import ConstrLangAlt ConstrTyping ConstrEntailment.
Require Import ConstrSubtypingLaws.
Require Import Coq.Program.Equality.

(** * Subenvironments for constraint typing [C ⊩ G1 ⪯ G2] *)
(** [G1] is a subenvironment of [G2], denoted [G1 ⪯ G2],
    if [dom(G1) = dom(G2)] and for each [x],
    [G1 ⊢ G1(x) <: G2(x)]. *)
Reserved Notation "C '⊩e' G1 '⪯' G2" (at level 35).

Inductive csubenv : constr -> ctx -> ctx -> Prop :=
| csubenv_empty : forall C, C ⊩e empty ⪯ empty
| csubenv_grow: forall C G G' x T T',
    C ⊩e G ⪯ G' ->
    ok (G & x ~ T) ->
    (C, G) ⊢c T <: T' ->
    C ⊩e G & x ~ T ⪯ G' & x ~ T'
where "C '⊩e' G1 '⪯' G2" := (csubenv C G1 G2).

Hint Constructors csubenv.

(** If [ok G], then [G ⪯ G].
    Note: [ok(G)] means that [G]'s domain consists of distinct variables.
    [ok] is defined in [TLC.LibEnv.v] *)
Lemma csubenv_refl : forall C G, ok G -> C ⊩e G ⪯ G.
Proof.
  intros C G H. induction H; eauto using csubtyp_refl.
Qed.
Hint Resolve csubenv_refl.

(** [G' subG G]                  #<br>#
    [ok(G', x: T)]               #<br>#
    [―――――――――――――――――――――――――――――]  #<br>#
    [G', x: T subG G, x: T]  #<br># *)
Lemma csubenv_push : forall C G1 G2 x T,
    C ⊩e G1 ⪯ G2 ->
    ok (G1 & x ~ T) -> ok (G2 & x ~ T) ->
    C ⊩e (G1 & x ~ T) ⪯ (G2 & x ~ T).
Proof.
  intros. induction H; intros; eauto using csubtyp_refl.
Qed.
Hint Resolve csubenv_push.

(** [G ⊢ S <: U]                      #<br>#
    [ok(G, x: S)] (see [subenv_push]) #<br>#
    [――――――――――――――――――――――――――――――――――]  #<br>#
    [G', x: T subG G, x: T] *)
Lemma csubenv_last: forall C G x S U,
  (C, G) ⊢c S <: U ->
  ok (G & x ~ S) ->
  C ⊩e (G & x ~ S) ⪯ (G & x ~ U).
Proof.
  intros.
  inversion H0;
  match goal with
  | [ H : empty = _ |- _ ] => destruct (empty_push_inv H2)
  | [ H : _ & _ ~ _ = _ & _ ~ _ |- _ ] =>
    apply eq_push_inv in H; destruct_all; subst
  end;
  auto.
Qed.
Hint Resolve csubenv_last.

Lemma csubenv_ok_fresh : forall C G G',
    C ⊩e G ⪯ G' ->
    ok G' /\ (forall x, x # G -> x # G').
Proof.
  introv H.
  induction H;
    destruct_all;
    match goal with
    | [H : ok (?G & ?x ~ _) |- _] =>
      pose proof (ok_push_inv H0) as [? ?]; split; auto
    | _ => split; auto
    end.
Qed.

Lemma csubenv_ok_l : forall C G1 G2,
    C ⊩e G1 ⪯ G2 -> ok G1.
Proof.
  introv H. induction H; auto.
Qed.
Hint Resolve csubenv_ok_l.

Lemma csubenv_ok_r: forall C G1 G2,
    C ⊩e G1 ⪯ G2 -> ok G2.
Proof.
  apply csubenv_ok_fresh.
Qed.
Hint Resolve csubenv_ok_r.
