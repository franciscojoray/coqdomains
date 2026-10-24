(*begin hide*)

Require Import Utils.
Require Import Program.
Require Import Lang.

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

Require Import DomainStuff.
Require Import PredomAll.
Require Import PredomProd.
Require Import Domains.
Require Import SemOps.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.
(*end hide*)

(** *Extrinsic term semantics *)

Fixpoint SemVar (n : Var) {E : Env} {struct n} : SemEnv E =-> VInf _BOT :=
  match n return SemEnv E =-> VInf _BOT with
  | O => match E as E0 return SemEnv E0 =-> VInf _BOT with
         | O => const _ PBot
         | S E' => pi2   (* the slot is already lifted (CBN, ISSUE-024) *)
         end
  | S n' => match E as E0 return SemEnv E0 =-> VInf _BOT with
            | O => const _ PBot
            | S E' => SemVar n' << pi1
            end
  end.

(** *Notation *)

Notation "η !! n" := (SemVar n η) (at level 1, no associativity).

Reserved Notation "⟦ t '⟧'" (at level 1, no associativity).

(** *Definition 40: Extrinsic Semantics *)

Fixpoint SemT {E : Env} (t : Term) {struct t} : SemEnv E =-> VInf _BOT :=
  match t return SemEnv E =-> VInf _BOT with
  | VAR n     => SemVar n
  | FUN e     => eta << inFun << (F (@SemT E.+1 e))
  | APP t1 t2 => AppOp (SemT t1) (SemT t2)
  end
where "⟦ t ⟧" := (SemT t).

(** *Notation and properties *)

Lemma SemT_VAR_equation : forall (E : Env) (η : SemEnv E) (n : Var),
     ⟦ VAR n ⟧ η =-= SemVar n η.
Proof.
  intros E η n. by unfold SemT.
Qed.

Lemma SemT_FUN_equation : forall (E : Env) (η : SemEnv E) (e : Term),
     ⟦ FUN e ⟧ η =-= eta (↑f ((F (@SemT E.+1 e)) η)).
Proof.
  intros E η e.
  unfold "⟦ _ ⟧" at 1. fold (@SemT E.+1 e).
  rewrite -> comp_simpl.
  apply tset_refl.
Qed.

Lemma SemT_APP_equation : forall (E : Env) (η : SemEnv E) (t1 t2 : Term),
     ⟦ t1 @ t2 ⟧ η =-= AppOp ⟦ t1 ⟧ ⟦ t2 ⟧ η.
Proof.
  by simpl.
Qed.

Lemma SemT_FUN_equation2 : forall (E : Env) (η : SemEnv E) (e : Term),
     ⟦ λ e ⟧ η =-= eta (inFun (F (@SemT E.+1 e) η)).
Proof.
  intros E η e.
  unfold "⟦ _ ⟧" at 1. fold (@SemT E.+1 e).
  rewrite -> comp_simpl.
  apply tset_refl.
Qed.

Lemma SemVar0 : forall (E : Env) (η : SemEnv E) (d : VInf _BOT),
    @SemVar 0 E.+1 (η, d) =-= d.
Proof. move => E η d. simpl. split; apply DLle_refl. Qed.

(* looking one slot deeper drops the freshest slot *)

Lemma SemVarS : forall (n : nat) (E : Env) (η : SemEnv E) (d : VInf _BOT),
    @SemVar (S n) E.+1 (η, d) =-= @SemVar n E η.
Proof. move => n E η d. simpl. split; apply DLle_refl. Qed.

(* the semantic lambda as a function of its argument *)

Lemma F_body : forall (E : Env) (t : Term) (η : SemEnv E) (d : DInf _BOT),
    F (@SemT E.+1 t) η d =-=
    kleisli (eta << Roll) (@SemT E.+1 t (η, kleisli (eta << Unroll) d)).
Proof.
  move => E t η d.
  unfold F, exp_fun. cbn.
  split; apply DLle_refl.
Qed.

(* applying the stream-kleisli extension of a thunk to a value *)
