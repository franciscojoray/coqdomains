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
Require Import Semantics.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.
(*end hide*)

(** *Levels: the reification level <-> de Bruijn index convention *)

(* Paper Def. 2 (reification), variable case:
     R_j(x_i) = q p^(j-i-1)   if i < j-1
     R_j(x_i) = q             otherwise
   Our instance: at level j (j variables in scope), the semantic mark
   inNat n is read back to the variable of de Bruijn index j - n.+1
   (= j-n-1); the nat-subtraction floor implements the collapse (index 0)
   for marks beyond the level. *)

(* the canonical discrete cpo of terms (needed so that `Term` coerces in
   `SimpleUOp`; also used by the reification modules) *)
Canonical Structure expr := Eval hnf in discrete_cpoType Term.

Definition FVar (E : Env) : nat_cpoType =-> discrete_cpoType Term :=
  SimpleUOp (fun n => VAR (E - n.+1)).

Unset Printing Notations.
Compute (FVar 0 0).
Compute (FVar 2 0).
Compute (FVar 2 1).
Compute (FVar 2 3).
Set Printing Notations.

(* Arithmetic supporting the convention. *)
Lemma subr_leOle : forall (E n : nat), (E - n) <= E.
Proof. move => E n. rewrite natO_le. by apply: leq_subr. Qed.

Lemma subn_round : forall (E n : nat), n <= E -> E - (E - n) = n.
Proof. move => E n Hn. exact: (subKn Hn). Qed.

Fixpoint id_env (n : nat) : SemEnv n.
  induction n.
  apply ().
  apply pair.
  apply (id_env n).
  apply (eta (inNat n)).   (* lifted slot (CBN, ISSUE-024) *)
Defined.

Eval hnf in (id_env 3).

Lemma SemVar_id_env : forall (E : Env) (k : nat), k <= E ->
    SemVar k (id_env (S E)) =-= eta (inNat (E - k)).
Proof.
  move => E. elim: E => [ |E' ih] k Hk.
  - have Hk0 : k = 0 by (by apply/eqP; move: Hk; rewrite natO_le leqn0).
    subst k. simpl. apply tset_refl.
  - case: k Hk => [ |k'] Hk.
    + simpl. apply tset_refl.
    + simpl. rewrite -> (ih k' Hk). apply tset_refl.
Qed.

(* `subr_leOle` and `subn_round` now live in `Levels.v` (ISSUE-000a). *)

(* The variable of de Bruijn index E - n denotes the semantic mark inNat n
   in the environment id_env (S E). *)

Lemma SemVarDenots : forall (E : Env) (n : nat), n <= E ->
    ⟦ VAR (E - n) ⟧ (id_env (S E)) =-= eta (inNat n).
Proof.
  move => E n Hn.
  rewrite -> SemT_VAR_equation.
  rewrite -> (SemVar_id_env (subr_leOle E n)).
  rewrite -> (subn_round Hn). apply tset_refl.
Qed.

(* NbE completeness for variables: the semantic value of the variable
   VAR (E - n) reifies back to the syntax. *)
