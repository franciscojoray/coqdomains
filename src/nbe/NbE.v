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
Require Import DomainLemmas.
Require Import SemOps.
Require Import Semantics.
Require Import Levels.
Require Import Reif.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.
(*end hide*)

(** *Normal forms and normalisation by evaluation (paper Defs 1, 3, 7) *)

Lemma ejemplito : forall (η : SemEnv 1),
    ⟦ VAR 0 ⟧ η =-= η !! 0.
  intro η.
  simpl.
  reflexivity.
Qed.

Definition v0 := 0.

(* SemT E (t: Term) : SemEnv E =-> VInf _BOT *)

Lemma otro_ejemplito : forall (n : nat),
    ⟦ VAR (v0) ⟧ (id_env (S n)) =-= eta (inNat n).
  intro n.
  simpl.
  reflexivity.
Qed.

Lemma ejemplito_fun :
    ⟦ FUN (VAR 0) ⟧ (id_env 0) =-= eta (inFun Id).
Proof.
  rewrite -> SemT_FUN_equation2.
  assert (Hf : F ⟦ VAR 0 ⟧ (id_env 0) =-= Id).
  { apply fmon_eq_intro. move => d.
    apply Oeq_trans with
        (y := kleisli (eta << Roll)
                (@SemT 1 (VAR 0) (id_env 0, kleisli (eta << Unroll) d))).
    { exact: (@F_body 0 (VAR 0) (id_env 0) d). }
    rewrite -> SemT_VAR_equation. rewrite -> SemVar0.
    exact: (KRKUR_id d). }
  rewrite -> Hf.
  apply tset_refl.
Qed.

(* the Var-branch of RrecC ignores its recursion argument *)

Lemma nbE_var_id : forall (E : Env) (n : nat), n <= E ->
    exists v : VInf,
      ⟦ VAR (E - n) ⟧ (id_env (S E)) =-= eta v
      /\ R (S E) v =-= eta (VAR (E - n)).
Proof.
  move => E n Hn. exists (inNat n).
  by split; [apply SemVarDenots | apply R_roundtrip].
Qed.

(* Stream-level congruence of Val *)

Lemma mark_fun0 : F ⟦VAR 0⟧ (id_env 1) (eta (Roll (inNat 1))) =-= eta (Roll (inNat 1)).
Proof.
  rewrite -> F_body.
  have Harg : @SemT 2 (VAR 0) (id_env 1, kleisli (eta << Unroll) (eta (Roll (inNat 1))))
              =-= eta (inNat 1).
  { rewrite -> SemT_VAR_equation. rewrite -> SemVar0.
    rewrite -> kleisli_eta. rewrite -> comp_simpl.
    apply StreamVal_eq. exact (fmon_eq_elim UR_id (inNat 1)). }
  apply Oeq_trans with (y := kleisli (eta << Roll) (eta (inNat 1))).
  - by apply kleisli_eq_arg.
  - rewrite -> kleisli_eta. rewrite -> comp_simpl. by [].
Qed.

Lemma mark_fun1 : F ⟦VAR 1⟧ (id_env 2) (eta (Roll (inNat 2))) =-= eta (Roll (inNat 1)).
Proof.
  rewrite -> F_body.
  have Harg : @SemT 3 (VAR 1) (id_env 2, kleisli (eta << Unroll) (eta (Roll (inNat 2))))
              =-= eta (inNat 1).
  { rewrite -> SemT_VAR_equation.
    rewrite -> (@SemVarS 0 2 (id_env 2) (kleisli (eta << Unroll) (eta (Roll (inNat 2))))).
    change (@SemVar 0 2 (id_env 1, eta (inNat 1)) =-= eta (inNat 1)).
    rewrite -> (@SemVar0 1 (id_env 1) (eta (inNat 1))). by []. }
  apply Oeq_trans with (y := kleisli (eta << Roll) (eta (inNat 1))).
  - by apply kleisli_eq_arg.
  - rewrite -> kleisli_eta. rewrite -> comp_simpl. by [].
Qed.

(* Regression test (the old counterexample): lambda.1 reifies to lambda.1 *)

Lemma R_FUN_1 : R 2 (inFun (F ⟦VAR 1⟧ (id_env 2))) =-= eta (FUN (VAR 1)).
Proof.
  rewrite -> (R_FUN 2 (F ⟦VAR 1⟧ (id_env 2))).
  rewrite -> (FunCase_eval (R 3) mark_fun1).
  rewrite -> (KLEISLI_etaVal (R 3) (inNat 1)).
  rewrite -> (R_roundtrip 2 1).
  rewrite -> kleisli_eta. rewrite -> comp_simpl. by [].
Qed.

(* Regression test: identity abstraction *)

Lemma R_FUN_0 : R 1 (inFun (F ⟦VAR 0⟧ (id_env 1))) =-= eta (FUN (VAR 0)).
Proof.
  rewrite -> (R_FUN 1 (F ⟦VAR 0⟧ (id_env 1))).
  rewrite -> (FunCase_eval (R 2) mark_fun0).
  rewrite -> (KLEISLI_etaVal (R 2) (inNat 1)).
  rewrite -> (R_roundtrip 1 1).
  rewrite -> kleisli_eta. rewrite -> comp_simpl. by [].
Qed.

(* Closed terms (paper R_0, ISSUE-022): the identity abstraction in the empty
   context.  The fresh mark at level 0 is inNat 0. *)

Lemma mark_fun_closed :
  F ⟦VAR 0⟧ (id_env 0) (eta (Roll (inNat 0))) =-= eta (Roll (inNat 0)).
Proof.
  rewrite -> F_body.
  have Harg : @SemT 1 (VAR 0) (id_env 0, kleisli (eta << Unroll) (eta (Roll (inNat 0))))
              =-= eta (inNat 0).
  { rewrite -> SemT_VAR_equation. rewrite -> SemVar0.
    rewrite -> kleisli_eta. rewrite -> comp_simpl.
    apply StreamVal_eq. exact (fmon_eq_elim UR_id (inNat 0)). }
  apply Oeq_trans with (y := kleisli (eta << Roll) (eta (inNat 0))).
  - by apply kleisli_eq_arg.
  - rewrite -> kleisli_eta. rewrite -> comp_simpl. by [].
Qed.

Lemma R_FUN_closed : R 0 (inFun (F ⟦VAR 0⟧ (id_env 0))) =-= eta (FUN (VAR 0)).
Proof.
  rewrite -> (R_FUN 0 (F ⟦VAR 0⟧ (id_env 0))).
  rewrite -> (FunCase_eval (R 1) mark_fun_closed).
  rewrite -> (KLEISLI_etaVal (R 1) (inNat 0)).
  rewrite -> (R_roundtrip 0 0).
  rewrite -> kleisli_eta. rewrite -> comp_simpl. by [].
Qed.

(* NbE completeness for the identity abstraction *)

Lemma nbE_fun_id : exists v : VInf,
    ⟦ FUN (VAR 1) ⟧ (id_env 2) =-= eta v
    /\ R 2 v =-= eta (FUN (VAR 1)).
Proof.
  exists (inFun (F ⟦VAR 1⟧ (id_env 2))).
  split.
  - by rewrite -> SemT_FUN_equation2.
  - exact R_FUN_1.
Qed.

(* AppCase computes to the DAPP-wrap of the strict pairing of the two
   same-level readbacks *)

Inductive Ne : Term -> Prop :=
| Ne_var : forall n : Var, Ne (VAR n)
| Ne_app : forall (k v : Term), Ne k -> Nf v -> Ne (APP k v)
with Nf : Term -> Prop :=
| Nf_fun : forall e : Term, Nf e -> Nf (FUN e)
| Nf_ne  : forall k : Term, Ne k -> Nf k.

(* paper Remark 2, fragment: Ne is included in Nf *)

Lemma Ne_Nf : forall k : Term, Ne k -> Nf k.
Proof. move => k H. by apply Nf_ne. Qed.

(* paper Def. 3, simple-language instance: the semantic normal/neutral values
   are those whose readback is a normal/neutral term. *)

Definition NfD (E : Env) (v : VInf) : Prop :=
  exists t : Term, R E v =-= eta t /\ Nf t.

Definition NeD (E : Env) (v : VInf) : Prop :=
  exists t : Term, R E v =-= eta t /\ Ne t.

(* R maps semantic normal forms to (reified) normal forms *)

Lemma NfD_readback : forall (E : Env) (v : VInf),
    NfD E v -> exists t, Nf t /\ R E v =-= eta t.
Proof. move => E v [t [H Ht]]. by exists t. Qed.

(** *Sanity checks *)

Example nf_id : Nf (FUN (VAR 0)).
Proof. apply Nf_fun. apply Nf_ne. apply Ne_var. Qed.

Example ne_app0 : Ne (APP (VAR 0) (VAR 1)).
Proof. apply Ne_app. apply Ne_var. apply Nf_ne. apply Ne_var. Qed.

(** *Normalisation by evaluation (paper Def. 7):
   nbe_Γ(t) = R_{|Γ|}(⟦t⟧ ρ_Γ), with the lift handled by the stream-kleisli
   extension of R. *)

Check R 0.
Check ⟦ VAR 0 ⟧ (id_env 1).
Check KLEISLI (R 0) (⟦ VAR 0 ⟧ (id_env 1)).

Definition nbe (E : Env) (t : Term) : discrete_cpoType Term _BOT :=
  KLEISLI (R E) (⟦ t ⟧ (id_env E)).

(* paper Lemma 8, variable instance: nbe is the identity on variables
   (index n in a context of size S E, with n <= E). *)

Lemma nbe_var : forall (E n : nat), n <= E ->
    nbe (S E) (VAR n) =-= eta (VAR n).
Proof.
  move => E n Hn.
  unfold nbe.
  rewrite -> SemT_VAR_equation.
  rewrite -> (SemVar_id_env Hn).
  rewrite -> (KLEISLI_etaVal (R (S E)) (inNat (E - n))).
  rewrite -> R_roundtrip.
  rewrite -> (subn_round Hn).
  apply tset_refl.
Qed.

(* paper Def. 7 at the empty context (ISSUE-022): closed terms normalise. *)

Lemma nbe_closed_id : nbe 0 (FUN (VAR 0)) =-= eta (FUN (VAR 0)).
Proof.
  unfold nbe.
  rewrite -> SemT_FUN_equation2.
  rewrite -> (KLEISLI_etaVal (R 0) (inFun (F ⟦VAR 0⟧ (id_env 0)))).
  exact R_FUN_closed.
Qed.

(* paper Lemma 8 on a neutral application (ISSUE-020): with application on
   neutrals, `x_0 · x_1` is the neutral `App x_0 x_1`, read back to the same
   term.  (Before ISSUE-020, `AppOp` sent neutrals to ⊥ and this was ⊥.) *)

Lemma nbe_neutral_app :
  nbe 2 (APP (VAR 1) (VAR 0)) =-= eta (APP (VAR 1) (VAR 0)).
Proof.
  unfold nbe.
  have H1 : ⟦ VAR 1 ⟧ (id_env 2) =-= eta (inNat 0) by (simpl; reflexivity).
  have H0 : ⟦ VAR 0 ⟧ (id_env 2) =-= eta (inNat 1) by (simpl; reflexivity).
  rewrite -> SemT_APP_equation.
  rewrite -> (AppOp_nat H1 H0).
  rewrite -> (KLEISLI_etaVal (R 2) (inPair (Roll (inNat 0), Roll (inNat 1)))).
  exact: (R_neutral_app (R_roundtrip 1 0) (R_roundtrip 1 1)).
Qed.

(* nested neutral application: the head `x_0 · x_1` is itself the neutral
   `App x_0 x_1` (an `inPair`), so the outer application uses the `inPair`
   case of `AppOp` (`AppOp_pair`) *)

Lemma nbe_neutral_app2 :
  nbe 2 (APP (APP (VAR 1) (VAR 0)) (VAR 0))
  =-= eta (APP (APP (VAR 1) (VAR 0)) (VAR 0)).
Proof.
  unfold nbe.
  have H1 : ⟦ VAR 1 ⟧ (id_env 2) =-= eta (inNat 0) by (simpl; reflexivity).
  have H0 : ⟦ VAR 0 ⟧ (id_env 2) =-= eta (inNat 1) by (simpl; reflexivity).
  have Hin : ⟦ APP (VAR 1) (VAR 0) ⟧ (id_env 2)
             =-= eta (inPair (Roll (inNat 0), Roll (inNat 1))).
  { rewrite -> SemT_APP_equation. exact: (AppOp_nat H1 H0). }
  rewrite -> SemT_APP_equation.
  rewrite -> (AppOp_pair Hin H0).
  rewrite -> (KLEISLI_etaVal (R 2)
               (inPair (Roll (inPair (Roll (inNat 0), Roll (inNat 1))),
                        Roll (inNat 1)))).
  apply: R_neutral_app.
  - exact: (R_neutral_app (R_roundtrip 1 0) (R_roundtrip 1 1)).
  - exact: (R_roundtrip 1 1).
Qed.
