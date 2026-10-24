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
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.
(*end hide*)

(** *Semantic environments, value-domain operators, and domain-congruence helpers *)

(* Call-by-name (ISSUE-024): a slot holds a *lifted* value, since a variable
   may be bound to a divergent argument. *)
Fixpoint SemEnv E : cpoType :=
  match E with
  | O => One
  | S E => SemEnv E * VInf _BOT
  end.

(** *Variable Semantics *)
(* Lookup of the n-th freshest slot.  With Var := nat the lookup is total:
   an empty environment (or an out-of-range index) yields the bottom of the
   lifted value domain. *)

Notation "↑⊥ v" := (eta v) (at level 1, left associativity).
(* Notation "↑int n" := (inl n) (at level 1, left associativity). *)
(* Notation "↑i⊥ n" := (↑⊥ (↑int n)) (at level 1, left associativity). *)

Notation "⊥" := PBot.

(** *Auxiliar functions *)

(* the semantic abstraction: the body is evaluated with the (lifted) argument
   in the fresh slot; non-strict in the argument (ISSUE-024) *)
Definition F (E : Env) (SemE : SemEnv E.+1 =-> VInf _BOT) :
  SemEnv E -=> (DInf _BOT -=> DInf _BOT)
  := exp_fun
      (kleisli (eta << Roll) <<
        SemE << (Id >< kleisli (eta << Unroll))).

Definition VInfToFun : VInf -=> (DInf _BOT -=> DInf _BOT) _BOT :=
  [| [| const _ ⊥, eta |] , const _ ⊥ |].

(* Semantic application `d · e` (paper §3, applicative structure of D):
     inFun f · e  = f e                 (β; read through Roll/Unroll)
     inNat n · e  = App (inNat n) e     (x_n is neutral)
     inPair p · e = App (inPair p) e    (App k v is neutral)
   where `App k v` is encoded as `inPair (Roll k, Roll v)` — the reification
   reads it back as `APP` (`Reif.v`, `R_APP`).  Neutral applications were
   previously sent to ⊥ (via `VInfToFun`); see ISSUE-020.
   Call-by-name (ISSUE-024): the argument is *lifted*.  Application is strict
   only in the head; `Lam f · a` passes `a` unevaluated (β holds for every
   argument), while a neutral stays strict in its argument (`App k ⊥` needs no
   representative: readback is strict anyway). *)

(* neutral case: k · a = App k a, strict in a *)
Definition NeuC : VInf =-> (VInf _BOT -=> VInf _BOT) :=
  exp_fun ((KLEISLIL (eta << inPair << (Roll >< Roll) << SWAP) << SWAP)
             : cpoCatType (VInf * VInf _BOT) (VInf _BOT)).

(* function case: f · a = f a (through Roll/Unroll), non-strict in a *)
Definition FunC : (DInf _BOT -=> DInf _BOT) =-> (VInf _BOT -=> VInf _BOT) :=
  exp_fun ((kleisli (eta << Unroll) << ev << (Id >< kleisli (eta << Roll)))
             : cpoCatType ((DInf _BOT -=> DInf _BOT) * VInf _BOT) (VInf _BOT)).

Definition AppC : VInf =-> (VInf _BOT -=> VInf _BOT) :=
  [| [| NeuC << inNat , FunC |] , NeuC << inPair |].

(* application of a value to a lifted argument *)
Definition AppV : VInf * VInf _BOT =-> VInf _BOT := uncurry AppC.

(* application on denotations: strict in the head only *)
Definition AppOp {E : Env}
           (d1 : SemEnv E =-> VInf _BOT)
           (d2 : SemEnv E =-> VInf _BOT) : SemEnv E =-> VInf _BOT :=
  KLEISLIL AppV << <| d1 , d2 |>
.

Infix "↓f"   := AppOp (at level 1, no associativity) .

(** Notation *)

Notation "↑f f" := (inFun f) (at level 1, left associativity).

Notation "↑n n" := (inNat n) (at level 1, left associativity).

Notation "↑p p" := (inPair p) (at level 1, left associativity).

Notation "↑⊥ v"   := (eta v) (at level 1, left associativity).

Notation "↑n⊥ n"  := (↑⊥ (↑n n)) (at level 1, left associativity).

Notation "↑f⊥ f"  := (↑⊥ (↑f f)) (at level 1, left associativity).

Notation "↑p⊥ p"  := (↑⊥ (↑p p)) (at level 1, left associativity).

Lemma SmashLemmaValVal :
  forall A B (d : A _BOT) (d' : B _BOT)
    (v : A) (v' : B),
    d =-= ↑⊥ v /\ d' =-= ↑⊥ v' ->
    (((Smash A B) d) d') =-= ↑⊥ (v , v').
Proof.
  intros A B d d' v v' H.
  inversion H. unfold Smash.
  rewrite -> H0. rewrite -> H1.
  simpl. by rewrite -> Operator2_simpl.
Qed.

Lemma StepLemma :
  forall {A B C} (f : cpoCatType (A * B) C) (g : cpoCatType A B),
    (ev << <| exp_fun f , g |>) =-= f <<  <| Id , g |>.
Proof.
  intros A B C f g.
  assert (Fid : exp_fun f =-= exp_fun f << Id) by
      (rewrite -> comp_idR; reflexivity).
  assert (Gid : g =-= Id << g) by
      (rewrite -> comp_idL; reflexivity).
  rewrite -> Fid at 1 ; 
    rewrite -> Gid at 1.
  rewrite -> prod_fun_compr.
  rewrite -> comp_assoc.
    by rewrite exp_com.
Qed.

Lemma SmashLemma_Bot :
  forall A B (d : A _BOT) (d' : B _BOT),
    d =-= ⊥ \/ d' =-= ⊥ ->
    (((Smash A B) d) d') =-= ⊥.
Proof.
  intros A B d d' H.
  inversion H.
  - (* Case "d =-= ⊥". *)
    unfold Smash.
    rewrite -> H0.
    by rewrite -> Operator2_strictL.
  - (* Case "d' =-= ⊥". *)
    unfold Smash.
    rewrite -> H0.
    by rewrite -> Operator2_strictR.
Qed.

Lemma VInfToFun_Fun : (VInfToFun << inFun) =-= eta.
Proof.
  rewrite comp_assoc. setoid_rewrite -> sum_fun_fst.
    by setoid_rewrite -> sum_fun_snd.
Qed.

(** *Computation laws of application *)

(* componentwise equality of pairs, first component (the library registers
   no canonical Setoid instance for products) *)
Lemma pair_eq_fst : forall (A B : cpoType) (a a' : A) (b : B),
    a =-= a' -> @tset_eq (@prod_ordType A B) (a, b) (a', b).
Proof.
  move => A B a a' b H. apply: Ole_antisym; split.
  - exact (proj1 H).
  - exact: Ole_refl.
  - exact (proj2 H).
  - exact: Ole_refl.
Qed.

Lemma AppV_fun : forall (f : DInf _BOT -=> DInf _BOT) (a : VInf _BOT),
    AppV (inFun f, a) =-= kleisli (eta << Unroll) (f (kleisli (eta << Roll) a)).
Proof.
  move => f a. unfold AppV, AppC, inFun. cbn.
  rewrite -> SUM_fun_simpl. cbn. rewrite -> SUM_fun_simpl. cbn.
  by split; apply: Ole_refl.
Qed.

Lemma AppV_nat : forall (n : nat) (e : VInf),
    AppV (inNat n, eta e) =-= eta (inPair (Roll (inNat n), Roll e)).
Proof.
  move => n e. unfold AppV, AppC, inNat. cbn.
  rewrite -> SUM_fun_simpl. cbn. rewrite -> SUM_fun_simpl. cbn.
  rewrite -> KLEISLIL_simpl.
  by split; apply: Ole_refl.
Qed.

Lemma AppV_pair : forall (p : DInf * DInf) (e : VInf),
    AppV (inPair p, eta e) =-= eta (inPair (Roll (inPair p), Roll e)).
Proof.
  move => p e. unfold AppV, AppC, inPair. cbn.
  rewrite -> SUM_fun_simpl. cbn.
  rewrite -> KLEISLIL_simpl.
  by split; apply: Ole_refl.
Qed.

(* if the head is a value, AppOp is AppV on the (lifted) argument *)
Lemma AppOp_eval : forall (E : Env) (d1 d2 : SemEnv E =-> VInf _BOT)
    (η : SemEnv E) (k : VInf),
    d1 η =-= eta k ->
    AppOp d1 d2 η =-= AppV (k, d2 η).
Proof.
  move => E d1 d2 η k H1.
  unfold AppOp.
  change (KLEISLIL AppV (d1 η, d2 η) =-= AppV (k, d2 η)).
  apply Oeq_trans with (y := KLEISLIL AppV (Val k, d2 η)).
  { apply: (fmon_stable (KLEISLIL AppV)). apply: pair_eq_fst.
    rewrite <- eta_val. exact H1. }
  exact: KLEISLIL_simpl.
Qed.

(* the neutral cases at the level of denotations *)
Lemma AppOp_nat : forall (E : Env) (d1 d2 : SemEnv E =-> VInf _BOT)
    (η : SemEnv E) (n : nat) (e : VInf),
    d1 η =-= eta (inNat n) -> d2 η =-= eta e ->
    AppOp d1 d2 η =-= eta (inPair (Roll (inNat n), Roll e)).
Proof.
  move => E d1 d2 η n e H1 H2.
  rewrite -> (AppOp_eval d2 H1). rewrite -> H2. exact: AppV_nat.
Qed.

Lemma AppOp_pair : forall (E : Env) (d1 d2 : SemEnv E =-> VInf _BOT)
    (η : SemEnv E) (p : DInf * DInf) (e : VInf),
    d1 η =-= eta (inPair p) -> d2 η =-= eta e ->
    AppOp d1 d2 η =-= eta (inPair (Roll (inPair p), Roll e)).
Proof.
  move => E d1 d2 η p e H1 H2.
  rewrite -> (AppOp_eval d2 H1). rewrite -> H2. exact: AppV_pair.
Qed.



Check forall (E:Env), VInf -=> discrete_cpoType Term _BOT.

(* `expr` (the canonical discrete cpo of terms) is defined in `Levels.v`. *)

(* The domain-level congruence/reduction lemmas (`StreamVal_eq`,
   `kleisli_eq_arg`, `KLEISLI_eq_arg`, `KLEISLI_etaVal`, `kleisli_eta`) now
   live in `DomainLemmas.v` (ISSUE-000d). *)
