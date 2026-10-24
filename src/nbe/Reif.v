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
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.
(*end hide*)

(** *Reification (paper Def. 2) as a family fixpoint *)

Definition DVAR : nat_cpoType =-> discrete_cpoType Term.
  apply SimpleUOp.
  apply VAR.
Defined.

Definition DFUN : discrete_cpoType Term =-> discrete_cpoType Term.
  apply SimpleUOp.
  apply FUN.
Defined.

(* The reification Var-branch (`FVar`) and the supporting arithmetic live in
   `Levels.v` (ISSUE-000a). *)

Definition dist {A B C : cpoType} : (A * (B + C)) =-> ((A * B) + (A * C)).
  assert (H: (B + C) =-> (A-=> ((A * B) + (A * C)))).
  refine (SUM_fun _ _).
  apply (CURRY (D0:= B)).
  refine (ccomp _ _). apply (in1 (A:= A*B)).
  refine (PROD_fun _ _). apply pi2. apply pi1.
  apply (CURRY (D0:= C)).
  refine (ccomp _ _). apply (in2 (B:= A*C)).
  refine (PROD_fun _ _). apply pi2. apply pi1.
  apply ((UNCURRY H) << <|pi2,pi1 |>).
Defined.

Definition DAPP :
  (discrete_cpoType Term * discrete_cpoType Term) =-> discrete_cpoType Term.
  apply (SimpleBOp (A := Term) (B := Term) (C := discrete_cpoType Term)).
  apply APP.
Defined.

(** *Reification: one fixpoint over the family of all levels *)
(* With unindexed Term the family is constant: RFam E is the same cpoType
   for every E; only the projection index carries the level. *)

Definition RFam (E : Env) : cpoType :=
  VInf -=> discrete_cpoType Term _BOT.

Definition RAmb : cpoType := prodi_cpoType RFam.

Lemma RAmbbotAxiom :
  Pointed.axiom (fun i : Env => const VInf (⊥ : discrete_cpoType Term _BOT)).
Proof.
  move => d x. by apply: leastP.
Qed.

Canonical Structure RAmbDC : cppoType :=
  Eval hnf in @CppoType RAmb (PointedMixin RAmbbotAxiom).

(* Rj (Lam f ) = λ (Rj+1 (f xj )) *)

Definition FunCase (E: Env) :
    (VInf -=> discrete_cpoType Term _BOT) * (DInf _BOT -=> DInf _BOT) =->
                                                     discrete_cpoType Term _BOT.
  refine (ccomp _ _).
  Focus 2.
  refine (PROD_fun _ _).
  apply pi1.
  apply (kleisli (eta << Unroll) << ev <<
           <| pi2 (A:=(VInf -=> discrete_cpoType Term _BOT))
            , const _ (eta (Roll (inNat E)))|>).
  refine (ccomp _ _).
  apply (kleisli (eta << DFUN)).
  refine (ccomp _ _).
  apply (ev (A:=VInf _BOT) (B:=discrete_cpoType Term _BOT)).
  refine (PROD_fun _ _).
  apply (KLEISLI << pi1 (B:=(VInf _BOT))).
  apply (pi2 (A:= VInf -=> discrete_cpoType Term _BOT)).
Defined.

(* Rj (App d d0 ) = App (Rj d) (Rj d0 ) *)

Definition AppCase (E: Env) :
  (VInf -=> discrete_cpoType Term _BOT) * (DInf * DInf) =->
  discrete_cpoType Term _BOT.
  refine (ccomp _ _).
  apply (kleisli (eta << DAPP)).
  refine (ccomp _ _).
  apply (uncurry (Smash (discrete_cpoType Term) (discrete_cpoType Term))).
  refine (PROD_fun _ _).
  refine (ccomp _ _).
  apply ((ev (A:=VInf _BOT) (B:=discrete_cpoType Term _BOT))).
  refine (PROD_fun _ _).
  apply (KLEISLI << pi1 (B := DInf * DInf)).
  apply (eta << Unroll << pi1 << pi2).
  refine (ccomp _ _).
  apply ((ev (A:=VInf _BOT) (B:=discrete_cpoType Term _BOT))).
  refine (PROD_fun _ _).
  apply (KLEISLI << pi1 (B := DInf * DInf)).
  apply (eta << Unroll << pi2 << pi2).
Defined.

Definition RrecC (E: Env) : RAmb =-> (VInf -=> discrete_cpoType Term _BOT).
  refine (exp_fun _).
  refine (ccomp _ _).
  Focus 2.
  apply dist.
  refine (ccomp _ _).
  Focus 2.
  refine (SUM_fun _ _).
  refine (ccomp _ _).
  apply (in1 (B:= RAmb * (DInf * DInf))).
  apply dist.
  apply in2.
  refine (SUM_fun (SUM_fun _ _) _).
  (* CASO Var *)
  apply (eta << FVar E << pi2).
  (* CASO Fun *)
  apply (FunCase E << <| PROJ RFam E.+1 << pi1 (B:= DInf _BOT -=> DInf _BOT)
                      , pi2 (A:= RAmb) |>).
  (* CASO App *)
  apply (AppCase E << <| PROJ RFam E << pi1 (B:= DInf * DInf)
                      , pi2 (A:= RAmb) |>).
Defined.

Definition Rrec : RAmb =-> RAmb :=
  PRODI_fun (fun E => RrecC E).

(* R E reifies at level E (paper R_j, with j = E variables in scope): the
   family member of index E.  Level 0 is a genuine member (paper R_0), so
   closed terms are read back too (ISSUE-022). *)

Definition R (E: Env) : VInf -=> discrete_cpoType Term _BOT :=
  PROJ RFam E (fixp Rrec).

Lemma RrecC_var : forall (E : Env) (ρ : RAmb) (n : nat),
    RrecC E ρ (inNat n) =-= eta (VAR (E - n.+1)).
Proof.
  move => E ρ n.
  unfold RrecC, dist, inNat, FVar.
  unlock SUM_fun.
  cbn.
  split; apply DLle_refl.
Qed.

(* RrecC's fun-case dispatches to FunCase — the only place where RrecC is
   unfolded; all clients use this law (no unfolds) *)

Lemma Rrec_FUN : forall (E : Env) (ρ : RAmb) (f : DInf _BOT -=> DInf _BOT),
    RrecC E ρ (inFun f) =-= FunCase E (PROJ RFam E.+1 ρ, f).
Proof.
  move => E ρ f.
  unfold RrecC, dist, inNat, inFun.
  unlock SUM_fun.
  cbn.
  split; apply DLle_refl.
Qed.

(* paper Def. 2, variable case at any level j: R_j(x_n) = q p^(j-n-1). *)

Lemma R_var : forall (E : Env) (n : nat),
    R E (inNat n) =-= eta (VAR (E - n.+1)).
Proof.
  move => E n.
  unfold R.
  rewrite -> (fixp_eq Rrec).
  change (RrecC E (fixp Rrec) (inNat n) =-= eta (VAR (E - n.+1))).
  apply (@RrecC_var E (fixp Rrec) n).
Qed.

(* R ∘ Sem = id, variable case: R reads the denotation of a variable back to
   the syntax.  (Unconditional on the readback side.) *)

Lemma R_roundtrip : forall (E : Env) (n : nat),
    R (S E) (inNat n) =-= eta (VAR (E - n)).
Proof.
  move => E n.
  rewrite -> (R_var (S E) n).
  by rewrite subSS.
Qed.

(* pointwise Var-branch behaviour of the fixpoint *)

Lemma R1_inNat : forall n, R 1 (inNat n) =-= eta (VAR (0 - n)).
Proof.
  move => n.
  apply (@R_roundtrip 0 n).
Qed.

(* The variable of index E - k denotes the semantic mark inNat (E - k)'s
   counterpart: lookup of slot k in the canonical environment of size S E
   yields the mark inNat (E - k). *)

Lemma FunCase_simpl : forall (E : Env) (r : VInf -=> discrete_cpoType Term _BOT)
                             (f : DInf _BOT -=> DInf _BOT),
    FunCase E (r, f) =-=
    kleisli (eta << DFUN)
      (KLEISLI r (kleisli (eta << Unroll) (f (eta (Roll (inNat E)))))).
Proof.
  move => E r f.
  unfold FunCase.
  cbn.
  split; apply DLle_refl.
Qed.

(* the fun-case evaluation law: reading the function at the fresh mark
   eta (Roll (inNat E)) (paper x_j at level j = E; lifted argument, CBN);
   the body is reified by the
   next level's thunk (no renaming layer) *)

Lemma FunCase_eval : forall (E : Env) (r : VInf -=> discrete_cpoType Term _BOT)
                             (f : DInf _BOT -=> DInf _BOT) (v : VInf),
    f (eta (Roll (inNat E))) =-= eta (Roll v) ->
    FunCase E (r, f) =-= kleisli (eta << DFUN) (KLEISLI r (eta v)).
Proof.
  move => E r f v Hf.
  rewrite -> (FunCase_simpl E r f).
  apply kleisli_eq_arg. apply KLEISLI_eq_arg.
  have Hf' : f (eta (Roll (inNat E))) =-= Val (Roll v).
  { rewrite <- eta_val. exact Hf. }
  have Hbody : kleisli (eta << Unroll) (f (eta (Roll (inNat E)))) =-= eta v.
  { apply Oeq_trans with (y := eta (Unroll (Roll v))).
    - apply Oeq_trans with (y := kleisli (eta << Unroll) (Val (Roll v))).
      + by apply kleisli_eq_arg.
      + rewrite -> kleisliVal. rewrite -> comp_simpl. by [].
    - apply StreamVal_eq.
      have X := fmon_eq_elim UR_id v.
      exact X. }
  exact Hbody.
Qed.

(* lookup of the freshest slot *)

Lemma AppCase_simpl : forall (E : Env) (r : VInf -=> discrete_cpoType Term _BOT)
                              (d d' : DInf),
    AppCase E (r, (d, d')) =-=
    kleisli (eta << DAPP)
      (Smash (discrete_cpoType Term) (discrete_cpoType Term)
        (KLEISLI r (eta (Unroll d))) (KLEISLI r (eta (Unroll d')))).
Proof.
  move => E r d d'.
  unfold AppCase.
  cbn.
  split; apply DLle_refl.
Qed.

(* client-facing App-branch law (mirror of Rrec_FUN) *)

Lemma RrecC_app : forall (E : Env) (ρ : RAmb) (d d' : DInf),
    RrecC E ρ (inPair (d, d')) =-=
    kleisli (eta << DAPP)
      (Smash (discrete_cpoType Term) (discrete_cpoType Term)
        (KLEISLI (PROJ RFam E ρ) (eta (Unroll d)))
        (KLEISLI (PROJ RFam E ρ) (eta (Unroll d')))).
Proof.
  move => E ρ d d'.
  unfold RrecC, dist, inPair.
  unlock SUM_fun.
  cbn.
  split; apply DLle_refl.
Qed.

(* client-facing laws of R itself (paper Def. 2, Lam and App cases), at any
   level E; clients need not unfold R into PROJ / fixp_eq *)

Lemma R_FUN : forall (E : Env) (f : DInf _BOT -=> DInf _BOT),
    R E (inFun f) =-= FunCase E (R E.+1, f).
Proof.
  move => E f.
  unfold R.
  rewrite -> (fixp_eq Rrec) at 1.
  change (RrecC E (fixp Rrec) (inFun f) =-=
          FunCase E (PROJ RFam E.+1 (fixp Rrec), f)).
  apply (@Rrec_FUN E (fixp Rrec) f).
Qed.

Lemma R_APP : forall (E : Env) (d d' : DInf),
    R E (inPair (d, d')) =-=
    kleisli (eta << DAPP)
      (Smash (discrete_cpoType Term) (discrete_cpoType Term)
        (KLEISLI (R E) (eta (Unroll d)))
        (KLEISLI (R E) (eta (Unroll d')))).
Proof.
  move => E d d'.
  unfold R.
  rewrite -> (fixp_eq Rrec) at 1.
  change (RrecC E (fixp Rrec) (inPair (d, d')) =-=
          kleisli (eta << DAPP)
            (Smash (discrete_cpoType Term) (discrete_cpoType Term)
              (KLEISLI (PROJ RFam E (fixp Rrec)) (eta (Unroll d)))
              (KLEISLI (PROJ RFam E (fixp Rrec)) (eta (Unroll d'))))).
  apply (@RrecC_app E (fixp Rrec) d d').
Qed.

(* paper Def. 2, App case, at the level of terms: a neutral application
   `App k e` (encoded `inPair (Roll k, Roll e)`, ISSUE-020) reads back to the
   application of the readbacks *)

Lemma R_neutral_app : forall (E : Env) (k e : VInf) (tk te : Term),
    R E k =-= eta tk -> R E e =-= eta te ->
    R E (inPair (Roll k, Roll e)) =-= eta (APP tk te).
Proof.
  move => E k e tk te Hk He.
  rewrite -> R_APP.
  have Uk : Unroll (Roll k) =-= k := fmon_eq_elim UR_id k.
  have Ue : Unroll (Roll e) =-= e := fmon_eq_elim UR_id e.
  rewrite -> Uk. rewrite -> Ue.
  rewrite -> (KLEISLI_etaVal (R E) k). rewrite -> Hk.
  rewrite -> (KLEISLI_etaVal (R E) e). rewrite -> He.
  have Hs : Smash (discrete_cpoType Term) (discrete_cpoType Term) (eta tk) (eta te)
            =-= eta (tk, te).
  { apply: SmashLemmaValVal. split; reflexivity. }
  rewrite -> Hs.
  rewrite -> kleisli_eta. rewrite -> comp_simpl.
  reflexivity.
Qed.

(** *Normal forms and neutral terms (paper Def. 1, simple language) *)
