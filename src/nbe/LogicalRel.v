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
Require Import ExSem.
Require Import Types.
Require Import TypedNbE.
Require Import Validity.
Require Import TypedEq.
Require Import EqSubst.
Require Import NbE.
Require Import Weakening.
From Stdlib Require Import List.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*end hide*)

(** *)
(*** Logical relations (paper Defs 8–9, Thm 2) — statements ***)
(** *)

(* ISSUE-015a: the old environment-parametrised relation was false.  The
   relation below is the Kripke/readback-carrying version; the proofs are
   filled in by ISSUE-015d … 015f. *)

(** *Readback-carrying relation *)

Definition ReifRel (Gamma : LCtx) (t : Term) (d : VInf) (theta : LType) : Prop :=
  forall (Theta : LCtx),
    exists t' : Term,
      R (length Theta + length Gamma)%N d =-= eta t' /\
      (Theta ++ Gamma) ⊢ wk (length Theta) t ≡ t' ⦂ theta.

(** *Term relation (paper Def. 8) *)

Fixpoint TermRel (Gamma : LCtx) (t : Term) (d : VInf) (theta : LType) : Prop :=
  match theta with
  | UnitTy => ReifRel Gamma t d UnitTy
  | FunTy theta1 theta2 =>
      ReifRel Gamma t d (FunTy theta1 theta2) /\
      forall (Theta : LCtx) (s : Term) (a : VInf),
        @TermRel (Theta ++ Gamma) s a theta1 ->
        exists w : VInf,
          AppV (d, eta a) =-= eta w /\
          @TermRel (Theta ++ Gamma) (APP (wk (length Theta) t) s) w theta2
  end.

Arguments TermRel : clear implicits.

Notation "Gamma ⊩ t ∼ d ⦂ theta" := (TermRel Gamma t d theta)
  (at level 1, no associativity).

(** *Related substitutions (paper Def. 9) *)

Definition SubRel (Delta Gamma : LCtx) (sigma : Lang.Sub)
                  (rho : SemEnv (length Gamma)) : Prop :=
  forall (v : Var), (v < length Gamma)%N ->
    exists d : VInf,
      rho !! v =-= eta d /\
      @TermRel Delta (sigma v) d (Gamma ∋ v).

Arguments SubRel : clear implicits.

(** *Basic properties [ISSUE-015d] *)

Lemma TermRel_reify : forall (Gamma : LCtx) (t : Term) (d : VInf) (theta : LType),
    Gamma ⊩ t ∼ d ⦂ theta -> ReifRel Gamma t d theta.
Proof.
  move => Gamma t d theta H. case: theta H => [theta1 theta2 | ] /= H.
  - exact: (proj1 H).
  - exact: H.
Qed.

Lemma TermRel_typed : forall (Gamma : LCtx) (t : Term) (d : VInf) (theta : LType),
    Gamma ⊩ t ∼ d ⦂ theta -> inhabited (Gamma ⊢ t ⦂ theta).
Proof.
  move => Gamma t d theta H.
  have HR : ReifRel Gamma t d theta.
  { case: theta H => [theta1 theta2 | ] /= H; [exact: (proj1 H) | exact: H]. }
  case: (HR nil) => t' [_ HE].
  case: (EqTm_typed HE) => [[Ht] _].
  rewrite wk_0 in Ht. by constructor.
Qed.

(* the reification component is stable under typed equality *)
Lemma ReifRel_eq : forall (Gamma : LCtx) (t t' : Term) (d : VInf)
                          (theta : LType),
    ReifRel Gamma t d theta ->
    Gamma ⊢ t ≡ t' ⦂ theta ->
    ReifRel Gamma t' d theta.
Proof.
  move => Gamma t t' d theta HR Heq Theta.
  case: (HR Theta) => t'' [HRd HE].
  exists t''. split => //.
  apply: (Eq_trans _ HE).
  apply: Eq_sym. exact: (@EqTm_wk Theta Gamma t t' theta Heq).
Qed.

Lemma TermRel_eq : forall (Gamma : LCtx) (t t' : Term) (d : VInf) (theta : LType),
    Gamma ⊩ t ∼ d ⦂ theta ->
    Gamma ⊢ t ≡ t' ⦂ theta ->
    Gamma ⊩ t' ∼ d ⦂ theta.
Proof.
  move => Gamma t t' d theta.
  elim: theta Gamma t t' d => [theta1 IH1 theta2 IH2 | ] /=.
  - move => Gamma t t' d Hrel Heq. case: Hrel => [HR Hfun]. split.
    + exact: (ReifRel_eq HR Heq).
    + move => Theta s a Hsa.
      case: (Hfun Theta s a Hsa) => w [Happ Hrel2].
      exists w. split => //.
      case: (TermRel_typed Hsa) => [Hs].
      have Heqapp :
        (Theta ++ Gamma) ⊢ APP (wk (length Theta) t) s
                          ≡ APP (wk (length Theta) t') s ⦂ theta2.
      { apply: Eq_app.
        - exact: (@EqTm_wk Theta Gamma t t' (theta1 ⇥ theta2) Heq).
        - exact: (Eq_refl Hs). }
      refine (IH2 (Theta ++ Gamma) (APP (wk (length Theta) t) s)
                  (APP (wk (length Theta) t') s) w _ _).
      - exact Hrel2.
      - exact Heqapp.
  - move => Gamma t t' d Hrel Heq. exact: (ReifRel_eq Hrel Heq).
Qed.

Lemma ReifRel_weaken : forall (Theta Gamma : LCtx) (t : Term) (d : VInf)
                              (theta : LType),
    ReifRel Gamma t d theta ->
    ReifRel (Theta ++ Gamma) (wk (length Theta) t) d theta.
Proof.
  move => Theta Gamma t d theta HR Theta'.
  case: (HR (Theta' ++ Theta)) => t' [HRd HE].
  exists t'. split.
  - rewrite length_app in HRd. rewrite length_app.
    by rewrite addnA.
  - have Hterm : wk (length Theta') (wk (length Theta) t)
                 = wk (length (Theta' ++ Theta)) t.
    { rewrite length_app. by rewrite wk_wk. }
    rewrite Hterm.
    have Hassoc : (Theta' ++ (Theta ++ Gamma)) = ((Theta' ++ Theta) ++ Gamma)
      by apply: catA.
    rewrite Hassoc. exact HE.
Qed.

Lemma TermRel_weaken : forall (Theta Gamma : LCtx) (t : Term) (d : VInf)
                              (theta : LType),
    Gamma ⊩ t ∼ d ⦂ theta ->
    (Theta ++ Gamma) ⊩ wk (length Theta) t ∼ d ⦂ theta.
Proof.
  move => Theta Gamma t d theta.
  elim: theta Gamma t d => [theta1 IH1 theta2 IH2 | ] /=.
  - move => Gamma t d Hrel. case: Hrel => [HR Hfun]. split.
    + exact: (@ReifRel_weaken Theta Gamma t d (theta1 ⇥ theta2) HR).
    + move => Theta' s a Hsa.
      have Hassoc : (Theta' ++ (Theta ++ Gamma)) = ((Theta' ++ Theta) ++ Gamma)
        by apply: catA.
      have Hsa' : ((Theta' ++ Theta) ++ Gamma) ⊩ s ∼ a ⦂ theta1.
      { rewrite -Hassoc. exact Hsa. }
      case: (Hfun (Theta' ++ Theta) s a Hsa') => w [Happ Hrel2].
      exists w. split => //.
      have Hterm : wk (length Theta') (wk (length Theta) t)
                   = wk (length (Theta' ++ Theta)) t.
      { rewrite length_app. by rewrite wk_wk. }
      rewrite -Hterm in Hrel2.
      rewrite -Hassoc in Hrel2.
      exact Hrel2.
  - move => Gamma t d HR.
    exact: (@ReifRel_weaken Theta Gamma t d UnitTy HR).
Qed.

(** *Reflection and the identity substitution [ISSUE-015e] *)

Lemma TermRel_reflect : forall (Gamma : LCtx) (t : Term) (d : VInf)
                               (theta : LType),
    NeV d -> ReifRel Gamma t d theta -> Gamma ⊩ t ∼ d ⦂ theta.
Proof.
  move => Gamma t d theta.
  elim: theta Gamma t d => [theta1 IH1 theta2 IH2 | ] /=.
  - move => Gamma t d Hne HR. split.
    + exact HR.
    + move => Theta s a Hsa.
      exists (inPair (Roll d, Roll a)). split.
      * exact: (@NeV_AppV d a Hne).
      * apply: (IH2 (Theta ++ Gamma) (APP (wk (length Theta) t) s)
                  (inPair (Roll d, Roll a))).
        -- exact: (@NeV_app d a Hne).
        -- move => Theta'.
           case: (HR (Theta' ++ Theta)) => tf [HRd HEf].
           have Hsa_w : (Theta' ++ (Theta ++ Gamma)) ⊩ wk (length Theta') s ∼ a ⦂ theta1.
           { exact: (@TermRel_weaken Theta' (Theta ++ Gamma) s a theta1 Hsa). }
           case: (TermRel_reify Hsa_w nil) => sf [HRa HEs].
           simpl in HEs.
           rewrite wk_0 in HEs.
           have Hindexa : (length [::] + length (Theta' ++ Theta ++ Gamma))%N
                          = (length Theta' + length (Theta ++ Gamma))%N.
           { by rewrite !length_app. }
           rewrite Hindexa in HRa.
           have Hindex : (length (Theta' ++ Theta) + length Gamma)%N
                         = (length Theta' + length (Theta ++ Gamma))%N.
           { by rewrite !length_app addnA. }
           rewrite Hindex in HRd.
           have HRapp := @R_neutral_app (length Theta' + length (Theta ++ Gamma))%N
                                          d a tf sf HRd HRa.
           exists (APP tf sf). split => //.
           have Hassoc : (Theta' ++ (Theta ++ Gamma)) = ((Theta' ++ Theta) ++ Gamma)
             by apply: catA.
           rewrite -Hassoc in HEf.
           have Hterm : wk (length Theta') (wk (length Theta) t)
                        = wk (length (Theta' ++ Theta)) t.
           { rewrite length_app. by rewrite wk_wk. }
           rewrite -Hterm in HEf.
           rewrite wk_APP.
           apply: Eq_app.
           ++ exact HEf.
           ++ exact HEs.
  - move => Gamma t d Hne HR. exact HR.
Qed.

Lemma TermRel_var : forall (Gamma : LCtx) (v : Var),
    (v < length Gamma)%N ->
    Gamma ⊩ VAR v ∼ inNat (length Gamma - v.+1) ⦂ (Gamma ∋ v).
Proof.
  move => Gamma v Hv.
  apply: TermRel_reflect.
  - exact: NeV_var.
  - move => Theta.
    exists (VAR (v + length Theta)%N).
    split.
    + exact: (@R_var_ext Gamma (length Theta) v Hv).
    + rewrite wk_VAR.
      have Hty : (Theta ++ Gamma) ⊢ VAR (v + length Theta)%N
                   ⦂ ((Theta ++ Gamma) ∋ (v + length Theta)%N).
      { apply: VarRule. rewrite length_app. rewrite addnC.
        by rewrite ltn_add2l. }
      rewrite (lookupType_app Theta Gamma v) in Hty.
      exact: (Eq_refl Hty).
Qed.

Lemma SubRel_weaken : forall (Theta Delta Gamma : LCtx) (sigma : Lang.Sub)
                             (rho : SemEnv (length Gamma)),
    SubRel Delta Gamma sigma rho ->
    SubRel (Theta ++ Delta) Gamma (fun n => wk (length Theta) (sigma n)) rho.
Proof.
  move => Theta Delta Gamma sigma rho Hsub v Hv.
  case: (Hsub v Hv) => d [Hrho Hrel].
  exists d. split => //.
  exact: (@TermRel_weaken Theta Delta (sigma v) d (Gamma ∋ v) Hrel).
Qed.

Lemma SubRel_ext : forall (Delta Gamma : LCtx) (sigma : Lang.Sub)
                          (rho : SemEnv (length Gamma)) (s : Term) (a : VInf)
                          (theta : LType),
    SubRel Delta Gamma sigma rho ->
    Delta ⊩ s ∼ a ⦂ theta ->
    SubRel Delta (theta × Gamma) (consMap s sigma) (rho, eta a).
Proof.
  move => Delta Gamma sigma rho s a theta Hsub Hrel v Hv.
  case: v Hv => [ |v'] Hv.
  - exists a. split.
    + exact: (@SemVar0 (length Gamma) rho (eta a)).
    + rewrite lookupType_cons_0. simpl. exact Hrel.
  - rewrite length_cons ltnS in Hv.
    case: (Hsub v' Hv) => d [Hrho Hrel'].
    exists d. split.
    + rewrite -> (@SemVarS v' (length Gamma) rho (eta a)). exact Hrho.
    + rewrite lookupType_cons_S. simpl. exact Hrel'.
Qed.

(* lookup in the canonical environment at the actual context length *)
Lemma SemVar_id_env_at : forall (Gamma : LCtx) (v : Var),
    (v < length Gamma)%N ->
    (id_env (length Gamma)) !! v =-= eta (inNat (length Gamma - v.+1)).
Proof.
  move => Gamma. elim: Gamma => [ |θ Gamma IH] v Hv.
  - done.
  - simpl in Hv. case: v Hv => [ |n] Hv.
    + simpl. by rewrite subn1.
    + simpl. rewrite (IH n Hv). f_equal. by rewrite subSS.
Qed.

Lemma SubRel_lift : forall (theta : LType) (Delta Gamma : LCtx)
                           (sigma : Lang.Sub) (rho : SemEnv (length Gamma))
                           (a : VInf),
    SubRel Delta Gamma sigma rho ->
    (theta × Delta) ⊩ VAR 0 ∼ a ⦂ theta ->
    SubRel (theta × Delta) (theta × Gamma) (liftSub sigma) (rho, eta a).
Proof.
  move => theta Delta Gamma sigma rho a Hsub Hvar v Hv.
  rewrite length_cons ltnS in Hv.
  case: v Hv => [ |v'] Hv.
  - exists a. split.
    + exact: (@SemVar0 (length Gamma) rho (eta a)).
    + rewrite lookupType_cons_0. simpl. exact Hvar.
  - case: (Hsub v' Hv) => d [Hrho Hrel].
    exists d. split.
    + rewrite -> (@SemVarS v' (length Gamma) rho (eta a)). exact Hrho.
    + rewrite lookupType_cons_S. rewrite liftSub_S.
      have Hw : (theta × Delta) ⊩ wk (length (theta × nil)) (sigma v') ∼ d
                  ⦂ (Gamma ∋ v').
      { exact: (@TermRel_weaken (theta × nil) Delta (sigma v') d (Gamma ∋ v') Hrel). }
      simpl in Hw.
      have Hren : (fun k : Var => S k) = (fun n : Var => (n + 1)%N)
        by apply: MapExtensional; move => n; by rewrite addn1.
      rewrite Hren. exact Hw.
Qed.

Lemma SubRel_id : forall (Gamma : LCtx),
    SubRel Gamma Gamma idSub (id_env (length Gamma)).
Proof.
  move => Gamma v Hv.
  exists (inNat (length Gamma - v.+1)). split.
  - exact: (SemVar_id_env_at Hv).
  - apply: TermRel_var. exact Hv.
Qed.

Lemma SubRel_SubOKP : forall (Delta Gamma : LCtx) (sigma : Lang.Sub)
                             (rho : SemEnv (length Gamma)),
    SubRel Delta Gamma sigma rho -> SubOKP Delta Gamma sigma.
Proof.
  move => Delta Gamma sigma rho H v Hv.
  case: (H v Hv) => d [_ Hrel].
  exact: (TermRel_typed Hrel).
Qed.

(* the semantic beta step at the value level, used by the FUN case *)
Lemma AppV_inFun_F : forall (E : Env) (e : Term) (rho : SemEnv E) (a : VInf),
    AppV (inFun (F (@SemT E.+1 e) rho), eta a) =-= @SemT E.+1 e (rho, eta a).
Proof.
  move => E e rho a.
  rewrite -> AppV_fun.
  apply Oeq_trans with
      (y := KUR (KR (@SemT E.+1 e (rho, KUR (KR (eta a)))))).
  { unfold KUR, KR. apply: kleisli_eq_arg.
    exact: (@F_body E e rho (kleisli (eta << Roll) (eta a))). }
  rewrite -> KURKR_id. rewrite -> KURKR_id. apply: tset_refl.
Qed.

(* the body of an abstraction at the fresh variable *)
Lemma F_fresh : forall (E : Env) (e : Term) (rho : SemEnv E) (n : nat),
    F (@SemT E.+1 e) rho (eta (Roll (inNat n))) =-=
    kleisli (eta << Roll) (@SemT E.+1 e (rho, eta (inNat n))).
Proof.
  move => E e rho n.
  apply Oeq_trans with
      (y := kleisli (eta << Roll)
              (@SemT E.+1 e (rho, kleisli (eta << Unroll) (eta (Roll (inNat n)))))).
  { exact: (F_body e rho (eta (Roll (inNat n)))). }
  apply: kleisli_eq_arg. apply: SemT_eq_env. apply: pair_Oeq.
  - apply: tset_refl.
  - rewrite -> kleisli_eta. rewrite -> comp_simpl.
    apply: StreamVal_eq. exact: (Unroll_Roll (inNat n)).
Qed.

(** *Fundamental theorem (paper Thm 2) [ISSUE-015f] *)

Theorem Fundamental : forall (Gamma : LCtx) (t : Term) (theta : LType),
    (Gamma ⊢ t ⦂ theta) ->
    forall (Delta : LCtx) (sigma : Lang.Sub) (rho : SemEnv (length Gamma)),
      SubRel Delta Gamma sigma rho ->
      exists d : VInf,
        ⟦ t ⟧ rho =-= eta d /\
        Delta ⊩ subT sigma t ∼ d ⦂ theta.
Proof.
  move => Gamma t theta H.
  elim: H => [Gamma0 v Hv | Gamma0 e theta' theta0 He IHe
              | Gamma0 t1 t2 theta0 theta' H1 IH1 H2 IH2].
  - (* VarRule *) move => Delta sigma rho Hsub.
    case: (Hsub v Hv) => d [Hrho Hrel].
    exists d. split.
    + rewrite SemT_VAR_equation. exact Hrho.
    + simpl. exact Hrel.
  - (* FunRule *) move => Delta sigma rho Hsub.
    pose f := F (@SemT (length Gamma0).+1 e) rho.
    exists (inFun f). split.
    + rewrite SemT_FUN_equation2. reflexivity.
    + split.
      * (* reification part *)
        move => Theta.
        set L := (length (Theta ++ Delta))%N.
        have Hsub_w : SubRel (Theta ++ Delta) Gamma0
                        (fun n => wk (length Theta) (sigma n)) rho.
        { exact: (@SubRel_weaken Theta Delta Gamma0 sigma rho Hsub). }
        have Hvar : (theta' × (Theta ++ Delta)) ⊩ VAR 0 ∼ inNat L ⦂ theta'.
        { have Hvar0 : (theta' × (Theta ++ Delta)) ⊩ VAR 0
                         ∼ inNat (length (theta' × (Theta ++ Delta)) - 0.+1)
                         ⦂ theta'.
          { apply: TermRel_var. rewrite length_cons. by rewrite ltn0Sn. }
          have Hmark : (length (theta' × (Theta ++ Delta)) - 0.+1) = L.
          { by rewrite length_cons subn1 /L. }
          rewrite Hmark in Hvar0. exact Hvar0. }
        have Hsub_lift : SubRel (theta' × (Theta ++ Delta)) (theta' × Gamma0)
                           (liftSub (fun n => wk (length Theta) (sigma n)))
                           (rho, eta (inNat L)).
        { exact: (@SubRel_lift theta' (Theta ++ Delta) Gamma0
                    (fun n => wk (length Theta) (sigma n)) rho (inNat L)
                    Hsub_w Hvar). }
        case: (IHe (theta' × (Theta ++ Delta))
                  (liftSub (fun n => wk (length Theta) (sigma n)))
                  (rho, eta (inNat L)) Hsub_lift) => w [Hw Hrelw].
        case: (TermRel_reify Hrelw nil) => b [HRb HEb].
        simpl in HEb. rewrite wk_0 in HEb.
        simpl in HRb.
        have Hidxb : (0 + (length (Theta ++ Delta)).+1)%N = L.+1
          by rewrite /L.
        rewrite Hidxb in HRb.
        change (R L.+1 w =-= eta b) in HRb.
        have Hf : f (eta (Roll (inNat L))) =-= eta (Roll w).
        { unfold f. rewrite (@F_fresh (length Gamma0) e rho L).
          rewrite Hw. rewrite kleisli_eta. rewrite comp_simpl. reflexivity. }
        have HRfun : R L (inFun f) =-= eta (FUN b).
        { rewrite (@R_FUN L f).
          rewrite (@FunCase_eval L (R L.+1) f w Hf).
          rewrite (KLEISLI_etaVal (R L.+1) w). rewrite HRb.
          rewrite kleisli_eta. rewrite comp_simpl. reflexivity. }
        exists (FUN b). split.
        -- have Hidx : (length Theta + length Delta)%N = L
             by rewrite /L length_app.
           rewrite Hidx. exact HRfun.
        -- rewrite wk_subT.
           change ((Theta ++ Delta) ⊢
                     FUN (subT (liftSub (fun n => wk (length Theta) (sigma n))) e)
                     ≡ FUN b ⦂ theta' ⇥ theta0).
           apply: Eq_xi. exact HEb.
      * (* applicative part *)
        move => Theta s a Hsa.
        have Hsub_w : SubRel (Theta ++ Delta) Gamma0
                        (fun n => wk (length Theta) (sigma n)) rho.
        { exact: (@SubRel_weaken Theta Delta Gamma0 sigma rho Hsub). }
        have Hsub_ext : SubRel (Theta ++ Delta) (theta' × Gamma0)
                          (consMap s (fun n => wk (length Theta) (sigma n)))
                          (rho, eta a).
        { exact: (@SubRel_ext (Theta ++ Delta) Gamma0
                    (fun n => wk (length Theta) (sigma n)) rho s a theta'
                    Hsub_w Hsa). }
        case: (IHe (Theta ++ Delta)
                  (consMap s (fun n => wk (length Theta) (sigma n)))
                  (rho, eta a) Hsub_ext) => w [Hw Hrelw].
        exists w. split.
        -- unfold f.
           apply Oeq_trans with (y := @SemT (length Gamma0).+1 e (rho, eta a)).
           ++ exact: (@AppV_inFun_F (length Gamma0) e rho a).
           ++ exact Hw.
        -- rewrite wk_subT.
           change ((Theta ++ Delta) ⊩
                     APP (FUN (subT (liftSub (fun n => wk (length Theta) (sigma n))) e)) s
                     ∼ w ⦂ theta0).
           have HsubOK : SubOKP (Theta ++ Delta) Gamma0
                           (fun n => wk (length Theta) (sigma n)).
           { exact: (SubRel_SubOKP Hsub_w). }
           case: (TypeJudge_subP He (SubOKP_lift HsubOK)) => [Hbody_ty].
           case: (TermRel_typed Hsa) => [Hs_ty].
           have HEbeta : (Theta ++ Delta) ⊢
                           APP (FUN (subT (liftSub (fun n => wk (length Theta) (sigma n))) e)) s
                           ≡ subT (consMap s idSub)
                               (subT (liftSub (fun n => wk (length Theta) (sigma n))) e)
                           ⦂ theta0.
           { apply: (@Eq_beta (Theta ++ Delta)
                       (subT (liftSub (fun n => wk (length Theta) (sigma n))) e)
                       s theta' theta0 Hbody_ty Hs_ty). }
           rewrite (subT_lift_single s
                      (fun n => wk (length Theta) (sigma n)) e) in HEbeta.
           apply: (TermRel_eq Hrelw). exact: (Eq_sym HEbeta).
  - (* AppRule *) move => Delta sigma rho Hsub.
    case: (IH1 Delta sigma rho Hsub) => d1 [Hd1 Hrel1].
    case: (IH2 Delta sigma rho Hsub) => d2 [Hd2 Hrel2].
    case: Hrel1 => [_ Hfun].
    case: (Hfun nil (subT sigma t2) d2 Hrel2) => w [Happ Hrelw].
    exists w. split.
    + rewrite SemT_APP_equation.
      apply Oeq_trans with (y := AppV (d1, @SemT (length Gamma0) t2 rho)).
      * apply: (AppOp_eval (E:=length Gamma0)
                  (d1:=@SemT (length Gamma0) t1)
                  (η:=rho) (k:=d1) (@SemT (length Gamma0) t2) Hd1).
      * rewrite Hd2. exact Happ.
    + rewrite wk_0 in Hrelw. simpl. exact Hrelw.
Qed.
