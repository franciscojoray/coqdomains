
(*begin hide*)
Require Import Utils.

(* new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(* endof new in 8.4 *)

From mathcomp Require Export ssreflect ssrnat ssrbool eqtype seq fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*end hide*)

Require Import Program.

(** *)
(*** Language Definition (unindexed) ***)
(** *)

(** *Language Syntax *)
(* Environment sizes are still needed for the SEMANTIC environments
   (SemEnv E); they no longer index the syntax. *)
Definition Env := nat.

(* De Bruijn indices as plain naturals; index 0 is the freshest (innermost)
   variable — the legacy ZVAR.  Terms are context-free: the same term may be
   discussed in an environment of any size. *)
Definition Var := nat.

(** *Syntax *)
Inductive Term :=
| VAR : Var -> Term
| FUN : Term -> Term
| APP : Term -> Term -> Term
.

Scheme Term_induction := Induction for Term Sort Prop.

(** *Notation *)
Notation "'λ' e" := (FUN e) (at level 1, no associativity).
Infix "@"        := APP (at level 201, left associativity).

(** *Sanity checks *)
Check FUN (VAR 0).
Check APP (VAR 0) (VAR 1).
Check λ (VAR 0).
Check λ (APP (VAR 1) (VAR 0 @ VAR 1)).

(*begin hide*)
(** *MAP Section *)
Section MAP.

  Variable P : Type.
  Definition Map := Var -> P.

  (* Head, tail and cons *)
  Definition tlMap (m:Map) : Map := fun n => m (S n).
  Definition hdMap (m:Map) : P := m 0.
  Definition consMap (hd: P) (tl : Map) : Map :=
    fun n => match n with
             | O => hd
             | S n' => tl n'
             end.

  Axiom MapExtensional : forall (r1 r2 : Map),
      (forall n, r1 n = r2 n) -> r1 = r2.

  Lemma hdConsMap : forall (v : P) (s : Map), hdMap (consMap v s) = v.
  Proof. by []. Qed.
  Lemma tlConsMap : forall (v : P) (s : Map), tlMap (consMap v s) = s.
  Proof. move => v s. by apply MapExtensional. Qed.

  Import Program.
  Lemma consMapEta : forall (m:Map), m = consMap (hdMap m) (tlMap m).
  Proof. move => m. apply MapExtensional. move => n. by case: n. Qed.

  (*==========================================================================
    Package of operations used with a Map
      vr embeds a Var into P
      vl maps a P back into a Term
      wk weakens a P (for going under a binder)
    ==========================================================================*)
  Record MapOps :=
    {
      vr : Var -> P;
      vl : P -> Term;
      wk : P -> P;
      wkvr : forall (n : Var), wk (vr n) = vr (S n);
      vlvr : forall (n : Var), vl (vr n) = VAR n
    }.
  Variable ops : MapOps.

  Definition lift (m : Map) : Map :=
    fun n => match n with
             | O => vr ops 0
             | S n' => wk ops (m n')
             end.

  Definition shiftMap (m : Map) : Map := fun n => wk ops (m n).
  Definition idMap : Map := vr ops.

  Lemma shiftConsMap :
    forall (m : Map) (x : P),
    shiftMap (consMap x m) = consMap (wk ops x) (shiftMap m).
  Proof. intros m x. apply MapExtensional. move => n. by case: n. Qed.

  Lemma LiftMapDef :
    forall (m : Map), lift m = consMap (vr ops 0) (shiftMap m).
  Proof. intros m. apply MapExtensional. move => n. by case: n. Qed.

  Fixpoint trav (t : Term) (m : Map) : Term :=
    match t with
    | VAR n    => vl ops (m n)
    | FUN e    => FUN (trav e (lift m))
    | APP t r  => APP (trav t m) (trav r m)
    end.

  Definition mapT (m : Map) (t : Term) : Term := trav t m.

  Variable m : Map.

  Lemma mapVAR : forall (n : Var), mapT m (VAR n) = vl ops (m n).
  Proof.
    intro. unfold mapT. by unfold trav.
  Qed.

  Lemma mapFUN : forall (e : Term),
      mapT m (FUN e) = FUN (mapT (lift m) e).
  Proof.
    intros e. unfold mapT. by [].
  Qed.

  Lemma mapAPP : forall (t t' : Term),
      mapT m (APP t t') = APP (mapT m t) (mapT m t').
  Proof.
    intros t t'. unfold mapT. by [].
  Qed.

  Lemma liftIdMap : lift idMap = idMap.
  Proof.
    apply MapExtensional. move => n. case: n; first by []; by apply wkvr.
  Qed.

  Lemma idMapDef :
    idMap = consMap (vr ops 0) (shiftMap idMap).
  Proof.
    rewrite <- (LiftMapDef idMap). by rewrite liftIdMap.
  Qed.

End MAP.

Hint Rewrite mapVAR mapFUN mapAPP : mapHints.

Arguments idMap [P] _.

Lemma applyIdMap P (ops:MapOps P) :
  forall (t : Term), mapT ops (idMap ops) t = t.
Proof.
  move => t. elim: t.
  - Case VAR.
      move => n.
      rewrite -> mapVAR.
      apply vlvr.
  - Case FUN.
      move => e H.
      rewrite -> mapFUN.
      rewrite -> liftIdMap.
        by rewrite -> H.
  - Case APP.
      move => t1 H t2 H0.
      rewrite -> mapAPP.
      rewrite -> H.
        by rewrite -> H0.
Qed.

(** *RENAMING Section *)
Definition Ren := Map Var.

(* update for 8.4 *)
Definition RenMapOps := (@Build_MapOps Var (fun n => n)
                                      VAR (fun x => S x)
                                      (fun n => Logic.eq_refl)
                                      (fun n => Logic.eq_refl)
                       ).

Definition renT := mapT RenMapOps.
Definition liftRen := lift RenMapOps.
Definition shiftRen := shiftMap RenMapOps.
Definition idRen := idMap RenMapOps.
Arguments idRen : clear implicits.

(*==========================================================================
  Composition of renaming
  ==========================================================================*)

Definition composeRen P (m : Map P) (r : Ren) : Map P
  := fun n => m (r n).

Lemma liftComposeRen : forall P ops (m:Map P) (r:Ren),
    lift ops (composeRen m r) = composeRen (lift ops m) (liftRen r).
Proof. intros. apply MapExtensional. move => n. by case: n. Qed.

Lemma applyComposeRen :
  forall (t : Term) P ops (m:Map P) (s : Ren),
      mapT ops (composeRen m s) t = mapT ops m (renT s t).
Proof.
  move => t. elim: t.
  - Case VAR.
      move => n P ops m s.
      rewrite -> mapVAR.
      unfold renT. repeat (rewrite -> mapVAR).
        by unfold composeRen.
  - Case FUN.
      move => e H P ops m s.
      unfold renT.
      repeat (rewrite -> mapFUN).
      repeat (rewrite -> liftComposeRen).
        by rewrite -> H.
  - Case APP.
      move => t1 H t2 H0 P ops m s.
      unfold renT.
      repeat (rewrite -> mapAPP).
      rewrite -> H.
        by rewrite -> H0.
Qed.

(** *Substitution Section *)
Definition Sub := Map Term.

Definition SubMapOps : MapOps Term :=
  (@Build_MapOps Term VAR (fun t => t)
                 (fun t => renT (fun n => S n) t)
                 (fun n => Logic.eq_refl)
                 (fun n => Logic.eq_refl)
  ).

Definition subT := mapT SubMapOps.
Definition shiftSub := shiftMap SubMapOps.
Definition liftSub := lift SubMapOps.
Definition idSub := idMap SubMapOps.
Arguments idSub : clear implicits.

(* pointwise reduction of the lifted maps *)
Lemma liftSub_O : forall (m : Sub), liftSub m 0 = VAR 0.
Proof. by []. Qed.
Lemma liftSub_S : forall (m : Sub) (n' : Var),
    liftSub m (S n') = renT (fun k => S k) (m n').
Proof. by []. Qed.
Lemma liftRen_O : forall (r : Ren), liftRen r 0 = 0.
Proof. by []. Qed.
Lemma liftRen_S : forall (r : Ren) (n' : Var), liftRen r (S n') = S (r n').
Proof. by []. Qed.

(** *Notation *)
Notation "[ x , .. , y ]" :=
  (consMap x .. (consMap y (idSub)) ..) : Sub_scope.
Delimit Scope Sub_scope with subst.
Arguments subT _%Sub_scope _.

Notation "t ⎧ δ ⎫" := (subT δ t) (at level 1, no associativity).

Ltac UnfoldRenSub := (unfold subT; unfold renT; unfold liftSub; unfold liftRen).
Ltac FoldRenSub := (fold subT; fold renT; fold liftSub; fold liftRen).
Ltac SimplMap := (UnfoldRenSub; autorewrite with mapHints; FoldRenSub).

(*==========================================================================
  Composition of substitution followed by renaming
  ==========================================================================*)

Definition composeRenSub (r : Ren) (s : Sub) : Sub :=
  fun n => renT r (s n)
.

Lemma liftComposeRenSub : forall (r:Ren) (s:Sub),
    liftSub (composeRenSub r s) = composeRenSub (liftRen r) (liftSub s).
Proof.
  intros r s. apply MapExtensional. move => n. case: n; first by []. move => n.
  rewrite liftSub_S. unfold composeRenSub. cbv beta.
  rewrite liftSub_S.
  unfold renT at 1 3.
  rewrite <- (applyComposeRen _). unfold composeRen. cbv beta.
  rewrite <- (applyComposeRen _). unfold composeRen. cbv beta.
  by [].
Qed.

Lemma applyComposeRenSub :
  forall (t : Term) (r : Ren) (s : Sub),
      subT (composeRenSub r s) t = renT r (subT s t).
Proof.
  move => t. elim: t.
  - Case VAR.
      move => n r s. by SimplMap.
  - Case FUN.
      move => e H r s.
      unfold "_ ⎧ _ ⎫".
      rewrite -> mapFUN.
      repeat (rewrite -> liftComposeRenSub).
        by rewrite -> H.
  - Case APP.
      move => t1 H t2 H0 r s.
      unfold "_ ⎧ _ ⎫".
      repeat (rewrite -> mapAPP).
      rewrite -> H.
        by rewrite -> H0.
Qed.

(*==========================================================================
  Composition of substitutions
  ==========================================================================*)

Definition composeSub (s' : Sub) (s : Sub) : Sub
  := fun n => subT s' (s n).
Arguments composeSub _%Sub_scope _%Sub_scope.

Lemma liftComposeSub : forall (s' : Sub) (s : Sub),
    liftSub (composeSub s' s) = composeSub (liftSub s') (liftSub s).
Proof.
  intros s' s. apply MapExtensional. move => n. case: n; first by []. move => n.
  rewrite liftSub_S. unfold composeSub. cbv beta.
  rewrite liftSub_S.
  rewrite <- (applyComposeRenSub _). unfold composeRenSub.
  unfold subT.
  rewrite <- (applyComposeRen _). unfold composeRen. cbv beta.
  by [].
Qed.

Lemma substComposeSub :
  forall (t : Term) (s' : Sub) (s : Sub),
      subT (composeSub s' s) t = subT s' (subT s t).
Proof.
  move => t. elim: t.
  - Case VAR.
      move => n s' s.
      unfold "_ ⎧ _ ⎫".
        by repeat (rewrite -> mapVAR).
  - Case FUN.
      move => e H s' s.
      unfold "_ ⎧ _ ⎫".
      repeat (rewrite -> mapFUN).
      repeat (rewrite -> liftComposeSub).
        by rewrite -> H.
  - Case APP.
      move => t1 H t2 H0 s' s.
      unfold "_ ⎧ _ ⎫".
      repeat (rewrite -> mapAPP).
      rewrite -> H.
        by rewrite -> H0.
Qed.

Lemma composeCons : forall (s' : Sub) (s : Sub) (v : Term),
    composeSub (consMap v s') (liftSub s) = consMap v (composeSub s' s).
Proof.
  intros s' s v. apply MapExtensional. move => n. case: n; first by []. move => n.
  unfold composeSub. cbv beta.
  rewrite liftSub_S.
  cbn [consMap].
  unfold subT.
  rewrite <- (applyComposeRen _). unfold composeRen. cbv beta iota.
  by [].
Qed.

Lemma composeSubIdLeft : forall (s : Sub), composeSub (idSub) s = s.
Proof. intros. apply MapExtensional.  intros n.
       apply (applyIdMap _ _).
Qed.

Lemma composeSubIdRight : forall (s : Sub), composeSub s (idSub) = s.
Proof.
  by [].
Qed.

(** *Sanity computations *)
Compute (renT (fun n => S n) (FUN (VAR 0))).
Compute (renT (fun n => S n) (APP (VAR 0) (VAR 1))).

(*end hide*)
