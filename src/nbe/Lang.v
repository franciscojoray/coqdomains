
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
(*** Language Definition ***)
(** *)

(** *Language Syntax *)
Definition Env := nat.

Inductive Var : Env -> Type :=
| ZVAR : forall E, Var (S E)
| SVAR : forall E, Var E -> Var (S E)
.

(** *Definition 36: Syntax *)
Inductive Term E :=
| VAR : Var E     -> Term E
| FUN : Term E.+1 -> Term E
| APP : Term E    -> Term E -> Term E
.

Scheme Term_induction := Induction for Term Sort Prop.

(** *Notation *)
Notation "'v⎨' v ⎬" := (VAR v) (at level 202, no associativity).
Notation "'λ' e" := (FUN e) (at level 1, no associativity).
Infix "@"        := APP (at level 201, left associativity).

(*begin hide*)
(** *MAP Section *)
Section MAP.

  Variable P : Env -> Type.
  Definition Map E E' := Var E -> P E'.
  
  (* Head, tail and cons *)
  Definition tlMap E E' (m:Map (E.+1) E') : Map E E' := fun v => m (SVAR v).
  Definition hdMap E E' (m:Map (E.+1) E') : P E' := m (ZVAR _).
  
  Definition consMap E E' (hd: P E') (tl : Map E E') : Map (E.+1) E' :=
    (fun var =>
       match var in Var p return (Map (p.-1) E') -> P E' with 
       | ZVAR _ => fun _ => hd
       | SVAR _ var' => fun tl' => tl' var'
       end tl). 
  
  Axiom MapExtensional : forall E E' (r1 r2 : Map E E'),
      (forall var, r1 var = r2 var) -> r1 = r2.
  
  Lemma hdConsMap : forall E E' (v : P E') (s : Map E E'), hdMap (consMap v s) = v. 
  Proof. by []. Qed.
  Lemma tlConsMap : forall E E' (v : P E') (s : Map E E'), tlMap (consMap v s) = s. 
  Proof. move => E E' v s. by apply MapExtensional. Qed.

  Import Program.
  Lemma consMapEta : forall E E' (m:Map (E.+1) E'), m = consMap (hdMap m) (tlMap m).
  Proof. move => E E' m. apply MapExtensional.
         intro. by dependent destruction var. 
  Qed.
  
  (*==========================================================================
    Package of operations used with a Map
      vr maps a Var into Var or Value (so is either the identity or TVAR)
      vl maps a Var or Value to a Value (so is either TVAR or the identity)
      wk weakens a Var or Value (so is either SVAR or renaming through SVAR on a value)
    ==========================================================================*)
  Record MapOps :=
    {
      vr : forall E, Var E -> P E;   
      vl : forall E, P E -> Term E;
      wk : forall E, P E -> P (E.+1);
      wkvr : forall E (var : Var E), wk (vr var) = vr (SVAR var);
      vlvr : forall E (var : Var E), vl (vr var) = VAR var
    }.
  Variable ops : MapOps.
  
  Definition lift E E' (m : Map E E') : Map (E.+1) (E'.+1) :=
    (fun var => match var in Var p return Map (p.-1) E' -> P (E'.+1) with
             | ZVAR _ => fun _ => vr ops (ZVAR _)
             | SVAR _ x => fun m => wk ops (m x)
             end m).
  
  Definition shiftMap E E' (m : Map E E') : Map E (E'.+1) :=
    fun var => wk ops (m var).
  Definition idMap E : Map E E := fun (var : Var E) => vr ops var.
  
  Lemma shiftConsMap :
    forall E E' (m : Map E E') (x : P E'),
    shiftMap (consMap x m) = consMap (wk ops x) (shiftMap m). 
  Proof. intros E E' m x. apply MapExtensional. by dependent destruction var. Qed.
  
  Lemma LiftMapDef :
    forall E E' (m : Map E' E), lift m = consMap (vr ops (ZVAR _)) (shiftMap m).
  Proof. intros. apply MapExtensional. by dependent destruction var. Qed.
  
  Fixpoint trav {E E'} (t : Term E) (m : Map E E') : Term E' :=
    match t with
    | VAR v    => vl ops (m v)
    | FUN e    => FUN (trav e (lift m))
    | APP t r  => APP (trav t m) (trav r m)
    end.
  
  Definition mapT E E' m t := @trav E E' t m.
  
  Variable E E' : Env.
  Variable m : Map E E'.
  
  Lemma mapVAR : forall (var : Var _),
      mapT m (VAR var) = vl ops (m var).
  Proof.
    intro. unfold mapT. by unfold trav.
  Qed.
  
  Lemma mapFUN : forall (e : Term _),
      mapT m (FUN e) = FUN (mapT (lift m) e).
  Proof.
    intros e. unfold mapT. by simpl.
  Qed.
  
  Lemma mapAPP : forall (t t' : Term _),
      mapT m (APP t t') = APP (mapT m t) (mapT m t').
  Proof.
    intros t t'. unfold mapT. by simpl.
  Qed.
    
  Lemma liftIdMap : lift (@idMap E) = @idMap (E.+1).
  Proof.
    apply MapExtensional. dependent destruction var; [by [] | by apply wkvr].  
  Qed.
  
  Lemma idMapDef :
    @idMap (E.+1) = consMap (vr ops (ZVAR _)) (shiftMap (@idMap E)).
  Proof.
    apply MapExtensional. dependent destruction var; first by [].
    unfold idMap, shiftMap. simpl. by rewrite wkvr.
  Qed.

End MAP.
  
Hint Rewrite mapVAR mapFUN mapAPP : mapHints.

Arguments idMap [P] _ _ _.

Lemma applyIdMap P (ops:MapOps P) E : 
  forall (t : Term E), mapT ops (idMap ops E) t = t.
Proof.
  move => t. elim: t.
  - Case VAR.
      move => E0 v.
      rewrite -> mapVAR.
      apply vlvr.
  - Case FUN.
      move => E0 e H.
      rewrite -> mapFUN.
      repeat (rewrite -> liftIdMap).
        by rewrite -> H.
  - Case APP.
      move => E0 t1 H t2 H0.
      rewrite -> mapAPP.
      rewrite -> H.
        by rewrite -> H0.
Qed.

(** *RENAMING Section *)
Definition Ren := Map Var.

(** update for 8.4 *)
Definition RenMapOps := (@Build_MapOps _ (fun _ v => v)
                                      VAR SVAR
                                      (fun _ _ => Logic.eq_refl)
                                      (fun _ _ => Logic.eq_refl)
                       ).

Definition renT := mapT RenMapOps.
Definition liftRen := lift RenMapOps.
Definition shiftRen := shiftMap RenMapOps.
Definition idRen := idMap RenMapOps.
Arguments idRen : clear implicits.

(*==========================================================================
  Composition of renaming
  ==========================================================================*)

Definition composeRen P E E' E''
           (m : Map P E' E'') (r : Ren E E') : Map P E E''
  := fun var => m (r var). 

Lemma liftComposeRen : forall P ops E E' E''
                         (m:Map P E' E'') (r:Ren E E'),
    lift ops (composeRen m r) = composeRen (lift ops m) (liftRen r).
Proof. intros. apply MapExtensional. by dependent destruction var. Qed.

Lemma applyComposeRen E : 
  forall (t : Term E) P ops E' E'' (m:Map P E' E'') (s : Ren E E'),
      mapT ops (composeRen m s) t = mapT ops m (renT s t).
Proof.
  move => t. elim: t.
  - Case VAR.
      move => E0 v P ops E' E'' m s.
      rewrite -> mapVAR.
      unfold renT. repeat (rewrite -> mapVAR).
        by unfold composeRen.
  - Case FUN.
      move => E0 e H P ops E' E'' m s.
      unfold renT.
      repeat (rewrite -> mapFUN).
      repeat (rewrite -> liftComposeRen).
        by rewrite -> H.
  - Case APP.
      move => E0 t1 H t2 H0 P ops E' E'' m s.
      unfold renT.
      repeat (rewrite -> mapAPP).
      rewrite -> H.
        by rewrite -> H0.
Qed.

(** *Substitution Section *)
Definition Sub := Map Term.
(** update for 8.4 *)

Definition SubMapOps : MapOps Term :=
  (@Build_MapOps _ VAR (fun _ v => v)
                 (fun E => renT (fun v => SVAR v))
                 (fun _ _ => Logic.eq_refl)
                 (fun _ _ => Logic.eq_refl)
  ).

Definition subT := mapT SubMapOps.
Definition shiftSub := shiftMap SubMapOps.
Definition liftSub := lift SubMapOps.
Definition idSub := idMap SubMapOps.
Arguments idSub : clear implicits.

(** *Notation *)
Notation "[ x , .. , y ]" :=
  (consMap x .. (consMap y (idSub _)) ..) : Sub_scope.
Delimit Scope Sub_scope with subst.
Arguments subT _ _ _%Sub_scope _.

Notation "t ⎧ δ ⎫" := (@subT _ _ δ t) (at level 1, no associativity).

Ltac UnfoldRenSub := (unfold subT; unfold renT; unfold liftSub; unfold liftRen).
Ltac FoldRenSub := (fold subT; fold renT; fold liftSub; fold liftRen).
Ltac SimplMap := (UnfoldRenSub; autorewrite with mapHints; FoldRenSub).

(*==========================================================================
  Composition of substitution followed by renaming
  ==========================================================================*)

Definition composeRenSub E E' E'' (r : Ren E' E'') (s : Sub E E') : Sub E E'' :=
  fun var => renT r (s var)
.

Lemma liftComposeRenSub : forall E E' E'' (r:Ren E' E'') (s:Sub E E'),
    liftSub (composeRenSub r s) = composeRenSub (liftRen r) (liftSub s).
Proof.
  intros. apply MapExtensional. dependent destruction var; first by [].
  simpl. unfold composeRenSub. unfold liftSub. unfold renT at 1.
  rewrite <- (applyComposeRen _). unfold lift. simpl wk. unfold renT.
  rewrite <- (applyComposeRen _). reflexivity.
Qed.

Lemma applyComposeRenSub E : 
  forall (t : Term E) E' E'' (r : Ren E' E'') (s : Sub E E'),
      subT (composeRenSub r s) t = renT r (subT s t).
Proof.
  move => t. elim: t.
  - Case VAR.
      move => E0 v E' E'' r s. by SimplMap.
  - Case FUN.
      move => E0 e H E' E'' r s.
      unfold "_ ⎧ _ ⎫".
      rewrite -> mapFUN.
      repeat (rewrite -> liftComposeRenSub).
        by rewrite -> H.
  - Case APP.
      move => E0 t1 H t2 H0 E' E'' r s.
      unfold "_ ⎧ _ ⎫".
      repeat (rewrite -> mapAPP).
      rewrite -> H.
        by rewrite -> H0.
Qed.

(*==========================================================================
  Composition of substitutions
  ==========================================================================*)

Definition composeSub E E' E'' (s' : Sub E' E'') (s : Sub E E') : Sub E E''
  := fun var => subT s' (s var).
Arguments composeSub _ _ _ _%Sub_scope _%Sub_scope _.

Lemma liftComposeSub : forall E E' E'' (s' : Sub E' E'') (s : Sub E E'),
    liftSub (composeSub s' s) = composeSub (liftSub s') (liftSub s).
Proof.
  intros. apply MapExtensional. dependent destruction var; first by []. 
  unfold composeSub. simpl liftSub.
  rewrite <- (applyComposeRenSub _). unfold composeRenSub. unfold subT.
    by rewrite <- (applyComposeRen _).
Qed.

Lemma substComposeSub E :
  forall (t : Term E) E' E'' (s' : Sub E' E'') (s : Sub E E'),
      subT (composeSub s' s) t = subT s' (subT s t).
Proof.  
  move => t. elim: t.
  - Case VAR.
      move => E0 v E' E'' s' s.
      unfold "_ ⎧ _ ⎫".
        by repeat (rewrite -> mapVAR).
  - Case FUN.
      move => E0 e H E' E'' s' s.
      unfold "_ ⎧ _ ⎫".
      repeat (rewrite -> mapFUN).
      repeat (rewrite -> liftComposeSub).
        by rewrite -> H.
  - Case APP.
      move => E0 t1 H t2 H0 E' E'' s' s.
      unfold "_ ⎧ _ ⎫".
      repeat (rewrite -> mapAPP).
      rewrite -> H.
        by rewrite -> H0.
Qed.

(** updated for 8.4 *)
Lemma composeCons : forall E E' E'' (s':Sub E' E'') (s:Sub E E') (v:Term _), 
    composeSub (consMap v s') (liftSub s) = consMap v (composeSub s' s).
  intros. apply MapExtensional. dependent destruction var; first by [].
  unfold composeSub. simpl consMap. unfold subT. unfold liftSub.
  unfold lift. simpl wk. rewrite <- (applyComposeRen _). 
  unfold composeRen. auto.
Qed.

Lemma composeSubIdLeft : forall E E' (s : Sub E E'), composeSub (idSub _) s = s.
Proof. intros. apply MapExtensional.  intros var.
       apply (applyIdMap _ _).
Qed.

Lemma composeSubIdRight : forall E E' (s:Sub E E'), composeSub s (idSub _) = s.
Proof.
  destruct E. by []. by [].
Qed.

(*end hide*)
