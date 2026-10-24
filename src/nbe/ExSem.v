(*begin hide*)

(* Facade: the unindexed NbE development is split by concern (ISSUE-000b).
   This module re-exports the deep modules so existing clients
   (`Require Import ExSem`) keep resolving. *)

Require Export SemOps.
Require Export Semantics.
(*end hide*)
