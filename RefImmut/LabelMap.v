(** Label maps (for stores).

*)

Require Import FSets.FMapInterface.
Require Import FSets.FMapFacts.
Require Import Coq.FSets.FMapWeakList.
Require Import Fsub.RefImmut.Label.

Module Import LabelMapImpl : FMapInterface.WSfun Label :=
  FMapWeakList.Make Label.
Module Import LabelMapFacts := FMapFacts.WFacts_fun Label LabelMapImpl.
Notation LabelMap := LabelMapImpl.t.
