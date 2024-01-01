(** This file's definitions taken from [1].
    Only standard lattice definitions are found in this file.
    
    [1] -- John Wiegley, A Reflection-based Proof Tactic for Lattices in Coq, 2022. 
           https://github.com/jwiegley/coq-lattice
*)

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Wellfounded.Lexicographic_Product.

Generalizable All Variables.

Reserved Infix "⊓" (at level 40, left associativity).
Reserved Infix "⊔" (at level 36, left associativity).

Class Lattice (A : Type) := {
  meet : A -> A -> A where "x ⊓ y" := (meet x y);
  join : A -> A -> A where "x ⊔ y" := (join x y);
  top : A;
  bot : A;

  meet_commutative : forall a b, a ⊓ b = b ⊓ a;
  meet_associative : forall a b c, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c);
  meet_absorptive  : forall a b, a ⊓ (a ⊔ b) = a;
  meet_idempotent  : forall a, a ⊓ a = a;

  join_commutative : forall a b, a ⊔ b = b ⊔ a;
  join_associative : forall a b c, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c);
  join_absorptive  : forall a b, a ⊔ (a ⊓ b) = a;
  join_idempotent  : forall a, a ⊔ a = a;

  meet_top : forall a, a ⊓ top = a;
  meet_bot : forall a, a ⊓ bot = bot;
  join_top : forall a, a ⊔ top = top;
  join_bot : forall a, a ⊔ bot = a;

  nontrivial : top <> bot
}.

Infix "⊓" := meet (at level 40, left associativity).
Infix "⊔" := join (at level 36, left associativity).

Class Order (A : Set) := {
  ord : relation A;

  reflexive :> Reflexive ord;
  antisymmetric : forall {x y}, ord x y -> ord y x -> x = y;
  transitive :> Transitive ord
}.

Infix "≤" := ord (at level 50).

Class LOSet {A : Set} `(@Order A) `(@Lattice A) := {
  meet_consistent : forall a b, a ≤ b <-> a = a ⊓ b;
  join_consistent : forall a b, a ≤ b <-> b = a ⊔ b
}.

Section Lattice.

Context `{O : Order A}.
Context `{L : Lattice A}.
Context `{@LOSet A O L}.

Theorem meet_is_glb : forall a b : A,
  forall x, x ≤ a /\ x ≤ b <-> x ≤ a ⊓ b.
Proof.
  split; intros.
    intuition.
    apply meet_consistent in H1.
    apply meet_consistent in H2.
    apply meet_consistent.
    rewrite <- meet_associative, <- H1.
    assumption.
  apply meet_consistent in H0.
  rewrite H0; clear H0.
  split; apply meet_consistent.
    rewrite meet_associative.
    rewrite (meet_commutative (a ⊓ b) a).
    rewrite <- (meet_associative a).
    rewrite meet_idempotent.
    reflexivity.
  rewrite meet_associative.
  rewrite meet_associative.
  rewrite meet_idempotent.
  reflexivity.
Qed.

Theorem meet_prime : forall a b : A,
  forall x, a ≤ x \/ b ≤ x -> a ⊓ b ≤ x.
Proof.
  intros.
  destruct H0;
  apply meet_consistent in H0;
  apply meet_consistent; [rewrite meet_commutative|];
  rewrite meet_associative;
  rewrite <- H0; reflexivity.
Qed.

Theorem join_is_lub : forall a b : A,
  forall x, a ≤ x /\ b ≤ x <-> a ⊔ b ≤ x.
Proof.
  split; intros.
    intuition.
    apply join_consistent in H1.
    apply join_consistent in H2.
    apply join_consistent.
    rewrite join_associative, <- H2.
    assumption.
  apply join_consistent in H0.
  rewrite H0; clear H0.
  split; apply join_consistent.
    rewrite <- join_associative.
    rewrite <- join_associative.
    rewrite join_idempotent.
    reflexivity.
  rewrite (join_commutative a b).
  rewrite <- join_associative.
  rewrite <- join_associative.
  rewrite join_idempotent.
  reflexivity.
Qed.

Theorem join_prime : forall a b : A,
  forall x, x ≤ a \/ x ≤ b -> x ≤ a ⊔ b.
Proof.
  intros.
  destruct H0;
  apply join_consistent in H0;
  apply join_consistent; [|rewrite join_commutative];
  rewrite <- join_associative;
  rewrite <- H0; reflexivity.
Qed.

Lemma lattice_gt_top : forall b : A,
  ord top b ->
  top = b.
Proof with eauto.
  intros * Ord.
  apply join_consistent in Ord.
  rewrite Ord;
  rewrite join_commutative;
  rewrite join_top...
Qed.

Lemma lattice_lt_bot : forall b : A,
  ord b bot ->
  bot = b.
Proof with eauto.
  intros * Ord.
  apply meet_consistent in Ord.
  rewrite Ord;
  rewrite meet_bot...
Qed.

End Lattice.