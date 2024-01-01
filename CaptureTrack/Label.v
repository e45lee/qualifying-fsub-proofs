(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir
     Arthur Charg\'eraud *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Max.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Equalities.

Require Import Coq.FSets.FSets.
Require Import FqMeta.CoqListFacts.
Require Import FqMeta.FSetExtra.
Require Import FqMeta.FSetWeakNotin.
Require Import FqMeta.LibTactics.

Require Import Lia.

(* ********************************************************************** *)
(** * Defining labels *)

(** Labels are structureless objects such that we can always generate
    one fresh from a finite collection.  Equality on labels is [eq] and
    decidable.  We use Coq's module system to make abstract the
    implementation of labels. *)

Module Type LABEL <: UsualDecidableType.

  Parameter label : Set.
  Definition t := label.

  Parameter eq_dec : forall x y : label, {x = y} + {x <> y}.

  Parameter label_fresh_for_list :
    forall (xs : list t), {x : label | ~ List.In x xs}.

  Parameter fresh : list label -> label.

  Parameter fresh_permute : forall l1 l2,
    (forall l, In l l1 <-> In l l2) ->
    fresh l1 = fresh l2.

  Parameter fresh_not_in : forall l, ~ In (fresh l) l.

  Parameter nat_of : label -> nat.

  #[global]
  Hint Resolve eq_dec : core.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

End LABEL.

(** The implementation of the above interface is hidden for
    documentation purposes. *)

Module Label : LABEL.

  (* begin hide *)
  Definition label := nat.
  Definition t := label.

  Definition eq_dec := eq_nat_dec.

  Lemma max_lt_r : forall x y z,
    x <= z -> x <= max y z.
  Proof.
    induction x. auto with arith.
    induction y. auto with arith.
      simpl. induction z. lia. auto with arith.
  Qed.

  Lemma nat_list_max : forall (xs : list nat),
    { n : nat | forall x, List.In x xs -> x <= n }.
  Proof with eauto; auto with arith.
    intros.
    exists (list_max xs).
    intros.
    induction xs; subst...
    * inversion H.
    * inversion H; subst...
      simpl in *...
      simpl in *... destruct H; subst...
      apply max_lt_r...
  Defined.

  Lemma label_fresh_for_list :
    forall (xs : list nat), { n : nat | ~ List.In n xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H].
    exists (S x). intros J. lapply (H (S x)). lia. trivial.
  Defined.

  Definition fresh (l : list label) :=
    match label_fresh_for_list l with
      (exist _ x _) => x
    end.

  Lemma max_list_of_in : forall x l,
    In x l ->
    x <= list_max l.
  Proof with eauto.
    intros.
    unshelve epose proof ((proj1 (list_max_le l (list_max l))) _)
      as InMax...
    unshelve epose proof (proj1 (Forall_forall _ l) InMax)...
  Qed.

  Lemma fresh_permute : forall l1 l2,
    (forall l, In l l1 <-> In l l2) ->
    fresh l1 = fresh l2.
  Proof with eauto.
    intros; unfold fresh, label_fresh_for_list; simpl;
      f_equal...
    enough (list_max l1 <= list_max l2 /\ list_max l2 <= list_max l1) by
      intuition.
    split; apply list_max_le; apply Forall_forall; intros;
      apply H in H0; apply max_list_of_in...
  Qed.

  Lemma fresh_not_in : forall l, ~ In (fresh l) l.
  Proof.
    intro l. unfold fresh.
    destruct label_fresh_for_list. auto.
  Qed.

  Definition nat_of := fun (x : label) => x.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

  (* end hide *)

End Label.

(** We make [label], [fresh], [fresh_not_in] and [label_fresh_for_list] available
    without qualification. *)

Notation label := Label.label.
Notation fresh := Label.fresh.
Notation fresh_not_in := Label.fresh_not_in.
Notation label_fresh_for_list := Label.label_fresh_for_list.

(* Automatically unfold Label.eq *)
Global Arguments Label.eq /.

(** It is trivial to declare an instance of [EqDec] for [label]. *)

#[export] Instance EqDec_label : @EqDec label eq eq_equivalence.
Proof. exact Label.eq_dec. Defined.


(* ********************************************************************** *)
(** * Finite sets of labels *)

(** We use our implementation of labels to obtain an implementation of
    finite sets of labels.  We give the resulting type an intuitive
    name, as well as import names of set operations for use within
    this library.  In order to avoid polluting Coq's namespace, we do
    not use [Module Export]. *)

Module Import LabelSetImpl : FSetExtra.WSfun Label :=
  FSetExtra.Make Label.

Notation labels :=
  LabelSetImpl.t.

(** The [LabelSetDecide] module provides the [fsetdec] tactic for
    solving facts about finite sets of labels. *)


Module Import LabelSetDecide := Coq.FSets.FSetDecide.WDecide_fun Label LabelSetImpl.
Export (hints) LabelSetDecide.

(** The [LabelSetNotin] module provides the [destruct_notin] and
    [solve_notin] for reasoning about non-membership in finite sets of
    labels, as well as a variety of lemmas about non-membership. *)

Module Import LabelSetNotin := FSetWeakNotin.Notin_fun Label LabelSetImpl.
Export (hints) LabelSetNotin.

(** Given the [fsetdec] tactic, we typically do not need to refer to
    specific lemmas about finite sets.  However, instantiating
    functors from the FSets library makes a number of setoid rewrites
    available.  These rewrites are crucial to developments since they
    allow us to replace a set with an extensionally equal set (see the
    [Equal] relation on finite sets) in propositions about finite
    sets. *)

Module LabelSetFacts := FSetFacts.WFacts_fun Label LabelSetImpl.
Module LabelSetProperties := FSetProperties.WProperties_fun Label LabelSetImpl.

Export (hints) LabelSetFacts.
Export (hints) LabelSetProperties.

(* ********************************************************************** *)
(** * Properties *)

(** For any given finite set of labels, we can generate an label fresh
    for it. *)

Lemma label_fresh : forall L : labels, { x : label | ~ In x L }.
Proof.
  intros L. destruct (label_fresh_for_list (elements L)) as [a H].
  exists a. intros J. contradiction H.
  rewrite <- CoqListFacts.InA_iff_In. auto using elements_1.
Qed.


(* ********************************************************************** *)
(** * Tactic support for picking fresh labels *)

(* begin hide *)

(** The auxiliary tactic [simplify_list_of_label_sets] takes a list of
    finite sets of labels and unions everything together, returning the
    resulting single finite set. *)

Ltac simplify_list_of_label_sets L :=
  let L := eval simpl in L in
  let L := ltac_remove_dups L in
  let L := eval simpl in (List.fold_right union empty L) in
  match L with
    | context C [union ?E empty] => context C [ E ]
  end.

(* end hide *)

(** [gather_labels_with F] returns the union of all the finite sets
    [F x] where [x] is a variable from the context such that [F x]
    type checks. *)

Ltac gather_labels_with F :=
  let apply_arg x :=
    match type of F with
      | _ -> _ -> _ -> _ => constr:(@F _ _ x)
      | _ -> _ -> _ => constr:(@F _ x)
      | _ -> _ => constr:(@F x)
    end in
  let rec gather V :=
    match goal with
      | H : _ |- _ =>
        let FH := apply_arg H in
        match V with
          | context [FH] => fail 1
          | _ => gather (union FH V)
        end
      | _ => V
    end in
  let L := gather empty in eval simpl in L.

(** [beautify_fset V] assumes that [V] is built as a union of finite
    sets and returns the same set cleaned up: empty sets are removed
    and items are laid out in a nicely parenthesized way. *)

Ltac beautify_fset V :=
  let rec go Acc E :=
     match E with
     | union ?E1 ?E2 => let Acc2 := go Acc E2 in go Acc2 E1
     | empty => Acc
     | ?E1 => match Acc with
                | empty => E1
                | _ => constr:(union E1 Acc)
              end
     end
  in go empty V.

(** The tactic [pick fresh Y for L] takes a finite set of labels [L]
    and a fresh name [Y], and adds to the context an label with name
    [Y] and a proof that [~ In Y L], i.e., that [Y] is fresh for [L].
    The tactic will fail if [Y] is already declared in the context.

    The variant [pick fresh Y] is similar, except that [Y] is fresh
    for "all labels in the context."  This version depends on the
    tactic [gather_labels], which is responsible for returning the set
    of "all labels in the context."  By default, it returns the empty
    set, but users are free (and expected) to redefine it. *)

Ltac gather_labels :=
  constr:(empty).

Tactic Notation "pick" "fresh" "label" ident(Y) "for" constr(L) :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  (destruct (label_fresh L) as [Y Fr]).

Tactic Notation "pick" "fresh" "label" ident(Y) :=
  let L := gather_labels in
  pick fresh label Y for L.

Ltac pick_fresh_label y :=
  pick fresh label y.

(** Example: We can redefine [gather_labels] to return all the
    "obvious" labels in the context using the [gather_labels_with] thus
    giving us a "useful" version of the "[pick fresh]" tactic. *)

Ltac gather_labels ::=
  let A := gather_labels_with (fun x : labels => x) in
  let B := gather_labels_with (fun x : label => singleton x) in
  constr:(union A B).

Lemma example_pick_fresh_use : forall (x y z : label) (L1 L2 L3: labels), True.
(* begin show *)
Proof.
  intros x y z L1 L2 L3.
  pick fresh label k.

  (** At this point in the proof, we have a new label [k] and a
      hypothesis [Fr] that [k] is fresh for [x], [y], [z], [L1], [L2],
      and [L3]. *)

  trivial.
Qed.
(* end show *)
