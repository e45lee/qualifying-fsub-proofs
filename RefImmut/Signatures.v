(* ********************************************************************** *)
(** * Signatures *)
Require Import FqMeta.Metatheory.
Require Import Fsub.RefImmut.Label.

(** We can use our implementation of association lists (in AssocList)
    to implement association lists whose keys are labels.  Thanks to
    parameter inlining, the types in the instantiated functor will all
    use [atom] for the type for keys. *)

Module Import Signatures := AssocList.Make Label LabelSetImpl.
Export (hints) Signatures.


(** We provide alternative names for the tactics on association lists
    to reflect our use of association lists for environments. *)

Ltac simpl_sig :=
  simpl_alist.

Tactic Notation "simpl_sig" "in" hyp(H) :=
  simpl_alist in H.

Tactic Notation "simpl_sig" "in" "*" :=
  simpl_alist in *.

Tactic Notation "rewrite_sig" constr(E) :=
  rewrite_alist E.

Tactic Notation "rewrite_sig" constr(E) "in" hyp(H) :=
  rewrite_alist E in H.

Tactic Notation "sig" "induction" ident(E) :=
  alist induction E.

Tactic Notation "sig" "induction" ident(E) "as" simple_intropattern(P) :=
  alist induction E as P.

(** As an alternative to the [x ~ a] notation, we also provide more
    list-like notation for writing association lists consisting of a
    single binding.

    Implementation note: The following notation overlaps with the
    standard recursive notation for lists, e.g., the one found in the
    Program library of Coq's standard library. *)

Declare Scope sig_scope.

Notation "L[ x ]" := (Signatures.one x) : sig_scope.

Open Scope sig_scope.
