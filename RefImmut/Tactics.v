(** Helper tactic definitions for Fsub.RefImmut.

    Authors: Edward Lee, Ondrej Lhotak, Yaoyu Zhao

    This work is based off the POPL'08 Coq tutorial
    authored by: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    This file contains a number of definitions, tactics, and lemmas
    that are based only on the syntax of the language at hand.  While
    the exact statements of everything here would change for a
    different language, the general structure of this file (i.e., the
    sequence of definitions, tactics, and lemmas) would remain the
    same.

    Table of contents:
      - #<a href="##fv">Free variables</a>#
      - #<a href="##subst">Substitution</a>#
      - #<a href="##gather_atoms">The "gather_atoms" tactic</a>#
      - #<a href="##properties">Properties of opening and substitution</a>#
      - #<a href="##lc">Local closure is preserved under substitution</a>#
      - #<a href="##nf-properties"> Additional properties of normal forms under opening and substitution</a>#
      - #<a href="##auto">Automation</a>#
      - #<a href="##body">Properties of body_e</a># *)
Require Export Metalib.Metatheory.

Ltac autodestruct_if :=
  repeat match goal with
  | H: context X [?A == ?B] |- _ => destruct ( A === B ); subst; eauto;
    try solve [inversion H]
  end.

(** * Borrowed from
      https://gitlab.mpi-sws.org/iris/stdpp/-/blob/master/theories/tactics.v *)

(** The tactic [select pat tac] finds the last (i.e., bottommost) hypothesis
matching [pat] and passes it to the continuation [tac]. Its main advantage over
using [match goal with ] directly is that it is shorter. If [pat] matches
multiple hypotheses and [tac] fails, then [select tac] will not backtrack on
subsequent matching hypotheses.

The tactic [select] is written in CPS and does not return the name of the
hypothesis due to limitations in the Ltac1 tactic runtime (see
https://gitter.im/coq/coq?at=5e96c82f85b01628f04bbb89). *)
Tactic Notation "select" open_constr(pat) tactic3(tac) :=
  lazymatch goal with
  (** Before running [tac] on the hypothesis [H] we must first unify the
      pattern [pat] with the term it matched against. This forces every evar
      coming from [pat] (and in particular from the holes [_] it contains and
      from the implicit arguments it uses) to be instantiated. If we do not do
      so then shelved goals are produced for every such evar. *)
  | H : pat |- _ => let T := (type of H) in unify T pat; tac H
  end.
(** [select_revert] reverts the first hypothesis matching [pat]. *)
Tactic Notation "revert" "select" open_constr(pat) := select pat (fun H => revert H).

Tactic Notation "rename" "select" open_constr(pat) "into" ident(name) :=
  select pat (fun H => rename H into name).

Tactic Notation "inversion" "select" open_constr(pat) :=
  select pat (fun H => inversion H).

Tactic Notation "destruct" "select" open_constr(pat) :=
  select pat (fun H => destruct H).

Tactic Notation "destruct" "select" open_constr(pat) "as" simple_intropattern(destruct_pat) :=
  select pat (fun H => destruct H as destruct_pat).


