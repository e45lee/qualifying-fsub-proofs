(** Infrastructure lemmas and tactic definitions for Fsub.

    Authors: Brian Aydemir and Arthur Chargu\'eraud, with help from
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
      - #<a href="##auto">Automation</a>#
      - #<a href="##body">Properties of body_e</a># *)

Require Export Base.Fsub_LetSum_Definitions.


(* ********************************************************************** *)
(** * #<a name="fv"></a># Free variables *)

(** In this section, we define free variable functions.  The functions
    [fv_tt] and [fv_te] calculate the set of atoms used as free type
    variables in a type or expression, respectively.  The function
    [fv_ee] calculates the set of atoms used as free expression
    variables in an expression.  Cases involving binders are
    straightforward since bound variables are indices, not names, in
    locally nameless representation. *)

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_bvar J => {}
  | typ_fvar X => {{ X }}
  | typ_arrow T1 T2 => (fv_tqt T1) `union` (fv_tqt T2)
  | typ_all T1 T2 => (fv_tt T1) `union` (fv_tqt T2)
  | typ_qall Q T  => (fv_tqt T)
  | typ_sum T1 T2 => (fv_tqt T1) `union` (fv_tqt T2)
  | typ_pair T1 T2 => (fv_tqt T1) `union` (fv_tqt T2)
  | typ_ref T1 => (fv_tqt T1)
  end
with fv_tqt (T : qtyp) {struct T} : atoms :=
  match T with
  | qtyp_qtyp Q T => (fv_tt T)
  end.

Fixpoint fv_te (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => {}
  | exp_abs P V e1  => (fv_tqt V) `union` (fv_te e1)
  | exp_app e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_tabs P V e1 => (fv_tt V) `union` (fv_te e1)
  | exp_tapp e1 V => (fv_tt V) `union` (fv_te e1)
  | exp_qabs P V e1 => (fv_te e1)
  | exp_qapp e1 V => (fv_te e1)
  | exp_let e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_inl P e1 => (fv_te e1)
  | exp_inr P e1 => (fv_te e1)
  | exp_case e1 e2 e3 => (fv_te e1) `union` (fv_te e2) `union` (fv_te e3)
  | exp_pair P e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_first e1 => (fv_te e1)
  | exp_second e1 => (fv_te e1)
  | exp_ref P e1 => (fv_te e1)
  | exp_ref_label P l => {}
  | exp_deref e1 => (fv_te e1)
  | exp_set_ref e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_upqual P e1 => (fv_te e1)
  | exp_check P e1 => (fv_te e1)
  end.

Fixpoint fv_qq (Q : qua) {struct Q} : atoms :=
  match Q with
  | qua_top => {}
  | qua_bot => {}
  | qua_bvar i => {}
  | qua_fvar X => {{ X }}
  | qua_meet Q1 Q2 => fv_qq Q1 `union` fv_qq Q2
  | qua_join Q1 Q2 => fv_qq Q1 `union` fv_qq Q2
  end.

Fixpoint fv_qt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_bvar J => {}
  | typ_fvar X => {}
  | typ_arrow T1 T2 => (fv_qqt T1) `union` (fv_qqt T2)
  | typ_all T1 T2 => (fv_qt T1) `union` (fv_qqt T2)
  | typ_qall Q T  => (fv_qq Q) `union` (fv_qqt T)
  | typ_sum T1 T2 => (fv_qqt T1) `union` (fv_qqt T2)
  | typ_pair T1 T2 => (fv_qqt T1) `union` (fv_qqt T2)
  | typ_ref T1 => fv_qqt T1
  end
with fv_qqt (T : qtyp) {struct T} : atoms :=
  match T with
  | qtyp_qtyp Q T => (fv_qq Q) `union` (fv_qt T)
  end.

Fixpoint fv_qe (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => {}
  | exp_abs P V e1  => (fv_qq P) `union` (fv_qqt V) `union` (fv_qe e1)
  | exp_app e1 e2 => (fv_qe e1) `union` (fv_qe e2)
  | exp_tabs P V e1 => (fv_qq P) `union` (fv_qt V) `union` (fv_qe e1)
  | exp_tapp e1 V => (fv_qt V) `union` (fv_qe e1)
  | exp_qabs P V e1 => (fv_qq P) `union` (fv_qe e1) `union` (fv_qq V)
  | exp_qapp e1 V => (fv_qe e1) `union` (fv_qq V)
  | exp_let e1 e2 => (fv_qe e1) `union` (fv_qe e2)
  | exp_inl P e1 => (fv_qq P) `union` (fv_qe e1)
  | exp_inr P e1 => (fv_qq P) `union` (fv_qe e1)
  | exp_case e1 e2 e3 => (fv_qe e1) `union` (fv_qe e2) `union` (fv_qe e3)
  | exp_pair P e1 e2 => (fv_qq P) `union` (fv_qe e1) `union` (fv_qe e2)
  | exp_first e1 => (fv_qe e1)
  | exp_second e1 => (fv_qe e1)
  | exp_ref P e1 => (fv_qq P) `union` (fv_qe e1)
  | exp_ref_label P l => (fv_qq P)
  | exp_deref e1 => (fv_qe e1)
  | exp_set_ref e1 e2 => (fv_qe e1) `union` (fv_qe e2)
  | exp_upqual P e1 => (fv_qq P) `union` (fv_qe e1)
  | exp_check P e1 => (fv_qq P) `union` (fv_qe e1)
  end.

Fixpoint fv_ee (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => {{ x }}
  | exp_abs P V e1 => (fv_ee e1)
  | exp_app e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_tabs P V e1 => (fv_ee e1)
  | exp_tapp e1 V => (fv_ee e1)
  | exp_qabs P V e1 => (fv_ee e1)
  | exp_qapp e1 V => (fv_ee e1)
  | exp_let e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_inl P e1 => (fv_ee e1)
  | exp_inr P e1 => (fv_ee e1)
  | exp_case e1 e2 e3 => (fv_ee e1) `union` (fv_ee e2) `union` (fv_ee e3)
  | exp_pair P e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_first e1 => (fv_ee e1)
  | exp_second e1 => (fv_ee e1)
  | exp_ref P e1 => (fv_ee e1)
  | exp_ref_label P l => {}
  | exp_deref e1 => (fv_ee e1)
  | exp_set_ref e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_upqual P e1 => (fv_ee e1)
  | exp_check P e1 => (fv_ee e1)
  end.


(* ********************************************************************** *)
(** * #<a name="subst"></a># Substitution *)

(** In this section, we define substitution for expression and type
    variables appearing in types, expressions, and environments.
    Substitution differs from opening because opening replaces indices
    whereas substitution replaces free variables.  The definitions
    below are relatively simple for two reasons.
      - We are using locally nameless representation, where bound
        variables are represented using indices.  Thus, there is no
        need to rename variables to avoid capture.
      - The definitions below assume that the term being substituted
        in, i.e., the second argument to each function, is locally
        closed.  Thus, there is no need to shift indices when passing
        under a binder. *)

Fixpoint subst_tt (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then U else T
  | typ_arrow T1 T2 => typ_arrow (subst_tqt Z U T1) (subst_tqt Z U T2)
  | typ_all T1 T2 => typ_all (subst_tt Z U T1) (subst_tqt Z U T2)
  | typ_qall Q T => typ_qall Q (subst_tqt Z U T)
  | typ_sum T1 T2 => typ_sum (subst_tqt Z U T1) (subst_tqt Z U T2)
  | typ_pair T1 T2 => typ_pair (subst_tqt Z U T1) (subst_tqt Z U T2)
  | typ_ref T1 => typ_ref (subst_tqt Z U T1)
  end
with subst_tqt (Z : atom) (U : typ) (T : qtyp) {struct T} : qtyp :=
  match T with
  | qtyp_qtyp Q T => qtyp_qtyp Q (subst_tt Z U T)
  end
  .

Fixpoint subst_qq (Z : atom) (U : qua) (T : qua) {struct T} : qua :=
  match T with
  | qua_top => qua_top
  | qua_bvar J => qua_bvar J
  | qua_fvar X => if X == Z then U else T
  | qua_meet T1 T2 => qua_meet (subst_qq Z U T1) (subst_qq Z U T2)
  | qua_join T1 T2 => qua_join (subst_qq Z U T1) (subst_qq Z U T2)
  | qua_bot => qua_bot
  end.

Fixpoint subst_qt (Z : atom) (U : qua) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => typ_bvar J
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (subst_qqt Z U T1) (subst_qqt Z U T2)
  | typ_all T1 T2 => typ_all (subst_qt Z U T1) (subst_qqt Z U T2)
  | typ_qall Q T => typ_qall (subst_qq Z U Q) (subst_qqt Z U T)
  | typ_sum T1 T2 => typ_sum (subst_qqt Z U T1) (subst_qqt Z U T2)
  | typ_pair T1 T2 => typ_pair (subst_qqt Z U T1) (subst_qqt Z U T2)
  | typ_ref T1 => typ_ref (subst_qqt Z U T1)
  end
with subst_qqt (Z : atom) (U : qua) (T : qtyp) {struct T} : qtyp :=
  match T with
  | qtyp_qtyp Q T => qtyp_qtyp (subst_qq Z U Q) (subst_qt Z U T)
  end.

Fixpoint subst_qe (Z : atom) (U : qua) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs P V e1 => exp_abs (subst_qq Z U P) (subst_qqt Z U V)  (subst_qe Z U e1)
  | exp_app e1 e2 => exp_app  (subst_qe Z U e1) (subst_qe Z U e2)
  | exp_tabs P V e1 => exp_tabs (subst_qq Z U P) (subst_qt Z U V)  (subst_qe Z U e1)
  | exp_tapp e1 V => exp_tapp (subst_qe Z U e1) (subst_qt Z U V)
  | exp_qabs P Q e1 => exp_qabs (subst_qq Z U P) (subst_qq Z U Q)  (subst_qe Z U e1)
  | exp_qapp e1 Q => exp_qapp (subst_qe Z U e1) (subst_qq Z U Q)
  | exp_let e1 e2 => exp_let (subst_qe Z U e1) (subst_qe Z U e2)
  | exp_inl P e1 => exp_inl (subst_qq Z U P) (subst_qe Z U e1)
  | exp_inr P e1 => exp_inr (subst_qq Z U P) (subst_qe Z U e1)
  | exp_case e1 e2 e3 => exp_case (subst_qe Z U e1)
                                  (subst_qe Z U e2) (subst_qe Z U e3)
  | exp_pair P e1 e2 => exp_pair (subst_qq Z U P) (subst_qe Z U e1) (subst_qe Z U e2)
  | exp_first e1 => exp_first (subst_qe Z U e1)
  | exp_second e1 => exp_second (subst_qe Z U e1)
  | exp_ref P e1 => exp_ref (subst_qq Z U P) (subst_qe Z U e1)
  | exp_ref_label P l => exp_ref_label  (subst_qq Z U P) l
  | exp_deref e1 => exp_deref (subst_qe Z U e1)
  | exp_set_ref e1 e2 => exp_set_ref (subst_qe Z U e1) (subst_qe Z U e2)
  | exp_upqual P e1 => exp_upqual (subst_qq Z U P) (subst_qe Z U e1)
  | exp_check P e1 => exp_check (subst_qq Z U P) (subst_qe Z U e1)
  end.

Fixpoint subst_te (Z : atom) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs P V e1 => exp_abs P (subst_tqt Z U V)  (subst_te Z U e1)
  | exp_app e1 e2 => exp_app  (subst_te Z U e1) (subst_te Z U e2)
  | exp_tabs P V e1 => exp_tabs P (subst_tt Z U V)  (subst_te Z U e1)
  | exp_tapp e1 V => exp_tapp (subst_te Z U e1) (subst_tt Z U V)
  | exp_qabs P Q e1 => exp_qabs P Q (subst_te Z U e1)
  | exp_qapp e1 Q => exp_qapp (subst_te Z U e1) Q
  | exp_let e1 e2 => exp_let (subst_te Z U e1) (subst_te Z U e2)
  | exp_inl P e1 => exp_inl P (subst_te Z U e1)
  | exp_inr P e1 => exp_inr P (subst_te Z U e1)
  | exp_case e1 e2 e3 => exp_case (subst_te Z U e1)
                                  (subst_te Z U e2) (subst_te Z U e3)
  | exp_pair P e1 e2 => exp_pair P (subst_te Z U e1) (subst_te Z U e2)
  | exp_first e1 => exp_first (subst_te Z U e1)
  | exp_second e1 => exp_second (subst_te Z U e1)
  | exp_ref P e1 => exp_ref P (subst_te Z U e1)
  | exp_ref_label P l => exp_ref_label P l
  | exp_deref e1 => exp_deref (subst_te Z U e1)
  | exp_set_ref e1 e2 => exp_set_ref (subst_te Z U e1) (subst_te Z U e2)
  | exp_upqual P e1 => exp_upqual P (subst_te Z U e1)
  | exp_check P e1 => exp_check P (subst_te Z U e1)
  end.

Fixpoint subst_ee (z : atom) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => if x == z then u else e
  | exp_abs P V e1 => exp_abs P V (subst_ee z u e1)
  | exp_app e1 e2 => exp_app (subst_ee z u e1) (subst_ee z u e2)
  | exp_tabs P V e1 => exp_tabs P V (subst_ee z u e1)
  | exp_tapp e1 V => exp_tapp (subst_ee z u e1) V
  | exp_qabs P Q e1 => exp_qabs P Q (subst_ee z u e1)
  | exp_qapp e1 Q => exp_qapp (subst_ee z u e1) Q
  | exp_let e1 e2 => exp_let (subst_ee z u e1) (subst_ee z u e2)
  | exp_inl P e1 => exp_inl P (subst_ee z u e1)
  | exp_inr P e1 => exp_inr P (subst_ee z u e1)
  | exp_case e1 e2 e3 => exp_case (subst_ee z u e1)
                                  (subst_ee z u e2) (subst_ee z u e3)
  | exp_pair P e1 e2 => exp_pair P (subst_ee z u e1) (subst_ee z u e2)
  | exp_first e1 => exp_first (subst_ee z u e1)
  | exp_second e1 => exp_second (subst_ee z u e1)
  | exp_ref P e1 => exp_ref P (subst_ee z u e1)
  | exp_ref_label P l => exp_ref_label P l
  | exp_deref e1 => exp_deref (subst_ee z u e1)
  | exp_set_ref e1 e2 => exp_set_ref (subst_ee z u e1) (subst_ee z u e2)
  | exp_upqual P e1 => exp_upqual P (subst_ee z u e1)
  | exp_check P e1 => exp_check P (subst_ee z u e1)
  end.

Definition subst_tb (Z : atom) (P : typ) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_tt Z P T)
  | bind_typ T => bind_typ (subst_tqt Z P T)
  | bind_qua Q => bind_qua Q
  end.


Definition subst_qb (Z : atom) (P : qua) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_qt Z P T)
  | bind_typ T => bind_typ (subst_qqt Z P T)
  | bind_qua Q => bind_qua (subst_qq Z P Q)
  end.

(* ********************************************************************** *)
(** * #<a name="gather_atoms"></a># The "[gather_atoms]" tactic *)

(** The Metatheory and MetatheoryAtom libraries define a number of
    tactics for working with cofinite quantification and for picking
    fresh atoms.  To specialize those tactics to this language, we
    only need to redefine the [gather_atoms] tactic, which returns the
    set of all atoms in the current context.

    The definition of [gather_atoms] follows a pattern based on
    repeated calls to [gather_atoms_with].  The one argument to this
    tactic is a function that takes an object of some particular type
    and returns a set of atoms that appear in that argument.  It is
    not necessary to understand exactly how [gather_atoms_with] works.
    If we add a new inductive datatype, say for kinds, to our
    language, then we would need to modify [gather_atoms].  On the
    other hand, if we merely add a new type, say products, then there
    is no need to modify [gather_atoms]; the required changes would be
    made in [fv_tt]. *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : exp => fv_te x) in
  let D := gather_atoms_with (fun x : exp => fv_ee x) in
  let E := gather_atoms_with (fun x : typ => fv_tt x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  let G := gather_atoms_with (fun x : qtyp => fv_tqt x) in
  let H := gather_atoms_with (fun x : qua => fv_qq x) in
  let I := gather_atoms_with (fun x : typ => fv_qt x) in
  let J := gather_atoms_with (fun x : qtyp => fv_qqt x) in
  let K := gather_atoms_with (fun x : exp => fv_qe x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F `union`
          G `union` H `union` I `union` J `union` K).


(* ********************************************************************** *)
(** * #<a name="properties"></a># Properties of opening and substitution *)

(** The following lemmas provide useful structural properties of
    substitution and opening.  While the exact statements are language
    specific, we have found that similar properties are needed in a
    wide range of languages.

    Below, we indicate which lemmas depend on which other lemmas.
    Since [te] functions depend on their [tt] counterparts, a similar
    dependency can be found in the lemmas.

    The lemmas are split into three sections, one each for the [tt],
    [te], and [ee] functions.  The most important lemmas are the
    following:
      - Substitution and opening commute with each other, e.g.,
        [subst_tt_open_tt_var].
      - Opening a term is equivalent to opening the term with a fresh
        name and then substituting for that name, e.g.,
        [subst_tt_intro].

    We keep the sections as uniform in structure as possible.  In
    particular, we state explicitly strengthened induction hypotheses
    even when there are more concise ways of proving the lemmas of
    interest. *)


(* ********************************************************************** *)
(** ** Properties of type substitution in types *)

(** The next lemma is the strengthened induction hypothesis for the
    lemma that follows, which states that opening a locally closed
    term is the identity.  This lemma is not otherwise independently
    useful. *)

Lemma open_qq_rec_qual_aux : forall T j V i U,
  i <> j ->
  open_qq_rec j V T = open_qq_rec i U (open_qq_rec j V T) ->
  T = open_qq_rec i U T.
Proof with congruence || eauto.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
  Case "qua_bvar".
    destruct (j === n)... destruct (i === n)...
Qed.

Lemma open_tt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T
with open_tqt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tqt_rec j V T = open_tqt_rec i U (open_tqt_rec j V T) ->
  T = open_tqt_rec i U T.
Proof with congruence || eauto.
------
  clear open_tt_rec_type_aux.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
  Case "typ_bvar".
    destruct (j === n)... destruct (i === n)...
------
  clear open_tqt_rec_type_aux.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_qt_rec_qual_aux : forall T j V i U,
  i <> j ->
  open_qt_rec j V T = open_qt_rec i U (open_qt_rec j V T) ->
  T = open_qt_rec i U T
with open_qqt_rec_qual_aux : forall T j V i U,
  i <> j ->
  open_qqt_rec j V T = open_qqt_rec i U (open_qqt_rec j V T) ->
  T = open_qqt_rec i U T.
Proof with congruence || eauto using open_qq_rec_qual_aux.
------
  clear open_qt_rec_qual_aux.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
------
  clear open_qqt_rec_qual_aux.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_tt_rec_qual_aux : forall T j V i U,
  open_qt_rec j V T = open_tt_rec i U (open_qt_rec j V T) ->
  T = open_tt_rec i U T
with open_tqt_rec_qual_aux : forall T j V i U,
  open_qqt_rec j V T = open_tqt_rec i U (open_qqt_rec j V T) ->
  T = open_tqt_rec i U T.
Proof with congruence || eauto using open_qq_rec_qual_aux.
------
  clear open_tt_rec_qual_aux.
  induction T; intros j V i U H; simpl in *; inversion H; f_equal...
------
  clear open_tqt_rec_qual_aux.
  induction T; intros j V i U H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_qt_rec_type_aux : forall T j V i U,
  open_tt_rec j V T = open_qt_rec i U (open_tt_rec j V T) ->
  T = open_qt_rec i U T
with open_qqt_rec_type_aux : forall T j V i U,
  open_tqt_rec j V T = open_qqt_rec i U (open_tqt_rec j V T) ->
  T = open_qqt_rec i U T.
Proof with congruence || eauto using open_qq_rec_qual_aux.
------
  clear open_qt_rec_type_aux.
  induction T; intros j V i U H; simpl in *; inversion H; f_equal...
------
  clear open_qqt_rec_type_aux.
  induction T; intros j V i U H; simpl in *; inversion H; f_equal...
Qed.


(** Opening a locally closed term is the identity.  This lemma depends
    on the immediately preceding lemma. *)

Lemma open_qq_rec_qual : forall T U k,
  qual T ->
  T = open_qq_rec k U T.
Proof with eauto.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
Qed.

Lemma open_qt_rec_type : forall T U k,
  type T ->
  T = open_qt_rec k U T
with open_qqt_rec_type : forall T U k,
  qtype T ->
  T = open_qqt_rec k U T.
Proof with eauto using open_qq_rec_qual.
------
  clear open_qt_rec_type.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  Case "typ_all".
    unfold open_tqt in *.
    pick fresh X.
    eapply (open_qqt_rec_type_aux T2 0)...
  Case "typ_qall".
    unfold open_qqt in *.
    pick fresh X.
    eapply (open_qqt_rec_qual_aux T 0 X)...
------
  clear open_qqt_rec_type.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
Qed.

Lemma open_tt_rec_type : forall T U k,
  type T ->
  T = open_tt_rec k U T
with open_tqt_rec_type : forall T U k,
  qtype T ->
  T = open_tqt_rec k U T.
Proof with eauto.
------
  clear open_tt_rec_type.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  Case "typ_all".
    unfold open_tt in *.
    pick fresh X.
    eapply (open_tqt_rec_type_aux T2 0 (typ_fvar X))...
  Case "typ_qall".
    unfold open_qqt in *.
    pick fresh X.
    eapply (open_tqt_rec_qual_aux T 0 (qua_fvar X))...
------
  clear open_tqt_rec_type.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
Qed.

(** If a name is fresh for a term, then substituting for it is the
    identity. *)

Lemma subst_qq_fresh : forall Z U T,
  Z `notin` fv_qq T ->
  T = subst_qq Z U T.
Proof with eauto.
------
  induction T; simpl; intro H; f_equal...
  destruct (a == Z)...
    contradict H; fsetdec.
Qed.

Lemma subst_qt_fresh : forall Z U T,
  Z `notin` fv_qt T ->
  T = subst_qt Z U T
with subst_qqt_fresh : forall Z U T,
  Z `notin` fv_qqt T ->
  T = subst_qqt Z U T.
Proof with auto using subst_qq_fresh.
------
  clear subst_qt_fresh.
  induction T; simpl; intro H; f_equal...
------
  clear subst_qqt_fresh.
  induction T; simpl; intro H; f_equal...
Qed.


Lemma subst_tt_fresh : forall Z U T,
  Z `notin` fv_tt T ->
  T = subst_tt Z U T
with subst_tqt_fresh : forall Z U T,
  Z `notin` fv_tqt T ->
  T = subst_tqt Z U T.
Proof with auto.
------
  clear subst_tt_fresh.
  induction T; simpl; intro H; f_equal...
  Case "typ_fvar".
    destruct (a == Z)...
    contradict H; fsetdec.
------
  clear subst_tqt_fresh.
  induction T; simpl; intro H; f_equal...
Qed.

(** Substitution commutes with opening under certain conditions.  This
    lemma depends on the fact that opening a locally closed term is
    the identity. *)

Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
  type P ->
  subst_tt X P (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_tt X P T2) (subst_tt X P T1)
with subst_tqt_open_tqt_rec : forall T1 T2 X P k,
  type P ->
  subst_tqt X P (open_tqt_rec k T2 T1) =
    open_tqt_rec k (subst_tt X P T2) (subst_tqt X P T1).
Proof with auto.
------
  clear subst_tt_open_tt_rec.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  Case "typ_bvar".
    destruct (k === n); subst...
  Case "typ_fvar".
    destruct (a == X); subst... apply open_tt_rec_type...
------
  clear subst_tqt_open_tqt_rec.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero. *)

Lemma subst_tt_open_tt : forall T1 T2 (X:atom) P,
  type P ->
  subst_tt X P (open_tt T1 T2) = open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_open_tt_rec...
Qed.

Lemma subst_tqt_open_tqt : forall T1 T2 (X:atom) P,
  type P ->
  subst_tqt X P (open_tqt T1 T2) = open_tqt (subst_tqt X P T1) (subst_tt X P T2).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tqt_open_tqt_rec...
Qed.


(** The next lemma is a direct corollary of the immediately preceding
    lemma---here, we're opening the term with a variable.  In
    practice, this lemma seems to be needed as a left-to-right rewrite
    rule, when stated in its current form. *)

Lemma subst_tt_open_tt_var : forall (X Y:atom) P T,
  Y <> X ->
  type P ->
  open_tt (subst_tt X P T) Y = subst_tt X P (open_tt T Y).
Proof with congruence || auto.
  intros X Y P T Neq Wu.
  unfold open_tt.
  rewrite subst_tt_open_tt_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma subst_tqt_open_tqt_var : forall (X Y:atom) P T,
  Y <> X ->
  type P ->
  open_tqt (subst_tqt X P T) Y = subst_tqt X P (open_tqt T Y).
Proof with congruence || auto.
  intros X Y P T Neq Wu.
  unfold open_tqt.
  rewrite subst_tqt_open_tqt_rec...
  simpl.
  destruct (Y == X)...
Qed.


(** The next lemma states that opening a term is equivalent to first
    opening the term with a fresh name and then substituting for the
    name.  This is actually the strengthened induction hypothesis for
    the version we use in practice. *)

Lemma subst_tt_intro_rec : forall X T2 U k,
  X `notin` fv_tt T2 ->
  open_tt_rec k U T2 = subst_tt X U (open_tt_rec k (typ_fvar X) T2)
with subst_tqt_intro_rec : forall X T2 U k,
  X `notin` fv_tqt T2 ->
  open_tqt_rec k U T2 = subst_tqt X U (open_tqt_rec k (typ_fvar X) T2).
Proof with congruence || auto.
------
  clear subst_tt_intro_rec.
  induction T2; intros U k Fr; simpl in *; f_equal...
  Case "typ_bvar".
    destruct (k === n)... simpl. destruct (X == X)...
  Case "typ_fvar".
    destruct (a == X)... contradict Fr; fsetdec.
------
  clear subst_tqt_intro_rec.
  induction T2; intros U k Fr; simpl in *; f_equal...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero.  *)

Lemma subst_tt_intro : forall X T2 U,
  X `notin` fv_tt T2 ->
  open_tt T2 U = subst_tt X U (open_tt T2 X).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_intro_rec...
Qed.

Lemma subst_tqt_intro : forall X T2 U,
  X `notin` fv_tqt T2 ->
  open_tqt T2 U = subst_tqt X U (open_tqt T2 X).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tqt_intro_rec...
Qed.

(** Substitution commutes with opening under certain conditions.  This
  lemma depends on the fact that opening a locally closed term is
  the identity. *)

Lemma subst_qq_open_qq_rec : forall T1 T2 X P k,
  qual P ->
  subst_qq X P (open_qq_rec k T2 T1) =
    open_qq_rec k (subst_qq X P T2) (subst_qq X P T1).
Proof with eauto.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  Case "qua_bvar".
    destruct (k === n); subst...
  Case "qua_fvar".
    destruct (a == X); subst... apply open_qq_rec_qual...
Qed.

Lemma subst_qt_open_tt_rec : forall T1 T2 X P k,
  qual P ->
  subst_qt X P (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_qt X P T2) (subst_qt X P T1)
with subst_qqt_open_tqt_rec : forall T1 T2 X P k,
  qual P ->
  subst_qqt X P (open_tqt_rec k T2 T1) =
    open_tqt_rec k (subst_qt X P T2) (subst_qqt X P T1).
Proof with auto.
------
  clear subst_qt_open_tt_rec.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  Case "typ_bvar".
    destruct (k === n); subst...
------
  clear subst_qqt_open_tqt_rec.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero. *)

Lemma subst_qt_open_tt : forall T1 T2 (X:atom) P,
  qual P ->
  subst_qt X P (open_tt T1 T2) = open_tt (subst_qt X P T1) (subst_qt X P T2).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_qt_open_tt_rec...
Qed.

Lemma subst_qqt_open_tqt : forall T1 T2 (X:atom) P,
  qual P ->
  subst_qqt X P (open_tqt T1 T2) = open_tqt (subst_qqt X P T1) (subst_qt X P T2).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_qqt_open_tqt_rec...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---here, we're opening the term with a variable.  In
    practice, this lemma seems to be needed as a left-to-right rewrite
    rule, when stated in its current form. *)

Lemma subst_qt_open_tt_var : forall (X Y:atom) P T,
  qual P ->
  open_tt (subst_qt X P T) Y = subst_qt X P (open_tt T Y).
Proof with congruence || auto.
  intros X Y P T Wu.
  unfold open_tt.
  rewrite subst_qt_open_tt_rec...
Qed.

Lemma subst_qqt_open_tqt_var : forall (X Y:atom) P T,
  qual P ->
  open_tqt (subst_qqt X P T) Y = subst_qqt X P (open_tqt T Y).
Proof with congruence || auto.
  intros X Y P T Wu.
  unfold open_tqt.
  rewrite subst_qqt_open_tqt_rec...
Qed.

(** The next lemma states that opening a term is equivalent to first
    opening the term with a fresh name and then substituting for the
    name.  This is actually the strengthened induction hypothesis for
    the version we use in practice. *)
Lemma subst_qq_intro_rec : forall X T2 U k,
  X `notin` fv_qq T2 ->
  open_qq_rec k U T2 = subst_qq X U (open_qq_rec k (qua_fvar X) T2).
Proof with congruence || auto.
  induction T2; intros U k Fr; simpl in *; f_equal...
  Case "qua_bvar".
    destruct (k === n)... simpl. destruct (X == X)...
  Case "qua_fvar".
    destruct (a == X)... contradict Fr; fsetdec.
Qed.

Lemma subst_qt_intro_rec : forall X T2 U k,
  X `notin` fv_qt T2 ->
  open_qt_rec k U T2 = subst_qt X U (open_qt_rec k (qua_fvar X) T2)
with subst_qqt_intro_rec : forall X T2 U k,
  X `notin` fv_qqt T2 ->
  open_qqt_rec k U T2 = subst_qqt X U (open_qqt_rec k (qua_fvar X) T2).
Proof with congruence || auto using subst_qq_intro_rec.
------
  clear subst_qt_intro_rec.
  induction T2; intros U k Fr; simpl in *; f_equal...
------
  clear subst_qqt_intro_rec.
  induction T2; intros U k Fr; simpl in *; f_equal...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero.  *)

Lemma subst_qt_intro : forall X T2 U,
  X `notin` fv_qt T2 ->
  open_qt T2 U = subst_qt X U (open_qt T2 X).
Proof with auto.
  intros.
  unfold open_qt.
  apply subst_qt_intro_rec...
Qed.

Lemma subst_qqt_intro : forall X T2 U,
  X `notin` fv_qqt T2 ->
  open_qqt T2 U = subst_qqt X U (open_qqt T2 X).
Proof with auto.
  intros.
  unfold open_qt.
  apply subst_qqt_intro_rec...
Qed.


(** Substitution commutes with opening under certain conditions.  This
  lemma depends on the fact that opening a locally closed term is
  the identity. *)

Lemma subst_qt_open_qt_rec : forall T1 T2 X P k,
  qual P ->
  subst_qt X P (open_qt_rec k T2 T1) =
    open_qt_rec k (subst_qq X P T2) (subst_qt X P T1)
with subst_qqt_open_qqt_rec : forall T1 T2 X P k,
  qual P ->
  subst_qqt X P (open_qqt_rec k T2 T1) =
    open_qqt_rec k (subst_qq X P T2) (subst_qqt X P T1).
Proof with auto using subst_qq_open_qq_rec.
------
  clear subst_qt_open_qt_rec.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
------
  clear subst_qqt_open_qqt_rec.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero. *)

Lemma subst_qt_open_qt : forall T1 T2 (X:atom) P,
  qual P ->
  subst_qt X P (open_qt T1 T2) = open_qt (subst_qt X P T1) (subst_qq X P T2).
Proof with auto.
  intros.
  unfold open_qt.
  apply subst_qt_open_qt_rec...
Qed.

Lemma subst_qqt_open_qqt : forall T1 T2 (X:atom) P,
  qual P ->
  subst_qqt X P (open_qqt T1 T2) = open_qqt (subst_qqt X P T1) (subst_qq X P T2).
Proof with auto.
  intros.
  unfold open_qqt.
  apply subst_qqt_open_qqt_rec...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---here, we're opening the term with a variable.  In
    practice, this lemma seems to be needed as a left-to-right rewrite
    rule, when stated in its current form. *)

Lemma subst_qt_open_qt_var : forall (X Y:atom) P T,
  X <> Y ->
  qual P ->
  open_qt (subst_qt X P T) Y = subst_qt X P (open_qt T Y).
Proof with repeat(congruence || auto; simpl; auto).
  intros X Y P T Fr Wu.
  unfold open_qt.
  erewrite subst_qq_fresh with (T := Y) at 1.
  rewrite <- subst_qt_open_qt_rec...
  simpl...
Qed.

Lemma subst_qqt_open_qqt_var : forall (X Y:atom) P T,
  X <> Y ->
  qual P ->
  open_qqt (subst_qqt X P T) Y = subst_qqt X P (open_qqt T Y).
Proof with congruence || auto.
  intros X Y P T Neq Wu.
  unfold open_qqt.
  erewrite subst_qq_fresh with (T := Y) at 1.
  rewrite <- subst_qqt_open_qqt_rec...
  simpl...
Qed.


(** Substitution commutes with opening under certain conditions.  This
  lemma depends on the fact that opening a locally closed term is
  the identity. *)

Lemma subst_tt_open_qt_rec : forall T1 T2 X P k,
  type P ->
  subst_tt X P (open_qt_rec k T2 T1) =
    open_qt_rec k T2 (subst_tt X P T1)
with subst_tqt_open_qqt_rec : forall T1 T2 X P k,
  type P ->
  subst_tqt X P (open_qqt_rec k T2 T1) =
    open_qqt_rec k T2 (subst_tqt X P T1).
Proof with auto using subst_qq_open_qq_rec, open_qt_rec_type.
------
  clear subst_tt_open_qt_rec.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  destruct (a == X); subst...
------
  clear subst_tqt_open_qqt_rec.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero. *)

Lemma subst_tt_open_qt : forall T1 T2 (X:atom) P,
  type P ->
  subst_tt X P (open_qt T1 T2) = open_qt (subst_tt X P T1) T2.
Proof with auto.
  intros.
  unfold open_qt.
  apply subst_tt_open_qt_rec...
Qed.

Lemma subst_tqt_open_qqt : forall T1 T2 (X:atom) P,
  type P ->
  subst_tqt X P (open_qqt T1 T2) = open_qqt (subst_tqt X P T1) T2.
Proof with auto.
  intros.
  unfold open_qqt.
  apply subst_tqt_open_qqt_rec...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---here, we're opening the term with a variable.  In
    practice, this lemma seems to be needed as a left-to-right rewrite
    rule, when stated in its current form. *)

Lemma subst_tt_open_qt_var : forall (X Y:atom) P T,
  type P ->
  open_qt (subst_tt X P T) Y = subst_tt X P (open_qt T Y).
Proof with congruence || auto.
  intros X Y P T Wu.
  unfold open_qt.
  rewrite subst_tt_open_qt_rec...
Qed.

Lemma subst_tqt_open_qqt_var : forall (X Y:atom) P T,
  type P ->
  open_qqt (subst_tqt X P T) Y = subst_tqt X P (open_qqt T Y).
Proof with congruence || auto.
  intros X Y P T Wu.
  unfold open_qqt.
  rewrite subst_tqt_open_qqt_rec...
Qed.

(* ********************************************************************** *)
(** ** Properties of type substitution in expressions *)

(** This section follows the structure of the previous section.  The
    one notable difference is that we require two auxiliary lemmas to
    show that substituting a type in a locally-closed expression is
    the identity. *)

Lemma open_te_rec_expr_aux : forall e j u i P ,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) ->
  e = open_te_rec i P e.
Proof with congruence || eauto.
  induction e; intros j u i P H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_te_rec_qual_aux : forall e j Q i P ,
  open_qe_rec j Q e = open_te_rec i P (open_qe_rec j Q e) ->
  e = open_te_rec i P e.
Proof with congruence || eauto using open_tt_rec_qual_aux,
  open_tqt_rec_qual_aux.
  induction e; intros j Q i P H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_te_rec_type_aux : forall e j Q i P,
  i <> j ->
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) ->
  e = open_te_rec i P e.
Proof.
  induction e; intros j Q i P Neq Heq; simpl in *; inversion Heq;
    f_equal; eauto using open_tqt_rec_type_aux, open_tt_rec_type_aux.
Qed.

Lemma open_te_rec_expr : forall e U k,
  expr e ->
  e = open_te_rec k U e.
Proof.
  intros e U k WF. revert k.
  induction WF; intros k; simpl; f_equal; auto using open_tt_rec_type,
    open_tqt_rec_type;
  try solve [
    unfold open_ee in *;
    pick fresh x;
    eapply open_te_rec_expr_aux with (j := 0) (u := exp_fvar x);
    auto
  | unfold open_te in *;
    pick fresh X;
    eapply open_te_rec_type_aux with (j := 0) (Q := typ_fvar X);
    auto
  | unfold open_qe in *;
    pick fresh X;
    eapply open_te_rec_qual_aux with (j := 0) (Q := qua_fvar X);
    auto
  ].
Qed.

Lemma subst_te_fresh : forall X U e,
  X `notin` fv_te e ->
  e = subst_te X U e.
Proof.
  induction e; simpl; intros; f_equal; auto using subst_tt_fresh, subst_tqt_fresh.
Qed.

Lemma subst_te_open_te_rec : forall e T X U k,
  type U ->
  subst_te X U (open_te_rec k T e) =
    open_te_rec k (subst_tt X U T) (subst_te X U e).
Proof.
  intros e T X U k WU. revert k.
  induction e; intros k; simpl; f_equal; auto using subst_tt_open_tt_rec,
    subst_tqt_open_tqt_rec.
Qed.

Lemma subst_te_open_te : forall e T X U,
  type U ->
  subst_te X U (open_te e T) = open_te (subst_te X U e) (subst_tt X U T).
Proof with auto.
  intros.
  unfold open_te.
  apply subst_te_open_te_rec...
Qed.

Lemma subst_te_open_te_var : forall (X Y:atom) U e,
  Y <> X ->
  type U ->
  open_te (subst_te X U e) Y = subst_te X U (open_te e Y).
Proof with congruence || auto.
  intros X Y U e Neq WU.
  unfold open_te.
  rewrite subst_te_open_te_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma subst_te_intro_rec : forall X e U k,
  X `notin` fv_te e ->
  open_te_rec k U e = subst_te X U (open_te_rec k (typ_fvar X) e).
Proof.
  induction e; intros U k Fr; simpl in *; f_equal;
    auto using subst_tt_intro_rec, subst_tqt_intro_rec.
Qed.

Lemma subst_te_intro : forall X e U,
  X `notin` fv_te e ->
  open_te e U = subst_te X U (open_te e X).
Proof with auto.
  intros.
  unfold open_te.
  apply subst_te_intro_rec...
Qed.


(* ********************************************************************** *)
(** ** Properties of expression substitution in expressions *)

(** This section follows the structure of the previous two sections. *)

Lemma open_ee_rec_expr_aux : forall e j v u i,
  i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof with congruence || eauto.
  induction e; intros j v u i Neq H; simpl in *; inversion H; f_equal...
  Case "exp_bvar".
    destruct (j===n)... destruct (i===n)...
Qed.

Lemma open_ee_rec_type_aux : forall e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; intros j V u i H; simpl; inversion H; f_equal; eauto.
Qed.

Lemma open_ee_rec_qual_aux : forall e j V u i,
  open_qe_rec j V e = open_ee_rec i u (open_qe_rec j V e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; intros j V u i H; simpl; inversion H; f_equal; eauto.
Qed.

Lemma open_ee_rec_expr : forall u e k,
  expr e ->
  e = open_ee_rec k u e.
Proof with auto.
  intros u e k Hexpr. revert k.
  induction Hexpr; intro k; simpl; f_equal; auto*;
  try solve [
    unfold open_ee in *;
    pick fresh x;
    eapply open_ee_rec_expr_aux with (j := 0) (v := exp_fvar x);
    auto
  | unfold open_te in *;
    pick fresh X;
    eapply open_ee_rec_type_aux with (j := 0) (V := typ_fvar X);
    auto
  | unfold open_qe in *;
    pick fresh X;
    eapply open_ee_rec_qual_aux with (j := 0) (V := qua_fvar X);
    auto
  ].
Qed.

Lemma subst_ee_fresh : forall (x: atom) u e,
  x `notin` fv_ee e ->
  e = subst_ee x u e.
Proof with auto.
  intros x u e; induction e; simpl; intro H; f_equal...
  Case "exp_fvar".
    destruct (a==x)...
    contradict H; fsetdec.
Qed.

Lemma subst_ee_open_ee_rec : forall e1 e2 x u k,
  expr u ->
  subst_ee x u (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_ee x u e2) (subst_ee x u e1).
Proof with auto.
  intros e1 e2 x u k WP. revert k.
  induction e1; intros k; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n); subst...
  Case "exp_fvar".
    destruct (a == x); subst... apply open_ee_rec_expr...
Qed.

Lemma subst_ee_open_ee : forall e1 e2 x u,
  expr u ->
  subst_ee x u (open_ee e1 e2) =
    open_ee (subst_ee x u e1) (subst_ee x u e2).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
Qed.

Lemma subst_ee_open_ee_var : forall (x y:atom) u e,
  y <> x ->
  expr u ->
  open_ee (subst_ee x u e) y = subst_ee x u (open_ee e y).
Proof with congruence || auto.
  intros x y u e Neq Wu.
  unfold open_ee.
  rewrite subst_ee_open_ee_rec...
  simpl.
  destruct (y == x)...
Qed.

Lemma subst_te_open_ee_rec : forall e1 e2 Z P k,
  subst_te Z P (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_te Z P e2) (subst_te Z P e1).
Proof with auto.
  induction e1; intros e2 Z P k; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n)...
Qed.

Lemma subst_te_open_ee : forall e1 e2 Z P,
  subst_te Z P (open_ee e1 e2) = open_ee (subst_te Z P e1) (subst_te Z P e2).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_te_open_ee_rec...
Qed.

Lemma subst_te_open_ee_var : forall Z (x:atom) P e,
  open_ee (subst_te Z P e) x = subst_te Z P (open_ee e x).
Proof with auto.
  intros.
  rewrite subst_te_open_ee...
Qed.

Lemma subst_ee_open_te_rec : forall e P z u k,
  expr u ->
  subst_ee z u (open_te_rec k P e) = open_te_rec k P (subst_ee z u e).
Proof with auto.
  induction e; intros P z u k H; simpl; f_equal...
  Case "exp_fvar".
    destruct (a == z)... apply open_te_rec_expr...
Qed.

Lemma subst_ee_open_te : forall e P z u,
  expr u ->
  subst_ee z u (open_te e P) = open_te (subst_ee z u e) P.
Proof with auto.
  intros.
  unfold open_te.
  apply subst_ee_open_te_rec...
Qed.

Lemma subst_ee_open_te_var : forall z (X:atom) u e,
  expr u ->
  open_te (subst_ee z u e) X = subst_ee z u (open_te e X).
Proof with auto.
  intros z X u e H.
  rewrite subst_ee_open_te...
Qed.

Lemma subst_ee_intro_rec : forall x e u k,
  x `notin` fv_ee e ->
  open_ee_rec k u e = subst_ee x u (open_ee_rec k (exp_fvar x) e).
Proof with congruence || auto.
  induction e; intros u k Fr; simpl in *; f_equal...
  Case "exp_bvar".
    destruct (k === n)... simpl. destruct (x == x)...
  Case "exp_fvar".
    destruct (a == x)... contradict Fr; fsetdec.
Qed.

Lemma subst_ee_intro : forall x e u,
  x `notin` fv_ee e ->
  open_ee e u = subst_ee x u (open_ee e x).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_intro_rec...
Qed.

Lemma subst_te_open_qe_rec : forall e1 Q Z P k,
  type P ->
  subst_te Z P (open_qe_rec k Q e1) =
    open_qe_rec k Q (subst_te Z P e1).
Proof with auto using subst_tqt_open_qqt_rec, subst_tt_open_qt_rec.
  induction e1; intros Q Z P TypP k; simpl; f_equal...
Qed.

Lemma subst_te_open_qe : forall e1 Q Z P,
  type P ->
  subst_te Z P (open_qe e1 Q) = open_qe (subst_te Z P e1) Q.
Proof with auto.
  intros.
  unfold open_qe.
  apply subst_te_open_qe_rec...
Qed.

Lemma subst_te_open_qe_var : forall Z (x:atom) P e,
  type P ->
  open_qe (subst_te Z P e) x = subst_te Z P (open_qe e x).
Proof with auto.
  intros.
  rewrite subst_te_open_qe...
Qed.

Lemma subst_qe_intro_rec : forall x e u k,
  x `notin` fv_qe e ->
  open_qe_rec k u e = subst_qe x u (open_qe_rec k (qua_fvar x) e).
Proof with congruence || auto using subst_qt_intro_rec,
  subst_qqt_intro_rec, subst_qq_intro_rec.
  induction e; intros u k Fr; simpl in *; f_equal...
Qed.

Lemma subst_qe_intro : forall x e U,
  x `notin` fv_qe e ->
  open_qe e U = subst_qe x U (open_qe e x).
Proof with auto.
  intros.
  unfold open_qe.
  apply subst_qe_intro_rec...
Qed.

Lemma open_qe_rec_expr_aux : forall e j u i P ,
  open_ee_rec j u e = open_qe_rec i P (open_ee_rec j u e) ->
  e = open_qe_rec i P e.
Proof with congruence || eauto.
  induction e; intros j u i P H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_qe_rec_qual_aux : forall e j Q i P,
  i <> j ->
  open_qe_rec j Q e = open_qe_rec i P (open_qe_rec j Q e) ->
  e = open_qe_rec i P e.
Proof with congruence || eauto using open_qq_rec_qual_aux,
  open_qt_rec_qual_aux,
  open_qqt_rec_qual_aux.
  induction e; intros j Q i P Neq H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_qe_rec_type_aux : forall e j Q i P,
  open_te_rec j Q e = open_qe_rec i P (open_te_rec j Q e) ->
  e = open_qe_rec i P e.
Proof with eauto.
  induction e; intros j Q i P Heq; simpl in *; inversion Heq;
    f_equal; subst; eauto using
    open_qqt_rec_type_aux,
    open_qt_rec_type_aux;
    try solve [rewrite <- H0; eauto];
    try solve [rewrite <- H1; eauto].
Qed.

Lemma open_qe_rec_expr : forall e U k,
  expr e ->
  e = open_qe_rec k U e.
Proof.
  intros e U k WF. revert k.
  induction WF; intros k; simpl; f_equal; auto using open_qt_rec_type,
    open_qqt_rec_type, open_qq_rec_qual;
  try solve [
    unfold open_ee in *;
    pick fresh x;
    eapply open_qe_rec_expr_aux with (j := 0) (u := exp_fvar x);
    auto
  | unfold open_te in *;
    pick fresh X;
    eapply open_qe_rec_type_aux with (j := 0) (Q := typ_fvar X);
    auto
  | unfold open_qe in *;
    pick fresh X;
    eapply open_qe_rec_qual_aux with (j := 0) (Q := qua_fvar X);
    auto
  ].
Qed.

Lemma subst_ee_open_qe_rec : forall e P z u k,
  expr u ->
  subst_ee z u (open_qe_rec k P e) = open_qe_rec k P (subst_ee z u e).
Proof with auto.
  induction e; intros P z u k H; simpl; f_equal...
  Case "exp_fvar".
    destruct (a == z)... apply open_qe_rec_expr...
Qed.

Lemma subst_ee_open_qe : forall e P z u,
  expr u ->
  subst_ee z u (open_qe e P) = open_qe (subst_ee z u e) P.
Proof with auto.
  intros.
  unfold open_qe.
  apply subst_ee_open_qe_rec...
Qed.

Lemma subst_ee_open_qe_var : forall z (X:atom) u e,
  expr u ->
  open_qe (subst_ee z u e) X = subst_ee z u (open_qe e X).
Proof with auto.
  intros z X u e H.
  rewrite subst_ee_open_qe...
Qed.

Lemma subst_qe_open_ee_rec : forall e1 e2 Z P k,
  subst_qe Z P (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_qe Z P e2) (subst_qe Z P e1).
Proof with auto.
  induction e1; intros e2 Z P k; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n)...
Qed.

Lemma subst_qe_open_ee : forall e1 e2 Z P,
  subst_qe Z P (open_ee e1 e2) = open_ee (subst_qe Z P e1) (subst_qe Z P e2).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_qe_open_ee_rec...
Qed.

Lemma subst_qe_open_ee_var : forall Z (x:atom) P e,
  open_ee (subst_qe Z P e) x = subst_qe Z P (open_ee e x).
Proof with auto.
  intros.
  rewrite subst_qe_open_ee...
Qed.

Lemma subst_qe_fresh : forall X U e,
  X `notin` fv_qe e ->
  e = subst_qe X U e.
Proof.
  induction e; simpl; intros; f_equal;
    auto using subst_qq_fresh, subst_qt_fresh, subst_qqt_fresh.
Qed.

Lemma subst_qe_open_qe_rec : forall e T X U k,
  qual U ->
  subst_qe X U (open_qe_rec k T e) =
    open_qe_rec k (subst_qq X U T) (subst_qe X U e).
Proof.
  intros e T X U k WU. revert k.
  induction e; intros k; simpl; f_equal; auto using subst_qt_open_qt_rec,
    subst_qqt_open_qqt_rec, subst_qq_open_qq_rec.
Qed.

Lemma subst_qe_open_qe : forall e T X U,
  qual U ->
  subst_qe X U (open_qe e T) = open_qe (subst_qe X U e) (subst_qq X U T).
Proof with auto.
  intros.
  unfold open_qe.
  apply subst_qe_open_qe_rec...
Qed.

Lemma subst_qe_open_qe_var : forall (X Y:atom) U e,
  Y <> X ->
  qual U ->
  open_qe (subst_qe X U e) Y = subst_qe X U (open_qe e Y).
Proof with congruence || auto.
  intros X Y U e Neq WU.
  unfold open_qe.
  erewrite (subst_qq_fresh) with (T := Y) at 1.
  rewrite <- subst_qe_open_qe_rec...
  simpl.
  destruct (Y == X)...
Qed.


Lemma subst_qe_open_te_rec : forall e T X U k,
  qual U ->
  subst_qe X U (open_te_rec k T e) =
    open_te_rec k (subst_qt X U T) (subst_qe X U e).
Proof with eauto.
  intros e T X U k WU. revert k.
  induction e; intros k; simpl; f_equal; eauto using subst_qt_open_tt_rec,
    subst_qqt_open_tqt_rec, subst_qq_open_qq_rec...
Qed.

Lemma subst_qe_open_te : forall e T X U,
  qual U ->
  subst_qe X U (open_te e T) = open_te (subst_qe X U e) (subst_qt X U T).
Proof with auto.
  intros.
  unfold open_qe.
  apply subst_qe_open_te_rec...
Qed.

Lemma subst_qe_open_te_var : forall (X Y:atom) U e,
  Y <> X ->
  qual U ->
  open_te (subst_qe X U e) Y = subst_qe X U (open_te e Y).
Proof with congruence || auto.
  intros X Y U e Neq WU.
  unfold open_te.
  rewrite subst_qe_open_te_rec...
Qed.

(* *********************************************************************** *)
(** * #<a name="lc"></a># Local closure is preserved under substitution *)

(** While these lemmas may be considered properties of substitution, we
    separate them out due to the lemmas that they depend on. *)

(** The following lemma depends on [subst_tt_open_tt_var]. *)

Lemma subst_qq_qual : forall Z P T,
  qual T ->
  qual P ->
  qual (subst_qq Z P T).
Proof with eauto.
  intros Z P T HT HP.
  induction HT; simpl...
  Case "qual_fvar".
    destruct (X == Z)...
Qed.

Lemma subst_tt_type : forall Z P T,
  type T ->
  type P ->
  type (subst_tt Z P T)
with subst_tqt_type : forall Z P T,
  qtype T ->
  type P ->
  qtype (subst_tqt Z P T).
Proof with auto.
------
  clear subst_tt_type.
  intros Z P T HT HP.
  induction HT; simpl...
  Case "type_fvar".
    destruct (X == Z)...
  Case "type_all".
    pick fresh Y and apply type_all...
    rewrite subst_tqt_open_tqt_var...
  Case "typ_qall".
    pick fresh Y and apply type_qall...
    rewrite subst_tqt_open_qqt_var...
------
  clear subst_tqt_type.
  intros Z P T HT HP.
  induction HT; simpl...
Qed.

Lemma subst_qt_type : forall Z P T,
  type T ->
  qual P ->
  type (subst_qt Z P T)
with subst_qqt_type : forall Z P T,
  qtype T ->
  qual P ->
  qtype (subst_qqt Z P T).
Proof with auto using subst_qq_qual.
------
  clear subst_qt_type.
  intros Z P T HT HP.
  induction HT; simpl...
  Case "type_all".
    pick fresh Y and apply type_all...
    rewrite subst_qqt_open_tqt_var...
  Case "typ_qall".
    pick fresh Y and apply type_qall...
    rewrite subst_qqt_open_qqt_var...
------
  clear subst_qqt_type.
  intros Z P T HT HP.
  induction HT; simpl...
Qed.

(** The following lemma depends on [subst_tt_type],
    [subst_te_open_ee_var], and [sbust_te_open_te_var]. *)

Lemma subst_te_expr : forall Z P e,
  expr e ->
  type P ->
  expr (subst_te Z P e).
Proof with eauto using subst_tt_type.
  intros Z P e He Hp.
  induction He; simpl; auto using subst_tt_type, subst_tqt_type;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton Z);
    intros;
    try rewrite subst_te_open_ee_var;
    try rewrite subst_te_open_te_var;
    try rewrite subst_te_open_qe_var;
    eauto using subst_tt_type, subst_tqt_type
  ].
Qed.

Lemma subst_qe_expr : forall Z P e,
  expr e ->
  qual P ->
  expr (subst_qe Z P e).
Proof with eauto using subst_qt_type, subst_qq_qual.
  intros Z P e He Hp.
  induction He; simpl; auto using subst_qt_type, subst_qq_qual;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton Z);
    intros;
    try rewrite subst_qe_open_ee_var;
    try rewrite subst_qe_open_te_var;
    try rewrite subst_qe_open_qe_var;
    eauto using subst_qt_type, subst_qqt_type, subst_qq_qual
  ].
Qed.

(** The following lemma depends on [subst_ee_open_ee_var] and
    [subst_ee_open_te_var]. *)

Lemma subst_ee_expr : forall z e1 e2,
  expr e1 ->
  expr e2 ->
  expr (subst_ee z e2 e1).
Proof with auto.
  intros z e1 e2 He1 He2.
  induction He1; simpl; auto;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton z);
    intros;
    try rewrite subst_ee_open_ee_var;
    try rewrite subst_ee_open_te_var;
    try rewrite subst_ee_open_qe_var;
    auto
  ].
  Case "expr_var".
    destruct (x == z)...
Qed.


(* *********************************************************************** *)
(** * #<a name="body"></a># Properties of [body_e] *)

(** The two kinds of facts we need about [body_e] are the following:
      - How to use it to derive that terms are locally closed.
      - How to derive it from the facts that terms are locally closed.

    Since we use it only in the context of [exp_let] and [exp_sum]
    (see the definition of reduction), those two constructors are the
    only ones we consider below. *)

Lemma expr_let_from_body : forall e1 e2,
  expr e1 ->
  body_e e2 ->
  expr (exp_let e1 e2).
Proof.
  intros e1 e2 H [J1 J2].
  pick fresh y and apply expr_let; auto.
Qed.

Lemma body_from_expr_let : forall e1 e2,
  expr (exp_let e1 e2) ->
  body_e e2.
Proof.
  intros e1 e2 H.
  unfold body_e.
  inversion H; eauto.
Qed.

Lemma expr_case_from_body : forall e1 e2 e3,
  expr e1 ->
  body_e e2 ->
  body_e e3 ->
  expr (exp_case e1 e2 e3).
Proof.
  intros e1 e2 e3 H [J1 J2] [K1 K2].
  pick fresh y and apply expr_case; auto.
Qed.

Lemma body_inl_from_expr_case : forall e1 e2 e3,
  expr (exp_case e1 e2 e3) ->
  body_e e2.
Proof.
  intros e1 e2 e3 H.
  unfold body_e.
  inversion H; eauto.
Qed.

Lemma body_inr_from_expr_case : forall e1 e2 e3,
  expr (exp_case e1 e2 e3) ->
  body_e e3.
Proof.
  intros e1 e2 e3 H.
  unfold body_e.
  inversion H; eauto.
Qed.

Lemma open_ee_body_e : forall e1 e2,
  body_e e1 -> expr e2 -> expr (open_ee e1 e2).
Proof.
  intros e1 e2 [L H] J.
  pick fresh x.
  rewrite (subst_ee_intro x); auto using subst_ee_expr.
Qed.


(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We add as hints the fact that local closure is preserved under
    substitution.  This is part of our strategy for automatically
    discharging local-closure proof obligations. *)

#[export] Hint Resolve subst_tt_type subst_te_expr subst_ee_expr
  subst_qt_type subst_qe_expr subst_qq_qual subst_qt_type : core.

(** We also add as hints the lemmas concerning [body_e]. *)

#[export] Hint Resolve expr_let_from_body body_from_expr_let : core.
#[export] Hint Resolve expr_case_from_body : core.
#[export] Hint Resolve body_inl_from_expr_case body_inr_from_expr_case : core.
#[export] Hint Resolve open_ee_body_e : core.

(** When reasoning about the [binds] relation and [map], we
    occasionally encounter situations where the binding is
    over-simplified.  The following hint undoes that simplification,
    thus enabling [Hint]s from the MetatheoryEnv library. *)

#[export] Hint Extern 1 (binds _ (?F (subst_tt ?X ?U ?T)) _) =>
  unsimpl (subst_tb X U (F T)) : core.
#[export] Hint Extern 1 (binds _ (?F (subst_qt ?X ?U ?T)) _) =>
  unsimpl (subst_qb X U (F T)) : core.
#[export] Hint Extern 1 (binds _ (?F (subst_qq ?X ?U ?T)) _) =>
  unsimpl (subst_qb X U (F T)) : core.
#[export] Hint Extern 1 (binds _ (?F (subst_tqt ?X ?U ?T)) _) =>
  unsimpl (subst_tb X U (F T)) : core.
#[export] Hint Extern 1 (binds _ (?F (subst_qqt ?X ?U ?T)) _) =>
  unsimpl (subst_qb X U (F T)) : core.
