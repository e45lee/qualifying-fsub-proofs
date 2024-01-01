(** Definition of Fsub (System F with subtyping).

    Authors: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    Table of contents:
      - #<a href="##syntax">Syntax (pre-terms)</a>#
      - #<a href="##open">Opening</a>#
      - #<a href="##lc">Local closure</a>#
      - #<a href="##env">Environments</a>#
      - #<a href="##wf">Well-formedness</a>#
      - #<a href="##sub">Subtyping</a>#
      - #<a href="##typing_doc">Typing</a>#
      - #<a href="##values">Values</a>#
      - #<a href="##reduction">Reduction</a>#
      - #<a href="##auto">Automation</a>#
*)

Require Export Fsub.CaptureTrack.LabelMap.
Require Export Fsub.CaptureTrack.Label.
Require Export Metalib.Metatheory.
Require Export String.

(* ********************************************************************** *)
(** * #<a name="syntax"></a># Syntax (pre-terms) *)

(** We use a locally nameless representation for Fsub, where bound
    variables are represented as natural numbers (de Bruijn indices)
    and free variables are represented as [atom]s.  The type [atom],
    defined in the MetatheoryAtom library, represents names: there are
    infinitely many atoms, equality is decidable on atoms, and it is
    possible to generate an atom fresh for any given finite set of
    atoms.

    We say that the definitions below define pre-types ([typ]) and
    pre-expressions ([exp]), collectively pre-terms, since the
    datatypes admit terms, such as [(typ_all typ_top (typ_bvar 3))],
    where indices are unbound.  A term is locally closed when it
    contains no unbound indices.

    Note that indices for bound type variables are distinct from
    indices for bound expression variables.  We make this explicit in
    the definitions below of the opening operations. *)

Inductive qua : Set :=
  | qua_top : qua
  | qua_bvar : nat -> qua
  | qua_fvar : atom -> qua
  | qua_meet : qua -> qua -> qua
  | qua_join : qua -> qua -> qua
  | qua_bot : qua
.

Inductive typ : Set :=
  | typ_top : typ
  | typ_bvar : nat -> typ
  | typ_fvar : atom -> typ
  | typ_arrow : qtyp -> qtyp -> typ
  | typ_all : typ -> qtyp -> typ
  | typ_qall : qua -> qtyp -> typ
  | typ_sum : qtyp -> qtyp -> typ
  | typ_pair : qtyp -> qtyp -> typ
  | typ_ref : qtyp -> typ
with qtyp : Set :=
  | qtyp_qtyp : qua -> typ -> qtyp
.

Inductive exp : Set :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : qua -> qtyp -> exp -> exp
  | exp_app : exp -> exp -> qua -> exp
  | exp_tabs : qua -> typ -> exp -> exp
  | exp_tapp : exp -> typ -> exp
  | exp_qabs : qua -> qua -> exp -> exp
  | exp_qapp : exp -> qua -> exp
  | exp_let : qua -> exp -> exp -> exp
  | exp_inl : qua -> exp -> exp
  | exp_inr : qua -> exp -> exp
  | exp_case : exp -> qua -> exp -> qua -> exp -> exp
  | exp_pair : qua -> exp -> exp -> exp
  | exp_first : exp -> exp
  | exp_second : exp -> exp
  | exp_ref : qua -> exp -> exp
  | exp_ref_label : qua -> label -> exp
  | exp_deref : exp -> exp
  | exp_set_ref : exp -> exp -> exp
  | exp_upqual : qua -> exp -> exp
  | exp_check : qua -> exp -> exp
.

(** We declare the constructors for indices and variables to be
    coercions.  For example, if Coq sees a [nat] where it expects an
    [exp], it will implicitly insert an application of [exp_bvar];
    similar behavior happens for [atom]s.  Thus, we may write
    [(exp_abs typ_top (exp_app 0 x))] instead of [(exp_abs typ_top
    (exp_app (exp_bvar 0) (exp_fvar x)))]. *)

Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.
Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.
Coercion qua_bvar : nat >-> qua.
Coercion qua_fvar : atom >-> qua.


(* ********************************************************************** *)
(** * #<a name="concrete"></a># Concrete Qualifiers *)

(** A concrete qualifier [at runtime] *)
Inductive concrete_qua : Set := cqua_top | cqua_bot.

(** concretely getting a runtime qualifier *)
Fixpoint concretize (q : qua) : (option concrete_qua) :=
  match q with
  | qua_top => Some cqua_top
  | qua_fvar X => None
  | qua_bvar n => None
  | qua_join Q1 Q2 =>
    match (concretize Q1) with 
    | Some cqua_top => Some cqua_top
    | Some cqua_bot => (concretize Q2)
    | None => None
    end
  | qua_meet Q1 Q2 =>
    match (concretize Q1) with
    | Some cqua_top => (concretize Q2)
    | Some cqua_bot => Some cqua_bot
    | None => None
    end
  | qua_bot => Some cqua_bot
  end.

(** getting a qualifier out of a concrete qualifier *)
Definition abstractize (s : concrete_qua) := 
  match s with
  | cqua_top => qua_top
  | cqua_bot => qua_bot
  end.

(** if a given concrete qualifier is compatible with another *)
Inductive cqua_compatible : concrete_qua -> concrete_qua -> Prop :=
  | cqua_compatible_same : forall s, cqua_compatible s s
  | cqua_compatible_up : cqua_compatible cqua_bot cqua_top.
Notation "s ~> t" := (cqua_compatible s t) (at level 70).


(* ********************************************************************** *)
(** * #<a name="open"></a># Opening terms *)

(** Opening replaces an index with a term.  This operation is required
    if we wish to work only with locally closed terms when going under
    binders (e.g., the typing rule for [exp_abs]).  It also
    corresponds to informal substitution for a bound variable, which
    occurs in the rule for beta reduction.

    We need to define three functions for opening due the syntax of
    Fsub, and we name them according to the following convention.
      - [tt]: Denotes an operation involving types appearing in types.
      - [te]: Denotes an operation involving types appearing in
        expressions.
      - [ee]: Denotes an operation involving expressions appearing in
        expressions.

    The notation used below for decidable equality on natural numbers
    (e.g., [K == J]) is defined in the CoqEqDec library, which is
    included by the Metatheory library.  The order of arguments to
    each "open" function is the same.  For example, [(open_tt_rec K U
    T)] can be read as "substitute [U] for index [K] in [T]."

    Note that we assume [U] is locally closed (and similarly for the
    other opening functions).  This assumption simplifies the
    implementations of opening by letting us avoid shifting.  Since
    bound variables are indices, there is no need to rename variables
    to avoid capture.  Finally, we assume that these functions are
    initially called with index zero and that zero is the only unbound
    index in the term.  This eliminates the need to possibly subtract
    one in the case of indices. *)

Fixpoint open_qq_rec (K : nat) (R : qua) (Q : qua)  {struct Q} : qua :=
  match Q with
  | qua_top => qua_top
  | qua_bvar J => if (K == J) then R else (qua_bvar J)
  | qua_fvar X => qua_fvar X
  | qua_meet Q1 Q2 => qua_meet (open_qq_rec K R Q1) (open_qq_rec K R Q2)
  | qua_join Q1 Q2 => qua_join (open_qq_rec K R Q1) (open_qq_rec K R Q2)
  | qua_bot => qua_bot
  end.

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ)  {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => if K == J then U else (typ_bvar J)
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tqt_rec K U T1) (open_tqt_rec (S K) U T2)
  | typ_all T1 T2 => typ_all (open_tt_rec K U T1) (open_tqt_rec (S K) U T2)
  | typ_qall Q T => typ_qall Q (open_tqt_rec (S K) U T)
  | typ_sum T1 T2 => typ_sum (open_tqt_rec K U T1) (open_tqt_rec K U T2)
  | typ_pair T1 T2 => typ_pair (open_tqt_rec K U T1) (open_tqt_rec K U T2)
  | typ_ref T1 => typ_ref (open_tqt_rec K U T1)
  end
with open_tqt_rec (K : nat) (U : typ) (T : qtyp)  {struct T} : qtyp :=
  match T with
  | qtyp_qtyp Q T => qtyp_qtyp Q (open_tt_rec K U T)
  end.

Fixpoint open_qt_rec (K : nat) (R : qua) (T : typ)  {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => typ_bvar J
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_qqt_rec K R T1) (open_qqt_rec (S K) R T2)
  | typ_all T1 T2 => typ_all (open_qt_rec K R T1) (open_qqt_rec (S K) R T2)
  | typ_qall Q T => typ_qall (open_qq_rec K R Q) (open_qqt_rec (S K) R T)
  | typ_sum T1 T2 => typ_sum (open_qqt_rec K R T1) (open_qqt_rec K R T2)
  | typ_pair T1 T2 => typ_pair (open_qqt_rec K R T1) (open_qqt_rec K R T2)
  | typ_ref T1 => typ_ref (open_qqt_rec K R T1)
  end
with open_qqt_rec (K : nat) (R : qua) (T : qtyp)  {struct T} : qtyp :=
  match T with
  | qtyp_qtyp Q T => qtyp_qtyp (open_qq_rec K R Q) (open_qt_rec K R T)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs P V e1 => exp_abs P (open_tqt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_app e1 e2 Q => exp_app  (open_te_rec K U e1) (open_te_rec K U e2) Q
  | exp_tabs P V e1 => exp_tabs P(open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  | exp_qabs P Q e1 => exp_qabs P Q (open_te_rec (S K) U e1)
  | exp_qapp e1 Q => exp_qapp (open_te_rec K U e1) Q
  | exp_let Q e1 e2 => exp_let Q (open_te_rec K U e1) (open_te_rec (S K) U e2)
  | exp_inl P e1 => exp_inl P (open_te_rec K U e1)
  | exp_inr P e2 => exp_inr P (open_te_rec K U e2)
  | exp_case e1 Q1 e2 Q2 e3 =>
      exp_case (open_te_rec K U e1) Q1 (open_te_rec (S K) U e2) Q2 (open_te_rec (S K) U e3)
  | exp_pair P e1 e2 => exp_pair P (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_first e1 => exp_first (open_te_rec K U e1)
  | exp_second e2 => exp_second (open_te_rec K U e2)
  | exp_ref P e1 => exp_ref P (open_te_rec K U e1)
  | exp_ref_label P l => exp_ref_label P l
  | exp_deref e1 => exp_deref (open_te_rec K U e1)
  | exp_set_ref e1 e2 => exp_set_ref (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_check P e1 => exp_check P (open_te_rec K U e1)
  | exp_upqual P e1 => exp_upqual P (open_te_rec K U e1)
  end.

Fixpoint open_qe_rec (K : nat) (R : qua) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs P V e1 => exp_abs (open_qq_rec K R P) (open_qqt_rec K R V)  (open_qe_rec (S K) R e1)
  | exp_app e1 e2 Q => exp_app  (open_qe_rec K R e1) (open_qe_rec K R e2) (open_qq_rec K R Q)
  | exp_tabs P V e1 => exp_tabs (open_qq_rec K R P) (open_qt_rec K R V)  (open_qe_rec (S K) R e1)
  | exp_tapp e1 V => exp_tapp (open_qe_rec K R e1) (open_qt_rec K R V)
  | exp_qabs P Q e1 => exp_qabs (open_qq_rec K R P) (open_qq_rec K R Q)  (open_qe_rec (S K) R e1)
  | exp_qapp e1 Q => exp_qapp (open_qe_rec K R e1) (open_qq_rec K R Q)
  | exp_let Q e1 e2 => exp_let (open_qq_rec K R Q) (open_qe_rec K R e1) (open_qe_rec (S K) R e2)
  | exp_inl P e1 => exp_inl (open_qq_rec K R P) (open_qe_rec K R e1)
  | exp_inr P e2 => exp_inr (open_qq_rec K R P) (open_qe_rec K R e2)
  | exp_case e1 Q1 e2 Q2 e3 =>
      exp_case (open_qe_rec K R e1) (open_qq_rec K R Q1) (open_qe_rec (S K) R e2) (open_qq_rec K R Q2) (open_qe_rec (S K) R e3)
  | exp_pair P e1 e2 => exp_pair  (open_qq_rec K R P) (open_qe_rec K R e1) (open_qe_rec K R e2)
  | exp_first e1 => exp_first (open_qe_rec K R e1)
  | exp_second e2 => exp_second (open_qe_rec K R e2)
  | exp_ref P e1 => exp_ref (open_qq_rec K R P) (open_qe_rec K R e1)
  | exp_ref_label P l => exp_ref_label (open_qq_rec K R P) l
  | exp_deref e1 => exp_deref (open_qe_rec K R e1)
  | exp_set_ref e1 e2 => exp_set_ref (open_qe_rec K R e1) (open_qe_rec K R e2)
  | exp_check P e1 => exp_check (open_qq_rec K R P) (open_qe_rec K R e1)
  | exp_upqual P e1 => exp_upqual (open_qq_rec K R P) (open_qe_rec K R e1)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (R : qua) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k == i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs P V e1 => exp_abs (open_qq_rec k R P) (open_qqt_rec k R V) (open_ee_rec (S k) f R e1)
  | exp_app e1 e2 Q => exp_app (open_ee_rec k f R e1) (open_ee_rec k f R e2) (open_qq_rec k R Q)
  | exp_tabs P V e1 => exp_tabs (open_qq_rec k R P) (open_qt_rec k R V) (open_ee_rec (S k) f R e1)
  | exp_tapp e1 V => exp_tapp (open_ee_rec k f R e1) (open_qt_rec k R V)
  | exp_qabs P Q e1 => exp_qabs (open_qq_rec k R P) (open_qq_rec k R Q) (open_ee_rec (S k) f R e1)
  | exp_qapp e1 Q => exp_qapp (open_ee_rec k f R e1) (open_qq_rec k R Q)
  | exp_let Q e1 e2 => exp_let (open_qq_rec k R Q) (open_ee_rec k f R e1) (open_ee_rec (S k) f R e2)
  | exp_inl P e1 => exp_inl (open_qq_rec k R P) (open_ee_rec k f R e1)
  | exp_inr P e2 => exp_inr (open_qq_rec k R P)(open_ee_rec k f R e2)
  | exp_case e1 Q1 e2 Q2 e3 =>
      exp_case (open_ee_rec k f R e1)
               (open_qq_rec k R Q1)
               (open_ee_rec (S k) f R e2)
               (open_qq_rec k R Q2)
               (open_ee_rec (S k) f R e3)
  | exp_pair P e1 e2 => exp_pair (open_qq_rec k R P) (open_ee_rec k f R e1) (open_ee_rec k f R e2)
  | exp_first e1 => exp_first (open_ee_rec k f R e1)
  | exp_second e2 => exp_second (open_ee_rec k f R e2)
  | exp_ref P e1 => exp_ref (open_qq_rec k R P) (open_ee_rec k f R e1)
  | exp_ref_label P l => exp_ref_label (open_qq_rec k R P) l
  | exp_deref e1 => exp_deref (open_ee_rec k f R e1)
  | exp_set_ref e1 e2 => exp_set_ref (open_ee_rec k f R e1) (open_ee_rec k f R e2)
  | exp_check P e1 => exp_check (open_qq_rec k R P) (open_ee_rec k f R e1)
  | exp_upqual P e1 => exp_upqual (open_qq_rec k R P) (open_ee_rec k f R e1)
  end.

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definitions provide
    convenient shorthands for such uses.  Note that the order of
    arguments is switched relative to the definitions above.  For
    example, [(open_tt T X)] can be read as "substitute the variable
    [X] for index [0] in [T]" and "open [T] with the variable [X]."
    Recall that the coercions above let us write [X] in place of
    [(typ_fvar X)], assuming that [X] is an [atom]. *)

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te e U := open_te_rec 0 U e.
Definition open_ee e1 e2 R:= open_ee_rec 0 e2 R e1.
Definition open_qq Q R := open_qq_rec 0 R Q.
Definition open_qe e R := open_qe_rec 0 R e.
Definition open_qt T R := open_qt_rec 0 R T.
Definition open_qqt T R := open_qqt_rec 0 R T.
Definition open_tqt T R := open_tqt_rec 0 R T.


(* ********************************************************************** *)
(** * #<a name="lc"></a># Local closure *)

(** Recall that [typ] and [exp] define pre-terms; these datatypes
    admit terms that contain unbound indices.  A term is locally
    closed, or syntactically well-formed, when no indices appearing in
    it are unbound.  The proposition [(type T)] holds when a type [T]
    is locally closed, and [(expr e)] holds when an expression [e] is
    locally closed.

    The inductive definitions below formalize local closure such that
    the resulting induction principles serve as structural induction
    principles over (locally closed) types and (locally closed)
    expressions.  In particular, unlike the situation with pre-terms,
    there are no cases for indices.  Thus, these induction principles
    correspond more closely to informal practice than the ones arising
    from the definitions of pre-terms.

    The interesting cases in the inductive definitions below are those
    that involve binding constructs, e.g., [typ_all].  Intuitively, to
    check if the pre-term [(typ_all T1 T2)] is locally closed, we must
    check that [T1] is locally closed and that [T2] is locally closed
    when opened with a variable.  However, there is a choice as to how
    many variables to quantify over.  One possibility is to quantify
    over only one variable ("existential" quantification), as in
<<
  type_all : forall X T1 T2,
      type T1 ->
      type (open_tt T2 X) ->
      type (typ_all T1 T2) .
>>  Or, we could quantify over as many variables as possible ("universal"
    quantification), as in
<<
  type_all : forall T1 T2,
      type T1 ->
      (forall X : atom, type (open_tt T2 X)) ->
      type (typ_all T1 T2) .
>>  It is possible to show that the resulting relations are equivalent.
    The former makes it easy to build derivations, while the latter
    provides a strong induction principle.  McKinna and Pollack used
    both forms of this relation in their work on formalizing Pure Type
    Systems.

    We take a different approach here and use "cofinite"
    quantification: we quantify over all but finitely many variables.
    This approach provides a convenient middle ground: we can build
    derivations reasonably easily and get reasonably strong induction
    principles.  With some work, one can show that the definitions
    below are equivalent to ones that use existential, and hence also
    universal, quantification. *)
Inductive qual : qua -> Prop :=
  | qual_top :
      qual qua_top
  | qual_fvar : forall (X : atom),
      qual (qua_fvar X)
  | qual_meet : forall Q1 Q2,
      qual Q1 ->
      qual Q2 ->
      qual (qua_meet Q1 Q2)
  | qual_join : forall Q1 Q2,
      qual Q1 ->
      qual Q2 ->
      qual (qua_join Q1 Q2)
  | qual_bot :
      qual qua_bot
.

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall L T1 T2,
      qtype T1 ->
      (forall X: atom, X `notin` L -> qtype (open_qqt T2 X)) ->
      type (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X : atom, X `notin` L -> qtype (open_tqt T2 X)) ->
      type (typ_all T1 T2)
  | type_qall : forall L Q T,
      qual Q ->
      (forall X : atom, X `notin` L -> qtype (open_qqt T X)) ->
      type (typ_qall Q T)
  | type_sum : forall T1 T2,
      qtype T1 ->
      qtype T2 ->
      type (typ_sum T1 T2)
  | type_pair : forall T1 T2,
      qtype T1 ->
      qtype T2 ->
      type (typ_pair T1 T2)
with qtype : qtyp -> Prop :=
  | qtype_qtyp : forall Q T,
      qual Q ->
      type T ->
      qtype (qtyp_qtyp Q T)
.

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L P T e1,
      qual P ->
      qtype T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x x)) ->
      expr (exp_abs P T e1)
  | expr_app : forall e1 e2 Q,
      expr e1 ->
      expr e2 ->
      qual Q ->
      expr (exp_app e1 e2 Q)
  | expr_tabs : forall L P T e1,
      qual P ->
      type T ->
      (forall X : atom, X `notin` L -> expr (open_te e1 X)) ->
      expr (exp_tabs P T e1)
  | expr_tapp : forall e1 V,
      expr e1 ->
      type V ->
      expr (exp_tapp e1 V)
  | expr_qabs : forall L P Q e1,
      qual P ->
      qual Q ->
      (forall X : atom, X `notin` L -> expr (open_qe e1 X)) ->
      expr (exp_qabs P Q e1)
  | expr_qapp : forall e1 Q,
      expr e1 ->
      qual Q ->
      expr (exp_qapp e1 Q)
  | expr_let : forall L Q e1 e2,
      qual Q ->
      expr e1 ->
      (forall x : atom, x `notin` L -> expr (open_ee e2 x x)) ->
      expr (exp_let Q e1 e2)
  | expr_inl : forall P e1,
      qual P ->
      expr e1 ->
      expr (exp_inl P e1)
  | expr_inr : forall P e1,
      qual P ->
      expr e1 ->
      expr (exp_inr P e1)
  | expr_case : forall L e1 Q1 e2 Q2 e3,
      expr e1 ->
      qual Q1 ->
      qual Q2 ->
      (forall x : atom, x `notin` L -> expr (open_ee e2 x x)) ->
      (forall x : atom, x `notin` L -> expr (open_ee e3 x x)) ->
      expr (exp_case e1 Q1 e2 Q2 e3)
  | expr_pair : forall P e1 e2,
      qual P ->
      expr e1 ->
      expr e2 ->
      expr (exp_pair P e1 e2)
  | expr_first : forall e1,
      expr e1 ->
      expr (exp_first e1)
  | expr_second : forall e1,
      expr e1 ->
      expr (exp_second e1)
  | expr_upqual : forall P e1,
      qual P ->
      expr e1 ->
      expr (exp_upqual P e1)
  | expr_check : forall P e1,
      qual P ->
      expr e1 ->
      expr (exp_check P e1)
.

(** #<a name="body_e_doc"></a># We also define what it means to be the
    body of an abstraction, since this simplifies slightly the
    definition of reduction and subsequent proofs.  It is not strictly
    necessary to make this definition in order to complete the
    development. *)

Definition body_e (e : exp) :=
  exists L, forall x : atom, x `notin` L -> expr (open_ee e x x).


(* ********************************************************************** *)
(** * #<a name="env"></a># Environments *)

(** In our presentation of System F with subtyping, we use a single
    environment for both typing and subtyping assumptions.  We
    formalize environments by representing them as association lists
    (lists of pairs of keys and values) whose keys are atoms.

    The Metatheory and MetatheoryEnv libraries provide functions,
    predicates, tactics, notations and lemmas that simplify working
    with environments.  They treat environments as lists of type [list
    (atom * A)].  The notation [(x ~ a)] denotes a list consisting of
    a single binding from [x] to [a].

    Since environments map [atom]s, the type [A] should encode whether
    a particular binding is a typing or subtyping assumption.  Thus,
    we instantiate [A] with the type [binding], defined below. *)

Inductive binding : Set :=
  | bind_sub : typ -> binding
  | bind_typ : qtyp -> binding
  | bind_qua : qua -> binding.


(** A binding [(X ~ bind_sub T)] records that a type variable [X] is a
    subtype of [T], and a binding [(x ~ bind_typ U)] records that an
    expression variable [x] has type [U].

    We define an abbreviation [env] for the type of environments, and
    an abbreviation [empty] for the empty environment.

    Note: Each instance of [Notation] below defines an abbreviation
    since the left-hand side consists of a single identifier that is
    not in quotes.  These abbreviations are used for both parsing (the
    left-hand side is equivalent to the right-hand side in all
    contexts) and printing (the right-hand side is pretty-printed as
    the left-hand side).  Since [nil] is normally a polymorphic
    constructor whose type argument is implicit, we prefix the name
    with "[@]" to signal to Coq that we are going to supply arguments
    to [nil] explicitly. *)

Notation env := (list (atom * binding)).
Notation empty := (@nil (atom * binding)).

(** #<b>#Examples:#</b># We use a convention where environments are
    never built using a cons operation [((x, a) :: E)] where [E] is
    non-[nil].  This makes the shape of environments more uniform and
    saves us from excessive fiddling with the shapes of environments.
    For example, Coq's tactics sometimes distinguish between consing
    on a new binding and prepending a one element list, even though
    the two operations are convertible with each other.

    Consider the following environments written in informal notation.
<<
  1. (empty environment)
  2. x : T
  3. x : T, Y <: S
  4. E, x : T, F
>>  In the third example, we have an environment that binds an
    expression variable [x] to [T] and a type variable [Y] to [S].
    In Coq, we would write these environments as follows.
<<
  1. empty
  2. x ~ bind_typ T
  3. Y ~ bind_sub S ++ x ~ bind_typ T
  4. F ++ x ~ bind_typ T ++ E
>> The symbol "[++]" denotes list concatenation and associates to the
    right.  (That notation is defined in Coq's List library.)  Note
    that in Coq, environments grow on the left, since that is where
    the head of a list is. *)


(* ********************************************************************** *)
(** * #<a name="wf"></a># Well-formedness *)

(** A type [T] is well-formed with respect to an environment [E],
    denoted [(wf_typ E T)], when [T] is locally-closed and its free
    variables are bound in [E].  We need this relation in order to
    restrict the subtyping and typing relations, defined below, to
    contain only well-formed types.  (This relation is missing in the
    original statement of the POPLmark Challenge.)

    Note: It is tempting to define the premise of [wf_typ_var] as [(X
    `in` dom E)], since that makes the rule easier to apply (no need
    to guess an instantiation for [U]).  Unfortunately, this is
    incorrect.  We need to check that [X] is bound as a type-variable,
    not an expression-variable; [(dom E)] does not distinguish between
    the two kinds of bindings. *)

Inductive wf_qua : env -> qua -> Prop :=
  | wf_qua_top : forall E,
      wf_qua E qua_top
  | wf_qua_fvar : forall R E (X : atom),
      binds X (bind_qua R) E ->
      wf_qua E (qua_fvar X)
  | wf_qua_term_fvar : forall T E (x : atom),
      binds x (bind_typ T) E ->
      wf_qua E (qua_fvar x)
  | wf_qua_meet : forall E Q1 Q2,
      wf_qua E Q1 ->
      wf_qua E Q2 ->
      wf_qua E (qua_meet Q1 Q2)
  | wf_qua_join : forall E Q1 Q2,
      wf_qua E Q1 ->
      wf_qua E Q2 ->
      wf_qua E (qua_join Q1 Q2)
  | wf_qua_bot : forall E,
      wf_qua E qua_bot
.

Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_top : forall E,
      wf_typ E typ_top
  | wf_typ_var : forall U E (X : atom),
      binds X (bind_sub U) E ->
      wf_typ E (typ_fvar X)
  | wf_typ_arrow : forall L E T1 T2,
      wf_qtyp E T1 ->
      (forall X : atom, X `notin` L ->
        wf_qtyp (X ~ bind_typ T1 ++ E) (open_qqt T2 X)) ->
      wf_typ E (typ_arrow T1 T2)
  | wf_typ_all : forall L E T1 T2,
      wf_typ E T1 ->
      (forall X : atom, X `notin` L ->
        wf_qtyp (X ~ bind_sub T1 ++ E) (open_tqt T2 X)) ->
      wf_typ E (typ_all T1 T2)
  | wf_typ_qall : forall L E T1 T2,
      wf_qua E T1 ->
      (forall X : atom, X `notin` L ->
        wf_qtyp (X ~ bind_qua T1 ++ E) (open_qqt T2 X)) ->
      wf_typ E (typ_qall T1 T2)
  | wf_typ_sum : forall E T1 T2,
      wf_qtyp E T1 ->
      wf_qtyp E T2 ->
      wf_typ E (typ_sum T1 T2)
  | wf_typ_pair : forall E T1 T2,
      wf_qtyp E T1 ->
      wf_qtyp E T2 ->
      wf_typ E (typ_pair T1 T2)
with wf_qtyp : env -> qtyp -> Prop :=
  | wf_qtyp_qtyp : forall E Q T,
      wf_qua E Q ->
      wf_typ E T ->
      wf_qtyp E (qtyp_qtyp Q T)
.

(** An environment [E] is well-formed, denoted [(wf_env E)], if each
    atom is bound at most at once and if each binding is to a
    well-formed type.  This is a stronger relation than the [uniq]
    relation defined in the MetatheoryEnv library.  We need this
    relation in order to restrict the subtyping and typing relations,
    defined below, to contain only well-formed environments.  (This
    relation is missing in the original statement of the POPLmark
    Challenge.)  *)

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) (T : typ),
      wf_env E ->
      wf_typ E T ->
      X `notin` dom E ->
      wf_env (X ~ bind_sub T ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : qtyp),
      wf_env E ->
      wf_qtyp E T ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ T ++ E)
  | wf_env_qua : forall (E : env) (X : atom) (Q : qua),
      wf_env E ->
      wf_qua E Q ->
      X `notin` dom E ->
      wf_env (X ~ bind_qua Q ++ E)
.

(* ********************************************************************** *)
(** * #<a name="sub"></a># Subtyping *)

(** The definition of subtyping is straightforward.  It uses the
    [binds] relation from the MetatheoryEnv library (in the
    [sub_trans_tvar] case) and cofinite quantification (in the
    [sub_all] case). *)

Inductive subqual : env -> qua -> qua -> Prop :=
  | subqual_top : forall E Q,
      wf_env E ->
      wf_qua E Q ->
      subqual E Q qua_top
  | subqual_bot : forall E Q,
      wf_env E ->
      wf_qua E Q ->
      subqual E qua_bot Q
  | subqual_refl_qvar : forall E X,
      wf_env E ->
      wf_qua E (qua_fvar X) ->
      subqual E (qua_fvar X) (qua_fvar X)
  | subqual_trans_qvar : forall R E Q X,
      binds X (bind_qua R) E ->
      subqual E R Q ->
      subqual E (qua_fvar X) Q
  | subqual_trans_term_qvar : forall R E T Q X,
      binds X (bind_typ (qtyp_qtyp R T)) E ->
      subqual E R Q ->
      subqual E (qua_fvar X) Q
  | subqual_join_inl : forall E R1 R2 Q,
      subqual E Q R1 ->
      wf_qua E R2 ->
      subqual E Q (qua_join R1 R2)
  | subqual_join_inr : forall E R1 R2 Q,
      wf_qua E R1 ->
      subqual E Q R2 ->
      subqual E Q (qua_join R1 R2)
  | subqual_join_elim : forall E R1 R2 Q,
      subqual E R1 Q ->
      subqual E R2 Q ->
      subqual E (qua_join R1 R2) Q
  | subqual_meet_eliml : forall E R1 R2 Q,
      subqual E R1 Q ->
      wf_qua E R2 ->
      subqual E (qua_meet R1 R2) Q
  | subqual_meet_elimr : forall E R1 R2 Q,
      wf_qua E R1 ->
      subqual E R2 Q ->
      subqual E (qua_meet R1 R2) Q
  | subqual_meet_intro : forall E R1 R2 Q,
      subqual E Q R1 ->
      subqual E Q R2 ->
      subqual E Q (qua_meet R1 R2)
(*  | subqual_dist : forall E Q R S Q' R' S',
      subqual E Q Q' ->
      subqual E R R' ->
      subqual E S S' ->
      subqual E (qua_meet Q (qua_join R S))
                (qua_join (qua_meet Q' R') (qua_meet Q' S')) *)
.


Inductive sub : env -> typ -> typ -> Prop :=
  | sub_top : forall E S,
      wf_env E ->
      wf_typ E S ->
      sub E S typ_top
  | sub_refl_tvar : forall E X,
      wf_env E ->
      wf_typ E (typ_fvar X) ->
      sub E (typ_fvar X) (typ_fvar X)
  | sub_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      sub E U T ->
      sub E (typ_fvar X) T
  | sub_arrow : forall L E S1 S2 T1 T2,
      subqtype E T1 S1 ->
      (forall X : atom, X `notin` L ->
        subqtype (X ~ bind_typ T1 ++ E) (open_qqt S2 X) (open_qqt T2 X)) ->
      sub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  | sub_all : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      (forall X : atom, X `notin` L ->
          subqtype (X ~ bind_sub T1 ++ E) (open_tqt S2 X) (open_tqt T2 X)) ->
      sub E (typ_all S1 S2) (typ_all T1 T2)
  | sub_qall : forall L E S1 S2 T1 T2,
      subqual E T1 S1 ->
      (forall X : atom, X `notin` L ->
          subqtype (X ~ bind_qua T1 ++ E) (open_qqt S2 X) (open_qqt T2 X)) ->
      sub E (typ_qall S1 S2) (typ_qall T1 T2)
  | sub_sum : forall E S1 S2 T1 T2,
      subqtype E S1 T1 ->
      subqtype E S2 T2 ->
      sub E (typ_sum S1 S2) (typ_sum T1 T2)
  | sub_pair : forall E S1 S2 T1 T2,
      subqtype E S1 T1 ->
      subqtype E S2 T2 ->
      sub E (typ_pair S1 S2) (typ_pair T1 T2)
with subqtype : env -> qtyp -> qtyp -> Prop :=
  | sub_qtyp_qtyp : forall E Q1 T1 Q2 T2,
      subqual E Q1 Q2 ->
      sub E T1 T2 ->
      subqtype E (qtyp_qtyp Q1 T1) (qtyp_qtyp Q2 T2)
.


(* ********************************************************************** *)
(** * #<a name="typing_doc"></a># Typing *)

(** The definition of typing is straightforward.  It uses the [binds]
    relation from the MetatheoryEnv library (in the [typing_var] case)
    and cofinite quantification in the cases involving binders (e.g.,
    [typing_abs] and [typing_tabs]). *)

Fixpoint fv_exp_for_qua (e : exp)  {struct e} : qua :=
  match e with
  | exp_bvar i => qua_bot
  | exp_fvar x => qua_fvar x
  | exp_abs P V e1 => (fv_exp_for_qua e1)
  | exp_app e1 e2 q => (qua_join (fv_exp_for_qua e1) (fv_exp_for_qua e2))
  | exp_tabs P V e1 => (fv_exp_for_qua e1)
  | exp_tapp e1 V => (fv_exp_for_qua e1)
  | exp_qabs P Q e1 => (fv_exp_for_qua e1)
  | exp_qapp e1 Q => (fv_exp_for_qua e1)
  | exp_let q e1 e2 => (qua_join (fv_exp_for_qua e1) (fv_exp_for_qua e2))
  | exp_inl P e1 => (fv_exp_for_qua e1)
  | exp_inr P e2 => (fv_exp_for_qua e2)
  | exp_case e1 q1 e2 q2 e3 => (qua_join (fv_exp_for_qua e1) (qua_join 
      (fv_exp_for_qua e2) (fv_exp_for_qua e3)))
  | exp_pair P e1 e2 => (qua_join (fv_exp_for_qua e1) (fv_exp_for_qua e2))
  | exp_first e1 => (fv_exp_for_qua e1)
  | exp_second e2 => (fv_exp_for_qua e2)
  | exp_ref P e1 => (fv_exp_for_qua e1)
  | exp_ref_label P l => qua_bot
  | exp_deref e1 => (fv_exp_for_qua e1)
  | exp_set_ref e1 e2 => (qua_join (fv_exp_for_qua e1) (fv_exp_for_qua e2))
  | exp_upqual P e1 => (fv_exp_for_qua e1)
  | exp_check P e1 => (fv_exp_for_qua e1)
  end.

Inductive typing : env -> exp -> qtyp -> Prop :=
  | typing_var : forall E x Q S,
      wf_env E ->
      binds x (bind_typ (qtyp_qtyp Q S)) E ->
      typing E (exp_fvar x) (qtyp_qtyp (qua_fvar x) S)
  | typing_abs : forall L P E V e1 T1,
      subqual E (fv_exp_for_qua e1) P ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ V ++ E) (open_ee e1 x x) (open_qqt T1 x)) ->
      typing E (exp_abs P V e1) (qtyp_qtyp P (typ_arrow V T1))
  | typing_app : forall Q R T1 E e1 e2 T2,
      typing E e1 (qtyp_qtyp Q (typ_arrow (qtyp_qtyp R T1) T2)) ->
      typing E e2 (qtyp_qtyp R T1) ->
      typing E (exp_app e1 e2 R) (open_qqt T2 R)
  | typing_tabs : forall L P E V e1 T1,
      subqual E (fv_exp_for_qua e1) P ->
      (forall X : atom, X `notin` L ->
        typing (X ~ bind_sub V ++ E) (open_te e1 X) (open_tqt T1 X)) ->
      typing E (exp_tabs P V e1) (qtyp_qtyp P (typ_all V T1))
  | typing_tapp : forall Q T1 E e1 T T2,
      typing E e1 (qtyp_qtyp Q (typ_all T1 T2)) ->
      sub E T T1 ->
      typing E (exp_tapp e1 T) (open_tqt T2 T)
  | typing_qabs : forall L E P Q e1 T1,
      subqual E (fv_exp_for_qua e1) P ->
      (forall X : atom, X `notin` L ->
        typing (X ~ bind_qua Q ++ E) (open_qe e1 X) (open_qqt T1 X)) ->
      typing E (exp_qabs P Q e1) (qtyp_qtyp P (typ_qall Q T1))
  | typing_qapp : forall R Q E e1 Q1 T,
      typing E e1 (qtyp_qtyp R (typ_qall Q1 T)) ->
      subqual E Q Q1 ->
      typing E (exp_qapp e1 Q) (open_qqt T Q)
  | typing_sub : forall S E e T,
      typing E e S ->
      subqtype E S T ->
      typing E e T
  | typing_let : forall L Q S T2 e1 e2 E,
      typing E e1 (qtyp_qtyp Q S) ->
      wf_qtyp E T2 ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ (qtyp_qtyp Q S) ++ E) (open_ee e2 x x) T2) ->
      typing E (exp_let Q e1 e2) T2
  | typing_inl : forall P Q1 S1 T2 e1 E,
      subqual E Q1 P ->
      typing E e1 (qtyp_qtyp Q1 S1) ->
      wf_qtyp E T2 ->
      typing E (exp_inl P e1) (qtyp_qtyp P (typ_sum (qtyp_qtyp Q1 S1) T2))
  | typing_inr : forall P T1 Q2 S2 e1 E,
      subqual E Q2 P ->
      typing E e1 (qtyp_qtyp Q2 S2) ->
      wf_qtyp E T1 ->
      typing E (exp_inr P e1) (qtyp_qtyp P (typ_sum T1 (qtyp_qtyp Q2 S2)))
  | typing_case : forall L R Q1 S1 Q2 S2 T e1 e2 e3 E,
      typing E e1 (qtyp_qtyp R (typ_sum (qtyp_qtyp Q1 S1) (qtyp_qtyp Q2 S2))) ->
      wf_qtyp E T ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ (qtyp_qtyp Q1 S1) ++ E) (open_ee e2 x x) T) ->
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ (qtyp_qtyp Q2 S2) ++ E) (open_ee e3 x x) T) ->
      typing E (exp_case e1 Q1 e2 Q2 e3) T
  | typing_pair : forall P Q1 S1 Q2 S2 e1 e2 E,
      subqual E (qua_join Q1 Q2) P ->
      typing E e1 (qtyp_qtyp Q1 S1) ->
      typing E e2 (qtyp_qtyp Q2 S2) ->
      typing E (exp_pair P e1 e2) (qtyp_qtyp P (typ_pair (qtyp_qtyp Q1 S1) (qtyp_qtyp Q2 S2)))
  | typing_first : forall Q T1 T2 e E,
      typing E e (qtyp_qtyp Q (typ_pair T1 T2)) ->
      typing E (exp_first e) T1
  | typing_second : forall Q T1 T2 e E,
      typing E e (qtyp_qtyp Q (typ_pair T1 T2)) ->
      typing E (exp_second e) T2
  | typing_upqual : forall E Q T P e,
      typing E e (qtyp_qtyp Q T) ->
      subqual E Q P ->
      typing E (exp_upqual P e) (qtyp_qtyp P T)
  | typing_check : forall E Q T P e,
      typing E e (qtyp_qtyp Q T) ->
      subqual E Q P ->
      typing E (exp_check P e) (qtyp_qtyp Q T)
.


(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall P T e1,
      expr (exp_abs P T e1) ->
      value (exp_abs P T e1)
  | value_tabs : forall P T e1,
      expr (exp_tabs P T e1) ->
      value (exp_tabs P T e1)
 | value_qabs : forall P Q e1,
      expr (exp_qabs P Q e1) ->
      value (exp_qabs P Q e1)
  | value_inl : forall P e1,
      qual P ->
      value e1 ->
      value (exp_inl P e1)
  | value_inr : forall P e1,
      qual P ->
      value e1 ->
      value (exp_inr P e1)
  | value_pair : forall P e1 e2,
      qual P ->
      value e1 ->
      value e2 ->
      value (exp_pair P e1 e2)
.


(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)

Inductive red : exp -> exp -> Prop :=
  | red_app_1 : forall e1 e1' e2 Q,
      expr e2 ->
      qual Q ->
      red e1 e1' ->
      red (exp_app e1 e2 Q) (exp_app e1' e2 Q)
  | red_app_2 : forall e1 e2 e2' Q,
      value e1 ->
      qual Q ->
      red e2 e2' ->
      red (exp_app e1 e2 Q) (exp_app e1 e2' Q)
  | red_tapp : forall e1 e1' V,
      type V ->
      red e1 e1' ->
      red (exp_tapp e1 V) (exp_tapp e1' V)
  | red_qapp : forall e1 e1' R,
      qual R ->
      red e1 e1' ->
      red (exp_qapp e1 R) (exp_qapp e1' R)
  | red_abs : forall P T e1 v2 Q,
      expr (exp_abs P T e1) ->
      value v2 ->
      qual Q ->
      red (exp_app (exp_abs P T e1) v2 Q) (open_ee e1 v2 Q)
  | red_tabs : forall P T1 e1 T2,
      expr (exp_tabs P T1 e1) ->
      type T2 ->
      red (exp_tapp (exp_tabs P T1 e1) T2) (open_te e1 T2)
  | red_qabs : forall P Q1 e1 Q2,
      expr (exp_qabs P Q1 e1) ->
      qual Q2 ->
      red (exp_qapp (exp_qabs P Q1 e1) Q2) (open_qe e1 Q2)
  | red_let_1 : forall Q e1 e1' e2,
      qual Q ->
      red e1 e1' ->
      body_e e2 ->
      red (exp_let Q e1 e2) (exp_let Q e1' e2)
  | red_let : forall Q v1 e2,
      qual Q ->
      value v1 ->
      body_e e2 ->
      red (exp_let Q v1 e2) (open_ee e2 v1 Q)
  | red_inl_1 : forall P e1 e1',
      qual P ->
      red e1 e1' ->
      red (exp_inl P e1) (exp_inl P e1')
  | red_inr_1 : forall P e1 e1',
      qual P ->
      red e1 e1' ->
      red (exp_inr P e1) (exp_inr P e1')
  | red_case_1 : forall e1 e1' Q1 Q2 e2 e3,
      qual Q1 ->
      qual Q2 ->
      red e1 e1' ->
      body_e e2 ->
      body_e e3 ->
      red (exp_case e1 Q1 e2 Q2 e3) (exp_case e1' Q1 e2 Q2 e3)
  | red_case_inl : forall P v1 Q1 Q2 e2 e3,
      qual P ->
      qual Q1 ->
      qual Q2 ->
      value v1 ->
      body_e e2 ->
      body_e e3 ->
      red (exp_case (exp_inl P v1) Q1 e2 Q2 e3) (open_ee e2 v1 Q1)
  | red_case_inr : forall P v1 Q1 Q2 e2 e3,
      qual P ->
      qual Q1 ->
      qual Q2 ->
      value v1 ->
      body_e e2 ->
      body_e e3 ->
      red (exp_case (exp_inr P v1) Q1 e2 Q2 e3) (open_ee e3 v1 Q2)
  | red_pair_1 : forall P e1 e1' e2,
      qual P ->
      red e1 e1' ->
      expr e2 ->
      red (exp_pair P e1 e2) (exp_pair P e1' e2)
  | red_pair_2 : forall P v1 e2 e2',
      qual P ->
      value v1 ->
      red e2 e2' ->
      red (exp_pair P v1 e2) (exp_pair P v1 e2')
  | red_pair_first_1 : forall e1 e1',
      red e1 e1' ->
      red (exp_first e1) (exp_first e1')
  | red_pair_second_1 : forall e1 e1',
      red e1 e1' ->
      red (exp_second e1) (exp_second e1')
  | red_pair_first_2 : forall P v1 v2,
      qual P ->
      value v1 ->
      value v2 ->
      red (exp_first (exp_pair P v1 v2)) v1
  | red_pair_second_2 : forall P v1 v2,
      qual P ->
      value v1 ->
      value v2 ->
      red (exp_second (exp_pair P v1 v2)) v2
  | red_upqual_1 : forall P e1 e1',
      qual P ->
      red e1 e1' ->
      red (exp_upqual P e1) (exp_upqual P e1')
  | red_upqual_abs : forall P Q cP cQ V e1,
      qual P ->
      qual Q ->
      expr (exp_abs Q V e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_upqual P (exp_abs Q V e1)) (exp_abs P V e1)
  | red_upqual_tabs : forall P Q cP cQ V e1,
      qual P ->
      qual Q ->
      expr (exp_tabs Q V e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_upqual P (exp_tabs Q V e1)) (exp_tabs P V e1)
  | red_upqual_qabs : forall P Q cP cQ V e1,
      qual P ->
      qual Q ->
      expr (exp_qabs Q V e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_upqual P (exp_qabs Q V e1)) (exp_qabs P V e1)
   | red_upqual_inl : forall P Q cP cQ e1,
      qual P ->
      qual Q ->
      expr (exp_inl Q e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_upqual P (exp_inl Q e1)) (exp_inl P e1)
   | red_upqual_inr : forall P Q cP cQ e1,
      qual P ->
      qual Q ->
      expr (exp_inr Q e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_upqual P (exp_inr Q e1)) (exp_inr P e1)
   | red_upqual_pair : forall P Q cP cQ e1 e2,
      qual P ->
      qual Q ->
      expr (exp_pair Q e1 e2) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_upqual P (exp_pair Q e1 e2)) (exp_pair P e1 e2)
  | red_check_1 : forall P e1 e1',
      qual P ->
      red e1 e1' ->
      red (exp_check P e1) (exp_check P e1')
  | red_check_abs : forall P Q cP cQ V e1,
      qual P ->
      qual Q ->
      expr (exp_abs Q V e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_check P (exp_abs Q V e1)) (exp_abs Q V e1)
  | red_check_tabs : forall P Q cP cQ V e1,
      qual P ->
      qual Q ->
      expr (exp_tabs Q V e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_check P (exp_tabs Q V e1)) (exp_tabs Q V e1)
  | red_check_qabs : forall P Q cP cQ V e1,
      qual P ->
      qual Q ->
      expr (exp_qabs Q V e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_check P (exp_qabs Q V e1)) (exp_qabs Q V e1)
   | red_check_inl : forall P Q cP cQ e1,
      qual P ->
      qual Q ->
      expr (exp_inl Q e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_check P (exp_inl Q e1)) (exp_inl Q e1)
   | red_check_inr : forall P Q cP cQ e1,
      qual P ->
      qual Q ->
      expr (exp_inr Q e1) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_check P (exp_inr Q e1)) (exp_inr Q e1)
   | red_check_pair : forall P Q cP cQ e1 e2,
      qual P ->
      qual Q ->
      expr (exp_pair Q e1 e2) ->
      concretize P = Some cP ->
      concretize Q = Some cQ ->
      cqua_compatible cQ cP ->
      red (exp_check P (exp_pair Q e1 e2)) (exp_pair Q e1 e2)
.


(* ********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We declare most constructors as [Hint]s to be used by the [auto]
    and [eauto] tactics.  We exclude constructors from the subtyping
    and typing relations that use cofinite quantification.  It is
    unlikely that [eauto] will find an instantiation for the finite
    set [L], and in those cases, [eauto] can take some time to fail.
    (A priori, this is not obvious.  In practice, one adds as hints
    all constructors and then later removes some constructors when
    they cause proof search to take too long.) *)

#[export] Hint Constructors type qtype expr qual wf_qua wf_typ wf_qtyp wf_env value red : core.
#[export] Hint Constructors subqual subqtype: core.
#[export] Hint Resolve sub_top sub_refl_tvar sub_arrow : core.
#[export] Hint Resolve sub_sum sub_pair : core.
#[export] Hint Resolve typing_var typing_app typing_tapp typing_sub typing_qapp : core.
#[export] Hint Resolve typing_inl typing_inr typing_pair typing_first typing_second : core.
#[export] Hint Resolve typing_upqual typing_check : core.
#[export] Hint Constructors  cqua_compatible : core.