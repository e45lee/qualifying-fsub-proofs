(** Properties of Free Lattices
    
    Here, we present a mechanized, syntactic proof of the crux of 
    Galatos' paper [1]; that transitivity can be made redundant
    with the right, syntax-directed, Gentzen-style natural deduction
    rules for the equational theory of lattices.
    
    
    [1] https://link.springer.com/article/10.1007/s11225-023-10063-4
*)

Require Export Base.LabelMap.
Require Export Base.Label.
Require Export FqMeta.Metatheory.
Require Export String.
Require Export Coq.Program.Equality.


(** A [qua], a qualifier term, consists of either top, bottom,
    variables, meets, and joins. *)
Inductive qua : Set :=
  | qua_top : qua
  | qua_fvar : atom -> qua
  | qua_meet : qua -> qua -> qua
  | qua_join : qua -> qua -> qua
  | qua_bot : qua
.

(** [subqual], restricted to the free lattice setting. *)
Inductive subqual : qua -> qua -> Prop :=
  | subqual_top : forall Q,
      subqual Q qua_top
  | subqual_bot : forall Q,
      subqual qua_bot Q
  | subqual_refl_qvar : forall  X,
      subqual (qua_fvar X) (qua_fvar X)
  | subqual_join_inl : forall R1 R2 Q,
      subqual Q R1 ->
      subqual Q (qua_join R1 R2)
  | subqual_join_inr : forall R1 R2 Q,
      subqual Q R2 ->
      subqual Q (qua_join R1 R2)
  | subqual_join_elim : forall R1 R2 Q,
      subqual R1 Q ->
      subqual R2 Q ->
      subqual (qua_join R1 R2) Q
  | subqual_meet_eliml : forall R1 R2 Q,
      subqual R1 Q ->
      subqual (qua_meet R1 R2) Q
  | subqual_meet_elimr : forall R1 R2 Q,
      subqual R2 Q ->
      subqual (qua_meet R1 R2) Q
  | subqual_meet_intro : forall R1 R2 Q,
      subqual Q R1 ->
      subqual Q R2 ->
      subqual Q (qua_meet R1 R2)
.

#[export] Hint Constructors subqual : core.

Lemma subqual_reflexivity : forall T,
  subqual T T.
Proof with eauto 6.
  intros T.
  induction T...
Qed.

Definition transitivity_on_subqual Q := forall S T,
  subqual S Q -> subqual Q T -> subqual S T.

Lemma subqual_join_split : forall R1 R2 T,
  subqual (qua_join R1 R2) T ->
  subqual R1 T /\ subqual R2 T.
Proof with eauto.
  intros * Sub.
  dependent induction Sub; try solve [intuition eauto]...
  - edestruct IHSub...
  - edestruct IHSub...
  - edestruct IHSub1...
    edestruct IHSub2...
Defined.

Lemma subqual_meet_split : forall P Q R,
  subqual P (qua_meet Q R) ->
  subqual P Q /\ subqual P R.
Proof with intuition eauto.
  intros * Sub.
  dependent induction Sub...
  - destruct IHSub1 with (Q := Q) (R := R)...
    destruct IHSub2 with (Q := Q) (R := R)...
  - destruct IHSub1 with (Q := Q) (R := R)...
    destruct IHSub2 with (Q := Q) (R := R)...
  - destruct IHSub with (Q := Q) (R := R)...
  - destruct IHSub with (Q := Q) (R := R)...
  - destruct IHSub with (Q := Q) (R := R)...
  - destruct IHSub with (Q := Q) (R := R)...
Qed.

Lemma subqual_transitivity : forall Q,
  transitivity_on_subqual Q.
Proof with simpl_env; auto.
  unfold transitivity_on_subqual.
  intros Q S T SsubQ QsubT.
  generalize dependent T.
  induction SsubQ; intros T QsubT...
  * dependent induction QsubT...
  * eapply subqual_join_split in QsubT as [SubL SubR]...
  * eapply subqual_join_split in QsubT as [SubL SubR]...
  * remember (qua_meet R1 R2) as R.
    induction QsubT; inversion HeqR; subst...
Qed.
