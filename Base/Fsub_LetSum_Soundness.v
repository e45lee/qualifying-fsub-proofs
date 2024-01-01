(** Type-safety proofs for Fsub.

    Authors: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    In parentheses are given the label of the corresponding lemma in
    the appendix (informal proofs) of the POPLmark Challenge.

    Table of contents:
      - #<a href="##subtyping">Properties of subtyping</a>#
      - #<a href="##typing">Properties of typing</a>#
      - #<a href="##preservation">Preservation</a>#
      - #<a href="##progress">Progress</a># *)
Require Import Base.Tactics.
Require Import Coq.Program.Equality.
Require Export Base.Fsub_LetSum_Lemmas.


(* ********************************************************************** *)
(** * #<a name="subtyping"></a># Properties of subtyping *)


(* ********************************************************************** *)
(** ** Reflexivity (1) *)
Lemma subqual_reflexivity : forall E T,
  wf_env E ->
  wf_qua E T ->
  subqual E T T.
Proof with eauto 6.
  intros E T Ok Wf.
  induction Wf...
Qed.

Lemma sub_reflexivity : forall E T,
  wf_env E ->
  wf_typ E T ->
  sub E T T
with subqtype_reflexivity : forall E T,
  wf_env E ->
  wf_qtyp E T ->
  subqtype E T T.
Proof with eauto using subqual_reflexivity.
------
  clear sub_reflexivity.
  intros E T Ok Wf.
  induction Wf...
  pick fresh Y and apply sub_all...
  pick fresh Y and apply sub_qall...
------
  clear subqtype_reflexivity.
  intros E T Ok Wf.
  induction Wf...
Qed.


(* ********************************************************************** *)
(** ** Weakening (2) *)

Lemma subqual_weakening : forall E F G S T,
  subqual (G ++ E) S T ->
  wf_env (G ++ F ++ E) ->
  subqual (G ++ F ++ E) S T.
Proof with simpl_env; auto 6 using wf_qua_weakening.
  intros E F G S T Sub Ok.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Sub; intros G Ok EQ; subst...
  Case "subqual_trans_qvar".
    apply (subqual_trans_qvar R)...
Qed.

Lemma sub_weakening : forall E F G S T,
  sub (G ++ E) S T ->
  wf_env (G ++ F ++ E) ->
  sub (G ++ F ++ E) S T
with subqtype_weakening : forall E F G S T,
  subqtype (G ++ E) S T ->
  wf_env (G ++ F ++ E) ->
  subqtype (G ++ F ++ E) S T.
Proof with simpl_env; auto using wf_typ_weakening, subqual_weakening,
  wf_qtyp_weakening, wf_qua_weakening.
------
  clear sub_weakening.
  intros E F G S T Sub Ok.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Sub; intros G Ok EQ; subst...
  Case "sub_trans_tvar".
    apply (sub_trans_tvar U)...
  Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- app_assoc.
    apply subqtype_weakening...
  Case "sub_qall".
    pick fresh Y and apply sub_qall...
    rewrite <- app_assoc.
    apply subqtype_weakening...
------
  clear subqtype_weakening.
  intros E F G S T Sub Ok.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Sub; intros G Ok EQ; subst...
Qed.


(* ********************************************************************** *)
(** ** Narrowing and transitivity (3) *)

Definition transitivity_on_sub Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.
Definition transitivity_on_subqtype Q := forall E S T,
  subqtype E S Q -> subqtype E Q T -> subqtype E S T.
Definition transitivity_on_subqual Q := forall E S T,
  subqual E S Q -> subqual E Q T -> subqual E S T.

Lemma subqual_narrowing_qua_aux : forall Q F E Z P S T,
  transitivity_on_subqual Q ->
  subqual (F ++ Z ~ bind_qua Q ++ E) S T ->
  subqual E P Q ->
  subqual (F ++ Z ~ bind_qua P ++ E) S T.
Proof with simpl_env; eauto using wf_qua_narrowing_qua,
  wf_env_narrowing_qua.
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ Z ~ bind_qua Q ++ E) as G. generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply (subqual_trans_qvar P); [ eauto using fresh_mid_head | ].
      apply TransQ.
      SSCase "P <: Q".
        rewrite_env (empty ++ (F ++ Z ~ bind_qua P) ++ E).
        apply subqual_weakening...
      SSCase "Q <: T".
        analyze_binds_uniq H.
        injection BindsTacVal; intros; subst...
    SCase "X <> Z".
      apply (subqual_trans_qvar R)...
Qed.

Lemma subqual_narrowing_sub_aux : forall Q F E Z P S T,
  transitivity_on_sub Q ->
  subqual (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub E P Q ->
  subqual (F ++ Z ~ bind_sub P ++ E) S T.
Proof with simpl_env; eauto using wf_qua_narrowing_sub,
  wf_env_narrowing_sub.
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G. generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "sub_trans_tvar".
    destruct (X == Z); subst...
    exfalso. analyze_binds_uniq H.
Qed.

Lemma sub_narrowing_sub_aux : forall Q F E Z P S T,
  transitivity_on_sub Q ->
  sub (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub E P Q ->
  sub (F ++ Z ~ bind_sub P ++ E) S T
with subqtype_narrowing_sub_aux : forall Q F E Z P S T,
  transitivity_on_sub Q ->
  subqtype (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub E P Q ->
  subqtype (F ++ Z ~ bind_sub P ++ E) S T.
Proof with simpl_env; eauto using wf_typ_narrowing_sub, wf_env_narrowing_sub,
  subqual_narrowing_sub_aux.
------
  clear sub_narrowing_sub_aux.
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G. generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply (sub_trans_tvar P); [ eauto using fresh_mid_head | ].
      apply TransQ.
      SSCase "P <: Q".
        rewrite_env (empty ++ (F ++ Z ~ bind_sub P) ++ E).
        apply sub_weakening...
      SSCase "Q <: T".
        analyze_binds_uniq H.
        injection BindsTacVal; intros; subst...
    SCase "X <> Z".
      apply (sub_trans_tvar U)...
  Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- app_assoc.
    eapply subqtype_narrowing_sub_aux...
  Case "sub_qall".
    pick fresh Y and apply sub_qall...
    rewrite <- app_assoc.
    eapply subqtype_narrowing_sub_aux...
------
  clear subqtype_narrowing_sub_aux.
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G. generalize dependent F.
  induction SsubT; intros F EQ; subst...  
Qed.

Lemma sub_narrowing_qua_aux : forall Q F E Z P S T,
  transitivity_on_subqual Q ->
  sub (F ++ Z ~ bind_qua Q ++ E) S T ->
  subqual E P Q ->
  sub (F ++ Z ~ bind_qua P ++ E) S T
with subqtype_narrowing_qua_aux : forall Q F E Z P S T,
  transitivity_on_subqual Q ->
  subqtype (F ++ Z ~ bind_qua Q ++ E) S T ->
  subqual E P Q ->
  subqtype (F ++ Z ~ bind_qua P ++ E) S T.
Proof with simpl_env; eauto using wf_typ_narrowing_qua, wf_env_narrowing_qua,
  subqual_narrowing_qua_aux.
------
  clear sub_narrowing_qua_aux.
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ Z ~ bind_qua Q ++ E) as G. generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      exfalso. analyze_binds_uniq H...
    SCase "X <> Z".
      apply (sub_trans_tvar U)...
  Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- app_assoc.
    eapply subqtype_narrowing_qua_aux...
  Case "sub_qall".
    pick fresh Y and apply sub_qall...
    rewrite <- app_assoc.
    eapply subqtype_narrowing_qua_aux...
------
  clear subqtype_narrowing_qua_aux.
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ Z ~ bind_qua Q ++ E) as G. generalize dependent F.
  induction SsubT; intros F EQ; subst...  
Qed.

Lemma subqual_join_split : forall E R1 R2 T,
  subqual E (qua_join R1 R2) T ->
  subqual E R1 T /\ subqual E R2 T.
Proof with eauto.
  intros * Sub.
  dependent induction Sub; try solve [intuition eauto]...
  - edestruct IHSub...
  - edestruct IHSub...
  - edestruct IHSub1...
    edestruct IHSub2...
Qed.


Lemma subqual_meet_split : forall E P Q R,
  subqual E P (qua_meet Q R) ->
  subqual E P Q /\ subqual E P R.
Proof with intuition eauto.
  intros * Sub.
  dependent induction Sub...
  - eapply subqual_trans_qvar...
    eapply IHSub with (Q := Q) (R := R)...
  - eapply subqual_trans_qvar...
    eapply IHSub with (Q := Q) (R := R)...
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
  intros Q E S T SsubQ QsubT.
  generalize dependent T.
  induction SsubQ; intros T QsubT...
  * dependent induction QsubT...
  * eapply subqual_trans_qvar with (R := R)...
  * eapply subqual_join_split in QsubT as [SubL SubR]...
  * eapply subqual_join_split in QsubT as [SubL SubR]...
  * remember (qua_meet R1 R2) as R.
    induction QsubT; inversion HeqR; subst...
Qed.

Lemma sub_transitivity_rec : forall Q,
  type Q -> transitivity_on_sub Q
with subqtype_transitivity_rec : forall Q,
  qtype Q -> transitivity_on_subqtype Q.
Proof with simpl_env; auto.
------
  clear sub_transitivity_rec.
  unfold transitivity_on_sub.
  intros Q W E S T SsubQ QsubT.
  generalize dependent T.
  generalize dependent S.
  generalize dependent E.
  remember Q as Q' in |- *.
  generalize dependent Q'.
  induction W;
    intros Q' EQ E S SsubQ;
    induction SsubQ; try discriminate; inversion EQ; subst;
    intros T' QsubT;
    inversion QsubT; subst; eauto 4 using sub_trans_tvar.
  Case "sub_arrow / sub_arrow".
    apply sub_arrow.
    eapply subqtype_transitivity_rec with (Q := T1)...
    eapply subqtype_transitivity_rec with (Q := T2)...
  Case "sub_all / sub_top".
    assert (sub E (typ_all S1 S2) (typ_all T1 T2)).
      SCase "proof of assertion".
      pick fresh y and apply sub_all...
    auto.
  Case "sub_all / sub_all".
    pick fresh Y and apply sub_all.
    SCase "bounds".
      eauto.
    SCase "bodies".
      lapply (H0 Y); [ intros K | auto ].
      lapply (H6 Y); [ intros K2 | auto ].
      eapply subqtype_transitivity_rec with (Q := (open_tqt T2 Y))...
      rewrite_env (empty ++ Y ~ bind_sub T0 ++ E).
      eapply (subqtype_narrowing_sub_aux T1)...
      unshelve epose proof (IHW T1 _) as TransT1...
      unfold transitivity_on_sub; eauto using TransT1...
  Case "sub_qall / sub_top".
    assert (sub E (typ_qall S1 S2) (typ_qall Q T)).
      SCase "proof of assertion".
      pick fresh y and apply sub_qall...  
    auto.
  Case "sub_qall / sub_qall".
    pick fresh Y and apply sub_qall...
    SCase "bounds".
      eapply subqual_transitivity with (Q := Q)...
    SCase "bodies".
      lapply (H2 Y); [ intros K | auto ].
      lapply (H8 Y); [ intros K2 | auto ].
      eapply subqtype_transitivity_rec...
      rewrite_env (empty ++ Y ~ bind_qua T1 ++ E).
      eapply subqtype_narrowing_qua_aux ...
      apply subqual_transitivity.
  Case "sub_sum / sub_sum".
    eapply sub_sum...
    eapply subqtype_transitivity_rec with (Q := T1)...
    eapply subqtype_transitivity_rec with (Q := T2)...
  Case "sub_pair / sub_pair".
    eapply sub_pair...
    eapply subqtype_transitivity_rec with (Q := T1)...
    eapply subqtype_transitivity_rec with (Q := T2)...
------
  clear subqtype_transitivity_rec.
  unfold transitivity_on_subqtype.
  intros Q W E S T SsubQ QsubT.
  generalize dependent T.
  generalize dependent S.
  generalize dependent E.
  remember Q as Q' in |- *.
  generalize dependent Q'.
  induction W;
    intros Q' EQ E S SsubQ;
    induction SsubQ; try discriminate; inversion EQ; subst;
    intros T' QsubT;
    inversion QsubT; subst; eauto 4 using sub_trans_tvar.
  eapply sub_qtyp_qtyp...
    eapply subqual_transitivity with (Q := Q)...
    eapply sub_transitivity_rec with (Q := T)...
Qed.

Lemma sub_transitivity : forall Q,
  transitivity_on_sub Q.
Proof with simpl_env; auto.
  unfold transitivity_on_sub.
  intros.
  eapply sub_transitivity_rec with (Q := Q)...
Qed.

Lemma subqtype_transitivity : forall Q,
  transitivity_on_subqtype Q.
Proof with simpl_env; auto.
  unfold transitivity_on_subqtype.
  intros.
  eapply subqtype_transitivity_rec with (Q := Q)...
Qed.

Lemma sub_narrowing_sub : forall Q E F Z P S T,
  sub E P Q ->
  sub (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub (F ++ Z ~ bind_sub P ++ E) S T.
Proof.
  intros.
  eapply sub_narrowing_sub_aux; eauto.
  apply sub_transitivity.
Qed.

Lemma subqtype_narrowing_sub : forall Q E F Z P S T,
  sub E P Q ->
  subqtype (F ++ Z ~ bind_sub Q ++ E) S T ->
  subqtype (F ++ Z ~ bind_sub P ++ E) S T.
Proof.
  intros.
  eapply subqtype_narrowing_sub_aux; eauto.
  apply sub_transitivity.
Qed.

Lemma subqual_narrowing_sub : forall Q E F Z P S T,
  sub E P Q ->
  subqual (F ++ Z ~ bind_sub Q ++ E) S T ->
  subqual (F ++ Z ~ bind_sub P ++ E) S T.
Proof.
  intros.
  eapply subqual_narrowing_sub_aux; eauto.
  apply sub_transitivity.
Qed.

Lemma sub_narrowing_qua : forall Q E F Z P S T,
  subqual E P Q ->
  sub (F ++ Z ~ bind_qua Q ++ E) S T ->
  sub (F ++ Z ~ bind_qua P ++ E) S T.
Proof.
  intros.
  eapply sub_narrowing_qua_aux; eauto.
  apply subqual_transitivity.
Qed.

Lemma subqtype_narrowing_qua : forall Q E F Z P S T,
  subqual E P Q ->
  subqtype (F ++ Z ~ bind_qua Q ++ E) S T ->
  subqtype (F ++ Z ~ bind_qua P ++ E) S T.
Proof.
  intros.
  eapply subqtype_narrowing_qua_aux; eauto.
  apply subqual_transitivity.
Qed.

Lemma subqual_narrowing_qua : forall Q E F Z P S T,
  subqual E P Q ->
  subqual (F ++ Z ~ bind_qua Q ++ E) S T ->
  subqual (F ++ Z ~ bind_qua P ++ E) S T.
Proof.
  intros.
  eapply subqual_narrowing_qua_aux; eauto.
  apply subqual_transitivity.
Qed.

(* ********************************************************************** *)
(** ** Type substitution preserves subtyping (10) *)

Lemma subqual_through_subst_qq : forall Q E F Z S T P,
  subqual (F ++ Z ~ bind_qua Q ++ E) S T ->
  subqual E P Q ->
  subqual (map (subst_qb Z P) F ++ E) (subst_qq Z P S) (subst_qq Z P T).
Proof with simpl_env;
  eauto 4 using wf_qua_subst_qb, wf_env_subst_qb, wf_qua_weaken_head.
  intros Q E F Z S T P SsubT PsubQ.
  remember (F ++ Z ~ bind_qua Q ++ E) as G.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl subst_qq...
  Case "subqual_top".
    eapply subqual_top...
  Case "subqual_bot".
    eapply subqual_bot...
  Case "subqual_refl_fvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply subqual_reflexivity...
    SCase "X <> Z".
      apply subqual_reflexivity...
      inversion H0; subst.
      analyze_binds H3...
      apply (wf_qua_fvar (subst_qq Z P R))...
  Case "subqual_trans_qvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply (subqual_transitivity Q).
      SSCase "left branch".
        rewrite_env (empty ++ map (subst_qb Z P) G ++ E).
        apply subqual_weakening...
      SSCase "right branch".
        rewrite (subst_qq_fresh Z P Q).
          analyze_binds_uniq H.
            inversion BindsTacVal; subst...
          apply (notin_fv_qq_wf_qua E); eauto using fresh_mid_tail.
    SCase "X <> Z".
      apply (subqual_trans_qvar (subst_qq Z P R))...
      rewrite (map_subst_qb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      analyze_binds H... 
  Case "subqual_join_inl".
    apply subqual_join_inl...
  Case "subqual_join_inr".
    apply subqual_join_inr...
  Case "subqual_meet_eliml".
    apply subqual_meet_eliml...
  Case "subqual_meet_elimr".
    apply subqual_meet_elimr...
Qed.

Lemma subqual_through_subst_tt : forall Q E F Z S T P,
  subqual (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub E P Q ->
  subqual (map (subst_tb Z P) F ++ E) S T.
Proof with simpl_env;
  eauto 4 using wf_qua_subst_tb, wf_env_subst_tb, wf_qua_weaken_head.
  intros Q E F Z S T P SsubT PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl...
  Case "subqual_top".
    apply subqual_top...
  Case "subqual_bot".
    eapply subqual_bot...
  Case "subqual_refl_fvar".
    apply subqual_reflexivity...
  Case "subqual_trans_qvar".
    apply (subqual_trans_qvar R)...
    analyze_binds H...
    unsimpl (subst_tb Z P (bind_qua R))...
  Case "subqual_join_inl".
    apply subqual_join_inl...
  Case "subqual_join_inr".
    apply subqual_join_inr...
  Case "subqual_meet_eliml".
    apply subqual_meet_eliml...
  Case "subqual_meet_elimr".
    apply subqual_meet_elimr...
Qed.

Lemma sub_through_subst_tt : forall Q E F Z S T P,
  sub (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub E P Q ->
  sub (map (subst_tb Z P) F ++ E) (subst_tt Z P S) (subst_tt Z P T)
with subqtype_through_subst_tqt : forall Q E F Z S T P,
  subqtype (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub E P Q ->
  subqtype (map (subst_tb Z P) F ++ E) (subst_tqt Z P S) (subst_tqt Z P T).
Proof with
      simpl_env;
      eauto 4 using wf_typ_subst_tb, wf_env_subst_tb, wf_typ_weaken_head.
------
  clear sub_through_subst_tt.
  intros Q E F Z S T P SsubT PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl subst_tt...
  Case "sub_top".
    apply sub_top...
  Case "sub_refl_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply sub_reflexivity...
    SCase "X <> Z".
      apply sub_reflexivity...
      inversion H0; subst.
      analyze_binds H3...
      apply (wf_typ_var (subst_tt Z P U))...
  Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply (sub_transitivity Q).
      SSCase "left branch".
        rewrite_env (empty ++ map (subst_tb Z P) G ++ E).
        apply sub_weakening...
      SSCase "right branch".
        rewrite (subst_tt_fresh Z P Q).
          analyze_binds_uniq H.
            inversion BindsTacVal; subst...
          apply (notin_fv_tt_wf_typ E); eauto using fresh_mid_tail.
    SCase "X <> Z".
      apply (sub_trans_tvar (subst_tt Z P U))...
      rewrite (map_subst_tb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      analyze_binds H...
  Case "sub_all".
    pick fresh X and apply sub_all...
    rewrite subst_tqt_open_tqt_var...
    rewrite subst_tqt_open_tqt_var...
    rewrite_env (map (subst_tb Z P) (X ~ bind_sub T1 ++ G) ++ E).
    eapply subqtype_through_subst_tqt...
  Case "sub_qall".
    apply (sub_qall L)... 
    eapply subqual_through_subst_tt...
    intros.
    rewrite <- subst_tqt_open_qqt...
    rewrite <- subst_tqt_open_qqt...
    rewrite_env (map (subst_tb Z P) (X ~ bind_qua T1 ++ G) ++ E).
    eapply subqtype_through_subst_tqt...
------
  clear subqtype_through_subst_tqt.
  intros Q E F Z S T P SsubT PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl subst_tt...
  econstructor; eauto using subqual_through_subst_tt...
Qed.

Lemma sub_through_subst_qt : forall Q E F Z S T P,
  sub (F ++ Z ~ bind_qua Q ++ E) S T ->
  subqual E P Q ->
  sub (map (subst_qb Z P) F ++ E) (subst_qt Z P S) (subst_qt Z P T)
with subqtype_through_subst_qqt : forall Q E F Z S T P,
  subqtype (F ++ Z ~ bind_qua Q ++ E) S T ->
  subqual E P Q ->
  subqtype (map (subst_qb Z P) F ++ E) (subst_qqt Z P S) (subst_qqt Z P T).
Proof with
      simpl_env;
      eauto 4 using wf_typ_subst_qb, wf_env_subst_qb, wf_typ_weaken_head, 
        subqual_through_subst_qq.
------
  clear sub_through_subst_qt.
  intros Q E F Z S T P SsubT PsubQ.
  remember (F ++ Z ~ bind_qua Q ++ E) as G.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl subst_qt...
  Case "sub_top".
    apply sub_top...
  Case "sub_refl_tvar".
    apply sub_reflexivity...
    unsimpl (subst_qt Z P X)...
  Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      exfalso. analyze_binds_uniq H.
    SCase "X <> Z".
      apply (sub_trans_tvar (subst_qt Z P U))...
      rewrite (map_subst_qb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      analyze_binds H...
  Case "sub_all".
    pick fresh X and apply sub_all...
    rewrite subst_qqt_open_tqt_var...
    rewrite subst_qqt_open_tqt_var...
    rewrite_env (map (subst_qb Z P) (X ~ bind_sub T1 ++ G) ++ E).
    eapply subqtype_through_subst_qqt...
  Case "sub_qall".
    pick fresh X and apply sub_qall...
    rewrite subst_qqt_open_qqt_var...
    rewrite subst_qqt_open_qqt_var...
    rewrite_env (map (subst_qb Z P) (X ~ bind_qua T1 ++ G) ++ E).
    eapply subqtype_through_subst_qqt...
------
  clear subqtype_through_subst_qqt.
  intros Q E F Z S T P SsubT PsubQ.
  remember (F ++ Z ~ bind_qua Q ++ E) as G.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl subst_qt...
  econstructor; eauto using subqual_through_subst_qq...
Qed.

(* ********************************************************************** *)
(** * #<a name="typing"></a># Properties of typing *)

(* ********************************************************************** *)
(** ** Weakening (5) *)

Lemma typing_weakening : forall E F G e T,
  typing (G ++ E) e T ->
  wf_env (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof with simpl_env;
           eauto using wf_typ_weakening,
                       wf_qtyp_weakening,
                       wf_qua_weakening,
                       wf_qtyp_from_wf_env_typ,
                       wf_typ_from_wf_env_sub,
                       wf_qua_from_wf_env_qua,
                       sub_weakening,
                       subqual_weakening,
                       subqtype_weakening.
  intros E F G e T Typ.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Typ; intros G EQ Ok; subst...
  Case "typing_abs".
    pick fresh x and apply typing_abs...
    lapply (H0 x); [intros K | auto].
    rewrite <- app_assoc.
    apply (H1 x)...
  Case "typing_tabs".
    pick fresh X and apply typing_tabs...
    lapply (H0 X); [intros K | auto].
    rewrite <- app_assoc.
    apply (H1 X)...
  Case "typing_qabs".
    pick fresh X and apply typing_qabs...
    lapply (H0 X); [intros K | auto].
    rewrite <- app_assoc.
    apply (H1 X)...
  Case "typing_let".
    pick fresh x and apply typing_let...
    lapply (H0 x); [intros K | auto].
    rewrite <- app_assoc.
    apply H0...
  Case "typing_inl".
    apply typing_inl...
  Case "typing_inr".
    apply typing_inr...
  Case "typing_case".
    pick fresh x and apply typing_case...
    SCase "inl branch".
      lapply (H0 x); [intros K | auto].
      rewrite <- app_assoc.
      apply H0...
      eassert (M : wf_qtyp (G ++ F ++ E) (qtyp_qtyp _ (typ_sum T1 T2)))...
      assert (J : wf_typ (G ++ F ++ E) (typ_sum T1 T2))...
      inversion J...
    SCase "inr branch".
      lapply (H2 x); [intros K | auto].
      rewrite <- app_assoc.
      apply H2...
      eassert (M : wf_qtyp (G ++ F ++ E) (qtyp_qtyp _ (typ_sum T1 T2)))...
      assert (J : wf_typ (G ++ F ++ E) (typ_sum T1 T2))...
      inversion J...
  Case "typing_pair".
    apply typing_pair...
Qed.


(* ********************************************************************** *)
(** ** Strengthening (6) *)

Lemma subqual_strengthening_typ : forall x U E F S T,
  subqual (F ++ x ~ bind_typ U ++ E) S T ->
  subqual (F ++ E) S T.
Proof with eauto using wf_typ_strengthening_typ, wf_env_strengthening,
  wf_qtyp_strengthening_typ, wf_qua_strengthening_typ.
  intros x U E F S T SsubT.
  remember (F ++ x ~ bind_typ U ++ E) as E'.
  generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "subqual_trans_qvar".
    apply (subqual_trans_qvar R)...
    analyze_binds H...
Qed.

Lemma sub_strengthening_typ : forall x U E F S T,
  sub (F ++ x ~ bind_typ U ++ E) S T ->
  sub (F ++ E) S T
with subqtype_strengthening_typ : forall x U E F S T,
  subqtype (F ++ x ~ bind_typ U  ++ E) S T ->
  subqtype (F ++ E) S T.
Proof with eauto using wf_typ_strengthening_typ, wf_env_strengthening,
  wf_qtyp_strengthening_typ, wf_qua_strengthening_typ.
------
  intros x U E F S T SsubT.
  remember (F ++ x ~ bind_typ U ++ E) as E'.
  generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "sub_trans_tvar".
    apply (sub_trans_tvar U0)...
    analyze_binds H...
  Case "sub_all".
    pick fresh X and apply sub_all...
    rewrite <- app_assoc.
    apply (subqtype_strengthening_typ x U E (X ~ bind_sub T1 ++ F))...
    apply H...
  Case "sub_qall".
    pick fresh X and apply sub_qall...
    - eapply subqual_strengthening_typ...
    - rewrite <- app_assoc.
      apply (subqtype_strengthening_typ x U E (X ~ bind_qua T1 ++ F))...
      apply H0...
------
  clear subqtype_strengthening_typ.
  intros x U E F S T SsubT.
  remember (F ++ x ~ bind_typ U ++ E) as E'.
  generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "sub_qtyp_qtyp".
    apply sub_qtyp_qtyp...
    apply (subqual_strengthening_typ x U)...
Qed.


(************************************************************************ *)
(** ** Narrowing for typing (7) *)

Lemma typing_narrowing_sub : forall Q E F X P e T,
  sub E P Q ->
  typing (F ++ X ~ bind_sub Q ++ E) e T ->
  typing (F ++ X ~ bind_sub P ++ E) e T.
Proof with eauto 6 using wf_env_narrowing_sub, 
  wf_typ_narrowing_sub, wf_qtyp_narrowing_sub, wf_qua_narrowing_sub,
  sub_narrowing_sub, subqual_narrowing_sub, subqtype_narrowing_sub.
  intros Q E F X P e T PsubQ Typ.
  remember (F ++ X ~ bind_sub Q ++ E) as E'.
  generalize dependent F.
  induction Typ; intros F EQ; subst...
  Case "typing_var".
    analyze_binds H0...
  Case "typing_abs".
    pick fresh y and apply typing_abs...
    rewrite <- app_assoc.
    apply H1...
  Case "typing_tabs".
    pick fresh y and apply typing_tabs...
    rewrite <- app_assoc.
    apply H1...
  Case "typing_qabs".
    pick fresh y and apply typing_qabs...
    rewrite <- app_assoc.
    apply H1...
  Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite <- app_assoc.
    apply H0...
  Case "typing_case".
    pick fresh y and apply typing_case...
    SCase "inl branch".
      rewrite <- app_assoc.
      apply H0...
    SCase "inr branch".
      rewrite <- app_assoc.
      apply H2...
Qed.

Lemma typing_narrowing_qua : forall Q E F X P e T,
  subqual E P Q ->
  typing (F ++ X ~ bind_qua Q ++ E) e T ->
  typing (F ++ X ~ bind_qua P ++ E) e T.
Proof with eauto 6 using wf_env_narrowing_qua, 
  wf_typ_narrowing_qua, wf_qtyp_narrowing_qua, wf_qua_narrowing_qua,
  sub_narrowing_qua, subqual_narrowing_qua, subqtype_narrowing_qua.
  intros Q E F X P e T PsubQ Typ.
  remember (F ++ X ~ bind_qua Q ++ E) as E'.
  generalize dependent F.
  induction Typ; intros F EQ; subst...
  Case "typing_var".
    analyze_binds H0...
  Case "typing_abs".
    pick fresh y and apply typing_abs...
    rewrite <- app_assoc.
    apply H1...
  Case "typing_tabs".
    pick fresh Y and apply typing_tabs...
    rewrite <- app_assoc.
    apply H1...
  Case "typing_qabs".
    pick fresh Y and apply typing_qabs...
    rewrite <- app_assoc.
    apply H1...
  Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite <- app_assoc.
    apply H0...
  Case "typing_case".
    pick fresh y and apply typing_case...
    SCase "inl branch".
      rewrite <- app_assoc.
      apply H0...
    SCase "inr branch".
      rewrite <- app_assoc.
      apply H2...
Qed.

(************************************************************************ *)
(** ** Substitution preserves typing (8) *)

Lemma typing_through_subst_ee : forall U E F x T e u,
  typing (F ++ x ~ bind_typ U ++ E) e T ->
  typing E u U ->
  typing (F ++ E) (subst_ee x u e) T.
(* begin show *)

(** We provide detailed comments for the following proof, mainly to
    point out several useful tactics and proof techniques.

    Starting a proof with "Proof with <some tactic>" allows us to
    specify a default tactic that should be used to solve goals.  To
    invoke this default tactic at the end of a proof step, we signal
    the end of the step with three periods instead of a single one,
    e.g., "apply typing_weakening...". *)

Proof with simpl_env;
           eauto 4 using wf_typ_strengthening_typ,
                         wf_qtyp_strengthening_typ,
                         wf_qua_strengthening_typ,
                         wf_env_strengthening,
                         sub_strengthening_typ,
                         subqtype_strengthening_typ,
                         subqual_strengthening_typ.

  (** The proof proceeds by induction on the given typing derivation
      for e.  We use the [remember] tactic, along with [generalize
      dependent], to ensure that the goal is properly strengthened
      before we use induction. *)

  intros U E F x T e u TypT TypU.
  remember (F ++ x ~ bind_typ U ++ E) as E'.
  generalize dependent F.
  induction TypT; intros F EQ; subst; simpl subst_ee...

  (** The [typing_var] case involves a case analysis on whether the
      variable is the same as the one being substituted for. *)

  Case "typing_var".
    destruct (x0 == x); try subst x0.

    (** In the case where [x0=x], we first observe that hypothesis
        [H0] implies that [T=U], since [x] can only be bound once in
        the environment.  The conclusion then follows from hypothesis
        [TypU] and weakening.  We can use the [analyze_binds_uniq]
        tactic, described in the MetatheoryEnv library, with [H0] to
        obtain the fact that [T=U]. *)

    SCase "x0 = x".
      analyze_binds_uniq H0.
        injection BindsTacVal; intros; subst.

        (** In order to apply [typing_weakening], we need to rewrite
            the environment so that it has the right shape.  (We could
            also prove a corollary of typing_weakening.)  The
            [rewrite_env] tactic, described in the Environment
            library, is one way to perform this rewriting. *)

        rewrite_env (empty ++ F ++ E).
        apply typing_weakening...

    (** In the case where [x0<>x], the result follows by an exhaustive
        case analysis on exactly where [x0] is bound in the
        environment.  We perform this case analysis by using the
        [analyze_binds] tactic, described in the MetatheoryEnv
        library. *)

    SCase "x0 <> x".
      analyze_binds H0.
        eauto using wf_env_strengthening.
        eauto using wf_env_strengthening.

  (** Informally, the [typing_abs] case is a straightforward
      application of the induction hypothesis, which is called [H0]
      here. *)

  Case "typing_abs".

    (** We use the "pick fresh and apply" tactic to apply the rule
        [typing_abs] without having to calculate the appropriate
        finite set of atoms. *)

    pick fresh y and apply typing_abs...

    (** We cannot apply [H0] directly here.  The first problem is that
        the induction hypothesis has [(subst_ee open_ee)], whereas in
        the goal we have [(open_ee subst_ee)].  The lemma
        [subst_ee_open_ee_var] lets us swap the order of these two
        operations. *)

    rewrite subst_ee_open_ee_var...

    (** The second problem is how the concatenations are associated in
        the environments.  In the goal, we currently have

<<       (y ~ bind_typ V ++ F ++ E),
>>
        where concatenation associates to the right.  In order to
        apply the induction hypothesis, we need

<<        ((y ~ bind_typ V ++ F) ++ E).
>>
        We can use the [rewrite_env] tactic to perform this rewriting,
        or we can rewrite directly with an appropriate lemma from the
        MetatheoryEnv library. *)

    rewrite <- app_assoc.

    (** Now we can apply the induction hypothesis. *)

    apply H1...

  (** The remaining cases in this proof are straightforward, given
      everything that we have pointed out above. *)

  Case "typing_tabs".
    pick fresh Y and apply typing_tabs...
    rewrite subst_ee_open_te_var...
    rewrite <- app_assoc.
    apply H1...
  
  Case "typing_qabs".
    pick fresh Y and apply typing_qabs...
    rewrite subst_ee_open_qe_var...
    rewrite <- app_assoc.
    apply H1...

  Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite subst_ee_open_ee_var...
    rewrite <- app_assoc.
    apply H0...

  Case "typing_inl".
    apply typing_inl...
  
  Case "typing_inr".
    apply typing_inr...

  Case "typing_case".
    pick fresh y and apply typing_case...
      rewrite subst_ee_open_ee_var...
        rewrite <- app_assoc.
        apply H0...
      rewrite subst_ee_open_ee_var...
        rewrite <- app_assoc.
        apply H2...

  Case "typing_pair".
    apply typing_pair...
Qed.
(* end show *)


(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

Lemma typing_through_subst_te : forall Q E F Z e T P,
  typing (F ++ Z ~ bind_sub Q ++ E) e T ->
  sub E P Q ->
  typing (map (subst_tb Z P) F ++ E) (subst_te Z P e) (subst_tqt Z P T).
Proof with simpl_env;
           eauto 6 using wf_env_subst_tb,
                         wf_typ_subst_tb,
                         wf_qua_subst_tb,
                         wf_qtyp_subst_tb,
                         sub_through_subst_tt,
                         subqtype_through_subst_tqt,
                         subqual_through_subst_tt.
  intros Q E F Z e T P Typ PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  assert (wf_env G) as WfEnv...
  induction Typ; intros F EQ; subst;
    simpl subst_te in *; simpl subst_tt in *;
    simpl subst_tqt in *...
  Case "typing_var".
    apply typing_var...
      rewrite (map_subst_tb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      analyze_binds H0...
  Case "typing_abs".
    pick fresh y and apply typing_abs...
    rewrite subst_te_open_ee_var...
    rewrite_env (map (subst_tb Z P) (y ~ bind_typ V ++ F) ++ E).
    apply H1...
    unshelve epose proof (H0 y _)...
  Case "typing_tabs".
    pick fresh Y and apply typing_tabs...
    rewrite subst_te_open_te_var...
    rewrite subst_tqt_open_tqt_var...
    rewrite_env (map (subst_tb Z P) (Y ~ bind_sub V ++ F) ++ E).
    apply H1...
    unshelve epose proof (H0 Y _)...
  Case "typing_tapp".
    rewrite subst_tqt_open_tqt...
  Case "typing_qabs".
    pick fresh y and apply typing_qabs...
    rewrite subst_te_open_qe_var...
    rewrite subst_tqt_open_qqt_var...
    rewrite_env (map (subst_tb Z P) (y ~ bind_qua Q0 ++ F) ++ E).
    apply H1...
    unshelve epose proof (H0 y _)...
  Case "typing_qapp".
    rewrite subst_tqt_open_qqt...
  Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite subst_te_open_ee_var...
    rewrite_env (map (subst_tb Z P) (y ~ bind_typ T1 ++ F) ++ E).
    apply H0...
  Case "typing_inl".
    eapply typing_inl...
  Case "typing_inr".
    eapply typing_inr...
  Case "typing_case".
    pick fresh y and apply typing_case...
    SCase "inl branch".
      rewrite subst_te_open_ee_var...
      rewrite_env (map (subst_tb Z P) (y ~ bind_typ T1 ++ F) ++ E).
      apply H0...
      unshelve epose proof (H y _)...
    SCase "inr branch".
      rewrite subst_te_open_ee_var...
      rewrite_env (map (subst_tb Z P) (y ~ bind_typ T2 ++ F) ++ E).
      apply H2...
      unshelve epose proof (H1 y _)...
  Case "typing_pair".
    eapply typing_pair...
Qed.

Lemma typing_through_subst_qe : forall Q E F Z e T P,
  typing (F ++ Z ~ bind_qua Q ++ E) e T ->
  subqual E P Q ->
  typing (map (subst_qb Z P) F ++ E) (subst_qe Z P e) (subst_qqt Z P T).
Proof with simpl_env;
           eauto 6 using wf_env_subst_qb,
                         wf_typ_subst_qb,
                         wf_qua_subst_qb,
                         wf_qtyp_subst_qb,
                         sub_through_subst_qt,
                         subqtype_through_subst_qqt,
                         subqual_through_subst_qq.
  intros Q E F Z e T P Typ PsubQ.
  remember (F ++ Z ~ bind_qua Q ++ E) as G.
  generalize dependent F.
  assert (wf_env G) as WfEnv...
  induction Typ; intros F EQ; subst;
    simpl subst_qe in *; simpl subst_qt in *;
    simpl subst_qqt in *...

  Case "typing_var".
    apply typing_var...
      rewrite (map_subst_qb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      analyze_binds H0...
  Case "typing_abs".
    pick fresh y and apply typing_abs...
    rewrite subst_qe_open_ee_var...
    rewrite_env (map (subst_qb Z P) (y ~ bind_typ V ++ F) ++ E).
    apply H1...
    unshelve epose proof (H0 y _)...
  Case "typing_tabs".
    pick fresh Y and apply typing_tabs...
    rewrite subst_qe_open_te_var...
    rewrite subst_qqt_open_tqt_var...
    rewrite_env (map (subst_qb Z P) (Y ~ bind_sub V ++ F) ++ E).
    apply H1...
    unshelve epose proof (H0 Y _)...
  Case "typing_tapp".
    rewrite subst_qqt_open_tqt...
  Case "typing_qabs".
    pick fresh y and apply typing_qabs...
    rewrite subst_qe_open_qe_var...
    rewrite subst_qqt_open_qqt_var...
    rewrite_env (map (subst_qb Z P) (y ~ bind_qua Q0 ++ F) ++ E).
    apply H1...
    unshelve epose proof (H0 y _)...
  Case "typing_qapp".
    rewrite subst_qqt_open_qqt...
  Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite subst_qe_open_ee_var...
    rewrite_env (map (subst_qb Z P) (y ~ bind_typ T1 ++ F) ++ E).
    apply H0...
  Case "typing_inl".
    eapply typing_inl...
  Case "typing_inr".
    eapply typing_inr...
  Case "typing_case".
    pick fresh y and apply typing_case...
    SCase "inl branch".
      rewrite subst_qe_open_ee_var...
      rewrite_env (map (subst_qb Z P) (y ~ bind_typ T1 ++ F) ++ E).
      apply H0...
      unshelve epose proof (H y _)...
    SCase "inr branch".
      rewrite subst_qe_open_ee_var...
      rewrite_env (map (subst_qb Z P) (y ~ bind_typ T2 ++ F) ++ E).
      apply H2...
      unshelve epose proof (H1 y _)...
  Case "typing_pair".
    eapply typing_pair...
Qed.


(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)


(* ********************************************************************** *)
(** ** Inversion of typing (13) / Canonical Typing Forms *)

Lemma typing_inv_abs : forall E P S1 e1 T,
  typing E (exp_abs P S1 e1) T ->
  forall Q U1 U2, subqtype E T (qtyp_qtyp Q (typ_arrow U1 U2)) ->
     subqtype E U1 S1
  /\ exists S2, exists L, forall x, x `notin` L ->
     typing (x ~ bind_typ S1 ++ E) (open_ee e1 x) S2 /\ subqtype E S2 U2 /\
     subqual E P Q.
Proof with auto.
  intros E P S1 e1 T Typ.
  remember (exp_abs P S1 e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 b1 EQ Q' U1 U2 Sub; inversion EQ; subst.
  Case "typing_abs".
    inversion Sub; subst.
    inversion select (sub _ (typ_arrow _ _) (typ_arrow _ _)); subst.
    split...
    exists T1. exists L...
  Case "typing_sub".
    eapply IHTyp with (Q := Q')...
    auto using (subqtype_transitivity T).
Qed.
Lemma typing_canonical_abs_rec : forall E P V e1 Qt Q T,
  typing E (exp_abs P V e1) Qt ->
  subqtype E Qt (qtyp_qtyp Q T) ->
  exists U1 U2,
     typing E (exp_abs P V e1) (qtyp_qtyp P (typ_arrow U1 U2)) /\
     subqtype E (qtyp_qtyp P (typ_arrow U1 U2)) Qt.
Proof with eauto using subqtype_reflexivity.
  intros * Typ Sub.
  assert (wf_env E)...
  dependent induction Typ...
  Case "typing_abs".
    inversion Sub; subst...
    exists V. exists T1; split...
    econstructor...
  Case "typing_sub".
    destruct (IHTyp P V e1) as [U1 [U2 [Typ' Sub']]]...
      eapply subqtype_transitivity...
    exists U1. exists U2; split...
  eapply subqtype_transitivity...
Qed.
Lemma typing_canonical_abs : forall E P V e1 Q T,
  typing E (exp_abs P V e1) (qtyp_qtyp Q T) ->
  exists U1 U2,
    typing E (exp_abs P V e1) (qtyp_qtyp P (typ_arrow U1 U2)) /\
    subqtype E (qtyp_qtyp P (typ_arrow U1 U2)) (qtyp_qtyp Q T).
Proof with eauto using subqtype_reflexivity.
  intros.
  eapply typing_canonical_abs_rec...
Qed.

Lemma typing_inv_tabs : forall E P S1 e1 T,
  typing E (exp_tabs P S1 e1) T ->
  forall Q U1 U2, subqtype E T (qtyp_qtyp Q (typ_all U1 U2)) ->
     sub E U1 S1
  /\ exists S2, exists L, forall X, X `notin` L ->
     typing (X ~ bind_sub U1 ++ E) (open_te e1 X) (open_tqt S2 X)
     /\ subqtype (X ~ bind_sub U1 ++ E) (open_tqt S2 X) (open_tqt U2 X)
     /\ subqual E P Q.
Proof with simpl_env; auto.
  intros E P S1 e1 T Typ.
  remember (exp_tabs P S1 e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 e0 EQ Q' U1 U2 Sub; inversion EQ; subst.
  Case "typing_tabs".
    inversion Sub; subst.
    inversion select (sub _ (typ_all _ _) (typ_all _ _)); subst.
    split...
    exists T1.
    exists (L0 `union` L).
    intros Y Fr.
    split...
    rewrite_env (empty ++ Y ~ bind_sub U1 ++ E).
    apply (typing_narrowing_sub S1)...
  Case "typing_sub".
    eapply IHTyp with (Q := Q')...
    auto using (subqtype_transitivity T).
Qed.
Lemma typing_inv_tabs_wide : forall E P S1 e1 T,
  typing E (exp_tabs P S1 e1) T ->
  forall Q U1 U2, subqtype E T (qtyp_qtyp Q (typ_all U1 U2)) ->
     sub E U1 S1
  /\ exists S2, exists L, forall X, X `notin` L ->
     typing (X ~ bind_sub S1 ++ E) (open_te e1 X) (open_tqt S2 X)
     /\ subqtype (X ~ bind_sub U1 ++ E) (open_tqt S2 X) (open_tqt U2 X)
     /\ subqual E P Q.
Proof with simpl_env; auto.
  intros E P S1 e1 T Typ.
  remember (exp_tabs P S1 e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 e0 EQ Q' U1 U2 Sub; inversion EQ; subst.
  Case "typing_tabs".
    inversion Sub; subst.
    inversion select (sub _ (typ_all _ _) (typ_all _ _)); subst.
    split...
    exists T1.
    exists (L0 `union` L).
    intros Y Fr.
    split...
  Case "typing_sub".
    eapply IHTyp with (Q := Q')...
    auto using (subqtype_transitivity T).
Qed.
Lemma typing_canonical_tabs_rec : forall E P S1 e1 Qt Q T,
  typing E (exp_tabs P S1 e1) Qt ->
  subqtype E Qt (qtyp_qtyp Q T) ->
  exists U1 U2,
     typing E (exp_tabs P S1 e1) (qtyp_qtyp P (typ_all U1 U2)) /\
     subqtype E (qtyp_qtyp P (typ_all U1 U2)) Qt.
Proof with eauto using subqtype_reflexivity.
  intros * Typ Sub.
  assert (wf_env E)...
  dependent induction Typ...
  Case "typing_abs".
    inversion Sub; subst...
    exists S1. exists T1; split...
    econstructor...
  Case "typing_sub".
    destruct (IHTyp P S1 e1) as [U1 [U2 [Typ' Sub']]]...
      eapply subqtype_transitivity...
    exists U1. exists U2; split...
  eapply subqtype_transitivity...
Qed.
Lemma typing_canonical_tabs : forall E P S1 e1 Q T,
  typing E (exp_tabs P S1 e1) (qtyp_qtyp Q T) ->
  exists U1 U2,
    typing E (exp_tabs P S1 e1) (qtyp_qtyp P (typ_all U1 U2)) /\
    subqtype E (qtyp_qtyp P (typ_all U1 U2)) (qtyp_qtyp Q T).
Proof with eauto using subqtype_reflexivity.
  intros.
  eapply typing_canonical_tabs_rec...
Qed.

Lemma typing_inv_qabs : forall E P S1 e1 T,
  typing E (exp_qabs P S1 e1) T ->
  forall Q U1 U2, subqtype E T (qtyp_qtyp Q (typ_qall U1 U2)) ->
     subqual E U1 S1
  /\ exists S2, exists L, forall X, X `notin` L ->
     typing (X ~ bind_qua U1 ++ E) (open_qe e1 X) (open_qqt S2 X)
     /\ subqtype (X ~ bind_qua U1 ++ E) (open_qqt S2 X) (open_qqt U2 X)
     /\ subqual E P Q.
Proof with simpl_env; auto.
  intros E P S1 e1 T Typ.
  remember (exp_qabs P S1 e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 e0 EQ Q' U1 U2 Sub; inversion EQ; subst.
  Case "typing_qabs".
    inversion Sub; subst.
    inversion select (sub _ (typ_qall _ _) (typ_qall _ _)); subst.
    split...
    exists T1.
    exists (L0 `union` L).
    intros Y Fr.
    split...
    rewrite_env (empty ++ Y ~ bind_qua U1 ++ E).
    apply (typing_narrowing_qua S1)...
  Case "typing_sub".
    eapply IHTyp with (Q := Q')...
    auto using (subqtype_transitivity T).
Qed.
Lemma typing_inv_qabs_wide : forall E P S1 e1 T,
  typing E (exp_qabs P S1 e1) T ->
  forall Q U1 U2, subqtype E T (qtyp_qtyp Q (typ_qall U1 U2)) ->
     subqual E U1 S1
  /\ exists S2, exists L, forall X, X `notin` L ->
     typing (X ~ bind_qua S1 ++ E) (open_qe e1 X) (open_qqt S2 X)
     /\ subqtype (X ~ bind_qua U1 ++ E) (open_qqt S2 X) (open_qqt U2 X)
     /\ subqual E P Q.
Proof with simpl_env; auto.
  intros E P S1 e1 T Typ.
  remember (exp_qabs P S1 e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 e0 EQ Q' U1 U2 Sub; inversion EQ; subst.
  Case "typing_qabs".
    inversion Sub; subst.
    inversion select (sub _ (typ_qall _ _) (typ_qall _ _)); subst.
    split...
    exists T1.
    exists (L0 `union` L).
    intros Y Fr.
    split...
  Case "typing_sub".
    eapply IHTyp with (Q := Q')...
    auto using (subqtype_transitivity T).
Qed.
Lemma typing_canonical_qabs_rec : forall E P S1 e1 Qt Q T,
  typing E (exp_qabs P S1 e1) Qt ->
  subqtype E Qt (qtyp_qtyp Q T) ->
  exists U1 U2,
     typing E (exp_qabs P S1 e1) (qtyp_qtyp P (typ_qall U1 U2)) /\
     subqtype E (qtyp_qtyp P (typ_qall U1 U2)) Qt.
Proof with eauto using subqtype_reflexivity.
  intros * Typ Sub.
  assert (wf_env E)...
  dependent induction Typ...
  Case "typing_abs".
    inversion Sub; subst...
    exists S1. exists T1; split...
    econstructor...
  Case "typing_sub".
    destruct (IHTyp P S1 e1) as [U1 [U2 [Typ' Sub']]]...
      eapply subqtype_transitivity...
    exists U1. exists U2; split...
  eapply subqtype_transitivity...
Qed.
Lemma typing_canonical_qabs : forall E P S1 e1 Q T,
  typing E (exp_qabs P S1 e1) (qtyp_qtyp Q T) ->
  exists U1 U2,
    typing E (exp_qabs P S1 e1) (qtyp_qtyp P (typ_qall U1 U2)) /\
    subqtype E (qtyp_qtyp P (typ_qall U1 U2)) (qtyp_qtyp Q T).
Proof with eauto using subqtype_reflexivity.
  intros.
  eapply typing_canonical_qabs_rec...
Qed.

Lemma typing_inv_inl : forall E P e1 T,
  typing E (exp_inl P e1) T ->
  forall Q U1 U2, subqtype E T (qtyp_qtyp Q (typ_sum U1 U2)) ->
  exists S1, typing E e1 S1 /\ subqtype E S1 U1 /\ subqual E P Q.
Proof with eauto.
  intros E P e1 T Typ.
  remember (exp_inl P e1) as e. generalize dependent e1.
  induction Typ; intros e' EQ Q' U1 U2 Sub; inversion EQ; subst.
  Case "typing_sub".
    eauto using (subqtype_transitivity T).
  Case "typing_inl".
    inversion Sub; subst...
    inversion select (sub _ (typ_sum _ _) (typ_sum _ _))...
Qed.
Lemma typing_canonical_inl_rec : forall E P e1 Qt Q T,
  typing E (exp_inl P e1) Qt ->
  subqtype E Qt (qtyp_qtyp Q T) ->
  exists U1 U2,
     typing E (exp_inl P e1) (qtyp_qtyp P (typ_sum U1 U2)) /\
     subqtype E (qtyp_qtyp P (typ_sum U1 U2)) Qt.
Proof with eauto using subqtype_reflexivity.
  intros * Typ Sub.
  assert (wf_env E)...
  dependent induction Typ...
  Case "typing_sub".
    destruct (IHTyp P e1) as [U1 [U2 [Typ' Sub']]]...
      eapply subqtype_transitivity...
    exists U1. exists U2; split...
    eapply subqtype_transitivity...
  Case "typing_inl".
    inversion Sub; subst...
    exists T1. exists T2; split...
Qed.
Lemma typing_canonical_inl : forall E P e1 Q T,
  typing E (exp_inl P e1) (qtyp_qtyp Q T) ->
  exists U1 U2,
    typing E (exp_inl P e1) (qtyp_qtyp P (typ_sum U1 U2)) /\
    subqtype E (qtyp_qtyp P (typ_sum U1 U2)) (qtyp_qtyp Q T).
Proof with eauto using subqtype_reflexivity.
  intros.
  eapply typing_canonical_inl_rec...
Qed.

Lemma typing_inv_inr : forall E P e1 T,
  typing E (exp_inr P e1) T ->
  forall Q U1 U2, subqtype E T (qtyp_qtyp Q (typ_sum U1 U2)) ->
  exists S1, typing E e1 S1 /\ subqtype E S1 U2 /\ subqual E P Q.
Proof with eauto.
  intros E P e1 T Typ.
  remember (exp_inr P e1) as e. generalize dependent e1.
  induction Typ; intros e' EQ Q' U1 U2 Sub; inversion EQ; subst.
  Case "typing_sub".
    eauto using (subqtype_transitivity T).
  Case "typing_inr".
    inversion Sub; subst...
    inversion select (sub _ (typ_sum _ _) (typ_sum _ _))...
Qed.
Lemma typing_canonical_inr_rec : forall E P e1 Qt Q T,
  typing E (exp_inr P e1) Qt ->
  subqtype E Qt (qtyp_qtyp Q T) ->
  exists U1 U2,
     typing E (exp_inr P e1) (qtyp_qtyp P (typ_sum U1 U2)) /\
     subqtype E (qtyp_qtyp P (typ_sum U1 U2)) Qt.
Proof with eauto using subqtype_reflexivity.
  intros * Typ Sub.
  assert (wf_env E)...
  dependent induction Typ...
  Case "typing_sub".
    destruct (IHTyp P e1) as [U1 [U2 [Typ' Sub']]]...
      eapply subqtype_transitivity...
    exists U1. exists U2; split...
    eapply subqtype_transitivity...
  Case "typing_inr".
    inversion Sub; subst...
    exists T1. exists T2; split...
Qed.
Lemma typing_canonical_inr : forall E P e1 Q T,
  typing E (exp_inr P e1) (qtyp_qtyp Q T) ->
  exists U1 U2,
    typing E (exp_inr P e1) (qtyp_qtyp P (typ_sum U1 U2)) /\
    subqtype E (qtyp_qtyp P (typ_sum U1 U2)) (qtyp_qtyp Q T).
Proof with eauto using subqtype_reflexivity.
  intros.
  eapply typing_canonical_inr_rec...
Qed.


Lemma typing_inv_pair : forall E P e1 e2 T,
  typing E (exp_pair P e1 e2) T ->
  forall Q U1 U2, subqtype E T (qtyp_qtyp Q (typ_pair U1 U2)) ->
  exists S1 S2, typing E e1 S1 /\ subqtype E S1 U1 /\
    typing E e2 S2 /\ subqtype E S2 U2 /\ subqual E P Q.
Proof with eauto.
  intros E P e1 e2 T Typ.
  remember (exp_pair P e1 e2) as e. generalize dependent e1. generalize dependent e2.
  induction Typ; intros e2' e1' EQ Q' U1 U2 Sub; inversion EQ; subst.
  Case "typing_sub".
    eauto using (subqtype_transitivity T).
  Case "typing_inr".
    inversion Sub; subst...
    inversion select (sub _ (typ_pair _ _) (typ_pair _ _)); subst...
    exists T1. exists T2...
Qed.
Lemma typing_canonical_pair_rec : forall E P e1 e2 Qt Q T,
  typing E (exp_pair P e1 e2) Qt ->
  subqtype E Qt (qtyp_qtyp Q T) ->
  exists U1 U2,
     typing E (exp_pair P e1 e2) (qtyp_qtyp P (typ_pair U1 U2)) /\
     subqtype E (qtyp_qtyp P (typ_pair U1 U2)) Qt.
Proof with eauto using subqtype_reflexivity.
  intros * Typ Sub.
  assert (wf_env E)...
  dependent induction Typ...
  Case "typing_sub".
    destruct (IHTyp P e1 e2) as [U1 [U2 [Typ' Sub']]]...
      eapply subqtype_transitivity...
    exists U1. exists U2; split...
    eapply subqtype_transitivity...
  Case "typing_inl".
    inversion Sub; subst...
    exists T1. exists T2; split...
Qed.
Lemma typing_canonical_pair : forall E P e1 e2 Q T,
  typing E (exp_pair P e1 e2) (qtyp_qtyp Q T) ->
  exists U1 U2,
    typing E (exp_pair P e1 e2) (qtyp_qtyp P (typ_pair U1 U2)) /\
    subqtype E (qtyp_qtyp P (typ_pair U1 U2)) (qtyp_qtyp Q T).
Proof with eauto using subqtype_reflexivity.
  intros.
  eapply typing_canonical_pair_rec...
Qed.


(* ********************************************************************** *)
(** ** Qualifiers and Concrete Qualifiers (14.5) *)

Lemma concrete_sub_qualifier : forall E Q s,
  concretize Q = Some s ->
  wf_env E ->
  wf_qua E Q ->
  subqual E (abstractize s) Q.
Proof with eauto.
  intros * Eq WfE WfQ.
  induction WfQ; simpl in *;
    try inversion select (Some _ = Some _); subst; simpl in *...
  - exfalso. inversion Eq.
  - destruct (concretize Q1) eqn:HQ1;
    destruct (concretize Q2) eqn:HQ2;
    simpl in *;
    try destruct c eqn:Hs0; subst; simpl in *;
    try destruct c0 eqn:Hs1; subst; simpl in *;
    inversion Eq; subst; simpl in *...
  - destruct (concretize Q1) eqn:HQ1;
    destruct (concretize Q2) eqn:HQ2;
    simpl in *;
    try destruct c eqn:Hs0; subst; simpl in *;
    try destruct c0 eqn:Hs1; subst; simpl in *;
    inversion Eq; subst; simpl in *...
Qed.

Lemma qualifier_sub_concrete : forall E Q s,
  concretize Q = Some s ->
  wf_env E ->
  wf_qua E Q ->
  subqual E Q (abstractize s).
Proof with eauto.
  intros * Eq WfE WfQ.
  induction WfQ; simpl in *;
    try inversion select (Some _ = Some _); subst; simpl in *...
  - exfalso. inversion Eq.
  - destruct (concretize Q1) eqn:HQ1;
    destruct (concretize Q2) eqn:HQ2;
    simpl in *;
    try destruct c eqn:Hs0; subst; simpl in *;
    try destruct c0 eqn:Hs1; subst; simpl in *;
    inversion Eq; subst; simpl in *...
  - destruct (concretize Q1) eqn:HQ1;
    destruct (concretize Q2) eqn:HQ2;
    simpl in *;
    try destruct c eqn:Hs0; subst; simpl in *;
    try destruct c0 eqn:Hs1; subst; simpl in *;
    inversion Eq; subst; simpl in *...
Qed.

Lemma subqual_compatible : forall s t,
  subqual empty (abstractize s) (abstractize t) ->
  s ~> t.
Proof with eauto.
  intros.
  destruct s; destruct t...
  simpl in *. dependent induction H...
Qed.

Lemma subqual_implies_compatible : forall P Q c d,
  subqual empty P Q ->
  concretize P = Some c ->
  concretize Q = Some d ->
  cqua_compatible c d.
Proof with eauto.
  intros * Sub EqP EqQ.
  eapply subqual_compatible...
  eapply subqual_transitivity with (Q := P).
  eapply concrete_sub_qualifier...
  eapply subqual_transitivity with (Q := Q)...
  eapply qualifier_sub_concrete...
Qed.

(* ********************************************************************** *)
(** ** Preservation (20) *)

Lemma preservation : forall E e e' T,
  typing E e T ->
  red e e' ->
  typing E e' T.
Proof with simpl_env; eauto.
  intros E e e' T Typ. generalize dependent e'.
  induction Typ; intros e' Red; try solve [ inversion Red; subst; eauto ].
  Case "typing_app".
    inversion Red; subst...
    SCase "red_abs".
      destruct (typing_inv_abs _ _ _ _ _ Typ1 Q T1 T2) as [P1 [S2 [L P2]]].
        apply subqtype_reflexivity...
      pick fresh x.
      destruct (P2 x) as [? [? ?]]...
      rewrite (subst_ee_intro x)...
      rewrite_env (empty ++ E).
      apply (typing_through_subst_ee T).
        apply (typing_sub S2)...
          rewrite_env (empty ++ x ~ bind_typ T ++ E).
          apply subqtype_weakening...
        eauto.
  Case "typing_tapp".
    inversion Red; subst...
    SCase "red_tabs".
      destruct (typing_inv_tabs _ _ _ _ _ Typ Q T1 T2) as [P1 [S2 [L P2]]].
        apply subqtype_reflexivity...
      pick fresh X.
      destruct (P2 X) as [? [? ?]]...
      rewrite (subst_te_intro X)...
      rewrite (subst_tqt_intro X)...
      rewrite_env (map (subst_tb X T) empty ++ E).
      apply (typing_through_subst_te T1)...
  Case "typing_qapp".
    inversion Red; subst...
    SCase "red_qabs".
      destruct (typing_inv_qabs _ _ _ _ _ Typ R Q1 T) as [P1 [S2 [L P2]]].
        apply subqtype_reflexivity...
      pick fresh X.
      destruct (P2 X) as [? [? ?]]...
      rewrite (subst_qe_intro X)...
      rewrite (subst_qqt_intro X)...
      rewrite_env (map (subst_qb X Q) empty ++ E).
      apply (typing_through_subst_qe Q1)...
  Case "typing_let".
    inversion Red; subst.
      SCase "red_let_1".
        eapply typing_let; eauto.
      SCase "red_let".
        pick fresh x.
        rewrite (subst_ee_intro x)...
        rewrite_env (empty ++ E).
        apply (typing_through_subst_ee T1)...
  Case "typing_case".
    inversion Red; subst.
    SCase "red_case_1".
      eapply typing_case; eauto.
    SCase "red_case_inl".
      destruct (typing_inv_inl _ _ _ _ Typ Q T1 T2) as [S1 [J2 [J3 J4]]].
        apply subqtype_reflexivity...
      pick fresh x.
      rewrite (subst_ee_intro x)...
      rewrite_env (empty ++ E).
      apply (typing_through_subst_ee T1)...
    SCase "red_case_inr".
      destruct (typing_inv_inr _ _ _ _ Typ Q T1 T2) as [S1 [J2 [J3 J4]]].
        apply subqtype_reflexivity...
      pick fresh x.
      rewrite (subst_ee_intro x)...
      rewrite_env (empty ++ E).
      apply (typing_through_subst_ee T2)...
  Case "typing_first".
    inversion Red; subst.
    SCase "red_pair_first_1".
      eapply typing_first...
    SCase "red_pair_first_2".
      destruct (typing_inv_pair _ _ _ _ _ Typ Q T1 T2)
        as [S1 [S2 [Typ1 [Sub1 [Typ2 [Sub2 SubQ]]]]]]...
        apply subqtype_reflexivity...
  Case "typing_second".
    inversion Red; subst.
    SCase "red_pair_second_1".
      eapply typing_second...
    SCase "red_pair_second_2".
      destruct (typing_inv_pair _ _ _ _ _ Typ Q T1 T2)
        as [S1 [S2 [Typ1 [Sub1 [Typ2 [Sub2 SubQ]]]]]]...
        apply subqtype_reflexivity...
  Case "typing_upqual".
    inversion Red; subst...
    SCase "red_upqual_abs".
      unshelve epose proof (typing_canonical_abs _ _ _ _ _ _ Typ)
        as [U1 [U2 [TypU1U2 SubU1U2]]].
      inversion SubU1U2; subst...
      eapply typing_sub with (S := qtyp_qtyp P (typ_arrow U1 U2))...
      destruct (typing_inv_abs _ _ _ _ _ TypU1U2 Q0 U1 U2) as [P1 [S2 [L P2]]]...
        eapply subqtype_reflexivity...
      eapply typing_sub with (S := qtyp_qtyp P (typ_arrow V S2))...
      eapply typing_abs with (L := L)...
      eapply P2...
      econstructor; eauto using subqual_reflexivity...
      econstructor... pick fresh x; eapply (P2 x)...
      econstructor; eauto using subqual_reflexivity...
    SCase "red_upqual_tabs".
      unshelve epose proof (typing_canonical_tabs _ _ _ _ _ _ Typ)
        as [U1 [U2 [TypU1U2 SubU1U2]]].
      inversion SubU1U2; subst...
      eapply typing_sub with (S := qtyp_qtyp P (typ_all U1 U2))...
      destruct (typing_inv_tabs_wide _ _ _ _ _ TypU1U2 Q0 U1 U2) as [P1 [S2 [L P2]]]...
        eapply subqtype_reflexivity...
      eapply typing_sub with (S := qtyp_qtyp P (typ_all V S2))...
      eapply typing_tabs with (L := L)...
      eapply P2...
      econstructor; eauto using subqual_reflexivity...
      econstructor... pick fresh X. eapply P2...
      econstructor; eauto using subqual_reflexivity...
    SCase "red_upqual_qabs".
      unshelve epose proof (typing_canonical_qabs _ _ _ _ _ _ Typ)
        as [U1 [U2 [TypU1U2 SubU1U2]]].
      inversion SubU1U2; subst...
      eapply typing_sub with (S := qtyp_qtyp P (typ_qall U1 U2))...
      destruct (typing_inv_qabs_wide _ _ _ _ _ TypU1U2 Q0 U1 U2) as [P1 [S2 [L P2]]]...
        eapply subqtype_reflexivity...
      eapply typing_sub with (S := qtyp_qtyp P (typ_qall V S2))...
      eapply typing_qabs with (L := L)...
      eapply P2...
      econstructor; eauto using subqual_reflexivity...
      econstructor... pick fresh X. eapply P2...
      econstructor; eauto using subqual_reflexivity...
    SCase "red_upqual_inl".
      unshelve epose proof (typing_canonical_inl _ _ _ _ _  Typ)
        as [U1 [U2 [TypU1U2 SubU1U2]]].
      assert (wf_qtyp E U2)...
        apply subqtype_regular in SubU1U2 as [? [WfU1U2 ?]]...
        inversion WfU1U2; subst...
        inversion select (wf_typ _ (typ_sum _ _))...
      inversion SubU1U2; subst...
      eapply typing_sub with (S := qtyp_qtyp P (typ_sum U1 U2))...
      destruct (typing_inv_inl _ _ _ _ TypU1U2 Q0 U1 U2) as [P1 [S2 [L P2]]]...
        eapply subqtype_reflexivity...
      econstructor... eapply subqual_reflexivity...
    SCase "red_upqual_inr".
      unshelve epose proof (typing_canonical_inr _ _ _ _ _  Typ)
        as [U1 [U2 [TypU1U2 SubU1U2]]].
      assert (wf_qtyp E U1)...
        apply subqtype_regular in SubU1U2 as [? [WfU1U2 ?]]...
        inversion WfU1U2; subst...
        inversion select (wf_typ _ (typ_sum _ _))...
      inversion SubU1U2; subst...
      eapply typing_sub with (S := qtyp_qtyp P (typ_sum U1 U2))...
      destruct (typing_inv_inr _ _ _ _ TypU1U2 Q0 U1 U2) as [P1 [S2 [L P2]]]...
        eapply subqtype_reflexivity...
      econstructor... eapply subqual_reflexivity...
    SCase "red_upqual_pair".
      unshelve epose proof (typing_canonical_pair _ _ _ _ _ _ Typ)
        as [U1 [U2 [TypU1U2 SubU1U2]]].
      inversion SubU1U2; subst...
      eapply typing_sub with (S := qtyp_qtyp P (typ_pair U1 U2))...
      destruct (typing_inv_pair _ _ _ _ _ TypU1U2 Q0 U1 U2) as [P1 [P2 [TypP1 [SubP1 [TypP2 [SubP2 SubQual]]]]]]...
        eapply subqtype_reflexivity...
      econstructor... eapply subqual_reflexivity...
Qed.

(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)


(* ********************************************************************** *)
(** ** Canonical forms (14) *)

Lemma canonical_form_abs : forall e Q U1 U2,
  value e ->
  typing empty e (qtyp_qtyp Q (typ_arrow U1 U2)) ->
  exists P, exists V, exists e1, e = exp_abs P V e1.
Proof.
  intros e Q U1 U2 Val Typ.
  remember empty as E.
  remember (qtyp_qtyp Q (typ_arrow U1 U2)) as T.
  revert Q U1 U2 HeqT HeqE.
  induction Typ; intros Q' U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion select (sub _ _ _); subst...
    inversion H0. 
    eapply IHTyp with (Q := Q1) (U1 := S1) (U2 := S2); auto.
Qed.

Lemma canonical_form_tabs : forall e Q U1 U2,
  value e ->
  typing empty e (qtyp_qtyp Q (typ_all U1 U2)) ->
  exists P, exists V, exists e1, e = exp_tabs P V e1.
Proof.
  intros e Q U1 U2 Val Typ.
  remember empty as E.
  remember (qtyp_qtyp Q (typ_all U1 U2)) as T.
  revert Q U1 U2 HeqT HeqT.
  induction Typ; intros Q' U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion select (sub _ _ _); subst...
    inversion H0. 
    eapply IHTyp with (Q := Q1) (U1 := S1) (U2 := S2); auto.
Qed.

Lemma canonical_form_qabs : forall e Q U1 U2,
  value e ->
  typing empty e (qtyp_qtyp Q (typ_qall U1 U2)) ->
  exists P, exists V, exists e1, e = exp_qabs P V e1.
Proof.
  intros e Q U1 U2 Val Typ.
  remember empty as E.
  remember (qtyp_qtyp Q (typ_qall U1 U2)) as T.
  revert Q U1 U2 HeqT HeqT.
  induction Typ; intros Q' U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion select (sub _ _ _); subst...
    inversion H0. 
    eapply IHTyp with (Q := Q1) (U1 := S1) (U2 := S2); auto.
Qed.

Lemma canonical_form_sum : forall e Q T1 T2,
  value e ->
  typing empty e (qtyp_qtyp Q (typ_sum T1 T2)) ->
  exists P e1, e = exp_inl P e1 \/ e = exp_inr P e1.
Proof.
  intros e Q T1 T2 Val Typ.
  remember empty as E.
  remember (qtyp_qtyp Q (typ_sum T1 T2)) as T.
  revert Q T1 T2 HeqE HeqT.
  induction Typ; intros Q' U1 U2 EQE EQT; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion select (sub _ _ _); subst...
    inversion H0. 
    eapply IHTyp; auto.
Qed.

Lemma canonical_form_pair : forall e Q T1 T2,
  value e ->
  typing empty e (qtyp_qtyp Q (typ_pair T1 T2)) ->
  exists P e1 e2, e = exp_pair P e1 e2.
Proof.
  intros e Q T1 T2 Val Typ.
  remember empty as E.
  remember (qtyp_qtyp Q (typ_pair T1 T2)) as T.
  revert Q T1 T2 HeqE HeqT.
  induction Typ; intros Q' U1 U2 EQE EQT; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion select (sub _ _ _); subst...
    inversion H0. 
    eapply IHTyp; auto.
Qed.

Lemma canonical_form_qual : forall Q,
  wf_qua empty Q ->
  exists s, concretize Q = Some s.
Proof with eauto.
  intros.
  dependent induction H; simpl...
  - analyze_binds H.
  - destruct IHwf_qua1 as [s1 Eq1]...
    destruct IHwf_qua2 as [s2 Eq2]...
    rewrite Eq1; rewrite Eq2; destruct s1; destruct s2...
  - destruct IHwf_qua1 as [s1 Eq1]...
    destruct IHwf_qua2 as [s2 Eq2]...
    rewrite Eq1; rewrite Eq2; destruct s1; destruct s2...
Qed.


(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma progress : forall e T,
  typing empty e T ->
  value e \/ exists e', red e e'.
Proof with eauto.
  intros e T Typ.
  remember empty as E. generalize dependent HeqE.
  assert (Typ' : typing E e T)...
  induction Typ; intros EQ; subst...
  Case "typing_var".
    inversion H0.
  Case "typing_app".
    right.
    destruct IHTyp1 as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct IHTyp2 as [Val2 | [e2' Rede2']]...
      SSCase "Val2".
        destruct (canonical_form_abs _ _ _ _ Val1 Typ1) as [P [S [e3 EQ]]].
        subst.
        exists (open_ee e3 e2)...
  Case "typing_tapp".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct (canonical_form_tabs _ _ _ _ Val1 Typ) as [P [S [e3 EQ]]].
      subst.
      exists (open_te e3 T)...
  Case "typing_tapp".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct (canonical_form_qabs _ _ _ _ Val1 Typ) as [P [S [e3 EQ]]].
      subst.
      exists (open_qe e3 Q)...
  Case "typing_let".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
  Case "typing_inl".
    destruct (typing_inv_inl _ _ _ _ Typ' P T1 T2 ) as [P' [S1 [J2 J3]]].
    apply subqtype_reflexivity...
    destruct IHTyp as [J1 | [e' J1]]...
  Case "typing_inr".
    destruct (typing_inv_inr _ _ _ _ Typ' P T1 T2) as [P' [S1 [J2 J3]]].
    apply subqtype_reflexivity...
    destruct IHTyp as [J1 | [e' J1]]...
  Case "typing_case".
    right.
    destruct IHTyp as [Val1 | [e' Rede']]...
    SCase "Val1".
      destruct (canonical_form_sum _ _ _ _ Val1 Typ) as [P [e4 [J1 | J1]]].
      SSCase "Left J1".
        subst.
        exists (open_ee e2 e4).
        inversion Val1; subst.
        assert (expr (exp_case (exp_inl P e4) e2 e3)) by auto.
        inversion H3...
      SSCase "Right J1".
        subst.
        exists (open_ee e3 e4)...
        inversion Val1; subst.
        assert (expr (exp_case (exp_inr P e4) e2 e3)) by auto.
        inversion H3...
  Case "typing_pair".
    destruct IHTyp1 as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct IHTyp2 as [Val2 | [e2' Rede2']]...
  Case "typing_first".
    right.
    destruct IHTyp as [Val1 | [e' Rede']]...
    SCase "Val1".
      destruct (canonical_form_pair _ _ _ _ Val1 Typ) as [P [e3 [e4 EQ]]]; subst.
      inversion Val1...
  Case "typing_second".
    right.
    destruct IHTyp as [Val1 | [e' Rede']]...
    SCase "Val1".
      destruct (canonical_form_pair _ _ _ _ Val1 Typ) as [P [e3 [e4 EQ]]]; subst.
      inversion Val1...
  Case "typing_upqual".
    right...
    destruct IHTyp as [Val1 | [e' Rede']]...
    unshelve epose proof (canonical_form_qual Q _) as [c EqC]...
    unshelve epose proof (canonical_form_qual P _) as [d EqD]...
    SCase "Val1".
      unshelve epose proof (subqual_regular _ _ _ H)
        as [? [? ?]]...
      inversion Val1; subst...
      SSCase "red_exp_abs".
        inversion select (expr (exp_abs _ _ _)); subst...
        exists (exp_abs P T0 e1)...
        unshelve epose proof (typing_canonical_abs _ _ _ _ Q T _)
          as [U1 [U2 [TypU1U2' SubQ']]]...
        inversion SubQ'.
        unshelve epose proof (subqual_transitivity Q empty P0 P _ _) as SubT...
        unshelve epose proof (subqual_regular _ _ _ SubT) as [? [? ?]]...
        unshelve epose proof (canonical_form_qual P0 _) as [b EqB]...
        econstructor...
        eapply subqual_implies_compatible...
      SSCase "red_exp_tabs".
        inversion select (expr (exp_tabs _ _ _)); subst...
        exists (exp_tabs P T0 e1)...
        unshelve epose proof (typing_canonical_tabs _ _ _ _ Q T _)
          as [U1 [U2 [TypU1U2' SubQ']]]...
        inversion SubQ'.
        unshelve epose proof (subqual_transitivity Q empty P0 P _ _) as SubT...
        unshelve epose proof (subqual_regular _ _ _ SubT) as [? [? ?]]...
        unshelve epose proof (canonical_form_qual P0 _) as [b EqB]...
        econstructor...
        eapply subqual_implies_compatible...
      SSCase "red_exp_qabs".
        inversion select (expr (exp_qabs _ _ _)); subst...
        exists (exp_qabs P Q0 e1)...
        unshelve epose proof (typing_canonical_qabs _ _ _ _ Q T Typ)
          as [U1 [U2 [TypU1U2' SubQ']]]...
        inversion SubQ'.
        unshelve epose proof (subqual_transitivity Q empty P0 P _ _) as SubT...
        unshelve epose proof (subqual_regular _ _ _ SubT) as [? [? ?]]...
        unshelve epose proof (canonical_form_qual P0 _) as [b EqB]...
        econstructor...
        eapply subqual_implies_compatible...
      SSCase "red_exp_inl".
        exists (exp_inl P e1)...
        unshelve epose proof (typing_canonical_inl _ _ _ Q T _)
          as [U1 [U2 [TypU1U2' SubQ']]]...
        inversion SubQ'.
        unshelve epose proof (subqual_transitivity Q empty P0 P _ _) as SubT...
        unshelve epose proof (subqual_regular _ _ _ SubT) as [? [? ?]]...
        unshelve epose proof (canonical_form_qual P0 _) as [b EqB]...
        econstructor...
        eapply subqual_implies_compatible...
      SSCase "red_exp_inr".
        exists (exp_inr P e1)...
        unshelve epose proof (typing_canonical_inr _ _ _ Q T _)
          as [U1 [U2 [TypU1U2' SubQ']]]...
        inversion SubQ'.
        unshelve epose proof (subqual_transitivity Q empty P0 P _ _) as SubT...
        unshelve epose proof (subqual_regular _ _ _ SubT) as [? [? ?]]...
        unshelve epose proof (canonical_form_qual P0 _) as [b EqB]...
        econstructor...
        eapply subqual_implies_compatible...
      SSCase "red_exp_pair".
        exists (exp_pair P e1 e2)...
        unshelve epose proof (typing_canonical_pair _ _ _ _ Q T Typ)
          as [U1 [U2 [TypU1U2' SubQ']]]...
        inversion SubQ'.
        unshelve epose proof (subqual_transitivity Q empty P0 P _ _) as SubT...
        unshelve epose proof (subqual_regular _ _ _ SubT) as [? [? ?]]...
        unshelve epose proof (canonical_form_qual P0 _) as [b EqB]...
        econstructor...
        eapply subqual_implies_compatible...                 
  Case "typing_check".
    right...
    destruct IHTyp as [Val1 | [e' Rede']]...  
    unshelve epose proof (canonical_form_qual Q _) as [c EqC]...
    unshelve epose proof (canonical_form_qual P _) as [d EqD]...
    SCase "Val1".
      unshelve epose proof (subqual_regular _ _ _ H)
        as [? [? ?]]...
      inversion Val1; subst...
      SSCase "red_exp_abs".
        inversion select (expr (exp_abs _ _ _)); subst...
        exists (exp_abs P0 T0 e1)...
        unshelve epose proof (typing_canonical_abs _ _ _ _ Q T _)
          as [U1 [U2 [TypU1U2' SubQ']]]...
        inversion SubQ'.
        unshelve epose proof (subqual_transitivity Q empty P0 P _ _) as SubT...
        unshelve epose proof (subqual_regular _ _ _ SubT) as [? [? ?]]...
        unshelve epose proof (canonical_form_qual P0 _) as [b EqB]...
        econstructor...
        eapply subqual_implies_compatible...
      SSCase "red_exp_tabs".
        inversion select (expr (exp_tabs _ _ _)); subst...
        exists (exp_tabs P0 T0 e1)...
        unshelve epose proof (typing_canonical_tabs _ _ _ _ Q T _)
          as [U1 [U2 [TypU1U2' SubQ']]]...
        inversion SubQ'.
        unshelve epose proof (subqual_transitivity Q empty P0 P _ _) as SubT...
        unshelve epose proof (subqual_regular _ _ _ SubT) as [? [? ?]]...
        unshelve epose proof (canonical_form_qual P0 _) as [b EqB]...
        econstructor...
        eapply subqual_implies_compatible...
      SSCase "red_exp_qabs".
        inversion select (expr (exp_qabs _ _ _)); subst...
        exists (exp_qabs P0 Q0 e1)...
        unshelve epose proof (typing_canonical_qabs _ _ _ _ Q T Typ)
          as [U1 [U2 [TypU1U2' SubQ']]]...
        inversion SubQ'.
        unshelve epose proof (subqual_transitivity Q empty P0 P _ _) as SubT...
        unshelve epose proof (subqual_regular _ _ _ SubT) as [? [? ?]]...
        unshelve epose proof (canonical_form_qual P0 _) as [b EqB]...
        econstructor...
        eapply subqual_implies_compatible...
      SSCase "red_exp_inl".
        exists (exp_inl P0 e1)...
        unshelve epose proof (typing_canonical_inl _ _ _ Q T _)
          as [U1 [U2 [TypU1U2' SubQ']]]...
        inversion SubQ'.
        unshelve epose proof (subqual_transitivity Q empty P0 P _ _) as SubT...
        unshelve epose proof (subqual_regular _ _ _ SubT) as [? [? ?]]...
        unshelve epose proof (canonical_form_qual P0 _) as [b EqB]...
        econstructor...
        eapply subqual_implies_compatible...
      SSCase "red_exp_inr".
        exists (exp_inr P0 e1)...
        unshelve epose proof (typing_canonical_inr _ _ _ Q T _)
          as [U1 [U2 [TypU1U2' SubQ']]]...
        inversion SubQ'.
        unshelve epose proof (subqual_transitivity Q empty P0 P _ _) as SubT...
        unshelve epose proof (subqual_regular _ _ _ SubT) as [? [? ?]]...
        unshelve epose proof (canonical_form_qual P0 _) as [b EqB]...
        econstructor...
        eapply subqual_implies_compatible...
      SSCase "red_exp_pair".
        exists (exp_pair P0 e1 e2)...
        unshelve epose proof (typing_canonical_pair _ _ _ _ Q T Typ)
          as [U1 [U2 [TypU1U2' SubQ']]]...
        inversion SubQ'.
        unshelve epose proof (subqual_transitivity Q empty P0 P _ _) as SubT...
        unshelve epose proof (subqual_regular _ _ _ SubT) as [? [? ?]]...
        unshelve epose proof (canonical_form_qual P0 _) as [b EqB]...
        econstructor...
        eapply subqual_implies_compatible...                 
Qed.
