(** Administrative lemmas for Fsub.CaptureTrack.

Authors: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    This file contains a number of administrative lemmas that we
    require for proving type-safety.  The lemmas mainly concern the
    relations [wf_typ] and [wf_env].

    This file also contains regularity lemmas, which show that various
    relations hold only for locally closed terms.  In addition to
    being necessary to complete the proof of type-safety, these lemmas
    help demonstrate that our definitions are correct; they would be
    worth proving even if they are unneeded for any "real" proofs.

    Table of contents:
      - #<a href="##wft">Properties of wf_typ</a>#
      - #<a href="##oktwft">Properties of wf_env and wf_typ</a>#
      - #<a href="##okt">Properties of wf_env</a>#
      - #<a href="##subst">Properties of substitution</a>#
      - #<a href="##regularity">Regularity lemmas</a>#
      - #<a href="##auto">Automation</a># *)
Require Import Fsub.CaptureTrack.Tactics.
Require Export Fsub.CaptureTrack.Fsub_LetSum_Infrastructure.


(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

(** If a type is well-formed in an environment, then it is locally
    closed. *)

Lemma qual_from_wf_qua : forall E T,
  wf_qua E T -> qual T.
Proof.
  intros E T H; induction H; eauto.
Qed.

Lemma type_from_wf_typ : forall E T,
  wf_typ E T -> type T
with qtype_from_wf_qtyp : forall E T,
  wf_qtyp E T -> qtype T.
Proof.
------
  clear type_from_wf_typ.
  intros E T H; induction H; eauto using qual_from_wf_qua.
------
  clear qtype_from_wf_qtyp.
  intros E T H; induction H; eauto using qual_from_wf_qua.
Qed.

(** The remaining properties are analogous to the properties that we
    need to show for the subtyping and typing relations. *)

Lemma wf_qua_weakening : forall T E F G,
  wf_qua (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wf_qua (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  intros T E F G Hwf_typ Hk.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction Hwf_typ; intros G Hok Heq; subst...
Qed.

Lemma wf_typ_weakening : forall T E F G,
  wf_typ (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T
with wf_qtyp_weakening : forall T E F G,
  wf_qtyp (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wf_qtyp (G ++ F ++ E) T.
Proof with simpl_env; eauto using wf_qua_weakening.
------
  clear wf_typ_weakening.
  intros T E F G Hwf_typ Hk.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction Hwf_typ; intros G Hok Heq; subst...
  Case "type_arrow".
    pick fresh Y and apply wf_typ_arrow...
    rewrite <- app_assoc.
    eapply wf_qtyp_weakening...
  Case "type_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    eapply wf_qtyp_weakening...
  Case "type_qall".
    pick fresh Y and apply wf_typ_qall...
    rewrite <- app_assoc.
    eapply wf_qtyp_weakening...
------
  clear wf_qtyp_weakening.
  intros T E F G Hwf_typ Hk.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction Hwf_typ; intros G Hok Heq; subst...
Qed.

Lemma wf_typ_weaken_head : forall T E F,
  wf_typ E T ->
  uniq (F ++ E) ->
  wf_typ (F ++ E) T.
Proof.
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_typ_weakening.
Qed.

Lemma wf_qtyp_weaken_head : forall T E F,
  wf_qtyp E T ->
  uniq (F ++ E) ->
  wf_qtyp (F ++ E) T.
Proof.
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_qtyp_weakening.
Qed.

Lemma wf_qua_weaken_head : forall T E F,
  wf_qua E T ->
  uniq (F ++ E) ->
  wf_qua (F ++ E) T.
Proof.
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_qua_weakening.
Qed.


Lemma wf_qua_narrowing_sub : forall V U T E F X,
  wf_qua (F ++ X ~ bind_sub V ++ E) T ->
  wf_qua (F ++ X ~ bind_sub U ++ E) T.
Proof with simpl_env; eauto.
  intros V U T E F X Hwf_typ.
  remember (F ++ X ~ bind_sub V ++ E) as G.
  generalize dependent F.
  induction Hwf_typ; intros F Heq; subst...
  Case "wf_qua_var".
    analyze_binds H...
  Case "wf_qua_term_var".
    analyze_binds H...
Qed.

Lemma wf_qua_narrowing_qua : forall V U T E F X,
  wf_qua (F ++ X ~ bind_qua V ++ E) T ->
  wf_qua (F ++ X ~ bind_qua U ++ E) T.
Proof with simpl_env; eauto.
  intros V U T E F X Hwf_typ.
  remember (F ++ X ~ bind_qua V ++ E) as G.
  generalize dependent F.
  induction Hwf_typ; intros F Heq; subst...
  Case "wf_qua_var".
    analyze_binds H...
  Case "wf_qua_term_var".
    analyze_binds H...
Qed.

Lemma wf_qua_narrowing_typ : forall V U T E F X,
  wf_qua (F ++ X ~ bind_typ V ++ E) T ->
  wf_qua (F ++ X ~ bind_typ U ++ E) T.
Proof with simpl_env; eauto.
  intros V U T E F X Hwf_typ.
  remember (F ++ X ~ bind_typ V ++ E) as G.
  generalize dependent F.
  induction Hwf_typ; intros F Heq; subst...
  Case "wf_qua_var".
    analyze_binds H...
  Case "wf_qua_term_var".
    analyze_binds H...
Qed.

Lemma wf_typ_narrowing_sub : forall V U T E F X,
  wf_typ (F ++ X ~ bind_sub V ++ E) T ->
  wf_typ (F ++ X ~ bind_sub U ++ E) T
with wf_qtyp_narrowing_sub : forall V U T E F X,
  wf_qtyp (F ++ X ~ bind_sub V ++ E) T ->
  wf_qtyp (F ++ X ~ bind_sub U ++ E) T.
Proof with simpl_env; eauto using wf_qua_narrowing_sub.
------
  clear wf_typ_narrowing_sub.
  intros V U T E F X Hwf_typ.
  remember (F ++ X ~ bind_sub V ++ E) as G.
  generalize dependent F.
  induction Hwf_typ; intros F Heq; subst...
  Case "wf_typ_var".
    analyze_binds H...
  Case "typ_arrow".
    pick fresh Y and apply wf_typ_arrow...
    rewrite <- app_assoc.
    eapply wf_qtyp_narrowing_sub...
  Case "typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    eapply wf_qtyp_narrowing_sub...
  Case "typ_qall".
    pick fresh Y and apply wf_typ_qall...
    rewrite <- app_assoc.
    eapply wf_qtyp_narrowing_sub...
------
  clear wf_qtyp_narrowing_sub.
  intros V U T E F X Hwf_typ.
  remember (F ++ X ~ bind_sub V ++ E) as G.
  generalize dependent F.
  induction Hwf_typ; intros F Heq; subst...
Qed.

Lemma wf_typ_narrowing_qua : forall V U T E F X,
  wf_typ (F ++ X ~ bind_qua V ++ E) T ->
  wf_typ (F ++ X ~ bind_qua U ++ E) T
with wf_qtyp_narrowing_qua : forall V U T E F X,
  wf_qtyp (F ++ X ~ bind_qua V ++ E) T ->
  wf_qtyp (F ++ X ~ bind_qua U ++ E) T.
Proof with simpl_env; eauto using wf_qua_narrowing_qua.
------
  clear wf_typ_narrowing_qua.
  intros V U T E F X Hwf_typ.
  remember (F ++ X ~ bind_qua V ++ E) as G.
  generalize dependent F.
  induction Hwf_typ; intros F Heq; subst...
  Case "wf_typ_var".
    analyze_binds H...
  Case "typ_arrow".
    pick fresh Y and apply wf_typ_arrow...
    rewrite <- app_assoc.
    eapply wf_qtyp_narrowing_qua...
  Case "typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    eapply wf_qtyp_narrowing_qua...
  Case "typ_qall".
    pick fresh Y and apply wf_typ_qall...
    rewrite <- app_assoc.
    eapply wf_qtyp_narrowing_qua...
------
  clear wf_qtyp_narrowing_qua.
  intros V U T E F X Hwf_typ.
  remember (F ++ X ~ bind_qua V ++ E) as G.
  generalize dependent F.
  induction Hwf_typ; intros F Heq; subst...
Qed.

Lemma wf_typ_narrowing_typ : forall V U T E F X,
  wf_typ (F ++ X ~ bind_typ V ++ E) T ->
  wf_typ (F ++ X ~ bind_typ U ++ E) T
with wf_qtyp_narrowing_typ : forall V U T E F X,
  wf_qtyp (F ++ X ~ bind_typ V ++ E) T ->
  wf_qtyp (F ++ X ~ bind_typ U ++ E) T.
Proof with simpl_env; eauto using wf_qua_narrowing_typ.
------
  clear wf_typ_narrowing_typ.
  intros V U T E F X Hwf_typ.
  remember (F ++ X ~ bind_typ V ++ E) as G.
  generalize dependent F.
  induction Hwf_typ; intros F Heq; subst...
  Case "wf_typ_var".
    analyze_binds H...
  Case "typ_arrow".
    pick fresh Y and apply wf_typ_arrow...
    rewrite <- app_assoc.
    eapply wf_qtyp_narrowing_typ...
  Case "typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    eapply wf_qtyp_narrowing_typ...
  Case "typ_qall".
    pick fresh Y and apply wf_typ_qall...
    rewrite <- app_assoc.
    eapply wf_qtyp_narrowing_typ...
------
  clear wf_qtyp_narrowing_typ.
  intros V U T E F X Hwf_typ.
  remember (F ++ X ~ bind_typ V ++ E) as G.
  generalize dependent F.
  induction Hwf_typ; intros F Heq; subst...
Qed.

(* Lemma wf_qua_strengthening_typ : forall E F x U T,
  wf_qua (F ++ x ~ bind_typ U ++ E) T ->
  wf_qua (F ++ E) T.
Proof with simpl_env; eauto.
  intros E F x U T H.
  remember (F ++ x ~ bind_typ U ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  Case "wf_qua_var".
    analyze_binds H...
Qed. *)

Lemma wf_qua_strengthening_sub : forall E F x U T,
  wf_qua (F ++ x ~ bind_sub U ++ E) T ->
  wf_qua (F ++ E) T.
Proof with simpl_env; eauto.
  intros E F x U T H.
  remember (F ++ x ~ bind_sub U ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  Case "wf_qua_var".
    analyze_binds H...
  Case "wf_qua_term_var".
    analyze_binds H...
Qed.

(* Lemma wf_typ_strengthening_typ : forall E F x U T,
  wf_typ (F ++ x ~ bind_typ U ++ E) T ->
  wf_typ (F ++ E) T
with wf_qtyp_strengthening_typ : forall E F x U T,
  wf_qtyp (F ++ x ~ bind_typ U ++ E) T ->
  wf_qtyp (F ++ E) T.
Proof with simpl_env; eauto using wf_qua_strengthening_typ.
------
  clear wf_typ_strengthening_typ.
  intros E F x U T H.
  remember (F ++ x ~ bind_typ U ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  Case "wf_typ_var".
    analyze_binds H...
  Case "wf_typ_arrow".
    pick fresh Y and apply wf_typ_arrow...
    rewrite <- app_assoc.
    eapply wf_qtyp_strengthening_typ...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    eapply wf_qtyp_strengthening_typ...
  Case "wf_typ_qall".
    pick fresh Y and apply wf_typ_qall...
    rewrite <- app_assoc.
    eapply wf_qtyp_strengthening_typ...
------
  clear wf_qtyp_strengthening_typ.
  intros E F x U T H.
  remember (F ++ x ~ bind_typ U ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...  
Qed. *)

Lemma wf_qua_subst_tb : forall F Q E Z P T,
  wf_qua (F ++ Z ~ bind_sub Q ++ E) T ->
  wf_typ E P ->
  uniq (map (subst_tb Z P) F ++ E) ->
  wf_qua (map (subst_tb Z P) F ++ E) T.
Proof with simpl_env; eauto using wf_qua_weaken_head, type_from_wf_typ.
------
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst...
  Case "wf_qua_var".
    destruct (X == Z); subst...
    SCase "X == Z".
      analyze_binds H...
      apply (wf_qua_fvar R)...
      replace (bind_qua R) with (subst_tb Z P (bind_qua R)) in *...
    SCase "X <> Z".
      analyze_binds H...
      apply (wf_qua_fvar R)...
      replace (bind_qua R) with (subst_tb Z P (bind_qua R)) in *...
  Case "wf_qua_term_var".
    destruct (x == Z); subst...
    SCase "x == Z".
      analyze_binds H...
      apply (wf_qua_term_fvar (subst_tqt Z P T))...
      replace (bind_typ (subst_tqt Z P T)) with (subst_tb Z P (bind_typ  T)) in *...
    SCase "x <> Z".
      analyze_binds H...
      apply (wf_qua_term_fvar (subst_tqt Z P T))...
Qed.

Lemma wf_typ_subst_tb : forall F Q E Z P T,
  wf_typ (F ++ Z ~ bind_sub Q ++ E) T ->
  wf_typ E P ->
  uniq (map (subst_tb Z P) F ++ E) ->
  wf_typ (map (subst_tb Z P) F ++ E) (subst_tt Z P T)
with wf_qtyp_subst_tb :  forall F Q E Z P T,
  wf_qtyp (F ++ Z ~ bind_sub Q ++ E) T ->
  wf_typ E P ->
  uniq (map (subst_tb Z P) F ++ E) ->
  wf_qtyp (map (subst_tb Z P) F ++ E) (subst_tqt Z P T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ,
  wf_qua_subst_tb.
------
  clear wf_typ_subst_tb.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt...
  Case "wf_typ_var".
    destruct (X == Z); subst...
    SCase "X <> Z".
      analyze_binds H...
      apply (wf_typ_var (subst_tt Z P U))...
  Case "wf_typ_arrow".
    pick fresh Y and apply wf_typ_arrow...
    rewrite subst_tqt_open_qqt_var...
    rewrite_env (map (subst_tb Z P) (Y ~ bind_typ T1 ++ F) ++ E).
    eapply wf_qtyp_subst_tb...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite subst_tqt_open_tqt_var...
    rewrite_env (map (subst_tb Z P) (Y ~ bind_sub T1 ++ F) ++ E).
    eapply wf_qtyp_subst_tb...
  Case "wf_typ_qall".
    pick fresh Y and apply wf_typ_qall...
    rewrite subst_tqt_open_qqt_var...
    rewrite_env (map (subst_tb Z P) (Y ~ bind_qua T1 ++ F) ++ E).
    eapply wf_qtyp_subst_tb...
------
  clear wf_qtyp_subst_tb.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_tqt; simpl subst_tt...
Qed.

Lemma wf_qua_subst_qb : forall F Q E Z P T,
  wf_qua (F ++ Z ~ bind_qua Q ++ E) T ->
  wf_qua E P ->
  uniq (map (subst_qb Z P) F ++ E) ->
  wf_qua (map (subst_qb Z P) F ++ E) (subst_qq Z P T).
Proof with simpl_env; eauto using wf_qua_weaken_head, type_from_wf_typ,
  qual_from_wf_qua.
------
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_qua Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_qq...
  Case "wf_qua_var".
    destruct (X == Z); subst...
    SCase "X in F".
      analyze_binds H...
      apply (wf_qua_fvar (subst_qq Z P R))...
  Case "wf_qua_term_var".
    destruct (x == Z); subst...
    SCase "x in F".
      analyze_binds H...
      apply (wf_qua_term_fvar (subst_qqt Z P T))...
Qed.

Lemma wf_typ_subst_qb : forall F Q E Z P T,
  wf_typ (F ++ Z ~ bind_qua Q ++ E) T ->
  wf_qua E P ->
  uniq (map (subst_qb Z P) F ++ E) ->
  wf_typ (map (subst_qb Z P) F ++ E) (subst_qt Z P T)
with wf_qtyp_subst_qb :  forall F Q E Z P T,
  wf_qtyp (F ++ Z ~ bind_qua Q ++ E) T ->
  wf_qua E P ->
  uniq (map (subst_qb Z P) F ++ E) ->
  wf_qtyp (map (subst_qb Z P) F ++ E) (subst_qqt Z P T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ,
  wf_qua_subst_qb, wf_qua_weaken_head, qual_from_wf_qua.
------
  clear wf_typ_subst_qb.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_qua Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_qt...
  Case "wf_typ_var".
    destruct (X == Z); subst...
    SCase "X == Z".
      analyze_binds H...
      apply (wf_typ_var (subst_qt Z P U))...   
    SCase "X <> Z".
      analyze_binds H...
      apply (wf_typ_var (subst_qt Z P U))...
  Case "wf_typ_arrow".
    pick fresh Y and apply wf_typ_arrow...
    rewrite subst_qqt_open_qqt_var...
    rewrite_env (map (subst_qb Z P) (Y ~ bind_typ T1 ++ F) ++ E).
    eapply wf_qtyp_subst_qb...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite subst_qqt_open_tqt_var...
    rewrite_env (map (subst_qb Z P) (Y ~ bind_sub T1 ++ F) ++ E).
    eapply wf_qtyp_subst_qb...
  Case "wf_typ_qall".
    pick fresh Y and apply wf_typ_qall...
    rewrite subst_qqt_open_qqt_var...
    rewrite_env (map (subst_qb Z P) (Y ~ bind_qua T1 ++ F) ++ E).
    eapply wf_qtyp_subst_qb...
------
  clear wf_qtyp_subst_qb.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_qua Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_qqt; simpl subst_qt...
Qed.

Lemma wf_qua_subst_qb_var : forall F Q E Z P T,
  wf_qua (F ++ Z ~ bind_typ Q ++ E) T ->
  wf_qua E P ->
  uniq (map (subst_qb Z P) F ++ E) ->
  wf_qua (map (subst_qb Z P) F ++ E) (subst_qq Z P T).
Proof with simpl_env; eauto using wf_qua_weaken_head, type_from_wf_typ,
  qual_from_wf_qua.
------
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_typ Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_qq...
  Case "wf_qua_var".
    destruct (X == Z); subst...
    SCase "X in F".
      analyze_binds H...
      apply (wf_qua_fvar (subst_qq Z P R))...
  Case "wf_qua_term_var".
    destruct (x == Z); subst...
    SCase "x in F".
      analyze_binds H...
      apply (wf_qua_term_fvar (subst_qqt Z P T))...
Qed.

Lemma wf_typ_subst_qb_var : forall F Q E Z P T,
  wf_typ (F ++ Z ~ bind_typ Q ++ E) T ->
  wf_qua E P ->
  uniq (map (subst_qb Z P) F ++ E) ->
  wf_typ (map (subst_qb Z P) F ++ E) (subst_qt Z P T)
with wf_qtyp_subst_qb_var :  forall F Q E Z P T,
  wf_qtyp (F ++ Z ~ bind_typ Q ++ E) T ->
  wf_qua E P ->
  uniq (map (subst_qb Z P) F ++ E) ->
  wf_qtyp (map (subst_qb Z P) F ++ E) (subst_qqt Z P T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ,
  wf_qua_subst_qb, wf_qua_subst_qb_var, wf_qua_weaken_head, qual_from_wf_qua.
------
  clear wf_typ_subst_qb_var.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_typ Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_qt...
  Case "wf_typ_var".
    destruct (X == Z); subst...
    SCase "X == Z".
      analyze_binds H...
      apply (wf_typ_var (subst_qt Z P U))...   
    SCase "X <> Z".
      analyze_binds H...
      apply (wf_typ_var (subst_qt Z P U))...
  Case "wf_typ_arrow".
    pick fresh Y and apply wf_typ_arrow...
    rewrite subst_qqt_open_qqt_var...
    rewrite_env (map (subst_qb Z P) (Y ~ bind_typ T1 ++ F) ++ E).
    eapply wf_qtyp_subst_qb_var...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite subst_qqt_open_tqt_var...
    rewrite_env (map (subst_qb Z P) (Y ~ bind_sub T1 ++ F) ++ E).
    eapply wf_qtyp_subst_qb_var...
  Case "wf_typ_qall".
    pick fresh Y and apply wf_typ_qall...
    rewrite subst_qqt_open_qqt_var...
    rewrite_env (map (subst_qb Z P) (Y ~ bind_qua T1 ++ F) ++ E).
    eapply wf_qtyp_subst_qb_var...
------
  clear wf_qtyp_subst_qb_var.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_typ Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_qqt; simpl subst_qt...
Qed.

Lemma wf_typ_open_typ : forall E U T1 T2,
  uniq E ->
  wf_typ E (typ_all T1 T2) ->
  wf_typ E U ->
  wf_qtyp E (open_tqt T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 Ok WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_tqt_intro X)...
  rewrite_env (map (subst_tb X U) empty ++ E).
  eapply wf_qtyp_subst_tb...
Qed.

Lemma wf_typ_open_qua : forall E U T1 T2,
  uniq E ->
  wf_typ E (typ_qall T1 T2) ->
  wf_qua E U ->
  wf_qtyp E (open_qqt T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 Ok WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_qqt_intro X)...
  rewrite_env (map (subst_qb X U) empty ++ E).
  eapply wf_qtyp_subst_qb...
Qed.

Lemma wf_typ_open_term_qua : forall E U T1 T2,
  uniq E ->
  wf_typ E (typ_arrow T1 T2) ->
  wf_qua E U ->
  wf_qtyp E (open_qqt T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 Ok WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_qqt_intro X)...
  rewrite_env (map (subst_qb X U) empty ++ E).
  eapply wf_qtyp_subst_qb_var...
Qed.

(* ********************************************************************** *)
(** * #<a name="oktwft"></a># Properties of [wf_env] and [wf_typ] *)

Lemma uniq_from_wf_env : forall E,
  wf_env E ->
  uniq E.
Proof.
  intros E H; induction H; auto.
Qed.

(** We add [uniq_from_wf_env] as a hint here since it helps blur the
    distinction between [wf_env] and [uniq] in proofs.  The lemmas in
    the MetatheoryEnv library use [uniq], whereas here we naturally
    have (or can easily show) the stronger [wf_env].  Thus,
    [uniq_from_wf_env] serves as a bridge that allows us to use the
    environments library. *)

#[export] Hint Resolve uniq_from_wf_env : core.

Lemma wf_qtyp_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  wf_qtyp E U.
Proof with auto using wf_qtyp_weaken_head.
  induction 1; intros J; analyze_binds J...
  injection BindsTacVal; intros; subst...
Qed.

Lemma wf_qtyp_from_wf_env_typ : forall x T E,
  wf_env (x ~ bind_typ T ++ E) ->
  wf_qtyp E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

Lemma wf_typ_from_wf_env_sub : forall x T E,
  wf_env (x ~ bind_sub T ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

Lemma wf_qua_from_wf_env_qua : forall x T E,
  wf_env (x ~ bind_qua T ++ E) ->
  wf_qua E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.


(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_env] *)

(** These properties are analogous to the properties that we need to
    show for the subtyping and typing relations. *)

Lemma wf_env_narrowing_sub : forall V E F U X,
  wf_env (F ++ X ~ bind_sub V ++ E) ->
  wf_typ E U ->
  wf_env (F ++ X ~ bind_sub U ++ E).
Proof with eauto using wf_typ_narrowing_sub, wf_qua_narrowing_sub, wf_qtyp_narrowing_sub.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_narrowing_qua : forall V E F U X,
  wf_env (F ++ X ~ bind_qua V ++ E) ->
  wf_qua E U ->
  wf_env (F ++ X ~ bind_qua U ++ E).
Proof with eauto using wf_typ_narrowing_qua, wf_qua_narrowing_qua, wf_qtyp_narrowing_qua.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_narrowing_typ : forall V E F U X,
  wf_env (F ++ X ~ bind_typ V ++ E) ->
  wf_qtyp E U ->
  wf_env (F ++ X ~ bind_typ U ++ E).
Proof with eauto using wf_typ_narrowing_typ, wf_qua_narrowing_typ, wf_qtyp_narrowing_typ.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_subst_tb : forall Q Z P E F,
  wf_env (F ++ Z ~ bind_sub Q ++ E) ->
  wf_typ E P ->
  wf_env (map (subst_tb Z P) F ++ E).
Proof with eauto 6 using wf_typ_subst_tb, wf_qtyp_subst_tb, wf_qua_subst_tb.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_tb...
Qed.

Lemma wf_env_subst_qb : forall Q Z P E F,
  wf_env (F ++ Z ~ bind_qua Q ++ E) ->
  wf_qua E P ->
  wf_env (map (subst_qb Z P) F ++ E).
Proof with eauto 6 using wf_typ_subst_qb, wf_qtyp_subst_qb, wf_qua_subst_qb.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_qb...
Qed.

Lemma wf_env_subst_qb_var : forall Q R Z P E F,
  wf_env (F ++ Z ~ bind_typ (qtyp_qtyp Q R) ++ E) ->
  wf_qua E P ->
  wf_env (map (subst_qb Z P) F ++ E).
Proof with eauto 6 using wf_typ_subst_qb_var, wf_qtyp_subst_qb_var, wf_qua_subst_qb_var.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_qb...
Qed.

Lemma wf_qua_subst_qb_var_indep : forall F Q E Z P R T,
  wf_qua (F ++ Z ~ bind_typ Q ++ E) T ->
  wf_qua E P ->
  wf_qua E R ->
  uniq (map (subst_qb Z P) F ++ E) ->
  wf_qua (map (subst_qb Z P) F ++ E) (subst_qq Z R T).
Proof with simpl_env; eauto using wf_qua_weaken_head, type_from_wf_typ,
  qual_from_wf_qua.
------
  intros F Q E Z P R T WT WP WR.
  remember (F ++ Z ~ bind_typ Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_qq...
  Case "wf_qua_var".
    destruct (X == Z); subst...
    SCase "X in F".
      analyze_binds H...
      apply (wf_qua_fvar (subst_qq Z P R0))...
  Case "wf_qua_term_var".
    destruct (x == Z); subst...
    SCase "x in F".
      analyze_binds H...
      apply (wf_qua_term_fvar (subst_qqt Z P T))...
Qed.

Lemma wf_qua_subst_qb_indep : forall F Q E Z P R T,
  wf_qua (F ++ Z ~ bind_qua Q ++ E) T ->
  wf_qua E P ->
  wf_qua E R ->
  uniq (map (subst_qb Z P) F ++ E) ->
  wf_qua (map (subst_qb Z P) F ++ E) (subst_qq Z R T).
Proof with simpl_env; eauto using wf_qua_weaken_head, type_from_wf_typ,
  qual_from_wf_qua.
------
  intros F Q E Z P R T WT WP WR.
  remember (F ++ Z ~ bind_qua Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_qq...
  Case "wf_qua_var".
    destruct (X == Z); subst...
    SCase "X in F".
      analyze_binds H...
      apply (wf_qua_fvar (subst_qq Z P R0))...
  Case "wf_qua_term_var".
    destruct (x == Z); subst...
    SCase "x in F".
      analyze_binds H...
      apply (wf_qua_term_fvar (subst_qqt Z P T))...
Qed.

Lemma wf_typ_from_wf_qtyp : forall E Q T,
  wf_qtyp E (qtyp_qtyp Q T) ->
  wf_typ E T.
Proof with eauto.
  intros; inversion H...
Qed.

Lemma wf_qua_from_wf_qtyp : forall E Q T,
  wf_qtyp E (qtyp_qtyp Q T) ->
  wf_qua E Q.
Proof with eauto.
  intros; inversion H...
Qed.

Lemma wf_qua_from_all_bound : forall E Q,
  qual Q ->
  (forall X, X `in` fv_qq Q ->
     (exists T, binds X (bind_typ T) E) \/ (exists Q, (binds X (bind_qua Q) E))) ->
  wf_qua E Q.
Proof with eauto.
  intros.
  induction H; subst; simpl in *...
  - unshelve epose proof (H0 X _)...
    destruct H as [[T Binds] | [Q Binds]]...
  - econstructor...
  - econstructor...
Qed.

(* ********************************************************************** *)
(** * #<a name="subst"></a># Environment is unchanged by substitution for a fresh name *)

Lemma notin_fv_tt_open_tt_rec : forall (Y X : atom) T k,
  X `notin` fv_tt (open_tt_rec k Y T) ->
  X `notin` fv_tt T
with notin_fv_tqt_open_tqt_rec : forall (Y X : atom) T k,
  X `notin` fv_tqt (open_tqt_rec k Y T) ->
  X `notin` fv_tqt T.
Proof.
------
  clear notin_fv_tt_open_tt_rec.
  intros Y X T.
  induction T; simpl; intros k Fr; eauto.
------
  clear notin_fv_tqt_open_tqt_rec.
  intros Y X T.
  induction T; simpl; intros k Fr; eauto.
Qed.

Lemma notin_fv_tt_open_tt : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_tt T.
Proof with eauto using notin_fv_tt_open_tt_rec.
  intros...
Qed.

Lemma notin_fv_tqt_open_tqt : forall (Y X : atom) T,
  X `notin` fv_tqt (open_tqt T Y) ->
  X `notin` fv_tqt T.
Proof with eauto using notin_fv_tqt_open_tqt_rec.
  intros...
Qed.

Lemma notin_fv_qq_open_qq_rec : forall (Y X : atom) T k,
  X `notin` fv_qq (open_qq_rec k Y T) ->
  X `notin` fv_qq T.
Proof.
  intros Y X T.
  induction T; simpl; intros k Fr; eauto.
Qed.

Lemma notin_fv_qt_open_qt_rec : forall (Y X : atom) T k,
  X `notin` fv_qt (open_qt_rec k Y T) ->
  X `notin` fv_qt T
with notin_fv_qqt_open_qqt_rec : forall (Y X : atom) T k,
  X `notin` fv_qqt (open_qqt_rec k Y T) ->
  X `notin` fv_qqt T.
Proof.
------
  clear notin_fv_qt_open_qt_rec.
  intros Y X T.
  induction T; simpl; intros k Fr; eauto using notin_fv_qq_open_qq_rec.
------
  clear notin_fv_qqt_open_qqt_rec.
  intros Y X T.
  induction T; simpl; intros k Fr; eauto using notin_fv_qq_open_qq_rec.
Qed.

Lemma notin_fv_qt_open_qt : forall (Y X : atom) T,
  X `notin` fv_qt (open_qt T Y) ->
  X `notin` fv_qt T.
Proof with eauto using notin_fv_qt_open_qt_rec.
  intros...
Qed.

Lemma notin_fv_qqt_open_qqt : forall (Y X : atom) T,
  X `notin` fv_qqt (open_qqt T Y) ->
  X `notin` fv_qqt T.
Proof with eauto using notin_fv_qqt_open_qqt_rec.
  intros...
Qed.

Lemma notin_fv_tt_open_qt_rec : forall (Y X : atom) T k,
  X `notin` fv_tt (open_qt_rec k Y T) ->
  X `notin` fv_tt T
with notin_fv_tqt_open_qqt_rec : forall (Y X : atom) T k,
  X `notin` fv_tqt (open_qqt_rec k Y T) ->
  X `notin` fv_tqt T.
Proof.
------
  clear notin_fv_tt_open_qt_rec.
  intros Y X T.
  induction T; simpl; intros k Fr; eauto.
------
  clear notin_fv_tqt_open_qqt_rec.
  intros Y X T.
  induction T; simpl; intros k Fr; eauto.
Qed.

Lemma notin_fv_tt_open_qt : forall (Y X : atom) T,
  X `notin` fv_tt (open_qt T Y) ->
  X `notin` fv_tt T.
Proof with eauto using notin_fv_tt_open_qt_rec.
  intros...
Qed.

Lemma notin_fv_tqt_open_qqt : forall (Y X : atom) T,
  X `notin` fv_tqt (open_qqt T Y) ->
  X `notin` fv_tqt T.
Proof with eauto using notin_fv_tqt_open_qqt_rec.
  intros...
Qed.

Lemma notin_fv_qt_open_tt_rec : forall (Y X : atom) T k,
  X `notin` fv_qt (open_tt_rec k Y T) ->
  X `notin` fv_qt T
with notin_fv_qqt_open_tqt_rec : forall (Y X : atom) T k,
  X `notin` fv_qqt (open_tqt_rec k Y T) ->
  X `notin` fv_qqt T.
Proof.
------
  clear notin_fv_qt_open_tt_rec.
  intros Y X T.
  induction T; simpl; intros k Fr; eauto using notin_fv_qq_open_qq_rec.
------
  clear notin_fv_qqt_open_tqt_rec.
  intros Y X T.
  induction T; simpl; intros k Fr; eauto using notin_fv_qq_open_qq_rec.
Qed.

Lemma notin_fv_qt_open_tt : forall (Y X : atom) T,
  X `notin` fv_qt (open_tt T Y) ->
  X `notin` fv_qt T.
Proof with eauto using notin_fv_qt_open_tt_rec.
  intros...
Qed.

Lemma notin_fv_qqt_open_tqt : forall (Y X : atom) T,
  X `notin` fv_qqt (open_tqt T Y) ->
  X `notin` fv_qqt T.
Proof with eauto using notin_fv_qqt_open_tqt_rec.
  intros...
Qed.

Lemma notin_fv_wf_qua : forall E (X : atom) T,
  wf_qua E T ->
  X `notin` dom E ->
  X `notin` fv_qq T.
Proof with auto.
  intros E X T Wf.
  induction Wf; intros Fr; simpl...
  Case "wf_qua_var".
    assert (X0 `in` (dom E))...
    eapply binds_In; eauto.
    assert (X <> X0) by fsetdec. fsetdec.
  Case "wf_qua_all".
    assert (x `in` (dom E))...
    eapply binds_In; eauto.
    assert (X <> x) by fsetdec. fsetdec.
Qed.

Lemma notin_fv_tt_wf_typ : forall E (X : atom) T,
  wf_typ E T ->
  X `notin` dom E ->
  X `notin` fv_tt T
with notin_fv_tqt_wf_qtyp : forall E (X : atom) T,
  wf_qtyp E T ->
  X `notin` dom E ->
  X `notin` fv_tqt T.
Proof with eauto.
------
  clear notin_fv_tt_wf_typ.
  intros E X T Wf_typ.
  induction Wf_typ; intros Fr; simpl...
  Case "wf_typ_var".
    assert (X0 `in` (dom E))...
    assert (X <> X0) by fsetdec. fsetdec.
  Case "wf_typ_arrow".
    apply notin_union...
    pick fresh Y.
    eapply (notin_fv_tqt_open_qqt Y)...
  Case "wf_typ_all".
    apply notin_union...
    pick fresh Y.
    eapply (notin_fv_tqt_open_tqt Y)...
  Case "wf_typ_qall".
    pick fresh Y.
    eapply (notin_fv_tqt_open_qqt Y)...
------
  clear notin_fv_tqt_wf_qtyp.
  intros E X T Wf_typ.
  induction Wf_typ; intros Fr; simpl...
Qed.

Lemma notin_fv_qq_wf_qua : forall E (X : atom) T,
  wf_qua E T ->
  X `notin` dom E ->
  X `notin` fv_qq T.
Proof with eauto.
  intros E X T Wf.
  induction Wf; intros Fr; simpl...
  Case "wf_qua_var".
    assert (X0 `in` (dom E))...
    assert (X <> X0) by fsetdec. fsetdec.
  Case "wf_qua_term_var".
    assert (x `in` (dom E))...
    assert (X <> x) by fsetdec. fsetdec.
Qed.

Lemma notin_fv_qt_wf_typ : forall E (X : atom) T,
  wf_typ E T ->
  X `notin` dom E ->
  X `notin` fv_qt T
with notin_fv_qqt_wf_qtyp : forall E (X : atom) T,
  wf_qtyp E T ->
  X `notin` dom E ->
  X `notin` fv_qqt T.
Proof with eauto using notin_fv_qq_wf_qua.
------
  clear notin_fv_qt_wf_typ.
  intros E X T Wf_typ.
  induction Wf_typ; intros Fr; simpl...
  Case "wf_typ_arrow".
    apply notin_union...
    pick fresh Y.
    eapply (notin_fv_qqt_open_qqt Y)...
  Case "wf_typ_all".
    apply notin_union...
    pick fresh Y.
    eapply (notin_fv_qqt_open_tqt Y)...
  Case "wf_typ_qall".
    apply notin_union...
    pick fresh Y.
    eapply (notin_fv_qqt_open_qqt Y)...
------
  clear notin_fv_qqt_wf_qtyp.
  intros E X T Wf_typ.
  induction Wf_typ; intros Fr; simpl...
Qed.

Lemma fv_exp_for_qua_through_subst_ee : forall x Q u e,
  (fv_exp_for_qua (subst_ee x u Q e)) = 
    (subst_qq x (fv_exp_for_qua u) (fv_exp_for_qua e)).
Proof with eauto; try solve [f_equal; eauto].
  intros.
  induction e; simpl; simpl subst_qq in *; simpl in *; eauto; f_equal...
  * destruct (a == x); subst...
Qed.

Lemma fv_exp_for_qua_subst_te_intro : forall X P e,
  fv_exp_for_qua e = fv_exp_for_qua (subst_te X P e).
Proof with eauto; try solve [f_equal; eauto].
  intros X P e.
  induction e; simpl; eauto; f_equal...
Qed.

Lemma fv_exp_for_qua_subst_qe_intro : forall X P e,
  fv_exp_for_qua e = fv_exp_for_qua (subst_qe X P e).
Proof with eauto; try solve [f_equal; eauto].
  intros X P e.
  induction e; simpl; eauto; f_equal...
Qed.

Lemma map_subst_tb_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_tb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_tt_wf_typ; eauto.
  rewrite <- IHwf_env...
    rewrite <- subst_tqt_fresh... eapply notin_fv_tqt_wf_qtyp; eauto.
  rewrite <- IHwf_env...
Qed.

Lemma map_subst_qb_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_qb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite <- subst_qt_fresh... eapply notin_fv_qt_wf_typ; eauto.
  rewrite <- IHwf_env...
    rewrite <- subst_qqt_fresh... eapply notin_fv_qqt_wf_qtyp; eauto.
  rewrite <- IHwf_env...
    rewrite <- subst_qq_fresh... eapply notin_fv_qq_wf_qua; eauto.
Qed.

Lemma fv_exp_for_qua_qual : forall e,
  qual (fv_exp_for_qua e).
Proof with eauto.
  intros.
  induction e; simpl...
Qed.

Lemma fv_exp_cap_open_ee : forall e (k: nat) (x : atom) (Y : atom),
  x `in` (fv_qq (fv_exp_for_qua e)) ->
  x `in` (fv_qq (fv_exp_for_qua (open_ee_rec k Y Y e))).
Proof with eauto.
  intros e k x Y Hxine. revert k.
  induction e; intro k; simpl in *...
  * exfalso. fsetdec.
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
      apply AtomSetImpl.union_1 in H...
      destruct H...
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
Qed.

Lemma fv_exp_cap_open_te : forall e (k : nat) (x : atom) (Y : atom),
  x `in` (fv_qq (fv_exp_for_qua e)) ->
  x `in` (fv_qq (fv_exp_for_qua (open_te_rec k Y e))).
Proof with eauto.
  intros e k x Y Hxine. revert k.
  induction e; intro k; simpl...
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
      apply AtomSetImpl.union_1 in H...
      destruct H...
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
Qed.

Lemma fv_exp_cap_open_ce : forall e (k : nat) (x : atom) (Y : atom),
  x `in` (fv_qq (fv_exp_for_qua e)) ->
  x `in` (fv_qq (fv_exp_for_qua (open_qe_rec k Y e))).
Proof with eauto.
  intros e k x Y Hxine. revert k.
  induction e; intro k; simpl...
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
      apply AtomSetImpl.union_1 in H...
      destruct H...
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
  * simpl in Hxine.
    apply AtomSetImpl.union_1 in Hxine.
    destruct Hxine.
    ** apply AtomSetImpl.union_2...
    ** apply AtomSetImpl.union_3...
Qed.

Lemma typing_qua_all_bound : forall E e T,
  typing E e T ->
  (forall X, X `in` fv_qq (fv_exp_for_qua e) ->
    (exists T, binds X (bind_typ T) E) \/ (exists Q, (binds X (bind_qua Q) E))).
Proof with eauto; simpl_env in *.
  intros.
  induction H; simpl in *; simpl_env...
  - replace X with x... fsetdec.
  - pick fresh Y.
    destruct (H2 Y) as [[T Binds] | [Q Binds]]...
      eapply fv_exp_cap_open_ee...
    analyze_binds Binds...
    analyze_binds Binds...
  - rewrite AtomSetFacts.union_iff in H0.
    destruct H0...
  - pick fresh Y.
    destruct (H2 Y) as [[T Binds] | [Q Binds]]...
      eapply fv_exp_cap_open_te...
    analyze_binds Binds...
    analyze_binds Binds...
  - pick fresh Y.
    destruct (H2 Y) as [[T Binds] | [Q' Binds]]...
      eapply fv_exp_cap_open_ce...
    analyze_binds Binds...
    analyze_binds Binds...
  - rewrite AtomSetFacts.union_iff in H0.
    destruct H0...
    pick fresh Y.
    destruct (H3 Y) as [[T Binds] | [Q' Binds]]...
      eapply fv_exp_cap_open_ee...
    analyze_binds Binds...
    analyze_binds Binds...   
  - rewrite AtomSetFacts.union_iff in H0.
    rewrite AtomSetFacts.union_iff in H0.
    destruct H0 as [? | [? | ?]]...
    pick fresh Y.
    destruct (H3 Y) as [[T' Binds] | [Q' Binds]]...
      eapply fv_exp_cap_open_ee...
    analyze_binds Binds...
    analyze_binds Binds...
    pick fresh Y.
    destruct (H5 Y) as [[T' Binds] | [Q' Binds]]...
      eapply fv_exp_cap_open_ee...
    analyze_binds Binds...
    analyze_binds Binds...
  - rewrite AtomSetFacts.union_iff in H0.
    destruct H0...
Qed.

(* ********************************************************************** *)
(** * #<a name="regularity"></a># Regularity of relations *)

Lemma subqual_regular : forall E S T,
  subqual E S T ->
  wf_env E /\ wf_qua E S /\ wf_qua E T.
Proof with simpl_env; try solve [auto | intuition auto].
  intros E S T H.
  induction H...
  Case "sub_trans_qvar".
    intuition eauto.
  Case "sub_trans_qvar_term".
    intuition eauto.
Qed.

Lemma sub_regular : forall E S T,
  sub E S T ->
  wf_env E /\ wf_typ E S /\ wf_typ E T
with subqtype_regular : forall E S T,
  subqtype E S T ->
  wf_env E /\ wf_qtyp E S /\ wf_qtyp E T.
Proof with simpl_env; try solve [auto | intuition auto].
------
  clear sub_regular.
  intros E S T H.
  induction H;
    repeat (select (subqtype _ _ _) (fun H => apply subqtype_regular in H))...
  Case "sub_trans_tvar".
    intuition eauto.
  Case "sub_arrow".
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh Y and apply wf_typ_arrow...
      unshelve epose proof (H0 Y _) as SubQ1;
        try apply subqtype_regular in SubQ1...
      rewrite_env (empty ++ Y ~ bind_typ S1 ++ E).
      apply (wf_qtyp_narrowing_typ T1)...
    SCase "Third of original three conjuncts".
      pick fresh Y and apply wf_typ_arrow...
      unshelve epose proof (H0 Y _) as SubQ1;
        try apply subqtype_regular in SubQ1...
  Case "sub_all".
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      unshelve epose proof (H0 Y _) as SubQ1;
        try apply subqtype_regular in SubQ1...
      rewrite_env (empty ++ Y ~ bind_sub S1 ++ E).
      apply (wf_qtyp_narrowing_sub T1)...
    SCase "Third of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      unshelve epose proof (H0 Y _) as SubQ1;
        try apply subqtype_regular in SubQ1...
  Case "sub_qall".
    eapply subqual_regular in H.
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh Y and apply wf_typ_qall...
      unshelve epose proof (H0 Y _) as SubQ1;
        try apply subqtype_regular in SubQ1...
      rewrite_env (empty ++ Y ~ bind_qua S1 ++ E).
      apply (wf_qtyp_narrowing_qua T1)...
    SCase "Third of original three conjuncts".
      pick fresh Y and apply wf_typ_qall...
      unshelve epose proof (H0 Y _) as SubQ1;
      try apply subqtype_regular in SubQ1...
------
  clear subqtype_regular.
  intros E S T H.
  induction H;
    repeat (select (sub _ _ _) (fun H => apply sub_regular in H));
    repeat (select (subqual _ _ _) (fun H => apply subqual_regular in H))...
Qed.

Lemma typing_qua : forall E e T,
  typing E e T ->
  wf_qua E (fv_exp_for_qua e).
Proof with eauto.
  intros.
  apply wf_qua_from_all_bound.
  apply fv_exp_for_qua_qual.
  apply typing_qua_all_bound with (T := T)...
Qed.

Lemma typing_regular : forall E e T,
  typing E e T ->
  wf_env E /\ expr e /\ wf_qtyp E T.
Proof with simpl_env; try solve [eauto using wf_typ_from_wf_qtyp, wf_qua_from_wf_qtyp |
  intuition eauto using wf_typ_from_wf_qtyp, wf_qua_from_wf_qtyp].
  intros E e T H; induction H...
  Case "typing_var".
    repeat split...
    eapply wf_qtyp_from_binds_typ in H0...
  Case "typing_abs".
    pick fresh y.
    destruct (H1 y) as [Hok [J K]]...
    repeat split. inversion Hok...
    SCase "Second of original three conjuncts".
      pick fresh x and apply expr_abs; eauto using qual_from_wf_qua...
        eapply qual_from_wf_qua. eapply subqual_regular...
        eauto using qtype_from_wf_qtyp, wf_qtyp_from_wf_env_typ.
        destruct (H1 x)...
        eapply subqual_regular...
    SCase "Third of original three conjuncts".
      pick fresh Z and apply wf_typ_arrow...
      eauto using wf_qtyp_from_wf_env_typ.
      destruct (H1 Z)...
  Case "typing_app".
    destruct IHtyping1 as [S0 [S1 S2]].
    destruct IHtyping2 as [_ [S3 S4]].
    inversion S4; subst.
    repeat split...
    econstructor... eauto using qual_from_wf_qua.
    inversion select (wf_qtyp _ (qtyp_qtyp _ (typ_arrow _ _))); subst...
    eapply (wf_typ_open_term_qua E R); eauto.
  Case "typing_tabs".
    pick fresh Y.
    destruct (H1 Y) as [Hok [J K]]...
    inversion Hok; subst.
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh X and apply expr_tabs; eauto using qual_from_wf_qua...
        eauto using type_from_wf_typ, wf_typ_from_wf_env_sub...
        eapply qual_from_wf_qua. eapply subqual_regular...
        eapply type_from_wf_typ...
        destruct (H1 X)...
        eapply subqual_regular...
    SCase "Third of original three conjuncts".
      pick fresh Z and apply wf_typ_all...
      destruct (H1 Z)...
  Case "typing_tapp".
    destruct (sub_regular _ _ _ H0) as [R1 [R2 R3]].
    repeat split...
    SCase "Second of original three conjuncts".
      apply expr_tapp...
      eauto using type_from_wf_typ.
    SCase "Third of original three conjuncts".
      destruct IHtyping as [R1' [R2' R3']].
        inversion select (wf_qtyp _ (qtyp_qtyp _ (typ_all _ _))).
      eapply wf_typ_open_typ; eauto.
  Case "typing_qabs".
    pick fresh Y.
    destruct (H1 Y) as [Hok [J K]]...
    inversion Hok; subst.
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh X and apply expr_qabs; eauto using qual_from_wf_qua...
        eapply qual_from_wf_qua. eapply subqual_regular...
        destruct (H1 X)...
        eapply subqual_regular...
    SCase "Third of original three conjuncts".
      pick fresh Z and apply wf_typ_qall...
      destruct (H1 Z)...
  Case "typing_qapp".
    destruct (subqual_regular _ _ _ H0) as [R1 [R2 R3]].
    repeat split...
    SCase "Second of original three conjuncts".
      apply expr_qapp...
      eauto using qual_from_wf_qua.
    SCase "Third of original three conjuncts".
      destruct IHtyping as [R1' [R2' R3']].
        inversion select (wf_qtyp _ (qtyp_qtyp _ (typ_qall _ _))).
      eapply wf_typ_open_qua; eauto.
  Case "typing_sub".
    repeat split...
    destruct (subqtype_regular _ _ _ H0)...
  Case "typing_let".
    destruct IHtyping as [R1' [R2' R3']].
    repeat split...
    pick fresh y and apply expr_let...
      inversion R3'; subst. eapply qual_from_wf_qua with (E := E)...
    destruct (H2 y) as [K1 [K2 K3]]...
  Case "typing_inl".
    repeat split... 
    eapply expr_inl; eauto using qual_from_wf_qua...
    eapply qual_from_wf_qua with (E := E)...
    eapply subqual_regular...
    eapply subqual_regular...
  Case "typing_inr".
    repeat split... 
    eapply expr_inr; eauto using qual_from_wf_qua...  
    eapply qual_from_wf_qua with (E := E)...
    eapply subqual_regular...
    eapply subqual_regular...
  Case "typing_case".
    repeat split...
    destruct IHtyping as [R1' [R2' R3']].
    SCase "Second of original three conjuncts".
      pick fresh x and apply expr_case...
        inversion R3'; subst; inversion H9; subst; inversion H10. eapply qual_from_wf_qua with (E := E)...
        inversion R3'; subst; inversion H9; subst; inversion H11. eapply qual_from_wf_qua with (E := E)...
        destruct (H2 x) as [? [? ?]]...
        destruct (H4 x) as [? [? ?]]...
  Case "typing_pair".
    destruct IHtyping1 as [R1' [R2' R3']]...
    destruct IHtyping2 as [R1'' [R2'' R3'']]...
    repeat split...
    econstructor... eapply qual_from_wf_qua. eapply subqual_regular...
    eapply subqual_regular...
  Case "typing_first".
    destruct IHtyping as [R1' [R2' R3']]...
    repeat split...
    inversion R3'; subst...
    inversion select (wf_typ _ (typ_pair _ _))...
  Case "typing_second".
    destruct IHtyping as [R1' [R2' R3']]...
    repeat split...
    inversion R3'; subst...
    inversion select (wf_typ _ (typ_pair _ _))... 
  Case "typing_upqual".
    destruct IHtyping as [R1' [R2' R3']]...
    destruct (subqual_regular E Q P) as [? [? ?]]...
    repeat split; eauto using qual_from_wf_qua...
  Case "typing_check".
    destruct IHtyping as [R1' [R2' R3']]...
    destruct (subqual_regular E Q P) as [? [? ?]]...
    repeat split; eauto using qual_from_wf_qua...
Qed.

Lemma value_regular : forall e,
  value e ->
  expr e.
Proof.
  intros e H. induction H; auto.
Qed.

Lemma red_regular : forall e e',
  red e e' ->
  expr e /\ expr e'.
Proof with try solve [auto | intuition auto].
  intros e e' H.
  induction H; assert(J := value_regular); split...
  Case "red_abs".
    inversion H. pick fresh y. rewrite (subst_ee_intro y)...
  Case "red_tabs".
    inversion H. pick fresh Y. rewrite (subst_te_intro Y)...
  Case "red_qabs".
    inversion H. pick fresh Y. rewrite (subst_qe_intro Y)...
  Case "red_let".
    inversion H1. pick fresh y. rewrite (subst_ee_intro y)...
  Case "red_case_inl".
    inversion H3. pick fresh y. rewrite (subst_ee_intro y)...
  Case "red_case_inr".
    inversion H4. pick fresh y. rewrite (subst_ee_intro y)...
  Case "red_upqual_abs".
    inversion H1; subst... econstructor...
  Case "red_upqual_tabs".
    inversion H1; subst... econstructor...
  Case "red_upqual_qabs".
    inversion H1; subst... econstructor...  
  Case "red_upqual_inl".
    inversion H1; subst... econstructor...  
  Case "red_upqual_inr".
    inversion H1; subst... econstructor...  
  Case "red_upqual_pair".
    inversion H1; subst... 
    inversion H1; subst...
Qed.

(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)


Lemma qual_from_typing_qtyp : forall E e Q T,
  typing E e (qtyp_qtyp Q T) ->
  qual Q.
Proof with eauto using qual_from_wf_qua.
  intros E e Q T Typ.
  destruct (typing_regular E e (qtyp_qtyp Q T))
    as [_ [_ Hqt]]...
  eapply qtype_from_wf_qtyp in Hqt...
  inversion Hqt...
Qed.

Lemma wf_qua_from_wf_qua_join_left : forall E R1 R2,
  wf_qua E (qua_join R1 R2) ->
  wf_qua E R1.
Proof with eauto.
  intros. inversion H...
Qed.

Lemma wf_qua_from_wf_qua_join_right : forall E R1 R2,
  wf_qua E (qua_join R1 R2) ->
  wf_qua E R2.
Proof with eauto.
  intros. inversion H...
Qed.

Lemma wf_qua_from_wf_qua_meet_left : forall E R1 R2,
  wf_qua E (qua_meet R1 R2) ->
  wf_qua E R1.
Proof with eauto.
  intros. inversion H...
Qed.

Lemma wf_qua_from_wf_qua_meet_right : forall E R1 R2,
  wf_qua E (qua_meet R1 R2) ->
  wf_qua E R2.
Proof with eauto.
  intros. inversion H...
Qed.

#[export] Hint Resolve wf_qua_from_wf_qua_join_left wf_qua_from_wf_qua_join_right
wf_qua_from_wf_qua_meet_left wf_qua_from_wf_qua_meet_right : core.


(** The lemma [uniq_from_wf_env] was already added above as a hint
    since it helps blur the distinction between [wf_env] and [uniq] in
    proofs.

    As currently stated, the regularity lemmas are ill-suited to be
    used with [auto] and [eauto] since they end in conjunctions.  Even
    if we were, for example, to split [sub_regularity] into three
    separate lemmas, the resulting lemmas would be usable only by
    [eauto] and there is no guarantee that [eauto] would be able to
    find proofs effectively.  Thus, the hints below apply the
    regularity lemmas and [type_from_wf_typ] to discharge goals about
    local closure and well-formedness, but in such a way as to
    minimize proof search.

    The first hint introduces an [wf_env] fact into the context.  It
    works well when combined with the lemmas relating [wf_env] and
    [wf_typ].  We choose to use those lemmas explicitly via [(auto
    using ...)] tactics rather than add them as hints.  When used this
    way, the explicitness makes the proof more informative rather than
    more cluttered (with useless details).

    The other three hints try outright to solve their respective
    goals. *)

#[export] Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: subqual _ _ _ |- _ => apply (proj1 (subqual_regular _ _ _ H))
  | H: subqtype _ _ _ |- _ => apply (proj1 (subqtype_regular _ _ _ H))
  | H: sub _ _ _ |- _ => apply (proj1 (sub_regular _ _ _ H))
  | H: typing _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ H))
  end : core.

#[export] Hint Extern 1 (wf_qtyp ?E ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ H)))
  | H: subqtype E T _ |- _ => apply (proj1 (proj2 (subqtype_regular _ _ _ H)))
  | H: subqtype E _ T |- _ => apply (proj2 (proj2 (subqtype_regular _ _ _ H)))
  end : core.

#[export] Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: sub E T _ |- _ => apply (proj1 (proj2 (sub_regular _ _ _ H)))
  | H: sub E _ T |- _ => apply (proj2 (proj2 (sub_regular _ _ _ H)))
  | H: wf_qtyp E (qtyp_qtyp ?Q T) |- _ => apply (wf_typ_from_wf_qtyp E Q T); auto
  end : core.

#[export] Hint Extern 1 (wf_qua ?E ?T) =>
  match goal with
  | H: subqual E T _ |- _ => apply (proj1 (proj2 (subqual_regular _ _ _ H)))
  | H: subqual E _ T |- _ => apply (proj2 (proj2 (subqual_regular _ _ _ H)))
  | H: wf_qtyp E (qtyp_qtyp T ?S) |- _ => apply (wf_qua_from_wf_qtyp E T S); auto
  end : core.

#[export] Hint Extern 1 (type ?T) =>
  let go E := apply (type_from_wf_typ E); auto in
  match goal with
  | H: typing ?E _ (qtyp_qtyp _ T) |- _ => go E
  | H: subqtype ?E _ (qtyp_qtyp _ T) _ |- _ => go E
  | H: subqtype ?E _ _ (qtyp_qtyp _ T) |- _ => go E
  | H: sub ?E T _ |- _ => go E
  | H: sub ?E _ T |- _ => go E
  end : core.

#[export] Hint Extern 1 (qtype ?T) =>
  let go E := apply (qtype_from_wf_qtyp E); auto in
  match goal with
  | H: typing ?E _ T |- _ => go E
  | H: subqtype ?E _ T |- _ => go E
  | H: subqtype ?E T _ |- _ => go E
  end : core.

#[export] Hint Extern 1 (qual ?T) =>
  let go E := apply (qual_from_wf_qua E); auto in
  match goal with
  | H: typing ?E _ (qtyp_qtyp T _) |- _ => go E
  | H: subqtype ?E _ (qtyp_qtyp T _) _ |- _ => go E
  | H: subqtype ?E _ _ (qtyp_qtyp T _) |- _ => go E
  | H: subqual ?E T _ |- _ => go E
  | H: subqual ?E _ T |- _ => go E
  end : core.

#[export] Hint Extern 1 (expr ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ H)))
  | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ H))
  end : core.
