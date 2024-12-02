(** This file defines all of the semantic typing lemmas for session types. Most of
these lemmas are semantic versions of the syntactic typing judgments typically
found in a syntactic type system. *)
From iris.bi.lib Require Import core.
From dlfactris.lang Require Import metatheory.
From dlfactris.session_logic Require Import proofmode.
From dlfactris.logrel Require Export session_types term_typing_rules.

Section session_typing_rules.
  Implicit Types A B : ltty.
  Implicit Types S T : lsty.
  Implicit Types Γ : ctx.

  Lemma ltyped_fork_chan Γ1 Γ2 S f :                                             (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=406e6468 *)
    (Γ2 ⊨ f : chan (lty_dual S) ⊸ any ⫤ []) -∗
    Γ1 ++ Γ2 ⊨ fork_chan f : chan S ⫤ Γ1.
  Proof.
    iIntros "#Hf" (vs) "!> HΓ /=".
    iDestruct (ctx_ltyped_app with "HΓ") as "[HΓ1 HΓ2]".
    iApply ("Hf" with "HΓ2"); iIntros (v) "[HA HΓ']".
    iApply (wp_fork_chan with "[HA]").
    { iIntros "!>" (c) "Hc". by iApply "HA". }
    iIntros "!>" (c) "Hc". iFrame.
  Qed.

  Lemma ltyped_send Γ Γ' (x : string) e A S :
    Γ' !! x = Some (chan (<!!> TY A; S))%lty →
    (Γ ⊨ e : A ⫤ Γ') -∗
    (Γ ⊨ send x e : () ⫤ ctx_overwrite x (chan S) Γ').
  Proof.
    iIntros (HΓx%ctx_lookup_perm) "#He !>". iIntros (vs) "HΓ /=".
    iApply ("He" with "HΓ"); iIntros (v) "[HA HΓ']".
    rewrite {2}HΓx /=.
    iDestruct (ctx_ltyped_cons_named with "HΓ'") as (c Hvs) "[Hc HΓ']".
    rewrite Hvs. wp_send with "[HA //]". iSplitR; [done|].
    iDestruct (ctx_ltyped_overwrite _ _ x (chan _) with "Hc HΓ'") as "HΓ' /=".
    by rewrite (insert_id vs).
  Qed.

  Lemma ltyped_send_texist {kt : ktele} Γ Γ' (x : string) e M
      (A : kt -k> ltty) (S : kt -k> lsty) Xs :
    LtyMsgTele M A S →
    Γ' !! x = Some (chan (<!!> M))%lty →
    (Γ ⊨ e : ktele_app A Xs ⫤ Γ') -∗
    (Γ ⊨ send x e : () ⫤ ctx_overwrite x (chan (ktele_app S Xs)) Γ').
  Proof.
    rewrite /LtyMsgTele.
    iIntros (HM HΓx%ctx_lookup_perm) "#He".
    iDestruct (ltyped_subsumption with "[] [] [] He") as "He'";
      [iApply ctx_le_refl|iApply lty_le_refl|..].
    { rewrite {2}HΓx.
      iApply ctx_le_cons; [|iApply ctx_le_refl]. iApply lty_le_chan.
      iEval (rewrite HM).
      iApply (lty_le_texist_intro_l (kt:=kt)). }
    iDestruct (ltyped_send _ _ x _ (ktele_app A Xs) (ktele_app S Xs) with "He'")
      as "He''".
    { apply ctx_insert_lookup. }
    rewrite /ctx_overwrite ctx_filter_ne_cons ctx_filter_ne_idemp.
    iApply "He''".
  Qed.

  Lemma ltyped_close Γ (x : string) :
    Γ !! x = Some (chan END!!)%lty →
    Γ ⊨ close x : () ⫤ ctx_filter_ne x Γ.
  Proof.
    iIntros (HΓx%ctx_lookup_perm) "!>". iIntros (vs) "HΓ /=".
    rewrite {1}HΓx /=.
    iDestruct (ctx_ltyped_cons_named with "HΓ") as (c Hvs) "[Hc HΓ]". rewrite Hvs.
    wp_close. by iFrame.
  Qed.

  Lemma subprot_lmsg_texist {kt : ktele} (m : ltys kt → msg) :
    ⊢ (<?> (∃.. Xs : ltys kt, m Xs)%lmsg) ⊑ (<? (Xs : ltys kt)> m Xs).
  Proof.
    iInduction kt as [|k kt] "IH".
    { rewrite /lty_msg_texist /=. by iExists LTysO. }
    rewrite /lty_msg_texist /=. iIntros (X).
    iApply (subprot_trans with "IH"). iIntros (Xs). by iExists (LTysS _ _).
  Qed.

  Lemma ltyped_recv_texist {kt} Γ1 Γ2 M x (xc : string) (e : expr)
      (A : kt -k> ltty) (S : kt -k> lsty) (B : ltty) :
    x ≠ BNamed xc →
    Γ1 !! xc = Some (chan (<??> M))%lty →
    LtyMsgTele M A S →
    (∀ Ys,
      ctx_overwrite x (ktele_app A Ys)
        (ctx_overwrite xc (chan (ktele_app S Ys)) Γ1) ⊨ e : B ⫤ Γ2) -∗
    Γ1 ⊨ (let: x := recv xc in e) : B ⫤
          ctx_filter_eq x (ctx_filter_ne xc Γ1) ++ ctx_anonymize x Γ2.
  Proof.
    rewrite /LtyMsgTele.
    iIntros (Hx HΓxc%ctx_lookup_perm HM) "#He !>". iIntros (vs) "HΓ1 /=".
    rewrite {2}HΓxc /=.
    iDestruct (ctx_ltyped_cons_named with "HΓ1") as (c Hvs) "[Hc HΓ1]".
    rewrite Hvs {1}(ctx_filter_eq_perm (ctx_filter_ne xc Γ1) x).
    iDestruct (ctx_ltyped_app with "HΓ1") as "[HΓ1eq HΓ1neq]".
    iAssert (c ↣ <? (Xs : ltys kt) (v : val)>
      MSG v {{ ltty_car (ktele_app A Xs) v }};
        lsty_car (ktele_app S Xs))%I with "[Hc]" as "Hc".
    { iApply (own_chan_subprot with "Hc"); iIntros "!>". rewrite HM.
      iApply subprot_lmsg_texist. }
    wp_recv (Xs v) as "HA". wp_pures. rewrite -subst_map_binder_insert.
    iApply ("He" with "[- HΓ1eq]").
    { iApply (ctx_ltyped_overwrite with "HA").
      destruct (decide (x = xc)) as [->|]; [done|].
      rewrite ctx_filter_ne_cons_ne //.
      iApply ctx_ltyped_cons_named. eauto with iFrame. }
    iIntros (w) "[$ HΓ]".
    iApply ctx_ltyped_app. iFrame "HΓ1eq". by iApply ctx_ltyped_anonymize'.
  Qed.

  Lemma ltyped_recv Γ (x : string) A S :
    Γ !! x = Some (chan (<??> TY A; S))%lty →
    Γ ⊨ recv x : A ⫤ ctx_overwrite x (chan S) Γ.
  Proof.
    iIntros (HΓx%ctx_lookup_perm) "!>". iIntros (vs) "HΓ /=".
    rewrite {1}HΓx /=.
    iDestruct (ctx_ltyped_cons_named with "HΓ") as (c Hvs) "[Hc HΓ]". rewrite Hvs.
    wp_recv (v) as "HA". iFrame "HA".
    iApply ctx_ltyped_cons_named. eauto with iFrame.
  Qed.

  Lemma ltyped_wait Γ (x : string) :
    Γ !! x = Some (chan END??)%lty →
    Γ ⊨ wait x : () ⫤ ctx_filter_ne x Γ.
  Proof.
    iIntros (HΓx%ctx_lookup_perm) "!>". iIntros (vs) "HΓ /=".
    rewrite {1}HΓx /=.
    iDestruct (ctx_ltyped_cons_named with "HΓ") as (c Hvs) "[Hc HΓ]". rewrite Hvs.
    wp_wait. by iFrame.
  Qed.

  Lemma ltyped_select Γ1 Γ2 (x : string) e t A S ASs :
    Γ2 !! x = Some (chan (lty_select ASs))%lty →
    ASs !! t = Some (A,S) →
    (Γ1 ⊨ e : A ⫤ Γ2) -∗
    Γ1 ⊨ send x (Sum t e) : () ⫤ ctx_overwrite x (chan S) Γ2.
  Proof.
    iIntros (HΓx%ctx_lookup_perm Ht); iIntros "#He !>" (vs) "HΓ /=".
    iApply ("He" with "HΓ"); iIntros (v) "[HA HΓ]". rewrite {2}HΓx /=.
    iDestruct (ctx_ltyped_cons_named with "HΓ") as (c Hvs) "[Hc HΓ]". rewrite Hvs.
    wp_send with "[HA]"; first by rewrite Ht /=.
    rewrite lookup_total_alt Ht /=. iSplitR; [done|].
    iApply ctx_ltyped_cons_named. eauto with iFrame.
  Qed.

  Lemma ltyped_branch Γ1 Γ2 ASs B (x : string) tes :
    Γ1 !! x = Some (chan (lty_branch ASs))%lty →
    ([∗ map] t ↦ AS ∈ ASs, ∃ e,
      ⌜ sum_branch t tes = Some e ⌝ ∧
      (ctx_overwrite x (chan AS.2) Γ1 ⊨ e : AS.1 ⊸ B ⫤ Γ2)) -∗
    Γ1 ⊨ MatchSum (recv x) tes : B ⫤ Γ2.
  Proof.
    iIntros (HΓx%ctx_lookup_perm) "#HAS !> %vs HΓ /=". rewrite {2}HΓx.
    iDestruct (ctx_ltyped_cons_named with "HΓ") as (c Hvs) "[Hc HΓ]". rewrite Hvs.
    wp_recv (t v) as "HA". rewrite lookup_total_alt.
    destruct (ASs !! t) as [[A S]|] eqn:Ht; simpl; [|done].
    iDestruct (big_sepM_lookup with "HAS") as (e He) "He"; first done. simpl.
    assert (TCEq (sum_branch t (prod_map id (subst_map vs) <$> tes))
                 (Some (subst_map vs e))).
    { apply TCEq_eq. revert e He. induction tes as [|[]];
        intros; repeat (case_decide || simplify_eq/=); eauto. }
    wp_pures. iApply ("He" with "[HΓ Hc]").
    { iApply ctx_ltyped_cons_named. eauto with iFrame. }
    iIntros (vret) "[HAB HΓ]". iApply ("HAB" with "HA"). eauto with iFrame.
  Qed.
End session_typing_rules.
