From dlfactris.lang Require Import metatheory.
From dlfactris.base_logic Require Export wp.
From dlfactris.base_logic Require Import cgraph.

Definition local_inv (σ : cfg) (ν : obj) : inEdges → aProp :=
  match ν with
  | Thread i => thread_inv (σ.1 !! i)
  | Chan l => heap_val_inv (σ.2 !! l)
  end.

Definition inv (σ : cfg) : siProp :=
  ginv (λ ν ins, aProp_at (local_inv σ ν ins)).

Lemma inv_unfold tid σ e :
  σ.1 !! tid = Some e →
  inv σ ⊣⊢ ∃ Σtid, inv' σ tid Σtid ∧ aProp_at (wp_prim e (λ _, emp%I)) Σtid.
Proof.
  intros He. iSplit.
  - iDestruct 1 as (g Hg) "#Hinv".
    iPoseProof ("Hinv" $! (Thread tid)) as "Hwp".
    rewrite /= He /=. iDestruct "Hwp" as (?) "Hwp".
    iExists _; iSplit; last done.
    rewrite inv'_unfold. iExists g; iSplit; first done.
    iIntros ([i|l]); [destruct (decide _) as [->|]|]; [|iApply "Hinv"..].
    eauto using lookup_lt_Some.
  - iDestruct 1 as (Σ) "[Hinv Hwp]". rewrite inv'_unfold.
    iDestruct "Hinv" as (g ?) "Hinv". iExists (g); iSplit; first done.
    iIntros (ν); iSpecialize ("Hinv" $! ν).
    destruct ν; [destruct (decide _) as [->|]|]; [|iApply "Hinv"..].
    rewrite /= He /= !aProp_at_sep_affinely_l !aProp_at_pure.
    iDestruct "Hinv" as ([]) "Hinv"; iSplit; first done.
    rewrite /aProp_at. by iRewrite -"Hinv".
Qed.

Lemma inv_initialization e :                                                     (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=f3656312 *)
  aProp_at (WP e {{ _, emp }}) ∅ ⊢ inv ([e],∅).
Proof.
  rewrite wp_wp_prim (inv_unfold 0) //.
  iIntros "Hwp". iExists ∅. iFrame "Hwp".
  rewrite inv'_unfold. iExists ∅. iSplit; [iPureIntro; apply empty_wf|].
  iIntros (ν). rewrite out_edges_empty in_labels_empty /=.
  destruct ν as [[|i]|l]; simpl.
  - auto.
  - rewrite aProp_at_affinely aProp_at_pure. auto.
  - rewrite lookup_empty /= aProp_at_affinely aProp_at_pure. auto.
Qed.

Lemma inv_preservation σ1 σ2 :                                                   (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=a6d9c0c5 *)
  step σ1 σ2 →
  inv σ1 ⊢ ▷ inv σ2.
Proof.
  iIntros (Hstep) "Hinv".
  destruct Hstep.
  assert (i < length es) by eauto using lookup_lt_Some.
  rewrite (inv_unfold i); eauto.
  rewrite (inv_unfold i); last first.
  { rewrite /= lookup_app_l ?insert_length //.
    rewrite list_lookup_insert //. }
  iDestruct "Hinv" as (Σ) "[Hinv Hwp]".
  rewrite wp_prim_unfold.
  erewrite prim_step_not_val; eauto.
  simpl. iDestruct "Hwp" as (Σ1) "#[Heq H]".
  iDestruct (excl_outEdges_injI with "Heq") as "HΣ".
  iMod ("H" with "[Hinv]") as "[_ H1]".
  { iNext. by iRewrite "HΣ". }
  iDestruct ("H1" with "[]") as (Σ') "[G1 G2]"; first eauto.
  iExists Σ'.
  iSplit; eauto.
  rewrite -insert_app_l //.
  by iApply inv'_tid_irrelevant.
Qed.

Definition active (σ : cfg) (o : obj) :=
  match o with
  | Thread i => match σ.1 !! i with
                | Some e => to_val e = None
                | None => False
                end
  | Chan l => is_Some (σ.2 !! l)
  end.

(* Waiting relation *)
Definition waiting (σ : cfg) (o1 o2 : obj) : Prop :=
  ∃ i l e, o1 = Thread i ∧ o2 = Chan l ∧ σ.1 !! i = Some e ∧ blocked e l σ.2.

Global Instance waiting_dec σ o1 o2 : Decision (waiting σ o1 o2).
Proof.
  refine
    match o1, o2 with
    | Thread i, Chan l =>
       match Some_dec (σ.1 !! i) with
       | inleft (e ↾ _) => cast_if (decide (blocked e l σ.2))
       | inright _ => right _
       end
    | _, _ => right _
    end; unfold waiting; naive_solver.
Defined.

Lemma inv_active_progress σ o :
  active σ o →
  inv σ ⊢ ▷ ⌜ ∃ σ', step σ σ' ⌝.
Proof.
  iIntros (H) "#Hinv_all".
  iPoseProof "Hinv_all" as (g) "[%Hg Hinv]".
  iInduction o as [] "IH" using (cgraph_ind' (λ o1 o2 _, waiting σ o1 o2) g Hg).
  iDestruct ("Hinv" $! o) as "Hx".
  destruct o; simpl.
  - unfold active in H.
    destruct (σ.1 !! n) eqn:Heq; try done. simpl.
    iDestruct "Hx" as (Hinl) "HΦ".
    rewrite wp_prim_unfold. rewrite H. simpl.
    iDestruct "HΦ" as (Σ) "[H1 H2]".
    iAssert (▷ inv' σ n Σ)%I as "Hinv'".
    { rewrite inv'_unfold /ginv.
      iExists g. iSplit; first done.
      iIntros (ν). destruct ν.
      - case_decide; subst.
        + iSplit; first by eauto using lookup_lt_Some. by iApply excl_outEdges_injI.
        + iApply "Hinv".
      - iApply "Hinv". }
    destruct σ as [es h].
    iMod ("H2" with "Hinv'") as ([Hred|[l Hblocked]]) "_".
    { eauto using reducible_step. }
    unfold blocked in *.
    assert (Hblocked' := Hblocked).
    destruct Hblocked' as (Φ & (k & e' & Hctx & -> & Hblocked') & HΣ).
    iAssert (▷ ∃ Φ',
      ⌜ out_edges g (Thread n) !! Chan l = Some (inr (MiniProt ARecv Φ')) ⌝)%I as ">%HΣ'".
    { iDestruct (excl_outEdges_injI with "H1") as "{H1} H1". iNext.
      rewrite gmap_equivI. iSpecialize ("H1" $! (Chan l)).
      rewrite option_equivI HΣ.
      case _: (_ !! Chan l)=> [[?|[a' Φ']]|]; rewrite ?sum_equivI //=.
      iExists Φ'. rewrite miniprot_equivI /=. by iDestruct "H1" as "[<- _]". }
    destruct HΣ' as [Φ' HΣ'].
    iApply ("IH" $! (Chan l) (inr (MiniProt ARecv Φ'))).
    + by rewrite HΣ'.
    + unfold waiting. simpl.
      iExists _, _, _. iSplit; first done.
      iSplit; first done. iSplit; first done.
      iPureIntro. unfold blocked. exists k,e'. done.
    + unfold active. simpl in *.
      destruct Hblocked'; eauto.
  - unfold active in H.
    destruct H as [[[v|]|w] Hσl]; rewrite Hσl /=.
    + (* Channel has a value *)
      iDestruct "Hx" as (Φ) "[Heq HΦ]".
      rewrite aProp_at_affinely bi.and_elim_r aProp_at_internal_eq.
      iDestruct (in_labels_out_edges1 with "Heq") as (v1) "Hv1".
      destruct (out_edges g v1 !! Chan l) eqn:Heq; last first.
      { iDestruct "Hv1" as %Hv1. inversion Hv1. }
      iApply ("IH1" with "[] [] [>]").
      * erewrite Heq. done.
      * destruct (decide (waiting σ v1 (Chan l))) as [Hw|Hw]; eauto.
        destruct Hw as (n & l' & e' & -> & [= ->] & Hn & Hbl).
        unfold blocked in Hbl.
        destruct Hbl as (k & e'' & Hctx & -> & Hbl').
        destruct Hbl'. simplify_eq.
      * unfold active.
        iSpecialize ("Hinv" $! v1).
        { destruct v1; simpl.
          - destruct (σ.1 !! n) eqn:Heq'; simpl.
            + iDestruct "Hinv" as (_) "Hinv".
              rewrite wp_prim_unfold.
              destruct (to_val e); eauto.
              rewrite aProp_at_except_0 aProp_at_emp. iMod "Hinv" as %HH.
              rewrite map_empty_equiv_eq in HH.
              rewrite HH lookup_empty // in Heq.
            + iDestruct "Hinv" as (HH) "Hinv".
              rewrite HH lookup_empty // in Heq.
          - destruct (σ.2 !! l0); simpl; eauto.
            iDestruct "Hinv" as (HH) "Hinv".
            rewrite HH lookup_empty // in Heq. }
    + (* Channel has no value *)
      iDestruct "Hx" as (Φ) "[Hout Heq]".
      rewrite in_labels_out_edges2.
      iDestruct "Heq" as (ν1 ν2 Hν12) "[H1 H2]".
      rewrite !aProp_at_internal_eq option_equivI.
      destruct (out_edges g ν1 !! Chan l) eqn:Heq; last done.
      iAssert ⌜ active σ ν1 ⌝%I with "[>]" as %Hactive.
      { iSpecialize ("Hinv" $! ν1). destruct ν1 as [i|l']; simpl.
        - destruct (σ.1 !! i) eqn:Heq'; simpl.
          + iDestruct "Hinv" as (_) "Hinv".
            rewrite wp_prim_unfold.
            destruct (to_val e); last done.
            rewrite aProp_at_except_0. iMod "Hinv" as %HH.
            rewrite HH lookup_empty // in Heq.
          + iDestruct "Hinv" as (HH) "Hinv".
            rewrite HH lookup_empty // in Heq.
        - destruct (σ.2 !! l'); simpl; eauto.
          iDestruct "Hinv" as (HH) "Hinv".
          rewrite HH lookup_empty // in Heq. }
      destruct (decide (waiting σ ν1 (Chan l))) as [Hw|Hw]; last first.
      { iApply ("IH1" $! ν1); eauto. by rewrite Heq. }
      destruct Hw as (n & l' & e' & -> & [= ->] & Hn & Hbl).
      destruct Hbl as (k & e'' & Hctx & -> & Hbl').
      destruct Hbl'; simplify_eq.
      iDestruct ("Hinv" $! (Thread n)) as "Hwp".
      rewrite /= Hn /=.
      iDestruct "Hwp" as "[%Hinl Hwp]".
      rewrite wp_prim_unfold.
      rewrite to_val_ctx_None //=.
      iDestruct "Hwp" as (Σ) "[Hw1 Hw2]".
      iAssert (▷ inv' (σ.1, σ.2) n Σ)%I as "Hinv'".
      { rewrite inv'_unfold /ginv.
        iExists g. iSplit; first done.
        iIntros (ν). destruct ν.
        - case_decide; subst.
          + iSplit; first by eauto using lookup_lt_Some. by iApply excl_outEdges_injI.
          + iApply "Hinv".
        - iApply "Hinv". }
      iMod ("Hw2" with "Hinv'") as "[%Hww Hww2]".
      unfold reducible_or_blocked_own in Hww.
      destruct Hww as [Hww|Hww].
      { eauto using reducible_step. }
      destruct Hww as (l' & Φ' & Hblocked & HΣ).
      eapply blocked_chan_unique in Hblocked as <-; eauto.
      rewrite excl_outEdges_injI. iNext.
      rewrite !gmap_equivI. iSpecialize ("Hw1" $! (Chan l)).
      rewrite HΣ Heq.
      rewrite !option_equivI.
      iRewrite "H1" in "Hw1".
      rewrite !sum_equivI !miniprot_equivI /=.
      iDestruct "Hw1" as "[%QED _]". simplify_eq.
    + (* References *)
      iDestruct "Hx" as "[%Houtchan H2]".
      rewrite aProp_at_internal_eq.
      iDestruct (in_labels_out_edges1 with "H2") as (v1) "Hv1".
      rewrite option_equivI.
      destruct (out_edges g v1 !! Chan l) eqn:Heq; last done.
      iAssert ⌜ active σ v1 ⌝%I with "[>]" as %Hactive.
      { iSpecialize ("Hinv" $! v1). destruct v1 as [i|l']; simpl.
        - destruct (σ.1 !! i) eqn:Heq'; simpl.
          + iDestruct "Hinv" as (_) "Hinv".
            rewrite wp_prim_unfold.
            destruct (to_val e); last done.
            rewrite aProp_at_except_0. iMod "Hinv" as %HH.
            rewrite HH lookup_empty // in Heq.
          + iDestruct "Hinv" as (HH) "Hinv".
            rewrite HH lookup_empty // in Heq.
        - destruct (σ.2 !! l'); simpl; eauto.
          iDestruct "Hinv" as (HH) "Hinv".
          rewrite HH lookup_empty // in Heq. }
      destruct (decide (waiting σ v1 (Chan l))) as [Hw|Hw]; last first.
      { iApply ("IH1" $! v1); try done. by rewrite Heq. }
      destruct Hw as (n & l' & e' & -> & [= ->] & Hn & Hbl).
      destruct Hbl as (k & e'' & Hctx & -> & Hbl').
      destruct Hbl'. simplify_eq.
Qed.

Lemma final_or_active σ :
  (Forall (λ e', is_Some (to_val e')) σ.1 ∧ σ.2 = ∅) ∨ ∃ o, active σ o.
Proof.
  destruct (decide (Forall (λ e', is_Some (to_val e')) σ.1 ∧ σ.2 = ∅))
    as [|[Hforall|Hσ]%not_and_r]; simpl.
  - by left.
  - right. apply (not_Forall_Exists _) in Hforall
      as (e & He & ?%eq_None_not_Some)%Exists_exists; simpl in *.
    apply elem_of_list_lookup in He as [l Hl].
    exists (Thread l). by rewrite /= Hl.
  - right. apply map_choose in Hσ as (l&o&Hl). exists (Chan l); naive_solver.
Qed.

Definition global_progress (σ : cfg) :=
  (Forall (λ e', is_Some (to_val e')) σ.1 ∧ σ.2 = ∅) ∨ ∃ σ', step σ σ'.

Definition all_progress_or_blocked (σ : cfg) :=
  Forall (λ e', is_Some (to_val e') ∨ reducible_or_blocked e' σ.2) σ.1.

Lemma inv_global_progress σ :                                                    (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=8ac7bdcb *)
  inv σ ⊢ ▷ ⌜ global_progress σ ⌝.
Proof.
  destruct (final_or_active σ) as [?|[o ?]].
  - iIntros "Hinv !> !%". by left.
  - iIntros "Hinv". iRight. by iApply inv_active_progress.
Qed.

Lemma inv_safety σ :                                                             (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=f8ccbcb5 *)
  inv σ ⊢ ▷ ⌜ all_progress_or_blocked σ ⌝.
Proof.
  iIntros "Hinv". rewrite /all_progress_or_blocked Forall_forall.
  iIntros (e [i Hi]%elem_of_list_lookup).
  iDestruct (inv_unfold with "Hinv") as (Σi) "[Hinv Hwp]"; first done.
  rewrite wp_prim_unfold. destruct (to_val e) eqn:?; simpl; first by eauto.
  iDestruct "Hwp" as (Σi') "[#HΣ Hwp]".
  iDestruct ("Hwp" $! i σ.1 σ.2 with "[Hinv]") as "[>%Hred _]".
  { rewrite excl_outEdges_injI. iNext. iRewrite "HΣ". by destruct σ. }
  rewrite /reducible_or_blocked; destruct Hred as [?|(?&?&?&?)]; eauto.
Qed.

Lemma adequacy e σ :                                                             (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=a026d91e *)
  (⊢ WP e {{ _, emp }}) →
  steps ([e],∅) σ →
  global_progress σ (* deadlock and leak freedom *) ∧
  all_progress_or_blocked σ (* conventional safety *).
Proof.
  intros Hwp Hsteps. rewrite aProp_emp_valid inv_initialization in Hwp.
  assert (⊢ inv σ).
  { induction Hsteps as [σ|σ1 σ2 σ3 Hstep Hsteps IH]; [done|].
    apply IH, later_soundness. by rewrite -inv_preservation. }
  apply (pure_soundness (PROP:=siProp)), later_soundness. iSplit.
  - by iApply inv_global_progress.
  - by iApply inv_safety.
Qed.
