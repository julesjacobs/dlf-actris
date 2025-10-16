From iris.algebra Require Export gmap.
From iris.algebra Require Import cofe_solver excl.
From dlfactris.lang Require Export lang.
From dlfactris.base_logic Require Export linpred miniprot.

Inductive obj := Thread : nat → obj | Chan : loc → obj.

Global Instance object_eqdecision : EqDecision obj.
Proof. solve_decision. Defined.
Global Instance object_countable : Countable obj.
Proof.
  refine (inj_countable' (λ l, match l with
  | Thread n => inl n
  | Chan n => inr n
  end) (λ l, match l with
  | inl n => Thread n
  | inr n => Chan n
  end) _); by intros [].
Qed.

(** TODO in Iris: Drop [OfeDiscrete] from [CmraDiscrete]. The valid of [excl A]
is always discrete, regardless of [A]. This makes it much easier to move stuff
to the Coq context. *)

(** * Solution of the recursive domain equation *)
(** We first declare a module type and then an instance of it so as to seal all of
the construction, this way we are sure we do not use any properties of the
construction, and also avoid Coq from blindly unfolding it. *)
Module Type aProp_solution_sig.
  Parameter aPrePropO : ofe.
  Global Declare Instance aPreProp_cofe : Cofe aPrePropO.

  Definition aResUR : ucmra := gmap obj (excl (val + later (miniprot val aPrePropO))).
  Notation aProp := (linPred aResUR).
  Notation aPropO := (linPredO aResUR).
  Notation aPropI := (linPredI aResUR).

  Parameter aProp_unfold : aPropO -n> aPrePropO.
  Parameter aProp_fold : aPrePropO -n> aPropO.
  Parameter aProp_fold_unfold : ∀ P : aProp, aProp_fold (aProp_unfold P) ≡ P.
  Parameter aProp_unfold_fold: ∀ P : aPrePropO, aProp_unfold (aProp_fold P) ≡ P.
End aProp_solution_sig.

Module Export aProp_solution : aProp_solution_sig.                               (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=0925cda4 *)
  Import cofe_solver.

  Definition aResURF :=
    gmapURF obj (exclRF (sumOF (constOF val) (laterOF (miniprotOF val idOF)))).
  Definition aProp_result : solution (linPredOF aResURF) := solver.result _.
  Definition aPrePropO : ofe := aProp_result.
  Global Instance aPreProp_cofe : Cofe aPrePropO := _.

  Definition aResUR : ucmra := gmap obj (excl (val + later (miniprot val aPrePropO))).
  Notation aProp := (linPred aResUR).
  Notation aPropO := (linPredO aResUR).
  Notation aPropI := (linPredI aResUR).

  Definition aProp_unfold : aPropO -n> aPrePropO := ofe_iso_1 (aProp_result).
  Definition aProp_fold : aPrePropO -n> aPropO := ofe_iso_2 (aProp_result).
  Lemma aProp_fold_unfold (P : aProp) : aProp_fold (aProp_unfold P) ≡ P.
  Proof. apply ofe_iso_21. Qed.
  Lemma aProp_unfold_fold (P : aPrePropO) : aProp_unfold (aProp_fold P) ≡ P.
  Proof. apply ofe_iso_12. Qed.
End aProp_solution.

Notation aMiniProt := (miniprot val aProp).
Definition aEdge : Type := val + aMiniProt.
Definition outEdges := gmap obj aEdge.

Definition excl_outEdges (Σ : outEdges) : aResUR :=
  Excl ∘ (sum_map (@id val) (Next ∘ miniprot_map aProp_unfold)) <$> Σ.
Global Typeclasses Opaque excl_outEdges.
Global Instance: Params (@excl_outEdges) 0 := {}.

Definition aProp_own (Σ : outEdges) : aProp :=                                   (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=db08d7fe *)
  linPred_own (excl_outEdges Σ).
Global Typeclasses Opaque aProp_own.
Global Instance: Params (@aProp_own) 0 := {}.

Definition own_chan_def (l : loc) (p : aMiniProt) : aProp :=                     (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=7298b435 *)
  aProp_own {[ Chan l := inr p ]}.
Local Definition own_chan_aux : seal (@own_chan_def). Proof. by eexists. Qed.
Definition own_chan := own_chan_aux.(unseal).
Local Definition own_chan_unseal : own_chan = _ := own_chan_aux.(seal_eq).
Global Instance: Params (@own_chan) 1 := {}.

Definition own_ref_def (l : loc) (v : val) : aProp :=
  aProp_own {[ Chan l := inl v ]}.
Local Definition own_ref_aux : seal (@own_ref_def). Proof. by eexists. Qed.
Definition own_ref := own_ref_aux.(unseal).
Local Definition own_ref_unseal : own_ref = _ := own_ref_aux.(seal_eq).
Notation "l ↦ v" := (own_ref l v) (at level 20) : bi_scope.

Definition aProp_at (P : aProp) (Σ : outEdges) : siProp :=
  linPred_at P (excl_outEdges Σ).
Global Typeclasses Opaque aProp_at.
Global Instance: Params (@aProp_at) 0 := {}.

Program Definition AProp (Φ : outEdges → siProp) : aProp :=
  {| linPred_at x := (∃ Σ, excl_outEdges Σ ≡ x ∧ Φ Σ)%I |}.
Next Obligation. intros Φ n x1 x2 Hx. f_equiv=> Σ. by rewrite Hx. Qed.

Section aProp.
  Implicit Types Σ : outEdges.
  Implicit Types P Q : aProp.

  Global Instance excl_outEdges_ne : NonExpansive excl_outEdges.
  Proof. solve_proper. Qed.
  Global Instance excl_outEdges_proper : Proper ((≡) ==> (≡)) excl_outEdges.
  Proof. apply: ne_proper. Qed.

  Lemma excl_outEdges_valid Σ : ✓ (excl_outEdges Σ).
  Proof. intros l. rewrite /excl_outEdges lookup_fmap. by destruct (_ !! _). Qed.
  Lemma excl_outEdges_union Σ1 Σ2 :
    Σ1 ##ₘ Σ2 → excl_outEdges (Σ1 ∪ Σ2) = excl_outEdges Σ1 ⋅ excl_outEdges Σ2.
  Proof.
    intros. rewrite gmap_op_union; last by apply map_disjoint_fmap.
    by rewrite -map_fmap_union.
  Qed.
  Lemma excl_outEdges_op_validI `{Sbi PROP} Σ1 Σ2 :
    ✓ (excl_outEdges Σ1 ⋅ excl_outEdges Σ2) ⊢@{PROP} ⌜ Σ1 ##ₘ Σ2 ⌝.
  Proof.
    iIntros "Hvalid". by iDestruct (internal_cmra_valid_elim with "Hvalid")
      as %Hdisj%gmap_op_valid0_disjoint%map_disjoint_fmap.
  Qed.
  Lemma excl_outEdges_uninj `{Sbi PROP} x :
    ✓ x ⊢@{PROP} ∃ Σ, x ≡ excl_outEdges Σ.
  Proof.
    change (cmra_car aResUR) with
      (gmap obj (excl (val + later (miniprotO val aPrePropO)))) in x.
    iIntros "#Hvalid". rewrite !gmap_validI.
    iInduction x as [|l ehv x Hx] "IH" using map_ind.
    { by iExists ∅. }
    iDestruct ("IH" with "[]") as (Σ) "Hx".
    { iIntros "!> %l'". destruct (decide (l = l')) as [->|].
      - by rewrite option_validI Hx.
      - iSpecialize ("Hvalid" $! l'). by rewrite lookup_insert_ne. }
    destruct ehv as [[v|p]|].
    - iExists (<[l:=inl v]> Σ). iRewrite "Hx".
       by rewrite /excl_outEdges fmap_insert.
    - iClear "Hvalid". destruct (Next_uninj p) as [p' Hp].
      iExists (<[l:=inr (miniprot_map aProp_fold p')]> Σ).
      rewrite Hp. iRewrite "Hx".
      rewrite /excl_outEdges fmap_insert /= -miniprot_map_compose.
      rewrite (miniprot_map_ext _ cid); last apply aProp_unfold_fold.
      by rewrite miniprot_map_id.
    - iSpecialize ("Hvalid" $! l). rewrite lookup_insert_eq.
      by rewrite option_validI excl_validI.
  Qed.
  Lemma excl_outEdges_injI `{!Sbi PROP} (Σ1 Σ2 : outEdges) :
    excl_outEdges Σ1 ≡ excl_outEdges Σ2 ⊢@{PROP} ▷ (Σ1 ≡ Σ2).
  Proof.
    rewrite /excl_outEdges /= !gmap_equivI. iIntros "H" (i).
    iSpecialize ("H" $! i). rewrite !lookup_fmap !option_equivI.
    destruct (_ !! i) as [hv1|], (_ !! i) as [hv2|]; simpl; [|done..].
    rewrite excl_equivI sum_equivI.
    destruct hv1 as [v1|p1], hv2 as [v2|p2]=> //=.
    { by iRewrite "H". }
    iModIntro. iDestruct (f_equivI (miniprot_map aProp_fold) with "H") as "H".
    rewrite -!miniprot_map_compose.
    rewrite !(miniprot_map_ext (_ ◎ _) cid); [|apply aProp_fold_unfold..].
    rewrite !miniprot_map_id. by iRewrite "H".
  Qed.

  Global Instance aProp_own_ne : NonExpansive aProp_own.
  Proof. solve_proper. Qed.
  Global Instance aProp_own_proper : Proper ((≡) ==> (≡)) aProp_own.
  Proof. apply: ne_proper. Qed.

  Global Instance own_chan_contractive l : Contractive (own_chan l).
  Proof.
    intros n p1 p2 Hp.
    rewrite own_chan_unseal /own_chan_def /aProp_own /excl_outEdges.
    rewrite !map_fmap_singleton /=. by repeat (f_contractive || f_equiv).
  Qed.
  Global Instance own_chan_ne l : NonExpansive (own_chan l).
  Proof. rewrite own_chan_unseal. solve_proper. Qed.
  Global Instance own_chan_proper l : Proper ((≡) ==> (≡)) (own_chan l).
  Proof. apply: ne_proper. Qed.

  Global Instance aProp_at_ne : NonExpansive2 aProp_at.
  Proof.
    apply (ne_2_internal_eq (PROP:=siProp)). iIntros (P1 P2 Σ1 Σ2) "#[HP He]".
    rewrite /aProp_at. iRewrite "He". iApply plainly.prop_ext; iIntros "!>".
    rewrite linPred_equivI. iApply "HP". iPureIntro. apply excl_outEdges_valid.
  Qed.
  Global Instance aProp_at_proper : Proper ((≡) ==> (≡) ==> (≡)) aProp_at.
  Proof. apply: ne_proper_2. Qed.
  Global Instance aProp_at_mono : Proper ((⊢) ==> (≡) ==> (⊢)) aProp_at.
  Proof.
    intros P1 P2. rewrite /aProp_at linPred_entails. iIntros (HP x1 x2 ->).
    iApply HP. iPureIntro. apply excl_outEdges_valid.
  Qed.
  Global Instance aProp_at_flip_mono :
    Proper (flip (⊢) ==> (≡) ==> flip (⊢)) aProp_at.
  Proof. intros P1 P2 ? x1 x2 ?. by apply aProp_at_mono. Qed.

  Lemma aProp_equivI P Q : P ≡ Q ⊣⊢ ∀ Σ, aProp_at P Σ ↔ aProp_at Q Σ.
  Proof.
    rewrite /aProp_at linPred_equivI. iSplit.
    - iIntros "H" (Σ). iApply "H". iPureIntro. apply excl_outEdges_valid.
    - iIntros "H" (x) "Hx". iDestruct (excl_outEdges_uninj with "Hx") as (Σ) "Hx".
      iRewrite "Hx". iApply "H".
  Qed.
  Global Instance AProp_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) AProp.
  Proof.
    apply (ne_internal_eq (PROP:=siProp) (A:=_ -d> _)). iIntros (P1 P2) "HP".
    rewrite discrete_fun_equivI aProp_equivI /=; iIntros (Σ).
    iSplit; iIntros "(%Σ' & ? & ?)"; iExists Σ';
      [iRewrite -("HP" $! Σ')|iRewrite ("HP" $! Σ')]; auto.
  Qed.
  Lemma aProp_at_pure Σ (φ : Prop) : aProp_at ⌜φ⌝ Σ ⊣⊢ ⌜φ⌝.
  Proof. by rewrite /aProp_at linPred_at_pure. Qed.
  Lemma aProp_at_emp Σ : aProp_at emp Σ ⊣⊢ Σ ≡ ∅.
  Proof.
    rewrite /aProp_at linPred_at_emp /= !discrete_eq !map_empty_equiv_eq.
    apply bi.pure_proper; split; [|by intros ->]. apply fmap_empty_inv.
  Qed.
  Lemma aProp_at_and Σ P Q : aProp_at (P ∧ Q) Σ ⊣⊢ aProp_at P Σ ∧ aProp_at Q Σ.
  Proof. by rewrite /aProp_at linPred_at_and. Qed.
  Lemma aProp_at_or Σ P Q : aProp_at (P ∨ Q) Σ ⊣⊢ aProp_at P Σ ∨ aProp_at Q Σ.
  Proof. by rewrite /aProp_at linPred_at_or. Qed.
  Lemma aProp_at_impl Σ P Q : aProp_at (P → Q) Σ ⊣⊢ (aProp_at P Σ → aProp_at Q Σ).
  Proof. by rewrite /aProp_at linPred_at_impl. Qed.
  Lemma aProp_at_forall {A} Σ (Φ : A → aProp) :
    aProp_at (∀ a, Φ a) Σ ⊣⊢ ∀ a, aProp_at (Φ a) Σ.
  Proof. by rewrite /aProp_at linPred_at_forall. Qed.
  Lemma aProp_at_exist {A} Σ (Φ : A → aProp) :
    aProp_at (∃ a, Φ a) Σ ⊣⊢ ∃ a, aProp_at (Φ a) Σ.
  Proof. by rewrite /aProp_at linPred_at_exist. Qed.
  Lemma aProp_at_sep Σ P Q :
    aProp_at (P ∗ Q) Σ ⊣⊢ ∃ Σ1 Σ2,
      ⌜ Σ = Σ1 ∪ Σ2 ⌝ ∧ ⌜ Σ1 ##ₘ Σ2 ⌝ ∧ aProp_at P Σ1 ∧ aProp_at Q Σ2.
  Proof.
    rewrite /aProp_at linPred_at_sep. iSplit.
    - iIntros "(%x1 & %x2 & #Hx & HP & HQ)".
      iAssert (✓ (x1 ⋅ x2))%I as "Hvalid".
      { iRewrite -"Hx". iPureIntro. apply excl_outEdges_valid. }
      iDestruct (internal_cmra_valid_elim with "Hvalid")
        as %Hdisj%gmap_op_valid0_disjoint.
      iClear "Hvalid". rewrite gmap_op_union //.
      iExists (filter (λ '(l,_), l ∈ dom x1) Σ), (filter (λ '(l,_), l ∉ dom x1) Σ).
      iSplit; [by rewrite map_filter_union_complement|].
      iSplit; [iPureIntro; apply map_disjoint_filter_complement|].
      iAssert (excl_outEdges (filter (λ '(l, _), l ∈ dom x1) Σ) ≡ x1)%I as "HΣ1".
      { rewrite /excl_outEdges !gmap_equivI. iIntros (l).
        specialize (Hdisj l). iSpecialize ("Hx" $! l).
        rewrite !lookup_fmap lookup_union map_lookup_filter !option_equivI.
        case: (Σ !! l)=> [p|] /=; case Hp1 : (x1 !! l)=> [p1|] //=.
        * rewrite union_Some_l option_guard_True ?elem_of_dom; eauto.
        * rewrite option_guard_False ?not_elem_of_dom //.
        * by rewrite union_Some_l. }
      iAssert (excl_outEdges (filter (λ '(l, _), l ∉ dom x1) Σ) ≡ x2)%I as "HΣ2".
      { rewrite map_union_comm //. rewrite /excl_outEdges !gmap_equivI. iIntros (l).
        specialize (Hdisj l). iSpecialize ("Hx" $! l).
        rewrite !lookup_fmap lookup_union map_lookup_filter !option_equivI.
        case: (Σ !! l)=> [p|] /=; case Hp2 : (x2 !! l)=> [p2|] //=.
        * assert (¬ is_Some (x1 !! l)).
          { intros [p1 Hp1]. by rewrite Hp1 Hp2 in Hdisj. }
          by rewrite union_Some_l option_guard_True ?elem_of_dom.
        * case Hp1 : (x1 !! l)=> [p1|] //=.
          assert (x1 !! l ≠ None).
          { intros Hp1'. by rewrite Hp1' in Hp1. }
          by rewrite option_guard_False ?not_elem_of_dom.
        * by rewrite union_Some_l. }
      iRewrite "HΣ1"; iRewrite "HΣ2"; auto.
    - iIntros "(%Σ1 & %Σ2 & -> & % & HP & HQ)". iExists _, _; iSplit; [|by iSplit].
      by rewrite excl_outEdges_union.
  Qed.
  Lemma aProp_at_wand Σ P Q :
    aProp_at (P -∗ Q) Σ ⊣⊢ ∀ Σ', ⌜ Σ ##ₘ Σ' ⌝ → aProp_at P Σ' → aProp_at Q (Σ ∪ Σ').
  Proof.
    rewrite /aProp_at linPred_at_wand. iSplit.
    - iIntros "#H %Σ' %Hdisj #HP". rewrite excl_outEdges_union //.
      iApply ("H" with "[] HP"). rewrite -excl_outEdges_union //.
      iPureIntro. apply excl_outEdges_valid.
    - iIntros "#H %x #Hvalid #HP".
      iDestruct (excl_outEdges_uninj x with "[]") as (Σ') "Hx".
      { by iApply cmra_validI_op_r. }
      iRewrite "Hx". iRewrite "Hx" in "HP". iRewrite "Hx" in "Hvalid". iClear "Hx".
      iDestruct (excl_outEdges_op_validI with "Hvalid") as %?.
      rewrite -excl_outEdges_union //. by iApply "H".
  Qed.
  Lemma aProp_at_persistently Σ P : aProp_at (<pers> P) Σ ⊣⊢ aProp_at P ∅.
  Proof. by rewrite /aProp_at linPred_at_persistently. Qed.
  Lemma aProp_at_later Σ P : aProp_at (▷ P) Σ ⊣⊢ ▷ aProp_at P Σ.
  Proof. by rewrite /aProp_at linPred_at_later. Qed.
  Lemma aProp_at_laterN Σ n P : aProp_at (▷^n P) Σ ⊣⊢ ▷^n aProp_at P Σ.
  Proof. by rewrite /aProp_at linPred_at_laterN. Qed.
  Lemma aProp_at_si_pure Σ Pi : aProp_at (<si_pure> Pi) Σ ⊣⊢ Pi.
  Proof. by rewrite /aProp_at linPred_at_si_pure. Qed.
  Lemma aProp_at_internal_eq {A : ofe} Σ (a1 a2 : A) :
    aProp_at (a1 ≡ a2) Σ ⊣⊢ a1 ≡ a2.
  Proof. by rewrite /aProp_at linPred_at_internal_eq. Qed.
  Lemma aProp_at_si_emp_valid P : <si_emp_valid> P ⊣⊢ aProp_at P ∅.
  Proof. by rewrite /aProp_at linPred_at_si_emp_valid. Qed.
  Lemma aProp_at_own Σ Σ' :
    aProp_at (aProp_own Σ') Σ ⊣⊢ excl_outEdges Σ ≡ excl_outEdges Σ'.
  Proof. by rewrite /aProp_at linPred_at_own. Qed.

  Lemma aProp_at_own_chan Σ l p :
    aProp_at (own_chan l p) Σ ⊣⊢ ∃ p', ⌜ Σ = {[ Chan l := inr p' ]} ⌝ ∧ ▷ (p' ≡ p).
  Proof.
    rewrite own_chan_unseal aProp_at_own. iSplit.
    - iIntros "#H". rewrite gmap_equivI. iPoseProof ("H" $! (Chan l)) as "#Hl".
      rewrite /excl_outEdges lookup_fmap map_fmap_singleton lookup_singleton_eq /=.
      rewrite option_equivI.
      destruct (_ !! Chan l) as [[v|p']|] eqn:?;
        rewrite /= ?excl_equivI ?sum_equivI //.
      iExists p'. rewrite later_equivI.
      iAssert ⌜ ∀ l', l' ≠ Chan l → Σ !! l' = None ⌝%I as %Hl'.
      { iIntros (l' ?). iSpecialize ("H" $! l').
        rewrite lookup_fmap lookup_singleton_ne // option_equivI.
        by destruct (_ !! l'). }
      iSplit.
      + iPureIntro. apply map_eq=> l'. destruct (decide (Chan l = l')) as [<-|].
        * by rewrite lookup_singleton_eq.
        * rewrite lookup_singleton_ne //. auto.
      + iNext. iDestruct (f_equivI (miniprot_map aProp_fold) with "Hl") as "Hl'".
        rewrite -!miniprot_map_compose.
        rewrite !(miniprot_map_ext (_ ◎ _) cid); [|apply aProp_fold_unfold..].
        by rewrite !miniprot_map_id.
    - iIntros "(%p'&->&#Hp)". rewrite /excl_outEdges !map_fmap_singleton.
      iApply (f_equivI (singletonM (Chan l))). iApply (f_equivI Excl); simpl.
      iApply f_equivI. iNext. by iRewrite "Hp".
  Qed.
  Lemma aProp_at_sep_own_chan Σ l p Q :
    aProp_at (own_chan l p ∗ Q) Σ ⊣⊢ ∃ p',
      ⌜ Σ !! Chan l = Some (inr p') ⌝ ∧ ▷ (p' ≡ p) ∧ aProp_at Q (delete (Chan l) Σ).
  Proof.
    rewrite aProp_at_sep. iSplit.
    - iIntros "(%Σ1 & %Σ2 & -> & %Hdisj & Hp & HQ)".
      iDestruct (aProp_at_own_chan with "Hp") as (p' ->) "Hp'".
      rewrite map_disjoint_singleton_l in Hdisj.
      iExists p'. rewrite lookup_union_l // lookup_singleton_eq.
      rewrite delete_union delete_singleton_eq left_id_L delete_id //. eauto.
    - iIntros "(%p' & %Hl & Hp' & HQ)".
      iExists {[ Chan l := inr p' ]}, (delete (Chan l) Σ). iSplit.
      { iPureIntro. by rewrite -insert_empty union_insert_delete // left_id_L. }
      iSplit.
      { iPureIntro. apply map_disjoint_singleton_l. by rewrite lookup_delete_eq. }
      iSplit; [|done]. iApply aProp_at_own_chan; eauto.
  Qed.

  Lemma aProp_at_own_ref Σ l v :
    aProp_at (l ↦ v) Σ ⊣⊢ ⌜ Σ = {[ Chan l := inl v ]} ⌝.
  Proof.
    rewrite own_ref_unseal aProp_at_own. iSplit.
    - iIntros "#H". rewrite gmap_equivI. iPoseProof ("H" $! (Chan l)) as "#Hl".
      rewrite /excl_outEdges lookup_fmap map_fmap_singleton lookup_singleton_eq /=.
      destruct (_ !! Chan l) as [[v'|p']|] eqn:?;
        rewrite /= ?option_equivI ?excl_equivI ?sum_equivI //.
      iDestruct "Hl" as %->%leibniz_equiv.
      iAssert ⌜ ∀ l', l' ≠ Chan l → Σ !! l' = None ⌝%I as %Hl'.
      { iIntros (l' ?). iSpecialize ("H" $! l').
        rewrite lookup_fmap lookup_singleton_ne // option_equivI.
        by destruct (_ !! l'). }
      iPureIntro. apply map_eq=> l'. destruct (decide (Chan l = l')) as [<-|].
      + by rewrite lookup_singleton_eq.
      + rewrite lookup_singleton_ne //. auto.
    - iIntros "->". rewrite /excl_outEdges !map_fmap_singleton.
      by iApply (f_equivI (singletonM (Chan l))).
  Qed.
  Lemma aProp_at_sep_own_ref Σ l v Q :
    aProp_at (l ↦ v ∗ Q) Σ ⊣⊢
      ⌜ Σ !! Chan l = Some (inl v) ⌝ ∧ aProp_at Q (delete (Chan l) Σ).
  Proof.
    rewrite aProp_at_sep. iSplit.
    - iIntros "(%Σ1 & %Σ2 & -> & %Hdisj & Hp & HQ)".
      iDestruct (aProp_at_own_ref with "Hp") as %->.
      rewrite map_disjoint_singleton_l in Hdisj.
      rewrite lookup_union_l // lookup_singleton_eq.
      rewrite delete_union delete_singleton_eq left_id_L delete_id //. eauto.
    - iIntros "[%HΣl HQ]".
      iExists {[ Chan l := inl v ]}, (delete (Chan l) Σ). iSplit.
      { iPureIntro. by rewrite -insert_empty union_insert_delete // left_id_L. }
      iSplit.
      { iPureIntro. apply map_disjoint_singleton_l. by rewrite lookup_delete_eq. }
      iSplit; [|done]. iApply aProp_at_own_ref; eauto.
  Qed.
  Global Instance own_ref_timeless l v : Timeless (l ↦ v).
  Proof.
    rewrite own_ref_unseal /own_ref_def /aProp_own /excl_outEdges.
    rewrite map_fmap_singleton /=. apply _.
  Qed.

  Lemma aProp_entails P Q : (P ⊢ Q) ↔ ∀ Σ, aProp_at P Σ ⊢ aProp_at Q Σ.
  Proof.
    rewrite /aProp_at linPred_entails. split.
    - iIntros (HPQ e). iApply HPQ. iPureIntro. apply excl_outEdges_valid.
    - iIntros (HPQ x) "#Hvalid".
      iDestruct (excl_outEdges_uninj x with "Hvalid") as (e) "Hx".
      iRewrite "Hx". iApply HPQ.
  Qed.
  Lemma aProp_equiv P Q : (P ⊣⊢ Q) ↔ ∀ Σ, aProp_at P Σ ⊣⊢ aProp_at Q Σ.
  Proof.
    setoid_rewrite bi.equiv_entails. rewrite !aProp_entails. naive_solver.
  Qed.
  Lemma aProp_emp_valid P : (⊢ P) ↔ ⊢ aProp_at P ∅.
  Proof. by rewrite linPred_emp_valid. Qed.

  Lemma aProp_at_affinely Σ P : aProp_at (<affine> P) Σ ⊣⊢ Σ ≡ ∅ ∧ aProp_at P ∅.
  Proof.
    rewrite /bi_affinely aProp_at_and aProp_at_emp.
    iSplit; iIntros "[Hx HP]"; (iSplit; [done|]);
      [by iRewrite "Hx" in "HP"|by iRewrite "Hx"].
  Qed.
  Lemma aProp_at_intuitionistically Σ P :
    aProp_at (□ P) Σ ⊣⊢ Σ ≡ ∅ ∧ aProp_at P ∅.
  Proof. by rewrite aProp_at_affinely aProp_at_persistently. Qed.
  Lemma aProp_at_except_0 Σ P : aProp_at (◇ P) Σ ⊣⊢ ◇ (aProp_at P Σ).
  Proof.
    by rewrite /bi_except_0 aProp_at_or aProp_at_later aProp_at_pure.
  Qed.
  Lemma aProp_at_plainly Σ P : aProp_at (■ P) Σ ⊣⊢ aProp_at P ∅.
  Proof. by rewrite /plainly aProp_at_si_pure aProp_at_si_emp_valid. Qed.

  Lemma aProp_at_sep_2 Σ1 Σ2 P Q :
    Σ1 ##ₘ Σ2 → aProp_at P Σ1 ∧ aProp_at Q Σ2 ⊢ aProp_at (P ∗ Q) (Σ1 ∪ Σ2).
  Proof. rewrite aProp_at_sep. iIntros. iExists Σ1, Σ2. auto. Qed.

  Lemma aProp_at_sep_affinely_l Σ P Q :
    aProp_at (<affine> P ∗ Q) Σ ⊣⊢ aProp_at P ∅ ∧ aProp_at Q Σ.
  Proof.
    rewrite aProp_at_sep. setoid_rewrite aProp_at_affinely. iSplit.
    - iIntros "#(%Σ1 & %Σ2 & -> & %Hx & [-> $] & ?)". by rewrite (left_id_L ∅).
    - iIntros "#[??]". iExists ∅, Σ. iSplit; [by rewrite left_id_L|].
      iSplit; [iPureIntro; apply map_disjoint_empty_l|]. auto.
  Qed.
  Lemma aProp_at_sep_affinely_r Σ P Q :
    aProp_at (P ∗ <affine> Q) Σ ⊣⊢ aProp_at P Σ ∧ aProp_at Q ∅.
  Proof. rewrite (comm _ P) aProp_at_sep_affinely_l. apply: comm. Qed.
  Lemma aProp_at_sep_affine_l Σ P Q :
    Affine P →
    aProp_at (P ∗ Q) Σ ⊣⊢ aProp_at P ∅ ∧ aProp_at Q Σ.
  Proof.
    intros. by rewrite -{1}(bi.affine_affinely P) aProp_at_sep_affinely_l.
  Qed.
  Lemma aProp_at_sep_affine_r Σ P Q :
    Affine Q →
    aProp_at (P ∗ Q) Σ ⊣⊢ aProp_at P Σ ∧ aProp_at Q ∅.
  Proof. intros. rewrite (comm _ P) aProp_at_sep_affine_l. apply: comm. Qed.

  Global Instance aProp_bi_positive : BiPositive aPropI.
  Proof.
    rewrite /BiPositive=> P Q. rewrite aProp_entails=> Σ.
    rewrite !aProp_at_affinely !aProp_at_sep !discrete_eq !map_empty_equiv_eq.
    iIntros "(-> & %Σ1 & %Σ2 & %Hemp & %Hdisj & ? & ?)".
    assert (Σ1 = ∅) as -> by (by eapply map_positive_l).
    rewrite left_id_L in Hemp; subst.
    iExists ∅, ∅. rewrite aProp_at_affinely. eauto 10.
  Qed.
End aProp.

Global Instance into_pure_aProp_at_pure P φ :
 IntoPure P φ →
 IntoPure (aProp_at P ∅) φ.
Proof. rewrite /IntoPure=> ->. by rewrite aProp_at_pure. Qed.
Global Instance into_pure_aProp_at_emp Σ :
 IntoPure (aProp_at emp Σ) (Σ = ∅).
Proof. by rewrite /IntoPure aProp_at_emp !discrete_eq !map_empty_equiv_eq. Qed.

Global Instance into_and_aProp_at_and p P P1 P2 Σ :
  IntoAnd false P P1 P2 →
  IntoAnd p (aProp_at P Σ) (aProp_at P1 Σ) (aProp_at P2 Σ).
Proof.
  rewrite /IntoAnd /=. intros ->.
  by rewrite aProp_at_and bi.intuitionistically_if_and.
Qed.
Global Instance into_and_aProp_at_sep_affine_l p P P1 P2 Σ :
  IntoSep P P1 P2 → Affine P1 →
  IntoAnd p (aProp_at P Σ) (aProp_at P1 ∅) (aProp_at P2 Σ).
Proof.
  rewrite /IntoSep /IntoAnd /=. intros -> ?.
  by rewrite aProp_at_sep_affine_l bi.intuitionistically_if_and.
Qed.
Global Instance into_and_aProp_at_sep_affine_r p P P1 P2 Σ :
  IntoSep P P1 P2 → Affine P2 →
  IntoAnd p (aProp_at P Σ) (aProp_at P1 Σ) (aProp_at P2 ∅).
Proof.
  rewrite /IntoSep /IntoAnd /=. intros -> ?.
  by rewrite aProp_at_sep_affine_r bi.intuitionistically_if_and.
Qed.
Global Instance into_and_aProp_at_affinely p P  Σ :
  IntoAnd p (aProp_at (<affine> P) Σ) ⌜ Σ = ∅ ⌝ (aProp_at P ∅) | 20.
Proof.
  rewrite /IntoAnd /=.
  by rewrite aProp_at_affinely !discrete_eq !map_empty_equiv_eq.
Qed.

Global Instance into_or_aProp_at_or P P1 P2 Σ :
  IntoOr P P1 P2 →
  IntoOr (aProp_at P Σ) (aProp_at P1 Σ) (aProp_at P2 Σ).
Proof. rewrite /IntoOr /=. intros ->. by rewrite aProp_at_or. Qed.

Global Instance into_exist_aProp_at_exist {A} P (Φ : A → aProp) name Σ :
  IntoExist P Φ name →
  IntoExist (aProp_at P Σ) (λ x, aProp_at (Φ x) Σ) name.
Proof. rewrite /IntoExist /=. intros ->. by rewrite aProp_at_exist. Qed.
Global Instance into_exist_aProp_at_sep P P1 P2 Σ :
  IntoSep P P1 P2 →
  IntoExist (aProp_at P Σ) (λ Σ1, ∃ Σ2,
    ⌜ Σ = Σ1 ∪ Σ2 ⌝ ∧ ⌜ Σ1 ##ₘ Σ2 ⌝ ∧ aProp_at P1 Σ1 ∧ aProp_at P2 Σ2)%I
    (to_ident_name Σ2) | 20.
Proof. rewrite /IntoSep /IntoExist /=. intros ->. by rewrite aProp_at_sep. Qed.

Global Instance into_forall_aProp_at_forall {A} P (Φ : A → aProp) Σ :
  IntoForall P Φ →
  IntoForall (aProp_at P Σ) (λ x, aProp_at (Φ x) Σ).
Proof. rewrite /IntoForall /=. intros ->. by rewrite aProp_at_forall. Qed.

Global Instance into_internal_eq_aProp_at_internal_eq {A : ofe} (x y : A) P Σ :
  IntoInternalEq P x y →
  IntoInternalEq (aProp_at P Σ) x y .
Proof. rewrite /IntoInternalEq. intros ->. by rewrite aProp_at_internal_eq. Qed.

Global Instance into_laterN_aProp_at_later only_head n P Q Σ :
  IntoLaterN only_head n P Q →
  IntoLaterN only_head n (aProp_at P Σ) (aProp_at Q Σ).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite aProp_at_laterN. Qed.

Lemma own_chan_exclusive l p1 p2 :
  own_chan l p1 ∗ own_chan l p2 ⊢ False.
Proof.
  apply aProp_entails. intros Σ.
  rewrite aProp_at_sep_own_chan.
  iIntros "[%p [%HΣ1 [H1 Hp]]]".
  rewrite aProp_at_own_chan.
  iDestruct "Hp" as (p1') "[%HΣ2 H2]".
  apply (f_equal (λ x, x !! Chan l)) in HΣ2.
  rewrite lookup_delete_eq in HΣ2.
  rewrite lookup_singleton_eq in HΣ2.
  discriminate.
Qed.

Lemma own_ref_exclusive l v1 v2 :
  own_ref l v1 ∗ own_ref l v2 ⊢ False.
Proof.
  apply aProp_entails. intros Σ.
  rewrite aProp_at_sep_own_ref.
  iIntros "[%HΣ1 H1]".
  rewrite aProp_at_own_ref.
  iDestruct "H1" as %HΣ2.
  apply (f_equal (λ x, x !! Chan l)) in HΣ2.
  rewrite lookup_delete_eq in HΣ2.
  rewrite lookup_singleton_eq in HΣ2.
  discriminate.
Qed.

Lemma own_chan_ref_exclusive l p v :
  own_chan l p ∗ own_ref l v ⊢ False.
Proof.
  apply aProp_entails. intros Σ.
  rewrite aProp_at_sep_own_chan.
  iIntros "[%p' [%HΣ1 [H1 Hp]]]".
  rewrite aProp_at_own_ref.
  iDestruct "Hp" as %HΣ2.
  apply (f_equal (λ x, x !! Chan l)) in HΣ2.
  rewrite lookup_delete_eq in HΣ2.
  rewrite lookup_singleton_eq in HΣ2.
  discriminate.
Qed.
