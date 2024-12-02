(** This file defines all of the semantic subtyping rules for term types and
session types. *)
From iris.bi.lib Require Import core.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From dlfactris.logrel Require Export subtyping term_types session_types.

Section subtyping_rules.
  Implicit Types A : ltty.
  Implicit Types S : lsty.

  (** Generic rules *)
  Lemma lty_le_refl {k} (K : lty k) : K <: K.
  Proof. destruct k; [by iIntros (v) "!>?"|by iModIntro;iApply subprot_refl]. Qed.
  Lemma lty_le_trans {k} (K1 K2 K3 : lty k) : K1 <: K2 -∗ K2 <: K3 -∗ K1 <: K3.
  Proof.
    destruct k.
    - iIntros "#H1 #H2" (v) "!> H". iApply "H2". by iApply "H1".
    - iIntros "#H1 #H2 !>". by iApply subprot_trans.
  Qed.

  Lemma lty_bi_le_refl {k} (K : lty k) : K <:> K.
  Proof. iSplit; iApply lty_le_refl. Qed.
  Lemma lty_bi_le_trans {k} (K1 K2 K3 : lty k) :
    K1 <:> K2 -∗ K2 <:> K3 -∗ K1 <:> K3.
  Proof. iIntros "#[H11 H12] #[H21 H22]". iSplit; by iApply lty_le_trans. Qed.
  Lemma lty_bi_le_sym {k} (K1 K2 : lty k) : K1 <:> K2 -∗ K2 <:> K1.
  Proof. iIntros "#[??]". by iSplit. Qed.

  Lemma lty_le_l {k} (K1 K2 K3 : lty k) : K1 <:> K2 -∗ K2 <: K3 -∗ K1 <: K3.
  Proof. iIntros "#[H1 _] #H2". by iApply lty_le_trans. Qed.
  Lemma lty_le_r {k} (K1 K2 K3 : lty k) : K1 <: K2 -∗ K2 <:> K3 -∗ K1 <: K3.
  Proof. iIntros "#H1 #[H2 _]". by iApply lty_le_trans. Qed.

  Lemma lty_le_rec_unfold {k} (C : lty k → lty k) `{!Contractive C} :
    lty_rec C <:> C (lty_rec C).
  Proof.
    iSplit.
    - rewrite {1}/lty_rec fixpoint_unfold. iApply lty_le_refl.
    - rewrite {2}/lty_rec fixpoint_unfold. iApply lty_le_refl.
  Qed.

  Lemma lty_le_rec_internal {k} (C1 C2 : lty k → lty k)
      `{Contractive C1, Contractive C2} :
    (∀ K1 K2, ▷ (K1 <: K2) -∗ C1 K1 <: C2 K2) -∗
    lty_rec C1 <: lty_rec C2.
  Proof.
    iIntros "#Hle". iLöb as "IH".
    iApply lty_le_l; [iApply lty_le_rec_unfold|].
    iApply lty_le_r; [|iApply lty_bi_le_sym; iApply lty_le_rec_unfold].
    by iApply "Hle".
  Qed.
  Lemma lty_le_rec_external {k} (C1 C2 : lty k → lty k)
      `{Contractive C1, Contractive C2} :
    (∀ K1 K2, (K1 <: K2) → C1 K1 <: C2 K2) →
    lty_rec C1 <: lty_rec C2.
  Proof.
    intros IH. rewrite /lty_rec. apply fixpoint_ind.
    - by intros K1' K2' -> ?.
    - exists (fixpoint C2). iApply lty_le_refl.
    - intros K' ?. rewrite (fixpoint_unfold C2). by apply IH.
    - apply bi.limit_preserving_entails; solve_proper.
  Qed.

  (** Term subtyping *)
  Lemma lty_le_any A : lty_copyable A -∗ A <: any.
  Proof. iIntros "#H" (v) "!> HA". by iDestruct ("H" with "HA") as "_". Qed.
  Lemma lty_copyable_any : ⊢ lty_copyable any.
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_le_copy A B : A <: B -∗ copy A <: copy B.
  Proof. iIntros "#Hle". iIntros (v) "!> #HA !>". by iApply "Hle". Qed.
  Lemma lty_le_copy_elim A : copy A <: A.
  Proof. by iIntros (v) "!> #H". Qed.
  Lemma lty_copyable_copy A : ⊢ lty_copyable (copy A).
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_le_copy_inv_mono A B : A <: B -∗ copy- A <: copy- B.
  Proof.
    iIntros "#Hle !>" (v) "#HA". iApply (coreP_wand (ltty_car A v) with "[] HA").
    iClear "HA". iIntros "!> !>". iApply "Hle".
  Qed.
  Lemma lty_le_copy_inv_elim A : copy- (copy A) <: A.
  Proof. iIntros (v) "!> #H". iApply (coreP_elim with "H"). Qed.
  Lemma lty_copyable_copy_inv A : ⊢ lty_copyable (copy- A).
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.
  Lemma lty_le_copy_inv_elim_copyable A : lty_copyable A -∗ copy- A <: A.
  Proof.
    iIntros "#Hcp".
    iApply lty_le_trans.
    - iApply lty_le_copy_inv_mono. iApply "Hcp".
    - iApply lty_le_copy_inv_elim.
  Qed.

  Lemma lty_copyable_unit : ⊢ lty_copyable ().
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.
  Lemma lty_copyable_bool : ⊢ lty_copyable lty_bool.
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.
  Lemma lty_copyable_int : ⊢ lty_copyable lty_int.
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_le_arr A11 A12 A21 A22 :
    ▷ (A21 <: A11) -∗ ▷ (A12 <: A22) -∗
    (A11 ⊸ A12) <: (A21 ⊸ A22).
  Proof.
    iIntros "#H1 #H2" (v) "!> H". iIntros (w) "H'".
    iApply (wp_later_wand with "(H (H1 H'))"). iIntros "!>" (v') "H".
    by iApply "H2".
  Qed.
  Lemma lty_le_arr_copy A11 A12 A21 A22 :
    ▷ (A21 <: A11) -∗ ▷ (A12 <: A22) -∗
    (A11 → A12) <: (A21 → A22).
  Proof. iIntros "#H1 #H2" (v) "!> #H !>". by iApply lty_le_arr. Qed.
  (** This rule is really trivial, since [A → B] is syntactic sugar for
  [copy (A ⊸ B)], but we include it anyway for completeness' sake. *)
  Lemma lty_copyable_arr_copy A B : ⊢ lty_copyable (A → B).
  Proof. iApply lty_copyable_copy. Qed.

  Lemma lty_le_prod A11 A12 A21 A22 :
    (A11 <: A21) -∗ (A12 <: A22) -∗
    A11 * A12 <: A21 * A22.
  Proof.
    iIntros "#H1 #H2" (v) "!>". iDestruct 1 as (w1 w2 ->) "[H1' H2']".
    iExists _, _.
    iDestruct ("H1" with "H1'") as "$".
    by iDestruct ("H2" with "H2'") as "$".
  Qed.

  Lemma lty_le_prod_copy A B :
    copy A * copy B <:> copy (A * B).
  Proof.
    iSplit; iModIntro; iIntros (v) "Hv";
      iDestruct "Hv" as (v1 v2 ->) "[#Hv1 #Hv2]".
    - iIntros "!>". iExists _, _. by iFrame "#".
    - iExists v1, v2. iSplit; [done|]. iFrame "#".
  Qed.

  Lemma lty_copyable_prod A B :
    lty_copyable A -∗ lty_copyable B -∗ lty_copyable (A * B).
  Proof.
    iIntros "#HcpA #HcpB". rewrite /lty_copyable /=.
    iApply lty_le_r.
    - by iApply lty_le_prod.
    - by iApply lty_le_prod_copy.
  Qed.

  Lemma lty_le_sum As1 As2 :
    ([∗ map] A1;A2 ∈ As1; As2, (A1 <: A2)) -∗
    lty_sum As1 <: lty_sum As2.
  Proof.
    iIntros "#H !> %v (%j & %w & [%A1 %HA1] & -> & ?)".
    iDestruct (big_sepM2_lookup_l with "H") as (A2 HA2) "HA"; first done.
    iExists j, w. rewrite !lookup_total_alt HA1 HA2 /=. do 2 (iSplit; [done|]).
    by iApply "HA".
  Qed.
  Lemma lty_le_sum_copy As :
    lty_sum (lty_copy <$> As) <:> copy (lty_sum As).
  Proof.
    iSplit; iIntros "!> %v (%j & %w & [%A1 %HA1] & -> & HA)"; iExists j, w.
    - rewrite lookup_fmap in HA1. destruct (As !! j) as [A|] eqn:HA; simplify_eq/=.
      rewrite !lookup_total_alt lookup_fmap HA /=. iDestruct "HA" as "#HA".
      eauto with iFrame.
    - rewrite !lookup_total_alt lookup_fmap HA1 /=. iDestruct "HA" as "#HA".
      eauto with iFrame.
  Qed.
  Lemma lty_copyable_sum As :
    ([∗ map] A ∈ As, lty_copyable A) -∗ lty_copyable (lty_sum As).
  Proof.
    iIntros "#HAs". rewrite /lty_copyable /=.
    iApply lty_le_r; last by iApply lty_le_sum_copy.
    iApply lty_le_sum. rewrite big_sepM2_fmap_r. by iApply big_sepM_sepM2_diag.
  Qed.

  Lemma lty_le_forall C1 C2 :
    ▷ (∀ A, C1 A <: C2 A) -∗
    (∀ A, C1 A) <: (∀ A, C2 A).
  Proof.
    iIntros "#Hle" (v) "!> H". iIntros (A).
    iApply (wp_later_wand with "H").
    iIntros "!>" (w) "Hw". by iApply "Hle".
  Qed.

  Lemma lty_le_exist C1 C2 :
    (∀ A, C1 A <: C2 A) -∗
    (∃ A, C1 A) <: (∃ A, C2 A).
  Proof.
    iIntros "#Hle" (v) "!>". iDestruct 1 as (A) "H". iExists A. by iApply "Hle".
  Qed.
  Lemma lty_le_exist_elim C B :
    C B <: ∃ A, C A.
  Proof. iIntros "!>" (v) "Hle". by iExists B. Qed.

  Lemma lty_le_exist_copy F :
    (∃ A, copy (F A)) <:> copy (∃ A, F A).
  Proof.
    iSplit; iIntros "!>" (v); iDestruct 1 as (A) "#Hv";
      iExists A; repeat iModIntro; iApply "Hv".
  Qed.

  Lemma lty_copyable_exist (C : ltty → ltty) :
    (∀ M, lty_copyable (C M)) -∗ lty_copyable (lty_exist C).
  Proof.
    iIntros "#Hle". rewrite /lty_copyable /tc_opaque.
    iApply lty_le_r; last by iApply lty_le_exist_copy.
    iApply lty_le_exist. iApply "Hle".
  Qed.

  (* TODO(COPY): Commuting rule for recursive types, allowing [copy] to move
  outside the recursive type. This rule should be derivable using Löb
  induction. *)
  Lemma lty_copyable_rec C `{!Contractive C} :
    (∀ A, lty_copyable (C A)) -∗ lty_copyable (lty_rec C).
  Proof.
    iIntros "#Hcopy".
    iIntros (v) "!> Hv".
    rewrite /lty_rec {1}fixpoint_unfold.
    iDestruct ("Hcopy" with "Hv") as "Hcopy'".
    iDestruct "Hcopy'" as "#Hcopy'".
    iModIntro.
    iEval (rewrite fixpoint_unfold).
    iApply "Hcopy'".
  Qed.

  Lemma lty_le_ref_uniq A1 A2 :
    ▷ (A1 <: A2) -∗ ref_uniq A1 <: ref_uniq A2.
  Proof.
    iIntros "#H1" (v) "!>". iDestruct 1 as (l w ->) "[Hl HA]".
    iDestruct ("H1" with "HA") as "HA".
    iExists l, w. by iFrame.
  Qed.

  Lemma lty_le_chan S1 S2 :
    ▷ (S1 <: S2) ⊢ chan S1 <: chan S2.
  Proof.
    iIntros "#Hle" (v) "!> H".
    iApply (own_chan_subprot with "H [Hle]"). eauto.
  Qed.

  (** Session subtyping *)
  Lemma lty_le_send A1 A2 S1 S2 :
    (A2 <: A1) -∗ ▷ (S1 <: S2) -∗
    (<!!> TY A1 ; S1) <: (<!!> TY A2 ; S2).
  Proof.
    iIntros "#HAle #HSle !>".
    iIntros (v) "H". iExists v.
    iDestruct ("HAle" with "H") as "$". by iModIntro.
  Qed.

  Lemma lty_le_recv A1 A2 S1 S2 :
    (A1 <: A2) -∗ ▷ (S1 <: S2) -∗
    (<??> TY A1 ; S1) <: (<??> TY A2 ; S2).
  Proof.
    iIntros "#HAle #HSle !>" (v) "H". iExists v.
    iDestruct ("HAle" with "H") as "$". by iModIntro.
  Qed.

  Lemma lty_le_exist_elim_l k (M : lty k → lmsg) S :
    (∀ (A : lty k), (<??> M A) <: S) ⊢
    (<?? (A : lty k)> M A) <: S.
  Proof.
    iIntros "#Hle !>".
    unshelve iApply subprot_exist_elim_l_inhabited; [by apply _|by auto].
  Qed.

  Lemma lty_le_exist_elim_r k (M : lty k → lmsg) S :
    (∀ (A : lty k), S <: (<!!> M A)) ⊢
    S <: (<!! (A : lty k)> M A).
  Proof.
    iIntros "#Hle !>".
    unshelve iApply subprot_exist_elim_r_inhabited; [by apply _|by auto].
  Qed.

  Lemma lty_le_exist_intro_l k (M : lty k → lmsg) (A : lty k) :
    (<!! X> M X) <: (<!!> M A).
  Proof. iIntros "!>". iApply (subprot_exist_intro_l). Qed.

  Lemma lty_le_exist_intro_r k (M : lty k → lmsg) (A : lty k) :
    (<??> M A) <: (<?? X> M X).
  Proof. iIntros "!>". iApply (subprot_exist_intro_r). Qed.

  Lemma lty_le_texist_elim_l {kt} (M : ltys kt → lmsg) S :
    (∀ Xs, (<??> M Xs) <: S) ⊢
    (<??.. Xs> M Xs) <: S.
  Proof.
    iIntros "H". iInduction kt as [|k kt] "IH"; simpl; [done|].
    iApply lty_le_exist_elim_l; iIntros (X).
    iApply "IH". iIntros (Xs). iApply "H".
  Qed.

  Lemma lty_le_texist_elim_r {kt : ktele} (M : ltys kt → lmsg) S :
    (∀ Xs, S <: (<!!> M Xs)) ⊢
    S <: (<!!.. Xs> M Xs).
  Proof.
    iIntros "H". iInduction kt as [|k kt] "IH"; simpl; [done|].
    iApply lty_le_exist_elim_r; iIntros (X).
    iApply "IH". iIntros (Xs). iApply "H".
  Qed.

  Lemma lty_le_texist_intro_l {kt : ktele} (M : ltys kt → lmsg) Ks :
    (<!!.. Xs> M Xs) <: (<!!> M Ks).
  Proof.
    induction Ks as [|k kT X Xs IH]; simpl; [iApply lty_le_refl|].
    iApply lty_le_trans; [by iApply lty_le_exist_intro_l|]. iApply IH.
  Qed.

  Lemma lty_le_texist_intro_r {kt : ktele} (M : ltys kt → lmsg) Ks :
    (<??> M Ks) <: (<??.. Xs> M Xs).
  Proof.
    induction Ks as [|k kt X Xs IH]; simpl; [iApply lty_le_refl|].
    iApply lty_le_trans; [|by iApply lty_le_exist_intro_r]. iApply IH.
  Qed.

  Lemma lty_le_select ASs1 ASs2 :
    ([∗ map] AS1;AS2 ∈ ASs1; ASs2, AS2.1 <: AS1.1 ∧ ▷ (AS1.2 <: AS2.2)) -∗
    lty_select ASs1 <: lty_select ASs2.
  Proof.
    iIntros "#Hle !> %t %v HA2"; iExists t, v. rewrite !lookup_total_alt.
    destruct (ASs2 !! t) as [[A2 S2]|] eqn:?; simpl; [|done].
    iDestruct (big_sepM2_lookup_r with "Hle") as ([A1 S1] ->) "[HA HS]"; first done.
    iDestruct ("HA" with "HA2") as "$". by iModIntro.
  Qed.
  Lemma lty_le_select_subseteq ASs1 ASs2 :
    ASs2 ⊆ ASs1 →
    lty_select ASs1 <: lty_select ASs2.
  Proof.
    iIntros (?) "!> %t %v H2". rewrite lookup_total_alt.
    destruct (ASs2 !! t) as [S|] eqn:?; simpl; [|done].
    iExists t, v. rewrite lookup_total_alt.
    assert (ASs1 !! t = Some S) as -> by eauto using lookup_weaken. by iFrame.
  Qed.
  Lemma lty_bi_le_select ASs1 ASs2 :
    ([∗ map] AS1;AS2 ∈ ASs1; ASs2, AS2.1 <:> AS1.1 ∧ ▷ (AS1.2 <:> AS2.2)) -∗
    lty_select ASs1 <:> lty_select ASs2.
  Proof.
    iIntros "H".
    iSplit.
    - iApply lty_le_select.
      iApply (big_sepM2_impl with "H").
      iIntros "!>" (k x1 x2 Hin1 Hin2) "[[$ _] [$ _]]".
    - iApply lty_le_select.
      iApply big_sepM2_flip.
      iApply (big_sepM2_impl with "H").
      iIntros "!>" (k x1 x2 Hin1 Hin2) "[[_ $] [_ $]]".
  Qed.
  Lemma lty_le_branch ASs1 ASs2 :
    ([∗ map] AS1;AS2 ∈ ASs1; ASs2, AS1.1 <: AS2.1 ∧ ▷ (AS1.2 <: AS2.2)) -∗
    lty_branch ASs1 <: lty_branch ASs2.
  Proof.
    iIntros "#Hle !> %t %v HA1"; iExists t, v. rewrite !lookup_total_alt.
    destruct (ASs1 !! t) as [[A1 S1]|] eqn:?; simpl; [|done].
    iDestruct (big_sepM2_lookup_l with "Hle") as ([A2 S2] ->) "[HA HS]"; first done.
    iDestruct ("HA" with "HA1") as "$". by iModIntro.
  Qed.
  Lemma lty_le_branch_subseteq ASs1 ASs2 :
    ASs1 ⊆ ASs2 →
    lty_branch ASs1 <: lty_branch ASs2.
  Proof.
    iIntros (?) "!> %t %v H2". rewrite lookup_total_alt.
    destruct (ASs1 !! t) as [S|] eqn:?; simpl; [|done].
    iExists t, v. rewrite lookup_total_alt.
    assert (ASs2 !! t = Some S) as -> by eauto using lookup_weaken. by iFrame.
  Qed.
  Lemma lty_bi_le_branch ASs1 ASs2 :
    ([∗ map] AS1;AS2 ∈ ASs1; ASs2, AS2.1 <:> AS1.1 ∧ ▷ (AS1.2 <:> AS2.2)) -∗
    lty_branch ASs1 <:> lty_branch ASs2.
  Proof.
    iIntros "H".
    iSplit.
    - iApply lty_le_branch.
      iApply (big_sepM2_impl with "H").
      iIntros "!>" (k x1 x2 Hin1 Hin2) "[[_ $] [$ _]]".
    - iApply lty_le_branch.
      iApply big_sepM2_flip.
      iApply (big_sepM2_impl with "H").
      iIntros "!>" (k x1 x2 Hin1 Hin2) "[[$ _] [_ $]]".
  Qed.

  (** The instances below make it possible to use the tactics [iIntros],
  [iExist], [iSplitL]/[iSplitR], [iFrame] and [iModIntro] on [lty_le] goals.
  These instances have higher precedence than the ones in [proto.v] to avoid
  needless unfolding of the subtyping relation. *)
  Global Instance lty_le_from_forall_l k (M : lty k → lmsg) (S : lsty) name :
    AsIdentName M name →
    FromForall (lty_message ARecv (lty_msg_exist M) <: S) (λ X, (<??> M X) <: S)%I name | 0.
  Proof. intros _. apply lty_le_exist_elim_l. Qed.
  Global Instance lty_le_from_forall_r k (S : lsty) (M : lty k → lmsg) name :
    AsIdentName M name →
    FromForall (S <: lty_message ASend (lty_msg_exist M)) (λ X, S <: (<!!> M X))%I name | 1.
  Proof. intros _. apply lty_le_exist_elim_r. Qed.

  Global Instance lty_le_from_exist_l k (M : lty k → lmsg) S :
    FromExist ((<!! X> M X) <: S) (λ X, (<!!> M X) <: S)%I | 0.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (lty_le_trans with "[] H"). iApply lty_le_exist_intro_l.
  Qed.
  Global Instance lty_le_from_exist_r k (M : lty k → lmsg) S :
    FromExist (S <: <?? X> M X) (λ X, S <: (<??> M X))%I | 1.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (lty_le_trans with "H"). iApply lty_le_exist_intro_r.
  Qed.

  Global Instance lty_le_from_modal_send A (S1 S2 : lsty) :
    FromModal True (modality_instances.modality_laterN 1) (S1 <: S2)
              ((<!!> TY A; S1) <: (<!!> TY A; S2)) (S1 <: S2) | 0.
  Proof.
    rewrite /FromModal. iIntros (_) "H". iApply lty_le_send.
    - iApply lty_le_refl.
    - done.
  Qed.

  Global Instance lty_le_from_modal_recv A (S1 S2 : lsty) :
    FromModal True (modality_instances.modality_laterN 1) (S1 <: S2)
              ((<??> TY A; S1) <: (<??> TY A; S2)) (S1 <: S2) | 0.
  Proof.
    rewrite /FromModal. iIntros (_) "H". iApply lty_le_recv.
    - iApply lty_le_refl.
    - done.
  Qed.

  (** Algebraic laws *)
  Lemma lty_le_dual S1 S2 : S2 <: S1 -∗ lty_dual S1 <: lty_dual S2.
  Proof. iIntros "#H !>". by iApply subprot_dual. Qed.
  Lemma lty_le_dual_l S1 S2 : lty_dual S2 <: S1 -∗ lty_dual S1 <: S2.
  Proof. iIntros "#H !>". by iApply subprot_dual_l. Qed.
  Lemma lty_le_dual_r S1 S2 : S2 <: lty_dual S1 -∗ S1 <: lty_dual S2.
  Proof. iIntros "#H !>". by iApply subprot_dual_r. Qed.
  Lemma lty_le_dual_dual S : S <:> lty_dual (lty_dual S).
  Proof. rewrite /lty_dual. rewrite dual_dual. iSplit; by iIntros "!>". Qed.
  Lemma lty_bi_le_dual S1 S2 : S1 <:> S2 -∗ lty_dual S1 <:> lty_dual S2.
  Proof.
    iIntros "#H".
    iSplit.
    - iIntros "!>". iDestruct "H" as "[_ H]". by iApply subprot_dual.
    - iIntros "!>". iDestruct "H" as "[H _]". by iApply subprot_dual.
  Qed.

  Lemma lty_le_dual_end a : lty_dual (lty_end a) <:> lty_end (action_dual a).
  Proof. rewrite /lty_dual dual_end=> /=. apply lty_bi_le_refl. Qed.
  Lemma lty_le_dual_message a A S :
    lty_dual (lty_message a (TY A; S)) <:>
      lty_message (action_dual a) (TY A; (lty_dual S)).
  Proof.
    rewrite /lty_dual dual_msg msg_dual_exist.
    setoid_rewrite msg_dual_base. iSplit; by iIntros "!> /=".
  Qed.

  Lemma lty_le_dual_send_exist {kt} M (A : kt -k> ltty) (S : kt -k> lsty) :
    LtyMsgTele M A S →
    lty_dual (<!!> M) <:>
        <??.. As> TY (ktele_app A As) ; lty_dual (ktele_app S As).
  Proof.
    rewrite /LtyMsgTele. iIntros (->).
    rewrite /lty_dual /lty_message dual_msg /=.
    induction kt as [|k kt IH]; rewrite msg_dual_exist.
    - iSplit; iIntros (v); iExists v; rewrite msg_dual_base; eauto.
    - iSplit.
      + iIntros (v). iExists v.
        iApply lty_le_l; [ iApply IH | iApply lty_le_refl ].
      + iIntros (v). iExists v.
        iApply lty_le_l; [ iApply lty_bi_le_sym; iApply IH | iApply lty_le_refl ].
  Qed.

  Lemma lty_le_dual_recv_exist {kt} M (A : kt -k> ltty) (S : kt -k> lsty) :
    LtyMsgTele M A S →
    lty_dual (<??> M) <:>
      <!!.. As> TY (ktele_app A As) ; lty_dual (ktele_app S As).
  Proof.
    rewrite /LtyMsgTele. iIntros (->).
    rewrite /lty_dual /lty_message dual_msg /=.
    induction kt as [|k kt IH]; rewrite msg_dual_exist.
    - iSplit; iIntros (v); iExists v; rewrite msg_dual_base; eauto.
    - iSplit.
      + iIntros (v). iExists v.
        iApply lty_le_l; [ iApply IH | iApply lty_le_refl ].
      + iIntros (v). iExists v.
        iApply lty_le_l; [ iApply lty_bi_le_sym; iApply IH | iApply lty_le_refl ].
  Qed.

  Lemma lty_le_dual_send A S : lty_dual (<!!> TY A; S) <:> (<??> TY A; lty_dual S).
  Proof. apply (lty_le_dual_send_exist (kt:=KTeleO)). apply _. Qed.
  Lemma lty_le_dual_recv A S : lty_dual (<??> TY A; S) <:> (<!!> TY A; lty_dual S).
  Proof. apply (lty_le_dual_recv_exist (kt:=KTeleO)). apply _. Qed.
  Lemma lty_le_dual_close : lty_dual END!! <:> END??.
  Proof. iSplit; rewrite /lty_end /lty_dual dual_end=> /=; iApply lty_le_refl. Qed.
  Lemma lty_le_dual_wait : lty_dual END?? <:> END!!.
  Proof. iSplit; by rewrite /lty_end /lty_dual dual_end; iApply lty_le_refl. Qed.

  Lemma lty_le_dual_choice a ASs :
    lty_dual (lty_choice a ASs)
    <:> lty_choice (action_dual a) (prod_map id lty_dual <$> ASs).
  Proof.
    rewrite /lty_dual /lty_choice dual_msg msg_dual_exist;
      setoid_rewrite msg_dual_exist; setoid_rewrite msg_dual_base.
    iSplit; iIntros "!> /="; destruct a; iIntros (j v) "H"; iExists j, v;
      rewrite !lookup_total_alt lookup_fmap; destruct (ASs !! j)=> //=;
      iFrame "H"; auto.
  Qed.

  Lemma lty_le_dual_select ASs :
    lty_dual (lty_select ASs) <:> lty_branch (prod_map id lty_dual <$> ASs).
  Proof. iApply lty_le_dual_choice. Qed.
  Lemma lty_le_dual_branch ASs :
    lty_dual (lty_branch ASs) <:> lty_select (prod_map id lty_dual <$> ASs).
  Proof. iApply lty_le_dual_choice. Qed.
End subtyping_rules.

Global Hint Extern 0 (environments.envs_entails _ (?x <: ?y)) =>
  first [is_evar x; fail 1 | is_evar y; fail 1|iApply lty_le_refl] : core.
