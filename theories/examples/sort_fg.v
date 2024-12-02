From stdpp Require Import sorting.
From dlfactris Require Import examples.llist session_logic.proofmode.
Import TImp TImp.notations.

Definition cont := true.
Definition stop := false.

Definition sort_service_fg_split : val :=
  rec: "go" "c" "c1" "c2" :=
    if: ~(recv "c") then send "c1" #stop;; send "c2" #stop else
    let: "x" := recv "c" in
    send "c1" #cont;; send "c1" "x";;
    "go" "c" "c2" "c1".

Definition sort_service_fg_forward : val :=
  rec: "go" "c" "cin" :=
    if: ~(recv "cin") then send "c" #stop;; close "cin" else
    let: "x" := recv "cin" in
    send "c" #cont;; send "c" "x";;
    "go" "c" "cin".

Definition sort_service_fg_merge : val :=
  rec: "go" "cmp" "c" "x1" "c1" "c2" :=
    if: ~recv "c2" then
      send "c" #cont;;
      send "c" "x1";;
      close "c2";;
      sort_service_fg_forward "c" "c1"
    else
      let: "x2" := recv "c2" in
      if: "cmp" "x1" "x2" then
        send "c" #cont;; send "c" "x1";; "go" "cmp" "c" "x2" "c2" "c1"
      else
        send "c" #cont;; send "c" "x2";; "go" "cmp" "c" "x1" "c1" "c2".

Definition sort_service_fg : val :=
  rec: "go" "cmp" "c" :=
    if: ~(recv "c") then send "c" #stop else
    let: "x" := recv "c" in
    if: ~(recv "c") then
      send "c" #cont;; send "c" "x";; send "c" #stop
    else
      let: "y" := recv "c" in
      let: "c1" := fork_chan (λ: "c", "go" "cmp" "c";; wait "c") in
      let: "c2" := fork_chan (λ: "c", "go" "cmp" "c";; wait "c") in
      send "c1" #cont;; send "c1" "x";;
      send "c2" #cont;; send "c2" "y";;
      sort_service_fg_split "c" "c1" "c2";;
      (* TODO: What does this exacly achieve? *)
      let: "x" := (recv "c1";; recv "c1") in
      sort_service_fg_merge "cmp" "c" "x" "c1" "c2".

Definition sort_service_fg_func : val := λ: "c",
  let: "cmp" := recv "c" in
  sort_service_fg "cmp" "c".

Definition send_all : val :=
  rec: "go" "c" "xs" :=
    if: lisnil "xs" then #() else
    send "c" #cont;; send "c" (lpop "xs");; "go" "c" "xs".

Definition recv_all : val :=
  rec: "go" "c" "ys" :=
    if: ~recv "c" then #() else
    let: "x" := recv "c" in
    "go" "c" "ys";; lcons "x" "ys".

Definition sort_client_fg : val := λ: "cmp" "xs",
  let: "c" :=
    fork_chan (λ: "c", sort_service_fg "cmp" "c";; wait "c") in
  send_all "c" "xs";;
  send "c" #stop;;
  recv_all "c" "xs";;
  close "c".

Definition cmp_spec {A} (I : A → val → aProp) (R : relation A)
           `{!RelDecision R} (cmp : val) : aProp :=
  □ ∀ x x' v v',
      I x v -∗ I x' v' -∗
      WP cmp v v'
         {{ w, ⌜⌜ w = #(bool_decide (R x x')) ⌝⌝ ∗ I x v ∗ I x' v' }}.

Section sort_fg_inner.
  Context {A} (I : A → val → aProp) (R : relation A) `{!RelDecision R, !Total R}.

  Definition sort_fg_tail_prot_aux (xs : list A)
      (rec : list A -d> prot) : list A -d> prot := λ ys,
    (<?(b:bool)> MSG #b {{ if b then emp else ⌜⌜ ys ≡ₚ xs ⌝⌝ }} ;
     if b then <? y v> MSG v {{ ⌜⌜ TlRel R y ys ⌝⌝ ∗ I y v }}; rec (ys ++ [y])
     else END!)%prot.

  Instance sort_fg_tail_prot_aux_contractive xs :
    Contractive (sort_fg_tail_prot_aux xs).
  Proof. solve_prot_contractive. Qed.
  Definition sort_fg_tail_prot (xs : list A) : list A → prot :=
    fixpoint (sort_fg_tail_prot_aux xs).
  Global Instance sort_fg_tail_prot_unfold xs ys :
    ProtUnfold (sort_fg_tail_prot xs ys)
      (sort_fg_tail_prot_aux xs (sort_fg_tail_prot xs) ys).
  Proof. apply prot_unfold_eq, (fixpoint_unfold (sort_fg_tail_prot_aux _)). Qed.

  Definition sort_fg_head_prot_aux
      (rec : list A -d> prot) : list A -d> prot := λ xs,
    (<!(b:bool)> MSG #b;
     if b then <! x v > MSG v {{ I x v }}; rec (xs ++ [x])
     else sort_fg_tail_prot xs [])%prot.

  Instance sort_fg_head_prot_aux_contractive : Contractive sort_fg_head_prot_aux.
  Proof. solve_prot_contractive. Qed.

  Definition sort_fg_head_prot : list A → prot :=
    fixpoint sort_fg_head_prot_aux.
  Global Instance sort_fg_head_prot_unfold xs :
    ProtUnfold (sort_fg_head_prot xs) (sort_fg_head_prot_aux sort_fg_head_prot xs).
  Proof. apply prot_unfold_eq, (fixpoint_unfold sort_fg_head_prot_aux). Qed.

  Definition sort_fg_prot : prot := sort_fg_head_prot [].                        (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=d154ada6 *)

  Lemma sort_service_fg_split_spec c c1 c2 xs xs1 xs2 :
    {{{ c ↣ dual (sort_fg_head_prot xs) ∗
        c1 ↣ sort_fg_head_prot xs1 ∗ c2 ↣ sort_fg_head_prot xs2 }}}
      sort_service_fg_split c c1 c2
    {{{ xs' xs1' xs2', RET #(); ⌜⌜ xs' ≡ₚ xs1' ++ xs2' ⌝⌝ ∗
            c ↣ (dual (sort_fg_tail_prot (xs ++ xs') [])) ∗
            c1 ↣ sort_fg_tail_prot (xs1 ++ xs1') [] ∗
            c2 ↣ sort_fg_tail_prot (xs2 ++ xs2') [] }}}.
  Proof.
    iIntros (Φ) "(Hc & Hc1 & Hc2) HΦ".
    iLöb as "IH" forall (c c1 c2 xs xs1 xs2). wp_rec!.
    wp_recv ([]); wp_pures.
    - wp_recv (x v) as "HI". wp_send. wp_send with "[HI //]".
      iApply ("IH" with "Hc Hc2 Hc1").
      iIntros "!>" (xs' xs1' xs2') "(%Hperm & Hc & Hc2 & Hc1)".
      rewrite -!(assoc_L (++)). iApply "HΦ"; iFrame.
      by rewrite Hperm (comm (++) xs1') assoc_L.
    - do 2 wp_send. iApply ("HΦ" $! [] [] []). rewrite !right_id_L. by iFrame.
  Qed.

  Lemma sort_service_fg_forward_spec c cin xs ys zs xs' ys' :
    xs ≡ₚ xs' ++ zs →
    ys ≡ₚ ys' ++ zs →
    Sorted R ys →
    (∀ x, TlRel R x ys' → TlRel R x ys) →
    {{{ c ↣ dual (sort_fg_tail_prot xs ys) ∗ cin ↣ sort_fg_tail_prot xs' ys' }}}
      sort_service_fg_forward c cin
    {{{ RET #(); c ↣ END? }}}.
  Proof.
    iIntros (Hxs Hys Hsorted Hrel Φ) "[Hc Hcin] HΦ".
    iLöb as "IH" forall (c cin xs ys xs' ys' Hxs Hys Hsorted Hrel). wp_rec!.
    wp_recv ([]) as "Hb".
    - wp_recv (x c') as "[%HR HI]". wp_send. wp_send with "[$HI]"; first by eauto.
      iApply ("IH" with "[%] [%] [%] [%] Hc Hcin HΦ").
      * done.
      * by rewrite Hys -!assoc_L (comm _ zs).
      * auto using Sorted_snoc.
      * intros x'.
        inversion 1; discriminate_list || simplify_list_eq. by constructor.
    - iDestruct "Hb" as %Hys'. wp_send with "[]".
      { by rewrite /= Hys Hxs Hys'. }
      wp_close. by iApply "HΦ".
  Qed.

  Lemma sort_service_fg_merge_spec cmp c c1 c2 xs ys xs1 xs2 y1 w1 ys1 ys2 :
    xs ≡ₚ xs1 ++ xs2 →
    ys ≡ₚ ys1 ++ ys2 →
    Sorted R ys →
    TlRel R y1 ys →
    (∀ x, TlRel R x ys2 → R x y1 → TlRel R x ys) →
    cmp_spec I R cmp -∗
    {{{ c ↣ dual (sort_fg_tail_prot xs ys) ∗
        c1 ↣ sort_fg_tail_prot xs1 (ys1 ++ [y1]) ∗
        c2 ↣ sort_fg_tail_prot xs2 ys2 ∗ I y1 w1 }}}
      sort_service_fg_merge cmp c w1 c1 c2
    {{{ RET #(); c ↣ END? }}}.
  Proof using Type*.
    iIntros (Hxs Hys Hsort Htl Htl_le) "#Hcmp !> %Φ (Hc & Hc1 & Hc2 & HIy1) HΦ".
    iLöb as "IH" forall (c1 c2 xs1 xs2 ys y1 w1 ys1 ys2 Hxs Hys Hsort Htl Htl_le).
    wp_rec. wp_recv ([]) as "Hb".
    - wp_recv (x v) as "[%HR HIx]".
      iApply ("Hcmp" with "HIy1 HIx"); iIntros "!> [HIy1 HIx]".
      case_bool_decide.
      + wp_send. wp_send with "[$HIy1 //]".
        iApply ("IH" with "[%] [%] [%] [%] [%] Hc Hc2 Hc1 HIx HΦ").
        * by rewrite comm.
        * by rewrite assoc (comm _ ys2) Hys.
        * by apply Sorted_snoc.
        * by constructor.
        * intros x'.
          inversion 1; discriminate_list || simplify_list_eq. by constructor.
      + wp_send. wp_send with "[$HIx]".
        { iIntros "!> !%". by apply Htl_le, total_not. }
        iApply ("IH" with "[% //] [%] [%] [%] [%] Hc Hc1 Hc2 HIy1 HΦ").
        * by rewrite Hys assoc.
        * by apply Sorted_snoc, Htl_le, total_not.
        * constructor. by apply total_not.
        * intros x'.
          inversion 1; discriminate_list || simplify_list_eq. by constructor.
    - wp_send. wp_send with "[$HIy1 //]". wp_close. iDestruct "Hb" as %Hys2.
      iApply (sort_service_fg_forward_spec with "[$Hc $Hc1] HΦ").
      * done.
      * by rewrite Hys Hys2 -!assoc_L (comm _ xs2).
      * by apply Sorted_snoc.
      * intros x'.
        inversion 1; discriminate_list || simplify_list_eq. by constructor.
  Qed.

  Lemma sort_service_fg_spec cmp c :
    cmp_spec I R cmp -∗
    {{{ c ↣ dual sort_fg_prot }}}
      sort_service_fg cmp c
    {{{ RET #(); c ↣ END? }}}.
  Proof using Type*.
    iIntros "#Hcmp !> %Φ Hc HΦ". iLöb as "IH" forall (c Φ). wp_rec!. wp_recv ([]).
    - wp_recv (x1 v1) as "HIx1". wp_recv ([]).
      + wp_recv (x2 v2) as "HIx2".
        iApply (wp_fork_chan sort_fg_prot); iIntros "!>" (cy) "Hcy".
        { iApply ("IH" with "Hcy"); iIntros "!> Hcy". by wp_wait. }
        iApply (wp_fork_chan sort_fg_prot); iIntros "!>" (cz) "Hcz".
        { iApply ("IH" with "Hcz"); iIntros "!> Hcz". by wp_wait. }
        wp_send. wp_send with "[HIx1 //]". wp_send. wp_send with "[HIx2 //]".
        iApply (sort_service_fg_split_spec with "[$Hc $Hcy $Hcz]").
        iIntros "!>" (xs' xs1' xs2'); iDestruct 1 as (Hxs') "(Hc & Hcy & Hcz) /=".
        wp_recv ([]) as "Hb"; last first.
        { iDestruct "Hb" as %Hperm. by apply Permutation_nil_cons in Hperm. }
        wp_recv (x v) as "[%HR HIx]".
        iApply (sort_service_fg_merge_spec _ _ _ _ _ [] _ _ _ _ [] []
               with "Hcmp [$Hc $Hcy $Hcz $HIx]"); simpl; auto using TlRel_nil, Sorted_nil.
        by rewrite Hxs' Permutation_middle.
      + wp_send. wp_send with "[$HIx1]"; first by auto using TlRel_nil.
        wp_send. by iApply "HΦ".
    - wp_send. by iApply "HΦ".
  Qed.

  Lemma send_all_spec c xs' l xs :
    {{{ llist I l xs ∗ c ↣ sort_fg_head_prot xs' }}}
      send_all c #l
    {{{ RET #(); llist I l [] ∗ c ↣ sort_fg_head_prot (xs' ++ xs) }}}.
  Proof.
    iIntros "%Φ [Hl Hc] HΦ".
    iInduction xs as [|x xs] "IH" forall (xs').
    { wp_rec. iApply (lisnil_spec with "Hl"); iIntros "!> Hl".
      wp_pures. rewrite right_id_L. iApply "HΦ". by iFrame. }
    wp_rec. iApply (lisnil_spec with "Hl"); iIntros "!> Hl". wp_send.
    iApply (lpop_spec with "Hl"); iIntros "!>" (v) "[HIx Hl]".
    wp_send with "[HIx //]".
    iApply ("IH" with "Hl Hc"). iIntros "!> [Hl Hc]". rewrite -assoc_L.
    iApply "HΦ". iFrame.
  Qed.

  Lemma recv_all_spec c l xs ys' :
    Sorted R ys' →
    {{{ llist I l [] ∗ c ↣ sort_fg_tail_prot xs ys' }}}
      recv_all c #l
    {{{ ys, RET #(); ⌜⌜ Sorted R (ys' ++ ys) ⌝⌝ ∗
                     ⌜⌜ ys' ++ ys ≡ₚ xs ⌝⌝ ∗ llist I l ys ∗ c ↣ END! }}}.
  Proof.
    iIntros (Hsort Φ) "[Hl Hc] HΦ". iLöb as "IH" forall (xs ys' Hsort Φ).
    wp_rec!. wp_recv ([]) as "Hb".
    - wp_recv (y v) as "[%Htl HIx]".
      iApply ("IH" with "[] Hl Hc"); first by auto using Sorted_snoc.
      iIntros "!>" (ys). rewrite -!assoc_L. iDestruct 1 as (??) "[Hl Hc]".
      iApply (lcons_spec with "Hl HIx"); iIntros "!> Hl". iApply "HΦ". by iFrame.
    - wp_pures. iApply "HΦ"; iFrame. rewrite /= right_id_L; by iFrame.
  Qed.

  Lemma sort_client_fg_spec cmp l xs :
    cmp_spec I R cmp -∗
    {{{ llist I l xs }}}
      sort_client_fg cmp #l
    {{{ ys, RET #(); ⌜⌜ Sorted R ys ⌝⌝ ∗ ⌜⌜ ys ≡ₚ xs ⌝⌝ ∗ llist I l ys }}}.
  Proof using Type*.
    iIntros "#Hcmp !> %Φ Hl HΦ". wp_rec.
    iApply (wp_fork_chan sort_fg_prot); iIntros "!>" (c) "Hc".
    { iApply (sort_service_fg_spec with "Hcmp Hc"); iIntros "!> Hc". by wp_wait. }
    iApply (send_all_spec with "[$Hl $Hc]"); iIntros "!> [Hl Hc]". wp_send.
    iApply (recv_all_spec with "[$Hl $Hc]"); [done|].
    iIntros "!>" (ys) "/=". iDestruct 1 as (??) "[Hk Hc]". wp_close.
    iApply "HΦ". by iFrame.
  Qed.
End sort_fg_inner.
