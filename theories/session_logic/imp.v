From dlfactris.session_logic Require Export sessions.

Module Imp.
  Definition fork_chan : val := λ: "f",                                          (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=f0b10cb3 *)
    Alloc $ Ses.fork_chan (λ: "c2", "f" (Alloc "c2")).

  Definition recv : val := λ: "c",
    let: '("v","r") := Ses.recv !"c" in
    "c" <- "r";; "v".

  Definition send : val := λ: "c" "v",
    "c" <- Ses.send (!"c") "v".

  Definition close : val := λ: "c",
    Ses.close !"c";; Free "c".

  Definition wait : val := λ: "c",
    Ses.wait !"c";; Free  "c".

  Notation prot := Ses.prot.
  Notation dual := Ses.dual.
  Notation end_prot := Ses.end_prot.
  Notation msg_prot := Ses.msg_prot.
  Notation subprot := Ses.subprot.

  Definition own_chan (c : val) (p : aMiniProt) : aProp :=
    ∃ (l : loc) ch, ⌜⌜ c = #l ⌝⌝ ∗ l ↦ ch ∗ Ses.own_chan ch p.

  Module Import notations.
    Notation "p ⊑ q" := (subprot p q) : bi_scope.
    Notation "c ↣ p" := (own_chan c p) : bi_scope.
  End notations.

  Notation subprot_refl := Ses.subprot_refl.
  Notation subprot_trans := Ses.subprot_trans.
  Notation subprot_dual := Ses.subprot_dual.

  Global Instance own_chan_contractive ch : Contractive (own_chan ch).
  Proof. solve_contractive. Qed.
  Global Instance own_chan_ne ch : NonExpansive (own_chan ch).
  Proof. solve_proper. Qed.
  Global Instance own_chan_proper ch : Proper ((≡) ==> (≡)) (own_chan ch).
  Proof. solve_proper. Qed.

  Lemma own_chan_subprot c p1 p2 : c ↣ p1 -∗ ▷ (p1 ⊑ p2) -∗ c ↣ p2.
  Proof.
    iIntros "(%l & %ch & -> & Hl & Hch) Hsp". iExists l, ch.
    iSplit; [done|]. iFrame. by iApply (Ses.own_chan_subprot with "Hch").
  Qed.

  Lemma wp_fork_chan p (f : val) :                                               (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=a3e914ff *)
    ▷ (∀ c, c ↣ dual p -∗ WP f c {{ _, emp }}) -∗
    WP fork_chan f {{ c, c ↣ p }}.
  Proof.
    iIntros "Hf". wp_rec!. iApply (Ses.wp_fork_chan with "[Hf]").
    { iIntros "!>" (c) "Hc". wp_alloc l as "Hl". iApply "Hf".
      iExists l, c. by iFrame. }
    iIntros "!>" (c) "Hc". wp_alloc l as "Hl". by iFrame.
  Qed.

  Lemma wp_recv {A} c (v : A → val) (P : A → aProp) (p : A → aMiniProt) :
    c ↣ msg_prot ARecv v P p -∗
    WP recv c {{ w, ∃ x, ⌜⌜ w = v x ⌝⌝ ∗ c ↣ p x ∗ P x }}.
  Proof.
    iIntros "(%l & %ch & -> & Hl & Hch)". wp_rec!. wp_load.
    iApply (Ses.wp_recv with "Hch"); iIntros "!>" (ch' x) "[Hch' HP]".
    wp_store!. by iFrame.
  Qed.

  Lemma wp_send {A} c (v : A → val) (P : A → aProp) (p : A → aMiniProt) x :
    c ↣ msg_prot ASend v P p -∗ P x -∗
    WP send c (v x) {{ v, ⌜⌜ v = #() ⌝⌝ ∗ c ↣ p x }}.
  Proof.
    iIntros "(%l & %ch & -> & Hl & Hch) HP". wp_rec!. wp_load.
    iApply (Ses.wp_send with "Hch HP"); iIntros "!>" (ch') "Hch'".
    wp_store. by iFrame.
  Qed.

  Lemma wp_wait c P :
    c ↣ end_prot ARecv P -∗ WP wait c {{ v, ⌜⌜ v = #() ⌝⌝ ∗ P }}.
  Proof.
    iIntros "(%l & %ch & -> & Hl & Hch)". wp_rec!. wp_load.
    iApply (Ses.wp_wait with "Hch"); iIntros "!> HP". wp_free. by iFrame.
  Qed.

  Lemma wp_close c P :
    c ↣ end_prot ASend P -∗ P -∗ WP close c {{ v, ⌜⌜ v = #() ⌝⌝ }}.
  Proof.
    iIntros "(%l & %ch & -> & Hl & Hch) HP". wp_rec!. wp_load.
    iApply (Ses.wp_close with "Hch HP"); iNext. by wp_free.
  Qed.

  Global Opaque fork_chan recv send close wait.
  Global Opaque own_chan.
End Imp.
