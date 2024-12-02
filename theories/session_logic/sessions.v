From dlfactris.session_logic Require Export sub.

Module Ses.
  Definition fork_chan : val := Sub.fork_chan.
  Definition recv : val := Sub.recv.
  Definition send : val := λ: "c" "v",
    Sub.fork_chan (λ: "c'", Sub.send "c" ("v", "c'")).
  Definition close : val := λ: "c", Sub.send "c" #().
  Definition wait := Sub.recv.

  Notation prot := Sub.prot.
  Notation dual := Sub.dual.
  Notation subprot := Sub.subprot.
  Notation own_chan := Sub.own_chan.

  Module Import notations := Sub.notations.

  Notation subprot_refl := Sub.subprot_refl.
  Notation subprot_trans := Sub.subprot_trans.
  Notation subprot_dual := Sub.subprot_dual.
  Notation own_chan_subprot := Sub.own_chan_subprot.

  Definition end_prot (a : action) (P : aProp) : prot :=                         (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=5973985d *)
    MiniProt a (λ r, ⌜⌜ r = #() ⌝⌝ ∗ P)%I.
  Global Instance: Params (@end_prot) 1 := {}.

  Definition msg_prot (a : action) {A}                                           (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=423aeac8 *)
      (v : A → val) (P : A → aProp) (p : A → prot) : prot :=
    MiniProt a (λ r, ∃ x c,
      ⌜⌜ r = (v x, c)%V ⌝⌝ ∗ P x ∗
      Sub.own_chan c (if a is ARecv then p x else dual (p x)))%I.
  Global Instance: Params (@msg_prot) 2 := {}.

  Global Instance msg_end_ne a : NonExpansive (end_prot a).
  Proof. solve_proper. Qed.
  Global Instance msg_end_proper a : Proper ((≡) ==> (≡)) (end_prot a).
  Proof. apply: ne_proper. Qed.

  Global Instance msg_prot_contractive {A} a n :
    Proper (pointwise_relation A (=) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist_later n) ==> dist n) (msg_prot a).
  Proof. solve_contractive. Qed.
  Global Instance msg_prot_ne {A} a n :
    Proper (pointwise_relation A (=) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==> dist n) (msg_prot a).
  Proof. solve_proper. Qed.
  Global Instance msg_prot_proper {A} a :
    Proper (pointwise_relation A (=) ==>
            pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==> (≡)) (msg_prot a).
  Proof.
    intros v1 v2 Hveq Φ1 Φ2 HΦeq p1 p2 Hpeq; apply equiv_dist=> n.
    f_equiv; [done|..]=> x; apply equiv_dist; auto.
  Qed.

  (** WPs for session channels *)
  Lemma wp_fork_chan p (f : val) :
    ▷ (∀ c, c ↣ dual p -∗ WP f c {{ _, emp }}) -∗
    WP fork_chan f {{ c, c ↣ p }}.
  Proof. apply Sub.wp_fork_chan. Qed.

  Lemma wp_recv {A} c (v : A → val) (P : A → aProp) (p : A → aMiniProt) :
    c ↣ msg_prot ARecv v P p -∗
    WP recv c {{ w, ∃ c', ∃ x, ⌜⌜ w = (v x, c')%V ⌝⌝ ∗ c' ↣ p x ∗ P x }}.
  Proof.
    iIntros "Hc". iApply (Sub.wp_recv with "Hc"); iIntros (x c') "!> [HP Hc']".
    eauto with iFrame.
  Qed.

  Lemma wp_send {A} c (v : A → val) (P : A → aProp) (p : A → aMiniProt) x :
    c ↣ msg_prot ASend v P p -∗ P x -∗
    WP send c (v x) {{ c', c' ↣ p x }}.
  Proof.
    iIntros "Hc HP". wp_rec. iApply Sub.wp_fork_chan; iIntros "!>" (c') "Hc'".
    wp_pures. iApply (Sub.wp_send with "Hc [-]"); last done.
    iExists x, c'. by iFrame.
  Qed.

  Lemma wp_wait c P :
    c ↣ end_prot ARecv P -∗ WP wait c {{ v, ⌜⌜ v = #() ⌝⌝ ∗ P }}.
  Proof. iIntros "Hc". iApply (Sub.wp_recv with "Hc"). Qed.

  Lemma wp_close c P :
    c ↣ end_prot ASend P -∗ P -∗ WP close c {{ v, ⌜⌜ v = #() ⌝⌝ }}.
  Proof. iIntros "Hc HP". wp_rec. iApply (Sub.wp_send with "Hc"). by iFrame. Qed.

  Global Opaque fork_chan recv send close wait.
  Global Typeclasses Opaque end_prot msg_prot.
End Ses.
