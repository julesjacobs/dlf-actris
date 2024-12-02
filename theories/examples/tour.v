From dlfactris.session_logic Require Export proofmode.
From dlfactris.examples Require Import assert.
Import TImp TImp.notations.

Definition prog1 : val := λ: <>,                                                 (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=3777478b *)
  let: "c1" := fork_chan (λ: "c2", send "c2" (recv "c2" + #1);; close "c2") in
  send "c1" #1;; let: "x" := recv "c1" in assert: ("x" = #2);; wait "c1".

Definition prog1_prot1 : prot :=                                                 (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=066585fc *)
  <!> MSG #1 ; <?> MSG #2; END?.

Lemma prog1_spec1 : {{{ emp }}} prog1 #() {{{ RET #(); emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec. iApply (wp_fork_chan prog1_prot1);
    iIntros "!> %c Hc".
  { wp_recv. wp_send. by wp_close. }
  wp_send. wp_recv. iApply wp_assert. wp_pures. iSplit; [done|].
  iIntros "!>". wp_wait. by iApply "HΦ".
Qed.

Definition prog1_prot2 : prot :=                                                 (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=a945065d *)
  <!(x:Z)> MSG #x ; <?> MSG #(x+1); END?.

Lemma prog1_spec2 : {{{ emp }}} prog1 #() {{{ RET #(); emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec. iApply (wp_fork_chan prog1_prot2);
    iIntros "!> %c Hc".
  { wp_recv. wp_send. by wp_close. }
  wp_send. wp_recv. iApply wp_assert. wp_pures. iSplit; [done|].
  iIntros "!>". wp_wait. by iApply "HΦ".
Qed.

Definition prog2 (e:val) : val := λ: "c",                                        (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=a00e1f9c *)
  let: "n" := recv "c" in
  if: "n" < #5 then close "c"
  else send "c" ("n" - #5);; e "c".

Definition prog2_prot (p:prot) : prot :=                                         (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=8bb83953 *)
  <?(n:Z)> MSG #n ; if bool_decide (n < 5)%Z then END! else <!> MSG #(n-5); p.

Lemma prog2_spec c (e:val) p :
  (∀ c, {{{ c ↣ p }}} e c {{{ RET #(); emp }}}) →
  {{{ c ↣ prog2_prot p }}} (prog2 e) c {{{ RET #(); emp }}}.
Proof.
  iIntros (He). iIntros (Φ) "Hc HΦ". wp_rec.
  wp_recv. wp_pures. case_bool_decide.
  - wp_close. by iApply "HΦ".
  - wp_send. by iApply (He with "Hc").
Qed.

Definition prog3 : val := λ: <>,                                                 (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=c1c2e11f *)
  let: "c1" := fork_chan (λ: "c2", let: "l" := recv "c2" in
                                   "l" <- (!"l" + #1);; close "c2") in
  let: "l" := Alloc #1 in send "c1" "l";; wait "c1";;
  let: "x" := !"l" in assert: ("x" = #2);; Free "l".

Definition prog3_prot : prot :=                                                  (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=cd546ffb *)
  <!(l:loc)(n:Z)> MSG #l {{ l ↦ #n }}; END?{{ l ↦ #(n+1) }}.

Lemma prog3_spec : {{{ emp }}} prog3 #() {{{ RET #(); emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec. iApply (wp_fork_chan prog3_prot);
    iIntros "!> %c Hc".
  { wp_rec. wp_recv as "Hl". wp_load. wp_store.
    iDestruct (own_chan_subprot with "Hc [Hl]") as "Hc".
    { iFrame. by eauto. }
    by wp_close. }
  wp_alloc l as "Hl". wp_send with "[$Hl]".
  iApply (wp_wait with "Hc"); iIntros "!> Hc".
  wp_load. iApply wp_assert. wp_pures. iSplit; [done|].
  iIntros "!>". wp_free. by iApply "HΦ".
Qed.

Definition prog4 : val := λ: <>,                                                 (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=5989934c *)
  let: "l" := Alloc #1 in
  let: "c1" := fork_chan (λ: "c2", "l" <- (!"l" + #1);; close "c2") in
  wait "c1";; let: "x" := !"l" in assert: ("x" = #2);; Free "l".

Definition prog4_prot (l:loc) : prot :=                                          (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=8ab3e3f1 *)
  END? {{ l ↦ #2 }}.

Lemma prog4_spec : {{{ emp }}} prog4 #() {{{ RET #(); emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec. wp_alloc l as "Hl".
  iApply (wp_fork_chan (prog4_prot l) with "[Hl]"); iIntros "!> %c Hc".
  { wp_load. wp_store.
    iDestruct (own_chan_subprot with "Hc [Hl]") as "Hc".
    { iApply subprot_dual. iFrame. by eauto. }
    by wp_close. }
  iApply (wp_wait with "Hc"); iIntros "!> Hc".
  wp_load. iApply wp_assert. wp_pures. iSplit; [done|].
  iIntros "!>". wp_pures. wp_free. by iApply "HΦ".
Qed.

Definition prog5 : val := λ: <>,                                                 (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=a3d68ef4 *)
  let: "d1" :=
    fork_chan (λ: "d2",
                 let: "c1" := recv "d2" in
                 let: "x" := recv "c1" in
                 assert: ("x" = #2);; close "d2") in
  let: "c1" :=
    fork_chan (λ: "c2", send "c2" #2;; wait "c2") in
  send "d1" "c1";; wait "d1";; close "c1".

Definition prog5_prot1 : prot :=                                                 (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=ce5ae00c *)
  <?> MSG #2 ; END!.
Definition prog5_prot2 : prot :=                                                 (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=039f4f5c *)
  <!(c:val)> MSG c {{ c ↣ prog5_prot1 }} ; END? {{ c ↣ END! }}.

Lemma prog5_spec : {{{ emp }}} prog5 #() {{{ RET #(); emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec.
  iApply (wp_fork_chan prog5_prot2); iIntros "!> %d Hd".
  { wp_rec. wp_recv (c) as "Hc". wp_recv.
    iApply wp_assert. wp_pures. iSplit; [done|].
    iIntros "!>". wp_pures.
    iDestruct (own_chan_subprot _ _ END!%prot with "Hd [Hc]") as "Hd".
    { iIntros "!>". by iFrame "Hc". }
    by wp_close. }
  iApply (wp_fork_chan prog5_prot1); iIntros "!> %c Hc".
  { wp_rec. wp_send. by wp_wait. }
  wp_send with "[$Hc]". iApply (wp_wait with "Hd"); iIntros "!>Hc".
  wp_close. by iApply "HΦ".
Qed.

Definition prog6 : val := λ: <>,                                                 (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=9503cac7 *)
  let: "d1" :=
    fork_chan (λ: "d2",
                 let: "c1" := !(recv "d2") in
                 let: "x" := recv "c1" in
                 assert: ("x" = #2);; close "d2") in
  let: "l" :=
    Alloc (fork_chan (λ: "c2", send "c2" #2;; wait "c2")) in
  send "d1" "l";; wait "d1";; close (!"l");; Free "l".

Definition prog6_prot2 : prot :=                                                 (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=1e08fe1e *)
  <!(l:loc)(c:val)> MSG #l {{ l ↦ c ∗ c ↣ <?> MSG #2 ; END! }} ;
  END? {{ l ↦ c ∗ c ↣ END! }}.

Lemma prog6_spec : {{{ emp }}} prog6 #() {{{ RET #(); emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec.
  iApply (wp_fork_chan prog6_prot2); iIntros "!> %d Hd".
  { wp_rec. wp_recv (l c) as "[Hl Hc]". wp_load. wp_recv.
    iApply wp_assert. wp_pures. iSplit; [done|].
    iIntros "!>". wp_pures.
    iDestruct (own_chan_subprot _ _ END!%prot with "Hd [Hl Hc]") as "Hd".
    { iIntros "!>". by iFrame "Hl Hc". }
    by wp_close. }
  iApply (wp_fork_chan prog5_prot1); iIntros "!> %c Hc".
  { wp_rec. wp_send. by wp_wait. }
  wp_alloc l as "Hl". wp_send with "[$Hl $Hc]".
  iApply (wp_wait with "Hd"); iIntros "!>[Hl Hc]".
  wp_load. wp_close. wp_free. by iApply "HΦ".
Qed.

Definition prog7 (e : val): val := λ: <>,                                        (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=ad1e6797 *)
  let: "c1" :=
    fork_chan (λ: "c2",
                 let: "f" := recv "c2" in
                 send "c2" ("f" #());;
                 close "c2") in
  e #().

Definition prog7_prot : prot :=                                                  (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=c66e8926 *)
  <!(f:val) (Φ:val → aProp)> MSG f {{ (WP f #() {{ Φ }}) }};
  <?(v:val)> MSG v {{ Φ v }}; END?.

Lemma prog7_spec (e : val) :
  (∀ c, {{{ c ↣ prog7_prot }}} e #() {{{ RET #(); emp }}}) →
  {{{ emp }}} (prog7 e) #() {{{ RET #(); emp }}}.
Proof.
  iIntros (HE Φ) "_ HΦ". wp_rec.
  iApply (wp_fork_chan prog7_prot); iIntros "!> %c Hc".
  { wp_rec. wp_recv (f) as "Hf".
    iApply "Hf"; iIntros "!>" (v) "HΦ".
    wp_send with "[$HΦ]". by wp_close. }
  by iApply (HE with "Hc").
Qed.
