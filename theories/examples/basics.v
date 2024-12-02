From dlfactris.session_logic Require Export proofmode.
Import TImp TImp.notations.

(** From https://gitlab.mpi-sws.org/iris/actris/-/blob/master/theories/examples/basics.v *)
(** Basic *)
Definition prog : val := λ: <>,
  let: "c" := fork_chan (λ: "c'", send "c'" #42;; close "c'") in
  let: "x" := recv "c" in wait "c";; "x".

Definition prog_prot : prot :=
  <?> MSG #42 ; END?.

Lemma prog_spec : {{{ emp }}} prog #() {{{ RET #42; emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec. iApply (wp_fork_chan prog_prot); iIntros "!> %c Hc".
  { wp_send. by wp_close. }
  wp_recv. wp_wait!. by iApply "HΦ".
Qed.

(** Tranfering References *)
Definition prog_ref : val := λ: <>,
  let: "c" := fork_chan (λ: "c'", send "c'" (Alloc #42);; close "c'") in
  let: "l" := recv "c" in let: "x" := ! "l" in Free "l";; wait "c";; "x".

Definition prot_ref : prot :=
  <? (l : loc)> MSG #l {{ l ↦ #42 }}; END?.

Lemma prog_ref_spec : {{{ emp }}} prog_ref #() {{{ RET #42; emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec. iApply (wp_fork_chan prot_ref); iIntros "!> %c Hc".
  { wp_alloc l as "Hl". wp_send with "[Hl//]". by wp_close. }
  wp_recv (l) as "Hl". wp_load. wp_free. wp_wait!. by iApply "HΦ".
Qed.

(** Delegation, i.e. transfering channels *)
Definition prog_del : val := λ: <>,
  let: "c1" := fork_chan (λ: "c1'",
    let: "c2" := fork_chan (λ: "c2'", send "c1'" "c2'";; close "c1'") in
    send "c2" #42;; close "c2") in
  let: "c2'" := recv "c1" in wait "c1";;
  let: "x" := recv "c2'" in wait "c2'";; "x".

Definition prot_del : prot :=
  <? c> MSG c {{ c ↣ prog_prot }}; END?.

Lemma prog_del_spec : {{{ emp }}} prog_del #() {{{ RET #42; emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec.
  iApply (wp_fork_chan prot_del); iIntros "!>" (c) "Hc".
  { iApply (wp_fork_chan (dual prog_prot) with "[Hc]"); iIntros "!>" (c2) "Hc2".
    + wp_send with "[$Hc2]". by wp_close.
    + wp_send. by wp_close. }
  wp_recv (c2) as "Hc2". wp_wait. wp_recv. wp_wait!. by iApply "HΦ".
Qed.

(** Dependent protocols *)
Definition prog_dep : val := λ: <>,
  let: "c" := fork_chan (λ: "c'",
    let: "x" := recv "c'" in send "c'" ("x" + #2);; close "c'") in
  send "c" #40;; let: "x" := recv "c" in wait "c";; "x".

Definition prot_dep : prot :=
  <! (x : Z)> MSG #x; <?> MSG #(x + 2); END?.

Lemma prog_dep_spec : {{{ emp }}} prog_dep #() {{{ RET #42; emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec.
  iApply (wp_fork_chan prot_dep); iIntros "!>" (c) "Hc".
  - wp_recv (x) as "_". wp_send with "[//]". by wp_close.
  - wp_send with "[//]". wp_recv. wp_wait!. by iApply "HΦ".
Qed.

Definition prog_dep_ref : val := λ: <>,
  let: "c" := fork_chan (λ: "c'",
    let: "l" := recv "c'" in "l" <- !"l" + #2;; send "c'" #();; close "c'") in
  let: "l" := Alloc #40 in send "c" "l";; recv "c";;
  let: "x" := !"l" in Free "l";; wait "c";; "x".

Definition prot_dep_ref : prot :=
  <! (l : loc) (x : Z)> MSG #l {{ l ↦ #x }};
  <?> MSG #() {{ l ↦ #(x + 2) }};
  END?.

Lemma prog_dep_ref_spec : {{{ emp }}} prog_dep_ref #() {{{ RET #42; emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec.
  iApply (wp_fork_chan prot_dep_ref); iIntros "!>" (c) "Hc".
  - wp_recv (l x) as "Hl". wp_load. wp_store. wp_send with "[$Hl]". by wp_close.
  - wp_alloc l as "Hl". wp_send with "[$Hl]". wp_recv as "Hl". wp_load.
    wp_free. wp_wait!. by iApply "HΦ".
Qed.

Definition prog_dep_del : val := λ: <>,
  let: "c1" := fork_chan (λ: "c1'",
    let: "cc2" := fork_chan (λ: "cc2", send "c1'" "cc2";; close "c1'") in
    let: "x" := recv "cc2" in send "cc2" ("x" + #2);; close "cc2") in
  let: "c2'" := recv "c1" in send "c2'" #40;;
  let: "x" := recv "c2'" in wait "c2'";; wait "c1";; "x".

Definition prot_dep_del : prot :=
  <? c> MSG c {{ c ↣ prot_dep }}; END?.

Lemma prog_dep_del_spec : {{{ emp }}} prog_dep_del #() {{{ RET #42; emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec.
  iApply (wp_fork_chan prot_dep_del); iIntros "!>" (c) "Hc1".
  - iApply (wp_fork_chan (dual prot_dep) with "[Hc1]"); iIntros "!>" (c2) "Hc2".
    + wp_send with "[$Hc2]". by wp_close.
    + wp_recv. wp_send. by wp_close.
  - wp_recv (c2) as "Hc2". wp_send with "[//]". wp_recv. wp_wait. wp_wait!.
    by iApply "HΦ".
Qed.

Definition prog_dep_del_2 : val := λ: <>,
  let: "c1" := fork_chan (λ: "c1'",
    let: "c2" := recv "c1'" in
    send "c2" #40;; send "c1'" #();; close "c1'") in
  let: "c2" := fork_chan (λ: "c2'",
    let: "x" := recv "c2'" in send "c2'" ("x" + #2);; close "c2'") in
  send "c1" "c2";; recv "c1";; wait "c1";; let: "x" := recv "c2" in
  wait "c2";; "x".

Definition prot_dep_del_2 : prot :=
  <! c> MSG c {{ c ↣ prot_dep }};
  <?> MSG #() {{ c ↣ prog_prot }};
  END?.

Lemma prog_dep_del_2_spec : {{{ emp }}} prog_dep_del_2 #() {{{ RET #42; emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec.
  iApply (wp_fork_chan prot_dep_del_2); iIntros "!>" (c) "Hc".
  { wp_recv (c2) as "Hc2". wp_send. wp_send with "[$Hc2]". by wp_close. }
  iApply (wp_fork_chan prot_dep); iIntros "!>" (c2) "Hc2".
  { wp_recv. wp_send. by wp_close. }
  wp_send with "[$Hc2]". wp_recv as "Hc2". wp_wait. wp_recv. wp_wait!.
  by iApply "HΦ".
Qed.

Definition prog_dep_del_3 : val := λ: <>,
  let: "c1" := fork_chan (λ: "c1'",
    let: "c" := recv "c1'" in let: "y" := recv "c1'" in
    send "c" "y";; send "c1'" #();; close "c1'") in
  let: "c2" := fork_chan (λ: "c2'",
    let: "x" := recv "c2'" in send "c2'" ("x" + #2);; close "c2'") in
  send "c1" "c2";; send "c1" #40;;
  recv "c1";; wait "c1";;
  let: "x" := recv "c2" in wait "c2";; "x".

Definition prot_dep_del_3 : prot :=
  <! c> MSG c {{ c ↣ prot_dep }};
  <! (y : Z)> MSG #y;
  <?> MSG #() {{ c ↣ <?> MSG #(y + 2); END? }};
  END?.

Lemma prog_dep_del_3_spec : {{{ emp }}} prog_dep_del_3 #() {{{ RET #42; emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec.
  iApply (wp_fork_chan prot_dep_del_3); iIntros "!>" (c1) "Hc1".
  { wp_recv (c2) as "Hc2". wp_recv. wp_send.
    wp_send with "[$Hc2]". by wp_close. }
  iApply (wp_fork_chan prot_dep); iIntros "!>" (c2) "Hc2".
  { wp_recv.  wp_send. by wp_close. }
  wp_send with "[$Hc2]". wp_send. wp_recv as "Hc2".
  wp_wait. wp_recv. wp_wait!. by iApply "HΦ".
Qed.

(** Loops *)
Definition prog_loop : val := λ: <>,
  let: "c" := fork_chan (rec: "go" "c'" :=
    if: recv "c'"
    then let: "x" := recv "c'" in send "c'" ("x" + #2);; "go" "c'"
    else wait "c'") in
  send "c" #true;;
  send "c" #18;;
  let: "x1" := recv "c" in
  send "c" #true;;
  send "c" #20;;
  let: "x2" := recv "c" in
  send "c" #false;;
  close "c";;
  "x1" + "x2".

Definition prot_loop_aux (rec : prot) : prot :=
  (<! (x : Z)> MSG #x; <?> MSG #(x + 2); rec) <+> END!.
Global Instance prot_loop_contractive : Contractive prot_loop_aux.
Proof. solve_prot_contractive. Qed.
Definition prot_loop : prot := fixpoint prot_loop_aux.
Global Instance prot_loop_unfold :
  ProtUnfold prot_loop (prot_loop_aux prot_loop).
Proof. apply prot_unfold_eq, (fixpoint_unfold _). Qed.

Lemma prog_loop_spec : {{{ emp }}} prog_loop #() {{{ RET #42; emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec.
  iApply (wp_fork_chan prot_loop); iIntros "!> %c Hc".
  - iLöb as "IH". wp_recv (b). destruct b.
    + wp_recv (x). wp_send. by iApply "IH".
    + wp_pures. by wp_wait.
  - wp_send. wp_send. wp_recv. wp_send. wp_send. wp_recv. wp_send. wp_close!.
    by iApply "HΦ".
Qed.

(** Transfering higher-order functions *)
Definition prog_fun : val := λ: <>,
  let: "c" := fork_chan (λ: "c'",
    let: "f" := recv "c'" in send "c'" (λ: <>, "f" #() + #2)) in
  let: "r" := Alloc #40 in
  send "c" (λ: <>, !"r");;
  recv "c" #().

Definition prog_fun_del : val := λ: <>,
  let: "c1" := fork_chan (λ: "c1'",
    let: "c2" := fork_chan (λ: "c2'",
      let: "x" := recv "c2'" in send "c2'" ("x" + #2);; close "c2'") in
    let: "x" := recv "c1'" in
    send "c1'"
         (λ: <>, send "c2" "x";;
                  let: "y" := recv "c2" in wait "c2";; "y");; close "c1'") in
  send "c1" #40;; let: "f" := recv "c1" in wait "c1";; "f" #().

Definition prot_fun_del : prot :=
  <! (x : Z)> MSG #x ;
  <? f> MSG f {{ WP f #() {{ v, ⌜⌜ v = #(x + 2) ⌝⌝ }} }}; END?.

Lemma prog_fun_del_spec : {{{ emp }}} prog_fun_del #() {{{ RET #42; emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec.
  iApply (wp_fork_chan prot_fun_del); iIntros "!>" (c) "Hc".
  - iApply (wp_fork_chan prot_dep); iIntros "!>" (c2) "Hc2".
    { wp_rec. wp_recv (x). wp_send. by wp_close. }
    wp_recv (x). wp_send with "[Hc2]".
    { wp_rec. wp_send. wp_recv. by wp_wait!. }
    by wp_close.
  - wp_send. wp_recv (f) as "Hf". wp_wait!. iApply "Hf". by iApply "HΦ".
Qed.
