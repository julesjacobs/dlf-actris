From dlfactris.session_logic Require Export tele_imp.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
Import TImp TImp.notations.

(** Tactics for proving contractiveness of protocols *)
Ltac f_dist_le :=
  match goal with
  | H : _ ≡{?n}≡ _ |- _ ≡{?n'}≡ _ => apply (dist_le n); [apply H|lia]
  end.

Ltac solve_prot_contractive :=
  solve_proper_core ltac:(fun _ =>
    first [f_contractive; simpl in * | f_equiv | f_dist_le]).

(** Let [auto] use reflexivity of subprot *)
Global Hint Extern 0 (environments.envs_entails _ (?x ⊑ ?y)) =>
  first [is_evar x; fail 1 | is_evar y; fail 1|iApply subprot_refl] : core.

(** * Normalization of protocols *)
Class ActionDualIf (d : bool) (a1 a2 : action) :=
  { dual_action_if : a2 = if d then action_dual a1 else a1 }.
Global Hint Mode ActionDualIf ! ! - : typeclass_instances.

Global Instance action_dual_if_false a : ActionDualIf false a a.
Proof. by constructor. Qed.
Global Instance action_dual_if_true_send : ActionDualIf true ASend ARecv.
Proof. by constructor. Qed.
Global Instance action_dual_if_true_recv : ActionDualIf true ARecv ASend.
Proof. by constructor. Qed.

Class ProtNormalize (d : bool) (p q : aMiniProt) :=
  { prot_normalize : ⊢ (if d then dual p else p) ⊑ q }.
Global Hint Mode ProtNormalize ! ! - : typeclass_instances.

Notation ProtUnfold p1 p2 :=
  (∀ d q, ProtNormalize d p2 q → ProtNormalize d p1 q).

Class MsgNormalize (d : bool) (a : action) (m1 m2 : msg) :=
  { msg_normalize :
      ProtNormalize d (<a> m1) (<(if d then action_dual a else a)> m2) }.
Global Hint Mode MsgNormalize ! ! ! - : typeclass_instances.

Class MsgTele {TT : tele} (m : msg)
    (tv : TT -t> val) (tP : TT -t> aProp) (tp : TT -t> aMiniProt) :=
  { msg_tele :
     m ≡ (∃.. x, MSG tele_app tv x {{ tele_app tP x }}; tele_app tp x)%msg }.
Global Hint Mode MsgTele - ! - - - : typeclass_instances.

Section classes.
  Implicit Types TT : tele.
  Implicit Types p : aMiniProt.
  Implicit Types m : msg.
  Implicit Types P : aProp.

  (** The instances below make it possible to use the tactics [iIntros],
  [iExist], [iSplitL]/[iSplitR], [iFrame] and [iModIntro] on [subprot] goals. *)
  Global Instance from_wand_end_recv P :
    TCIf (TCEq P emp%I) False TCTrue →
    FromWand (END? {{ P }} ⊑ END?) P (END? ⊑ END?) | 10.
  Proof. intros _. rewrite /FromWand. iApply subprot_end_elim_l. Qed.
  Global Instance from_wand_end_send P :
    TCIf (TCEq P emp%I) False TCTrue →
    FromWand (END! ⊑ END! {{ P }}) P (END! ⊑ END!) | 11.
  Proof. intros _. rewrite /FromWand. iApply subprot_end_elim_r. Qed.

  Global Instance frame_end_recv q R P Q1 Q2 :
    Frame q R Q1 Q2 →
    Frame q R (END? {{ P }} ⊑ END? {{ Q1 }}) (END? {{ P }} ⊑ END? {{ Q2 }}) | 10.
  Proof.
    rewrite /Frame /=. iIntros (HP) "[HR H]".
    iApply (subprot_trans with "H"). iApply subprot_end_elim_l.
    iIntros "HQ". iApply subprot_end_intro_r. iApply HP; iFrame.
  Qed.
  Global Instance frame_end_send q R P1 P2 Q :
    Frame q R P1 P2 →
    Frame q R (END! {{ P1 }} ⊑ END! {{ Q }}) (END! {{ P2 }} ⊑ END! {{ Q }}) | 10.
  Proof.
    rewrite /Frame /=. iIntros (HP) "[HR H]".
    iApply (subprot_trans with "[HR] H"). iApply subprot_end_elim_r.
    iIntros "HQ". iApply subprot_end_intro_l. iApply HP; iFrame.
  Qed.
  Global Instance from_sep_end_recv P Q :
    FromSep (END? {{ P }} ⊑ END? {{ Q }}) Q (END? {{ P }} ⊑ END?) | 11.
  Proof. rewrite /FromSep. by iIntros "[$ H]". Qed.
  Global Instance from_sep_end_send P Q :
    FromSep (END! {{ P }} ⊑ END! {{ Q }}) P (END! ⊑ END! {{ Q }}) | 10.
  Proof. rewrite /FromSep. by iIntros "[$ H]". Qed.

  Global Instance from_forall_recv {A} (m1 : A → msg) m2 name :
    AsIdentName m1 name →
    FromForall (msg_prot ARecv (msg_exist m1) ⊑ (<?> m2))
               (λ x, (<?> m1 x) ⊑ (<?> m2))%I name | 10.
  Proof. intros _. apply subprot_exist_elim_l. Qed.
  Global Instance rrom_forall_tele_recv {TT : tele} (m1 : TT → msg) m2 name :
    AsIdentName m1 name →
    FromForall (msg_prot ARecv (msg_texist m1) ⊑ (<?> m2))
               (λ x, (<?> m1 x) ⊑ (<?> m2))%I name | 11.
  Proof. intros _. apply subprot_texist_elim_l. Qed.
  Global Instance from_forall_send {A} m1 (m2 : A → msg) name :
    AsIdentName m2 name →
    FromForall ((<!> m1) ⊑ msg_prot ASend (msg_exist m2))
               (λ x, (<!> m1) ⊑ (<!> m2 x))%I name | 20.
  Proof. intros _. apply subprot_exist_elim_r. Qed.
  Global Instance from_forall_tele_send {TT : tele} m1 (m2 : TT → msg) name :
    AsIdentName m2 name →
    FromForall ((<!> m1) ⊑ msg_prot ASend (msg_texist m2))
               (λ x, (<!> m1) ⊑ (<!> m2 x))%I name | 21.
  Proof. intros _. rewrite /FromForall. iApply subprot_texist_elim_r. Qed.

  Global Instance from_wand_recv m v P p :
    TCIf (TCEq P emp%I) False TCTrue →
    FromWand ((<?> MSG v {{ P }}; p) ⊑ (<?> m)) P ((<?> MSG v; p) ⊑ (<?> m)) | 10.
  Proof. intros _. apply subprot_payload_elim_l. Qed.
  Global Instance from_wand_send m v P p :
    TCIf (TCEq P emp%I) False TCTrue →
    FromWand ((<!> m) ⊑ (<!> MSG v {{ P }}; p)) P ((<!> m) ⊑ (<!> MSG v; p)) | 11.
  Proof. intros _. apply subprot_payload_elim_r. Qed.

  Global Instance from_exist_send {A} (m : A → msg) p :
    FromExist ((<! x> m x) ⊑ p) (λ a, (<!> m a) ⊑ p)%I | 10.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (subprot_trans with "[] H"). iApply subprot_exist_intro_l.
  Qed.
  Global Instance from_exist_tele_send {TT : tele} (m : TT → msg) p :
    FromExist ((<!.. x> m x) ⊑ p) (λ a, (<!> m a) ⊑ p)%I | 11.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (subprot_trans with "[] H"). iApply subprot_texist_intro_l.
  Qed.
  Global Instance from_exist_recv {A} (m : A → msg) p :
    FromExist (p ⊑ <? x> m x) (λ a, p ⊑ (<?> m a))%I | 20.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (subprot_trans with "H"). iApply subprot_exist_intro_r.
  Qed.
  Global Instance from_exist_tele_recv {TT : tele} (m : TT → msg) p :
    FromExist (p ⊑ <?.. x> m x) (λ a, p ⊑ (<?> m a))%I | 21.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (subprot_trans with "H"). iApply subprot_texist_intro_r.
  Qed.

  Global Instance frame_send q m v R P Q p :
    Frame q R P Q →
    Frame q R ((<!> MSG v {{ P }}; p) ⊑ (<!> m))
              ((<!> MSG v {{ Q }}; p) ⊑ (<!> m)) | 10.
  Proof.
    rewrite /Frame /=. iIntros (HP) "[HR H]".
    iApply (subprot_trans with "[HR] H"). iApply subprot_payload_elim_r.
    iIntros "HQ". iApply subprot_payload_intro_l. iApply HP; iFrame.
  Qed.
  Global Instance frame_recv q m v R P Q p :
    Frame q R P Q →
    Frame q R ((<?> m) ⊑ (<?> MSG v {{ P }}; p))
              ((<?> m) ⊑ (<?> MSG v {{ Q }}; p)) | 11.
  Proof.
    rewrite /Frame /=. iIntros (HP) "[HR H]".
    iApply (subprot_trans with "H"). iApply subprot_payload_elim_l.
    iIntros "HQ". iApply subprot_payload_intro_r. iApply HP; iFrame.
  Qed.
  Global Instance from_sep_send m v P p :
    FromSep ((<!> MSG v {{ P }}; p) ⊑ (<!> m)) P ((<!> MSG v; p) ⊑ (<!> m)) | 10.
  Proof. rewrite /FromSep. by iIntros "[$ H]". Qed.
  Global Instance from_sep_recv m v P p :
    FromSep ((<?> m) ⊑ (<?> MSG v {{ P }}; p)) P ((<?> m) ⊑ (<?> MSG v; p)) | 11.
  Proof. rewrite /FromSep. by iIntros "[$ H]". Qed.

  Global Instance from_modal_msg a v p1 p2 :
    FromModal True (modality_instances.modality_laterN 1) (p1 ⊑ p2)
              ((<a> MSG v; p1) ⊑ (<a> MSG v; p2)) (p1 ⊑ p2).
  Proof. intros _. apply subprot_base. Qed.

  (** Session normalize *)
  Lemma prot_unfold_eq p1 p2 : p1 ≡ p2 → ProtUnfold p1 p2.
  Proof. intros Hp d q [Hq]; constructor. destruct d; by rewrite Hp. Qed.

  Global Instance prot_normalize_done p : ProtNormalize false p p | 0.
  Proof. constructor. iApply subprot_refl. Qed.
  Global Instance prot_normalize_done_dual p : ProtNormalize true p (dual p) | 0.
  Proof. constructor. iApply subprot_refl. Qed.
  Global Instance prot_normalize_done_dual_end d a1 a2 P :
    ActionDualIf d a1 a2 →
    ProtNormalize d (END@a1 {{ P }}) (END@a2 {{ P }}) | 0.
  Proof. intros [->]. constructor. destruct d; rewrite ?dual_end; auto. Qed.

  Global Instance prot_normalize_dual d p q :
    ProtNormalize (negb d) p q →
    ProtNormalize d (dual p) q.
  Proof. intros [Hp]; constructor. by destruct d; rewrite /= ?dual_dual. Qed.

  Global Instance msg_normalize_base d a v P p q :
    ProtNormalize d p q →
    MsgNormalize d a (MSG v {{ P }}; p) (MSG v {{ P }}; q).
  Proof.
    intros [Hp]; do 2 split. iApply subprot_trans; [|by iApply subprot_base].
    destruct d; by rewrite /= ?dual_msg ?msg_dual_base.
  Qed.
  Global Instance msg_normalize_exist_base {A} d a (m : A → msg)
      (v : A → val) (P : A → aProp) (q : A → aMiniProt) y v' P' q' :
    ActionDualIf d a ASend →
    (∀ x, MsgNormalize d a (m x) (MSG v x {{ P x }}; q x)) →
    TCEq (v y) v' → TCEq (P y) P' → TCEq (q y) q' →
    MsgNormalize d a (∃ x, m x) (MSG v' {{ P' }}; q').
  Proof.
    intros [Ha] Hpq <-%TCEq_eq <-%TCEq_eq <-%TCEq_eq. do 2 split.
    destruct (Hpq y) as [[Hm]]. destruct a, d; simplify_eq/=.
    - by iExists y.
    - rewrite dual_msg /= msg_dual_exist. iExists y. by rewrite dual_msg in Hm.
  Qed.

  Global Instance msg_normalize_exist {A} d a (m1 m2 : A → msg) :
    (∀ x, MsgNormalize d a (m1 x) (m2 x)) →
    MsgNormalize d a (∃ x, m1 x) (∃ x, m2 x).
  Proof.
    intros Hp; do 2 split.
    destruct d, a; simpl in *; rewrite ?dual_msg ?msg_dual_exist /=;
      iIntros (x); iExists x; destruct (Hp x) as [[Hpx]];
      move: Hpx; rewrite ?dual_msg; auto.
  Qed.

  Global Instance msg_tele_base v P p :
    MsgTele (TT:=TeleO) (MSG v {{ P }}; p) v P p.
  Proof. by constructor. Qed.
  Global Instance msg_tele_exist {A} {TT : A → tele} (m : A → msg) tv tP tp :
    (∀ x, MsgTele (TT:=TT x) (m x) (tv x) (tP x) (tp x)) →
    MsgTele (TT:=TeleS TT) (∃ x, m x) tv tP tp.
  Proof. intros Hm. constructor; simpl; f_equiv=> x. apply Hm. Qed.

  Global Instance msg_normalize_texist {TT : tele} d a m (tv : TT -t> _) tP tp tq :
    MsgTele m tv tP tp →
    (∀.. x, ProtNormalize d (tele_app tp x) (tele_app tq x)) →
    MsgNormalize d a m (∃.. x : TT, MSG tele_app tv x {{ tele_app tP x }}; tele_app tq x).
  Proof.
    rewrite tforall_forall. intros [Hm] Hpq; do 2 split.
    destruct d; rewrite /= Hm ?dual_msg ?msg_dual_base ?msg_dual_texist {Hm};
      destruct a; simpl; iIntros (x); iExists x; rewrite ?msg_dual_base;
      iIntros "$ !>"; destruct (Hpq x); auto.
  Qed.

  Global Instance prot_normalize_message d a1 a2 m1 m2 :
    ActionDualIf d a1 a2 →
    MsgNormalize d a1 m1 m2 →
    ProtNormalize d (<a1> m1) (<a2> m2).
  Proof. by intros [->] [Hm]. Qed.

  (** Automatically perform normalization of protocols in the proof mode when
  using [iAssumption] and [iFrame]. *)
  Global Instance from_assumption_own_chan q c p1 p2 :
    ProtNormalize false p1 p2 →
    FromAssumption q (c ↣ p1) (c ↣ p2).
  Proof.
    intros [Hp]. rewrite /FromAssumption bi.intuitionistically_if_elim.
    iIntros "H". by iApply (own_chan_subprot with "H").
  Qed.
  Global Instance into_wand_own_chan_send q c p1 v P p2 Q :
    ProtNormalize false p1 (<!> MSG v {{ P }}; p2) →
    FromAssumption false Q (▷ P) →
    IntoWand q false (c ↣ p1) Q (c ↣ <!> MSG v; p2).
  Proof.
    intros [Hp]; rewrite /FromAssumption /IntoWand /= bi.intuitionistically_if_elim /=.
    iIntros (->) "H HP". iApply (own_chan_subprot with "H").
    iApply subprot_trans; first by iApply Hp. iFrame "HP". auto.
  Qed.
  Global Instance into_wand_own_chan_end q c p P Q :
    ProtNormalize false p (END! {{ P }}) →
    FromAssumption false Q (▷ P) →
    IntoWand q false (c ↣ p) Q (c ↣ END!).
  Proof.
    intros [Hp]; rewrite /FromAssumption /IntoWand /= bi.intuitionistically_if_elim /=.
    iIntros (->) "H HP". iApply (own_chan_subprot with "H").
    iApply subprot_trans; first by iApply Hp. iFrame "HP". auto.
  Qed.
  Global Instance frame_own_chan q c p1 p2 :
    ProtNormalize false p1 p2 →
    Frame q (c ↣ p1) (c ↣ p2) emp.
  Proof.
    intros [Hp]. rewrite /Frame bi.intuitionistically_if_elim.
    iIntros "[H _]". by iApply (own_chan_subprot with "H").
  Qed.
End classes.

Lemma tac_wp_recv {TT : tele} {Δ Δ' n k e i c p Φ tv tP tp Q} j :
  DoPureStepsIntoCtx e (TCEq (recv (Val c))) n k →
  MaybeIntoLaterNEnvs n Δ Δ' → (* we should do one more in the part not containing i *)
  envs_lookup i Δ' = Some (false, c ↣ p)%I →
  ProtNormalize false p (<?.. x> MSG tv x {{ tP x }}; tp x) →
  (∀.. x, FinalizeWP (k (Val (tv x))) Φ (tele_app Q x)) →
  let Δ'' := envs_delete false i false Δ' in
  (∀.. x : TT,
    match envs_app false (Esnoc (Esnoc Enil j (tP x)) i (c ↣ tp x)) Δ'' with
    | Some Δ''' => envs_entails Δ''' (tele_app Q x)
    | None => False
    end) →
  envs_entails Δ (WP e {{ Φ }}).
Proof.
  rewrite envs_entails_unseal /= !tforall_forall.
  iIntros ((e'&?&<-%TCEq_eq&Hwp)%do_pure_steps_into_ctx_wp ??? HQ HΔ'') "HΔ".
  rewrite into_laterN_env_sound /=. iApply Hwp; iNext.
  rewrite envs_lookup_sound //=. set (envs_delete true i false Δ') as Δ''.
  iDestruct "HΔ" as "[Hc HΔ]". iApply (wp_recv with "Hc").
  iIntros "!> %w (%x & -> & Hc & HP)". destruct (HQ x) as [HQ']; clear HQ.
  specialize (HΔ'' x). destruct (envs_app _ _ _) as [Δ'''|] eqn:?; last done.
  iApply HQ'. iApply HΔ''.
  iApply (envs_app_sound with "[$]"); first done. by iFrame.
Qed.

Lemma tac_wp_send {TT : tele} {Δ Δ' e n k i c v p tv tP tp Φ} neg js :
  DoPureStepsIntoCtx e (TCEq (send (Val c) (Val v))) n k →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_lookup i Δ' = Some (false, c ↣ p)%I →
  ProtNormalize false p (<!.. x> MSG tv x {{ tP x }}; tp x) →
  let Δ'' := envs_delete false i false Δ' in
  (∃.. x : TT,
    match envs_split (if neg is true then base.Right else base.Left) js Δ'' with
    | Some (Δ1,Δ2) =>
       match envs_app false (Esnoc Enil i (c ↣ tp x)) Δ2 with
       | Some Δ2' =>
          v = tv x ∧
          envs_entails Δ1 (tP x) ∧
          ∃ Q, FinalizeWP (k (Val #())) Φ Q ∧ envs_entails Δ2' Q
       | None => False
       end
    | None => False
    end) →
  envs_entails Δ (WP e {{ Φ }}).
Proof.
  rewrite envs_entails_unseal /= !texist_exist.
  iIntros ((e'&?&<-%TCEq_eq&Hwp)%do_pure_steps_into_ctx_wp ?? [Hp] [x HΔ'']) "HΔ".
  rewrite into_laterN_env_sound /=. iApply Hwp; iNext.
  destruct (envs_split _ _ _) as [[Δ1 Δ2]|] eqn:? => //.
  destruct (envs_app _ _ _) as [Δ2'|] eqn:? => //.
  rewrite envs_lookup_sound //= envs_split_sound //=.
  rewrite (envs_app_sound Δ2) //; simpl. destruct HΔ'' as (-> & -> & Q & [HQ] & ->).
  iDestruct "HΔ" as "(Hc & HP & HQ)". iApply (wp_send with "[Hc HP]").
  { iApply (own_chan_subprot with "Hc"); iIntros "!>".
    iApply subprot_trans; [iApply Hp|]. iExists x. iFrame "HP". auto. }
  iIntros "!> Hc". iApply HQ. iApply "HQ"; by iFrame.
Qed.

Lemma tac_wp_wait {Δ Δ' e n k c p i Φ Q} :
  DoPureStepsIntoCtx e (TCEq (wait (Val c))) n k →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_lookup i Δ' = Some (false, c ↣ p)%I →
  ProtNormalize false p END? →
  FinalizeWP (k (Val #())) Φ Q →
  envs_entails (envs_delete false i false Δ') Q →
  envs_entails Δ (WP e {{ Φ }}).
Proof.
  rewrite envs_entails_unseal.
  iIntros ((e'&?&<-%TCEq_eq&Hwp)%do_pure_steps_into_ctx_wp ??? [HQ] HΔ') "HΔ".
  rewrite into_laterN_env_sound /= envs_lookup_sound //=.
  set (envs_delete true i false Δ') as Δ''.
  iDestruct "HΔ" as "[Hc HΔ]"; [done..|].
  iApply Hwp. iNext. iApply (wp_wait with "Hc"); iIntros "!> _".
  iApply HQ. by iApply HΔ'.
Qed.

Lemma tac_wp_close {Δ Δ' e n k c p i Φ Q} :
  DoPureStepsIntoCtx e (TCEq (close (Val c))) n k →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_lookup i Δ' = Some (false, c ↣ p)%I →
  ProtNormalize false p END! →
  FinalizeWP (k (Val #())) Φ Q →
  envs_entails (envs_delete false i false Δ') Q →
  envs_entails Δ (WP e {{ Φ }}).
Proof.
  rewrite envs_entails_unseal.
  iIntros ((e'&?&<-%TCEq_eq&Hwp)%do_pure_steps_into_ctx_wp ??? [HQ] HΔ') "HΔ".
  rewrite into_laterN_env_sound /= envs_lookup_sound //=.
  set (envs_delete true i false Δ') as Δ''.
  iDestruct "HΔ" as "[Hc HΔ]"; [done..|].
  iApply Hwp. iNext. iApply (wp_close with "Hc"); iNext.
  iApply HQ. by iApply HΔ'.
Qed.

Tactic Notation "wp_recv_core" tactic3(tac_intros) "as" tactic3(tac) :=
  iStartProof;
  let Htmp := iFresh in
  lazymatch goal with
  | |- environments.envs_entails _ (WP _ {{ _ }}) =>
     notypeclasses refine (tac_wp_recv Htmp _ _ _ _ _ _);
       [tc_solve || fail 1 "wp_recv: cannot find 'recv' subexpression"
       |tc_solve (* into laters *)
       |iAssumptionCore || fail 1 "wp_recv: cannot find ↦"
       |tc_solve || fail 1 "wp_recv: protocol not a recv"
       |try tc_solve (* wp finalize *)
       |pm_reduce; cbn [tforall tele_fold tele_bind tele_app];
        tac_intros; intros; tac Htmp]
  | _ => fail "wp_recv: goal not a 'wp'"
  end.

Tactic Notation "wp_recv" "as" constr(pat) :=
  wp_recv_core (idtac) as (fun H => iDestructHyp H as pat).
Tactic Notation "wp_recv" := wp_recv as "_".
Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as pat).
Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as "_").

Tactic Notation "wp_send_core" tactic3(tac_exist) "with" constr(pat) :=
  let solve_done d :=
    lazymatch d with
    | true =>
       done ||
       let Q := match goal with |- envs_entails _ ?Q => Q end in
       fail "wp_send: cannot solve" Q "using done"
    | false => idtac
    end in
  lazymatch spec_pat.parse pat with
  | [SGoal (SpecGoal GSpatial ?neg ?Hs_frame ?Hs ?d)] =>
     let Hs' := eval cbv in (if neg then Hs else Hs_frame ++ Hs) in
     iStartProof;
     lazymatch goal with
     | |- environments.envs_entails _ (WP _ {{ _ }}) =>
          notypeclasses refine (tac_wp_send neg Hs' _ _ _ _ _);
            [tc_solve || fail 1 "wp_send: cannot find 'send' subexpression"
            |tc_solve (* into laters *)
            |iAssumptionCore || fail 1 "wp_send: cannot find ↦"
            |tc_solve || fail 1 "wp_send: protocol not a send"
            |pm_reduce; simpl; tac_exist;
             repeat lazymatch goal with |- ∃ _, _ => eexists _ end;
             notypeclasses refine (conj _ (conj _ (ex_intro _ _ (conj _ _))));
               [notypeclasses refine (eq_refl _)
                 || fail 1 "wp_send: value does not match protocol"
               |iFrame Hs_frame; solve_done d
               |tc_solve (* simpl *)
               |]]
     | _ => fail "wp_send: not a 'wp'"
     end
  | _ => fail "wp_send: only a single non-framing spec pattern supported"
  end.

(* From https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/931 *)
Ltac2 with_ltac1_list f ls :=
  let ls := Option.get (Ltac1.to_list ls) in
  f ls.

Tactic Notation "wp_send" "with" constr(pat) :=
  wp_send_core (idtac) with pat.
Tactic Notation "wp_send" := wp_send with "[//]".
Tactic Notation "wp_send" "(" ne_uconstr_list_sep(xs,",") ")" "with" constr(pat) :=
  wp_send_core (idtac;
    let f := ltac2:(xs |- with_ltac1_list (List.iter ltac1:(x |- eexists x)) xs)
    in f xs) with pat.

Tactic Notation "wp_wait" :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (WP _ {{ _ }}) =>
     notypeclasses refine (tac_wp_wait _ _ _ _ _ _);
       [tc_solve || fail 1 "wp_wait: cannot find 'wait' subexpression"
       |tc_solve (* into laters *)
       |iAssumptionCore || fail 1 "wp_wait: cannot find ↦"
       |tc_solve || fail 1 "wp_wait: protocol not an END?"
       |tc_solve (* simpl *)
       |pm_reduce]
  | _ => fail "wp_wait: goal not a 'wp'"
  end.
Tactic Notation "wp_wait" "!" := wp_wait; wp_pures _.

Tactic Notation "wp_close" :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (WP _ {{ _ }}) =>
     notypeclasses refine (tac_wp_close _ _ _ _ _ _);
       [tc_solve || fail 1 "wp_close: cannot find 'close' subexpression"
       |tc_solve (* into laters *)
       |iAssumptionCore || fail 1 "wp_close: cannot find ↦"
       |tc_solve || fail 1 "wp_close: protocol not an END!"
       |tc_solve (* simpl *)
       |pm_reduce]
  | _ => fail "wp_close: goal not a 'wp'"
  end.
Tactic Notation "wp_close" "!" := wp_close; wp_pures _.
