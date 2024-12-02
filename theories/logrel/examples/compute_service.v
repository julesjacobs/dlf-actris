(** This file contains a computation service with the type

  μ rec. & { cont : ? (X:★) (() ⊸ X). ! X. rec,
             stop : ?end }

It recursively receives computations, computes them, and then
sends back the results.
The example is type checked using only the rules of the type system. *)
From dlfactris.session_logic Require Import proofmode.
From dlfactris.logrel Require Import session_typing_rules.

Definition compute_service : val :=
  rec: "go" "c":=
    match: (recv "c") with
    | "cont" <> => let: "f" := recv "c" in
                   send "c" ("f" #());; "go" "c"
    | "stop" <> => wait "c"
    end.

Definition compute_client : val :=
  λ: <>,
     let: "c1" := fork_chan (λ: "c1", close "c1") in
     let: "c2" := fork_chan compute_service in
     send "c2" (Sum "cont" #());;
     send "c2" (λ: <>, wait "c1");;
     recv "c2";;
     send "c2" (Sum "stop" #());;
     close "c2".

Section compute_example.

  Definition compute_service_type_aux (rec : lsty) : lsty :=
    lty_branch $ <["cont" := ((), (<?? A> TY () ⊸ A; <!!> TY A ; rec))%lty]> $
                 <["stop" := ((), END??)%lty]> $ ∅.
  Instance compute_service_type_contractive :
    Contractive (compute_service_type_aux).
  Proof. solve_prot_contractive. Qed.
  Definition compute_service_type : lsty :=
    lty_rec (compute_service_type_aux).
  Lemma compute_service_type_unfold :
    compute_service_type ≡ compute_service_type_aux (compute_service_type).
  Proof. apply fixpoint_unfold. Qed.

  Lemma ltyped_compute_service Γ :                                               (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=ca007d94 *)
    Γ ⊨ compute_service : lty_chan compute_service_type ⊸ any ⫤ Γ.
  Proof.
    iApply (ltyped_subsumption_alt);
      [by iApply ctx_le_refl| |by iApply lty_le_copy_elim|by iApply ctx_le_refl].
    iApply ltyped_val_ltyped.
    iApply ltyped_val_rec.
    iApply (ltyped_subsumption_alt);
      [| |by iApply lty_le_refl|by iApply ctx_le_refl].
    { iApply ctx_le_cons; [by iApply lty_le_refl|].
      iApply ctx_le_cons; [|by iApply ctx_le_refl].
      iApply lty_le_chan.
      iApply lty_le_l; [|iApply lty_le_refl].
      iApply lty_le_rec_unfold. }
    iApply ltyped_branch; [done|].
    rewrite big_sepM_insert; [|done].
    iSplit.
    { iExists _. iSplit; [done|].
      iApply ltyped_subsumption_alt;
        [|iApply ltyped_lam|by iApply lty_le_refl|by iApply ctx_le_refl].
      { rewrite right_id_L. iApply ctx_le_refl. }
      iApply ltyped_subsumption_alt;
        [by iApply ctx_le_refl|iApply ltyped_recv_texist|by iApply lty_le_refl|];
        [try eauto..|]; [try apply _..|].
      { iIntros (Ys).
        pose proof (ltys_S_inv Ys) as (K&?&->).
        pose proof (ltys_O_inv x) as ->. simpl.
        iApply ltyped_seq; [by iApply lty_copyable_unit| |].
        - iApply ltyped_send; last first.
          + iApply ltyped_app; [by iApply ltyped_unit|by iApply ltyped_var].
          + done.
        - iApply ltyped_app_copy.
          + by iApply ltyped_var.
          + rewrite /ctx_overwrite. simpl.
            iApply ltyped_subsumption_alt;
              [| |by iApply lty_le_refl|by iApply ctx_le_refl].
            { iApply ctx_le_cons; [iApply lty_le_refl|].
              iApply ctx_le_cons.
              { iApply lty_le_any. iApply lty_copyable_copy_inv. }
              iApply ctx_le_refl. }
            by iApply ltyped_var. }
      simpl.
      iApply ctx_le_trans.
      { iApply ctx_le_cons; [iApply lty_le_refl|].
        iApply ctx_le_cons; [iApply lty_le_refl|].
        iApply ctx_le_cons; [iApply lty_le_refl|].
        iApply ctx_le_drop. iApply lty_copyable_unit. }
      iApply ctx_le_trans.
      { iApply ctx_le_cons; [iApply lty_le_refl|].
        iApply ctx_le_cons; [iApply lty_le_refl|].
        iApply ctx_le_drop. iApply lty_copyable_any. }
      iApply ctx_le_trans.
      { iApply ctx_le_cons; [iApply lty_le_refl|].
        iApply ctx_le_drop. iApply lty_copyable_copy_inv. }
      iApply ctx_le_drop. iApply lty_copyable_copy_inv. }
    rewrite big_sepM_insert; [|done].
    iSplit.
    { iExists _. iSplit; [done|].
      iApply ltyped_subsumption_alt;
        [|iApply ltyped_lam|by iApply lty_le_refl|by iApply ctx_le_refl].
      { rewrite right_id_L. iApply ctx_le_refl. }
      iApply ltyped_subsumption_alt;
        [iApply ctx_le_refl|iApply ltyped_wait| |].
      { simpl. done. }
      { iApply lty_le_any. iApply lty_copyable_unit. }
      simpl.
      iApply ctx_le_trans.
      { iApply ctx_le_cons; [iApply lty_le_refl|].
        iApply ctx_le_drop. iApply lty_copyable_copy. }
      iApply ctx_le_drop. iApply lty_copyable_unit. }
    by iApply big_sepM_empty.
  Qed.


  Definition compute_client_type_aux (rec : lsty) : lsty :=
    lty_select $ <["cont" := ((), (<!! A> TY () ⊸ A; <??> TY A ; rec))%lty]> $
                 <["stop" := ((), END!!)%lty]> $ ∅.
  Instance compute_client_type_contractive :
    Contractive (compute_client_type_aux).
  Proof. solve_prot_contractive. Qed.
  Definition compute_client_type : lsty :=
    lty_rec (compute_client_type_aux).
  Lemma compute_client_type_unfold :
    compute_client_type ≡ compute_client_type_aux (compute_client_type).
  Proof. apply fixpoint_unfold. Qed.

  Lemma compute_client_service_dual :
    lty_dual compute_service_type <:> compute_client_type.
  Proof.
    iLöb as "IH".
    rewrite /compute_service_type /compute_client_type.
    iApply lty_bi_le_trans.
    { iApply lty_bi_le_dual. iApply lty_le_rec_unfold. }
    iApply lty_bi_le_trans; last first.
    { iApply lty_bi_le_sym. iApply lty_le_rec_unfold. }
    iApply lty_bi_le_trans; [iApply lty_le_dual_branch|].
    iApply lty_bi_le_select.
    rewrite fmap_insert. iApply big_sepM2_insert; [done..|].
    iSplit.
    { iSplit; [iApply lty_bi_le_refl|].
      iIntros "!>". simpl.
      iApply lty_bi_le_trans.
      { iApply lty_le_dual_recv_exist. }
      simpl.
      iSplit.
      - iIntros (A). iExists A. iApply lty_le_send; [done|].
        iIntros "!>".
        iApply lty_le_trans.
        { iApply lty_le_l; [iApply lty_le_dual_send|iApply lty_le_refl]. }
        iApply lty_le_recv; [done|].
        iIntros "!>". iDestruct "IH" as "[$ _]".
      - iIntros (A). iExists A. iApply lty_le_send; [done|].
        iIntros "!>".
        iApply lty_le_trans; last first.
        { iApply lty_le_r;
            [iApply lty_le_refl|iApply lty_bi_le_sym; iApply lty_le_dual_send]. }
        iApply lty_le_recv; [done|].
        iIntros "!>". iDestruct "IH" as "[_ $]". }
    rewrite fmap_insert. iApply big_sepM2_insert; [done..|].
    iSplit.
    { iSplit; [iApply lty_bi_le_refl|].
      iIntros "!>". simpl.
      iApply lty_le_dual_wait. }
    rewrite fmap_empty. by iApply big_sepM2_empty.
  Qed.

  Lemma ltyped_compute_client :
    [] ⊨ compute_client : () ⊸ () ⫤ [].
  Proof.
    iApply ltyped_val_ltyped.
    iApply ltyped_val_lam.
    iApply ltyped_subsumption_alt;
      [by iApply ctx_le_refl|iApply ltyped_let|by iApply lty_le_refl|].
    { iApply ltyped_subsumption_alt;
        [|iApply (ltyped_fork_chan _ [] END??)|
          by iApply lty_le_refl|by iApply ctx_le_refl].
      { rewrite right_id_L. iApply ctx_le_refl. }
      iApply ltyped_subsumption_alt;
        [|iApply ltyped_lam|iApply lty_le_refl|iApply ctx_le_refl].
      { rewrite right_id_L. iApply ctx_le_refl. }
      iApply ltyped_subsumption_alt;
        [|iApply ltyped_close| |].
      - iApply ctx_le_cons; [|iApply ctx_le_refl].
        iApply lty_le_chan. iApply lty_le_l; [|iApply lty_le_refl].
        iApply lty_le_dual_wait.
      - done.
      - iApply lty_le_any. iApply lty_copyable_unit.
      - iApply ctx_le_refl. }
    { iApply ltyped_subsumption_alt;
        [by iApply ctx_le_refl|iApply ltyped_let|by iApply lty_le_refl|].
      { iApply ltyped_subsumption_alt;
          [|iApply (ltyped_fork_chan _ [] compute_client_type)|
            by iApply lty_le_refl|by iApply ctx_le_refl].
        { rewrite right_id_L. iApply ctx_le_refl. }
        iApply ltyped_subsumption_alt;
          [by iApply ctx_le_refl|iApply ltyped_compute_service|
            |by iApply ctx_le_refl].
        iApply lty_le_arr; [|iApply lty_le_refl].
        iApply lty_le_chan.
        iApply lty_le_dual_l.
        iApply lty_le_l; [iApply compute_client_service_dual|].
        iApply lty_le_refl. }
      { iApply ltyped_subsumption_alt;
          [| |by iApply lty_le_refl|by iApply ctx_le_refl].
        { iApply ctx_le_cons; [|iApply ctx_le_refl].
          iApply lty_le_chan.
          iApply lty_le_l; [|iApply lty_le_refl].
          iApply lty_le_rec_unfold. }
        iApply ltyped_seq; [iApply lty_copyable_unit| |].
        { iApply ltyped_select; [| |iApply ltyped_unit]; done. }
        iApply ltyped_seq; [iApply lty_copyable_unit| |].
        { iApply ltyped_subsumption_alt;
            [ | |iApply lty_le_refl|iApply ctx_le_refl].
          { iApply ctx_le_cons; [|iApply ctx_le_refl].
            iApply lty_le_chan. iExists lty_unit. iApply lty_le_refl. }
          iApply ltyped_send; last first.
          { iApply ltyped_subsumption_alt;
              [|iApply (ltyped_lam _ _ _ _ ())|
                iApply lty_le_refl|iApply ctx_le_refl].
            { simpl.
              iApply ctx_le_trans.
              { by iApply ctx_le_cons_cons_ne. }
              replace [CtxItem "c1" (chan END??);
                       CtxItem "c2"
                               (chan (<!!> TY () ⊸ (); <??> TY ();
                                      lty_rec compute_client_type_aux));
                       CtxItem <> ()] with
                ([CtxItem "c1" (chan END??)] ++
                 [CtxItem "c2" (chan (<!!> TY () ⊸ (); <??> TY ();
                                      lty_rec compute_client_type_aux));
                  CtxItem <> ()]) by set_solver.
              iApply ctx_le_refl. }
            iApply ltyped_subsumption_alt;
              [iApply ctx_le_refl|iApply ltyped_wait|iApply lty_le_refl|];
              [done|].
            iApply ctx_le_trans.
            { iApply ctx_le_cons; [iApply lty_le_refl|]. iApply ctx_le_refl. }
            iApply ctx_le_drop. iApply lty_copyable_unit. }
          done. }
        iApply ltyped_seq; [iApply lty_copyable_unit|iApply ltyped_recv; done|].
        iApply ltyped_subsumption_alt;
          [| |by iApply lty_le_refl|by iApply ctx_le_refl].
        { iApply ctx_le_cons; [|iApply ctx_le_refl].
          iApply lty_le_chan.
          iApply lty_le_l; [|iApply lty_le_refl].
          iApply lty_le_rec_unfold. }
        iApply ltyped_seq; [iApply lty_copyable_unit| |].
        { iApply ltyped_select; [| |iApply ltyped_unit]; done. }
        iApply ltyped_close. done. }
      iApply ctx_le_refl. }
    simpl. iApply ctx_le_drop. iApply lty_copyable_unit.
  Qed.

End compute_example.
