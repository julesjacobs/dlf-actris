(** This file provides three wrappers around the distributed version of merge
sort, demonstrating Actris's support for delegation and branching:

- [sort_service_br]: a service that allows one to sort a series of lists in
  sequence.
- [sort_service_del]: a service that allows one to sort a series of lists in
  parallel by delegating a sort service for a single list to a new channel.
- [sort_service_br_del]: a service that allows one to sort a series of list by
  forking itself. *)
From stdpp Require Import sorting.
From dlfactris.session_logic Require Import proofmode.
From dlfactris.examples Require Export llist compare sort.
Import TImp TImp.notations.

Definition sort_service_br : val :=
  rec: "go" "cmp" "c" :=
    if: ~recv "c" then wait "c" else
    sort_service_cont "cmp" "c";;
    "go" "cmp" "c".

Definition sort_service_del : val :=
  rec: "go" "cmp" "c" :=
    if: ~recv "c" then wait "c" else
    send "c" (fork_chan (λ: "c", sort_service "cmp" "c"));;
    "go" "cmp" "c".

Definition sort_service_br_del : val :=
  rec: "go" "cmp" "c" :=
    if: recv "c" then
      sort_service_cont "cmp" "c";;
      "go" "cmp" "c"
    else if: recv "c" then
      send "c" (fork_chan (λ: "c", "go" "cmp" "c"));;
      "go" "cmp" "c"
    else wait "c".

Section sort_service_br_del.
  Context {A} (I : A → val → aProp) (R : A → A → Prop) `{!RelDecision R, !Total R}.

  Definition sort_protocol_br_aux (rec : prot) : prot :=
    sort_protocol_cont I R rec <+> END!.
  Instance sort_protocol_br_aux_contractive : Contractive sort_protocol_br_aux.
  Proof. solve_prot_contractive. Qed.
  Definition sort_protocol_br : prot := fixpoint sort_protocol_br_aux.
  Global Instance sort_protocol_br_unfold :
    ProtUnfold sort_protocol_br (sort_protocol_br_aux sort_protocol_br).
  Proof. apply prot_unfold_eq, (fixpoint_unfold sort_protocol_br_aux). Qed.

  Lemma sort_service_br_spec cmp c :
    cmp_spec I R cmp -∗
    {{{ c ↣ dual sort_protocol_br }}}
      sort_service_br cmp c
    {{{ RET #(); emp }}}.
  Proof using A I R RelDecision0 Total0.
    iIntros "#Hcmp !>" (Ψ) "Hc HΨ". iLöb as "IH" forall (c Ψ).
    wp_rec. wp_recv ([]); wp_pures.
    { iApply (sort_service_cont_spec with "Hcmp Hc"); iIntros "!> Hc".
      by iApply ("IH" with "Hc"). }
    rewrite dual_end. wp_wait. by iApply "HΨ".
  Qed.

  Definition sort_protocol_del_aux (rec : prot) : prot :=
    (<? c> MSG c {{ c ↣ sort_protocol I R}}; rec) <+> END!.
  Instance sort_protocol_del_aux_contractive : Contractive sort_protocol_del_aux.
  Proof. solve_prot_contractive. Qed.
  Definition sort_protocol_del : prot := fixpoint sort_protocol_del_aux.
  Global Instance sort_protocol_del_unfold :
    ProtUnfold sort_protocol_del (sort_protocol_del_aux sort_protocol_del).
  Proof. apply prot_unfold_eq, (fixpoint_unfold sort_protocol_del_aux). Qed.

  Lemma sort_protocol_del_spec cmp c :
    cmp_spec I R cmp -∗
    {{{ c ↣ dual sort_protocol_del }}}
      sort_service_del cmp c
    {{{ RET #(); emp }}}.
  Proof using A I R RelDecision0 Total0.
    iIntros "#Hcmp !>" (Ψ) "Hc HΨ". iLöb as "IH" forall (Ψ).
    wp_rec. wp_recv ([]); wp_pures.
    { iApply (wp_fork_chan (sort_protocol I R));
        iIntros "!>" (c') "Hc'".
      { by iApply (sort_service_spec with "Hcmp Hc'"); iIntros "!> Hc'". }
      wp_send with "[$Hc']". by iApply ("IH" with "Hc"). }
    rewrite dual_end. wp_wait. by iApply "HΨ".
  Qed.

  Definition sort_protocol_br_del_aux (rec : prot) : prot :=
    sort_protocol_cont I R rec <+> ((<? c> MSG c {{ c ↣ rec }}; rec) <+> END!).
  Instance sort_protocol_br_del_aux_contractive : Contractive sort_protocol_br_del_aux.
  Proof. solve_prot_contractive. Qed.
  Definition sort_protocol_br_del : prot := fixpoint sort_protocol_br_del_aux.
  Global Instance sort_protocol_br_del_unfold :
    ProtUnfold sort_protocol_br_del (sort_protocol_br_del_aux sort_protocol_br_del).
  Proof. apply prot_unfold_eq, (fixpoint_unfold sort_protocol_br_del_aux). Qed.

  Lemma sort_service_br_del_spec cmp c :
    cmp_spec I R cmp -∗
    {{{ c ↣ dual sort_protocol_br_del }}}
      sort_service_br_del cmp c
    {{{ RET #(); emp }}}.
  Proof using A I R RelDecision0 Total0.
    iIntros "#Hcmp !>" (Ψ) "Hc HΨ". iLöb as "IH" forall (c Ψ).
    wp_rec. wp_recv ([]); wp_pures.
    { iApply (sort_service_cont_spec with "Hcmp Hc"); iIntros "!> Hc".
      by iApply ("IH" with "Hc"). }
    wp_recv ([]); wp_pures.
    { iApply (wp_fork_chan sort_protocol_br_del); iIntros "!>" (c') "Hc'".
      { iApply ("IH" with "Hc'"); auto. }
      wp_send with "[$Hc']".
      by iApply ("IH" with "Hc"). }
    rewrite dual_end. wp_wait. by iApply "HΨ".
  Qed.

End sort_service_br_del.
