(** This file contains shows that the program

  λ c, (recv c, recv c)

can be assigned the type

  chan (?int.?int.end) ⊸ (int * int)

by exclusively using the semantic typing rules. *)
From dlfactris.session_logic Require Import proofmode.
From dlfactris.logrel Require Export term_typing_rules session_typing_rules.

Definition prog : expr :=
  λ: "c", let: "xy" := (recv "c", recv "c") in wait "c";; "xy".

Lemma prog_typed :
  [] ⊨ prog : chan (<??> TY lty_int; <??> TY lty_int; END??) ⊸ lty_int * lty_int.
Proof.
  iApply (ltyped_lam []).
  iApply ltyped_subsumption_alt;
    [by iApply ctx_le_refl| |by iApply lty_le_refl|].
  { iApply ltyped_let.
    { iApply ltyped_pair.
      - by iApply ltyped_recv.
      - by iApply ltyped_recv. }
    iApply ltyped_seq; [by iApply lty_copyable_unit|by iApply ltyped_wait|].
    by iApply ltyped_var. }
  iApply ctx_le_drop. iApply lty_copyable_copy_inv.
Qed.
