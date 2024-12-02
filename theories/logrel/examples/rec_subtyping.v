(** This file demonstrates how Löb induction can be used to prove subtyping
of recursive protocols that combine polymorphism and asynchronous subtyping.
In pseudo syntax, the subtyping we show is:

     μ rec. ! (X,Y:★) (X ⊸ Y). !X. ?Y. rec
  <: μ rec. ! (X1,X2:★) (X1 ⊸ bool). !X1. ?bool. !(X2 ⊸ int). !X2. ?int. rec
*)
From dlfactris.session_logic Require Import proofmode.
From dlfactris.logrel Require Import subtyping_rules.

Section basics.

  Definition prot1_aux (rec : lsty) : lsty :=
    <!! X Y> TY (X ⊸ Y); <!!> TY X; <??> TY Y; rec.
  Instance prot1_aux_contractive : Contractive prot1_aux.
  Proof. solve_prot_contractive. Qed.
  Definition prot1 := lty_rec prot1_aux.

  Definition prot2_aux (rec : lsty) : lsty :=
    <!! X1> TY (X1 ⊸ lty_int); <!!> TY X1; <??> TY lty_int;
    <!! X2> TY (X2 ⊸ lty_bool); <!!> TY X2; <??> TY lty_bool; rec.
  Instance prot2_aux_contractive : Contractive prot2_aux.
  Proof. solve_prot_contractive. Qed.
  Definition prot2 := lty_rec prot2_aux.

  Lemma rec_swap_example : prot1 <: prot2.
  Proof.
    iLöb as "IH".
    iDestruct (lty_le_rec_unfold (prot1_aux)) as "[H1 _]".
    iDestruct (lty_le_rec_unfold (prot2_aux)) as "[_ H2]".
    iApply (lty_le_trans with "H1"). iApply (lty_le_trans with "[] H2").
    iIntros (X). iExists X, lty_int. iIntros "!>!>!>".
    iApply (lty_le_trans with "H1").
    iIntros (X'). iExists X', lty_bool. iIntros "!>!>!>".
    iApply "IH".
  Qed.

End basics.
