From stdpp Require Import gmap fin_sets finite.
From dlfactris.prelude Require Export prelude.

Ltac qed := done || eauto || naive_solver lia || set_solver.
Definition uforest A `{Countable A} := gset (A * A).

Section uforest.
  Context `{Countable A}.
  Notation G := (uforest A).
  Notation P := (list A).

  Definition path (g : G) (xs : P) :=
    ∀ i a b, xs !! i = Some a → xs !! (i + 1) = Some b → (a,b) ∈ g.

  (* NB. connected g a a ↔ False *)
  Definition connected (g : G) (x y : A) := ∃ xs,
    path g (x :: xs ++ [y]).

  Definition connected0 (g : G) (x y : A) :=
    x = y ∨ connected g x y.

  Definition undirected (g : G) :=
    ∀ x y, (x,y) ∈ g → (y,x) ∈ g.

  Definition no_self_loops (g : G) :=
    ∀ x, (x,x) ∉ g.

  Definition has_u_turn (xs : P) :=
    ∃ i x, xs !! i = Some x ∧ xs !! (i+2) = Some x.

  Record is_uforest (g : G) : Prop := {
    uforest_undirected : undirected g;
    uforest_u_turns x xs :
      path g ([x] ++ xs ++ [x]) → has_u_turn ([x] ++ xs ++ [x])
  }.

  Definition uedge (x y : A) : uforest A :=
    {[ (x,y); (y,x) ]}.

  Definition has_edge (xs : P) a b i :=
    (xs !! i = Some a ∧ xs !! (i + 1) = Some b) ∨
    (xs !! i = Some b ∧ xs !! (i + 1) = Some a).

  Definition lone (g : uforest A) (x : A) := ∀ y,
    (x,y) ∉ g.

  Lemma path_edge g x y : (x,y) ∈ g → path g [x;y].
  Proof. intros ? [|[]]; naive_solver. Qed.

  Lemma uforest_no_self_loops g : is_uforest g → no_self_loops g.
  Proof.
    intros Hforest x Hx.
    destruct (uforest_u_turns g Hforest x []) as (i & a & ? & ?); simpl in *.
    - by apply path_edge.
    - destruct i as [|[]]; naive_solver.
  Qed.

  Lemma has_u_turn_reverse xs : has_u_turn (reverse xs) ↔ has_u_turn xs.
  Proof.
    revert xs. assert (∀ xs, has_u_turn (reverse xs) → has_u_turn xs).
    { intros xs (i & x & [Hxs ?]%reverse_lookup_Some & [??]%reverse_lookup_Some).
      exists (length xs - S (i + 2)), x. split; [done|].
      rewrite -Hxs. f_equal. lia. }
    intros xs; split; [by auto|]. rewrite -{1}(reverse_involutive xs). auto.
  Qed.
  Lemma has_u_turn_prefix xs ys :
    xs `prefix_of` ys → has_u_turn xs → has_u_turn ys.
  Proof.
    intros [xs' ->] (j & x & Hj & Hj').
    exists j, x. by rewrite !lookup_app Hj Hj'.
  Qed.
  Lemma has_u_turn_suffix xs ys :
    xs `suffix_of` ys → has_u_turn xs → has_u_turn ys.
  Proof.
    intros [xs' ->] (j & x & Hj & Hj').
    exists (length xs' + j), x. rewrite !lookup_app_r; [|lia..]. split.
    - rewrite -Hj. f_equal; lia.
    - rewrite -Hj'. f_equal; lia.
  Qed.
  Lemma has_u_turn_nil : has_u_turn [] ↔ False.
  Proof. split; [|done]. by intros (j&?&?&?). Qed.
  Lemma has_u_turn_cons x xs :
    has_u_turn (x :: xs) ↔ xs !! 1 = Some x ∨ has_u_turn xs.
  Proof.
    split.
    { intros ([|j]&y&?&?); simplify_eq/=; auto. right. by exists j, y. }
    intros [?|?].
    + exists 0. by exists x.
    + apply has_u_turn_suffix with xs; auto using suffix_cons_r.
  Qed.
  Global Instance has_u_turn_dec : ∀ xs, Decision (has_u_turn xs).
  Proof using Type*.
    refine (fix go xs : Decision (has_u_turn xs) :=
      match xs with
      | [] => right _
      | x :: xs => cast_if (decide (xs !! 1 = Some x ∨ has_u_turn xs))
      end); rewrite ?has_u_turn_nil ?has_u_turn_cons; naive_solver.
  Defined.

  Lemma path_singleton g b : path g [b].
  Proof. intros []; naive_solver. Qed.
  Lemma path_app g x xs ys :
    path g (xs ++ [x]) → path g (x :: ys) → path g (xs ++ x :: ys).
  Proof.
    intros Hp1 Hp2 i a b. destruct (decide (i < length xs)).
    { rewrite cons_middle assoc.
      rewrite !(lookup_app_l (_ ++ _)) ?length_app /=; [|lia..]. apply Hp1. }
    rewrite /= !lookup_app_r /=; [|lia..].
    replace (i + 1 - length xs) with (i - length xs + 1) by lia. by apply Hp2.
  Qed.
  Lemma path_cons g x y xs :
    (x,y) ∈ g → path g (y :: xs) → path g (x :: y :: xs).
  Proof. intros ?. by apply (path_app _ _ [x]), path_edge. Qed.
  Lemma path_reverse g xs :
    undirected g → path g xs → path g (reverse xs).
  Proof.
    intros Hundir Hpath i a b [Hxs ?]%reverse_lookup_Some [??]%reverse_lookup_Some.
    eapply Hundir, Hpath; first done. rewrite -Hxs. f_equal; lia.
  Qed.

  Lemma path_suffix g xs ys : xs `suffix_of` ys → path g ys → path g xs.
  Proof.
    intros [xs' ->] Hpath i x y Hx Hy.
    apply (Hpath (i + length xs')).
    - rewrite lookup_app_r; try lia.
      rewrite -Hx. f_equal; lia.
    - rewrite lookup_app_r; last lia. rewrite -Hy. f_equal; lia.
  Qed.
  Lemma path_prefix g xs ys : xs `prefix_of` ys → path g ys → path g xs.
  Proof.
    intros [xs' ->] Hpath i x y Hx Hy.
    apply (Hpath i); by rewrite lookup_app ?Hx ?Hy.
  Qed.
  Lemma path_subseteq g1 g2 xs : g1 ⊆ g2 → path g1 xs → path g2 xs.
  Proof. unfold path. set_solver. Qed.
  Lemma path_remove_mid g xs i j x :
    i ≤ j →
    xs !! i = Some x →
    xs !! j = Some x →
    path g xs → path g (take i xs ++ drop j xs).
  Proof.
    intros ? Hi Hj Hp. rewrite (drop_S _ x) //. apply path_app.
    - rewrite -take_S_r //. apply path_prefix with xs, Hp. apply prefix_take.
    - rewrite -drop_S //. apply path_suffix with xs, Hp. apply suffix_drop.
  Qed.

  Lemma connected_edge g x y :
    (x,y) ∈ g → connected g x y.
  Proof. intros ?. exists []. by apply path_edge. Qed.
  Lemma connected_sym g x y :
    undirected g → connected g x y → connected g y x.
  Proof.
    intros Hundir [xs Hxs]. exists (reverse xs).
    rewrite -reverse_cons -reverse_snoc. by apply path_reverse.
  Qed.
  Lemma connected_trans g x y z :
    connected g x y → connected g y z → connected g x z.
  Proof. 
    intros [xs Hxs] [ys Hys]. exists (xs ++ y :: ys).
    replace (x :: (xs ++ y :: ys) ++ [z])
      with ((x :: xs) ++ y :: (ys ++ [z])) by (by rewrite -!assoc).
    by apply path_app.
  Qed.
  Lemma connected_alt g x y :
    x ≠ y →
    connected g x y ↔ ∃ xs, path g xs ∧ xs !! 0 = Some x ∧ last xs = Some y.
  Proof.
    intros. split.
    + intros [xs Hxs]. exists (x :: xs ++ [y]).
      by rewrite app_comm_cons last_snoc.
    + intros ([|x1 xs] & Hp & Hfst & Hlast); simplify_eq/=.
      destruct xs as [|y' xs _] using rev_ind; simplify_eq/=.
      rewrite app_comm_cons last_snoc in Hlast; simplify_eq/=.
      by exists xs.
  Qed.

  Lemma not_connected0 g x y : ¬connected0 g x y ↔ x ≠ y ∧ ¬connected g x y.
  Proof. unfold connected0. naive_solver. Qed.
  Lemma connected0_edge g x y : (x,y) ∈ g → connected0 g x y.
  Proof. unfold connected0. auto using connected_edge. Qed.
  Lemma connected0_sym g x y :
    undirected g → connected0 g x y → connected0 g y x.
  Proof. unfold connected0. naive_solver eauto using connected_sym. Qed.
  Lemma connected0_trans_l g x y z :
    connected g x y → connected0 g y z → connected0 g x z.
  Proof. unfold connected0. naive_solver eauto using connected_trans. Qed.
  Lemma connected0_trans_r g x y z :
    connected0 g x y → connected g y z → connected0 g x z.
  Proof. unfold connected0. naive_solver eauto using connected_trans. Qed.
  Lemma connected0_trans g x y z :
    connected0 g x y → connected0 g y z → connected0 g x z.
  Proof. unfold connected0. naive_solver eauto using connected_trans. Qed.
  Lemma connected0_alt g x y :
    connected0 g x y ↔ ∃ xs, path g xs ∧ xs !! 0 = Some x ∧ last xs = Some y.
  Proof.
    unfold connected0. destruct (decide (x = y)) as [->|].
    - split; [|by auto]. intros _. exists [y]. eauto using path_singleton.
    - rewrite connected_alt //. naive_solver.
  Qed.

  Lemma uedge_sym x y : uedge x y = uedge y x.
  Proof. unfold uedge. set_solver. Qed.
  Lemma uedge_undirected x y : undirected (uedge x y).
  Proof. rewrite /undirected /uedge. set_solver. Qed.

  Global Instance has_edge_dec xs x y i : Decision (has_edge xs x y i).
  Proof using Type*. solve_decision. Defined.
  Lemma has_edge_sym xs x y i : has_edge xs x y i ↔ has_edge xs y x i.
  Proof. unfold has_edge. naive_solver. Qed.

  Lemma path_no_u_turn g xs x y :
    x ≠ y →
    path g (x :: xs ++ [y]) →
    ∃ xs', path g (x :: xs' ++ [y]) ∧ ¬has_u_turn (x :: xs' ++ [y]).
  Proof.
    intros Hxy Hp. induction (Nat.lt_wf_0_projected length xs) as [xs _ IH].
    destruct (decide (has_u_turn ([x] ++ xs ++ [y])))
      as [([|i]&y'&?&?)|]; simplify_eq/=; [..|by eauto].
    { destruct xs as [|x1 [|x2 xs]]; simplify_eq/=.
      apply (IH xs); [lia|]. eapply path_suffix, Hp.
      by do 2 apply suffix_cons_r. }
    assert (i + 2 < length (xs ++ [y])) as Hi by eauto using lookup_lt_Some.
    rewrite length_app /= in Hi.
    apply (IH (take i xs ++ drop (i + 2) xs)).
    { rewrite length_app length_take length_drop. lia. }
    assert (x :: (take i xs ++ drop (i + 2) xs) ++ [y]
      = take (S i) (x :: xs ++ [y]) ++ drop (S (i + 2)) (x :: xs ++ [y])) as ->.
    { f_equal/=. rewrite -assoc drop_app_le; [|lia].
      by rewrite take_app_le; [|lia]. }
    apply path_remove_mid with y'; auto with lia.
  Qed.

  Lemma find_first_edge (xs : P) (a b : A) :
    (∃ i, xs !! i = Some a ∧ xs !! S i = Some b ∧
      ∀ j, j < i → ¬ (xs !! j = Some a ∧ xs !! S j = Some b)) ∨
    (∀ i, ¬ (xs !! i = Some a ∧ xs !! S i = Some b)).
  Proof using Type*.
    induction xs.
    { right. intros i []. destruct i; simplify_eq. }
    destruct xs; simpl in *.
    { right. intros i []. destruct i; simplify_eq.  }
    destruct (decide (a0 = a ∧ a1 = b)).
    { left. exists 0. qed. }
    destruct IHxs.
    - left. destruct H0 as (i & Ha & Hb & Hlow).
      exists (S i). simpl. split; first done. split; first done.
      intros j Hj.
      intros []. apply n.
      destruct j; simpl in *; first naive_solver.
      specialize (Hlow j).
      assert (j < i) as Q by lia.
      specialize (Hlow Q).
      exfalso.
      apply Hlow. done.
    - right. intros i [].
      destruct i; simpl in *; first naive_solver.
      by apply (H0 i).
  Qed.

  Lemma find_first_has_edge (xs : P) (a b : A) :
    (∃ i, has_edge xs a b i ∧ ∀ j, j < i → ¬ has_edge xs a b j)
    ∨ (∀ i, ¬ has_edge xs a b i).
  Proof using Type*.
    induction xs; simpl.
    { right. intros i HH. unfold has_edge in *. destruct i; simpl in *; qed. }
    destruct xs.
    { right. intro. unfold has_edge. replace (i + 1) with (S i) by lia; simpl. destruct i; simpl; qed. }
    destruct (decide ((a0 = a ∧ a1 = b) ∨ (a0 = b ∧ a1 = a))).
    {
      left. exists 0. split; intros; try lia.
      unfold has_edge. simpl. qed.
    }
    destruct IHxs.
    {
      left. destruct H0 as (i & Hi1 & Hi2). exists (S i).
      split.
      - unfold has_edge. simpl. unfold has_edge in Hi1. qed.
      - intros. destruct j.
        + unfold has_edge. simpl. qed.
        + unfold has_edge in *. simpl.
          assert (j < i) as QQ by lia.
          specialize (Hi2 _ QQ).
          qed.
    }
    right. intro. intro. unfold has_edge in *.
    destruct i; simpl in *; qed.
  Qed.

  Lemma path_has_edge g a b xs :
    path (g ∪ uedge a b) xs → (∀ i, ¬ has_edge xs a b i) →
    path g xs.
  Proof.
    intros Hpath Hne i x y Hx Hy.
    specialize (Hpath i x y Hx Hy).
    apply elem_of_union in Hpath as []; first done.
    specialize (Hne i). contradict Hne.
    unfold has_edge. unfold uedge in H0.
    set_solver.
  Qed.

  Lemma has_edge_take a b j i xs :
    has_edge xs a b i ∧ i+1 < j ↔ has_edge (take j xs) a b i.
  Proof.
    split.
    - intros [].
      destruct H0 as [[]|[]]; [left | right]; split;
      rewrite lookup_take; (done || lia).
    - intros [[]|[]];
      apply lookup_take_Some in H0 as [];
      apply lookup_take_Some in H1 as []; split; try lia; [left | right]; qed.
  Qed.

  Lemma has_edge_drop a b j i xs :
    has_edge xs a b i ∧ i >= j → has_edge (drop j xs) a b (i - j).
  Proof.
    intros [].
    destruct H0 as [[]|[]]; [left | right]; split;
    rewrite lookup_drop; rewrite <-?H0, <-?H2; f_equiv; lia.
  Qed.

  (* Hiding this in a definition is necessary because otherwise the wlog tactic
     will generalize over the Lookup instance.
     This way the wlog tactic can not peek inside the proposition and won't find any
     Lookup instance as a subterm. *)
  Definition bar (xs : P) x i1 a b :=
    ([x] ++ xs ++ [x]) !! i1 = Some a ∧ ([x] ++ xs ++ [x]) !! (i1 + 1) = Some b.

  Lemma has_u_turn_alt (g : G) xs x :
    is_uforest g → path g xs → length xs > 1 →
    xs !! 0 = Some x → last xs = Some x →
    has_u_turn xs.
  Proof.
    intros Hforest Hpath Hlen H1 H2.
    pose proof (split_both xs x Hlen H1 H2).
    rewrite H0. rewrite H0 in Hpath.
    destruct Hforest; simpl in *; eauto.
  Qed.

  Lemma has_u_turn_mid (g : G) xs i1 i2 x :
    is_uforest g → path g (drop i1 (take (S i2) xs)) → i1 < i2 →
    xs !! i1 = Some x → xs !! i2 = Some x →
    has_u_turn xs.
  Proof.
    intros Hforest Hpath Hneq H1 H2.
    eapply has_u_turn_prefix, (has_u_turn_suffix (drop i1 (take (S i2) xs)));
      [apply prefix_take|apply suffix_drop|].
    eapply (has_u_turn_alt g (drop i1 (take (S i2) xs))); eauto.
    - rewrite length_drop. rewrite length_take. apply lookup_lt_Some in H2.
      apply lookup_lt_Some in H1. lia.
    - rewrite lookup_drop. apply lookup_take_Some. split; last lia.
      rewrite<-H1. f_equiv. lia.
    - rewrite<-H2. rewrite last_drop.
      + eapply last_take.
        by apply lookup_lt_Some in H2.
      + rewrite length_take. apply lookup_lt_Some in H2. apply lookup_lt_Some in H1. lia.
  Qed.

  Lemma uforest_connect (g : G) (a b : A) :
    is_uforest g → ¬ connected0 g a b → is_uforest (g ∪ uedge a b).
  Proof.
    intros [] Hnconn.
    constructor.
    { intros x y HH.
      apply elem_of_union.
      apply elem_of_union in HH as [].
      + left. apply uforest_undirected0. done.
      + right. apply uedge_undirected. done. }
    intros x xs Hpath.
    destruct (find_first_has_edge ([x] ++ xs ++ [x]) a b) as [(i1 & Hi1v & Hi1r)|H1].
    {
      (* Use wlog (a,b) here *)
      unfold has_edge in Hi1v.
      wlog: a b Hpath Hi1v Hi1r Hnconn / bar xs x i1 a b; unfold bar.
      {
        intros Hwlog.
        destruct Hi1v.
        { apply (Hwlog a b); eauto. }
        apply (Hwlog b a); eauto.
        - rewrite uedge_sym. done.
        - intro. rewrite has_edge_sym. eauto.
        - contradict Hnconn. apply connected0_sym; eauto.
      }
      clear Hi1v. intros [Hi1vA Hi1vB].
      (* Now we are in the situation x .. a b ... x *)
      assert (path g (take (i1+1) ([x] ++ xs ++ [x]))) as Hpath1.
      {
        apply (path_has_edge g a b).
        - eapply path_prefix, Hpath. apply prefix_take.
        - intros j He.
          apply has_edge_take in He as [He Hle].
          assert (j < i1) by lia.
          eapply Hi1r; done.
      }
      destruct (find_first_has_edge (drop (i1 + 1) ([x] ++ xs ++ [x])) a b).
      {
        (* Now we are in the situation x ... a b ... (ab|ba) ... x *)
        destruct H0 as (i2 & He & Hne).
        assert (path g (take (i2+1) $ drop (i1+1) ([x] ++ xs ++ [x]))) as Hpath2.
        {
          apply (path_has_edge g a b).
          - eapply path_prefix, path_suffix, Hpath; [apply prefix_take|].
            apply suffix_drop.
          - intros j He'.
            rewrite <-has_edge_take in He'.
            destruct He' as [He' Hne'].
            assert (j < i2) by lia.
            eapply Hne; done.
        }
        assert (take (i2 + 1) (drop (i1 + 1) ([x] ++ xs ++ [x])) !! 0 = Some b) as Hsb.
        {
          rewrite lookup_take; last lia. rewrite lookup_drop.
          rewrite Nat.add_0_r. done.
        }
        destruct He as [He|He].
        {
          (* Now we are in the situation x ... a b ... a b ... x *)
          exfalso. apply Hnconn. apply connected0_sym; first done.
          apply connected0_alt.
          eexists.
          split; first done. split; first done.
          replace (i2+1) with (S i2) by lia.
          apply last_take_Some. destruct He. done.
        }
        {
          (* Now we are in the situation x ... a b ... b a ... x *)
          assert (last (take (i2 + 1) (drop (i1 + 1) ([x] ++ xs ++ [x]))) = Some b) as Hsb'.
          {
            replace (i2 + 1) with (S i2) by lia.
            destruct He.
            rewrite last_take; first done.
            apply lookup_lt_Some in H0. done.
          }
          destruct He.
          destruct (decide (i2 = 0)).
          {
            subst. simpl in *.
            rewrite lookup_drop in H0.
            apply lookup_take_Some in Hsb as [Hsb ?]. rewrite lookup_drop in Hsb.
            rewrite lookup_drop in H1.
            exists i1, a.
            split; eauto.
            rewrite -H1. f_equiv. lia.
          }
          rewrite take_drop_commute in Hpath2.
          replace (i1 + 1 + (i2 + 1)) with (S (i1 + (i2 + 1))) in Hpath2 by lia.
          eapply has_u_turn_mid.
          + constructor; eauto.
          + exact Hpath2.
          + lia.
          + apply lookup_take_Some in Hsb as [Hsb ?].
            rewrite lookup_drop in Hsb. replace (i1 + 1 + 0) with (i1 + 1) in Hsb by lia.
            done.
          + rewrite lookup_drop in H0. rewrite -H0. f_equiv. lia.
        }
      }
      {
        (* Now we are in the situation x ... a b ... x *)
        assert (path g (drop (i1+1) ([x] ++ xs ++ [x]))) as Hpath2.
        {
          apply (path_has_edge g a b).
          - eapply path_suffix, Hpath. apply suffix_drop.
          - intros j He'. eapply H0. done.
        }
        contradict Hnconn.
        apply connected0_sym; first done.
        apply (connected0_trans g b x a).
        - apply connected0_alt. eexists.
          split; first exact Hpath2.
          split.
          + rewrite lookup_drop. rewrite <- Hi1vB. f_equiv. lia.
          + rewrite last_drop.
            * rewrite app_assoc. rewrite last_snoc. done.
            * apply lookup_lt_Some in Hi1vB. done.
        - apply connected0_alt. eexists.
          split; first exact Hpath1; replace (i1 + 1) with (S i1) by lia.
          split; first done.
          rewrite last_take; first done.
          apply lookup_lt_Some in Hi1vA. done.
      }
    }
    (* No (a,b)|(b,a) *)
    apply uforest_u_turns0. revert H1 Hpath.
    generalize ([x] ++ xs ++ [x]). intros.
    intros i q r Hq Hr.
    specialize (Hpath i q r).
    rewrite-> elem_of_union in Hpath.
    destruct Hpath; eauto.
    specialize (H1 i). exfalso. apply H1.
    unfold has_edge.
    assert ((q = a ∧ r = b) ∨ (q = b ∧ r = a)) as [[]|[]] by (unfold uedge in *; set_solver);
    subst; eauto.
  Qed.

  Lemma uforest_disconnect (g : G) (a b : A) :
    is_uforest g → (a,b) ∈ g → ¬ connected0 (g ∖ uedge a b) a b.
  Proof.
    intros [] Hedge [|Hconn].
    { subst. eapply uforest_no_self_loops; try constructor; eauto. }
    destruct Hconn as (xs & Hpath).
    apply path_no_u_turn in Hpath.
    - destruct Hpath as (xs' & Hpath' & Hnut).
      pose proof (uforest_u_turns0 b ([a] ++ xs')).
      destruct H0.
      {
        simpl. apply path_cons; first by apply uforest_undirected.
        eapply path_subseteq; last done. set_solver.
      }
      destruct H0. destruct H0.
      destruct x; simpl in *.
      + assert (x0 = b) as -> by qed. simplify_eq.
        destruct xs'; simplify_eq/=.
        * specialize (Hpath' 0 a b); simpl in *. unfold uedge in *. set_solver.
        * specialize (Hpath' 0 a b); simpl in *. unfold uedge in *. set_solver.
      + apply Hnut. exists x,x0. split; eauto.
    - intros ->. pose proof (uforest_no_self_loops g).
      cut ((b,b) ∉ g). { intro Q. apply Q. done. }
      apply H0. constructor; done.
  Qed.

  Lemma uforest_delete g x1 x2 :
    is_uforest g → is_uforest (g ∖ uedge x1 x2).
  Proof.
    intros [Hundir Huturn]. constructor.
    - intros y1 y2 Hy. unfold uedge in *. set_solver.
    - intros y ys Hp. apply Huturn. eapply path_subseteq, Hp. set_solver.
  Qed.

  Lemma uforest_empty : is_uforest ∅.
  Proof.
    constructor; [unfold undirected; set_solver|].
    intros x [|y ys] Hp; simpl in *.
    - specialize (Hp 0 x x). set_solver.
    - specialize (Hp 0 x y). set_solver.
  Qed.

  Lemma uforest_extend (x y : A) (g : uforest A) :
    x ≠ y → lone g y →
    is_uforest g → is_uforest (g ∪ uedge x y).
  Proof.
    intros Hneq Hlone [].
    apply uforest_connect; [done..|].
    intros [->|[]]; eauto.
    unfold path in *. unfold lone in *.
    destruct (([x] ++ x0 ++ [y]) !! length x0) eqn:E.
    2: {
      apply lookup_ge_None_1 in E. simpl in *.
      rewrite length_app in E. lia.
    }
    eapply Hlone.
    apply uforest_undirected0.
    eapply (H0 (length x0)); [done|].
    replace (length x0 + 1) with (length ([x] ++ x0) + 0); simpl; [|lia].
    by rewrite lookup_app_add.
  Qed.

  Lemma uforest_modify (x y z : A) (g : uforest A) :
    x ≠ z → y ≠ z →
    is_uforest g → (x,y) ∈ g → (x,z) ∈ g →
    is_uforest ((g ∖ uedge x z) ∪ uedge y z).
  Proof.
    intros Hxnz Hynz Hforest Hxy Hxz.
    apply uforest_connect; try done.
    - by apply uforest_delete.
    - pose proof (uforest_disconnect g x z Hforest Hxz) as Hconn.
      intro Hconn'.
      eapply connected0_trans in Hconn'.
      { apply Hconn. exact Hconn'. }
      apply connected0_edge.
      unfold uedge. set_solver.
  Qed.

  Definition uvertices (g : G) : gset A :=
    set_map fst g ∪ set_map snd g.

  Definition no_u_turns (f : A → option A) :=
    ∀ a b c, f a = Some b → f b = Some c → a ≠ c.

  Fixpoint search_iter
    (g : uforest A) (f : A → option A) (a : A) (n : nat) : A :=
    match n with
    | 0 => a
    | S n => match f a with
             | None => a
             | Some a' => search_iter g f a' n
             end
    end.

  Definition search (g : uforest A) (x : A) (f : A → option A) : A :=
    search_iter g f x (size (uvertices g)).

  Fixpoint search_iter_list
    (g : uforest A) (f : A → option A) (a : A) (n : nat) : list A :=
    match n with
    | 0 => []
    | S n => match f a with
             | None => []
             | Some a' => a' :: search_iter_list g f a' n
             end
    end.

  Definition valid (g : uforest A) (f : A → option A) :=
    ∀ x y, x ∈ uvertices g → f x = Some y → (x,y) ∈ g.

  Definition fpath (g : G) (f : A → option A) (xs : P) :=
    ∀ i a b, xs !! i = Some a → xs !! (i+1) = Some b → f a = Some b.

  Lemma fpath_sub (g : G) (f : A → option A) (xs ys : P) :
    fpath g f (xs ++ ys) → fpath g f xs.
  Proof.
    intros Hpath i a b Ha Hb.
    eapply Hpath.
    - rewrite lookup_app_l; first done.
      eapply lookup_lt_Some; done.
    - rewrite lookup_app_l; first done.
      eapply lookup_lt_Some; done.
  Qed.

  Lemma edge_in_uvertices (g : G) (x y : A) :
    (x,y) ∈ g → y ∈ uvertices g.
  Proof.
    intro. unfold uvertices.
    apply elem_of_union_r.
    apply elem_of_map.
    exists (x,y). simpl. eauto.
  Qed.

  Lemma fpath_uvertices (g : G) (f : A → option A) (x : A) (xs : P) :
    valid g f → x ∈ uvertices g → fpath g f (x::xs) → ∀ a, a ∈ (x::xs) → a ∈ uvertices g.
  Proof.
    rewrite <- (reverse_involutive xs).
    generalize (reverse xs). clear xs.
    intros xs Hvalid Hvert Hfpath.
    induction xs as [|y xs IHxs]; simpl; intros a Hin.
    { apply elem_of_cons in Hin as []; qed. }
    rewrite reverse_cons in Hin.
    rewrite reverse_cons in Hfpath.
    rewrite-> app_comm_cons in *.
    apply elem_of_app in Hin as [].
    { apply IHxs; eauto.
      eapply fpath_sub; done. }
    assert (a = y) as <- by set_solver. clear H0.
    unfold valid in *.
    destruct xs; simpl in *.
    { eapply edge_in_uvertices. eapply Hvalid; first done.
      by apply (Hfpath 0). }
    eapply edge_in_uvertices. eapply Hvalid.
    { eapply IHxs; first by eapply fpath_sub.
      rewrite reverse_cons. rewrite app_comm_cons.
      apply elem_of_app. right. assert (∀ (x:A), x ∈ [x]) by set_solver.
      apply H0. }
    eapply (Hfpath (length (x :: reverse xs))).
    - rewrite reverse_cons. rewrite app_comm_cons.
      rewrite lookup_app_l; last first.
      { rewrite app_comm_cons.
        rewrite length_app. simpl. lia. }
      rewrite app_comm_cons.
      replace (length (x :: reverse xs)) with (length (x :: reverse xs) + 0) by lia.
      by rewrite lookup_app_add.
    - rewrite app_comm_cons.
      rewrite lookup_app_r; last first.
      { rewrite reverse_cons. rewrite app_comm_cons. rewrite length_app. simpl.
        lia. }
      simpl.
      rewrite reverse_cons. rewrite length_app. simpl.
      replace (length (reverse xs) + 1 - (length (reverse xs) + 1)) with 0 by lia. done.
  Qed.

  Lemma fpath_path (g : G) (f : A → option A) (x : A) (xs : P) :
    x ∈ uvertices g → valid g f → fpath g f (x::xs) → path g (x::xs).
  Proof.
    intros Hvert Hvalid Hfpath i a b Ha Hb.
    apply Hvalid.
    - eapply fpath_uvertices; try done. eapply elem_of_list_lookup_2;done.
    - unfold fpath in *. eapply Hfpath; done.
  Qed.

  Lemma fpath_drop (g : G) (f : A → option A) (xs : P) (k : nat) :
    fpath g f xs → fpath g f (drop k xs).
  Proof.
    intros Hfpath i a b Ha Hb.
    rewrite-> (lookup_drop xs) in Ha.
    rewrite-> (lookup_drop xs) in Hb.
    eapply Hfpath; first exact Ha.
    rewrite <-Nat.add_assoc. done.
  Qed.

  Lemma fpath_take (g : G) (f : A → option A) (xs : P) (k : nat) :
    fpath g f xs → fpath g f (take k xs).
  Proof.
    intros Hfpath i a b Ha Hb.
    apply lookup_take_Some in Ha as [].
    apply lookup_take_Some in Hb as [].
    eapply Hfpath; eauto.
  Qed.

  Lemma fpaths_no_u_turns f g xs :
    no_u_turns f → fpath g f xs → ¬ has_u_turn xs.
  Proof.
    intros Hnut Hpath Hut.
    destruct Hut as (i & x & H1 & H2).
    unfold fpath in *.
    destruct (xs !! (i+1)) eqn:E.
    - pose proof (Hpath _ _ _ H1 E).
      replace (i+2) with (i+1+1) in H2 by lia.
      pose proof (Hpath _ _ _ E H2).
      eapply Hnut; eauto.
    - apply lookup_ge_None_1 in E.
      apply lookup_lt_Some in H2. lia.
  Qed.

  Lemma uforest_no_floops (g : G) (f : A → option A) (x y : A) (xs : P) i j :
    valid g f → no_u_turns f → is_uforest g → x ∈ uvertices g →
    xs !! 0 = Some x → i < j → xs !! i = Some y → xs !! j = Some y →
    fpath g f xs → False.
  Proof.
    intros Hvalid Hnut Hforest Hvert Hstart Hle H1 H2 Hfpath.
    assert (path g xs).
    { destruct xs; simplify_eq/=. apply fpath_path in Hfpath; try done. }
    assert (has_u_turn xs).
    { eapply has_u_turn_mid; eauto.
      eapply path_suffix, path_prefix, H0; [apply suffix_drop|]. apply prefix_take. }
    eapply fpaths_no_u_turns; eauto.
  Qed.

  Lemma uforest_no_floops' (g : G) (f : A → option A) (x : A) (xs : P) :
    valid g f → no_u_turns f → is_uforest g → x ∈ uvertices g → fpath g f ([x] ++ xs ++ [x]) → False.
  Proof.
    intros Hvalid Hnut [] Hvert Hfpath.
    apply fpath_path in Hfpath as Hpath; try done.
    edestruct uforest_u_turns0; first exact Hpath.
    destruct H0 as (y & Hy1 & Hy2).
    unfold fpath in Hfpath.
    destruct (([x] ++ xs ++ [x]) !! (x0 + 1)) eqn:Hymid; last first.
    { apply lookup_ge_None_1 in Hymid.
      apply lookup_lt_Some in Hy2.
      lia. }
    specialize (Hfpath x0 y a Hy1 Hymid) as Q1.
    specialize (Hfpath (x0 + 1) a y Hymid) as Q2. replace (x0 + 1 + 1)  with (x0 + 2)  in Q2 by lia.
    specialize (Q2 Hy2).
    unfold no_u_turns in *.
    eapply Hnut; eauto.
  Qed.

  Lemma search_lemma (g : uforest A) (x : A) (f : A → option A) :
    is_uforest g → no_u_turns f → valid g f →
    x ∈ uvertices g → f (search g x f) = None.
  Proof.
    intros Hforest Huturn Hvalid Hx.
    (* Suppose f (search g x f) = Some y *)
    destruct (f (search g x f)) eqn:Hss;[|done].
    exfalso.
    (* Have a long f-path in g *)
    assert (∃ xs, fpath g f (x::xs) ∧ size (uvertices g) < length (x::xs)).
    { unfold search in Hss.
      exists (search_iter_list g f x (size (uvertices g))).
      revert x Hss Hx.
      induction (size (uvertices g)); simpl in *; intros.
      { split;last lia. unfold fpath. intros. destruct i; simplify_eq/=. }
      destruct (f x) eqn:E; simplify_eq/=.
      specialize (IHn _ Hss). destruct IHn.
      { unfold valid in *.
        eapply edge_in_uvertices. eapply Hvalid; eauto. }
      split; last lia.
      unfold fpath in *.
      intros. destruct i; simplify_eq/=; eauto. }
    destruct H0 as (xs & Hpath & Hsize).
    (* Since the path is longer than the number of uvertices, there must be a duplicate vertex in the path *)
    destruct (list_pigeonhole (x::xs) (elements (uvertices g)))
      as (i & j & y & Hneq & Hi & Hj).
    { intros x'. rewrite elem_of_elements. eauto using fpath_uvertices. }
    { done. }
    (* Duplicate vertex gives a u-turn → contradiction *)
    eapply uforest_no_floops; eauto; done.
  Qed.

  Lemma search_in_uvertices (g : uforest A) (x : A) (f: A → option A) :
    is_uforest g → valid g f → x ∈ uvertices g → search g x f ∈ uvertices g.
  Proof.
    unfold search.
    revert x.
    induction (size _); simpl; eauto. intros.
    destruct (f x) eqn:E; eauto. apply IHn; eauto.
    unfold valid in *.
    eapply edge_in_uvertices; eauto.
  Qed.

  Lemma search_exists (g : uforest A) (x : A) (f : A → option A) :
    is_uforest g → no_u_turns f → valid g f →
    x ∈ uvertices g → ∃ y, f y = None ∧ y ∈ uvertices g.
  Proof.
    intros. exists (search g x f).
    split.
    + apply search_lemma; eauto.
    + apply search_in_uvertices; eauto.
  Qed.

  Lemma path_uvertices g xs :
    is_uforest g → 2 ≤ length xs → path g xs → ∀ x, x ∈ xs → x ∈ uvertices g.
  Proof.
    intros Hforest. intros.
    unfold path in *.
    apply elem_of_list_lookup in H2 as (? & ?).
    destruct x0.
    - destruct (xs !! 1) eqn:E.
      + specialize (H1 _ _ _ H2 E).
        eapply edge_in_uvertices.
        eapply uforest_undirected; eauto.
      + eapply lookup_ge_None in E. lia.
    - destruct (xs !! x0) eqn:E.
      + eapply edge_in_uvertices. eapply H1; eauto. rewrite <- H2.
        f_equiv. lia.
      + eapply lookup_lt_Some in H2.
        eapply lookup_ge_None in E.
        lia.
  Qed.

  Lemma long_paths_have_u_turns g xs :
    is_uforest g → size (uvertices g)+10 < length xs → path g xs → has_u_turn xs.
  Proof.
    intros Hforest Hsize Hpath.
    destruct (list_pigeonhole xs (elements (uvertices g)))
      as (i & j & y & Hi & Hj & Hlt); eauto.
    { intros x. rewrite elem_of_elements. eapply path_uvertices; eauto with lia. }
    { rewrite /size /set_size /= in Hsize. lia. }
    assert (path g (drop i (take (S j) xs))) as Hsubpath.
    { eapply path_suffix, path_prefix, Hpath; [apply suffix_drop|].
      apply prefix_take. }
    eapply has_u_turn_mid; eauto.
  Qed.

  Definition asym (R : relation A) :=
    ∀ x y, R x y → R y x → x = y.
  Definition Rpath (R : relation A) (xs : list A) : Prop :=
    ∀ i x y, xs !! i = Some x → xs !! (i + 1) = Some y → R y x.
  Definition Rvalid (R : relation A) (g : uforest A) : Prop :=
    ∀ x y, R x y → (y,x) ∈ g.

  Lemma Rpath_path g (R : A → A → Prop) (xs : list A) :
    Rpath R xs → Rvalid R g → path g xs.
  Proof.
    intros H1 H2 i a b Ha Hb.
    eapply H2.
    eapply H1; eauto.
  Qed.

  Lemma Rpath_no_u_turns R xs g :
    is_uforest g → Rvalid R g → Rpath R xs → asym R → ¬ has_u_turn xs.
  Proof.
    intros Hforest Hvalid H1 H2 (i & x & Q1 & Q2).
    destruct (xs !! (i + 1)) eqn:E; last first.
    { eapply lookup_ge_None in E.
      eapply lookup_lt_Some in Q2. lia. }
    assert (x = a).
    {
      eapply H2.
      - eapply H1; first exact E.
        replace (i + 1 + 1) with (i + 2) by lia. done.
      - eapply H1; last done. done.
    }
    subst.
    eapply uforest_no_self_loops; first done.
    eapply Hvalid.
    eapply H1; first exact Q1. done.
  Qed.

  Lemma Rpath_snoc xs x y R :
    Rpath R (xs ++ [x]) → R y x → Rpath R ((xs ++ [x]) ++ [y]).
  Proof.
    intros.
    unfold Rpath in *.
    intros.
    destruct (decide (i + 1 < length (xs ++ [x]))).
    - eapply (H0 i).
      + rewrite lookup_app in H2.
        rewrite <-H2.
        destruct ((xs ++ [x]) !! i) eqn:E; eauto.
        destruct (i - length (xs ++ [x])) eqn:F; simplify_eq/=.
        eapply lookup_ge_None in E.
        assert (length (xs ++ [x]) = i) by lia.
        subst.
        rewrite lookup_app_add in H3. simpl in *. simplify_eq.
      + rewrite lookup_app in H3.
        rewrite <-H3.
        destruct ((xs ++ [x]) !! (i + 1)) eqn:E; eauto.
        destruct (i + 1 - length (xs ++ [x])) eqn:F; simplify_eq/=.
        eapply lookup_ge_None in E. lia.
    - assert (i + 1 = length (xs ++ [x])).
      { eapply lookup_lt_Some in H3. rewrite length_app in H3. simpl in *. lia. }
      rewrite H4 in H3.
      replace (length (xs ++ [x])) with (length (xs ++ [x]) + 0) in H3 by lia.
      rewrite lookup_app_add in H3. simplify_eq/=.
      rewrite lookup_app in H2.
      rewrite lookup_app in H2.
      destruct (xs !! i) eqn:E.
      { eapply lookup_lt_Some in E.
        rewrite length_app in H4. simpl in *. lia. }
      destruct (i - length xs) eqn:F.
      + simpl in *. simplify_eq. done.
      + simpl in *. destruct ((i - length (xs ++ [x]))) eqn:G;
        simplify_eq/=.
        rewrite length_app in G. simpl in *.
        rewrite length_app in n.
        rewrite length_app in H4.
        simpl in *. lia.
  Qed.

  Definition ureachable R g n x :=
    ∃ xs, Rpath R (xs ++ [x]) ∧
          length (xs ++ [x]) + n > size (uvertices g) + 10.

  Lemma rel_wf_helper R (g : uforest A) n :
    is_uforest g → asym R → Rvalid R g →
    ∀ x, ureachable R g n x → Acc R x.
  Proof.
    intros Hforest Hasym Hvalid.
    induction n.
    - intros x (xs & HRpath & Hlen).
      exfalso. eapply Rpath_no_u_turns; eauto.
      eapply long_paths_have_u_turns; eauto with lia.
      eapply Rpath_path; eauto.
    - intros x (xs & HRpath & Hlen).
      constructor. intros. eapply IHn.
      exists (xs ++ [x]). split.
      + eapply Rpath_snoc; eauto.
      + simpl. rewrite length_app; simpl. lia.
  Qed.

  Lemma ureachable_0 R g a :
    ureachable R g (size (uvertices g) + 10) a.
  Proof.
    unfold ureachable.
    exists [].
    split.
    - unfold Rpath. intros. simpl in *.
      destruct i; simplify_eq/=.
    - simpl in *. lia.
  Qed.

  Lemma rel_wf R g :
    asym R →
    Rvalid R g →
    is_uforest g → well_founded R.
  Proof.
    intros. unfold well_founded. intro.
    eapply rel_wf_helper; eauto using ureachable_0.
  Qed.

  Lemma uforest_ind R g (P : A → Prop) :
    is_uforest g →
    asym R →
    (∀ x, (∀ y, R x y → (x,y) ∈ g → P y) → P x) → (∀ x, P x).
  Proof.
    intros Hforest Hasym Hind.
    set T := λ x y, R y x ∧ (y,x) ∈ g.
    assert (asym T).
    { intros x y [] []. eapply Hasym; eauto. }
    assert (Rvalid T g).
    { intros x y []. done. }
    pose proof (rel_wf T g H0 H1 Hforest).
    intros x. specialize (H2 x).
    induction H2. eapply Hind.
    intros. eapply H3. split; eauto.
  Qed.

End uforest.

Lemma connected0_elem_of `{Countable A} (f : uforest A) v1 v2 :
  is_uforest f →
  connected0 f v1 v2 ↔ rtsc (λ x y, (x,y) ∈ f) v1 v2.
Proof.
  intros.
  rewrite connected0_alt.
  split.
  - intros (xs & Hpath & Qf & Ql). apply rtc_list.
    exists xs. rewrite head_lookup. split_and!; eauto.
    intros. left. eapply Hpath; rewrite ?Nat.add_1_r; eauto.
  - intros (xs & Qf & Ql & Hpath)%rtc_list.
    exists xs. rewrite -head_lookup. split_and!; eauto.
    intros ????. rewrite Nat.add_1_r. intros ?.
    edestruct Hpath; first exact H1; eauto.
    eapply uforest_undirected; eauto.
Qed.
