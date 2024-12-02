From iris.algebra Require Import gmap.
From iris.proofmode Require Export proofmode.
From iris.si_logic Require Export bi.
From dlfactris.algebra Require Export multiset.
From dlfactris.base_logic Require Import uforests.

Ltac sdec := repeat case_decide; simplify_eq/=; eauto; try done.

(* Definition uforest V := gset (V * V). *)
Notation cgraph V L := (gmap V (gmap V L)).

Section cgraph.
  Context `{Countable V} {L : ofe}.

  Definition out_edges (g : cgraph V L) (v : V) : gmap V L :=
    default ∅ (g !! v).

  Definition ms_insert (v v' : V) (ev' : gmap V L) (ins : multiset L) : multiset L :=
    from_option (λ x, {[+ x +]}) ∅ (ev' !! v) ⊎ ins.

  Definition in_labels (g : cgraph V L) (v : V) : multiset L :=
    map_fold (ms_insert v) ∅ g.

  Definition edge (g : cgraph V L) (ν1 ν2 : V) := is_Some (out_edges g ν1 !! ν2).

  Definition make_undirected (g : gset (V * V)) : gset (V * V) :=
    g ∪ set_map prod_swap g.

  Definition dedges (g : cgraph V L) : gset (V * V) :=
    dom (gmap_uncurry g).
  Definition to_uforest (g : cgraph V L) : uforest V :=
    make_undirected $ dedges g.

  Definition no_short_loops (g : cgraph V L) :=
    ∀ ν1 ν2, ¬(edge g ν1 ν2 ∧ edge g ν2 ν1).

  Definition cgraph_wf (g : cgraph V L) :=
    no_short_loops g ∧ is_uforest (to_uforest g).

  Definition uconn (g : cgraph V L) := rtsc (edge g).

  Section general.
    Lemma in_labels_insert g i x v :
      g !! i = None →
      in_labels (<[i:=x]> g) v ≡ from_option (λ x, {[+ x +]}) ∅ (x !! v) ⊎ in_labels g v.
    Proof.
      intros Hi.
      unfold in_labels at 1.
      erewrite map_fold_insert with (R := (≡));
      eauto; first apply _; first solve_proper.
      intros. unfold ms_insert.
      destruct (z1 !! v) eqn:E;
      destruct (z2 !! v) eqn:F; simpl; eauto.
      rewrite assoc.
      rewrite (comm (⊎) {[+ o +]}).
      rewrite assoc. done.
    Qed.

    Lemma in_labels_delete g i v y :
      g !! i = Some y →
      from_option (λ x, {[+ x +]}) ∅ (y !! v) ⊎ in_labels (delete i g) v ≡ in_labels g v.
    Proof.
      intro.
      pose proof (in_labels_insert (delete i g) i y v) as HH.
      rewrite insert_delete in HH; last done.
      rewrite HH; last by apply lookup_delete.
      done.
    Qed.

    Lemma in_labels_update g i x y v :
      g !! i = Some y →
      from_option (λ x, {[+ x +]}) ∅ (y !! v) ⊎ in_labels (<[i:=x]> g) v ≡
      from_option (λ x, {[+ x +]}) ∅ (x !! v) ⊎ in_labels g v.
    Proof.
      intro.
      assert (<[i:=x]> g = <[i:=x]> $ delete i g) as ->.
      { by rewrite insert_delete_insert. }
      rewrite in_labels_insert; last by apply lookup_delete.
      rewrite comm. rewrite -assoc.
      rewrite (comm (⊎) (in_labels _ _)).
      rewrite in_labels_delete; eauto.
    Qed.

    Lemma out_edges_in_labels_L g ν1 ν2 l :
      out_edges g ν1 !! ν2 = Some l →
      ∃ x, in_labels g ν2 ≡ {[+ l +]} ⊎ x.
    Proof.
      revert ν1 ν2 l.
      induction g using map_ind; intros.
      - rewrite lookup_empty in H0. inversion H0.
      - unfold out_edges in H1.
        rewrite lookup_insert_spec in H1.
        case_decide; simplify_eq.
        + exists (in_labels m ν2).
          rewrite in_labels_insert; eauto.
          rewrite H1. done.
        + destruct (m !! ν1) eqn:E. 2: { rewrite lookup_empty in H1. inversion H1. }
          destruct (IHg ν1 ν2 l).
          { unfold out_edges. rewrite E. done. }
          setoid_rewrite in_labels_insert; eauto.
          setoid_rewrite H3.
          exists (from_option (λ x, {[+ x +]}) ∅ (x !! ν2) ⊎ x0).
          rewrite !assoc.
          rewrite (comm (⊎) _ {[+ l +]}).
          done.
    Qed.

    Lemma no_in_labels_no_out_edge g ν1 ν2 :
      in_labels g ν2 = ∅ →
      out_edges g ν1 !! ν2 = None.
    Proof.
      intros Hin%multiset_empty_equiv_eq.
      destruct (out_edges g ν1 !! ν2) eqn:E; eauto.
      eapply out_edges_in_labels_L in E as [X Hin'].
      rewrite Hin' multiset_empty_equiv_eq multiset_disj_union_eq_empty in Hin.
      by destruct Hin.
    Qed.

    Lemma out_edges_insert (g : cgraph V L) (ν1 ν2 : V) e :
      out_edges (<[ ν1 := e ]> g) ν2 =
        if decide (ν1 = ν2) then e
        else out_edges g ν2.
    Proof.
      rewrite /out_edges. rewrite lookup_insert_spec.
      repeat case_decide; simplify_eq; done.
    Qed.

    Lemma in_labels_empty v :
      in_labels ∅ v = ∅.
    Proof.
      rewrite /in_labels map_fold_empty //.
    Qed.

    Lemma no_edges_no_uconn g v v' :
      out_edges g v = ∅ →
      in_labels g v = ∅ →
      uconn g v' v → v = v'.
    Proof.
      intros Hout Hin Hconn.
      eapply not_rtsc; last done.
      intros y. unfold edge. split; intros [].
      - rewrite Hout in H0. rewrite lookup_empty in H0. simplify_eq.
      - eapply no_in_labels_no_out_edge in Hin. erewrite H0 in Hin. simplify_eq.
    Qed.

    Lemma some_edge_L (g : cgraph V L) (ν1 ν2 : V) (l : L) :
      out_edges g ν1 !! ν2 = Some l → edge g ν1 ν2.
    Proof.
      unfold edge. intros ->. eauto.
    Qed.

    Lemma some_edge (g : cgraph V L) (ν1 ν2 : V) (l : L) :
      out_edges g ν1 !! ν2 ≡ Some l → edge g ν1 ν2.
    Proof.
      intro. inversion H0.
      unfold edge. rewrite -H1. eauto.
    Qed.

    Lemma not_uconn_out_disjoint g ν1 ν2 :
      ¬ uconn g ν1 ν2 → out_edges g ν1 ##ₘ out_edges g ν2.
    Proof.
      intros HH v.
      destruct (out_edges g ν1 !! v) eqn:E;
      destruct (out_edges g ν2 !! v) eqn:F; simpl; eauto.
      assert (edge g ν1 v); eauto using some_edge_L.

      assert (edge g ν2 v); eauto using some_edge_L.
      apply HH.
      eapply rtc_transitive; eapply rtc_once; [left|right]; eauto.
    Qed.
  End general.


  Section acyclicity.
    Lemma make_undirected_sc (R : relation V) (e : gset (V * V)) :
      (∀ x y, (x,y) ∈ e ↔ R x y) →
      ∀ x y, (x,y) ∈ make_undirected e ↔ sc R x y.
    Proof.
      intros. unfold make_undirected.
      rewrite elem_of_union.
      rewrite elem_of_set_map_prod_swap.
      split; intros []; [left|right|..]; naive_solver.
    Qed.

    Lemma gmap_uncurry_out_edges g x y :
      gmap_uncurry g !! (x, y) = out_edges g x !! y.
    Proof.
      rewrite lookup_gmap_uncurry.
      unfold out_edges.
      destruct (g !! x); simpl; eauto.
    Qed.

    Lemma elem_of_dedges x y g :
      (x, y) ∈ dedges g ↔ edge g x y.
    Proof.
      unfold dedges.
      rewrite elem_of_dom.
      unfold edge.
      rewrite gmap_uncurry_out_edges. done.
    Qed.

    Lemma elem_of_to_uforest g x y :
      (x,y) ∈ to_uforest g ↔ sc (edge g) x y.
    Proof.
      unfold to_uforest.
      eapply make_undirected_sc. intros.
      eapply elem_of_dedges.
    Qed.

    Lemma out_edges_empty v :
      out_edges ∅ v = ∅.
    Proof.
      unfold out_edges. rewrite lookup_empty //.
    Qed.

    Lemma edge_empty ν1 ν2 :
      edge ∅ ν1 ν2 ↔ False.
    Proof.
      split; intros [].
      rewrite out_edges_empty lookup_empty in H0. simplify_eq.
    Qed.

    Lemma to_uforest_empty :
      to_uforest ∅ = ∅.
    Proof.
      eapply set_eq. intros [x y].
      rewrite elem_of_to_uforest.
      unfold edge, sc.
      rewrite !out_edges_empty !lookup_empty //.
    Qed.

  End acyclicity.

  Section empty_cgraph.
    Lemma empty_wf :
      cgraph_wf ∅.
    Proof.
      unfold cgraph_wf.
      split.
      - intros ??. rewrite !edge_empty. naive_solver.
      - rewrite to_uforest_empty. eapply uforest_empty.
    Qed.
  End empty_cgraph.

  Section insert_edge.
    (* This function is only supposed to be called if there is not already an edge
       between ν1 and ν2. In fact, it's only supposed to be called if ν1 and ν2
       are complete disconnected. *)
    Definition insert_edge (g : cgraph V L) (ν1 ν2 : V) (l : L) :=
      <[ ν1 := <[ ν2 := l ]> $ out_edges g ν1 ]> g.

    Lemma out_edges_insert_edge (g : cgraph V L) (ν1 ν2 v3 : V) (l : L) :
      out_edges (insert_edge g ν1 ν2 l) v3 =
        if decide (ν1 = v3) then <[ ν2 := l ]> $ out_edges g v3
        else out_edges g v3.
    Proof.
      unfold insert_edge. rewrite out_edges_insert.
      repeat case_decide; simplify_eq; done.
    Qed.

    Lemma in_labels_insert_edge (g : cgraph V L) (ν1 ν2 v3 : V) (l : L) :
      ¬ edge g ν1 ν2 →
      in_labels (insert_edge g ν1 ν2 l) v3 ≡
        if decide (ν2 = v3) then {[+ l +]} ⊎ in_labels g v3
        else in_labels g v3.
    Proof.
      intros Hnotedge.
      unfold insert_edge.
      destruct (g !! ν1) eqn:E.
      - assert (g !! ν1 = Some g0) as HH; eauto.
        pose proof (in_labels_update g ν1 (<[ν2:=l]> (out_edges g ν1)) g0 v3 HH) as H0.
        rewrite lookup_insert_spec in H0.
        destruct (g0 !! v3) eqn:F; simpl in *.
        + case_decide; simplify_eq/=.
          * exfalso. apply Hnotedge.
            unfold edge. unfold out_edges.
            rewrite E. rewrite F. eauto.
          * unfold out_edges in H0 at 2.
            rewrite E in H0.
            rewrite F in H0. simpl in *. by apply (inj _) in H0.
        + rewrite ->left_id in H0. 2: { intro. simpl. rewrite left_id. done. }
          rewrite H0. case_decide; simpl; eauto. unfold out_edges.
          rewrite HH. rewrite F. simpl. rewrite left_id. done.
      - rewrite in_labels_insert; eauto.
        rewrite lookup_insert_spec.
        case_decide; simplify_eq; try done.
        unfold out_edges.
        rewrite E. rewrite lookup_empty.
        simpl. rewrite left_id. done.
    Qed.

    Lemma edge_insert_edge g ν1 ν2 x y l :
      edge (insert_edge g ν1 ν2 l) x y ↔ edge g x y ∨ (x = ν1 ∧ y = ν2).
    Proof.
      unfold edge.
      rewrite out_edges_insert_edge.
      case_decide; subst.
      - rewrite lookup_insert_spec. case_decide; subst.
        + naive_solver.
        + naive_solver.
      - naive_solver.
    Qed.

    Lemma sc_edge_insert_edge g ν1 ν2 x y l :
      sc (edge (insert_edge g ν1 ν2 l)) x y ↔
        sc (edge g) x y ∨ (x = ν1 ∧ y = ν2) ∨ (x = ν2 ∧ y = ν1).
    Proof.
      split.
      - intros []; rewrite ->edge_insert_edge in H0;
        destruct H0; try naive_solver.
        + left. left. done.
        + left. right. done.
      - intros [].
        + destruct H0;[left|right]; rewrite edge_insert_edge; eauto.
        + destruct H0;[left|right]; rewrite edge_insert_edge; eauto.
          naive_solver.
    Qed.

    Lemma to_uforest_insert_edge g ν1 ν2 l :
      to_uforest (insert_edge g ν1 ν2 l) = to_uforest g ∪ uedge ν1 ν2.
    Proof.
      eapply set_eq. intros [x y].
      rewrite elem_of_union.
      rewrite !elem_of_to_uforest.
      rewrite !sc_edge_insert_edge.
      unfold uedge. set_solver.
    Qed.

    Lemma uconn_connected0 g ν1 ν2 :
      cgraph_wf g →
      uconn g ν1 ν2 ↔ connected0 (to_uforest g) ν1 ν2.
    Proof.
      unfold uconn. intros.
      rewrite connected0_elem_of. 2: { by destruct H0. }
      assert (∀ x y, sc (edge g) x y ↔ (x,y) ∈ to_uforest g).
      { intros. rewrite elem_of_to_uforest. done. }
      unfold rtsc.
      erewrite rtc_iff; eauto.
      intros.
      split.
      - intros. left. rewrite elem_of_to_uforest. done.
      - intros []; rewrite ->elem_of_to_uforest in H2; eauto.
        destruct H2; [right|left]; done.
    Qed.

    Lemma insert_edge_wf g ν1 ν2 l :
      ¬ uconn g ν1 ν2 →
      cgraph_wf g →
      cgraph_wf (insert_edge g ν1 ν2 l).
    Proof.
      intros H0 [].
      split.
      - intros x y. rewrite !edge_insert_edge.
        intros [].
        destruct H3; destruct H4.
        + eapply H1; eauto.
        + destruct H4; subst.
          eapply H0. eapply rtc_once.
          right. done.
        + destruct H3; subst.
          eapply H0. eapply rtc_once.
          right. done.
        + destruct H3. destruct H4. subst.
          eapply H0. constructor.
      - rewrite to_uforest_insert_edge.
        eapply uforest_connect; eauto.
        rewrite -uconn_connected0; done.
    Qed.
  End insert_edge.


  Section delete_edge.
    Definition delete_edge (g : cgraph V L) (ν1 ν2 : V) :=
      <[ ν1 := delete ν2 (out_edges g ν1) ]> g.

    Lemma out_edges_delete_edge (g : cgraph V L) (ν1 ν2 v3 : V) :
      out_edges (delete_edge g ν1 ν2) v3 =
        if decide (ν1 = v3) then delete ν2 (out_edges g v3)
        else out_edges g v3.
    Proof.
      unfold delete_edge. rewrite out_edges_insert.
      repeat case_decide; simplify_eq; done.
    Qed.

    Lemma in_labels_delete_edge_eq (g : cgraph V L) (ν1 ν2 : V) (l : L) (x : multiset L) :
      out_edges g ν1 !! ν2 = Some l →
      in_labels g ν2 ≡ {[+ l +]} ⊎ x →
      in_labels (delete_edge g ν1 ν2) ν2 ≡ x.
    Proof.
      intros H1 H2.
      unfold delete_edge.
      destruct (g !! ν1) eqn:E; last first.
      { unfold out_edges in H1. rewrite E lookup_empty in H1. simplify_eq. }
      pose proof (in_labels_update g ν1 (delete ν2 (out_edges g ν1)) g0 ν2 E) as H0.
      destruct (g0 !! ν2) eqn:F; simpl in *.
      - rewrite lookup_delete in H0.
        simpl in *.
        rewrite ->H2 in H0.
        unfold out_edges in H1.
        rewrite E in H1. rewrite F in H1. simplify_eq.
        revert H0. rewrite left_id. by intros H0%(inj _).
      - unfold out_edges in H1. rewrite E F in H1. simplify_eq.
    Qed.

    Lemma in_labels_delete_edge_neq (g : cgraph V L) (ν1 ν2 v3 : V) :
      ν2 ≠ v3 →
      in_labels (delete_edge g ν1 ν2) v3 ≡ in_labels g v3.
    Proof.
      intros Hneq.
      unfold delete_edge.
      destruct (g !! ν1) eqn:E.
      - pose proof (in_labels_update g ν1 (delete ν2 (out_edges g ν1)) g0 v3 E) as H0.
        destruct (g0 !! v3) eqn:F.
        + simpl in *.
          rewrite lookup_delete_spec in H0.
          unfold out_edges in H0 at 2.
          rewrite E in H0.
          rewrite F in H0.
          case_decide; simplify_eq.
          simpl in *.
          by apply (inj _) in H0.
        + simpl in *. rewrite ->left_id in H0.
          2: { intro. simpl. rewrite left_id. done. }
          rewrite H0.
          rewrite lookup_delete_spec.
          unfold out_edges. rewrite E.
          rewrite F. case_decide; simplify_eq; simpl.
          rewrite left_id. done.
      - rewrite in_labels_insert; eauto.
        rewrite lookup_delete_spec.
        unfold out_edges.
        rewrite E. rewrite lookup_empty.
        case_decide; simpl; rewrite left_id //.
    Qed.

    Lemma edge_delete_edge g ν1 ν2 w1 w2 :
      ν1 ≠ w1 ∨ ν2 ≠ w2 →
      edge g w1 w2 →
      edge (delete_edge g ν1 ν2) w1 w2.
    Proof.
      intros.
      unfold edge.
      rewrite out_edges_delete_edge.
      case_decide; simplify_eq; eauto.
      rewrite lookup_delete_spec.
      case_decide; simplify_eq; eauto.
      naive_solver.
    Qed.

    Lemma edge_delete_edge' g ν1 ν2 w1 w2 :
      edge g w1 w2 →
      edge (delete_edge g ν1 ν2) w1 w2 ∨ (ν1 = w1 ∧ ν2 = w2).
    Proof.
      intros.
      pose proof (edge_delete_edge g ν1 ν2 w1 w2).
      destruct (decide (ν1 = w1));
      destruct (decide (ν2 = w2));
      naive_solver.
    Qed.

    Lemma edge_delete_edge'' g ν1 ν2 x y :
      edge (delete_edge g ν1 ν2) x y ↔ edge g x y ∧ ¬ (x = ν1 ∧ y = ν2).
    Proof.
      split.
      - intros.
        move: H0.
        unfold edge. rewrite !out_edges_delete_edge.
        repeat case_decide; subst.
        + rewrite lookup_delete_spec.
          case_decide; subst; first by intros []. naive_solver.
        +  naive_solver.
      - intros []. eapply edge_delete_edge; eauto.
        destruct (decide (x = ν1)); destruct (decide (y = ν2)); naive_solver.
    Qed.

    Lemma elem_of_uedge (x y a b : V) :
      (x, y) ∈ uedge a b ↔ (x = a ∧ y = b) ∨ (x = b ∧ y = a).
    Proof.
      unfold uedge.
      set_solver.
    Qed.

    Lemma edge_dec g x y : Decision (edge g x y).
    Proof.
      unfold edge.
      destruct (out_edges g x !! y).
      - left. eauto.
      - right. eauto.
    Qed.

    Lemma to_uforest_delete_edge g ν1 ν2 :
      no_short_loops g →
      edge g ν1 ν2 →
      to_uforest (delete_edge g ν1 ν2) = to_uforest g ∖ uedge ν1 ν2.
    Proof.
      intros.
      eapply set_eq. intros [x y].
      rewrite elem_of_difference.
      rewrite !elem_of_to_uforest.
      rewrite !sc_or.
      specialize (H0 ν1 ν2).
      rewrite !edge_delete_edge''.
      rewrite elem_of_uedge.
      naive_solver.
    Qed.

    Definition cgraph_equiv g1 g2 :=
      ∀ v, out_edges g1 v = out_edges g2 v.

    Lemma cgraph_equiv_edge g1 g2 ν1 ν2 :
      cgraph_equiv g1 g2 →
      edge g1 ν1 ν2 →
      edge g2 ν1 ν2.
    Proof.
      unfold edge. intros ->. done.
    Qed.

    Lemma uconn_equiv g1 g2 ν1 ν2 :
      cgraph_equiv g1 g2 →
      uconn g1 ν1 ν2 → uconn g2 ν1 ν2.
    Proof.
      intros He Hc.
      induction Hc; try reflexivity.
      eapply rtc_transitive; eauto.
      eapply rtc_once.
      destruct H0;[left|right]; eauto using cgraph_equiv_edge.
    Qed.

    Lemma delete_edge_not_edge g ν1 ν2 :
      ¬ edge g ν1 ν2 →
      cgraph_equiv (delete_edge g ν1 ν2) g.
    Proof.
      intros ??.
      rewrite out_edges_delete_edge.
      case_decide; subst; eauto.
      rewrite delete_notin; eauto.
      destruct (out_edges g v !! ν2) eqn:E; eauto.
      exfalso. eapply H0. unfold edge. rewrite E. eauto.
    Qed.

    Lemma cgraph_equiv_sym g1 g2 :
      cgraph_equiv g1 g2 → cgraph_equiv g2 g1.
    Proof.
      intros ??.
      symmetry. eapply H0.
    Qed.

    Lemma to_uforest_proper : Proper (cgraph_equiv ==> (=)) to_uforest.
    Proof.
      solve_proper_prepare.
      eapply set_eq.
      intros [a b].
      rewrite !elem_of_to_uforest.
      rewrite !sc_or.
      split; intros []; eauto using cgraph_equiv_edge,cgraph_equiv_sym.
    Qed.

    Lemma delete_edge_wf g ν1 ν2 :
      cgraph_wf g →
      cgraph_wf (delete_edge g ν1 ν2).
    Proof.
      intros [].
      unfold cgraph_wf.
      split.
      - unfold no_short_loops. intros x y [].
        apply edge_delete_edge'' in H2 as [].
        apply edge_delete_edge'' in H3 as [].
        unfold no_short_loops in *.
        eapply H0. eauto.
      - destruct (decide (edge g ν1 ν2)).
        + rewrite to_uforest_delete_edge; eauto.
          eapply uforest_delete; done.
        + assert (to_uforest (delete_edge g ν1 ν2) = to_uforest g).
          {
            eapply to_uforest_proper.
            eapply delete_edge_not_edge. done.
          }
          rewrite H2. done.
    Qed.

    Lemma delete_edge_uconn g ν1 ν2 :
      cgraph_wf g →
      edge g ν1 ν2 →
      ¬ uconn (delete_edge g ν1 ν2) ν1 ν2.
    Proof.
      intros [] ?.
      rewrite uconn_connected0; last by eapply delete_edge_wf.
      rewrite to_uforest_delete_edge; eauto.
      eapply uforest_disconnect; eauto.
      rewrite elem_of_to_uforest; eauto.
      by left.
    Qed.

    Lemma no_self_edge g ν1 ν2 :
      cgraph_wf g →
      edge g ν1 ν2 → ν1 ≠ ν2.
    Proof.
      intros H1 H2 ->.
      eapply delete_edge_uconn; eauto. reflexivity.
    Qed.

    Lemma no_self_edge' g ν1 ν2 :
      cgraph_wf g →
      sc (edge g) ν1 ν2 → ν1 ≠ ν2.
    Proof.
      intros H1 [] ->; eapply no_self_edge; eauto.
    Qed.

    Lemma no_self_edge'' g v :
      cgraph_wf g →
      out_edges g v !! v = None.
    Proof.
      intros.
      destruct (_!!_) eqn:E; eauto.
      exfalso.
      eapply no_self_edge; eauto using some_edge_L.
    Qed.

    Lemma no_triangle g ν1 ν2 v3 :
      cgraph_wf g →
      sc (edge g) ν1 ν2 →
      sc (edge g) ν2 v3 →
      sc (edge g) v3 ν1 →
      False.
    Proof.
      intros Hwf H1 H2 H3.
      assert (ν1 ≠ ν2); eauto using no_self_edge'.
      assert (ν2 ≠ v3); eauto using no_self_edge'.
      assert (v3 ≠ ν1); eauto using no_self_edge'.
      destruct H1,H2,H3; eapply delete_edge_uconn; eauto;
      eapply rtc_transitive; eapply rtc_once;
      try (solve [left; eapply edge_delete_edge; eauto] ||
           solve [right; eapply edge_delete_edge; eauto]).
      - left. eapply edge_delete_edge; eauto.
      - left. eapply edge_delete_edge.
        + right. intro. eapply H4. symmetry. done.
        + eauto.
      - right. eapply edge_delete_edge; eauto.
    Qed.

    Lemma edge_out_disjoint g ν1 ν2 :
      cgraph_wf g → edge g ν1 ν2 → out_edges g ν1 ##ₘ out_edges g ν2.
    Proof.
      intros Hwf Hν12 v.
      destruct (out_edges g ν1 !! v) eqn:E;
      destruct (out_edges g ν2 !! v) eqn:F; simpl; eauto.
      eapply no_triangle; eauto.
      - left. eauto.
      - left. unfold edge. erewrite F. eauto.
      - right. unfold edge. rewrite E. eauto.
    Qed.
  End delete_edge.


  Section update_edge.
    Definition update_edge g ν1 ν2 l' :=
      insert_edge (delete_edge g ν1 ν2) ν1 ν2 l'.

    Lemma update_edge_out_edges g ν1 ν2 l' v :
      out_edges (update_edge g ν1 ν2 l') v =
        if decide (v = ν1) then <[ ν2 := l' ]> (out_edges g v)
        else out_edges g v.
    Proof.
      unfold update_edge.
      rewrite out_edges_insert_edge.
      rewrite out_edges_delete_edge.
      repeat case_decide; simplify_eq; eauto.
      apply map_eq. intros v.
      rewrite insert_delete_insert //.
    Qed.

    Lemma update_in_labels_neq g v ν1 ν2 l' :
      v ≠ ν2 →
      in_labels (update_edge g ν1 ν2 l') v ≡ in_labels g v.
    Proof.
      intros H1.
      rewrite /update_edge in_labels_insert_edge.
      - case_decide; simplify_eq. rewrite in_labels_delete_edge_neq; eauto.
      - unfold edge. rewrite out_edges_delete_edge.
        case_decide; simplify_eq. rewrite lookup_delete. done.
    Qed.

    Lemma update_edge_wf g ν1 ν2 l' :
      cgraph_wf g →
      edge g ν1 ν2 →
      cgraph_wf (update_edge g ν1 ν2 l').
    Proof.
      intros H1 H2.
      unfold update_edge.
      apply insert_edge_wf.
      - apply delete_edge_uconn; eauto.
      - eapply delete_edge_wf; eauto.
    Qed.
  End update_edge.

  Section move_edge.
    (* Move an edge ν1 --[l]--> v3 to be ν2 --[l]--> v *)
    (* This is only allowed if there is also an edge between ν1 and ν2. *)
    Definition move_edge g ν1 ν2 v3 :=
      match out_edges g ν1 !! v3 with
      | Some l => insert_edge (delete_edge g ν1 v3) ν2 v3 l
      | None => g
      end.

    Lemma move_edge_out_edges g ν1 ν2 v3 v l :
      out_edges g ν1 !! v3 = Some l →
      out_edges (move_edge g ν1 ν2 v3) v =
        if decide (v = ν2) then <[ v3 := l ]> $ out_edges g v
        else if decide (v = ν1) then delete v3 $ out_edges g v
        else out_edges g v.
    Proof.
      intros H1.
      unfold move_edge. rewrite H1.
      rewrite out_edges_insert_edge.
      rewrite out_edges_delete_edge.
      repeat case_decide; simplify_eq; eauto; apply map_eq; intro;
      rewrite ?lookup_union ?lookup_insert_spec ?lookup_delete_spec ?lookup_empty;
      repeat case_decide; simplify_eq; eauto.
    Qed.

    Lemma move_edge_in_labels g ν1 ν2 v3 v :
      cgraph_wf g →
      sc (edge g) ν1 ν2 →
      in_labels (move_edge g ν1 ν2 v3) v ≡ in_labels g v.
    Proof.
      intros Hwf Hν12.
      unfold move_edge.
      destruct (_!!_) eqn:E; eauto.
      rewrite in_labels_insert_edge.
      - case_decide; simplify_eq.
        + destruct (out_edges_in_labels_L _ _ _ _ E).
          rewrite in_labels_delete_edge_eq; eauto.
          by symmetry.
        + rewrite in_labels_delete_edge_neq; eauto.
      - unfold edge.
        assert (ν1 ≠ ν2); eauto using no_self_edge'.
        rewrite out_edges_delete_edge.
        case_decide; simplify_eq.
        intro HH.
        eapply no_triangle; eauto.
        + left; eauto.
        + right. unfold edge. erewrite E. eauto.
    Qed.

    Lemma move_edge_in_labels' g ν1 ν2 v3 v :
      cgraph_wf g →
      ¬ uconn g ν1 ν2 →
      in_labels (move_edge g ν1 ν2 v3) v ≡ in_labels g v.
    Proof.
      intros Hwf Hν12.
      unfold move_edge.
      destruct (_!!_) eqn:E; eauto.
      rewrite in_labels_insert_edge.
      - case_decide; simplify_eq.
        + destruct (out_edges_in_labels_L _ _ _ _ E).
          rewrite in_labels_delete_edge_eq; eauto.
          by symmetry.
        + rewrite in_labels_delete_edge_neq; eauto.
      - unfold edge.
        assert (ν1 ≠ ν2). { intros ->. apply Hν12. reflexivity. }
        rewrite out_edges_delete_edge.
        case_decide; simplify_eq.
        intros [].
        assert (edge g ν1 v3); eauto using some_edge_L.
        assert (edge g ν2 v3); eauto using some_edge_L.
        apply Hν12.
        eapply rtc_transitive; eapply rtc_once;[left|right]; eauto.
    Qed.

    Lemma move_edge_wf g ν1 ν2 v3 :
      ν2 ≠ v3 →
      cgraph_wf g →
      sc (edge g) ν1 ν2 →
      cgraph_wf (move_edge g ν1 ν2 v3).
    Proof.
      intros Hneq Hwf Hν12.
      unfold move_edge.
      destruct (_!!_) eqn:E; eauto.
      apply insert_edge_wf; eauto using delete_edge_wf.
      intro Hconn.
      eapply (delete_edge_uconn g ν1 v3); eauto.
      - unfold edge. rewrite E. eauto.
      - unfold uconn in *.
        assert (sc (edge (delete_edge g ν1 v3)) ν1 ν2). {
          destruct Hν12.
          - left. unfold edge. rewrite out_edges_delete_edge.
            case_decide; simplify_eq.
            rewrite lookup_delete_ne; eauto.
          - right. unfold edge. rewrite out_edges_delete_edge.
            case_decide; simplify_eq; eauto.
            exfalso. eapply no_self_edge; eauto.
        }
        eapply transitivity; last done.
        econstructor; first done.
        econstructor.
    Qed.

    Lemma edge_delete_edge''' g ν1 ν2 w1 w2 :
      edge (delete_edge g w1 w2) ν1 ν2 → edge g ν1 ν2.
    Proof.
      rewrite /delete_edge /edge /out_edges.
      destruct (g !! w1) eqn:F; simpl; rewrite lookup_insert_spec; repeat case_decide;
      rewrite ?lookup_delete_spec; repeat case_decide; simplify_eq;
      try destruct (g !! ν1) eqn:E; simpl; rewrite ?lookup_empty; eauto; try intros [];
      simplify_eq. rewrite H0. eauto.
    Qed.

    Lemma delete_edge_preserves_not_uconn g ν1 ν2 w1 w2 :
      uconn (delete_edge g w1 w2) ν1 ν2 → uconn g ν1 ν2.
    Proof.
      intros HH. induction HH; try reflexivity.
      eapply rtc_transitive; eauto. eapply rtc_once.
      destruct H0; [left|right]; eauto using edge_delete_edge'''.
    Qed.

    Lemma move_edge_wf' g ν1 ν2 v3 :
      ν2 ≠ v3 →
      cgraph_wf g →
      ¬ uconn g ν1 ν2 →
      cgraph_wf (move_edge g ν1 ν2 v3).
    Proof.
      intros Hneq Hwf Hν12.
      unfold move_edge.
      destruct (_!!_) eqn:E; eauto.
      apply insert_edge_wf; eauto using delete_edge_wf.
      assert (¬ uconn g v3 ν2).
      { intro. apply Hν12.
        eapply rtc_transitive; eauto.
        eapply rtc_once. left. eauto using some_edge_L. }
      intro. apply delete_edge_preserves_not_uconn in H1.
      apply H0. symmetry. done.
    Qed.

    Lemma move_edge_uconn g ν1 ν2 v3 :
      cgraph_wf g →
      ¬ uconn g ν1 ν2 →
      ¬ uconn (move_edge g ν1 ν2 v3) ν1 ν2.
    Proof.
      intros Hwf H1.
      destruct (out_edges g ν1 !! v3) eqn:E; last first.
      { unfold move_edge. rewrite E. done. }
      assert (¬ uconn (delete_edge (move_edge (insert_edge g ν1 ν2 o) ν1 ν2 v3) ν1 ν2) ν1 ν2).
      {
        eapply delete_edge_uconn.
        - eapply move_edge_wf.
          + intros ->. eapply H1. eapply rtc_once. left. eauto using some_edge_L.
          + eapply insert_edge_wf; eauto.
          + left. unfold edge.
            rewrite out_edges_insert_edge.
            case_decide; simplify_eq. rewrite lookup_insert. eauto.
        - unfold edge.
          erewrite move_edge_out_edges; last first.
          + rewrite out_edges_insert_edge.
            case_decide; simplify_eq.
            rewrite lookup_insert_spec.
            case_decide; simplify_eq; eauto.
          + rewrite !out_edges_insert_edge.
            repeat case_decide; simplify_eq.
            * rewrite !lookup_insert_spec.
              case_decide; simplify_eq. eauto.
            * rewrite lookup_delete_spec lookup_insert_spec.
              case_decide; simplify_eq.
              -- exfalso. apply H1.
                 eapply rtc_once. left. eauto using some_edge_L.
              -- case_decide; simplify_eq. eauto.
      }
      intro. apply H0.
      eapply uconn_equiv; eauto.
      intro.
      rewrite out_edges_delete_edge.
      erewrite move_edge_out_edges; last done.
      erewrite move_edge_out_edges; last first.
      { rewrite out_edges_insert_edge. case_decide; eauto.
        rewrite lookup_insert_spec. case_decide; simplify_eq; eauto. }
      rewrite !out_edges_insert_edge.
      repeat case_decide; simplify_eq; eauto.
      - assert (ν2 ≠ v3). { intros ->. eapply no_self_edge; eauto using some_edge_L. }
        rewrite delete_insert_ne; eauto.
        rewrite delete_insert; eauto.
        destruct (out_edges g ν2 !! ν2) eqn:F; eauto.
        exfalso. eapply no_self_edge; eauto using some_edge_L.
      - rewrite delete_commute.
        rewrite delete_insert; eauto.
        destruct (out_edges g v !! ν2) eqn:F; eauto.
        exfalso. apply H1. apply rtc_once.
        left. eapply some_edge_L; eauto.
    Qed.
  End move_edge.

  Section move_edges.
    Lemma move_edges g ν1 ν2 e1 e2 :
      cgraph_wf g →
      ¬ uconn g ν1 ν2 →
      e1 ##ₘ e2 →
      out_edges g ν1 = e1 ∪ e2 →
      ∃ g', cgraph_wf g' ∧
        ¬ uconn g' ν1 ν2 ∧
        (∀ v, out_edges g' v =
          if decide (v = ν1) then e1
          else if decide (v = ν2) then out_edges g v ∪ e2
          else out_edges g v) ∧
        (∀ v, in_labels g' v ≡ in_labels g v).
    Proof.
      revert g e1.
      induction e2 using map_ind; intros g e1;
      intros Hwf Hnuconn Hdisj Hout.
      - exists g. rewrite right_id_L in Hout.
        split_and!; eauto. intro.
        repeat case_decide; simplify_eq; eauto.
        rewrite right_id_L //.
      - specialize (IHe2 (move_edge g ν1 ν2 i) e1).
        destruct IHe2.
        + apply move_edge_wf'; eauto. intros ->. apply Hnuconn.
          apply rtc_once.
          left.
          unfold edge.
          rewrite Hout.
          rewrite lookup_union lookup_insert.
          destruct (e1 !! i); eauto.
        + apply move_edge_uconn; eauto.
        + solve_map_disjoint.
        + destruct (out_edges g ν1 !! i) eqn:E.
          2: { rewrite Hout in E. rewrite lookup_union lookup_insert in E.
            destruct (e1 !! i); simpl in *; simplify_eq.  }
          erewrite move_edge_out_edges; eauto.
          repeat case_decide; simplify_eq.
          -- exfalso. apply Hnuconn. reflexivity.
          -- rewrite Hout. rewrite delete_union.
             rewrite delete_insert; eauto.
             rewrite delete_notin; eauto.
             solve_map_disjoint.
        + destruct H1 as (H1 & H2 & H3 & H4).
          exists x0. split_and!; eauto.
          -- intros v. rewrite H3.
             assert (out_edges g ν1 !! i = Some x).
             { rewrite Hout. rewrite lookup_union lookup_insert.
                destruct (e1 !! i) eqn:E; simpl; eauto.
                specialize (Hdisj i). rewrite E in Hdisj. rewrite lookup_insert in Hdisj.
                simpl in *. done. }
             repeat case_decide; simplify_eq; eauto.
             ++ erewrite move_edge_out_edges; eauto.
                case_decide; simplify_eq.
                apply map_eq; intro.
                rewrite !lookup_union !lookup_insert_spec;
                repeat case_decide; simplify_eq; eauto.
                rewrite H0. simpl.
                destruct (out_edges g ν2 !! i0) eqn:E; eauto; simpl.
                exfalso.
                apply Hnuconn.
                eapply rtc_transitive; eapply rtc_once; [left|right];
                eauto using some_edge_L.
             ++ erewrite move_edge_out_edges; eauto.
                repeat case_decide; simplify_eq. done.
          -- intros v. rewrite H4. rewrite move_edge_in_labels'; eauto.
    Qed.

    Lemma move_edges' g ν1 ν2 e1 e2 :
      cgraph_wf g →
      ¬ uconn g ν1 ν2 →
      e1 ##ₘ e2 →
      out_edges g ν1 = e1 ∪ e2 →
      ∃ g', cgraph_wf g' ∧
        ¬ uconn g' ν1 ν2 ∧
        out_edges g' ν1 = e1 ∧
        out_edges g' ν2 = out_edges g ν2 ∪ e2 ∧
        (∀ v, v ≠ ν1 → v ≠ ν2 → out_edges g' v = out_edges g v) ∧
        (∀ v, in_labels g' v ≡ in_labels g v).
    Proof.
      intros.
      edestruct move_edges as (?&?&?&?&?); eauto.
      eexists. split_and!; eauto.
      - specialize (H6 ν1). case_decide; simplify_eq; done.
      - specialize (H6 ν2). repeat case_decide; simplify_eq; done.
      - intros. specialize (H6 v); repeat case_decide; simplify_eq; eauto.
    Qed.
  End move_edges.

  Section exchange.
    Lemma exchange g ν1 ν2 e1 e2 :
      cgraph_wf g →
      ¬ uconn g ν1 ν2 →
      e1 ##ₘ e2 →
      out_edges g ν1 ∪ out_edges g ν2 = e1 ∪ e2 →
      ∃ g', cgraph_wf g' ∧
        ¬ uconn g' ν1 ν2 ∧
        out_edges g' ν1 = e1 ∧
        out_edges g' ν2 = e2 ∧
        (∀ v, v ≠ ν1 → v ≠ ν2 → out_edges g' v = out_edges g v) ∧
        (∀ v, in_labels g' v ≡ in_labels g v).
    Proof.
      intros Hwf Hnuconn Hdisj Hsplit.
      assert (out_edges g ν1 ##ₘ out_edges g ν2) as Hdisj'.
      { apply not_uconn_out_disjoint. done. }
      destruct (map_cross_split (e1 ∪ e2) _ _ _ Hdisj' Hdisj)
        as (e11 & e12 & e21 & e22 & Hdisj1 & Hdisj2 & Hdisj3 & Hdisj4 &
            ? & ? & HH1 & HH2); eauto; subst.

      destruct (move_edges' g ν1 ν2 e11 e12)
        as (g' & Hwf' & Hnuconn' & Hν1 & Hν2 & Hv & Hin); eauto.
      rewrite <-H1 in Hν2.
      rewrite <-assoc_L in Hν2; last apply _.
      rewrite map_union_comm in Hν2; last solve_map_disjoint.

      destruct (move_edges' g' ν2 ν1 (e22 ∪ e12) e21)
        as (g'' & Hwf'' & Hnuconn'' & Hν1' & Hν2' & Hv' & Hin'); eauto.
      { intro. apply Hnuconn'. symmetry. done. }
      { solve_map_disjoint. }

      eexists. split_and!; eauto.
      - intro. symmetry in H2. eauto.
      - rewrite Hν2' Hν1 //.
      - rewrite Hν1'. rewrite map_union_comm; eauto.
      - intros. rewrite Hv'; eauto.
      - intros. rewrite Hin'. eauto.
    Qed.
  End exchange.

  Lemma cgraph_ind (R : relation V) (g : cgraph V L) (P : V → Prop) :
    cgraph_wf g →
    asym R →
    (∀ x, (∀ y, R x y → sc (edge g) x y → P y) → P x) → (∀ x, P x).
  Proof.
    intros [] Hasy Hind.
    eapply uforest_ind; eauto.
    intros. eapply Hind.
    intros. eapply H2; eauto.
    eapply elem_of_to_uforest.
    done.
  Qed.

  (*
     The relation R x y l tells us for each pair of objects (x,y), what
     the waiting direction is for an edge x--[l]-->y labeled with l.
     If R x y l, then the waiting direction is in the same direction as the edge.
     If ¬R x y l, then waiting direction is in the opposite direction as the edge.
     So R tells us the waiting direction *relative to* the edge direction.
  *)
  Lemma cgraph_ind' (R : V → V → L → Prop)
      {Hproper : ∀ x y, Proper ((≡) ==> iff) (R x y)}
      (g : cgraph V L)
      (Hwf : cgraph_wf g)
      (P : V → Prop) :
    (∀ x,
      (∀ y l, out_edges g x !! y ≡ Some l → R x y l → P y) →
      (∀ y l, out_edges g y !! x ≡ Some l → ¬ R y x l → P y) →
      P x) →
    (∀ x, P x).
  Proof.
    intros Hind.
    eapply (cgraph_ind (λ x y,
      ∃ l, (out_edges g x !! y ≡ Some l ∧ R x y l) ∨
           (out_edges g y !! x ≡ Some l ∧ ¬ R y x l))); eauto.
    - destruct Hwf.
      intros ?? (l1 & [[]|[]]) (l2 & [[]|[]]).
      + exfalso. eapply H0; eauto using some_edge.
      + exfalso. rewrite ->H2 in H4. inversion H4. subst.
        eapply H5. rewrite <-H8. done.
      + exfalso. rewrite ->H2 in H4. inversion H4. subst.
        eapply H3. rewrite H8. done.
      + exfalso. eapply H0; eauto using some_edge.
    - intros. eapply Hind; intros.
      + eapply H0; eauto.
        left. eauto using some_edge.
      + eapply H0; eauto.
        right. eauto using some_edge.
  Qed.
End cgraph.

Section cgraph_si.
  Context `{!Sbi PROP, Countable V} {L : ofe}.
  Implicit Types g : cgraph V L.

  Lemma in_labels_out_edges g ν2 l X :
    in_labels g ν2 ≡ {[+ l +]} ⊎ X ⊢@{PROP} ∃ ν1, out_edges g ν1 !! ν2 ≡ Some l.
  Proof.
    iIntros "H".
    iInduction g as [|v l1 g] "IH" using map_ind forall (X).
    - rewrite in_labels_empty.
      by iDestruct "H" as %?%symmetry%multiset_empty_equiv_eq.
    - rewrite in_labels_insert //.
      destruct (l1 !! ν2) as [l2|] eqn:E; simpl.
      + iDestruct (multiset_singleton_disj_unionI with "H") as "[[H1 H2]|H]".
        * iExists v. rewrite out_edges_insert decide_True // E.
          iRewrite "H1". done.
        * iDestruct "H" as (Z) "[H1 H2]".
          setoid_rewrite out_edges_insert.
          iDestruct ("IH" with "H1") as (v3) "H3".
          iExists v3. unfold out_edges.
          destruct (g !! v3) eqn:E2; last first.
          { rewrite lookup_empty. iDestruct "H3" as %H3. inversion H3. }
          rewrite decide_False //. intros ->. simplify_eq.
      + rewrite left_id.
        iDestruct ("IH" with "H") as (ν1) "H".
        setoid_rewrite out_edges_insert.
        iExists ν1. case_decide; eauto. subst.
        by rewrite /out_edges H0 lookup_empty option_equivI.
  Qed.

  Lemma in_labels_out_edges1 g ν2 l :
    in_labels g ν2 ≡ {[+ l +]} ⊢@{PROP}
    ∃ ν1, out_edges g ν1 !! ν2 ≡ Some l.
  Proof.
    iIntros "H". iApply (in_labels_out_edges _ _ _ ∅).
    rewrite right_id //.
  Qed.

  Lemma in_labels_out_edges2 g v l1 l2 :
    in_labels g v ≡ {[+ l1; l2 +]} ⊢@{PROP}
    ∃ ν1 ν2, ⌜ ν1 ≠ ν2 ⌝ ∧
      out_edges g ν1 !! v ≡ Some l1 ∧
      out_edges g ν2 !! v ≡ Some l2.
  Proof.
    iIntros "H".
    iInduction g as [|v3 l3 g] "IH" using map_ind.
    { rewrite in_labels_empty.
      by iDestruct "H" as %?%symmetry%multiset_empty_equiv_eq. }
    rewrite in_labels_insert //.
    destruct (l3 !! v) as [l4|] eqn:E; simpl.
    - iDestruct (multiset_singleton_disj_union_singletonsI with "H") as "[[H1 H2]|[H1 H2]]".
      + iDestruct (in_labels_out_edges1 with "H2") as (ν1) "H2".
        iExists v3,ν1.
        rewrite !out_edges_insert.
        repeat case_decide; simplify_eq; eauto.
        { rewrite /out_edges H0 lookup_empty.
          iDestruct "H2" as %H2. inversion H2. }
        iSplit; first done.
        iSplit; eauto.
        rewrite E. iRewrite "H1". done.
      + iDestruct (in_labels_out_edges1 with "H2") as (ν1) "H2".
        iExists ν1,v3.
        rewrite !out_edges_insert.
        repeat case_decide; simplify_eq; eauto.
        { rewrite /out_edges H0 lookup_empty.
          iDestruct "H2" as %H2. inversion H2. }
        iSplit; first done.
        iSplit; eauto.
        rewrite E. iRewrite "H1". done.
    - rewrite left_id.
      iDestruct ("IH" with "H") as (ν1 ν2) "(% & H1 & H2)".
      iExists ν1,ν2. iSplit; first done.
      rewrite !out_edges_insert.
      case_decide; case_decide; simplify_eq; eauto.
      + rewrite /out_edges H0 lookup_empty.
        iDestruct "H1" as %Q. inversion Q.
      + rewrite /out_edges H0 lookup_empty.
        iDestruct "H2" as %Q. inversion Q.
  Qed.

  Lemma in_labels_delete_edge_eqI g ν1 ν2 l X :
    out_edges g ν1 !! ν2 = Some l →
    in_labels g ν2 ≡ {[+ l +]} ⊎ X ⊢@{PROP} in_labels (delete_edge g ν1 ν2) ν2 ≡ X.
  Proof.
    iIntros (Hout) "Hin". rewrite /delete_edge. unfold out_edges in Hout.
    destruct (g !! ν1) as [Σ|] eqn:Hgν1; last done.
    pose proof (in_labels_update g ν1 (delete ν2 (out_edges g ν1)) Σ ν2 Hgν1) as HΣ.
    destruct (Σ !! ν2) eqn:F; simplify_eq/=.
    rewrite lookup_delete /= left_id in HΣ. by rewrite -HΣ multiset_disj_union_injI.
  Qed.

  Lemma exchange_alloc g ν1 ν2 Σ1 Σ2 l :
    cgraph_wf g →
    ¬uconn g ν1 ν2 →
    Σ1 ##ₘ Σ2 →
    out_edges g ν1 ∪ out_edges g ν2 ≡ Σ1 ∪ Σ2 ⊢@{PROP}
    ∃ g',
      ⌜ cgraph_wf g' ⌝ ∧
      out_edges g' ν1 ≡ {[ ν2 := l ]} ∪ Σ1 ∧
      out_edges g' ν2 ≡ Σ2 ∧
      (∀ ν, ⌜ ν ≠ ν1 ∧ ν ≠ ν2 ⌝ → out_edges g' ν ≡ out_edges g ν) ∧
      in_labels g' ν2 ≡ {[+ l +]} ⊎ in_labels g ν2 ∧
      (∀ ν, ⌜ ν ≠ ν2 ⌝ → in_labels g' ν ≡ in_labels g ν).
  Proof.
    iIntros (Hwf Hnuconn Hdisj) "Hsplit".
    iDestruct (gmap_union_equiv_eqI with "Hsplit") as (Σ1' Σ2' ?) "#[HΣ1 HΣ2]".
    iAssert ⌜ Σ1' ##ₘ Σ2' ⌝%I as %?.
    { iRewrite "HΣ1". by iRewrite "HΣ2". }
    destruct (exchange g ν1 ν2 Σ1' Σ2')
      as (g' & Hwf' & Hnuconn' & Hout1 & Hout2 & Hrest & Hin); [by eauto..|].
    assert (¬edge g' ν1 ν2).
    { intros ?. apply Hnuconn', rtc_once. by left. }
    iExists (insert_edge g' ν1 ν2 l).
    iSplit; [by eauto using insert_edge_wf|]. repeat iSplit.
    - rewrite out_edges_insert_edge decide_True // Hout1.
      rewrite insert_union_singleton_l. by iRewrite "HΣ1".
    - assert (ν1 ≠ ν2).
      { intros ->. by apply Hnuconn'. }
      by rewrite out_edges_insert_edge decide_False // Hout2.
    - iIntros (ν [??]). rewrite out_edges_insert_edge decide_False // Hrest //.
    - by rewrite in_labels_insert_edge // decide_True // Hin.
    - iIntros (ν ?). rewrite in_labels_insert_edge // decide_False //.
  Qed.

  Lemma exchange_dealloc g ν1 ν2 Σ1 Σ2 l :
    cgraph_wf g →
    Σ1 ##ₘ Σ2 →
    out_edges g ν1 !! ν2 ≡ Some l ∧
    delete ν2 (out_edges g ν1) ∪ out_edges g ν2 ≡ Σ1 ∪ Σ2 ⊢@{PROP}
    ∃ g',
      ⌜ cgraph_wf g' ⌝ ∧
      ⌜ ¬ uconn g' ν1 ν2 ⌝ ∧
      out_edges g' ν1 ≡ Σ1 ∧
      out_edges g' ν2 ≡ Σ2 ∧
      (∀ ν, ⌜ ν ≠ ν1 ∧ ν ≠ ν2 ⌝ → out_edges g' ν ≡ out_edges g ν) ∧
      (∀ X, in_labels g ν2 ≡ {[+ l +]} ⊎ X → in_labels g' ν2 ≡ X) ∧
      (∀ v, ⌜ v ≠ ν2 ⌝ → in_labels g' v ≡ in_labels g v).
  Proof.
    iIntros (Hg Hdisj) "#[Hout Hsplit]". rewrite option_equivI.
    destruct (out_edges g ν1 !! ν2) as [l'|] eqn:Hl; [|done].
    iDestruct (gmap_union_equiv_eqI with "Hsplit") as (Σ1' Σ2' ?) "[HΣ1 HΣ2]".
    iAssert ⌜ Σ1' ##ₘ Σ2' ⌝%I as %?.
    { iRewrite "HΣ1". by iRewrite "HΣ2". }
    destruct (exchange (delete_edge g ν1 ν2) ν1 ν2 Σ1' Σ2')
      as (g' & Hwf' & Hnuconn' & Hout1 & Hout2 & Hrest & Hin).
    - eapply delete_edge_wf; eauto.
    - eapply delete_edge_uconn; eauto using some_edge_L.
    - done.
    - rewrite !out_edges_delete_edge. sdec; eauto.
      exfalso. eapply no_self_edge; eauto using some_edge_L.
    - iExists g'. iSplit; [done|]. repeat iSplit; auto.
      + by rewrite Hout1.
      + by rewrite Hout2.
      + iIntros (ν [??]). rewrite Hrest // out_edges_delete_edge. by case_decide.
      + iIntros (X) "H". rewrite Hin.
        iApply in_labels_delete_edge_eqI; first done. by iRewrite "Hout".
      + iIntros (ν ?). rewrite Hin. by rewrite in_labels_delete_edge_neq.
  Qed.

  Lemma out_edges_in_labels g ν1 ν2 l :
    out_edges g ν1 !! ν2 ≡ Some l ⊢@{PROP} ∃ X, in_labels g ν2 ≡ {[+ l +]} ⊎ X.
  Proof.
    iIntros "Hl". rewrite option_equivI.
    destruct (out_edges g ν1 !! ν2) as [l'|] eqn:Hl; [|done].
    destruct (out_edges_in_labels_L g ν1 ν2 l') as [X ?]; first by rewrite Hl.
    iExists X. by iRewrite -"Hl".
  Qed.

  Lemma move_fork g ν1 ν2 ν3 Σ1 Σ2 l1 l2 :
    cgraph_wf g →
    ν1 ≠ ν2 ∧ ν1 ≠ ν3 ∧ ν2 ≠ ν3 →
    out_edges g ν2 = ∅ → out_edges g ν3 = ∅ →
    in_labels g ν2 = ∅ → in_labels g ν3 = ∅ →
    Σ1 ##ₘ Σ2 →
    out_edges g ν1 ≡ Σ1 ∪ Σ2 ⊢@{PROP}
    ∃ g',
      ⌜ cgraph_wf g' ⌝ ∧
      out_edges g' ν1 ≡ {[ ν2 := l1 ]} ∪ Σ2 ∧
      out_edges g' ν2 ≡ ∅ ∧
      out_edges g' ν3 ≡ {[ ν2 := l2 ]} ∪ Σ1 ∧
      in_labels g' ν2 ≡ {[+ l1; l2 +]} ∧
      (∀ v, ⌜ v ≠ ν1 ∧ v ≠ ν2 ∧ v ≠ ν3⌝ → out_edges g' v ≡ out_edges g v) ∧
      (∀ v, ⌜ v ≠ ν2 ⌝ → in_labels g' v ≡ in_labels g v).
  Proof.
    iIntros (Hwf (Hneq12 & Hneq13 & Hneq23) Hout2 Hout3 Hin2 Hin3 Hdisj) "#Hout".
    iDestruct (exchange_alloc g ν1 ν2 Σ2 Σ1 l1 with "[]")
      as (g' Hwf') "(Hout1' & Hout2' & Hout' & Hin2' & Hin')".
    { done. }
    { intros Hu. apply Hneq12, symmetry.
      eapply no_edges_no_uconn; [done| |done]. rewrite Hin2 //. }
    { done. }
    { rewrite Hout2 right_id_L map_union_comm //. }
    iAssert (out_edges g' ν3 ≡ ∅)%I as %Hout3'.
    { iRewrite ("Hout'" $! ν3 with "[//]"). by rewrite Hout3. }
    rewrite map_empty_equiv_eq in Hout3'.
    iAssert (in_labels g' ν3 ≡ ∅)%I as %?%multiset_empty_equiv_eq.
    { iRewrite ("Hin'" $! ν3 with "[//]"). by rewrite Hin3. }
    iDestruct (exchange_alloc g' ν3 ν2 Σ1 ∅ l2 with "[]")
      as (g'' Hwf'') "(Hout3'' & Hout2'' & Hout'' & Hin2'' & Hin'')".
    { done. }
    { intros ?. by apply Hneq23, symmetry, (no_edges_no_uconn g'). }
    { solve_map_disjoint. }
    { by rewrite Hout3' left_id right_id. }
    iExists g''. iSplit; first done. repeat iSplit.
    - by iRewrite ("Hout''" $! ν1 with "[//]").
    - done.
    - done.
    - iRewrite "Hin2''". iRewrite "Hin2'". rewrite Hin2 right_id.
      by rewrite -(comm _ {[+ l2 +]}).
    - iIntros (ν (?&?&?)). iRewrite ("Hout''" $! ν with "[//]").
      by iRewrite ("Hout'" $! ν with "[//]").
    - iIntros (ν ?). iRewrite ("Hin''" $! ν with "[//]").
      by iRewrite ("Hin'" $! ν with "[//]").
  Qed.

  Lemma exchange_relabel g ν1 ν2 Σ1 Σ2 l l' :
    cgraph_wf g →
    Σ1 ##ₘ Σ2 →
    out_edges g ν1 !! ν2 ≡ Some l ∧
    delete ν2 (out_edges g ν1) ∪ out_edges g ν2 ≡ Σ1 ∪ Σ2 ⊢@{PROP}
    ∃ g',
      ⌜ cgraph_wf g' ⌝ ∧
      out_edges g' ν1 ≡ {[ ν2 := l' ]} ∪ Σ1 ∧
      out_edges g' ν2 ≡ Σ2 ∧
      (∀ ν, ⌜ ν ≠ ν1 ∧ ν ≠ ν2 ⌝ → out_edges g' ν ≡ out_edges g ν) ∧
      (∀ X, in_labels g ν2 ≡ {[+ l +]} ⊎ X → in_labels g' ν2 ≡ {[+ l' +]} ⊎ X) ∧
      (∀ ν, ⌜ ν ≠ ν2 ⌝ → in_labels g' ν ≡ in_labels g ν).
  Proof.
    iIntros (Hwf Hdisj) "#[Hout Hsplit]".
    iDestruct (exchange_dealloc g ν1 ν2 Σ1 Σ2 l with "[]")
      as (g' Hwf' Hnuconn') "(Hout1 & Hout2 & Hrest & Hin2 & Hin)"; [by auto..|].
    assert (¬edge g' ν1 ν2).
    { intros ?. apply Hnuconn', rtc_once. by left. }
    iExists (insert_edge g' ν1 ν2 l').
    iSplit; first by eauto using insert_edge_wf.
    repeat iSplit.
    - rewrite out_edges_insert_edge decide_True //.
      rewrite insert_union_singleton_l. by iRewrite "Hout1".
    - assert (ν1 ≠ ν2) by (intros ->; by apply Hnuconn').
      by rewrite out_edges_insert_edge decide_False.
    - iIntros (ν [??]). rewrite out_edges_insert_edge decide_False //.
      by iApply "Hrest".
    - iIntros (X) "#HX".
      rewrite in_labels_insert_edge // decide_True //.
      by iRewrite ("Hin2" $! X with "[//]").
    - iIntros (ν ?). rewrite in_labels_insert_edge // decide_False //.
      by iApply "Hin".
  Qed.

  Lemma ref_alloc g ν1 ν2 l :
    cgraph_wf g →
    ν1 ≠ ν2 →
    out_edges g ν2 = ∅ →
    in_labels g ν2 = ∅ →
    ⊢@{PROP}
    ∃ g',
      ⌜ cgraph_wf g' ⌝ ∧
      out_edges g' ν1 ≡ {[ ν2:=l ]} ∪ out_edges g ν1 ∧
      (∀ v, ⌜ v ≠ ν1 ⌝ → out_edges g' v ≡ out_edges g v) ∧
      in_labels g' ν2 ≡ {[+ l +]} ∧
      (∀ v, ⌜ v ≠ ν2 ⌝ → in_labels g' v ≡ in_labels g v).
  Proof.
    iIntros (Hwf Hneq12 Hout Hin). assert (¬ uconn g ν1 ν2).
    { intros ?. by eapply Hneq12, symmetry, no_edges_no_uconn. }
    iDestruct (exchange_alloc g ν1 ν2 (out_edges g ν1) (out_edges g ν2) l with "[]")
      as (g' Hwf') "(Hout1 & Hout2 & Hout & Hin1 & Hin2)";
      [by eauto using not_uconn_out_disjoint..|].
    iExists g'. iSplit; first done. repeat iSplit.
    - done.
    - iIntros (ν ?). destruct (decide (ν = ν2)) as [->|]; [done|].
      iApply "Hout". auto.
    - iRewrite "Hin1". by rewrite Hin !right_id.
    - done.
  Qed.

  Lemma ref_free g ν1 ν2 l :
    cgraph_wf g →
    out_edges g ν1 !! ν2 ≡ Some l ∧ in_labels g ν2 ≡ {[+ l +]} ⊢@{PROP}
    ∃ g',
      ⌜ cgraph_wf g' ⌝ ∧
      out_edges g' ν1 ≡ delete ν2 (out_edges g ν1) ∧
      in_labels g' ν2 ≡ ∅ ∧
      (∀ ν, ⌜ ν ≠ ν1 ⌝ → out_edges g' ν ≡ out_edges g ν) ∧
      (∀ v, ⌜ v ≠ ν2 ⌝ → in_labels g' v ≡ in_labels g v).
  Proof.
    iIntros (Hwf) "#[Hout Hin]".
    iAssert ⌜ delete ν2 (out_edges g ν1) ##ₘ out_edges g ν2 ⌝%I as %Hdisj.
    { rewrite option_equivI. destruct (_ !! _) as [l'|] eqn:Hν1; last done.
      iPureIntro.
      by eapply map_disjoint_delete_l, edge_out_disjoint, some_edge_L. }
    iDestruct (exchange_dealloc g ν1 ν2
                 (delete ν2 (out_edges g ν1)) (out_edges g ν2) l with "[]")
      as (g' Hwf' Huconn) "(Hout1 & Hout2 & Hout' & Hin1 & Hin2)"; eauto.
    iExists g'. iSplit; first done. repeat iSplit.
    - done.
    - iApply "Hin1". by rewrite right_id.
    - iIntros (ν ?). destruct (decide (ν = ν2)) as [->|]; [done|].
      iApply "Hout'". auto.
    - done.
  Qed.
End cgraph_si.
