/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import CliqueMinorsLib.Minors

/-!
# Graphs with at least `3n - 5` edges have a `K₅` minor

**Mader (1968).** A graph on `n ≥ 3` vertices with at least `3n - 5` edges has a `K₅` minor;
equivalently a graph on `n ≥ 3` vertices without a `K₅` minor has at most `3n - 6` edges.

The proof is a minimal-counterexample argument in the style of `mader_aux`. In a graph with at
least `3n - 5` edges supported on `n` vertices that is minimal under deleting vertices of degree at
most three, deleting edges and contracting edges, every vertex has degree at least `4`, the number
of edges is exactly `3n - 5`, and every edge lies in at least three triangles. Some vertex `x` has
degree `4` or `5`; its neighbourhood then has at least `3 · deg x / 2 > 2 · deg x - 3` edges, so
by Dirac's bound (`edges_aux`) it has a `K₄` minor, and `x` completes it to a `K₅` minor.
-/

@[expose] public section

open SimpleGraph

namespace CliqueMinors

variable {V : Type*}

section MaderFive

open scoped Classical

variable [Fintype V]

theorem degree_eq_zero_of_not_mem_support {G : SimpleGraph V} {S : Finset V}
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) {v : V} (hv : v ∉ S) : G.degree v = 0 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw
  exact hv (hsupp _ _ ((mem_neighborFinset _ _ _).1 hw))

theorem sum_degree_support {G : SimpleGraph V} {S : Finset V}
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) :
    ∑ v ∈ S, G.degree v = 2 * G.edgeFinset.card := by
  rw [← sum_degrees_eq_twice_card_edges]
  refine Finset.sum_subset (Finset.subset_univ _) fun v _ hv => ?_
  exact degree_eq_zero_of_not_mem_support hsupp hv

/-- At most `n (n - 1) / 2` edges on a support of `n` vertices. -/
theorem two_mul_card_edgeFinset_le {G : SimpleGraph V} {S : Finset V}
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) :
    2 * G.edgeFinset.card ≤ S.card * (S.card - 1) := by
  rw [← sum_degree_support hsupp]
  calc ∑ v ∈ S, G.degree v ≤ ∑ v ∈ S, (S.card - 1) := by
        refine Finset.sum_le_sum fun v hv => ?_
        rw [← card_neighborFinset_eq_degree, ← Finset.card_erase_of_mem hv]
        refine Finset.card_le_card fun w hw => ?_
        rw [mem_neighborFinset] at hw
        exact Finset.mem_erase.2 ⟨hw.ne.symm, hsupp _ _ hw.symm⟩
    _ = S.card * (S.card - 1) := by rw [Finset.sum_const, smul_eq_mul]

theorem card_edgeFinset_deleteEdge {G : SimpleGraph V} {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    (G.deleteEdges {e}).edgeFinset.card + 1 = G.edgeFinset.card := by
  have h : (G.deleteEdges {e}).edgeFinset = G.edgeFinset.erase e := by
    ext f
    simp only [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff,
      Finset.mem_erase]
    tauto
  rw [h, Finset.card_erase_of_mem he]
  have := Finset.card_pos.2 ⟨e, he⟩
  omega

theorem mader_five_aux : ∀ (n : ℕ) (G : SimpleGraph V) (S : Finset V), S.card = n →
    (∀ a b, G.Adj a b → a ∈ S) → 3 ≤ n → 3 * n ≤ G.edgeFinset.card + 5 →
    IsMinor (⊤ : SimpleGraph (Fin 5)) G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  suffices ∀ m (G : SimpleGraph V) (S : Finset V), G.edgeFinset.card = m → S.card = n →
      (∀ a b, G.Adj a b → a ∈ S) → 3 ≤ n → 3 * n ≤ G.edgeFinset.card + 5 →
      IsMinor (⊤ : SimpleGraph (Fin 5)) G from fun G S => this _ G S rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro G S hm hn hsupp h3 hE
  -- At least five vertices: on three or four vertices there are too few edges.
  have hmax := two_mul_card_edgeFinset_le hsupp
  rw [hn] at hmax
  have h5 : 5 ≤ n := by
    by_contra hlt
    interval_cases n <;> omega
  -- A vertex of degree at most three is deleted.
  by_cases hlow : ∃ x ∈ S, G.degree x ≤ 3
  · obtain ⟨x, hxS, hx⟩ := hlow
    obtain ⟨G', hG'⟩ : ∃ G', G' = G.deleteIncidenceSet x := ⟨_, rfl⟩
    have hE' := card_edges_deleteIncidenceSet G G' x hG'
    have hsupp' : ∀ a b, G'.Adj a b → a ∈ S.erase x := by
      subst hG'; exact deleteIncidenceSet_supp hsupp
    refine isMinor_mono (G' := G') (hG' ▸ deleteIncidenceSet_le' G x) ?_
    refine ihn (n - 1) (by omega) G' (S.erase x) (by rw [Finset.card_erase_of_mem hxS, hn])
      hsupp' (by omega) (by omega)
  push_neg at hlow
  -- An edge whose contraction keeps the density is contracted.
  by_cases hc : ∃ x y, G.Adj x y ∧ 3 * (n - 1) ≤ (contractG G x y).edgeFinset.card + 5
  · obtain ⟨x, y, hxy, hc⟩ := hc
    refine isMinor_lift_contract (G' := contractG G x y) hxy
      (fun u v h => (contractG_adj.1 h).2) (by norm_num) ?_
    have hyS : y ∈ S := hsupp _ _ hxy.symm
    exact ihn (n - 1) (by omega) (contractG G x y) (S.erase y)
      (by rw [Finset.card_erase_of_mem hyS, hn]) (contract_support hxy hsupp) (by omega) hc
  simp only [not_exists, not_and, not_le] at hc
  -- A surplus edge is deleted.
  by_cases hsur : 3 * n < G.edgeFinset.card + 5
  · have hE0 : 0 < G.edgeFinset.card := by omega
    obtain ⟨e, he⟩ := Finset.card_pos.1 hE0
    have hdel := card_edgeFinset_deleteEdge he
    have key : ∀ H : SimpleGraph V, H = G.deleteEdges {e} →
        H.edgeFinset.card + 1 = G.edgeFinset.card := by
      rintro H rfl; convert hdel
    have h' := key _ rfl
    refine isMinor_mono (G' := G.deleteEdges {e}) (deleteEdges_le _) ?_
    refine ihm _ ?_ (G.deleteEdges {e}) S rfl hn
      (fun a b h => hsupp a b (deleteEdges_le _ h)) h3 ?_
    all_goals omega
  -- Now `|E| = 3n - 5`, every vertex has degree at least `4` and every edge lies in at least
  -- three triangles; a vertex of degree at most `5` finishes.
  have hsum := sum_degree_support hsupp
  obtain ⟨x, hxS, hx⟩ : ∃ x ∈ S, G.degree x ≤ 5 := by
    by_contra hno
    push_neg at hno
    have : ∑ v ∈ S, 6 ≤ ∑ v ∈ S, G.degree v := Finset.sum_le_sum fun v hv => hno v hv
    rw [Finset.sum_const, smul_eq_mul, hn] at this
    omega
  have hx4 := hlow x hxS
  have hcom : ∀ v, G.Adj x v → 3 ≤ (G.neighborFinset x ∩ G.neighborFinset v).card := by
    intro v hv
    have h1 := card_edge_contract hv
    have h2 := hc x v hv
    omega
  have hcone := cone_edges hcom
  rw [card_neighborFinset_eq_degree] at hcone
  refine isMinor_lift_cone (G' := coneG G x) (fun u v h => h) (r := 4) (by norm_num) ?_
  by_contra hK4
  have := edges_aux (G.degree x) (coneG G x) (G.neighborFinset x) (card_neighborFinset_eq_degree _ _)
    (by omega) (fun a b h => by simpa using h.2.1) hK4
  omega

/-- **Mader (1968).** A finite graph on `n ≥ 3` vertices with at least `3n - 5` edges has a `K₅`
minor. -/
theorem isMinor_K5_of_card_edgeFinset (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V)
    (h : 3 * Fintype.card V ≤ G.edgeFinset.card + 5) : IsMinor (⊤ : SimpleGraph (Fin 5)) G :=
  mader_five_aux _ G Finset.univ rfl (fun _ _ _ => Finset.mem_univ _)
    (by rwa [Finset.card_univ]) (by rwa [Finset.card_univ])

end MaderFive

end CliqueMinors
