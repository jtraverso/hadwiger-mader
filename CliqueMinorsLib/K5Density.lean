/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CliqueMinorsLib.Minors

/-!
# The 3n − 5 edge threshold for a K₅ minor

Contract an edge with at most two common neighbors, losing at most three edges.
If every edge incident to a chosen vertex has at least three common neighbors,
its neighborhood has minimum degree at least three. Dirac's K₄-minor lemma in
that neighborhood, followed by adding the central vertex, gives a K₅ minor.
The n = 3 base case is excluded by the elementary three-edge upper bound.
-/

@[expose] public section

namespace CliqueMinors

open SimpleGraph Finset

variable {V W : Type*}

open Classical in
/-- Disjoint nonempty branch sets give an injection into the original vertex set. -/
theorem card_le_of_isMinor [Fintype V] [Fintype W]
    (H : SimpleGraph W) (G : SimpleGraph V) (h : IsMinor H G) :
    Fintype.card W ≤ Fintype.card V := by
  classical
  obtain ⟨M⟩ := h
  let f : W → V := fun w => (M.branch_nonempty w).choose
  have hf (w : W) : f w ∈ M.branch w := (M.branch_nonempty w).choose_spec
  apply Fintype.card_le_of_injective f
  intro w w' heq
  by_contra hne
  have hboth : f w ∈ M.branch w' := by simpa only [heq] using hf w'
  exact Finset.disjoint_left.mp (M.branch_disjoint w w' hne) (hf w) hboth

section Counting

variable [Fintype V]

open Classical in
theorem card_edges_le_three_of_support_three (G : SimpleGraph V) (S : Finset V)
    (hS : S.card = 3) (hsupp : ∀ u v, G.Adj u v → u ∈ S) : G.edgeFinset.card ≤ 3 := by
  obtain ⟨a, b, c, _hab, _hac, _hbc, rfl⟩ := Finset.card_eq_three.mp hS
  have hsub : G.edgeFinset ⊆ {s(a, b), s(a, c), s(b, c)} := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := by simpa using he
      have hu : u = a ∨ u = b ∨ u = c := by simpa using hsupp u v huv
      have hv : v = a ∨ v = b ∨ v = c := by simpa using hsupp v u huv.symm
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        simp_all
  have h1 := Finset.card_insert_le s(a, b) {s(a, c), s(b, c)}
  have h2 := Finset.card_insert_le s(a, c) {s(b, c)}
  have h3 : ({s(b, c)} : Finset (Sym2 V)).card = 1 := Finset.card_singleton _
  have h4 := Finset.card_le_card hsub
  omega

open Classical in
theorem mader_K5_aux : ∀ (n : ℕ) (G : SimpleGraph V) (S : Finset V), S.card = n →
    3 ≤ n → (∀ u v, G.Adj u v → u ∈ S) → 3 * n ≤ G.edgeFinset.card + 5 →
    IsMinor (⊤ : SimpleGraph (Fin 5)) G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G S hS hn hsupp hE
    by_cases hn3 : n = 3
    · have hsmall := card_edges_le_three_of_support_three G S (hS.trans hn3) hsupp
      omega
    have hn4 : 4 ≤ n := by omega
    obtain ⟨x, y, hxy⟩ := exists_adj_of_card_pos (G := G) (by omega)
    by_cases hc : ∃ v, G.Adj x v ∧ (G.neighborFinset x ∩ G.neighborFinset v).card ≤ 2
    · obtain ⟨v, hxv, hcommon⟩ := hc
      have hvS : v ∈ S := hsupp _ _ hxv.symm
      have hcontract := card_edge_contract hxv
      apply isMinor_lift_contract (G' := contractG G x v) hxv
        (fun _ _ h => (contractG_adj.mp h).2) (by decide)
      apply ih (n - 1) (by omega) (contractG G x v) (S.erase v)
        (by rw [Finset.card_erase_of_mem hvS, hS]) (by omega)
        (contract_support hxv hsupp)
      omega
    · have hcommon (v : V) (hv : G.Adj x v) :
          3 ≤ (G.neighborFinset x ∩ G.neighborFinset v).card := by
        have hnot : ¬ (G.neighborFinset x ∩ G.neighborFinset v).card ≤ 2 :=
          fun h => hc ⟨v, hv, h⟩
        omega
      have hdegree (v : V) (hv : v ∈ G.neighborFinset x) :
          3 ≤ (coneG G x).degree v := by
        apply (hcommon v ((mem_neighborFinset _ _ _).mp hv)).trans
        rw [← card_neighborFinset_eq_degree]
        apply Finset.card_le_card
        intro t ht
        simp only [Finset.mem_inter, mem_neighborFinset] at ht
        exact (mem_neighborFinset _ _ _).mpr ⟨ht.2, (mem_neighborFinset _ _ _).mp hv, ht.1⟩
      have hK4 : IsMinor (⊤ : SimpleGraph (Fin 4)) (coneG G x) :=
        dirac_aux _ (coneG G x) (G.neighborFinset x) rfl
          ⟨y, (mem_neighborFinset _ _ _).mpr hxy⟩
          (fun _ _ h => (mem_neighborFinset _ _ _).mpr h.2.1) hdegree
      exact isMinor_lift_cone (G' := coneG G x) (fun _ _ h => h) (by decide) hK4

open Classical in
/-- Mader's K₅ density bound. The integer inequality expresses e(G) ≥ 3n − 5. -/
theorem mader_K5 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V) (h : 3 * Fintype.card V ≤ G.edgeFinset.card + 5) :
    IsMinor (⊤ : SimpleGraph (Fin 5)) G := by
  classical
  refine mader_K5_aux _ G univ (by simp) hn (by intro _ _ _; simp) ?_
  convert h using 3
  ext e; simp

open Classical in
/-- K₅-minor-free graphs have at most 3n − 6 edges for n ≥ 3. -/
theorem card_edgeFinset_le_K5 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G) :
    G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  by_contra hbound
  exact h (mader_K5 G hn (by omega))

end Counting

end CliqueMinors
