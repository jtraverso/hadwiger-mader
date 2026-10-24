/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Graph operations used in the clique-minor arguments

Edge contraction, neighbourhood graphs and the two-vertex replacement used in Dirac's argument,
expressed as graphs on the same vertex type, together with the degree and edge counts needed for
the minimal-counterexample arguments in `CliqueMinorsLib.Minors`.
-/

@[expose] public section

open SimpleGraph

namespace CliqueMinors

variable {V : Type*}

section GraphOps


variable [Fintype V]

open Classical in
/-- Contraction of the vertex `y` into the vertex `x`, keeping the vertex type: `y` becomes
isolated and `x` receives the former neighbours of `y`. -/
def contractG (G : SimpleGraph V) (x y : V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ a ≠ y ∧ b ≠ y ∧ (G.Adj a b ∨ (a = x ∧ G.Adj y b) ∨ (b = x ∧ G.Adj y a))
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.2.1, h.2.1, by
    rcases h.2.2.2 with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

open Classical in
omit [Fintype V] in
theorem contractG_adj {G : SimpleGraph V} {x y a b : V} :
    (contractG G x y).Adj a b ↔
      a ≠ b ∧ a ≠ y ∧ b ≠ y ∧ (G.Adj a b ∨ (a = x ∧ G.Adj y b) ∨ (b = x ∧ G.Adj y a)) :=
  Iff.rfl

open Classical in
/-- The graph induced by `G` on the neighbourhood of `x` (as a graph on the same vertex type). -/
def coneG (G : SimpleGraph V) (x : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ G.Adj x a ∧ G.Adj x b
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

open Classical in
omit [Fintype V] in
theorem coneG_adj {G : SimpleGraph V} {x a b : V} :
    (coneG G x).Adj a b ↔ G.Adj a b ∧ G.Adj x a ∧ G.Adj x b :=
  Iff.rfl

open Classical in
theorem exists_adj_of_card_pos {G : SimpleGraph V} (h : 0 < G.edgeFinset.card) :
    ∃ a b, G.Adj a b := by
  obtain ⟨e, he⟩ := Finset.card_pos.1 h
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, b, by simpa using he⟩

open Classical in
theorem card_edge_contract {G : SimpleGraph V} {x y : V} (hxy : G.Adj x y) :
    G.edgeFinset.card ≤ (contractG G x y).edgeFinset.card + 1 +
      (G.neighborFinset x ∩ G.neighborFinset y).card := by
  set E1 := G.edgeFinset.filter (fun e => y ∉ e)
  set T := G.neighborFinset y \ insert x (G.neighborFinset x)
  have h1 : E1 ∪ T.image (fun v => s(x, v)) ⊆ (contractG G x y).edgeFinset := by
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · rw [Finset.mem_filter] at he
      obtain ⟨he, hy⟩ := he
      induction e using Sym2.ind with
      | _ a b =>
        have hab : G.Adj a b := by simpa using he
        simp only [Sym2.mem_iff, not_or] at hy
        simp only [mem_edgeFinset, mem_edgeSet]
        exact contractG_adj.2 ⟨hab.ne, Ne.symm hy.1, Ne.symm hy.2, Or.inl hab⟩
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
      simp only [T, Finset.mem_sdiff, Finset.mem_insert, mem_neighborFinset, not_or] at hv
      simp only [mem_edgeFinset, mem_edgeSet]
      exact contractG_adj.2 ⟨Ne.symm hv.2.1, hxy.ne, hv.1.ne.symm, Or.inr (Or.inl ⟨rfl, hv.1⟩)⟩
  have hdisj : Disjoint E1 (T.image (fun v => s(x, v))) := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he'
    simp only [T, Finset.mem_sdiff, Finset.mem_insert, mem_neighborFinset, not_or] at hv
    rw [Finset.mem_filter] at he
    exact hv.2.2 (by simpa using he.1)
  have himg : (T.image (fun v => s(x, v))).card = T.card :=
    Finset.card_image_of_injective _ (fun a b h => Sym2.congr_right.1 h)
  have hE1 : G.edgeFinset.card = E1.card + G.degree y := by
    rw [← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter,
      Finset.card_filter_add_card_filter_not (s := G.edgeFinset) (p := fun e => y ∉ e) |>.symm]
    simp [E1]
  have hT : G.degree y ≤ T.card + 1 + (G.neighborFinset x ∩ G.neighborFinset y).card := by
    have h2 : T.card + (G.neighborFinset y ∩ insert x (G.neighborFinset x)).card =
        (G.neighborFinset y).card := Finset.card_sdiff_add_card_inter _ _
    have h3 : G.neighborFinset y ∩ insert x (G.neighborFinset x) ⊆
        insert x (G.neighborFinset x ∩ G.neighborFinset y) := by
      intro v hv
      simp only [Finset.mem_inter, Finset.mem_insert] at hv ⊢
      tauto
    have h4 := (Finset.card_le_card h3).trans (Finset.card_insert_le _ _)
    rw [← card_neighborFinset_eq_degree]
    omega
  have h5 := Finset.card_le_card h1
  rw [Finset.card_union_of_disjoint hdisj, himg] at h5
  omega

open Classical in
omit [Fintype V] in
theorem contract_support {G : SimpleGraph V} {S : Finset V} {x y : V} (hxy : G.Adj x y)
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) :
    ∀ a b, (contractG G x y).Adj a b → a ∈ S.erase y := by
  intro a b h
  refine Finset.mem_erase.2 ⟨h.2.1, ?_⟩
  rcases h.2.2.2 with h | ⟨rfl, _⟩ | ⟨_, h⟩
  · exact hsupp _ _ h
  · exact hsupp _ _ hxy
  · exact hsupp _ _ h.symm

open Classical in
theorem contract_degree {G : SimpleGraph V} {S : Finset V} {x y : V} (k : ℕ) (hxy : G.Adj x y)
    (hdeg : ∀ v ∈ S, k ≤ G.degree v)
    (hmerge : k ≤ (((G.neighborFinset x ∪ G.neighborFinset y).erase x).erase y).card)
    (hcommon : ∀ z, G.Adj x z → G.Adj y z → k + 1 ≤ G.degree z) :
    ∀ v ∈ S.erase y, k ≤ (contractG G x y).degree v := by
  intro v hv
  obtain ⟨hvy, hvS⟩ := Finset.mem_erase.1 hv
  rw [← card_neighborFinset_eq_degree]
  by_cases hvx : v = x
  · subst hvx
    refine hmerge.trans (Finset.card_le_card fun t ht => ?_)
    simp only [Finset.mem_erase, Finset.mem_union, mem_neighborFinset] at ht
    rw [mem_neighborFinset]
    refine ⟨Ne.symm ht.2.1, hvy, ht.1, ?_⟩
    rcases ht.2.2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, h⟩)
  have hsub1 : (G.neighborFinset v).erase y ⊆ (contractG G x y).neighborFinset v := by
    intro t ht
    simp only [Finset.mem_erase, mem_neighborFinset] at ht
    rw [mem_neighborFinset]
    exact ⟨ht.2.ne, hvy, ht.1, Or.inl ht.2⟩
  by_cases hvy' : G.Adj v y
  · by_cases hvx' : G.Adj v x
    · have := hcommon v hvx'.symm hvy'.symm
      have h1 := Finset.card_le_card hsub1
      rw [Finset.card_erase_of_mem (by simpa using hvy'), card_neighborFinset_eq_degree] at h1
      omega
    · have hsub2 : insert x ((G.neighborFinset v).erase y) ⊆
          (contractG G x y).neighborFinset v := by
        refine Finset.insert_subset ?_ hsub1
        rw [mem_neighborFinset]
        exact ⟨hvx, hvy, hxy.ne, Or.inr (Or.inr ⟨rfl, hvy'.symm⟩)⟩
      have h1 := Finset.card_le_card hsub2
      rw [Finset.card_insert_of_notMem (by simp [hvx']),
        Finset.card_erase_of_mem (by simpa using hvy'), card_neighborFinset_eq_degree] at h1
      have := hdeg v hvS
      omega
  · have hsub : G.neighborFinset v ⊆ (contractG G x y).neighborFinset v := by
      intro t ht
      rw [mem_neighborFinset] at ht ⊢
      exact ⟨ht.ne, hvy, fun h => hvy' (h ▸ ht), Or.inl ht⟩
    exact (hdeg v hvS).trans ((card_neighborFinset_eq_degree G v).symm.le.trans
      (Finset.card_le_card hsub))

open Classical in
theorem cone_edges {G : SimpleGraph V} {x : V} {m : ℕ}
    (hc : ∀ v, G.Adj x v → m ≤ (G.neighborFinset x ∩ G.neighborFinset v).card) :
    m * (G.neighborFinset x).card ≤ 2 * (coneG G x).edgeFinset.card := by
  rw [← sum_degrees_eq_twice_card_edges]
  calc m * (G.neighborFinset x).card = ∑ v ∈ G.neighborFinset x, m := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ v ∈ G.neighborFinset x, (coneG G x).degree v := by
        refine Finset.sum_le_sum fun v hv => ?_
        rw [mem_neighborFinset] at hv
        refine (hc v hv).trans ?_
        rw [← card_neighborFinset_eq_degree]
        refine Finset.card_le_card fun t ht => ?_
        simp only [Finset.mem_inter, mem_neighborFinset] at ht
        rw [mem_neighborFinset]
        exact ⟨ht.2, hv, ht.1⟩
    _ ≤ ∑ v, (coneG G x).degree v :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)

open Classical in
omit [Fintype V] in
theorem three_le_card {s : Finset V} {p q r : V} (hp : p ∈ s) (hq : q ∈ s) (hr : r ∈ s)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : 3 ≤ s.card := by
  have h3 : ({p, q, r} : Finset V).card = 3 := Finset.card_eq_three.2 ⟨p, q, r, hpq, hpr, hqr, rfl⟩
  rw [← h3]
  refine Finset.card_le_card fun t ht => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl <;> assumption

open Classical in
omit [Fintype V] in
theorem exists_mem_ne_ne {s : Finset V} (h : 3 ≤ s.card) (p q : V) :
    ∃ z ∈ s, z ≠ p ∧ z ≠ q := by
  have h1 := Finset.pred_card_le_card_erase (s := s) (a := p)
  have h2 := Finset.pred_card_le_card_erase (s := s.erase p) (a := q)
  obtain ⟨z, hz⟩ := Finset.card_pos.1 (show 0 < ((s.erase p).erase q).card by omega)
  simp only [Finset.mem_erase] at hz
  exact ⟨z, hz.2.2, hz.2.1, hz.1⟩

open Classical in
omit [Fintype V] in
theorem eq_of_card_le_three {s : Finset V} (h : s.card ≤ 3) {p q r : V} (hp : p ∈ s)
    (hq : q ∈ s) (hr : r ∈ s) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {t : V} (ht : t ∈ s) :
    t = p ∨ t = q ∨ t = r := by
  by_contra hne
  simp only [not_or] at hne
  have h3 : ({p, q, r} : Finset V).card = 3 := Finset.card_eq_three.2 ⟨p, q, r, hpq, hpr, hqr, rfl⟩
  have h4 : (insert t ({p, q, r} : Finset V)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hne.1, hne.2.1, hne.2.2]), h3]
  have : (insert t ({p, q, r} : Finset V)).card ≤ s.card := by
    refine Finset.card_le_card fun u hu => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> assumption
  omega

open Classical in
theorem mem_merged {G : SimpleGraph V} {x y t : V} :
    t ∈ ((G.neighborFinset x ∪ G.neighborFinset y).erase x).erase y ↔
      t ≠ y ∧ t ≠ x ∧ (G.Adj x t ∨ G.Adj y t) := by
  simp

open Classical in
/-- Two-vertex replacement used in Dirac's argument: delete `x` and `b`, add the edge `ac`. -/
def opG (G : SimpleGraph V) (x b a c : V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ u ≠ x ∧ u ≠ b ∧ v ≠ x ∧ v ≠ b ∧
    (G.Adj u v ∨ (u = a ∧ v = c) ∨ (u = c ∧ v = a))
  symm := ⟨fun u v h => ⟨h.1.symm, h.2.2.2.1, h.2.2.2.2.1, h.2.1, h.2.2.1, by
    rcases h.2.2.2.2.2 with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

open Classical in
omit [Fintype V] in
theorem opG_adj {G : SimpleGraph V} {x b a c u v : V} :
    (opG G x b a c).Adj u v ↔ u ≠ v ∧ u ≠ x ∧ u ≠ b ∧ v ≠ x ∧ v ≠ b ∧
      (G.Adj u v ∨ (u = a ∧ v = c) ∨ (u = c ∧ v = a)) :=
  Iff.rfl

open Classical in
omit [Fintype V] in
theorem deleteIncidenceSet_supp {G : SimpleGraph V} {S : Finset V} {v : V}
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) :
    ∀ a b, (G.deleteIncidenceSet v).Adj a b → a ∈ S.erase v := by
  intro a b h
  rw [deleteIncidenceSet_adj] at h
  exact Finset.mem_erase.2 ⟨h.2.1, hsupp _ _ h.1⟩

open Classical in
omit [Fintype V] in
theorem deleteIncidenceSet_le' (G : SimpleGraph V) (v : V) : G.deleteIncidenceSet v ≤ G :=
  fun _ _ h => (deleteIncidenceSet_adj.1 h).1

open Classical in
theorem card_edges_deleteIncidenceSet (G G' : SimpleGraph V) (v : V)
    (hG' : G' = G.deleteIncidenceSet v) :
    G.edgeFinset.card = G'.edgeFinset.card + G.degree v := by
  subst hG'
  have h1 := card_edgeFinset_deleteIncidenceSet G v
  have h2 : G.degree v ≤ G.edgeFinset.card := by
    rw [← card_incidenceFinset_eq_degree]
    exact Finset.card_le_card (G.incidenceFinset_subset v)
  convert (Nat.sub_add_cancel h2).symm using 3
  convert h1 using 2
  ext e; simp

end GraphOps

end CliqueMinors
