/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Dense graphs have large clique minors; graphs without small clique minors

For finite simple graphs, with minors given by branch-set models (`MinorModel`):

* `HadwigerMader.mader`: **Mader (1967).** A nonempty graph with `2 ^ r · |V| ≤ 8 · |E|` (average
  degree at least `2 ^ (r - 2)`) has `K_r` as a minor.
* `HadwigerMader.exists_degree_le_two`: **Dirac (1952).** A nonempty graph without a `K₄` minor has
  a vertex of degree at most two.
* `HadwigerMader.card_edgeFinset_le`: a graph on `n ≥ 2` vertices without a `K₄` minor has at most
  `2n - 3` edges.
* `HadwigerMader.colorable_two_of_not_isMinor_K3`,
  `HadwigerMader.colorable_three_of_not_isMinor_K4`: **Hadwiger's conjecture for `t ≤ 4`**
  (Hadwiger 1943, Dirac 1952): a finite graph without a `K_t` minor is `(t - 1)`-colourable for
  `t = 3, 4`.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open SimpleGraph

namespace HadwigerMader

variable {V W : Type*}

/-- A branch-set model of `H` as a minor of `G`: disjoint, nonempty, connected branch sets, one
for every vertex of `H`, with an edge of `G` between the branch sets of adjacent vertices. -/
structure MinorModel (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : W → Finset V
  branch_nonempty : ∀ w, (branch w).Nonempty
  branch_connected : ∀ w, (G.induce (↑(branch w) : Set V)).Connected
  branch_disjoint : ∀ w w', w ≠ w' → Disjoint (branch w) (branch w')
  branch_adjacent : ∀ w w', H.Adj w w' → ∃ u ∈ branch w, ∃ v ∈ branch w', G.Adj u v

/-- `H` is a minor of `G`. -/
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop := Nonempty (MinorModel G H)

/-- **Mader's theorem (1967).** A nonempty finite graph whose average degree is at least
`2 ^ (r - 2)`, i.e. `2 ^ r · |V| ≤ 8 · |E|`, has the complete graph `K_r` as a minor. -/
theorem mader [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (h : 2 ^ r * Fintype.card V ≤ 8 * G.edgeFinset.card) :
    IsMinor (⊤ : SimpleGraph (Fin r)) G := by
  sorry

/-- **Dirac (1952).** A nonempty finite graph without a `K₄` minor has a vertex of degree at most
two. -/
theorem exists_degree_le_two [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) : ∃ v, G.degree v ≤ 2 := by
  sorry

/-- A finite graph on `n ≥ 2` vertices without a `K₄` minor has at most `2n - 3` edges. -/
theorem card_edgeFinset_le [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) :
    G.edgeFinset.card + 3 ≤ 2 * Fintype.card V := by
  sorry

/-- **Hadwiger's conjecture for `t = 3`.** A finite graph without a `K₃` minor (a forest) is
2-colourable. -/
theorem colorable_two_of_not_isMinor_K3 [Finite V] (G : SimpleGraph V)
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 3)) G) : G.Colorable 2 := by
  sorry

/-- **Hadwiger's conjecture for `t = 4` (Hadwiger 1943, Dirac 1952).** A finite graph without a
`K₄` minor is 3-colourable. -/
theorem colorable_three_of_not_isMinor_K4 [Finite V] (G : SimpleGraph V)
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) : G.Colorable 3 := by
  sorry

/-- A finite minor has no more vertices than its host graph. -/
theorem card_le_of_isMinor [Fintype V] [Fintype W]
    (H : SimpleGraph W) (G : SimpleGraph V) (h : IsMinor H G) :
    Fintype.card W ≤ Fintype.card V := by
  sorry

/-- Mader's K₅ edge threshold for n ≥ 3, stated without truncated subtraction. -/
theorem mader_K5 [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V) (h : 3 * Fintype.card V ≤ G.edgeFinset.card + 5) :
    IsMinor (⊤ : SimpleGraph (Fin 5)) G := by
  sorry

/-- K₅-minor-free finite graphs on n ≥ 3 vertices have at most 3n − 6 edges. -/
theorem card_edgeFinset_le_K5 [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G) :
    G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  sorry

end HadwigerMader
