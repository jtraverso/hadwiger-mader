/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CliqueMinorsLib.K5Density

/-!
# Proofs of the statements in `Challenge.lean`

The definitions below are verbatim copies of those in `Challenge.lean`; minor models coincide field
by field with `CliqueMinors.MinorModel` of `CliqueMinorsLib/Minors.lean`, where the theorems are
proved (Mader's theorem by induction on `r` and on the number of vertices with edge contractions;
Dirac's lemma by a minimal counterexample; Hadwiger's conjecture for `t ≤ 4` by colouring greedily
along vertices of degree at most two).
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

/-- The minor notion of this file is that of `CliqueMinorsLib`. -/
theorem isMinor_iff_lib {V W : Type*} (H : SimpleGraph W) (G : SimpleGraph V) :
    IsMinor H G ↔ CliqueMinors.IsMinor H G := by
  constructor
  · rintro ⟨M⟩
    exact ⟨⟨M.branch, M.branch_nonempty, M.branch_connected, M.branch_disjoint,
      M.branch_adjacent⟩⟩
  · rintro ⟨M⟩
    exact ⟨⟨M.branch, M.branch_nonempty, M.branch_connected, M.branch_disjoint,
      M.branch_adjacent⟩⟩

/-- **Mader's theorem (1967).** A nonempty finite graph whose average degree is at least
`2 ^ (r - 2)`, i.e. `2 ^ r · |V| ≤ 8 · |E|`, has the complete graph `K_r` as a minor. -/
theorem mader [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (h : 2 ^ r * Fintype.card V ≤ 8 * G.edgeFinset.card) :
    IsMinor (⊤ : SimpleGraph (Fin r)) G :=
  (isMinor_iff_lib _ G).2 (CliqueMinors.mader G r h)

/-- **Dirac (1952).** A nonempty finite graph without a `K₄` minor has a vertex of degree at most
two. -/
theorem exists_degree_le_two [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) : ∃ v, G.degree v ≤ 2 :=
  CliqueMinors.exists_degree_le_two G (fun h' => h ((isMinor_iff_lib _ G).2 h'))

/-- A finite graph on `n ≥ 2` vertices without a `K₄` minor has at most `2n - 3` edges. -/
theorem card_edgeFinset_le [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) :
    G.edgeFinset.card + 3 ≤ 2 * Fintype.card V :=
  CliqueMinors.card_edgeFinset_le G hn (fun h' => h ((isMinor_iff_lib _ G).2 h'))

/-- **Hadwiger's conjecture for `t = 3`.** A finite graph without a `K₃` minor (a forest) is
2-colourable. -/
theorem colorable_two_of_not_isMinor_K3 [Finite V] (G : SimpleGraph V)
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 3)) G) : G.Colorable 2 :=
  CliqueMinors.colorable_two_of_not_isMinor_K3 G (fun h' => h ((isMinor_iff_lib _ G).2 h'))

/-- **Hadwiger's conjecture for `t = 4` (Hadwiger 1943, Dirac 1952).** A finite graph without a
`K₄` minor is 3-colourable. -/
theorem colorable_three_of_not_isMinor_K4 [Finite V] (G : SimpleGraph V)
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) : G.Colorable 3 :=
  CliqueMinors.colorable_three_of_not_isMinor_K4 G
    (fun h' => h ((isMinor_iff_lib _ G).2 h'))

/-- A finite minor has no more vertices than its host graph. -/
theorem card_le_of_isMinor [Fintype V] [Fintype W]
    (H : SimpleGraph W) (G : SimpleGraph V) (h : IsMinor H G) :
    Fintype.card W ≤ Fintype.card V :=
  CliqueMinors.card_le_of_isMinor H G ((isMinor_iff_lib H G).mp h)

/-- Mader's K₅ edge threshold for n ≥ 3, stated without truncated subtraction. -/
theorem mader_K5 [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V) (h : 3 * Fintype.card V ≤ G.edgeFinset.card + 5) :
    IsMinor (⊤ : SimpleGraph (Fin 5)) G :=
  (isMinor_iff_lib _ G).mpr (CliqueMinors.mader_K5 G hn h)

/-- K₅-minor-free finite graphs on n ≥ 3 vertices have at most 3n − 6 edges. -/
theorem card_edgeFinset_le_K5 [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 5)) G) :
    G.edgeFinset.card + 6 ≤ 3 * Fintype.card V :=
  CliqueMinors.card_edgeFinset_le_K5 G hn (fun h' => h ((isMinor_iff_lib _ G).mpr h'))

end HadwigerMader
