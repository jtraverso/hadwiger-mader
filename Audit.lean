/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

import Solution

/-! Axiom audit and small-order boundary checks. -/

#print axioms HadwigerMader.mader
#print axioms HadwigerMader.exists_degree_le_two
#print axioms HadwigerMader.card_edgeFinset_le
#print axioms HadwigerMader.colorable_two_of_not_isMinor_K3
#print axioms HadwigerMader.colorable_three_of_not_isMinor_K4
#print axioms HadwigerMader.card_le_of_isMinor
#print axioms HadwigerMader.mader_K5
#print axioms HadwigerMader.card_edgeFinset_le_K5

-- The small-order guard is essential: K₂ satisfies the density inequality,
-- but cannot have K₅ as a minor.
example : 3 * Fintype.card (Fin 2) ≤
    (⊤ : SimpleGraph (Fin 2)).edgeFinset.card + 5 ∧
    ¬ HadwigerMader.IsMinor (⊤ : SimpleGraph (Fin 5)) (⊤ : SimpleGraph (Fin 2)) := by
  constructor
  · decide
  · intro h
    have hcard := HadwigerMader.card_le_of_isMinor _ _ h
    norm_num at hcard

-- K₄ attains 3n−6, and still has no K₅ minor.
example : (⊤ : SimpleGraph (Fin 4)).edgeFinset.card + 6 = 3 * Fintype.card (Fin 4) ∧
    ¬ HadwigerMader.IsMinor (⊤ : SimpleGraph (Fin 5)) (⊤ : SimpleGraph (Fin 4)) := by
  constructor
  · decide
  · intro h
    have hcard := HadwigerMader.card_le_of_isMinor _ _ h
    norm_num at hcard

-- At order five the threshold is ten edges and applies to K₅.
example : HadwigerMader.IsMinor (⊤ : SimpleGraph (Fin 5)) (⊤ : SimpleGraph (Fin 5)) := by
  exact HadwigerMader.mader_K5 _ (by decide) (by decide)
