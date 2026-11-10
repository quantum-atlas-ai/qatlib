/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

namespace Qatlib.Papers.AdversarySrch07.MainResults

open Qatlib.Concepts.GramQueryCore.LowerBoundTools

noncomputable def xi (i : ℕ) : ℝ := (Nat.centralBinom i : ℝ) / 4 ^ i

noncomputable def AM (m j : ℕ) : ℝ := ∑ i ∈ Finset.range (m - j), xi i * xi (i + j)

def ospInput (N : ℕ) : Fin (2 * N) → Fin (2 * N) → Fin 2 :=
  fun x j => if (x.val + j.val) % (2 * N) < N then 1 else 0

def ospDelta (N : ℕ) : Fin (2 * N) → Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ :=
  sourceAlphabetDelta (ospInput N)

noncomputable def ospAdvNonneg (N : ℕ) : ℝ≥0∞ :=
  ⨆ Γ : { Γ : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ //
      Γ.IsHermitian ∧
      (∀ x y, (Γ x y).im = 0) ∧
      (∀ x y, x = y → Γ x y = 0) ∧
      (∀ x y, 0 ≤ (Γ x y).re) ∧
      (∀ j : Fin (2 * N), ‖Γ ⊙ ospDelta N j‖ ≤ 1) },
    ENNReal.ofReal ‖Γ.1‖

noncomputable def ospAdvNeg (N : ℕ) : ℝ≥0∞ :=
  sourceAdversary (ospDelta N) (id : Fin (2 * N) → Fin (2 * N))

end Qatlib.Papers.AdversarySrch07.MainResults
