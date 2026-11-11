/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FluctThermal22.MainResults.Framework.ThermalWorkModel

set_option backward.isDefEq.respectTransparency false

/-!
# Vector norms and matrix–vector products for state-level statements

Fixed source: arXiv:2203.08882.  The state-level lemmas (Lemma 3.1, 3.2, 3.4,
3.5, 3.6, E.1) are statements about Hilbert-space vectors `|Ψ⟩` and the
Euclidean norm squares `‖A|Ψ⟩‖²`.  To keep them independent of any particular
`EuclideanSpace` instance choice, we define the squared Euclidean norm of a
complex vector `κ → ℂ` directly as a finite sum of `Complex.normSq`, and the
matrix–vector product by an explicit finite sum.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.FluctThermal22.MainResults.Framework

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- Squared Euclidean norm `‖v‖² = Σ_i |v_i|²` of a finite complex vector. -/
def l2normSq (v : κ → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

/-- Matrix–vector product `A *ᵥ v` as an explicit finite sum. -/
def matVec (A : Matrix κ κ ℂ) (v : κ → ℂ) : κ → ℂ := fun i => ∑ j, A i j * v j

/-- The `k`-th column of a matrix, viewed as a vector. -/
def col (V : Matrix κ κ ℂ) (k : κ) : κ → ℂ := fun i => V i k

/-- The Euclidean squared norm is nonnegative. -/
theorem l2normSq_nonneg (v : κ → ℂ) : 0 ≤ l2normSq v :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

/-- The zero vector has zero squared norm. -/
theorem l2normSq_zero : l2normSq (κ := κ) (fun _ => (0 : ℂ)) = 0 := by
  unfold l2normSq
  simp

/-- Squared norm of a scalar multiple. -/
theorem l2normSq_smul (c : ℂ) (v : κ → ℂ) :
    l2normSq (fun i => c * v i) = Complex.normSq c * l2normSq v := by
  unfold l2normSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.normSq_mul]

end Qatlib.Papers.FluctThermal22.MainResults.Framework
