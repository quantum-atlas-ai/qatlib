/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NoncommGibbs23.MainResults.Model

@[expose] public section


set_option autoImplicit false

namespace Qatlib.Papers.NoncommGibbs23.MainResults
open Qatlib.Papers.NoncommGibbs23.MainResults

/-! ## Lemma II.2: factorization and skew-symmetry -/

/-- Energy-domain factor `f̂₊` of the Gaussian coefficient (2.3), p. 11. -/
noncomputable def gaussianFactorPlus (σE σγ ωγ ν : ℝ) : ℝ :=
  σγ / Real.sqrt (σE ^ 2 + σγ ^ 2) *
    Real.exp (-(ν + 2 * ωγ) ^ 2 / (8 * (σE ^ 2 + σγ ^ 2)))

/-- Energy-domain factor `f̂₋` of the Gaussian coefficient (2.3), p. 11. -/
noncomputable def gaussianFactorMinus (σE ν : ℝ) : ℝ :=
  Real.exp (-ν ^ 2 / (8 * σE ^ 2))

/-- **Lemma II.2, factorization (2.3)** (p. 11). The Gaussian coefficients factor as
`α_{ν1ν2} = f̂₊(ν1+ν2) · f̂₋(ν1-ν2)`. -/
theorem lemmaII2_factorization (σE σγ ωγ ν1 ν2 : ℝ) :
    gaussianCoeff σE σγ ωγ ν1 ν2 =
      gaussianFactorPlus σE σγ ωγ (ν1 + ν2) * gaussianFactorMinus σE (ν1 - ν2) := by
  simp only [gaussianCoeff, gaussianFactorPlus, gaussianFactorMinus]

/-- **Lemma II.2, skew-symmetry (2.4)** (p. 11). With `β = 2ωγ/(σE²+σγ²)`, the
Gaussian coefficients satisfy
`α_{ν1ν2} e^{β(ν1+ν2)/2} = α_{-ν2,-ν1}`. -/
theorem lemmaII2_skewSymmetry (σE σγ ωγ ν1 ν2 : ℝ)
    (hσE : 0 < σE) (hσγ : 0 < σγ) :
    gaussianCoeff σE σγ ωγ ν1 ν2 *
        Real.exp (gaussianBeta σE σγ ωγ * (ν1 + ν2) / 2)
      = gaussianCoeff σE σγ ωγ (-ν2) (-ν1) := by
  have hS : σE ^ 2 + σγ ^ 2 ≠ 0 := by positivity
  have hE : σE ^ 2 ≠ 0 := by positivity
  simp only [gaussianCoeff, gaussianBeta]
  have h3 : ∀ x y z : ℝ,
      Real.exp x * Real.exp y * Real.exp z = Real.exp (x + y + z) := by
    intro x y z
    rw [← Real.exp_add, ← Real.exp_add]
  have h2 : ∀ x y : ℝ, Real.exp x * Real.exp y = Real.exp (x + y) :=
    fun x y => (Real.exp_add x y).symm
  set A : ℝ := σγ / Real.sqrt (σE ^ 2 + σγ ^ 2) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have hL : A * Real.exp (-(ν1 + ν2 + 2 * ωγ) ^ 2 / (8 * (σE ^ 2 + σγ ^ 2))) *
        Real.exp (-(ν1 - ν2) ^ 2 / (8 * σE ^ 2)) *
        Real.exp (2 * ωγ / (σE ^ 2 + σγ ^ 2) * (ν1 + ν2) / 2)
      = A * Real.exp (-(ν1 + ν2 + 2 * ωγ) ^ 2 / (8 * (σE ^ 2 + σγ ^ 2)) +
          -(ν1 - ν2) ^ 2 / (8 * σE ^ 2) +
          2 * ωγ / (σE ^ 2 + σγ ^ 2) * (ν1 + ν2) / 2) := by
    rw [show A * Real.exp (-(ν1 + ν2 + 2 * ωγ) ^ 2 / (8 * (σE ^ 2 + σγ ^ 2))) *
          Real.exp (-(ν1 - ν2) ^ 2 / (8 * σE ^ 2)) *
          Real.exp (2 * ωγ / (σE ^ 2 + σγ ^ 2) * (ν1 + ν2) / 2)
        = A * (Real.exp (-(ν1 + ν2 + 2 * ωγ) ^ 2 / (8 * (σE ^ 2 + σγ ^ 2))) *
            Real.exp (-(ν1 - ν2) ^ 2 / (8 * σE ^ 2)) *
            Real.exp (2 * ωγ / (σE ^ 2 + σγ ^ 2) * (ν1 + ν2) / 2)) by ring]
    rw [h3]
  have hR : A * Real.exp (-(-ν2 + -ν1 + 2 * ωγ) ^ 2 / (8 * (σE ^ 2 + σγ ^ 2))) *
        Real.exp (-(-ν2 - -ν1) ^ 2 / (8 * σE ^ 2))
      = A * Real.exp (-(-ν2 + -ν1 + 2 * ωγ) ^ 2 / (8 * (σE ^ 2 + σγ ^ 2)) +
          (-(-ν2 - -ν1) ^ 2 / (8 * σE ^ 2))) := by
    rw [show A * Real.exp (-(-ν2 + -ν1 + 2 * ωγ) ^ 2 / (8 * (σE ^ 2 + σγ ^ 2))) *
          Real.exp (-(-ν2 - -ν1) ^ 2 / (8 * σE ^ 2))
        = A * (Real.exp (-(-ν2 + -ν1 + 2 * ωγ) ^ 2 / (8 * (σE ^ 2 + σγ ^ 2))) *
            Real.exp (-(-ν2 - -ν1) ^ 2 / (8 * σE ^ 2))) by ring]
    rw [h2]
  rw [hL, hR]
  apply mul_left_cancel₀ (ne_of_gt hApos)
  congr 1
  field_simp
  ring


end Qatlib.Papers.NoncommGibbs23.MainResults
