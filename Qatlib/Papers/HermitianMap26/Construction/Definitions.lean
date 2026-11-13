/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Nat.Log
import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureKraus

/-!
# Signed Kraus data and normalization

This module defines the operator and signed Kraus data used in the construction of
[CaiEtAl2026]. A `SignedKraus` family has coefficients in `{1, -1}` and satisfies the signed
trace-preservation identity; `action` is its signed operator sum.

The module introduces inverse-square-root normalization, a family extended by a completion
operator, and branch post-processing weights. The final branch has weight zero, and
`completedKraus_complete` proves completeness when its Gram matrix fills the normalization
deficit.

## Main statements

* `SignedKraus`: bundles operators, signs, and the signed completeness equation.
* `normalizedSum_eq_inv`: expresses the normalized Gram sum for a positive scale.
* `completedKraus_complete`: proves completeness of a family with a suitable completion.

## References

* [Cai et al., 2026][CaiEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ComplexOrder BigOperators

namespace Qatlib.Papers.HermitianMap26.Construction

/-- Complex square matrices of dimension `d`, used as operators. -/
abbrev Op (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- A family of `r` operators with coefficients equal to one or minus one, satisfying the signed
Kraus trace-preservation identity. -/
structure SignedKraus (d r : ℕ) where

  K : Fin r → Op d

  α : Fin r → ℂ

  sign : ∀ i, α i = 1 ∨ α i = -1

  tracePreserving : ∑ i, α i • ((K i)ᴴ * K i) = 1

namespace SignedKraus

variable {d r : ℕ} (D : SignedKraus d r)

/-- The signed Kraus action `∑ i, D.α i • (D.K i * ρ * (D.K i)ᴴ)`. -/
def action (ρ : Op d) : Op d :=
  ∑ i, D.α i • (D.K i * ρ * (D.K i)ᴴ)

/-- The unsigned sum of the Gram matrices of the Kraus operators. -/
def krausSum : Op d :=
  ∑ i, (D.K i)ᴴ * D.K i

/-- The complex inverse of the real square root of the normalization parameter `γ`. -/
def sqrtScale (γ : ℝ) : ℂ := ((Real.sqrt γ : ℂ))⁻¹

/-- The Kraus operator `D.K i` scaled by the inverse square root of `γ`. -/
def normalizedKraus (γ : ℝ) (i : Fin r) : Op d :=
  sqrtScale γ • D.K i

/-- The sum of the Gram matrices of the normalized Kraus operators. -/
def normalizedSum (γ : ℝ) : Op d :=
  ∑ i, (D.normalizedKraus γ i)ᴴ * D.normalizedKraus γ i

/-- The normalized Kraus family extended by a final operator `C`. -/
def completedKraus (γ : ℝ) (C : Op d) : Fin (r + 1) → Op d :=
  Fin.lastCases C (fun i => D.normalizedKraus γ i)

/-- The branch weights `γ * D.α i` on the original indices and zero on the final completion
branch. -/
def postProcessingWeight (γ : ℝ) : Fin (r + 1) → ℂ :=
  Fin.lastCases 0 (fun i => (γ : ℂ) * D.α i)

/-- The real part of the trace pairing of the signed Kraus output `D.action ρ` with `O`. -/
def compiledMean (ρ O : Op d) : ℝ := (D.action ρ * O).trace.re

/-- For positive `γ`, the scale multiplied by its conjugate equals the complex inverse of `γ`. -/
lemma sqrtScale_mul_star (γ : ℝ) (hγ : 0 < γ) :
    sqrtScale γ * star (sqrtScale γ) = ((γ : ℂ))⁻¹ := by
  unfold sqrtScale
  rw [Complex.star_def, ← Complex.ofReal_inv, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [← Complex.ofReal_inv, Complex.ofReal_inj, ← mul_inv, Real.mul_self_sqrt hγ.le]

/-- For positive `γ`, the conjugate scale multiplied by the scale equals the complex inverse of
`γ`. -/
lemma star_mul_sqrtScale (γ : ℝ) (hγ : 0 < γ) :
    star (sqrtScale γ) * sqrtScale γ = ((γ : ℂ))⁻¹ := by
  rw [mul_comm, sqrtScale_mul_star γ hγ]

/-- The normalized Gram sum equals the unsigned Kraus sum scaled by `star (sqrtScale γ) *
sqrtScale γ`. -/
lemma normalizedSum_eq (γ : ℝ) :
    D.normalizedSum γ = (star (sqrtScale γ) * sqrtScale γ) • D.krausSum := by
  unfold normalizedSum krausSum normalizedKraus sqrtScale
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- For positive `γ`, the normalized Gram sum is `γ⁻¹` times the unsigned Kraus sum. -/
lemma normalizedSum_eq_inv (γ : ℝ) (hγ : 0 < γ) :
    D.normalizedSum γ = ((γ : ℂ))⁻¹ • D.krausSum := by
  rw [D.normalizedSum_eq γ, star_mul_sqrtScale γ hγ]

/-- The final member of the completed family is the completion operator `C`. -/
@[simp] lemma completedKraus_last (γ : ℝ) (C : Op d) :
    D.completedKraus γ C (Fin.last r) = C :=
  Fin.lastCases_last

/-- At an original index, the completed family equals the corresponding normalized Kraus
operator. -/
@[simp] lemma completedKraus_castSucc (γ : ℝ) (C : Op d) (i : Fin r) :
    D.completedKraus γ C i.castSucc = D.normalizedKraus γ i :=
  Fin.lastCases_castSucc i

/-- The post-processing weight at an original index is `γ * D.α i`. -/
@[simp] lemma postProcessingWeight_castSucc (γ : ℝ) (i : Fin r) :
    D.postProcessingWeight γ i.castSucc = (γ : ℂ) * D.α i :=
  Fin.lastCases_castSucc i

/-- The post-processing weight of the completion branch is zero. -/
@[simp] lemma postProcessingWeight_last (γ : ℝ) :
    D.postProcessingWeight γ (Fin.last r) = 0 :=
  Fin.lastCases_last

/-- If the Gram matrix of `C` fills the deficit of the normalized Gram sum, appending `C` gives
a Kraus-complete family. -/
theorem completedKraus_complete (γ : ℝ) {C : Op d}
    (hC : Cᴴ * C = 1 - D.normalizedSum γ) :
    Qatlib.Concepts.ChannelTheory.Stinespring.KrausComplete
      (D.completedKraus γ C) := by
  unfold Qatlib.Concepts.ChannelTheory.Stinespring.KrausComplete
  rw [Fin.sum_univ_castSucc]
  simp only [completedKraus_castSucc, completedKraus_last]
  unfold normalizedSum at hC
  rw [hC]
  abel

end SignedKraus

end Qatlib.Papers.HermitianMap26.Construction
