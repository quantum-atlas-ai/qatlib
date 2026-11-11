/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.HermitianMat.CFC
import QuantumInfo.ForMathlib.HermitianMat.Order

set_option backward.isDefEq.respectTransparency false

/-!
# Gram Effects

The actual Gram factor of an arbitrary full-register positive effect, constructed by the existing finite Hermitian functional calculus.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder
open Matrix
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- The actual Gram factor of an arbitrary full-register positive effect, constructed by the existing finite Hermitian functional calculus. -/
def psdGramFactor {I : Type*} [Fintype I] [DecidableEq I]
    (E : HermitianMat I ℂ) : Matrix I I ℂ := (E.cfc Real.sqrt).mat

/-- Every positive full-register effect has the proved actual factor RᴴR; no factorization certificate is an input. -/
theorem psdGramFactor_identity {I : Type*} [Fintype I] [DecidableEq I]
    (E : HermitianMat I ℂ) (hE : 0 ≤ E) :
    (psdGramFactor E)ᴴ * psdGramFactor E = E.mat := by
  unfold psdGramFactor
  rw [(E.cfc Real.sqrt).H, ← HermitianMat.mat_cfc_mul_apply]
  have he : E.cfc (fun x => Real.sqrt x*Real.sqrt x) = E.cfc id := by
    apply E.cfc_congr_of_nonneg hE
    intro x hx
    exact Real.mul_self_sqrt hx
  rw [HermitianMat.cfc_id] at he
  exact congrArg HermitianMat.mat he

/-- The literal quadratic Born weight of a complete-register effect against a supplied vector. -/
def effectWeight {I : Type*} [Fintype I] (E : HermitianMat I ℂ) (ψ : I → ℂ) : ℝ :=
  (star ψ ⬝ᵥ (E.mat *ᵥ ψ)).re

/-- The actual quadratic effect weight decomposes into the squared full-register row amplitudes of its constructed Gram factor. -/
theorem effectWeight_eq_gram_rows {I : Type*} [Fintype I] [DecidableEq I]
    (E : HermitianMat I ℂ) (hE : 0 ≤ E) (ψ : I → ℂ) :
    effectWeight E ψ = ∑ row, Complex.normSq (∑ i, psdGramFactor E row i*ψ i) := by
  unfold effectWeight
  rw [← psdGramFactor_identity E hE, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  change (∑ row, star ((psdGramFactor E *ᵥ ψ) row)*((psdGramFactor E *ᵥ ψ) row)).re = _
  simp only [Complex.re_sum, Matrix.mulVec, dotProduct, Complex.star_def,
    Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add,
    Complex.normSq_apply]

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
