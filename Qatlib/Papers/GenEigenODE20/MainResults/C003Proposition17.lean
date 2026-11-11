/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenEigenODE20.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# c003 — Proposition 17, Eqs. (33)--(35)

Shao--Liu, arXiv:2010.15027v2, Proposition 17, pp. 12--13.

For the discretisation matrix `M` of Eq. (27) the paper proves

* `‖M‖ = Θ(‖I ⊗ A - τ⁻¹ D ⊗ B‖)`  (33),
* `‖M⁻¹‖ ≤ O(κ_E ‖B⁻¹‖ / ε)`  (34),
* hence `κ(M) ≤ O(κ_E (‖A‖ + ρ‖B‖) ‖B⁻¹‖ / ε)`  (35).

This module records the `Θ`-relation as an explicit two-constant predicate,
proves that it is symmetric (the direction actually used when (33) is read as
a norm comparison), and proves the condition-number composition (35) from the
inverse-norm bound (34) and the operator-norm bound for `M`.  The constants
`c_M` and the factor `c_M` in (35) are the unspecified constants of the paper's
`O(·)` and are kept explicit rather than hidden.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GenEigenODE20.MainResults

/-- Two nonnegative quantities are `Θ`-equivalent when each is bounded by a
positive constant multiple of the other.  This is the content of Eq. (33). -/
def ThetaEquivalent (x y : ℝ) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ c₁ * y ≤ x ∧ x ≤ c₂ * y

/-- `Θ`-equivalence is symmetric: Eq. (33) may be read in either direction. -/
theorem thetaEquivalent_symm {x y : ℝ} (hy : 0 < y) (h : ThetaEquivalent x y) :
    ThetaEquivalent y x := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hle₁, hle₂⟩ := h
  refine ⟨c₂⁻¹, c₁⁻¹, by positivity, by positivity, ?_, ?_⟩
  · have hm := mul_le_mul_of_nonneg_left hle₂ (le_of_lt (inv_pos.mpr hc₂))
    have heq : c₂⁻¹ * (c₂ * y) = y := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc₂), one_mul]
    linarith
  · have hm := mul_le_mul_of_nonneg_left hle₁ (le_of_lt (inv_pos.mpr hc₁))
    have heq : c₁⁻¹ * (c₁ * y) = y := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc₁), one_mul]
    linarith

/-- **Eq. (34) as a big-`O` statement.**  The paper's inverse-norm bound is
equivalent to the existence of a positive constant `C` with
`‖M⁻¹‖ ≤ C · κ_E ‖B⁻¹‖ / ε`. -/
theorem prop17_inverse_norm_bigO
    (normMinv κE BinvNorm ε : ℝ)
    (h : normMinv ≤ κE * BinvNorm / ε) :
    ∃ C : ℝ, 0 < C ∧ normMinv ≤ C * (κE * BinvNorm / ε) :=
  ⟨1, one_pos, by simpa using h⟩

/-- **Proposition 17, Eq. (35).**  Combining the operator-norm bound
`‖M‖ ≤ c_M (‖A‖ + ρ‖B‖)` with the inverse-norm bound (34) gives the paper's
condition-number bound. -/
theorem prop17_condition_number_bound
    (normM normMinv κE BinvNorm normA normB ρ cM ε : ℝ)
    (hMinv : normMinv ≤ κE * BinvNorm / ε)
    (hM : normM ≤ cM * (normA + ρ * normB))
    (hε : 0 < ε) (hκ : 0 ≤ κE) (hB : 0 ≤ BinvNorm)
    (hcM : 0 ≤ cM) (hA : 0 ≤ normA) (hBv : 0 ≤ normB) (hρ : 0 ≤ ρ)
    (hMinv0 : 0 ≤ normMinv) :
    normM * normMinv ≤ cM * (normA + ρ * normB) * (κE * BinvNorm / ε) := by
  have hK : 0 ≤ κE * BinvNorm / ε := by positivity
  have hM0 : 0 ≤ cM * (normA + ρ * normB) := by positivity
  exact mul_le_mul hM hMinv hMinv0 hM0

/-- **Eq. (33), directional form.**  If `‖M‖` is `Θ`-equivalent to the norm of
`I ⊗ A - τ⁻¹ D ⊗ B`, then that latter norm is `Θ`-equivalent to `‖M‖` as well,
with the constants inverted. -/
theorem prop17_M_norm_theta {normM K : ℝ} (hK : 0 < K)
    (h : ThetaEquivalent normM K) : ThetaEquivalent K normM :=
  thetaEquivalent_symm hK h

end Qatlib.Papers.GenEigenODE20.MainResults
