/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HeatEquation20.MainResults.Model

@[expose] public section


/-!
# HeatEquation20 — analytic core of the singular values of `T` (B10)–(B11), p. 28

Fixed source: arXiv:2004.06516v2.

Appendix B, eqs. (B10)–(B11) (p. 28) give the singular values of the
`m × m` matrix `T = 1 − S` of (B3), `S` the sub-diagonal shift:

`σ_k = 2 cos(k π / (2m+1))`, `1 ≤ k ≤ m`, and in particular
`σ_min ≤ π/(2m+1)`; this is the lower half of `‖A⁻¹‖ = Θ(m)` in
Proposition 25.  In the locked layer `bidiagT`, `lowerShift` and the predicate
`IsSingularValue` are fixed, but no spectral statement about `bidiagT` is
present.

This file supplies the analytic core of the verification
`(Tᵀ T) v = σ_k² v` for the vector `v_j = sin((2j+1)θ_k)`:

* `two_cos_theta_pos`: the positivity conjunct `0 < 2 cos θ_k` of (B10);
* `bidiag_recurrence_identity`: the interior three-term identity
  `2 sin x + sin (x+2θ) + sin (x−2θ) = 4 cos²θ sin x`, which makes `v` an
  eigenvector at the interior indices;
* `bidiag_boundary_identity`: the boundary identity
  `2 sin A + sin (A−2θ) = 4 cos²θ sin A` under `sin (A+2θ) = 0`, which makes
  `v` an eigenvector at the two boundary indices, since
  `sin ((2m+1) θ_k) = sin (kπ) = 0` (`theta_sin_zero`).

Not supplied here: the finite-dimensional assembly, i.e. the description of
`bidiagT m *ᵥ v` and `(bidiagT m)ᵀ *ᵥ w` as `v_j − v_{j−1}` and `w_j − w_{j+1}`
on the interior with the two boundary conventions, the resulting formula for
`(Tᵀ T) *ᵥ v`, and `IsSingularValue (bidiagT m) σ_k` itself.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.HeatEquation20.MainResults

open Qatlib.Papers.HeatEquation20.MainResults

/-- **The positivity conjunct of (B10)** (arXiv:2004.06516v2, p. 28): for
`1 ≤ k ≤ m` the singular value candidate `2 cos(k π/(2m+1))` is positive,
because the angle lies in `(0, π/2)`. -/
theorem two_cos_theta_pos (m k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ m) :
    0 < 2 * Real.cos ((k : ℝ) * Real.pi / (2 * (m : ℝ) + 1)) := by
  have hden : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hk : (0 : ℝ) < (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hkm : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk2
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlt : (k : ℝ) * Real.pi / (2 * (m : ℝ) + 1) < Real.pi / 2 := by
    rw [div_lt_div_iff₀ hden two_pos]
    nlinarith
  refine mul_pos two_pos (Real.cos_pos_of_mem_Ioo ⟨?_, hlt⟩)
  have hpos : 0 < (k : ℝ) * Real.pi / (2 * (m : ℝ) + 1) :=
    div_pos (mul_pos hk hpi) hden
  linarith

/-- The angle `θ_k = kπ/(2m+1)` satisfies `sin((2m+1) θ_k) = 0`. -/
lemma theta_sin_zero (m k : ℕ) :
    Real.sin ((2 * (m : ℝ) + 1) * ((k : ℝ) * Real.pi / (2 * (m : ℝ) + 1))) = 0 := by
  have hden : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hden]
  exact Real.sin_nat_mul_pi k

/-- The product-to-sum form used at the interior indices:
`sin (x+2θ) + sin (x−2θ) = 2 cos 2θ sin x`. -/
lemma sin_add_two_add_sin_sub_two (x θ : ℝ) :
    Real.sin (x + 2 * θ) + Real.sin (x - 2 * θ) = 2 * Real.cos (2 * θ) * Real.sin x := by
  rw [Real.sin_add, Real.sin_sub]
  ring

/-- **Interior identity of (B10)** (arXiv:2004.06516v2, p. 28): with
`σ² = 4 cos²θ`, the three-term combination
`2 sin x + sin (x+2θ) + sin (x−2θ)` equals `σ² sin x`.  This is the statement
that `j ↦ sin((2j+1)θ)` is an eigenvector of the interior rows of `Tᵀ T`. -/
lemma bidiag_recurrence_identity (x θ : ℝ) :
    2 * Real.sin x + Real.sin (x + 2 * θ) + Real.sin (x - 2 * θ)
      = 4 * Real.cos θ ^ 2 * Real.sin x := by
  rw [add_assoc, sin_add_two_add_sin_sub_two, Real.cos_two_mul]
  ring

/-- **Boundary identity of (B10)** (arXiv:2004.06516v2, p. 28): if
`sin (A+2θ) = 0`, then `2 sin A + sin (A−2θ) = 4 cos²θ sin A`.  At the two
boundary indices of `Tᵀ T` this is the missing neighbour term: the vanishing
`sin((2m+1)θ_k) = 0` supplies the hypothesis at one end, and the same identity
with `A = θ_k` supplies the other end. -/
lemma bidiag_boundary_identity (A θ : ℝ) (h : Real.sin (A + 2 * θ) = 0) :
    2 * Real.sin A + Real.sin (A - 2 * θ) = 4 * Real.cos θ ^ 2 * Real.sin A := by
  have h' : Real.sin A * Real.cos (2 * θ) + Real.cos A * Real.sin (2 * θ) = 0 := by
    rw [← Real.sin_add]
    exact h
  have hexp : Real.sin (A - 2 * θ)
      = Real.sin A * Real.cos (2 * θ) - Real.cos A * Real.sin (2 * θ) := Real.sin_sub _ _
  have hc : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have h'' : Real.sin A * (2 * Real.cos θ ^ 2 - 1) + Real.cos A * Real.sin (2 * θ) = 0 := by
    rw [← hc]
    exact h'
  rw [hexp, hc]
  linear_combination -h''

end Qatlib.Papers.HeatEquation20.MainResults
