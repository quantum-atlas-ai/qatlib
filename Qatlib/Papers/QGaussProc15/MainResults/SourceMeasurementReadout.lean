/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGaussProc15.MainResults.SourceReadoutModel

set_option backward.isDefEq.respectTransparency false

/-!
# QGaussProc15 c003 — the measurement expectation `uᵀ A⁻¹ v`

Zhao--Fitzsimons--Fitzsimons, fixed arXiv:1512.03929v1 (12 Dec 2015),
claim c003, page 4: "The measurement result is then a Bernoulli random
variable with expectation value `c s_u^{-1/2} s_v^{-1/2} c_u c_v uᵀ A⁻¹ v`."

The source prepares two sparse vectors `u` and `v` as superpositions
(page 3), runs the QLA conditioned on the branch bit (step 4, pages 3--4),
and measures `M = X_A I_B |1><1|_C |1><1|_D`.  The post-selected branch
amplitudes are `(c_u/√s_u) γ_i` and `(c_v c/√s_v) β_i/λ_i`, where `γ` and
`β` are the coordinates of `u` and `v` in the eigenbasis of `A`.  The
expectation of `X_A` on the two branches is the paper's expression
`∑ i, (1/4) [(a_i + b_i)² − (a_i − b_i)²]` (page 4); `readoutExpectation`
is exactly that expression, and `source_measurement_expectation` evaluates
it to the claimed closed form.  This is the only measurement used by the
GPR estimators of Eqs. (10)--(11).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QGaussProc15.MainResults

/-- **Fixed arXiv:1512.03929v1, page 4 (c003).**  The readout expectation
of `X_A ⊗ I_B ⊗ |1><1|_C ⊗ |1><1|_D` on the post-selected state equals
`c · s_u^{-1/2} · s_v^{-1/2} · c_u · c_v · uᵀ A⁻¹ v`, with `u` and `v` the
eigenbasis expansions `∑ γ_i μ_i` and `∑ β_i μ_i`, and `A⁻¹` the spectral
inverse of `A = ∑ lam_i μ_i μ_iᵀ`.

The source describes the outcome as a Bernoulli variable; its expectation
is this operator expectation (a value in `[-1,1]` before rescaling).  The
positive sparsities `s_u, s_v` and nonzero eigenvalues are the source's
standing assumptions: the vectors are `s_u`- and `s_v`-sparse and `A` is
invertible. -/
theorem source_measurement_expectation {n : ℕ} (μ : Fin n → Fin n → ℝ)
    (γ β lam : Fin n → ℝ) (cu cv c su sv : ℝ)
    (horth : Orthonormal μ) (hlam : ∀ i, lam i ≠ 0)
    (hsu : 0 < su) (hsv : 0 < sv) :
    readoutExpectation γ β lam cu cv c su sv
      = c * (Real.sqrt su)⁻¹ * (Real.sqrt sv)⁻¹ * cu * cv *
          gprLinearPredictor μ γ β lam := by
  rw [readoutExpectation_eq γ β lam cu cv c su sv hsu hsv,
    ← dot_spectralInverse_expand horth γ β]
  rfl

end Qatlib.Papers.QGaussProc15.MainResults
