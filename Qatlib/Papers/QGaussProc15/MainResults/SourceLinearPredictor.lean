/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGaussProc15.MainResults.SourceMeasurementReadout

set_option backward.isDefEq.respectTransparency false

/-!
# QGaussProc15 c004 — the linear-predictor estimator, source Eq. (10)

Zhao--Fitzsimons--Fitzsimons, fixed arXiv:1512.03929v1 (12 Dec 2015),
page 4, Eq. (10):

`f̄_* = √(s_{k_*} s_y) / (σ_n² c_{k_*} c_y) · ⟨M⟩`.

The source takes `u = k_*`, `v = y`, `A = K + σ_n² I` and `c = σ_n²` in
the readout of c003.  (The printed text on page 4 writes `A = K − σ_n² I`,
which is inconsistent with the min-eigenvalue argument `λ_min ≥ σ_n²`
used in the same paragraph and with Eq. (4); the metadata `content` notes
the typo, and we follow the mathematically consistent `K + σ_n² I`.)

The estimator is applied to the measured expectation, so after substituting
the c003 identity the two scaling factors cancel and the estimator returns
`k_*ᵀ (K + σ_n² I)⁻¹ y`, i.e. the classical GPR linear predictor of
Eq. (4).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QGaussProc15.MainResults

/-- The source Eq. (10) estimator, applied to a measured readout
expectation `M`: `√(s_k s_y) / (σ_n² c_k c_y) · M`. -/
def linearPredictorEstimator (sk sy σn ck cy M : ℝ) : ℝ :=
  Real.sqrt (sk * sy) / (σn ^ 2 * ck * cy) * M

/-- **Fixed arXiv:1512.03929v1, page 4, Eq. (10) (c004).**  Running the
QLA readout of c003 with `u = k_*`, `v = y`, `c = σ_n²`, sparsities
`s_k, s_y` and state-preparation constants `c_k, c_y`, the estimator
`√(s_k s_y)/(σ_n² c_k c_y) · ⟨M⟩` recovers `k_*ᵀ A⁻¹ y`, the GPR linear
predictor of Eq. (4).

The orthonormal eigenbasis `μ`, nonzero eigenvalues `lam`, and positive
`σ_n, c_k, c_y, s_k, s_y` are the source's standing assumptions (Hermitian
positive-definite `K + σ_n² I`, nonzero preparation constants, sparse
vectors). -/
theorem source_linear_predictor_estimator {n : ℕ} (μ : Fin n → Fin n → ℝ)
    (γ β lam : Fin n → ℝ) (σn ck cy sk sy : ℝ)
    (horth : Orthonormal μ) (hlam : ∀ i, lam i ≠ 0)
    (hσn : 0 < σn) (hck : 0 < ck) (hcy : 0 < cy)
    (hsk : 0 < sk) (hsy : 0 < sy) :
    linearPredictorEstimator sk sy σn ck cy
        (readoutExpectation γ β lam ck cy (σn ^ 2) sk sy)
      = gprLinearPredictor μ γ β lam := by
  rw [source_measurement_expectation μ γ β lam ck cy (σn ^ 2) sk sy
    horth hlam hsk hsy]
  unfold linearPredictorEstimator
  have hsq : Real.sqrt (sk * sy) = Real.sqrt sk * Real.sqrt sy :=
    Real.sqrt_mul hsk.le sy
  rw [hsq]
  have hsk' : Real.sqrt sk ≠ 0 := (Real.sqrt_pos.mpr hsk).ne'
  have hsy' : Real.sqrt sy ≠ 0 := (Real.sqrt_pos.mpr hsy).ne'
  have hσn' : σn ^ 2 ≠ 0 := by positivity
  have hck' : ck ≠ 0 := hck.ne'
  have hcy' : cy ≠ 0 := hcy.ne'
  field_simp
  try ring

/-- **Fixed arXiv:1512.03929v1, page 4, Eq. (10) (c004), GPR form.**
The c004 estimator recovers exactly the classical GPR linear predictor
`k_*ᵀ (K + σ_n² I)⁻¹ y`; this is the same statement as
`source_linear_predictor_estimator`, written through the model definition
`gprLinearPredictor`. -/
theorem source_linear_predictor_recovers_gpr {n : ℕ} (μ : Fin n → Fin n → ℝ)
    (γ β lam : Fin n → ℝ) (σn ck cy sk sy : ℝ)
    (horth : Orthonormal μ) (hlam : ∀ i, lam i ≠ 0)
    (hσn : 0 < σn) (hck : 0 < ck) (hcy : 0 < cy)
    (hsk : 0 < sk) (hsy : 0 < sy) :
    linearPredictorEstimator sk sy σn ck cy
        (readoutExpectation γ β lam ck cy (σn ^ 2) sk sy)
      = dot (expand μ γ) (mulVec (spectralInverse μ lam) (expand μ β)) := by
  rw [source_linear_predictor_estimator μ γ β lam σn ck cy sk sy
    horth hlam hσn hck hcy hsk hsy]
  rfl

end Qatlib.Papers.QGaussProc15.MainResults
