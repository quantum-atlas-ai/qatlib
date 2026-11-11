/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGaussProc15.MainResults.SourceMeasurementReadout

set_option backward.isDefEq.respectTransparency false

/-!
# QGaussProc15 c005 — the variance estimator, source Eq. (11)

Zhao--Fitzsimons--Fitzsimons, fixed arXiv:1512.03929v1 (12 Dec 2015),
page 4, Eq. (11):

`𝕍[f_*] = k(x_*,x_*) − s_{k_*} / (σ_n² c_{k_*}²) · ⟨M⟩`.

The source runs the same readout as for the linear predictor but takes
`v = k_*` as well as `u = k_*` (so both branches use the coordinates `β`
of `k_*` in the eigenbasis of `A = K + σ_n² I`), with `c = σ_n²`.  After
substituting the c003 identity the estimator returns
`k(x_*,x_*) − k_*ᵀ (K + σ_n² I)⁻¹ k_*`, i.e. the predictive variance of
Eq. (5).  `M` is measured on several independent runs; the estimator below
acts on the resulting expectation.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QGaussProc15.MainResults

/-- The source Eq. (11) variance estimator, applied to a measured readout
expectation `M`: `k(x_*,x_*) − s_k/(σ_n² c_k²) · M`. -/
def varianceEstimator (kxx sk σn ck M : ℝ) : ℝ :=
  kxx - sk / (σn ^ 2 * ck ^ 2) * M

/-- `(√s)⁻¹ · (√s)⁻¹ = s⁻¹` for `s ≥ 0`: used to cancel the two sparsity
normalisations of the c003 readout against the `s_k` factor of the Eq. (11)
estimator. -/
theorem sqrt_inv_mul_sqrt_inv {s : ℝ} (hs : 0 ≤ s) :
    (Real.sqrt s)⁻¹ * (Real.sqrt s)⁻¹ = s⁻¹ := by
  rw [← mul_inv, ← Real.sqrt_mul hs, show s * s = s ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_nonneg hs]

/-- **Fixed arXiv:1512.03929v1, page 4, Eq. (11) (c005).**  Running the
readout of c003 with `u = v = k_*`, `c = σ_n²`, sparsity `s_k` and
preparation constant `c_k`, the estimator
`k(x_*,x_*) − s_k/(σ_n² c_k²) · ⟨M⟩` recovers the GPR predictive variance
`k(x_*,x_*) − k_*ᵀ A⁻¹ k_*` of Eq. (5).

The orthonormal eigenbasis `μ`, nonzero eigenvalues `lam`, and positive
`σ_n, c_k, s_k` are the source's standing assumptions. -/
theorem source_variance_estimator {n : ℕ} (μ : Fin n → Fin n → ℝ)
    (β lam : Fin n → ℝ) (kxx σn ck sk : ℝ)
    (horth : Orthonormal μ) (hlam : ∀ i, lam i ≠ 0)
    (hσn : 0 < σn) (hck : 0 < ck) (hsk : 0 < sk) :
    varianceEstimator kxx sk σn ck
        (readoutExpectation β β lam ck ck (σn ^ 2) sk sk)
      = gprPredictiveVariance kxx μ β lam := by
  unfold varianceEstimator gprPredictiveVariance
  rw [readoutExpectation_eq β β lam ck ck (σn ^ 2) sk sk hsk hsk,
    dot_spectralInverse_expand horth β β]
  -- Replace `√sk` by a variable `t` and use `t * t = sk` to cancel the
  -- two sparsity normalisations against the `s_k` prefactor.
  set t := Real.sqrt sk with ht
  have htne : t ≠ 0 := by rw [ht]; exact (Real.sqrt_pos.mpr hsk).ne'
  have htt : t * t = sk := by rw [ht]; exact Real.mul_self_sqrt hsk.le
  rw [← htt]
  have hσn' : σn ^ 2 ≠ 0 := by positivity
  have hck' : ck ≠ 0 := hck.ne'
  field_simp
  try ring

/-- **Fixed arXiv:1512.03929v1, page 4, Eq. (11) (c005), Eq. (5) form.**
The c005 estimator recovers exactly the classical GPR predictive variance;
this is the same statement as `source_variance_estimator`, written through
the model definition `gprPredictiveVariance`. -/
theorem source_variance_recovers_gpr {n : ℕ} (μ : Fin n → Fin n → ℝ)
    (β lam : Fin n → ℝ) (kxx σn ck sk : ℝ)
    (horth : Orthonormal μ) (hlam : ∀ i, lam i ≠ 0)
    (hσn : 0 < σn) (hck : 0 < ck) (hsk : 0 < sk) :
    varianceEstimator kxx sk σn ck
        (readoutExpectation β β lam ck ck (σn ^ 2) sk sk)
      = kxx - dot (expand μ β) (mulVec (spectralInverse μ lam) (expand μ β)) := by
  rw [source_variance_estimator μ β lam kxx σn ck sk horth hlam hσn hck hsk]
  rfl

end Qatlib.Papers.QGaussProc15.MainResults
