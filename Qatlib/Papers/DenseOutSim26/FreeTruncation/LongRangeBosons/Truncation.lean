/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DenseOutSim26.FreeTruncation.Core.DenseOutput

/-!
# Long-range Bose-Hubbard systems: truncation radius
(arXiv:2609.40094v1, p.17, Theorem 9)

Under the long-range assumption `α > 3D + 1` with `β = ⌊α − 3D − 1⌋`, and for
truncation radii beyond the Lieb-Robinson light cone `R ≥ v_LR T`, the
dense-output truncation error obeys Eq. (53)

`|J_H(O) − J_{H_R}(O)| ≤ O(T²/R^β)`,

and Eq. (54) gives the sufficient radius
`R_ε(T) = Θ(v_LR T + (T²/ε)^{1/β})`.

This file records both statements.  The radius choice is proved from the error
bound as in Theorem 3; the `O(T²/R^β)` estimate itself is the paper's
Lieb-Robinson-based derivation and is stated with its hypotheses.
-/

namespace Qatlib.Papers.DenseOutSim26.FreeTruncation.LongRangeBosons

open MeasureTheory intervalIntegral
open Qatlib.Papers.DenseOutSim26.FreeTruncation.Core

set_option autoImplicit false

/-- The sufficient radius of Eq. (54):
`R_ε(T) = v_LR T + (T²/ε)^{1/β}` (up to the `Θ` constant). -/
noncomputable def boseHubbardRadius (vLR T ε β : ℝ) : ℝ :=
  vLR * T + (T ^ 2 / ε) ^ (1 / β)

/-- **Theorem 9, Eq. (53) (integration step)**: for `R ≥ v_LR T` and
`β = ⌊α − 3D − 1⌋ > 0`, the pointwise Lieb-Robinson estimate
`‖⟨ψ₀|O(t) − O_R(t)|ψ₀⟩‖ ≤ C‖O‖ t R^{−β}` (Eq. (52)) integrates to the
dense-output bound `∫₀^T ≤ C T²/R^β`. -/
theorem theorem9_truncation_error
    {f : ℝ → ℝ} {C T β R : ℝ}
    (hT : 0 ≤ T) (hR : 0 < R) (hC : 0 ≤ C)
    (hInt : IntervalIntegrable f volume (0 : ℝ) T)
    (hpt : ∀ t ∈ Set.Icc (0 : ℝ) T, f t ≤ C * t / R ^ β) :
    ∫ t in (0 : ℝ)..T, f t ≤ C * T ^ 2 / R ^ β :=
  integral_div_rpow_bound hT hC hR hInt hpt

/-- **Theorem 9, Eq. (53)**: the dense-output truncation error of long-range
Bose-Hubbard systems is `O(T²/R^β)`, obtained from the integrated pointwise
estimate together with `|J_H − J_{H_R}| ≤ ∫₀^T ‖O(t) − O_R(t)‖ dt`. -/
theorem theorem9_dense_output_error
    {f : ℝ → ℝ} {JH JHR C T β R : ℝ}
    (hT : 0 ≤ T) (hR : 0 < R) (hC : 0 ≤ C)
    (hInt : IntervalIntegrable f volume (0 : ℝ) T)
    (hpt : ∀ t ∈ Set.Icc (0 : ℝ) T, f t ≤ C * t / R ^ β)
    (hgap : |JH - JHR| ≤ ∫ t in (0 : ℝ)..T, f t) :
    |JH - JHR| ≤ C * T ^ 2 / R ^ β :=
  le_trans hgap (theorem9_truncation_error hT hR hC hInt hpt)

/-- **Theorem 9, Eq. (54) (sufficient radius)**: if the error is bounded by
`C T²/R^β` and `R ≥ (C T²/ε)^{1/β}`, then the error is at most `ε`. -/
theorem theorem9_sufficient_radius
    {JH JHR C T ε β R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hβ : 0 < β) (hC : 0 < C)
    (herr : |JH - JHR| ≤ C * T ^ 2 / R ^ β)
    (hRbig : (C * T ^ 2 / ε) ^ (1 / β) ≤ R) :
    |JH - JHR| ≤ ε := by
  have hbase0 : 0 ≤ C * T ^ 2 / ε :=
    div_nonneg (mul_nonneg hC.le (sq_nonneg T)) hε.le
  have hpow : C * T ^ 2 / ε ≤ R ^ β := by
    have hmono : ((C * T ^ 2 / ε) ^ (1 / β)) ^ β ≤ R ^ β :=
      Real.rpow_le_rpow (Real.rpow_nonneg hbase0 _) hRbig hβ.le
    rwa [← Real.rpow_mul hbase0, one_div, inv_mul_cancel₀ hβ.ne', Real.rpow_one] at hmono
  have hRq : (0 : ℝ) < R ^ β := Real.rpow_pos_of_pos hR _
  have hle : C * T ^ 2 / R ^ β ≤ ε := by
    rw [div_le_iff₀ hRq]
    have h2 := (div_le_iff₀ hε).mp hpow
    nlinarith [h2]
  linarith [herr]

/-- **Theorem 9, Eq. (54) (form of the radius)**: the paper's radius is the sum
of the light-cone term `v_LR T` and the accuracy term `(T²/ε)^{1/β}`. -/
theorem theorem9_radius_form (vLR T ε β : ℝ) :
    boseHubbardRadius vLR T ε β = vLR * T + (T ^ 2 / ε) ^ (1 / β) := rfl

end Qatlib.Papers.DenseOutSim26.FreeTruncation.LongRangeBosons
