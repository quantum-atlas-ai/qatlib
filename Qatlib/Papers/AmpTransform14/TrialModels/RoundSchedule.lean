/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AmpTransform14.TrialModels
public import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedProgression

@[expose] public section

/-!
# The Grover round count against the work factor

`Qatlib.Concepts.AmpTransform.NoiseEnvelope.aqAngle` is `arcsin (sqrt (M/N))` and `aqRounds` is
`floor (pi / (4 * aqAngle N M))`, so the abstract angle hypothesis of
`Qatlib.Papers.AmpTransform14.TrialModels.groverIterations_le_workFactor` is discharged at the
prescribed round count. Under `M <= N` the square root is at most one, which supplies the
domain condition of `Real.sin_arcsin`, and `M > 0` makes the angle positive. This links the
scalar work-factor model `sqrt(N/M)` of [Cornwell2014], Chapter 2, Section 2.8, printed p. 26, to
the round count actually used by the amplified word.

## Main statements

* `aqRounds_le_workFactor`: the prescribed round count is at most `pi / (4 * sqrt (M/N))`.
* `one_le_aqRounds`: under positive half density the prescribed round count is at least one.

## References

* [Cornwell, 2014][Cornwell2014], Chapter 2, Section 2.8, printed p. 26,
  [arXiv:1406.0190](https://arxiv.org/abs/1406.0190)
-/

set_option autoImplicit false

namespace Qatlib.Papers.AmpTransform14.TrialModels

open Qatlib.Concepts.AmpTransform.NoiseEnvelope

open scoped BigOperators

/-- For `0 < M <= N` and `0 < N`, the prescribed Grover round count `aqRounds N M` is at most
the amplified work factor `pi / (4 * sqrt (M/N))` of [Cornwell2014], Chapter 2, Section 2.8. -/
theorem aqRounds_le_workFactor (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hMN : M ≤ N) :
    ((aqRounds N M : ℕ) : ℝ) ≤ Real.pi / (4 * Real.sqrt ((M : ℝ) / (N : ℝ))) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMN' : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
  have hp0 : 0 < (M : ℝ) / (N : ℝ) := div_pos hMR hNR
  have hp1 : (M : ℝ) / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNR]
    exact hMN'
  have hs1 : Real.sqrt ((M : ℝ) / (N : ℝ)) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hp1
  have hsin : Real.sin (aqAngle N M) = Real.sqrt ((M : ℝ) / (N : ℝ)) := by
    rw [aqAngle, Real.sin_arcsin (by linarith [Real.sqrt_nonneg ((M : ℝ) / (N : ℝ))]) hs1]
  have hθ : 0 < aqAngle N M := Real.arcsin_pos.mpr (Real.sqrt_pos_of_pos hp0)
  simpa only [aqRounds] using
    Qatlib.Papers.AmpTransform14.TrialModels.groverIterations_le_workFactor hθ hsin hMR hNR

/-- Under positive half density `2 * M <= N` with `0 < M`, the prescribed round count is at
least one: the angle is at most `pi/4`, so its reciprocal ratio already reaches one. This is the
round count of the amplified word actually performing at least one Grover iteration. -/
theorem one_le_aqRounds (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hMN : 2 * M ≤ N) :
    1 ≤ aqRounds N M := by
  obtain ⟨hθ, hquarter, -⟩ := aq_angle_properties N M hN hM hMN
  have hfour : 0 < 4 * aqAngle N M := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hratio : 1 ≤ Real.pi / (4 * aqAngle N M) := by
    rw [le_div_iff₀ hfour]
    nlinarith
  unfold aqRounds
  exact Nat.le_floor (by exact_mod_cast hratio)

end Qatlib.Papers.AmpTransform14.TrialModels
