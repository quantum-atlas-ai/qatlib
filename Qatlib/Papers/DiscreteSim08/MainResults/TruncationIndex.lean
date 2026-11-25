/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DiscreteSim08.MainResults.Budget
public import Qatlib.Papers.DiscreteSim08.MainResults.Truncation
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Truncation order as a function of the target error

Set the truncation order to the floor of twice the logarithmic ratio in Eq. (25).
The first discarded order is strictly greater than that ratio. A Stirling lower
bound on its factorial controls the finite Poisson comparison term by the target
reciprocal error, and the existing budget consumes the same integer.
-/

set_option autoImplicit false

open Qatlib.Papers.DiscreteSim08.MainResults

namespace Qatlib.Papers.DiscreteSim08.MainResults

/-- The finite tail comparison in Eqs. (24)–(25) admits a truncation
order within twice the logarithmic ratio for every `X > exp 1`. -/
theorem truncation_index_bound (X : ℝ) (hX : Real.exp 1 < X) :
    ∃ k : ℕ, (k : ℝ) ≤ 2 * Real.log X / Real.log (Real.log X) ∧
      2 * poissonTerm (1 / 8) (k + 1) ≤ 1 / X := by
  let L := Real.log X
  let W := Real.log L
  have hXpos := (Real.exp_pos (1 : ℝ)).trans hX
  have hL : 1 < L := by
    have h := Real.log_lt_log (Real.exp_pos (1 : ℝ)) hX
    rwa [Real.log_exp] at h
  have hLp : 0 < L := zero_lt_one.trans hL
  have hWp : 0 < W := Real.log_pos hL
  let k := ⌊2 * L / W⌋₊
  let j : ℕ := k + 1
  have hj : 2 * L / W < (j : ℝ) := by
    simpa only [j, k, Nat.cast_succ] using Nat.lt_floor_add_one (2 * L / W)
  have hjp : 0 < (j : ℝ) := by dsimp [j]; positivity
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hlog : Real.log (2 * L / W) = W - Real.log (W / 2) := by
    rw [show 2 * L / W = L / (W / 2) by ring, Real.log_div hLp.ne' (by positivity)]
  have hscale : W / 2 ≤ Real.log (j : ℝ) - 1 := by
    have hl := Real.log_le_log (show 0 < 2 * L / W by positivity) hj.le
    rw [hlog] at hl
    linarith [Real.log_le_sub_one_of_pos (show 0 < W / 2 by positivity)]
  have hLfac : L ≤ (j : ℝ) * (Real.log (j : ℝ) - 1) := calc
    L ≤ (j : ℝ) * (W / 2) := by
      have h := (div_lt_iff₀ hWp).mp hj
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale hjp.le
  have hst := Stirling.le_log_factorial_stirling (show j ≠ 0 by dsimp [j]; omega)
  have hlogfac : L ≤ Real.log (j.factorial : ℝ) := by
    have hlogj := Real.log_nonneg hj1
    have hlogpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  have hXfac : X ≤ (j.factorial : ℝ) :=
    (Real.log_le_log_iff hXpos (by positivity)).mp hlogfac
  have hpow : ((1 : ℝ) / 8) ^ j ≤ 1 / 8 := by
    calc
      _ ≤ ((1 : ℝ) / 8) ^ (1 : ℕ) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.succ_le_succ (Nat.zero_le k))
      _ = _ := pow_one _
  refine ⟨k, Nat.floor_le (by positivity), ?_⟩
  change 2 * poissonTerm (1 / 8) j ≤ 1 / X
  calc
    _ = (2 * ((1 : ℝ) / 8) ^ j) / (j.factorial : ℝ) := by rw [poissonTerm, mul_div_assoc]
    _ ≤ 1 / (j.factorial : ℝ) := div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ 1 / X := one_div_le_one_div_of_le hXpos hXfac

/-- The selected cutoff gives the reciprocal-error binomial tail bound and
the scalar query budget under the segment mean hypothesis. -/
theorem truncation_query_budget (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hX : Real.exp 1 < T / ε) (m : ℕ) (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hμ : (m : ℝ) * B ≤ 1 / 8) :
    ∃ k : ℕ, binomTail m k B ≤ ε / T ∧
      8 * T * k / ε ≤
        16 * (T * Real.log (T / ε)) / (ε * Real.log (Real.log (T / ε))) := by
  obtain ⟨k, hcut, htail⟩ := truncation_index_bound (T / ε) hX
  have heq : 1 / (T / ε) = ε / T := by rw [one_div, inv_div]
  have hlog : 1 < Real.log (T / ε) := by
    have h := Real.log_lt_log (Real.exp_pos (1 : ℝ)) hX
    rwa [Real.log_exp] at h
  exact ⟨k, binomTail_le_eps m k B (ε / T) hB0 hB1 hμ (heq ▸ htail),
    theorem1_query_budget T ε k hT hε hlog hcut⟩

/-- Equation (23)'s probability weight of a one in one of the control qubits. -/
noncomputable def segmentControlProb (θ : ℝ) : ℝ :=
  Real.sin (θ / 2) / controlledSimulationNorm θ

/-- For a nonnegative angle and a segment with total angle at most one quarter,
the exact ancilla probability in Eq. (23) has mean at most one eighth. -/
theorem segment_control_prob_bound (m : ℕ) (hm : 0 < m) (θ : ℝ) (hθ : 0 ≤ θ)
    (hsegment : (m : ℝ) * θ ≤ 1 / 4) :
    0 ≤ segmentControlProb θ ∧ segmentControlProb θ ≤ 1 ∧
      (m : ℝ) * segmentControlProb θ ≤ 1 / 8 := by
  let x := θ / 2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hθle : θ ≤ (m : ℝ) * θ := by simpa using mul_le_mul_of_nonneg_right hm1 hθ
  have hxle : x ≤ 1 / 8 := by dsimp [x]; linarith
  have hsin0 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx
    (by linarith [Real.pi_gt_three])
  have hsin : Real.sin x ≤ x := Real.sin_le hx
  have hcos : 1 - x ≤ Real.cos x := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := x), mul_nonneg hx (show 0 ≤ 2 - x by linarith)]
  have hden : 0 < Real.cos x + Real.sin x := by linarith
  have hB0 : 0 ≤ segmentControlProb θ := div_nonneg hsin0 hden.le
  have hB : segmentControlProb θ ≤ x := by
    change Real.sin x / (Real.cos x + Real.sin x) ≤ x
    apply (div_le_iff₀ hden).2
    have h1 := mul_le_mul_of_nonneg_right hsin (show 0 ≤ 1 - x by linarith)
    have h2 := mul_le_mul_of_nonneg_left hcos hx
    nlinarith
  refine ⟨hB0, hB.trans (by linarith), ?_⟩
  have h := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg m : 0 ≤ (m : ℝ))
  dsimp [x] at h
  linarith

/-- The small-angle segment of §II.C admits a single truncation index meeting
both the finite fidelity target and the explicit scalar query budget. -/
theorem segment_truncation_query_budget (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hX : Real.exp 1 < T / ε) (m : ℕ) (hm : 0 < m) (θ : ℝ) (hθ : 0 ≤ θ)
    (hsegment : (m : ℝ) * θ ≤ 1 / 4) :
    ∃ k : ℕ, binomTail m k (segmentControlProb θ) ≤ ε / T ∧
      8 * T * k / ε ≤
        16 * (T * Real.log (T / ε)) / (ε * Real.log (Real.log (T / ε))) := by
  obtain ⟨hB0, hB1, hμ⟩ := segment_control_prob_bound m hm θ hθ hsegment
  exact truncation_query_budget T ε hT hε hX m (segmentControlProb θ) hB0 hB1 hμ

end Qatlib.Papers.DiscreteSim08.MainResults
