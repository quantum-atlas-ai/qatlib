/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAnnealing08.MainResults.ZenoRandomization

@[expose] public section

/-!
# Scalar attenuation in quantum simulated annealing

The spectral gap and repetition constraints bound the off-phase scalar in the
randomized step on page 3 of arXiv:0804.1571v1.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QAnnealing08.MainResults

open Qatlib.Papers.QAnnealing08.MainResults.ZenoRandomization

/-- The source gap and repetition conditions bound both signs of the off-phase
amplitude by `μ/2`, with strict attenuation whenever `μ > 0`. -/
theorem zeno_phase_step (μ ν' φ δ : ℝ) (k s p : ℕ) (hμ : 0 ≤ μ)
    (hφ : |φ| ≤ Real.pi / 2) (hδ0 : 0 < δ) (hδ : Real.sqrt (2 * δ) ≤ |φ|)
    (hν : ν' ≤ Real.sqrt (2 * (k + 1)) * μ)
    (hp : 8 * Real.pi / Real.sqrt (2 * δ) < (2 : ℝ) ^ p)
    (hs : 8 * (k + 1) ≤ 4 ^ s) :
    ν' * ‖(randomExpAvg (2 ^ p) (2 * φ)) ^ s‖ ≤ μ / 2 ∧
      (0 < μ → ν' * ‖(randomExpAvg (2 ^ p) (2 * φ)) ^ s‖ < μ / 2) := by
  have hN : 0 < (2 : ℕ) ^ p := by positivity
  have hsqrt : 0 < Real.sqrt (2 * δ) := by positivity
  have hφpos : 0 < |φ| := hsqrt.trans_le hδ
  have hsinPos :
      0 < Real.sin (|φ|) := Real.sin_pos_of_pos_of_lt_pi hφpos (by linarith [Real.pi_pos])
  have hsinAbs : |Real.sin φ| = |Real.sin (|φ|)| := by
    rcases le_or_gt 0 φ with hpos | hneg
    · rw [abs_of_nonneg hpos]
    · rw [abs_of_neg hneg, Real.sin_neg, abs_neg]
  have hsin : Real.sin (2 * φ / 2) ≠ 0 := by
    rw [show 2 * φ / 2 = φ by ring, ← abs_pos, hsinAbs]
    exact abs_pos.mpr hsinPos.ne'
  have hcoeff := norm_randomExpAvg_pow_le (2 ^ p) hN (2 * φ) s hsin
  rw [show 2 * φ / 2 = φ by ring, hsinAbs] at hcoeff
  have hgap := decoherenceFactor_le_sqrt_delta (2 ^ p) hN |φ| δ hφpos hφ hδ0 hδ
  have hcount := (div_lt_iff₀ hsqrt).mp hp
  have hhalf : 1 / (((2 ^ p : ℕ) : ℝ) * |Real.sin (|φ|)|) < 1 / 2 := by
    apply hgap.trans_lt
    push_cast
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith [Real.pi_pos]
  have hs' : s ≠ 0 := by
    rintro rfl
    simp at hs
    omega
  have hstrict := hcoeff.trans_lt (pow_lt_pow_left₀ hhalf (by positivity) hs')
  have hupper := pow_half_le_sqrt_inv hs
  have hscale : 0 < Real.sqrt (2 * ((k : ℝ) + 1)) := by positivity
  have hcancel : Real.sqrt (2 * ((k : ℝ) + 1)) * μ *
      (1 / (2 * Real.sqrt (2 * ((k : ℝ) + 1)))) = μ / 2 := by
    field_simp
  have hbound := mul_le_mul_of_nonneg_right hν
    (norm_nonneg ((randomExpAvg (2 ^ p) (2 * φ)) ^ s))
  constructor
  · exact hbound.trans ((mul_le_mul_of_nonneg_left (hstrict.le.trans hupper)
      (mul_nonneg hscale.le hμ)).trans_eq hcancel)
  · intro hμpos
    exact hbound.trans_lt ((mul_lt_mul_of_pos_left (hstrict.trans_le hupper)
      (mul_pos hscale hμpos)).trans_eq hcancel)

end Qatlib.Papers.QAnnealing08.MainResults
