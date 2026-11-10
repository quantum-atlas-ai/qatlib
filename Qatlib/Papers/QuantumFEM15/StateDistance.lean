/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Real
open scoped ComplexOrder InnerProductSpace

namespace Qatlib.Papers.QuantumFEM15.StateDistance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def qleOutput (U : ℕ → E →L[ℂ] E) (A : E →L[ℂ] E) : ℕ → E → E
  | 0, ψ => U 0 ψ
  | (T + 1), ψ => U (T + 1) (A (qleOutput U A T ψ))

theorem qleOutput_norm (U : ℕ → E →L[ℂ] E)
    (hU : ∀ (i : ℕ) (x : E), ‖U i x‖ = ‖x‖)
    (A : E →L[ℂ] E) (hA : ∀ x : E, ‖A x‖ = ‖x‖) :
    ∀ (T : ℕ) (ψ : E), ‖qleOutput U A T ψ‖ = ‖ψ‖
  | 0, ψ => by simpa [qleOutput] using hU 0 ψ
  | (T + 1), ψ => by
      simp only [qleOutput]
      rw [hU, hA, qleOutput_norm U hU A hA T ψ]

theorem qleOutput_dist_le (U : ℕ → E →L[ℂ] E)
    (hU : ∀ (i : ℕ) (x : E), ‖U i x‖ = ‖x‖)
    (A B : E →L[ℂ] E) (hA : ∀ x : E, ‖A x‖ = ‖x‖)
    (hB : ∀ x : E, ‖B x‖ = ‖x‖) (δ : ℝ) (hAB : ‖A - B‖ ≤ δ) :
    ∀ (T : ℕ) (ψ : E),
      ‖qleOutput U A T ψ - qleOutput U B T ψ‖ ≤ (T : ℝ) * δ * ‖ψ‖ := by
  have hδ : 0 ≤ δ := le_trans (norm_nonneg (A - B)) hAB
  intro T
  induction T with
  | zero =>
      intro ψ
      simp [qleOutput]
  | succ T ih =>
      intro ψ
      set xA : E := qleOutput U A T ψ with hxA
      set xB : E := qleOutput U B T ψ with hxB
      have hxA_norm : ‖xA‖ = ‖ψ‖ := qleOutput_norm U hU A hA T ψ
      have hxB_norm : ‖xB‖ = ‖ψ‖ := qleOutput_norm U hU B hB T ψ
      have hsub : qleOutput U A (T + 1) ψ - qleOutput U B (T + 1) ψ
          = U (T + 1) (A xA - B xB) := by
        simp only [qleOutput, hxA, hxB]
        rw [map_sub]
      rw [hsub, hU]
      have hsplit : A xA - B xB = (A xA - B xA) + (B xA - B xB) := by abel
      rw [hsplit]
      have h1 : ‖A xA - B xA‖ ≤ δ * ‖ψ‖ := by
        have hABx : A xA - B xA = (A - B) xA := by
          rw [ContinuousLinearMap.sub_apply]
        rw [hABx]
        calc ‖(A - B) xA‖ ≤ ‖A - B‖ * ‖xA‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ δ * ‖ψ‖ := by
              rw [hxA_norm]
              exact mul_le_mul hAB (le_refl _) (norm_nonneg _) hδ
      have h2 : ‖B xA - B xB‖ ≤ (T : ℝ) * δ * ‖ψ‖ := by
        have hBsub : B xA - B xB = B (xA - xB) := by rw [map_sub]
        rw [hBsub, hB]
        exact ih ψ
      calc ‖(A xA - B xA) + (B xA - B xB)‖
          ≤ ‖A xA - B xA‖ + ‖B xA - B xB‖ := norm_add_le _ _
        _ ≤ δ * ‖ψ‖ + (T : ℝ) * δ * ‖ψ‖ := add_le_add h1 h2
        _ = ((T + 1 : ℕ) : ℝ) * δ * ‖ψ‖ := by push_cast; ring

theorem oracle_distance_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ φ ψ' φ' : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hoverlap : inner ℂ ψ φ = (Real.sqrt (1 - ε) : ℂ))
    (hcompl : ‖φ' - ψ'‖ = ‖ψ - φ‖) :
    Real.sqrt (‖ψ - φ‖ ^ 2 + ‖φ' - ψ'‖ ^ 2) ≤ 2 * Real.sqrt ε := by
  have hsqrt1 : 0 ≤ Real.sqrt (1 - ε) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (1 - ε) ^ 2 = 1 - ε := Real.sq_sqrt (by linarith)
  have hle1 : Real.sqrt (1 - ε) ≤ 1 := by nlinarith [hsq, hsqrt1, hε0]

  have hnorm2 : ‖ψ - φ‖ ^ 2 = 2 - 2 * Real.sqrt (1 - ε) := by
    rw [norm_sub_sq (𝕜 := ℂ), hψ, hφ, hoverlap]
    simp [Complex.ofReal_re]
    ring
  have h2eps : ‖ψ - φ‖ ^ 2 ≤ 2 * ε := by
    rw [hnorm2]; nlinarith [hsq, hsqrt1, hle1]
  rw [hcompl]
  have hsum : ‖ψ - φ‖ ^ 2 + ‖ψ - φ‖ ^ 2 = 2 * ‖ψ - φ‖ ^ 2 := by ring
  rw [hsum]
  have h4 : 2 * ‖ψ - φ‖ ^ 2 ≤ 4 * ε := by nlinarith [h2eps]
  calc Real.sqrt (2 * ‖ψ - φ‖ ^ 2) ≤ Real.sqrt (4 * ε) := Real.sqrt_le_sqrt h4
    _ = 2 * Real.sqrt ε := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
        norm_num

theorem qle_black_box_lower_bound (U : ℕ → E →L[ℂ] E)
    (hU : ∀ (i : ℕ) (x : E), ‖U i x‖ = ‖x‖)
    (A B : E →L[ℂ] E) (hA : ∀ x : E, ‖A x‖ = ‖x‖)
    (hB : ∀ x : E, ‖B x‖ = ‖x‖) (ε : ℝ) (hε : 0 < ε)
    (hAB : ‖A - B‖ ≤ 2 * Real.sqrt ε)
    (ψ : E) (hψ : ‖ψ‖ = 1) (T : ℕ)
    (hdist : (1 / 3 : ℝ) ≤ ‖qleOutput U A T ψ - qleOutput U B T ψ‖) :
    (1 / (6 * Real.sqrt ε) : ℝ) ≤ (T : ℝ) := by
  have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hmain := qleOutput_dist_le U hU A B hA hB (2 * Real.sqrt ε) hAB T ψ
  have h13 : (1 / 3 : ℝ) ≤ (T : ℝ) * (2 * Real.sqrt ε) := by
    calc (1 / 3 : ℝ) ≤ ‖qleOutput U A T ψ - qleOutput U B T ψ‖ := hdist
      _ ≤ (T : ℝ) * (2 * Real.sqrt ε) * ‖ψ‖ := hmain
      _ = (T : ℝ) * (2 * Real.sqrt ε) := by rw [hψ, mul_one]
  have h6 : (0 : ℝ) < 6 * Real.sqrt ε := by positivity
  rw [div_le_iff₀ h6]
  have hmul : (T : ℝ) * (6 * Real.sqrt ε) = 3 * ((T : ℝ) * (2 * Real.sqrt ε)) := by
    ring
  rw [hmul]
  nlinarith [h13]

end Qatlib.Papers.QuantumFEM15.StateDistance
