/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HidShiftQuad09.MainResults.Defs
import Qatlib.Papers.HidShiftQuad09.MainResults.FindCloseQuadratic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HidShiftQuad09.MainResults.ShiftedLargeU3

open scoped BigOperators RealInnerProductSpace
open Qatlib.Papers.HidShiftQuad09.MainResults.Defs

theorem bent_fourierCoeff_ne_zero {n : ℕ} (f : Cube n → ZMod 2) (hb : bent f)
    (w : Cube n) : fourierCoeff f w ≠ 0 := by
  intro h
  have hw := hb w
  rw [h, abs_zero] at hw
  have hpos : 0 < (2 : ℝ) ^ (-(n : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  linarith

theorem bent_fourier_sign {n : ℕ} (f : Cube n → ZMod 2) (hb : bent f) :
    ∃ σ : Cube n → ℝ,
      (∀ w, σ w = 1 ∨ σ w = -1) ∧
      ∀ w, fourierCoeff f w = σ w * (2 : ℝ) ^ (-(n : ℝ) / 2) := by
  have hcpos : 0 < (2 : ℝ) ^ (-(n : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hcne : (2 : ℝ) ^ (-(n : ℝ) / 2) ≠ 0 := ne_of_gt hcpos
  refine ⟨fun w => fourierCoeff f w / (2 : ℝ) ^ (-(n : ℝ) / 2), ?_, ?_⟩
  · intro w
    show fourierCoeff f w / (2 : ℝ) ^ (-(n : ℝ) / 2) = 1 ∨
      fourierCoeff f w / (2 : ℝ) ^ (-(n : ℝ) / 2) = -1
    rcases (abs_eq hcpos.le).mp (hb w) with h | h
    · left; rw [h, div_self hcne]
    · right; rw [h, neg_div, div_self hcne]
  · intro w
    show fourierCoeff f w = (fourierCoeff f w / (2 : ℝ) ^ (-(n : ℝ) / 2)) *
      (2 : ℝ) ^ (-(n : ℝ) / 2)
    rw [div_mul_cancel₀ _ hcne]

theorem close_of_largeU3_input {n : ℕ} (f : Cube n → ZMod 2) (q : QuadPoly n)
    (ε : ℝ) (hcorr : 1 - 4 * ε < |corr f q.eval|) :
    disagreeFrac f q.eval < 2 * ε ∨ 1 - 2 * ε < disagreeFrac f q.eval := by
  have h := FindCloseQuadratic.abs_corr_gt_implies_close f q.eval (4 * ε) hcorr
  rcases h with h | h
  · left; linarith
  · right; linarith

theorem largeU3_findClose (n : ℕ) (ε : ℝ) (f : Cube n → ZMod 2)
    (hinv : ∃ q : QuadPoly n, 1 - 4 * ε < |corr f q.eval|) :
    ∃ q : QuadPoly n,
      1 - 4 * ε < |corr f q.eval| ∧
        (disagreeFrac f q.eval < 2 * ε ∨ 1 - 2 * ε < disagreeFrac f q.eval) := by
  obtain ⟨q, hq⟩ := hinv
  exact ⟨q, hq, close_of_largeU3_input f q ε hq⟩

theorem largeU3_step1_success
    (n : ℕ) (hn : 0 < n) (ε : ℝ) (f : Cube n → ZMod 2) (q : QuadPoly n)
    (hε0 : 0 ≤ ε)
    (hcorr : 1 - ε < |corr f q.eval|)
    {N : ℕ} (ψf ψg φ : EuclideanSpace ℝ (Fin N))
    (hψf : ‖ψf‖ = 1) (hψg : ‖ψg‖ = 1) (hφ : ‖φ‖ = 1)
    (hinner : ⟪ψf, ψg⟫ = |corr f q.eval| ^ (n / 1000))
    (hp0 : 1 / 2 ≤ ⟪ψg, φ⟫ ^ 2) :
    ∃ c : ℝ, 0 < c ∧ c * (1 - (n : ℝ) * ε) ≤ ⟪ψf, φ⟫ ^ 2 :=
  FindCloseQuadratic.source_theorem2_findCloseQuadratic n hn ε f q hε0 hcorr
    ψf ψg φ hψf hψg hφ hinner hp0

end Qatlib.Papers.HidShiftQuad09.MainResults.ShiftedLargeU3
