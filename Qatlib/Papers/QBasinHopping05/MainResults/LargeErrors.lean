/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.QBasinHopping05.MainResults

def orbit {E : Type*} (u : ℕ → E → E) : ℕ → E → E
  | 0, x => x
  | n + 1, x => u n (orbit u n x)

def gbsGradientEstimateCount (r L : ℕ) : ℕ := (2 * r + 1) * L

theorem orbit_norm_sub_le {E : Type*} [NormedAddCommGroup E]
    (f g : ℕ → E → E) (ε : ℝ)
    (hn : ∀ i x y, ‖f i x - f i y‖ ≤ ‖x - y‖)
    (hfg : ∀ i x, ‖f i x - g i x‖ ≤ ε) :
    ∀ (N : ℕ) (ψ : E), ‖orbit f N ψ - orbit g N ψ‖ ≤ (N : ℝ) * ε := by
  intro N
  induction N with
  | zero =>
      intro ψ
      simp [orbit]
  | succ n ih =>
      intro ψ
      have hrec : ‖orbit f n ψ - orbit g n ψ‖ ≤ (n : ℝ) * ε := ih ψ
      have hlip : ‖f n (orbit f n ψ) - f n (orbit g n ψ)‖
          ≤ ‖orbit f n ψ - orbit g n ψ‖ := hn n _ _
      have hstep : ‖f n (orbit g n ψ) - g n (orbit g n ψ)‖ ≤ ε := hfg n _
      have hsplit : ‖f n (orbit f n ψ) - g n (orbit g n ψ)‖
          ≤ ‖f n (orbit f n ψ) - f n (orbit g n ψ)‖
            + ‖f n (orbit g n ψ) - g n (orbit g n ψ)‖ := by
        have h := norm_add_le (f n (orbit f n ψ) - f n (orbit g n ψ))
          (f n (orbit g n ψ) - g n (orbit g n ψ))
        have heq : (f n (orbit f n ψ) - f n (orbit g n ψ))
            + (f n (orbit g n ψ) - g n (orbit g n ψ))
            = f n (orbit f n ψ) - g n (orbit g n ψ) := by abel
        rw [heq] at h
        exact h
      have hmain : ‖f n (orbit f n ψ) - g n (orbit g n ψ)‖ ≤ (n : ℝ) * ε + ε := by
        linarith
      calc ‖orbit f (n + 1) ψ - orbit g (n + 1) ψ‖
          = ‖f n (orbit f n ψ) - g n (orbit g n ψ)‖ := by simp [orbit]
        _ ≤ (n : ℝ) * ε + ε := hmain
        _ = ((n + 1 : ℕ) : ℝ) * ε := by push_cast; ring

theorem orbit_norm_sub_lt {E : Type*} [NormedAddCommGroup E]
    (f g : ℕ → E → E) (ε : ℝ)
    (hn : ∀ i x y, ‖f i x - f i y‖ ≤ ‖x - y‖)
    (hfg : ∀ i x, ‖f i x - g i x‖ < ε) :
    ∀ (N : ℕ), 0 < N → ∀ ψ : E,
      ‖orbit f N ψ - orbit g N ψ‖ < (N : ℝ) * ε := by
  intro N
  induction N with
  | zero => intro h; exact absurd h (Nat.lt_irrefl 0)
  | succ n _ih =>
      intro _ ψ
      have hrec : ‖orbit f n ψ - orbit g n ψ‖ ≤ (n : ℝ) * ε :=
        orbit_norm_sub_le f g ε hn (fun i x => (hfg i x).le) n ψ
      have hstep : ‖f n (orbit g n ψ) - g n (orbit g n ψ)‖ < ε := hfg n _
      have hlip := hn n (orbit f n ψ) (orbit g n ψ)
      have hsplit : ‖f n (orbit f n ψ) - g n (orbit g n ψ)‖
          ≤ ‖f n (orbit f n ψ) - f n (orbit g n ψ)‖
            + ‖f n (orbit g n ψ) - g n (orbit g n ψ)‖ := by
        have h := norm_add_le (f n (orbit f n ψ) - f n (orbit g n ψ))
          (f n (orbit g n ψ) - g n (orbit g n ψ))
        have heq : (f n (orbit f n ψ) - f n (orbit g n ψ))
            + (f n (orbit g n ψ) - g n (orbit g n ψ))
            = f n (orbit f n ψ) - g n (orbit g n ψ) := by abel
        rw [heq] at h
        exact h
      calc ‖orbit f (n + 1) ψ - orbit g (n + 1) ψ‖
          = ‖f n (orbit f n ψ) - g n (orbit g n ψ)‖ := by simp [orbit]
        _ ≤ ‖f n (orbit f n ψ) - f n (orbit g n ψ)‖
              + ‖f n (orbit g n ψ) - g n (orbit g n ψ)‖ := hsplit
        _ < (n : ℝ) * ε + ε := by linarith
        _ = ((n + 1 : ℕ) : ℝ) * ε := by push_cast; ring

theorem isometry_nonexpansive {E : Type*} [NormedAddCommGroup E]
    (U : E ≃ᵢ E) (x y : E) : ‖U x - U y‖ ≤ ‖x - y‖ := by
  rw [← dist_eq_norm, ← dist_eq_norm, U.dist_eq]

theorem gbs_large_error_state_distance {E : Type*} [NormedAddCommGroup E]
    (r L : ℕ) (f g : ℕ → E → E) (ε : ℝ)
    (hn : ∀ i x y, ‖f i x - f i y‖ ≤ ‖x - y‖)
    (hfg : ∀ i x, ‖f i x - g i x‖ ≤ ε) (ψ : E) :
    ‖orbit f (gbsGradientEstimateCount r L) ψ
        - orbit g (gbsGradientEstimateCount r L) ψ‖
      ≤ (gbsGradientEstimateCount r L : ℝ) * ε :=
  orbit_norm_sub_le f g ε hn hfg _ ψ

theorem gbs_large_error_state_distance_lt {E : Type*} [NormedAddCommGroup E]
    (r L : ℕ) (hL : 0 < L) (f g : ℕ → E → E) (ε : ℝ)
    (hn : ∀ i x y, ‖f i x - f i y‖ ≤ ‖x - y‖)
    (hfg : ∀ i x, ‖f i x - g i x‖ < ε) (ψ : E) :
    ‖orbit f (gbsGradientEstimateCount r L) ψ
        - orbit g (gbsGradientEstimateCount r L) ψ‖
      < (gbsGradientEstimateCount r L : ℝ) * ε := by
  have hpos : 0 < gbsGradientEstimateCount r L := by
    unfold gbsGradientEstimateCount
    exact Nat.mul_pos (by omega) hL
  exact orbit_norm_sub_lt f g ε hn hfg _ hpos ψ

theorem gbs_large_error_unitary_distance {E : Type*} [NormedAddCommGroup E]
    (r L : ℕ) (U V : ℕ → E ≃ᵢ E) (ε : ℝ)
    (hfg : ∀ i x, ‖U i x - V i x‖ ≤ ε) (ψ : E) :
    ‖orbit (fun i => U i) (gbsGradientEstimateCount r L) ψ
        - orbit (fun i => V i) (gbsGradientEstimateCount r L) ψ‖
      ≤ (gbsGradientEstimateCount r L : ℝ) * ε :=
  gbs_large_error_state_distance r L _ _ ε
    (fun i => isometry_nonexpansive (U i)) hfg ψ

theorem large_error_tolerance_exists (r L : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ (gbsGradientEstimateCount r L : ℝ) * ε < η := by
  refine ⟨η / ((gbsGradientEstimateCount r L : ℝ) + 1), ?_, ?_⟩
  · positivity
  · have hpos : (0 : ℝ) < (gbsGradientEstimateCount r L : ℝ) + 1 := by positivity
    have hnonneg : (0 : ℝ) ≤ (gbsGradientEstimateCount r L : ℝ) := by positivity
    have hrewrite : (gbsGradientEstimateCount r L : ℝ)
          * (η / ((gbsGradientEstimateCount r L : ℝ) + 1))
        = ((gbsGradientEstimateCount r L : ℝ) * η)
          / ((gbsGradientEstimateCount r L : ℝ) + 1) := by ring
    rw [hrewrite, div_lt_iff₀ hpos]
    nlinarith

theorem large_errors_negligible {E : Type*} [NormedAddCommGroup E]
    (r L : ℕ) (hL : 0 < L) (f g : ℕ → E → E)
    (hn : ∀ i x y, ‖f i x - f i y‖ ≤ ‖x - y‖) (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (hfg : ∀ i x, ‖f i x - g i x‖ < ε) (ψ : E),
        ‖orbit f (gbsGradientEstimateCount r L) ψ
          - orbit g (gbsGradientEstimateCount r L) ψ‖ < η := by
  obtain ⟨ε, hε, hlt⟩ := large_error_tolerance_exists r L η hη
  refine ⟨ε, hε, ?_⟩
  intro hfg ψ
  have h := gbs_large_error_state_distance_lt r L hL f g ε hn hfg ψ
  linarith

end Qatlib.Papers.QBasinHopping05.MainResults
