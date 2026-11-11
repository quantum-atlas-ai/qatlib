/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic

/-!
# Accumulation of gradient-oracle errors

For time-dependent maps, `orbit` iterates the successive steps and `gbsGradientEstimateCount`
records `(2 * r + 1) * L` gradient estimates. Nonexpansiveness of the reference steps and
uniform bounds on each perturbation give linear accumulation of state distance, providing the
stability estimates used in [Bulger2005].

## Main statements

* `orbit_norm_sub_le`: the general linear error-accumulation bound.
* `gbs_large_error_unitary_distance`: the specialization to isometric steps.
* `large_errors_negligible`: a positive local tolerance for any target final error.

## References

* [Bulger, 2005][Bulger2005]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QBasinHopping05.MainResults

/-- The time-dependent iteration that applies step `u n` after the first `n` steps, starting
with the identity at zero. -/
def orbit {E : Type*} (u : ℕ → E → E) : ℕ → E → E
  | 0, x => x
  | n + 1, x => u n (orbit u n x)

/-- The gradient-estimation count `(2 * r + 1) * L`. -/
def gbsGradientEstimateCount (r L : ℕ) : ℕ := (2 * r + 1) * L

/-- If each reference step is nonexpansive and differs uniformly from the corresponding
perturbed step by at most `ε`, the distance after `N` steps is at most `Nε` [Bulger2005]. -/
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

/-- With nonexpansive reference steps and strict uniform local error below `ε`, the distance
after any positive number `N` of steps is strictly below `Nε`. -/
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

/-- An isometric equivalence is nonexpansive in norm distance [Bulger2005]. -/
theorem isometry_nonexpansive {E : Type*} [NormedAddCommGroup E]
    (U : E ≃ᵢ E) (x y : E) : ‖U x - U y‖ ≤ ‖x - y‖ := by
  rw [← dist_eq_norm, ← dist_eq_norm, U.dist_eq]

/-- The distance between the two basin-hopping orbits is at most the gradient-estimation count
times the uniform local error, provided the reference steps are nonexpansive [Bulger2005]. -/
theorem gbs_large_error_state_distance {E : Type*} [NormedAddCommGroup E]
    (r L : ℕ) (f g : ℕ → E → E) (ε : ℝ)
    (hn : ∀ i x y, ‖f i x - f i y‖ ≤ ‖x - y‖)
    (hfg : ∀ i x, ‖f i x - g i x‖ ≤ ε) (ψ : E) :
    ‖orbit f (gbsGradientEstimateCount r L) ψ
        - orbit g (gbsGradientEstimateCount r L) ψ‖
      ≤ (gbsGradientEstimateCount r L : ℝ) * ε :=
  orbit_norm_sub_le f g ε hn hfg _ ψ

/-- For positive `L`, strict uniform local error bounds give a strict accumulated-distance bound
by the gradient-estimation count times `ε` [Bulger2005]. -/
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

/-- For two sequences of isometric equivalences, uniform local distance at most `ε` gives
accumulated basin-hopping distance at most the gradient-estimation count times `ε`
[Bulger2005]. -/
theorem gbs_large_error_unitary_distance {E : Type*} [NormedAddCommGroup E]
    (r L : ℕ) (U V : ℕ → E ≃ᵢ E) (ε : ℝ)
    (hfg : ∀ i x, ‖U i x - V i x‖ ≤ ε) (ψ : E) :
    ‖orbit (fun i => U i) (gbsGradientEstimateCount r L) ψ
        - orbit (fun i => V i) (gbsGradientEstimateCount r L) ψ‖
      ≤ (gbsGradientEstimateCount r L : ℝ) * ε :=
  gbs_large_error_state_distance r L _ _ ε
    (fun i => isometry_nonexpansive (U i)) hfg ψ

/-- For any positive target `η`, there is a positive `ε` whose product with the
gradient-estimation count is below `η` [Bulger2005]. -/
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

/-- For positive `L`, nonexpansive reference steps, and any positive target error, a
sufficiently small positive uniform local tolerance guarantees orbit distance below that
target for every initial state [Bulger2005]. -/
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
