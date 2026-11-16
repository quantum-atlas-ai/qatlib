/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
public import Mathlib.Tactic

@[expose] public section


/-!
# Phase ambiguity in the legacy eigenvector perturbation contract

The paper chooses the perturbed eigenvector's phase and uses an actual singular
gap. The legacy contract universally quantifies both eigenvectors and an
unrelated positive denominator. Opposite unit vectors already disprove it.
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath.BornBridge
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Papers.ThermalState23.MainResults.PhaseBoundary

/-- The complete legacy E.2 contract with arbitrary eigenvector phases and denominator. -/
def LegacyE2 : Prop :=
  ∀ (n : ℕ) (M A : Matrix (Fin n) (Fin n) ℂ) (v v' : Fin n → ℂ) (lam lam' ς : ℝ),
    ‖toEuclidean_fromVec v‖ = 1 → ‖toEuclidean_fromVec v'‖ = 1 →
      (∀ i : Fin n, (M *ᵥ v) i = (lam : ℂ) * v i) →
        (∀ i : Fin n, ((M + A) *ᵥ v') i = (lam' : ℂ) * v' i) →
          0 < ς →
            ‖toEuclidean_fromVec v' - toEuclidean_fromVec v‖ ≤
              2 * Real.sqrt 2 * (‖A‖ + |lam' - lam|) / ς

/-- Opposite phases of one scalar unit eigenvector refute the complete legacy E.2 contract. -/
theorem opposite_phase : ¬ LegacyE2 := by
  intro h
  have hplus : ‖toEuclidean_fromVec (fun _ : Fin 1 => (1 : ℂ))‖ = 1 := by
    have hs : ‖toEuclidean_fromVec (fun _ : Fin 1 => (1 : ℂ))‖ ^ 2 = 1 := by
      rw [norm_toEuclidean_fromVec_sq]
      simp
    nlinarith [norm_nonneg (toEuclidean_fromVec (fun _ : Fin 1 => (1 : ℂ)))]
  have hminus : ‖toEuclidean_fromVec (fun _ : Fin 1 => (-1 : ℂ))‖ = 1 := by
    have hs : ‖toEuclidean_fromVec (fun _ : Fin 1 => (-1 : ℂ))‖ ^ 2 = 1 := by
      rw [norm_toEuclidean_fromVec_sq]
      simp
    nlinarith [norm_nonneg (toEuclidean_fromVec (fun _ : Fin 1 => (-1 : ℂ)))]
  have bad := h 1 0 0 (fun _ => 1) (fun _ => -1) 0 0 1 hplus hminus
    (by simp) (by simp) (by norm_num)
  have hzero : ‖toEuclidean_fromVec (fun _ : Fin 1 => (-2 : ℂ))‖ ≤ 0 := by
    have heq : (fun _ : Fin 1 => (-1 : ℂ)) - (fun _ => (1 : ℂ)) = (fun _ => (-2 : ℂ)) := by
      funext i
      norm_num
    simpa only [toEuclidean_fromVec, ← WithLp.toLp_sub, heq, norm_zero,
      sub_self, abs_zero, zero_add, mul_zero, zero_div] using bad
  have hs : ‖toEuclidean_fromVec (fun _ : Fin 1 => (-2 : ℂ))‖ ^ 2 = 4 := by
    rw [norm_toEuclidean_fromVec_sq]
    norm_num
  have hnonneg := norm_nonneg (toEuclidean_fromVec (fun _ : Fin 1 => (-2 : ℂ)))
  have hz : ‖toEuclidean_fromVec (fun _ : Fin 1 => (-2 : ℂ))‖ = 0 := le_antisymm hzero hnonneg
  rw [hz] at hs
  norm_num at hs

end Qatlib.Papers.ThermalState23.MainResults.PhaseBoundary
