/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Superposition02.MainResults.Superposition
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Superposition02.MainResults

namespace Composition

open DyadicSource ControlledRotation

theorem sqrt_mul_cosTheta (pL pR : ℝ) (hL : 0 ≤ pL) (hR : 0 ≤ pR) :
    Real.sqrt (pL + pR) * cosTheta pL pR = Real.sqrt pL := by
  by_cases hp : pL + pR = 0
  · have hL0 : pL = 0 := le_antisymm (by linarith) hL
    have hR0 : pR = 0 := le_antisymm (by linarith) hR
    subst hL0
    subst hR0
    simp [cosTheta, leftFraction]
  · have hp' : 0 < pL + pR := lt_of_le_of_ne (by linarith) (Ne.symm hp)
    exact refined_left_amplitude _ pL pR (Real.sqrt_nonneg _) hp'
      (Real.sq_sqrt (le_of_lt hp'))

theorem sqrt_mul_sinTheta (pL pR : ℝ) (hL : 0 ≤ pL) (hR : 0 ≤ pR) :
    Real.sqrt (pL + pR) * sinTheta pL pR = Real.sqrt pR := by
  by_cases hp : pL + pR = 0
  · have hL0 : pL = 0 := le_antisymm (by linarith) hL
    have hR0 : pR = 0 := le_antisymm (by linarith) hR
    subst hL0
    subst hR0
    simp [sinTheta, leftFraction]
  · have hp' : 0 < pL + pR := lt_of_le_of_ne (by linarith) (Ne.symm hp)
    exact refined_right_amplitude _ pL pR (Real.sqrt_nonneg _) hp'
      (Real.sq_sqrt (le_of_lt hp'))

theorem dyadic_left_amplitude (D : DyadicMass) (m k : ℕ) :
    D.amplitude m k *
        (cosTheta (D.mass (m + 1) (2 * k)) (D.mass (m + 1) (2 * k + 1)) : ℂ) =
      D.amplitude (m + 1) (2 * k) := by
  have hden : D.mass (m + 1) (2 * k) + D.mass (m + 1) (2 * k + 1) = D.mass m k :=
    (D.refine m k).symm
  have hreal : Real.sqrt (D.mass m k) *
      cosTheta (D.mass (m + 1) (2 * k)) (D.mass (m + 1) (2 * k + 1)) =
        Real.sqrt (D.mass (m + 1) (2 * k)) := by
    rw [← hden]
    exact sqrt_mul_cosTheta _ _ (D.nonneg (m + 1) (2 * k))
      (D.nonneg (m + 1) (2 * k + 1))
  have h := congrArg (fun x : ℝ => (x : ℂ)) hreal
  simpa [DyadicSource.DyadicMass.amplitude, Complex.ofReal_mul] using h

theorem dyadic_right_amplitude (D : DyadicMass) (m k : ℕ) :
    D.amplitude m k *
        (sinTheta (D.mass (m + 1) (2 * k)) (D.mass (m + 1) (2 * k + 1)) : ℂ) =
      D.amplitude (m + 1) (2 * k + 1) := by
  have hden : D.mass (m + 1) (2 * k) + D.mass (m + 1) (2 * k + 1) = D.mass m k :=
    (D.refine m k).symm
  have hreal : Real.sqrt (D.mass m k) *
      sinTheta (D.mass (m + 1) (2 * k)) (D.mass (m + 1) (2 * k + 1)) =
        Real.sqrt (D.mass (m + 1) (2 * k + 1)) := by
    rw [← hden]
    exact sqrt_mul_sinTheta _ _ (D.nonneg (m + 1) (2 * k))
      (D.nonneg (m + 1) (2 * k + 1))
  have h := congrArg (fun x : ℝ => (x : ℂ)) hreal
  simpa [DyadicSource.DyadicMass.amplitude, Complex.ofReal_mul] using h

theorem branch_probabilities_sum (D : DyadicMass) (m k : ℕ) (hp : 0 < D.mass m k) :
    D.mass (m + 1) (2 * k) / D.mass m k +
        D.mass (m + 1) (2 * k + 1) / D.mass m k = 1 := by
  rw [← add_div, ← D.refine m k, div_self (ne_of_gt hp)]

theorem block_mass (D : DyadicMass) (m k d : ℕ) :
    (∑ j ∈ Finset.range (2 ^ d), D.mass (m + d) (k * 2 ^ d + j)) = D.mass m k := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ, Nat.mul_comm]
    have hadd : m + (d + 1) = (m + d) + 1 := (Nat.add_assoc m d 1).symm
    rw [hpow, hadd]
    have hsplit := sum_range_even_odd
      (fun j => D.mass ((m + d) + 1) (k * (2 * 2 ^ d) + j)) (2 ^ d)
    rw [hsplit]
    have hpair : ∀ t : ℕ,
        D.mass ((m + d) + 1) (k * (2 * 2 ^ d) + 2 * t) +
          D.mass ((m + d) + 1) (k * (2 * 2 ^ d) + (2 * t + 1)) =
        D.mass (m + d) (k * 2 ^ d + t) := by
      intro t
      have h1 : k * (2 * 2 ^ d) + 2 * t = 2 * (k * 2 ^ d + t) := by ring
      have h2 : k * (2 * 2 ^ d) + (2 * t + 1) = 2 * (k * 2 ^ d + t) + 1 := by ring
      rw [h1, h2, ← D.refine (m + d) (k * 2 ^ d + t)]
    rw [← Finset.sum_add_distrib]
    exact (Finset.sum_congr rfl (fun t _ => hpair t)).trans ih

theorem descendant_born_probability (D : DyadicMass) (m k d : ℕ) :
    (∑ j ∈ Finset.range (2 ^ d),
        ‖D.amplitude (m + d) (k * 2 ^ d + j)‖ ^ 2) = D.mass m k := by
  simp_rw [DyadicSource.born_amplitude]
  exact block_mass D m k d

end Composition

end Qatlib.Papers.Superposition02.MainResults
