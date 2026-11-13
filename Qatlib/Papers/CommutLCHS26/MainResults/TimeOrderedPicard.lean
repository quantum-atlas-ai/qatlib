/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.DysonGrid.DysonTruncationGrid

/-!
# Picard identities for ordered Dyson prefixes

This module relates finite Dyson prefixes to Picard iteration and residual integral identities.
Contractivity of the ordered evolution yields factorial truncation estimates for the
time-dependent setting associated with [AftabAnTrivisa2026].

## Main statements

* `dysonPrefix_error_identity`: an exact propagated-residual formula.
* `norm_dysonPrefix_error_le`: the factorial error bound under a positive semidefinite
  Hermitian-part condition.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.TimeOrderedPicard

open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.InteractionEvo.DysonGrid

variable {I : Type} [Fintype I] [DecidableEq I]

/-- A Dyson prefix evaluated at its initial time is the identity matrix. -/
@[simp] theorem dysonPrefix_self (A : ℝ → Matrix I I ℂ) (s : ℝ) (n : ℕ) :
    dysonPrefix A s s n = 1 := by
  rw [dysonPrefix, Finset.sum_range_succ']
  simp [orderedDysonTerm]

/-- For continuous `A`, the derivative of the successor Dyson prefix is `-A t` times the
preceding prefix. -/
theorem dysonPrefix_hasDerivAt_succ (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    (s : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun u => dysonPrefix A s u (n + 1)) (-(A t * dysonPrefix A s t n)) t := by
  have hd := (HasDerivAt.fun_sum (u := Finset.range (n + 1))
    (fun k _ => orderedDysonTerm_hasDerivAt_succ A hA s k t)).add_const
      (1 : Matrix I I ℂ)
  convert! hd using 1
  · funext u
    simp only [dysonPrefix, Finset.sum_range_succ', orderedDysonTerm]
  · simp only [dysonPrefix, Finset.mul_sum, Finset.sum_neg_distrib]

/-- The derivative of a Dyson prefix equals its highest-order residual term minus `A t` times
that prefix. -/
theorem dysonPrefix_hasDerivAt (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    (s : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun u => dysonPrefix A s u n)
      (A t * orderedDysonTerm A s n t - A t * dysonPrefix A s t n) t := by
  cases n with
  | zero => simpa [dysonPrefix, orderedDysonTerm] using!
      hasDerivAt_const t (1 : Matrix I I ℂ)
  | succ n =>
    convert! dysonPrefix_hasDerivAt_succ A hA s n t using 1
    rw [dysonPrefix, Finset.sum_range_succ]
    noncomm_ring

/-- The successor Dyson prefix satisfies the Picard integral recurrence. -/
theorem dysonPrefix_succ_eq_picard (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    (s : ℝ) (n : ℕ) (t : ℝ) :
    dysonPrefix A s t (n + 1) =
      1 + ∫ u in s..t, -(A u * dysonPrefix A s u n) := by
  have hc : Continuous (fun u => dysonPrefix A s u n) :=
    continuous_finsetSum _ (fun k _ => orderedDysonTerm_continuous A hA s k)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => dysonPrefix_hasDerivAt_succ A hA s n u)
    ((hA.mul hc).neg.intervalIntegrable s t)
  rw [dysonPrefix_self] at hi
  rw [hi]
  abel

/-- A differentiable matrix function with residual `R` differs from its propagated initial value
by the ordered-evolution integral of `R`. -/
theorem residual_identity (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    (Y R : ℝ → Matrix I I ℂ)
    (hY : ∀ u, HasDerivAt Y (R u - A u * Y u) u) (hR : Continuous R) (s t : ℝ) :
    Y t - orderedEvolution A s t * Y s =
      ∫ u in s..t, orderedEvolution A u t * R u := by
  have hd (u : ℝ) : HasDerivAt (fun v => orderedEvolution A v t * Y v)
      (orderedEvolution A u t * R u) u := by
    convert! (orderedEvolution_hasDerivAt_start A hA t u).mul (hY u) using 1
    noncomm_ring
  have hc : Continuous (fun u => orderedEvolution A u t) :=
    continuous_iff_continuousAt.mpr fun u =>
      (orderedEvolution_hasDerivAt_start A hA t u).continuousAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((hc.mul hR).intervalIntegrable s t)
  simpa using! hi.symm

/-- The error between a Dyson prefix and ordered evolution is the propagated integral of its
highest-order residual. -/
theorem dysonPrefix_error_identity (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    (s : ℝ) (n : ℕ) (t : ℝ) :
    dysonPrefix A s t n - orderedEvolution A s t =
      ∫ u in s..t, orderedEvolution A u t *
        (A u * orderedDysonTerm A s n u) := by
  simpa using! residual_identity A hA (fun u => dysonPrefix A s u n)
    (fun u => A u * orderedDysonTerm A s n u)
    (dysonPrefix_hasDerivAt A hA s n)
    (hA.mul (orderedDysonTerm_continuous A hA s n)) s t

/-- For a continuous generator with positive semidefinite Hermitian part and norm bound `M`, the
Dyson-prefix error on `[s, t]` is at most `(M (t - s))^(n + 1) / (n + 1)!`, supporting the
time-dependent estimates in [AftabAnTrivisa2026]. -/
theorem norm_dysonPrefix_error_le (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    (hPSD : ∀ u, (A u + (A u)ᴴ).PosSemidef) (s t M : ℝ) (hst : s ≤ t)
    (hM : 0 ≤ M) (hbound : ∀ u ∈ Icc s t, ‖A u‖ ≤ M) (n : ℕ) :
    ‖dysonPrefix A s t n - orderedEvolution A s t‖ ≤
      (M * (t - s)) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rw [dysonPrefix_error_identity A hA]
  let g : ℝ → ℝ := fun u => M ^ (n + 1) / (n.factorial : ℝ) * |u - s| ^ n
  have hg : Continuous g := by fun_prop
  have hb (u : ℝ) (hu : u ∈ Ioc s t) :
      ‖orderedEvolution A u t * (A u * orderedDysonTerm A s n u)‖ ≤ g u := by
    have hu' : u ∈ Icc s t := ⟨hu.1.le, hu.2⟩
    have hn := orderedDysonTerm_norm_le A hA s u M hM (fun v hv => by
      have hv' : v ∈ Icc s u := by simpa [uIcc_of_le hu'.1] using! hv
      exact hbound v ⟨hv'.1, hv'.2.trans hu'.2⟩) n
    calc
      _ ≤ ‖orderedEvolution A u t‖ * (‖A u‖ * ‖orderedDysonTerm A s n u‖) :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * (M * ((M * |u - s|) ^ n / (n.factorial : ℝ))) :=
        mul_le_mul (ordered_evolution_psd_contraction I A hA hPSD u t hu.2)
          (mul_le_mul (hbound u hu') hn (norm_nonneg _) hM)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
      _ = g u := by dsimp [g]; rw [mul_pow, pow_succ]; ring
  calc
    _ ≤ ∫ u in s..t, g u := intervalIntegral.norm_integral_le_of_norm_le hst
      (Filter.Eventually.of_forall hb) (hg.intervalIntegrable s t)
    _ = (M * (t - s)) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
      rw [intervalIntegral.integral_of_le hst, ← uIoc_of_le hst]
      dsimp [g]
      rw [MeasureTheory.integral_const_mul, integral_pow_abs_sub_uIoc,
        abs_of_nonneg (sub_nonneg.mpr hst), Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one, mul_pow]
      field_simp

end Qatlib.Papers.CommutLCHS26.MainResults.TimeOrderedPicard
