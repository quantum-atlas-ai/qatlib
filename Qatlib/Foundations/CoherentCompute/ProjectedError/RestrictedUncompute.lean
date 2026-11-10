/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Foundations.CoherentCompute.ProjectedError

theorem coherentUncomputeRestrictedBound
    {E Ω Θ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype Ω]
    (U V T : E →L[ℂ] E) (P : Ω → E →L[ℂ] E) (Q : Θ → E →L[ℂ] E)
    (S : Θ → E →L[ℂ] E) (F : Ω → Θ) (ε : ℝ) (hε : 0 ≤ ε)
    (hVU : ∀ x, V (U x) = x)
    (hV : ∀ x, ‖V x‖ ≤ ‖x‖) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hS : ∀ θ x, ‖S θ x‖ ≤ ‖x‖)
    (hcomm : ∀ θ x, S θ (U x) = U (S θ x))
    (hcontrolled : ∀ θ x, T (Q θ x) = S θ (Q θ x))
    (hpyth : ∀ x, ∑ i, ‖P i x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (hcompute : ∀ i x,
      ‖U (P i x) - Q (F i) (U (P i x))‖ ^ 2 ≤ ε * ‖P i x‖ ^ 2) :
    ‖(V.comp (T.comp U)).comp (∑ i, P i) - ∑ i, (S (F i)).comp (P i)‖ ≤
      2 * Real.sqrt ((Fintype.card Ω : ℝ) * ε) := by
  classical
  let A := (V.comp (T.comp U)).comp (∑ i, P i) - ∑ i, (S (F i)).comp (P i)
  have hblock (i : Ω) (x : E) :
      ‖V (T (U (P i x))) - S (F i) (P i x)‖ ≤ 2 * Real.sqrt ε * ‖P i x‖ := by
    let y := U (P i x) - Q (F i) (U (P i x))
    have hbad : ‖y‖ ≤ Real.sqrt ε * ‖P i x‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
      simpa [y, mul_pow, Real.sq_sqrt hε] using hcompute i x
    have heq : V (T (U (P i x))) - S (F i) (P i x) = V (T y - S (F i) y) := by
      dsimp only [y]
      simp only [map_sub]
      rw [hcontrolled, hcomm, hVU]
      abel
    rw [heq]
    calc
      ‖V (T y - S (F i) y)‖ ≤ ‖T y - S (F i) y‖ := hV _
      _ ≤ ‖T y‖ + ‖S (F i) y‖ := norm_sub_le _ _
      _ ≤ ‖y‖ + ‖y‖ := add_le_add (hT _) (hS _ _)
      _ ≤ 2 * Real.sqrt ε * ‖P i x‖ := by nlinarith
  have hcard : (0 : ℝ) ≤ Fintype.card Ω := Nat.cast_nonneg _
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hsum : ∑ i, ‖P i x‖ ≤ Real.sqrt (Fintype.card Ω : ℝ) * ‖x‖ := by
    have hcs : (∑ i, ‖P i x‖) ^ 2 ≤ (Fintype.card Ω : ℝ) * ‖x‖ ^ 2 := by
      have hh := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Ω))
        (f := fun i => ‖P i x‖)
      simp only [Finset.card_univ] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (hpyth x) hcard)
    apply (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa [mul_pow, Real.sq_sqrt hcard] using hcs
  have hAx : A x = ∑ i, (V (T (U (P i x))) - S (F i) (P i x)) := by
    simp only [A, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sum_apply, map_sum, Finset.sum_sub_distrib]
  change ‖A x‖ ≤ _
  rw [hAx]
  calc
    ‖∑ i, (V (T (U (P i x))) - S (F i) (P i x))‖ ≤
        ∑ i, ‖V (T (U (P i x))) - S (F i) (P i x)‖ := norm_sum_le _ _
    _ ≤ ∑ i, 2 * Real.sqrt ε * ‖P i x‖ := Finset.sum_le_sum fun i _ => hblock i x
    _ = (2 * Real.sqrt ε) * ∑ i, ‖P i x‖ := by rw [Finset.mul_sum]
    _ ≤ (2 * Real.sqrt ε) * (Real.sqrt (Fintype.card Ω : ℝ) * ‖x‖) := by gcongr
    _ = 2 * Real.sqrt ((Fintype.card Ω : ℝ) * ε) * ‖x‖ := by
      rw [Real.sqrt_mul hcard]
      ring

end Qatlib.Foundations.CoherentCompute.ProjectedError
