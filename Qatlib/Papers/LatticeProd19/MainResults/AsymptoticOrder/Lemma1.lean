/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Qatlib.Papers.LatticeProd19.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Asymptotic Scaling versus Vanishing Iterated Derivatives

This module proves Lemma 1: for a smooth function `F : ℝ → E` into a real normed
space, the asymptotic bound `F(t) = O(t^{p+1})` as `t → 0` is equivalent to the
vanishing of all iterated derivatives `F^{(j)}(0) = 0` for `0 ≤ j ≤ p`.

## Main statements

* `lemma1_asymptotic_iff_deriv_zero`: `F(t) = O(t^{p+1})` at `0` iff
  `∀ j ≤ p, iteratedDeriv j F 0 = 0`.

## References

* [Childs and Su, 2019][ChildsSu2019], Lemma 1, Eqs. (11)--(12), p. 3.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LatticeProd19.MainResults.AsymptoticOrder

open Asymptotics Filter Set
open scoped Topology

/-- **Lemma 1**: for an infinitely differentiable `F : ℝ → E`, the asymptotic bound
`F(t) = O(t^{p+1})` as `t → 0` holds if and only if `iteratedDeriv j F 0 = 0` for
every `j ≤ p`. -/
theorem lemma1_asymptotic_iff_deriv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (p : ℕ) (_hp : 1 ≤ p) (hF : ContDiff ℝ ⊤ F) :
    Asymptotics.IsBigO (𝓝 (0 : ℝ)) F (fun t : ℝ => t ^ (p + 1)) ↔
      ∀ j ≤ p, iteratedDeriv j F 0 = 0 := by
  constructor
  · intro hbig j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      have hle : ContDiff ℝ j F := hF.of_le (by simp)
      have hrem : (fun x : ℝ => F x - taylorWithinEval F j univ 0 x) =o[𝓝 (0 : ℝ)]
          (fun x : ℝ => x ^ j) := by
        simpa using taylor_isLittleO_univ (f := F) (x₀ := 0) hle
      have hpoly : ∀ x : ℝ,
          taylorWithinEval F j univ 0 x =
            (((j.factorial : ℝ)⁻¹ * x ^ j) • iteratedDeriv j F 0) := by
        intro x
        rw [taylor_within_apply, Finset.sum_eq_single j]
        · simp [iteratedDerivWithin_univ]
        · intro m hm hne
          have hmj : m < j := by
            simp only [Finset.mem_range] at hm
            omega
          rw [iteratedDerivWithin_univ, ih m hmj (by omega), smul_zero]
        · intro hnot
          simp at hnot
      have hsmall : F =o[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ j) :=
        hbig.trans_isLittleO (isLittleO_pow_pow (by omega))
      have hP : (fun x : ℝ => ((j.factorial : ℝ)⁻¹ * x ^ j) • iteratedDeriv j F 0)
          =o[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ j) := by
        simpa only [sub_sub_cancel, hpoly] using hsmall.sub hrem
      by_contra hv
      have ha : 0 < (j.factorial : ℝ)⁻¹ := by positivity
      have hvnorm : 0 < ‖iteratedDeriv j F 0‖ := norm_pos_iff.mpr hv
      have hc : 0 < (j.factorial : ℝ)⁻¹ * ‖iteratedDeriv j F 0‖ / 2 := by
        positivity
      obtain ⟨δ, hδ, hbound⟩ :=
        Metric.eventually_nhds_iff.mp (isLittleO_iff.mp hP hc)
      have hx : 0 < δ / 2 := by linarith
      have hpow : 0 < ‖(δ / 2) ^ j‖ := norm_pos_iff.mpr (pow_ne_zero j (ne_of_gt hx))
      have hineq := hbound (y := δ / 2) (by
        simpa only [Real.dist_eq, sub_zero, abs_of_pos hx] using (show δ / 2 < δ by
          linarith))
      rw [norm_smul, norm_mul, Real.norm_eq_abs, abs_of_pos ha] at hineq
      have hcoeff : (j.factorial : ℝ)⁻¹ * ‖iteratedDeriv j F 0‖ ≤
          (j.factorial : ℝ)⁻¹ * ‖iteratedDeriv j F 0‖ / 2 := by
        apply (mul_le_mul_iff_left₀ hpow).mp
        nlinarith [hineq]
      linarith
  · intro hderiv
    have hle : ContDiff ℝ (p + 1) F := hF.of_le (by simp)
    have hrem := taylor_isLittleO_univ (f := F) (x₀ := 0) hle
    set v : E := iteratedDeriv (p + 1) F 0 with hv
    set c : ℝ := ((p + 1).factorial : ℝ)⁻¹ with hc
    have hpoly : ∀ x : ℝ,
        taylorWithinEval F (p + 1) univ 0 x = (c * x ^ (p + 1)) • v := by
      intro x
      rw [taylor_within_apply]
      rw [Finset.sum_eq_single (p + 1)]
      · simp [hc, hv, iteratedDerivWithin_univ]
      · intro k hk hne
        have hkp : k ≤ p := by
          simp only [Finset.mem_range] at hk
          omega
        rw [iteratedDerivWithin_univ, hderiv k hkp, smul_zero]
      · intro hnot
        simp at hnot
    have hP : (fun x : ℝ => (c * x ^ (p + 1)) • v) =O[𝓝 (0 : ℝ)]
        (fun x : ℝ => x ^ (p + 1)) := by
      have h1 : (fun x : ℝ => x ^ (p + 1) • v) =O[𝓝 (0 : ℝ)]
          (fun x : ℝ => x ^ (p + 1)) := by
        refine Asymptotics.isBigO_iff.mpr ⟨‖v‖, ?_⟩
        filter_upwards with x
        rw [norm_smul, mul_comm]
      simpa only [mul_smul, Pi.smul_def] using h1.const_smul_left c
    have hremO : (fun x : ℝ => F x - taylorWithinEval F (p + 1) univ 0 x) =O[𝓝 (0 : ℝ)]
        (fun x : ℝ => x ^ (p + 1)) := by
      simpa using hrem.isBigO
    have hsum := hremO.add hP
    have heq : F = fun x : ℝ =>
        (F x - taylorWithinEval F (p + 1) univ 0 x) + (c * x ^ (p + 1)) • v := by
      funext x
      rw [hpoly x, sub_add_cancel]
    rw [heq]
    exact hsum

end Qatlib.Papers.LatticeProd19.MainResults.AsymptoticOrder
