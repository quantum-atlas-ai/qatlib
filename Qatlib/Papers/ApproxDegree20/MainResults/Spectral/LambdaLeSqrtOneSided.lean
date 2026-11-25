/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ApproxDegree20.MainResults.Spectral.SensitivityAdjacency

@[expose] public section

/-!
# Spectral sensitivity versus the one-sided sensitivities

Source: arXiv:2010.12629v1, Appendix A.3, Lemma 31 (page 31) with Proposition 30 (page 30):
for every total Boolean function `f` the spectral sensitivity satisfies
`λ(f) ≤ √(s₀(f) s₁(f))`.

Ordering the inputs by the value of `f` turns the sensitivity graph into the off-diagonal block
matrix `[[0, Bᵀ], [B, 0]]`, so `λ(f) = ‖B‖`.  The `0 → 1` block `B` has absolute row sums at
most `s₁(f)` and absolute column sums at most `s₀(f)`, and the Hölder estimate
`‖B‖² ≤ ‖B‖₁ ‖B‖∞` gives the claim.  The proof below runs the same computation directly on the
vector action: each side contributes a factor `s₀(f) s₁(f)`.

Boundary: total Boolean functions on an arbitrary finite coordinate type `I`.  Partially defined
functions, for which the paper states the same bound, are not covered.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds (sensAdjacency spectralSensitivity)
open Qatlib.Papers.ApproxDegree20.MainResults.Definitions
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ApproxDegree20.MainResults.Spectral

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- An adjacency entry whose endpoints carry the same value of `f` vanishes. -/
theorem norm_sensAdjacency_eq_zero_of_value_eq (f : (I → Bool) → Bool) {x y : I → Bool}
    (h : f x = f y) : ‖sensAdjacency f x y‖ = 0 := by
  simp only [sensAdjacency]
  rw [ite_eq_right (fun hc => hc.2 h), norm_zero]

set_option maxHeartbeats 1000000 in
/-- The spectral sensitivity is at most the square root of the product of the one-sided
sensitivities. -/
theorem spectralSensitivity_le_sqrt_s0_mul_s1 (f : (I → Bool) → Bool) :
    spectralSensitivity f ≤ Real.sqrt ((s0 f : ℝ) * (s1 f : ℝ)) := by
  classical
  set s0r : ℝ := (s0 f : ℝ) with hs0
  set s1r : ℝ := (s1 f : ℝ) with hs1
  have hs0nn : 0 ≤ s0r := by positivity
  have hs1nn : 0 ≤ s1r := by positivity
  have hC : (0 : ℝ) ≤ Real.sqrt (s0r * s1r) := Real.sqrt_nonneg _
  rw [show spectralSensitivity f = ‖sensAdjacency f‖ from rfl]
  refine l2_opNorm_le_of_mulVec_le hC _ fun v => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp ?_
  set b : (I → Bool) → ℝ := fun y => ‖v y‖ with hb
  have hb0 : ∀ y, 0 ≤ b y := fun y => norm_nonneg _
  set w : (I → Bool) → ℝ := fun x => if f x = true then s1r else s0r with hw
  have hw0 : ∀ x, 0 ≤ w x := by
    intro x
    simp only [hw]
    split_ifs <;> positivity
  -- the weight of a neighbor is the one-sided sensitivity of the opposite side
  have hwne : ∀ x y, f x ≠ f y →
      w x * ‖sensAdjacency f x y‖ = (if f y = true then s0r else s1r)
        * ‖sensAdjacency f x y‖ := by
    intro x y hxy
    have hwx : w x = if f y = true then s0r else s1r := by
      simp only [hw]
      by_cases hy : f y = true <;> by_cases hx : f x = true <;> simp_all
    rw [hwx]
  -- row estimate with the side-dependent weight
  have hrow : ∀ x, ‖(sensAdjacency f *ᵥ v) x‖ ^ 2
      ≤ w x * (∑ y, ‖sensAdjacency f x y‖ * b y ^ 2) := by
    intro x
    have h := mulVec_normSq_le (sensAdjacency f) v x
    have hrowle : (∑ y, ‖sensAdjacency f x y‖) ≤ w x := by
      by_cases hx : f x = true
      · have h := rowSum_le_s1 f hx
        have hwx : w x = s1r := by
          simp only [hw]
          rw [ite_eq_left hx]
        rw [hwx, hs1]
        exact h
      · have hxf : f x = false := by simpa using hx
        have h := rowSum_le_s0 f hxf
        have hwx : w x = s0r := by
          simp only [hw]
          rw [ite_eq_right hx]
        rw [hwx, hs0]
        exact h
    have hb2 : 0 ≤ ∑ y, ‖sensAdjacency f x y‖ * b y ^ 2 :=
      Finset.sum_nonneg fun y _ => by positivity
    exact h.trans (mul_le_mul_of_nonneg_right hrowle hb2)
  -- column estimate for the weighted column sums
  have hcol : ∀ y, (∑ x, w x * ‖sensAdjacency f x y‖) ≤ s0r * s1r := by
    intro y
    have hstep : (∑ x, w x * ‖sensAdjacency f x y‖)
        = (if f y = true then s0r else s1r) * (∑ x, ‖sensAdjacency f x y‖) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hxy : f x = f y
      · rw [norm_sensAdjacency_eq_zero_of_value_eq f hxy]
        ring
      · exact hwne x y hxy
    have hcolle : (∑ x, ‖sensAdjacency f x y‖) ≤ if f y = true then s1r else s0r := by
      by_cases hy : f y = true
      · have h := rowSum_le_s1 f hy
        rw [colSum_sensAdjacency, ← rowSum_sensAdjacency, ite_eq_left hy, hs1]
        exact h
      · have hyf : f y = false := by simpa using hy
        have h := rowSum_le_s0 f hyf
        rw [colSum_sensAdjacency, ← rowSum_sensAdjacency, ite_eq_right hy, hs0]
        exact h
    rw [hstep]
    by_cases hy : f y = true
    · rw [ite_eq_left hy] at hcolle ⊢
      exact mul_le_mul_of_nonneg_left hcolle hs0nn
    · rw [ite_eq_right hy] at hcolle ⊢
      calc s1r * (∑ x, ‖sensAdjacency f x y‖) ≤ s1r * s0r :=
            mul_le_mul_of_nonneg_left hcolle hs1nn
        _ = s0r * s1r := by ring
  calc ‖toEuclidean_fromVec (sensAdjacency f *ᵥ v)‖ ^ 2
      = ∑ x, ‖(sensAdjacency f *ᵥ v) x‖ ^ 2 := norm_toEuclidean_fromVec_sq _
    _ ≤ ∑ x, w x * (∑ y, ‖sensAdjacency f x y‖ * b y ^ 2) :=
        Finset.sum_le_sum fun x _ => hrow x
    _ = ∑ y, (∑ x, w x * ‖sensAdjacency f x y‖) * b y ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ ∑ y, (s0r * s1r) * b y ^ 2 :=
        Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_right (hcol y) (by positivity)
    _ = (s0r * s1r) * ∑ y, b y ^ 2 := by rw [Finset.mul_sum]
    _ = (Real.sqrt (s0r * s1r) * ‖toEuclidean_fromVec v‖) ^ 2 := by
        rw [mul_pow, norm_toEuclidean_fromVec_sq, Real.sq_sqrt (by positivity)]

end Qatlib.Papers.ApproxDegree20.MainResults.Spectral
