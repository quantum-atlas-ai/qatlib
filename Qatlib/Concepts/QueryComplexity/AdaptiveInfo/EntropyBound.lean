/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Entropy lower bounds for classical queries

This module derives lower bounds on expected query cost from Kraft inequalities and entropy. It
defines natural logarithm entropy as `entropy` and the weighted actual query cost as
`expectedQueries`.

The results apply to exact recovery on all labels or only on the positive probability support.
They formalize the classical information bound discussed in [TerhalSmolin1998].

## Main statements

* `entropy_le_log_mul_length`: an entropy bound for lengths satisfying a Kraft inequality.
* `information_lower_bound`: entropy divided by the logarithm of the answer alphabet size bounds
  expected queries.
* `support_information_lower_bound`: the same bound when correctness holds on the source
  support.

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.AdaptiveInfo.EntropyBound

open Qatlib.Concepts.QueryComplexity.AdaptiveInfo

/-- The entropy of a finite probability distribution is at most its cross entropy against any
strictly positive subprobability function. -/
theorem entropy_le_cross_of_subprob {Y : Type} [Fintype Y]
    (p q : Y → ℝ) (hp : ∀ y, 0 ≤ p y) (hsum : ∑ y, p y = 1)
    (hq : ∀ y, 0 < q y) (hqsum : ∑ y, q y ≤ 1) :
    (∑ y, Real.negMulLog (p y)) ≤ -(∑ y, p y*Real.log (q y)) := by
  have hpoint (y : Y) : Real.negMulLog (p y) ≤ -(p y*Real.log (q y))+q y-p y := by
    by_cases hz : p y=0
    · simp only [hz, Real.negMulLog_zero, zero_mul, neg_zero, zero_add, sub_zero]
      exact (hq y).le
    · have hpos : 0 < p y := lt_of_le_of_ne (hp y) (Ne.symm hz)
      have hl := Real.log_le_sub_one_of_pos (div_pos (hq y) hpos)
      rw [Real.log_div (hq y).ne' hpos.ne'] at hl
      have hm := mul_le_mul_of_nonneg_left hl (hp y)
      have he : p y*(q y/p y-1)=q y-p y := by field_simp
      rw [he] at hm
      unfold Real.negMulLog
      nlinarith
  have hs := Finset.sum_le_sum (fun y (_ : y∈(Finset.univ:Finset Y)) => hpoint y)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, hsum] at hs
  linarith

/-- Lengths satisfying the Kraft inequality bound entropy by the expected length times the
natural logarithm of the alphabet size. -/
theorem entropy_le_log_mul_length {Y : Type} [Fintype Y] (p : Y → ℝ)
    (hp : ∀ y, 0 ≤ p y) (hsum : ∑ y, p y = 1)
    (A : ℕ) (hA : 0 < A) (length : Y → ℕ)
    (hKraft : ∑ y, (1/(A:ℝ))^(length y) ≤ 1) :
    (∑ y, Real.negMulLog (p y)) ≤ Real.log A * (∑ y, p y*(length y:ℝ)) := by
  have h := entropy_le_cross_of_subprob p (fun y => (1/(A:ℝ))^(length y)) hp hsum
    (by intro y; exact pow_pos (one_div_pos.mpr (by exact_mod_cast hA)) _) hKraft
  have hterm (y : Y) : p y*Real.log ((1/(A:ℝ))^(length y)) =
      -Real.log A * (p y*(length y:ℝ)) := by
    rw [Real.log_pow, one_div, Real.log_inv]
    ring
  simp_rw [hterm] at h
  rw [← Finset.mul_sum] at h
  nlinarith

/-- For an alphabet of at least two symbols, entropy divided by the logarithm of its size bounds
the expected length of any lengths satisfying the Kraft inequality. -/
theorem entropy_div_log_le_length {Y : Type} [Fintype Y] (p : Y → ℝ)
    (hp : ∀ y, 0 ≤ p y) (hsum : ∑ y, p y = 1)
    (A : ℕ) (hA : 2 ≤ A) (length : Y → ℕ)
    (hKraft : ∑ y, (1/(A:ℝ))^(length y) ≤ 1) :
    (∑ y, Real.negMulLog (p y))/Real.log A ≤ ∑ y, p y*(length y:ℝ) := by
  apply (div_le_iff₀ (Real.log_pos (by exact_mod_cast (show 1<A by omega)))).2
  simpa only [mul_comm] using entropy_le_log_mul_length p hp hsum A (by omega) length hKraft

/-- The natural logarithm entropy of a finite real weight function, defined as the sum of
`Real.negMulLog`. -/
noncomputable def entropy {Y : Type} [Fintype Y] (p : Y → ℝ) : ℝ :=
  ∑ y, Real.negMulLog (p y)

/-- The expected actual query count of a classical tree, weighted by a finite source
distribution. -/
noncomputable def expectedQueries {I A Y : Type} [Fintype Y]
    (oracle : Y → I → A) (tree : ClassicalDefs.QueryTree I A Y) (p : Y → ℝ) : ℝ :=
  ∑ y, p y * ((ClassicalDefs.run (oracle y) tree).2:ℝ)

/-- For exact recovery, source entropy divided by the logarithm of the answer alphabet
cardinality is a lower bound on expected queries. -/
theorem information_lower_bound {I A Y : Type} [Fintype A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] (oracle : Y → I → A)
    (tree : ClassicalDefs.QueryTree I A Y) (p : Y → ℝ)
    (hp : ∀ y, 0≤p y) (hsum : ∑ y,p y=1) (hA : 2≤Fintype.card A)
    (hcorrect : ∀ y, (ClassicalDefs.run (oracle y) tree).1=y) :
    entropy p / Real.log (Fintype.card A) ≤ expectedQueries oracle tree p := by
  apply entropy_div_log_le_length p hp hsum (Fintype.card A) hA
    (fun y => (ClassicalDefs.run (oracle y) tree).2)
  simpa only [Finset.mem_univ,true_implies] using
    ClassicalDefs.actual_kraft oracle tree Finset.univ (fun y _ => hcorrect y)

/-- The entropy lower bound on expected queries requires exact recovery only for labels with
positive source probability. This is the support version of the information bound in [Terhal
and Smolin, Eq. (1.2)][TerhalSmolin1998]. -/
theorem support_information_lower_bound {I A Y : Type} [Fintype A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] (oracle : Y → I → A)
    (tree : ClassicalDefs.QueryTree I A Y) (p : Y → ℝ)
    (hp : ∀ y, 0≤p y) (hsum : ∑ y,p y=1) (hA : 2≤Fintype.card A)
    (hcorrect : ∀ y, 0<p y → (ClassicalDefs.run (oracle y) tree).1=y) :
    entropy p / Real.log (Fintype.card A) ≤ expectedQueries oracle tree p := by
  classical
  let S := Finset.univ.filter (fun y => 0<p y)
  have hz (y : Y) (hy : y ∉ S) : p y=0 := by
    have hn : ¬0<p y := by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hy
    have hnonneg := hp y
    linarith
  have hrestricted (f : Y → ℝ) (hzero : ∀ y ∉ S, f y=0) :
      (∑ y : S,f y) = ∑ y,f y := by
    rw [Finset.sum_coe_sort]
    exact Finset.sum_subset (Finset.filter_subset _ _) (fun y _ hy => hzero y hy)
  have hs : (∑ y : S,p y)=1 := by rw [hrestricted p hz,hsum]
  have hK : ∑ y : S, (1/(Fintype.card A:ℝ))^((ClassicalDefs.run (oracle y) tree).2) ≤ 1 := by
    rw [Finset.sum_coe_sort S (fun y : Y =>
      (1/(Fintype.card A:ℝ))^((ClassicalDefs.run (oracle y) tree).2))]
    exact ClassicalDefs.actual_kraft oracle tree S
      (fun y hy => hcorrect y (Finset.mem_filter.mp hy).2)
  have h := entropy_div_log_le_length (fun y : S => p y) (fun y => hp y) hs
    (Fintype.card A) hA (fun y => (ClassicalDefs.run (oracle y) tree).2) hK
  rw [hrestricted (fun y => Real.negMulLog (p y))
    (fun y hy => by simp only [hz y hy,Real.negMulLog_zero]),
    hrestricted (fun y => p y*((ClassicalDefs.run (oracle y) tree).2:ℝ))
    (fun y hy => by simp only [hz y hy,zero_mul])] at h
  exact h

/-- The entropy lower bound expressed using entropy in bits and the base two logarithm of the
answer alphabet cardinality. -/
theorem source_information_lower_bound {I A Y : Type} [Fintype A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] (oracle : Y → I → A)
    (tree : ClassicalDefs.QueryTree I A Y) (p : Y → ℝ)
    (hp : ∀ y, 0≤p y) (hsum : ∑ y,p y=1) (hA : 2≤Fintype.card A)
    (hcorrect : ∀ y, (ClassicalDefs.run (oracle y) tree).1=y) :
    (entropy p/Real.log 2)/Real.logb 2 (Fintype.card A) ≤ expectedQueries oracle tree p := by
  have he : (entropy p/Real.log 2)/Real.logb 2 (Fintype.card A) =
      entropy p/Real.log (Fintype.card A) := by
    have h2 : Real.log (2:ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hcard : Real.log (Fintype.card A:ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1<Fintype.card A by omega))).ne'
    rw [Real.logb]
    field_simp
  rw [he]
  exact information_lower_bound oracle tree p hp hsum hA hcorrect

end Qatlib.Concepts.QueryComplexity.AdaptiveInfo.EntropyBound
