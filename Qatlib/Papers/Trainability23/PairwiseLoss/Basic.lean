/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDistTV
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Pairwise losses on finite distributions

This module defines finite-distribution supports, the coordinatewise loss `pairwiseLoss`, and
its separated-support value `lossFixedPoint`. It computes this value for absolute-difference and
clipped relative-entropy losses and relates disjoint supports to maximal total variation. See
[RudolphEtAl2024].

## Main statements

* `pairwiseLoss_eq_lossFixedPoint`: disjoint supports give the separated-support expression when
  `f 0 0 = 0`.
* `tv_pairwiseLoss_eq_two_of_disjoint`: the unscaled absolute-difference loss is two on disjoint
  supports.
* `kl_lossFixedPoint_eq` and `revKl_lossFixedPoint_eq`: clipped relative-entropy expressions for
  positive clipping thresholds.

## References

* [Rudolph et al., 2024][RudolphEtAl2024]
-/

set_option warningAsError false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.Trainability23.PairwiseLoss

open scoped BigOperators

/-- The finite set of points where a finite distribution has nonzero probability. -/
noncomputable def support {X : Type*} [Fintype X] (p : FinDist X) : Finset X :=
  Finset.univ.filter (fun x => p.prob x ≠ 0)

/-- The probabilities summed over the support of a finite distribution equal one. -/
theorem sum_support {X : Type*} [Fintype X] (p : FinDist X) :
    ∑ x ∈ support p, p.prob x = 1 := by
  have h : ∑ x ∈ support p, p.prob x = ∑ x : X, p.prob x := by
    refine Finset.sum_subset ?_ ?_
    · intro x _
      simp
    · intro x _ hx
      simpa [support] using hx
  rw [h, p.sum_one]

/-- The sum over coordinates of `f (p x) (q x)` for two real-valued functions on a finite type. -/
noncomputable def pairwiseLoss {X : Type*} [Fintype X] (f : ℝ → ℝ → ℝ) (p q : X → ℝ) : ℝ :=
  ∑ x, f (p x) (q x)

/-- The separated-support loss obtained by summing `f (p x) 0` over `P` and `f 0 (q x)` over
`Q`. -/
noncomputable def lossFixedPoint {X : Type*} (f : ℝ → ℝ → ℝ) (p : X → ℝ) (P : Finset X)
    (q : X → ℝ) (Q : Finset X) : ℝ :=
  ∑ x ∈ P, f (p x) 0 + ∑ x ∈ Q, f 0 (q x)

/-- The absolute difference `|a - b|` used as the unscaled total-variation summand. -/
def tvPairwise (a b : ℝ) : ℝ := |a - b|

/-- The relative-entropy summand `a * Real.log (a / max b ε)` with the denominator clipped at
`ε`. -/
noncomputable def clippedKL (ε : ℝ) (a b : ℝ) : ℝ := a * Real.log (a / max b ε)

/-- The reverse relative-entropy summand `b * Real.log (b / max a ε)` with the denominator
clipped at `ε`. -/
noncomputable def clippedKLRev (ε : ℝ) (a b : ℝ) : ℝ := b * Real.log (b / max a ε)

/-- The absolute difference of two nonnegative real numbers is at most their sum. -/
theorem abs_sub_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : |a - b| ≤ a + b := by
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The sum of absolute probability differences between two finite distributions is at most two. -/
theorem sum_abs_sub_le_two {X : Type*} [Fintype X] (p q : FinDist X) :
    ∑ x, |p.prob x - q.prob x| ≤ 2 := by
  calc ∑ x, |p.prob x - q.prob x|
      ≤ ∑ x, (p.prob x + q.prob x) :=
        Finset.sum_le_sum fun x _ => abs_sub_le_add (p.nonneg x) (q.nonneg x)
    _ = ∑ x, p.prob x + ∑ x, q.prob x := Finset.sum_add_distrib
    _ = 2 := by rw [p.sum_one, q.sum_one]; norm_num

/-- The total variation distance between two finite distributions is at most one. -/
theorem tvDist_le_one {X : Type*} [Fintype X] [DecidableEq X] (p q : FinDist X) :
    tvDist p q ≤ 1 := by
  have h := sum_abs_sub_le_two p q
  unfold tvDist
  linarith

/-- The sum of absolute probability differences is two exactly when, at each point, at least one
distribution assigns zero probability. -/
theorem sum_abs_sub_eq_two_iff {X : Type*} [Fintype X] (p q : FinDist X) :
    (∑ x, |p.prob x - q.prob x| = 2) ↔ ∀ x, p.prob x = 0 ∨ q.prob x = 0 := by
  have hsum : ∑ x, (p.prob x + q.prob x) = 2 := by
    rw [Finset.sum_add_distrib, p.sum_one, q.sum_one]
    norm_num
  have hle : ∀ x : X, |p.prob x - q.prob x| ≤ p.prob x + q.prob x :=
    fun x => abs_sub_le_add (p.nonneg x) (q.nonneg x)
  constructor
  · intro h
    have hzero : ∑ x, (p.prob x + q.prob x - |p.prob x - q.prob x|) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, h]
      norm_num
    have hnonneg : ∀ x ∈ (Finset.univ : Finset X),
        0 ≤ p.prob x + q.prob x - |p.prob x - q.prob x| :=
      fun x _ => sub_nonneg.mpr (hle x)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero
    intro x
    have hx : p.prob x + q.prob x - |p.prob x - q.prob x| = 0 := hall x (Finset.mem_univ x)
    have habs : |p.prob x - q.prob x| = p.prob x + q.prob x := by linarith
    have hmin : min (p.prob x) (q.prob x) = 0 := by
      have h1 : max (p.prob x) (q.prob x) - min (p.prob x) (q.prob x)
          = |p.prob x - q.prob x| := by
        rw [max_sub_min_eq_abs, abs_sub_comm]
      have h2 := max_add_min (p.prob x) (q.prob x)
      linarith
    rcases le_total (p.prob x) (q.prob x) with hle' | hle'
    · left
      rwa [min_eq_left hle'] at hmin
    · right
      rwa [min_eq_right hle'] at hmin
  · intro h
    have hterm : ∀ x : X, |p.prob x - q.prob x| = p.prob x + q.prob x := by
      intro x
      rcases h x with hx | hx
      · rw [hx, zero_sub, abs_neg, abs_of_nonneg (q.nonneg x), zero_add]
      · rw [hx, sub_zero, abs_of_nonneg (p.nonneg x), add_zero]
    calc ∑ x, |p.prob x - q.prob x|
        = ∑ x, (p.prob x + q.prob x) := Finset.sum_congr rfl fun x _ => hterm x
      _ = 2 := hsum

/-- If `f a 0 = a` and `f 0 b = b` for nonnegative inputs, its separated-support loss on two
finite distributions is two. -/
theorem lossFixedPoint_eq_two_of_oneSided {X : Type*} [Fintype X] (f : ℝ → ℝ → ℝ)
    (hleft : ∀ a, 0 ≤ a → f a 0 = a) (hright : ∀ b, 0 ≤ b → f 0 b = b)
    (p q : FinDist X) :
    lossFixedPoint f p.prob (support p) q.prob (support q) = 2 := by
  have h1 : ∑ x ∈ support p, f (p.prob x) 0 = ∑ x ∈ support p, p.prob x :=
    Finset.sum_congr rfl fun x _ => hleft (p.prob x) (p.nonneg x)
  have h2 : ∑ x ∈ support q, f 0 (q.prob x) = ∑ x ∈ support q, q.prob x :=
    Finset.sum_congr rfl fun x _ => hright (q.prob x) (q.nonneg x)
  unfold lossFixedPoint
  rw [h1, h2, sum_support p, sum_support q]
  norm_num

/-- The separated-support absolute-difference loss of any two finite distributions is two. -/
theorem tv_lossFixedPoint_eq_two {X : Type*} [Fintype X] (p q : FinDist X) :
    lossFixedPoint tvPairwise p.prob (support p) q.prob (support q) = 2 := by
  have h1 : ∑ x ∈ support p, tvPairwise (p.prob x) 0 = ∑ x ∈ support p, p.prob x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [tvPairwise, abs_of_nonneg (p.nonneg x)]
  have h2 : ∑ x ∈ support q, tvPairwise 0 (q.prob x) = ∑ x ∈ support q, q.prob x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [tvPairwise, abs_of_nonneg (q.nonneg x)]
  unfold lossFixedPoint
  rw [h1, h2, sum_support p, sum_support q]
  norm_num

/-- The separated-support absolute-difference loss is constant across any parameterized family
of finite distributions. -/
theorem tv_lossFixedPoint_const {X : Type*} [Fintype X] {Θ : Type*} (p : FinDist X)
    (q : Θ → FinDist X) (t t' : Θ) :
    lossFixedPoint tvPairwise p.prob (support p) (q t).prob (support (q t))
      = lossFixedPoint tvPairwise p.prob (support p) (q t').prob (support (q t')) := by
  rw [tv_lossFixedPoint_eq_two p (q t), tv_lossFixedPoint_eq_two p (q t')]

/-- For distributions with disjoint supports, a pairwise loss satisfying `f 0 0 = 0` equals its
separated-support expression. See [RudolphEtAl2024]. -/
theorem pairwiseLoss_eq_lossFixedPoint {X : Type*} [Fintype X] [DecidableEq X]
    (f : ℝ → ℝ → ℝ) (hf : f 0 0 = 0) (p q : FinDist X)
    (hdisj : Disjoint (support p) (support q)) :
    pairwiseLoss f p.prob q.prob =
      lossFixedPoint f p.prob (support p) q.prob (support q) := by
  have hp0 : ∀ x, x ∉ support p → p.prob x = 0 := fun x hx => by simpa [support] using hx
  have hq0 : ∀ x, x ∉ support q → q.prob x = 0 := fun x hx => by simpa [support] using hx
  have hunion : ∑ x ∈ support p ∪ support q, f (p.prob x) (q.prob x)
      = ∑ x : X, f (p.prob x) (q.prob x) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro x _ hx
    rw [Finset.mem_union, not_or] at hx
    rw [hp0 x hx.1, hq0 x hx.2, hf]
  have hA : ∑ x ∈ support p, f (p.prob x) (q.prob x) = ∑ x ∈ support p, f (p.prob x) 0 := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [hq0 x fun h => (Finset.disjoint_left.mp hdisj) hx h]
  have hB : ∑ x ∈ support q, f (p.prob x) (q.prob x) = ∑ x ∈ support q, f 0 (q.prob x) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [hp0 x fun h => (Finset.disjoint_left.mp hdisj) h hx]
  rw [pairwiseLoss, lossFixedPoint, ← hunion, Finset.sum_union hdisj, hA, hB]

/-- A pairwise loss on disjoint supports is two when it vanishes at `(0, 0)` and has the stated
one-sided values on nonnegative inputs. -/
theorem pairwiseLoss_eq_two_of_disjoint_of_oneSided {X : Type*} [Fintype X] [DecidableEq X]
    (f : ℝ → ℝ → ℝ) (hf : f 0 0 = 0)
    (hleft : ∀ a, 0 ≤ a → f a 0 = a) (hright : ∀ b, 0 ≤ b → f 0 b = b)
    (p q : FinDist X) (hdisj : Disjoint (support p) (support q)) :
    pairwiseLoss f p.prob q.prob = 2 := by
  rw [pairwiseLoss_eq_lossFixedPoint f hf p q hdisj,
    lossFixedPoint_eq_two_of_oneSided f hleft hright p q]

/-- The unscaled absolute-difference loss of distributions with disjoint supports is two. See
[RudolphEtAl2024]. -/
theorem tv_pairwiseLoss_eq_two_of_disjoint {X : Type*} [Fintype X] [DecidableEq X]
    (p q : FinDist X) (hdisj : Disjoint (support p) (support q)) :
    pairwiseLoss tvPairwise p.prob q.prob = 2 := by
  refine pairwiseLoss_eq_two_of_disjoint_of_oneSided tvPairwise ?_ ?_ ?_ p q hdisj
  · simp [tvPairwise]
  · intro a ha
    simp [tvPairwise, abs_of_nonneg ha]
  · intro b hb
    simp [tvPairwise, abs_of_nonneg hb]

/-- For positive `ε`, the separated-support clipped relative-entropy loss is the support sum of
`p.prob x * Real.log (p.prob x / ε)`. See [RudolphEtAl2024]. -/
theorem kl_lossFixedPoint_eq {X : Type*} [Fintype X] (ε : ℝ) (hε : 0 < ε) (p q : FinDist X) :
    lossFixedPoint (clippedKL ε) p.prob (support p) q.prob (support q)
      = ∑ x ∈ support p, p.prob x * Real.log (p.prob x / ε) := by
  have hleft : ∀ a : ℝ, clippedKL ε a 0 = a * Real.log (a / ε) := by
    intro a
    simp [clippedKL, max_eq_right (le_of_lt hε)]
  have hright : ∀ b : ℝ, clippedKL ε 0 b = 0 := by
    intro b
    simp [clippedKL]
  unfold lossFixedPoint
  rw [Finset.sum_congr rfl fun x _ => hleft (p.prob x),
    Finset.sum_congr rfl fun x _ => hright (q.prob x), Finset.sum_const_zero, add_zero]

/-- For positive `ε`, the separated-support reverse clipped relative-entropy loss is the support
sum of `q.prob x * Real.log (q.prob x / ε)`. See [RudolphEtAl2024]. -/
theorem revKl_lossFixedPoint_eq {X : Type*} [Fintype X] (ε : ℝ) (hε : 0 < ε) (p q : FinDist X) :
    lossFixedPoint (clippedKLRev ε) p.prob (support p) q.prob (support q)
      = ∑ x ∈ support q, q.prob x * Real.log (q.prob x / ε) := by
  have hleft : ∀ a : ℝ, clippedKLRev ε a 0 = 0 := by
    intro a
    simp [clippedKLRev]
  have hright : ∀ b : ℝ, clippedKLRev ε 0 b = b * Real.log (b / ε) := by
    intro b
    simp [clippedKLRev, max_eq_right (le_of_lt hε)]
  unfold lossFixedPoint
  rw [Finset.sum_congr rfl fun x _ => hleft (p.prob x),
    Finset.sum_congr rfl fun x _ => hright (q.prob x), Finset.sum_const_zero, zero_add]

end Qatlib.Papers.Trainability23.PairwiseLoss
