/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ApproxDegree20.MainResults.Spectral.SensitivityAdjacency

@[expose] public section

/-!
# Sensitivity is bounded by the square of the spectral sensitivity

Source: arXiv:2010.12629v1, Appendix A.4, Lemma 34 (page 32): for every total Boolean function
`f` the sensitivity `s(f)` satisfies `s(f) ≤ λ(f)²`.

The sensitivity graph of `f` contains a star centred at an input `x` of maximum sensitivity with
one leaf for each sensitive coordinate.  Testing the operator norm on the vector
`√s · e_x + ∑_{leaf} e_l`, whose squared norm is `2s`, exhibits `λ(f)² ≥ s` for
`s = s_x(f) = s(f)`.

Boundary: total Boolean functions on an arbitrary finite coordinate type `I`; partially defined
functions are not covered.  The case `s(f) = 0` is handled separately because the test vector
is then zero.
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

/-- An input is never a sensitive neighbour of itself. -/
theorem not_mem_image_flipBit_self (f : (I → Bool) → Bool) (x : I → Bool) :
    x ∉ (sensitiveAt f x).image (flipBit x) := by
  rw [Finset.mem_image]
  rintro ⟨i, -, hi⟩
  have h : flipBit x i i = x i := by rw [hi]
  have hflip : flipBit x i i = !(x i) := by simp [flipBit]
  rw [hflip] at h
  cases hx : x i <;> simp [hx] at h

/-- The sensitivity is at most the square of the spectral sensitivity. -/
theorem sensitivity_le_spectralSensitivity_sq (f : (I → Bool) → Bool) :
    (sensitivity f : ℝ) ≤ spectralSensitivity f ^ 2 := by
  classical
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (I → Bool))
    ⟨fun _ => false, Finset.mem_univ _⟩ (fun y => sensitivityAt f y)
  have hx' : (sensitivity f : ℝ) = (sensitivityAt f x : ℝ) := Nat.cast_inj.mpr hx
  rw [hx']
  set L : Finset (I → Bool) := (sensitiveAt f x).image (flipBit x) with hL
  by_cases hs : sensitivityAt f x = 0
  · simp only [hs, Nat.cast_zero]
    positivity
  have hxL : x ∉ L := not_mem_image_flipBit_self f x
  have hfilter : Finset.univ.filter (fun y : I → Bool => y ∈ L) = L := by
    ext y
    simp
  set s : ℝ := (sensitivityAt f x : ℝ) with hsd
  have hLcard : (L.card : ℝ) = s := by
    rw [hL, Finset.card_image_of_injective _ (flipBit_injective x), hsd]
    simp only [sensitivityAt]
  have hspos : 0 < s := by
    rw [hsd]
    exact_mod_cast Nat.pos_of_ne_zero hs
  set v : QState (I → Bool) :=
    fun y => if y = x then (Real.sqrt s : ℂ) else if y ∈ L then 1 else 0 with hv
  have hvx : v x = (Real.sqrt s : ℂ) := by simp [hv]
  have hvl : ∀ l ∈ L, v l = 1 := by
    intro l hl
    simp only [hv]
    rw [ite_eq_right (fun h : l = x => hxL (h ▸ hl)), ite_eq_left hl]
  have hvz : ∀ z, z ≠ x → z ∉ L → v z = 0 := by
    intro z hzx hzL
    simp only [hv]
    rw [ite_eq_right hzx, ite_eq_right hzL]
  have hvsq : ‖toEuclidean_fromVec v‖ ^ 2 = 2 * s := by
    rw [norm_toEuclidean_fromVec_sq]
    have hxpart : (∑ y ∈ Finset.univ.filter (fun y => ¬ y ∈ L), ‖v y‖ ^ 2) = s := by
      have hsingle : (∑ y ∈ Finset.univ.filter (fun y => ¬ y ∈ L), ‖v y‖ ^ 2)
          = ‖v x‖ ^ 2 := by
        refine Finset.sum_eq_single x ?_ ?_
        · intro y hy hyx
          rw [Finset.mem_filter] at hy
          rw [hvz y hyx hy.2, norm_zero]
          ring
        · intro hxnot
          exact absurd (by simp [hxL]) hxnot
      rw [hsingle, hvx, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hspos.le]
    have hLpart : (∑ y ∈ L, ‖v y‖ ^ 2) = (L.card : ℝ) := by
      have hone : ∀ y ∈ L, ‖v y‖ ^ 2 = (1 : ℝ) := by
        intro y hy
        rw [hvl y hy]
        simp
      rw [Finset.sum_congr rfl hone]
      simp
    rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (I → Bool)))
      (p := fun y => y ∈ L)]
    rw [hfilter, hxpart, hLpart, hLcard]
    ring
  have hAx : ‖(sensAdjacency f *ᵥ v) x‖ = s := by
    have hcoord : (sensAdjacency f *ᵥ v) x = ((L.card : ℕ) : ℂ) := by
      simp only [Matrix.mulVec, dotProduct]
      have hsupp : ∀ y ∈ (Finset.univ : Finset (I → Bool)), y ∉ L →
          sensAdjacency f x y * v y = 0 := by
        intro y _ hyL
        by_cases hyx : y = x
        · subst hyx
          simp [sensAdjacency]
        · rw [hvz y hyx hyL, mul_zero]
      rw [← Finset.sum_subset (Finset.subset_univ L) hsupp]
      have hone : ∀ y ∈ L, sensAdjacency f x y * v y = 1 := by
        intro y hyL
        have hmem := (mem_image_flipBit_iff f x y).mp hyL
        simp only [sensAdjacency]
        rw [ite_eq_left hmem, one_mul, hvl y hyL]
      rw [Finset.sum_congr rfl hone]
      simp
    rw [hcoord, Complex.norm_natCast, hLcard]
  have hAl : ∀ l ∈ L, s ≤ ‖(sensAdjacency f *ᵥ v) l‖ ^ 2 := by
    intro l hl
    have hcoord : (sensAdjacency f *ᵥ v) l = (Real.sqrt s : ℂ) := by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single x]
      · have hmem := (mem_image_flipBit_iff f x l).mp hl
        rw [sensAdjacency_symm f x l]
        simp only [sensAdjacency]
        rw [ite_eq_left hmem, one_mul, hvx]
      · intro z _ hzx
        rcases Classical.em (z ∈ L) with hzL | hzL
        · have hzmem := (mem_image_flipBit_iff f x z).mp hzL
          have hlmem := (mem_image_flipBit_iff f x l).mp hl
          have hval : f l = f z := by
            have h1 : f l ≠ f x := Ne.symm hlmem.2
            have h2 : f z ≠ f x := Ne.symm hzmem.2
            cases hx1 : f x <;> cases hl1 : f l <;> cases hz1 : f z <;> simp_all
          simp only [sensAdjacency]
          rw [ite_eq_right (fun hc => hc.2 hval), zero_mul]
        · rw [hvz z hzx hzL, mul_zero]
      · exact fun h => absurd (Finset.mem_univ x) h
    rw [hcoord, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt hspos.le]
  have hAvsq : 2 * s ^ 2 ≤ ‖toEuclidean_fromVec (sensAdjacency f *ᵥ v)‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq]
    rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (I → Bool)))
      (p := fun y => y ∈ L)]
    rw [hfilter]
    have hxpart : s ^ 2
        ≤ ∑ y ∈ Finset.univ.filter (fun y => ¬ y ∈ L),
            ‖(sensAdjacency f *ᵥ v) y‖ ^ 2 := by
      have hle := Finset.single_le_sum
        (f := fun y => ‖(sensAdjacency f *ᵥ v) y‖ ^ 2)
        (fun y _ => by positivity) (show x ∈ Finset.univ.filter (fun y => ¬ y ∈ L) by
          simp [hxL])
      rw [hAx] at hle
      exact hle
    have hLpart : (L.card : ℝ) * s
        ≤ ∑ y ∈ L, ‖(sensAdjacency f *ᵥ v) y‖ ^ 2 := by
      have h1 : (∑ y ∈ L, s) ≤ ∑ y ∈ L, ‖(sensAdjacency f *ᵥ v) y‖ ^ 2 :=
        Finset.sum_le_sum fun y hy => hAl y hy
      rwa [Finset.sum_const, nsmul_eq_mul] at h1
    have h2 : s * s ≤ ∑ y ∈ L, ‖(sensAdjacency f *ᵥ v) y‖ ^ 2 := by
      have h3 := hLpart
      rw [hLcard] at h3
      exact h3
    nlinarith [hxpart, h2]
  have hle := l2_norm_mulVec_fromVec_le (sensAdjacency f) v
  have hnorm : ‖toEuclidean_fromVec (sensAdjacency f *ᵥ v)‖ ^ 2
      ≤ spectralSensitivity f ^ 2 * (‖toEuclidean_fromVec v‖ ^ 2) := by
    have h2 : (0 : ℝ) ≤ spectralSensitivity f * ‖toEuclidean_fromVec v‖ :=
      mul_nonneg (spectralSensitivity_nonneg f) (norm_nonneg _)
    have h3 := (sq_le_sq₀ (norm_nonneg _) h2).mpr hle
    rw [mul_pow] at h3
    exact h3
  rw [hvsq] at hnorm
  nlinarith [hAvsq, hnorm, hspos]

end Qatlib.Papers.ApproxDegree20.MainResults.Spectral
