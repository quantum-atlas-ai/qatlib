/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HammingDist09.MainResults.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic

/-!
# Perfect discrimination and constant-distance codes

This module proves the query-state and code-distance implications underlying Lemma 4.1 of
[MeyerPommersheim2009]. The states `queryState` encode a Boolean concept family using two
response states, and their Gram entries are expressed in terms of `hammingDist`.

Perfect discrimination forces these states to be orthogonal, which gives a common distance at
least half the input-domain size. With equally many concepts and inputs and an even domain size
greater than two, the common distance is exactly half the domain size and the learning matrix
has Hadamard columns.

## Main statements

* `perfect_discrimination_orthogonal`: derives orthogonality from perfect measurement
  discrimination.
* `constant_distance_code_half`: identifies the common distance in the square even-size case.
* `lemma_4_1`: combines the constant-distance and Hadamard conclusions.

## References

* [Meyer and Pommersheim, 2009][MeyerPommersheim2009]
-/

set_option warningAsError false

set_option maxHeartbeats 1000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.HammingDist09.MainResults.Distance

noncomputable section

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- Normalized states that a positive semidefinite measurement distinguishes perfectly are
pairwise orthogonal. -/
lemma perfect_discrimination_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → H → ℂ) (hA : ∀ i, star (A i) ⬝ᵥ A i = 1)
    (P : ι → Matrix H H ℂ) (hP : ∀ i, (P i).PosSemidef)
    (hsum : ∑ i, P i = 1)
    (hperf : ∀ i, star (A i) ⬝ᵥ ((P i) *ᵥ A i) = 1) :
    ∀ i j, i ≠ j → star (A i) ⬝ᵥ A j = 0 := by

  have hker : ∀ i j : ι, i ≠ j → P j *ᵥ A i = 0 := by
    intro i j hij
    have hY : (∑ k ∈ Finset.univ.erase i, P k) = 1 - P i := by
      have h := Finset.sum_erase_add (Finset.univ) P (Finset.mem_univ i)
      rw [hsum] at h
      exact eq_sub_iff_add_eq.mpr h
    have hYpsd : (∑ k ∈ Finset.univ.erase i, P k).PosSemidef :=
      posSemidef_sum _ (fun k _ => hP k)
    have hq : star (A i) ⬝ᵥ ((∑ k ∈ Finset.univ.erase i, P k) *ᵥ A i) = 0 := by
      rw [hY, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hA i, hperf i,
        sub_self]
    have hYA : (∑ k ∈ Finset.univ.erase i, P k) *ᵥ A i = 0 :=
      hYpsd.dotProduct_mulVec_zero_iff.mp hq

    have hf_nonneg : ∀ k : ι, 0 ≤ (star (A i) ⬝ᵥ (P k *ᵥ A i)).re := by
      intro k
      have h := (hP k).dotProduct_mulVec_nonneg (A i)
      exact (Complex.nonneg_iff.mp h).1
    have hsum_re : (∑ k ∈ Finset.univ.erase i, (star (A i) ⬝ᵥ (P k *ᵥ A i)).re) = 0 := by
      rw [← Complex.re_sum]
      have h1 : (∑ k ∈ Finset.univ.erase i, star (A i) ⬝ᵥ (P k *ᵥ A i))
          = star (A i) ⬝ᵥ ((∑ k ∈ Finset.univ.erase i, P k) *ᵥ A i) := by
        rw [Matrix.sum_mulVec, dotProduct_sum]
      rw [h1, hq, Complex.zero_re]
    have hjmem : j ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
    have hzj : (star (A i) ⬝ᵥ (P j *ᵥ A i)).re = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hf_nonneg k)).mp hsum_re j hjmem
    have hz : star (A i) ⬝ᵥ (P j *ᵥ A i) = 0 := by
      refine Complex.ext hzj ?_
      have h := (hP j).dotProduct_mulVec_nonneg (A i)
      exact (Complex.nonneg_iff.mp h).2.symm
    exact (hP j).dotProduct_mulVec_zero_iff.mp hz
  intro i j hij

  have hAj : A j = ∑ k, P k *ᵥ A j := by
    conv_lhs => rw [← Matrix.one_mulVec (A j), ← hsum]
    rw [Matrix.sum_mulVec]
  have hterm : ∀ k ∈ (Finset.univ : Finset ι), star (A i) ⬝ᵥ (P k *ᵥ A j) = 0 := by
    intro k _
    by_cases hkj : k = j
    · rw [hkj]
      rw [Matrix.dotProduct_mulVec, ← (hP j).1.eq, ← Matrix.star_mulVec, hker i j hij]
      simp
    · rw [hker j k (fun h : j = k => hkj h.symm), dotProduct_zero]
  rw [hAj, dotProduct_sum]
  exact Finset.sum_eq_zero hterm

section QueryDefs

variable {X C : Type*} [Fintype X]

/-- The query-state amplitude at `(x, b)`, given by `a * u (f c x) b`. -/
def queryState (f : C → X → ZMod 2) (u : ZMod 2 → Fin 2 → ℂ) (a : ℂ) (c : C) :
    X × Fin 2 → ℂ :=
  fun p => a * u (f c p.1) p.2

/-- When the squared modulus of `a` is the inverse domain size, the query-state inner product is
the average of the response-state inner products. -/
lemma queryState_gram (f : C → X → ZMod 2) (u : ZMod 2 → Fin 2 → ℂ) (a : ℂ)
    (ha : star a * a = ((Fintype.card X : ℂ))⁻¹) (c c' : C) :
    star (queryState f u a c) ⬝ᵥ queryState f u a c'
      = ((Fintype.card X : ℂ))⁻¹ * ∑ x : X, star (u (f c x)) ⬝ᵥ u (f c' x) := by
  simp only [dotProduct, queryState, Pi.star_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [star_mul]
  show star (u (f c x) b) * star a * (a * u (f c' x) b)
      = ((Fintype.card X : ℂ))⁻¹ * (star (u (f c x) b) * u (f c' x) b)
  rw [show star (u (f c x) b) * star a * (a * u (f c' x) b)
      = (star a * a) * (star (u (f c x) b) * u (f c' x) b) by ring, ha]

/-- For normalized response states with common real cross inner product `lam`, the query-state
Gram entry is the domain-size-normalized sum of the agreement count and `lam` times the
Hamming distance. -/
lemma queryState_gram_card (f : C → X → ZMod 2) (u : ZMod 2 → Fin 2 → ℂ) (a : ℂ)
    (ha : star a * a = ((Fintype.card X : ℂ))⁻¹) (lam : ℝ)
    (hu : ∀ y, star (u y) ⬝ᵥ u y = 1)
    (huv : ∀ y y', y ≠ y' → star (u y) ⬝ᵥ u y' = (lam : ℂ)) (c c' : C) :
    star (queryState f u a c) ⬝ᵥ queryState f u a c'
      = ((Fintype.card X : ℂ))⁻¹ *
          (((Fintype.card X - hammingDist f c c' : ℕ) : ℂ)
            + (hammingDist f c c' : ℂ) * (lam : ℂ)) := by
  rw [queryState_gram f u a ha c c']
  congr 1
  have hinner : ∀ x : X,
      star (u (f c x)) ⬝ᵥ u (f c' x) = if f c x = f c' x then (1 : ℂ) else (lam : ℂ) := by
    intro x
    by_cases h : f c x = f c' x
    · rw [if_pos h, h, hu]
    · rw [if_neg h, huv _ _ h]
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  have hdN : hammingDist f c c' ≤ Fintype.card X := by
    rw [hammingDist]
    exact Finset.card_filter_le _ _
  have hsub : (Finset.univ.filter (fun x => f c x = f c' x)).card
      = Fintype.card X - hammingDist f c c' := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset X))
      (p := fun x => f c x = f c' x)
    simp only [Finset.card_univ] at h
    have hd : (Finset.univ.filter (fun x => ¬ f c x = f c' x)).card
        = hammingDist f c c' := rfl
    omega
  have h1 : (∑ x : X, (if f c x = f c' x then (1 : ℂ) else 0))
      = ((Fintype.card X - hammingDist f c c' : ℕ) : ℂ) := by
    rw [sum_ite_one_eq_card, hsub]
  have h2 : (∑ x : X, (if f c x = f c' x then (0 : ℂ) else 1))
      = (hammingDist f c c' : ℂ) := by
    rw [show (∑ x : X, (if f c x = f c' x then (0 : ℂ) else 1))
        = ∑ x : X, (if f c x ≠ f c' x then (1 : ℂ) else 0) from
      Finset.sum_congr rfl (fun x _ => by by_cases h : f c x = f c' x <;> simp [h])]
    rw [sum_ite_one_eq_card]
    rfl
  calc (∑ x : X, (if f c x = f c' x then (1 : ℂ) else (lam : ℂ)))
      = ∑ x : X, ((if f c x = f c' x then (1 : ℂ) else 0)
          + (lam : ℂ) * (if f c x = f c' x then (0 : ℂ) else 1)) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : f c x = f c' x <;> simp [h]
    _ = (∑ x : X, (if f c x = f c' x then (1 : ℂ) else 0))
          + (lam : ℂ) * (∑ x : X, (if f c x = f c' x then (0 : ℂ) else 1)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = ((Fintype.card X - hammingDist f c c' : ℕ) : ℂ)
          + (lam : ℂ) * (hammingDist f c c' : ℂ) := by rw [h1, h2]
    _ = ((Fintype.card X - hammingDist f c c' : ℕ) : ℂ)
          + (hammingDist f c c' : ℂ) * (lam : ℂ) := by rw [mul_comm]

/-- Perfect discrimination of the specified query states forces all distinct concepts to have a
common Hamming distance at least half the input-domain size, assuming at least two concepts.
[MeyerPommersheim2009]. -/
theorem lemma_4_1_perfect [DecidableEq X] [Fintype C] [DecidableEq C]
    (f : C → X → ZMod 2) (u : ZMod 2 → Fin 2 → ℂ) (a : ℂ) (lam : ℝ)
    (hN : 0 < Fintype.card X) (hlam : -1 ≤ lam) (hlam1 : lam ≤ 1)
    (ha : star a * a = ((Fintype.card X : ℂ))⁻¹)
    (hu : ∀ y, star (u y) ⬝ᵥ u y = 1)
    (huv : ∀ y y', y ≠ y' → star (u y) ⬝ᵥ u y' = (lam : ℂ))
    (P : C → Matrix (X × Fin 2) (X × Fin 2) ℂ) (hP : ∀ c, (P c).PosSemidef)
    (hsum : ∑ c, P c = 1)
    (hperf : ∀ c, star (queryState f u a c) ⬝ᵥ ((P c) *ᵥ queryState f u a c) = 1)
    (hex : ∃ c c' : C, c ≠ c') :
    ∃ d : ℕ, (Fintype.card X : ℝ) / 2 ≤ (d : ℝ) ∧
      ∀ c c' : C, c ≠ c' → hammingDist f c c' = d := by
  have hunit : ∀ c : C, star (queryState f u a c) ⬝ᵥ queryState f u a c = 1 := by
    intro c
    rw [queryState_gram_card f u a ha lam hu huv c c]
    have hd : hammingDist f c c = 0 := by simp [hammingDist]
    rw [hd, Nat.sub_zero, Nat.cast_zero, zero_mul, add_zero]
    have hNc : (Fintype.card X : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mp hN)
    field_simp
  have horth := perfect_discrimination_orthogonal (queryState f u a) hunit P hP hsum hperf
  have hgram : ∀ c c' : C, c ≠ c' →
      (Fintype.card X : ℝ) - (hammingDist f c c' : ℝ)
        + lam * (hammingDist f c c' : ℝ) = 0 := by
    intro c c' hcc
    have h := horth c c' hcc
    rw [queryState_gram_card f u a ha lam hu huv c c'] at h
    have hNc : (Fintype.card X : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mp hN)
    have hmul : ((Fintype.card X : ℂ)) *
        (((Fintype.card X : ℂ))⁻¹ *
          (((Fintype.card X - hammingDist f c c' : ℕ) : ℂ)
            + (hammingDist f c c' : ℂ) * (lam : ℂ))) = 0 := by rw [h, mul_zero]
    rw [← mul_assoc, mul_inv_cancel₀ hNc, one_mul] at hmul
    have hre := congrArg Complex.re hmul
    simp only [Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.natCast_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, mul_zero, sub_zero] at hre
    have hdN : hammingDist f c c' ≤ Fintype.card X := by
      rw [hammingDist]
      exact Finset.card_filter_le _ _
    rw [Nat.cast_sub hdN] at hre
    linarith
  exact lemma_4_1_distance f lam hN hlam hlam1 hgram hex

end QueryDefs

section Plotkin

variable {X C : Type*} [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

omit [DecidableEq X] in

/-- For an even domain size greater than two and equally many Boolean concepts, a common
pairwise distance at least half the domain size must equal exactly half that size.
[MeyerPommersheim2009]. -/
theorem constant_distance_code_half (f : C → X → ZMod 2) (d : ℕ)
    (hN2 : 2 < Fintype.card X) (hcard : Fintype.card C = Fintype.card X)
    (heven : Even (Fintype.card X))
    (hcode : ∀ c c' : C, c ≠ c' → hammingDist f c c' = d)
    (hge : (Fintype.card X : ℝ) / 2 ≤ (d : ℝ)) :
    2 * d = Fintype.card X := by
  classical

  have hsquare : ∀ x : X, (∑ c : C, learningMatrix f x c) ^ 2
      = ∑ c : C, ∑ c' : C, learningMatrix f x c * learningMatrix f x c' := by
    intro x
    rw [sq, Fintype.sum_mul_sum]
  have hdouble : (∑ x : X, (∑ c : C, learningMatrix f x c) ^ 2)
      = ∑ c : C, ∑ c' : C, ∑ x : X, learningMatrix f x c * learningMatrix f x c' := by
    rw [Finset.sum_congr rfl (fun x _ => hsquare x)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_comm]
  have hinner : ∀ c c' : C, (∑ x : X, learningMatrix f x c * learningMatrix f x c')
      = (Fintype.card X : ℤ) - 2 * (hammingDist f c c' : ℤ) := by
    intro c c'
    simpa only [learningMatrix] using learningMatrix_col_inner f c c'

  have hper : ∀ c : C,
      (∑ c' : C, ((Fintype.card X : ℤ) - 2 * (hammingDist f c c' : ℤ)))
        = (Fintype.card X : ℤ)
          + ((Fintype.card C : ℤ) - 1) * ((Fintype.card X : ℤ) - 2 * (d : ℤ)) := by
    intro c
    have hdc : hammingDist f c c = 0 := by simp [hammingDist]
    rw [← Finset.sum_erase_add (Finset.univ)
      (fun c' => ((Fintype.card X : ℤ) - 2 * (hammingDist f c c' : ℤ)))
      (Finset.mem_univ c), hdc]
    have hconst : ∀ c' ∈ Finset.univ.erase c,
        ((Fintype.card X : ℤ) - 2 * (hammingDist f c c' : ℤ))
          = ((Fintype.card X : ℤ) - 2 * (d : ℤ)) := by
      intro c' hc'
      have hne : c' ≠ c := (Finset.mem_erase.mp hc').1
      rw [hcode c c' (fun h => hne h.symm)]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ]
    have hc1 : 1 ≤ Fintype.card C := by omega
    rw [nsmul_eq_mul, Nat.cast_sub hc1]
    ring
  have htot : (∑ c : C, ∑ c' : C,
        ((Fintype.card X : ℤ) - 2 * (hammingDist f c c' : ℤ)))
      = (Fintype.card C : ℤ) * (Fintype.card X : ℤ)
        + (Fintype.card C : ℤ) * ((Fintype.card C : ℤ) - 1)
            * ((Fintype.card X : ℤ) - 2 * (d : ℤ)) := by
    rw [Finset.sum_congr rfl (fun c _ => hper c), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  have hnonneg : (0 : ℤ) ≤ (∑ x : X, (∑ c : C, learningMatrix f x c) ^ 2) := by
    apply Finset.sum_nonneg
    intro x _
    exact sq_nonneg _
  have hdouble' : (∑ x : X, (∑ c : C, learningMatrix f x c) ^ 2)
      = ∑ c : C, ∑ c' : C,
          ((Fintype.card X : ℤ) - 2 * (hammingDist f c c' : ℤ)) := by
    rw [hdouble]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro c' _
    exact hinner c c'
  have hnonneg' : (0 : ℤ) ≤ (Fintype.card C : ℤ) * (Fintype.card X : ℤ)
      + (Fintype.card C : ℤ) * ((Fintype.card C : ℤ) - 1)
          * ((Fintype.card X : ℤ) - 2 * (d : ℤ)) := by
    rw [← htot, ← hdouble']
    exact hnonneg

  have hkey : (0 : ℤ) ≤ (Fintype.card X : ℤ) * (Fintype.card X : ℤ)
      + (Fintype.card X : ℤ) * ((Fintype.card X : ℤ) - 1)
          * ((Fintype.card X : ℤ) - 2 * (d : ℤ)) := by
    simpa [hcard] using hnonneg'
  have hfac : (0 : ℤ) ≤ (Fintype.card X : ℤ) *
      ((Fintype.card X : ℤ)
        + ((Fintype.card X : ℤ) - 1) * ((Fintype.card X : ℤ) - 2 * (d : ℤ))) := by
    have heq : (Fintype.card X : ℤ) * (Fintype.card X : ℤ)
        + (Fintype.card X : ℤ) * ((Fintype.card X : ℤ) - 1)
            * ((Fintype.card X : ℤ) - 2 * (d : ℤ))
        = (Fintype.card X : ℤ) * ((Fintype.card X : ℤ)
            + ((Fintype.card X : ℤ) - 1) * ((Fintype.card X : ℤ) - 2 * (d : ℤ))) := by
      ring
    rwa [heq] at hkey
  have hNpos : (0 : ℤ) < (Fintype.card X : ℤ) := by
    have h : 0 < Fintype.card X := by omega
    exact_mod_cast h
  have hbase : (0 : ℤ) ≤ (Fintype.card X : ℤ)
      + ((Fintype.card X : ℤ) - 1) * ((Fintype.card X : ℤ) - 2 * (d : ℤ)) :=
    (mul_nonneg_iff_of_pos_left hNpos).mp hfac
  have hprod : ((Fintype.card X : ℤ) - 1) * (2 * (d : ℤ) - (Fintype.card X : ℤ))
      ≤ (Fintype.card X : ℤ) := by
    have hneg : ((Fintype.card X : ℤ) - 1) * ((Fintype.card X : ℤ) - 2 * (d : ℤ))
        = -(((Fintype.card X : ℤ) - 1) * (2 * (d : ℤ) - (Fintype.card X : ℤ))) := by
      ring
    linarith

  have hz_nonneg : (0 : ℤ) ≤ 2 * (d : ℤ) - (Fintype.card X : ℤ) := by
    have h1 : (((Fintype.card X : ℤ) : ℝ) ≤ ((2 * (d : ℤ) : ℤ) : ℝ)) := by
      push_cast
      linarith
    have h2 : (Fintype.card X : ℤ) ≤ 2 * (d : ℤ) := Int.cast_le.mp h1
    linarith
  have hz_lt : 2 * (d : ℤ) - (Fintype.card X : ℤ) < 2 := by
    by_contra hcon
    have hcon' : 2 ≤ 2 * (d : ℤ) - (Fintype.card X : ℤ) := not_lt.mp hcon
    have hN1 : (0 : ℤ) ≤ (Fintype.card X : ℤ) - 1 := by omega
    have hstep : 2 * ((Fintype.card X : ℤ) - 1)
        ≤ ((Fintype.card X : ℤ) - 1) * (2 * (d : ℤ) - (Fintype.card X : ℤ)) := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hcon' hN1
    have hle : 2 * ((Fintype.card X : ℤ) - 1) ≤ (Fintype.card X : ℤ) :=
      le_trans hstep hprod
    omega

  obtain ⟨k, hk⟩ := heven
  have hcast : (Fintype.card X : ℤ) = 2 * (k : ℤ) := by
    have h : (Fintype.card X : ℤ) = (k : ℤ) + (k : ℤ) := by exact_mod_cast hk
    rw [h]; ring
  have hz0 : 2 * (d : ℤ) - (Fintype.card X : ℤ) = 0 := by
    have hz_even : 2 * (d : ℤ) - (Fintype.card X : ℤ) = 2 * ((d : ℤ) - (k : ℤ)) := by
      rw [hcast]; ring
    have hk0 : (d : ℤ) - (k : ℤ) = 0 := by omega
    rw [hz_even, hk0]; ring
  have hfinal : 2 * (d : ℤ) = (Fintype.card X : ℤ) := by
    linarith
  exact_mod_cast hfinal

omit [DecidableEq X] in

/-- For an even domain size greater than two and equally many concepts, constant pairwise
Hamming distance at least half the domain size implies the Hadamard column condition.
[MeyerPommersheim2009]. -/
theorem lemma_4_1_hadamard_of_constant_distance (f : C → X → ZMod 2) (d : ℕ)
    (hN2 : 2 < Fintype.card X) (hcard : Fintype.card C = Fintype.card X)
    (heven : Even (Fintype.card X))
    (hcode : ∀ c c' : C, c ≠ c' → hammingDist f c c' = d)
    (hge : (Fintype.card X : ℝ) / 2 ≤ (d : ℝ)) :
    IsHadamardColumns (learningMatrix f) :=
  lemma_4_1_hadamard f d hN2 hcard heven hcode
    (constant_distance_code_half f d hN2 hcard heven hcode hge)

/-- Perfect discrimination of the specified query states forces a common pairwise Hamming
distance at least half the domain size. If the numbers of inputs and concepts agree and the
domain size is even and greater than two, the learning matrix has Hadamard columns.
[MeyerPommersheim2009]. -/
theorem lemma_4_1 (f : C → X → ZMod 2) (u : ZMod 2 → Fin 2 → ℂ) (a : ℂ) (lam : ℝ)
    (hN : 0 < Fintype.card X) (hlam : -1 ≤ lam) (hlam1 : lam ≤ 1)
    (ha : star a * a = ((Fintype.card X : ℂ))⁻¹)
    (hu : ∀ y, star (u y) ⬝ᵥ u y = 1)
    (huv : ∀ y y', y ≠ y' → star (u y) ⬝ᵥ u y' = (lam : ℂ))
    (P : C → Matrix (X × Fin 2) (X × Fin 2) ℂ) (hP : ∀ c, (P c).PosSemidef)
    (hsum : ∑ c, P c = 1)
    (hperf : ∀ c, star (queryState f u a c) ⬝ᵥ ((P c) *ᵥ queryState f u a c) = 1)
    (hex : ∃ c c' : C, c ≠ c') :
    (∃ d : ℕ, (Fintype.card X : ℝ) / 2 ≤ (d : ℝ) ∧
        ∀ c c' : C, c ≠ c' → hammingDist f c c' = d) ∧
      (Fintype.card C = Fintype.card X → 2 < Fintype.card X → Even (Fintype.card X) →
        IsHadamardColumns (learningMatrix f)) := by
  have hdist := lemma_4_1_perfect f u a lam hN hlam hlam1 ha hu huv P hP hsum hperf hex
  refine ⟨hdist, ?_⟩
  intro hcard hN2 heven
  obtain ⟨d, hge, hcode⟩ := hdist
  exact lemma_4_1_hadamard_of_constant_distance f d hN2 hcard heven hcode hge

end Plotkin

end

end Qatlib.Papers.HammingDist09.MainResults.Distance
