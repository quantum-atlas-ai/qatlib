/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BosonFock.BosonOperators.BosonPermanent
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.Exponential
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib

set_option autoImplicit false

namespace Qatlib.Concepts.CountingClasses.ClassTransport

open Qatlib

open scoped BigOperators Nat ComplexConjugate

noncomputable def loTvDist {ι : Type} [Fintype ι] (p q : ι → ℝ) : ℝ := (∑ i, |p i - q i|) / 2

theorem loTvDist_nonneg {ι : Type} [Fintype ι] (p q : ι → ℝ) : 0 ≤ loTvDist p q := by
  unfold loTvDist
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  · norm_num

theorem loTvDist_triangle {ι : Type} [Fintype ι] (p q r : ι → ℝ) :
    loTvDist p r ≤ loTvDist p q + loTvDist q r := by
  have h : ∀ i, |p i - r i| ≤ |p i - q i| + |q i - r i| := by
    intro i
    calc |p i - r i| = |(p i - q i) + (q i - r i)| := by congr 1; ring
      _ ≤ |p i - q i| + |q i - r i| := abs_add_le _ _
  have hs : (∑ i, |p i - r i|) ≤ (∑ i, |p i - q i|) + ∑ i, |q i - r i| := by
    have h' := Finset.sum_le_sum
      (s := Finset.univ)
      (f := fun i => |p i - r i|) (g := fun i => |p i - q i| + |q i - r i|)
      (fun i _ => h i)
    rwa [Finset.sum_add_distrib] at h'
  unfold loTvDist
  linarith

theorem loTvDist_apply_le {ι : Type} [Fintype ι] (p q : ι → ℝ) (i₀ : ι) :
    |p i₀ - q i₀| ≤ 2 * loTvDist p q := by
  have h1 : |p i₀ - q i₀| ≤ ∑ i, |p i - q i| :=
    Finset.single_le_sum (f := fun i => |p i - q i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i₀)
  unfold loTvDist
  linarith

noncomputable def loBeamSplitter (m : ℕ) (i j : Fin m) (θ ph : ℝ) :
    Matrix (Fin m) (Fin m) ℂ :=
  if i = j then 1 else Matrix.of fun a b =>
    if a = i ∧ b = i then Complex.ofReal (Real.cos θ)
    else if a = i ∧ b = j then -(Complex.exp (ph * Complex.I) * Complex.ofReal (Real.sin θ))
    else if a = j ∧ b = i then Complex.exp (-(ph * Complex.I)) * Complex.ofReal (Real.sin θ)
    else if a = j ∧ b = j then Complex.ofReal (Real.cos θ)
    else if a = b then 1 else 0

private theorem loConjExpIP (ph : ℝ) :
    conj (Complex.exp (ph * Complex.I)) = Complex.exp (-(ph * Complex.I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

private theorem loConjExpIM (ph : ℝ) :
    conj (Complex.exp (-(ph * Complex.I))) = Complex.exp (ph * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

private theorem loBS_val_ii {m : ℕ} (i j : Fin m) (θ ph : ℝ) (hij : i ≠ j) :
    loBeamSplitter m i j θ ph i i = Complex.ofReal (Real.cos θ) := by
  unfold loBeamSplitter
  rw [if_neg hij, Matrix.of_apply, if_pos ⟨rfl, rfl⟩]

private theorem loBS_val_ij {m : ℕ} (i j : Fin m) (θ ph : ℝ) (hij : i ≠ j) :
    loBeamSplitter m i j θ ph i j = -(Complex.exp (ph * Complex.I)
      * Complex.ofReal (Real.sin θ)) := by
  unfold loBeamSplitter
  rw [if_neg hij, Matrix.of_apply, if_neg (fun h => hij h.2.symm), if_pos ⟨rfl, rfl⟩]

private theorem loBS_val_ji {m : ℕ} (i j : Fin m) (θ ph : ℝ) (hij : i ≠ j) :
    loBeamSplitter m i j θ ph j i = Complex.exp (-(ph * Complex.I))
      * Complex.ofReal (Real.sin θ) := by
  unfold loBeamSplitter
  rw [if_neg hij, Matrix.of_apply, if_neg (fun h => hij h.1.symm),
    if_neg (fun h => hij h.1.symm), if_pos ⟨rfl, rfl⟩]

private theorem loBS_val_jj {m : ℕ} (i j : Fin m) (θ ph : ℝ) (hij : i ≠ j) :
    loBeamSplitter m i j θ ph j j = Complex.ofReal (Real.cos θ) := by
  unfold loBeamSplitter
  rw [if_neg hij, Matrix.of_apply, if_neg (fun h => hij h.1.symm),
    if_neg (fun h => hij h.1.symm), if_neg (fun h => hij h.2.symm), if_pos ⟨rfl, rfl⟩]

private theorem loBS_val_off {m : ℕ} (i j : Fin m) (θ ph : ℝ) (hij : i ≠ j) (k c : Fin m)
    (hki : k ≠ i) (hkj : k ≠ j) : loBeamSplitter m i j θ ph k c = if k = c then 1 else 0 := by
  unfold loBeamSplitter
  rw [if_neg hij, Matrix.of_apply, if_neg (fun h => hki h.1), if_neg (fun h => hki h.1),
    if_neg (fun h => hkj h.1), if_neg (fun h => hkj h.1)]

private theorem loBS_zero_col {m : ℕ} (i j : Fin m) (θ ph : ℝ) (hij : i ≠ j) (k c : Fin m)
    (hci : c ≠ i) (hcj : c ≠ j) (hkc : k ≠ c) : loBeamSplitter m i j θ ph k c = 0 := by
  unfold loBeamSplitter
  rw [if_neg hij, Matrix.of_apply, if_neg (fun h => hci h.2), if_neg (fun h => hcj h.2),
    if_neg (fun h => hci h.2), if_neg (fun h => hcj h.2), if_neg hkc]

theorem loBeamSplitter_mem_unitaryGroup (m : ℕ) (i j : Fin m) (θ ph : ℝ) :
    loBeamSplitter m i j θ ph ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  by_cases hij : i = j
  · rw [hij]
    have h1 : loBeamSplitter m j j θ ph = 1 := by simp [loBeamSplitter]
    rw [h1]
    exact Submonoid.one_mem _
  · rw [Matrix.mem_unitaryGroup_iff]
    ext a b
    simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Complex.star_def]
    have hcs : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
      have h := Real.sin_sq_add_cos_sq θ
      rw [pow_two, pow_two] at h
      linarith
    have hsc : Real.sin θ * Real.sin θ + Real.cos θ * Real.cos θ = 1 := by
      have h := Real.sin_sq_add_cos_sq θ
      rw [pow_two, pow_two] at h
      linarith
    have hP : Complex.exp (ph * Complex.I) * Complex.exp (-(ph * Complex.I)) = 1 := by
      rw [← Complex.exp_add]; simp
    have hPm : Complex.exp (-(ph * Complex.I)) * Complex.exp (ph * Complex.I) = 1 := by
      rw [← Complex.exp_add]; simp
    by_cases hai : a = i
    · rw [hai]
      by_cases hbi : b = i
      · rw [hbi]

        have hzero : ∀ k ∈ Finset.univ, k ∉ ({i, j} : Finset (Fin m)) →
            loBeamSplitter m i j θ ph i k * conj (loBeamSplitter m i j θ ph i k) = 0 := by
          intro k _ hk
          have h1 : k ≠ i := fun h => hk (by simp [h])
          have h2 : k ≠ j := fun h => hk (by simp [h])
          rw [loBS_zero_col i j θ ph hij i k h1 h2 (fun h => h1 h.symm)]
          ring
        have hsin : (Complex.exp (ph * Complex.I) * Complex.ofReal (Real.sin θ)) *
            (Complex.exp (-(ph * Complex.I)) * Complex.ofReal (Real.sin θ))
            = Complex.ofReal (Real.sin θ * Real.sin θ) := by
          have hre : (Complex.exp (ph * Complex.I) * Complex.ofReal (Real.sin θ)) *
              (Complex.exp (-(ph * Complex.I)) * Complex.ofReal (Real.sin θ))
              = (Complex.exp (ph * Complex.I) * Complex.exp (-(ph * Complex.I)))
                * (Complex.ofReal (Real.sin θ) * Complex.ofReal (Real.sin θ)) := by ring
          rw [hre, hP, one_mul, Complex.ofReal_mul]
        rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin m))) hzero,
          Finset.sum_pair hij, loBS_val_ii i j θ ph hij, loBS_val_ij i j θ ph hij,
          Complex.conj_ofReal, map_neg, map_mul, Complex.conj_ofReal,
          loConjExpIP, neg_mul_neg, ← Complex.ofReal_mul, hsin, ← Complex.ofReal_add, hcs,
          Complex.ofReal_one, Matrix.one_apply_eq]
      · by_cases hbj : b = j
        · rw [hbj]

          have hzero : ∀ k ∈ Finset.univ, k ∉ ({i, j} : Finset (Fin m)) →
              loBeamSplitter m i j θ ph i k * conj (loBeamSplitter m i j θ ph j k) = 0 := by
            intro k _ hk
            have h1 : k ≠ i := fun h => hk (by simp [h])
            have h2 : k ≠ j := fun h => hk (by simp [h])
            rw [loBS_zero_col i j θ ph hij i k h1 h2 (fun h => h1 h.symm)]
            ring
          rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin m))) hzero,
            Finset.sum_pair hij, loBS_val_ii i j θ ph hij, loBS_val_ji i j θ ph hij,
            loBS_val_ij i j θ ph hij, loBS_val_jj i j θ ph hij,
            map_mul, loConjExpIM, Complex.conj_ofReal, Complex.conj_ofReal,
            Matrix.one_apply_ne hij]
          ring
        · have hzero : ∀ k ∈ Finset.univ,
              loBeamSplitter m i j θ ph i k * conj (loBeamSplitter m i j θ ph b k) = 0 := by
            intro k _
            by_cases hki : k = i
            · rw [hki]
              rw [loBS_val_ii i j θ ph hij, loBS_val_off i j θ ph hij b i hbi hbj, if_neg hbi]
              simp
            · by_cases hkj : k = j
              · rw [hkj]
                rw [loBS_val_ij i j θ ph hij, loBS_val_off i j θ ph hij b j hbi hbj, if_neg hbj]
                simp
              · rw [loBS_zero_col i j θ ph hij i k hki hkj (fun h => hki h.symm)]
                simp
          rw [Finset.sum_eq_zero hzero, Matrix.one_apply_ne (fun h => hbi h.symm)]
    · by_cases haj : a = j
      · rw [haj]
        by_cases hbj : b = j
        · rw [hbj]

          have hzero : ∀ k ∈ Finset.univ, k ∉ ({i, j} : Finset (Fin m)) →
              loBeamSplitter m i j θ ph j k * conj (loBeamSplitter m i j θ ph j k) = 0 := by
            intro k _ hk
            have h1 : k ≠ i := fun h => hk (by simp [h])
            have h2 : k ≠ j := fun h => hk (by simp [h])
            rw [loBS_zero_col i j θ ph hij j k h1 h2 (fun h => h2 h.symm)]
            ring
          have hsin : (Complex.exp (-(ph * Complex.I)) * Complex.ofReal (Real.sin θ)) *
              (Complex.exp (ph * Complex.I) * Complex.ofReal (Real.sin θ))
              = Complex.ofReal (Real.sin θ * Real.sin θ) := by
            have hre : (Complex.exp (-(ph * Complex.I)) * Complex.ofReal (Real.sin θ)) *
                (Complex.exp (ph * Complex.I) * Complex.ofReal (Real.sin θ))
                = (Complex.exp (-(ph * Complex.I)) * Complex.exp (ph * Complex.I))
                  * (Complex.ofReal (Real.sin θ) * Complex.ofReal (Real.sin θ)) := by ring
            rw [hre, hPm, one_mul, Complex.ofReal_mul]
          rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin m))) hzero,
            Finset.sum_pair hij, loBS_val_ji i j θ ph hij, loBS_val_jj i j θ ph hij,
            map_mul, loConjExpIM, Complex.conj_ofReal, Complex.conj_ofReal,
            hsin, ← Complex.ofReal_mul, ← Complex.ofReal_add, hsc,
            Complex.ofReal_one, Matrix.one_apply_eq]
        · by_cases hbi : b = i
          · rw [hbi]

            have hzero : ∀ k ∈ Finset.univ, k ∉ ({i, j} : Finset (Fin m)) →
                loBeamSplitter m i j θ ph j k * conj (loBeamSplitter m i j θ ph i k) = 0 := by
              intro k _ hk
              have h1 : k ≠ i := fun h => hk (by simp [h])
              have h2 : k ≠ j := fun h => hk (by simp [h])
              rw [loBS_zero_col i j θ ph hij j k h1 h2 (fun h => h2 h.symm)]
              ring
            rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin m))) hzero,
              Finset.sum_pair hij, loBS_val_ji i j θ ph hij, loBS_val_ii i j θ ph hij,
              loBS_val_jj i j θ ph hij, loBS_val_ij i j θ ph hij,
              Complex.conj_ofReal, map_neg, map_mul, loConjExpIP, Complex.conj_ofReal,
              Matrix.one_apply_ne (fun h => hij h.symm)]
            ring
          · have hzero : ∀ k ∈ Finset.univ,
                loBeamSplitter m i j θ ph j k * conj (loBeamSplitter m i j θ ph b k) = 0 := by
              intro k _
              by_cases hkj : k = j
              · rw [hkj]
                rw [loBS_val_jj i j θ ph hij, loBS_val_off i j θ ph hij b j hbi hbj, if_neg hbj]
                simp
              · by_cases hki : k = i
                · rw [hki]
                  rw [loBS_val_ji i j θ ph hij, loBS_val_off i j θ ph hij b i hbi hbj, if_neg hbi]
                  simp
                · rw [loBS_zero_col i j θ ph hij j k hki hkj (fun h => hkj h.symm)]
                  simp
            rw [Finset.sum_eq_zero hzero, Matrix.one_apply_ne (fun h => hbj h.symm)]
      · by_cases hbi : b = i
        · rw [hbi]

          have hzero : ∀ k ∈ Finset.univ,
              loBeamSplitter m i j θ ph a k * conj (loBeamSplitter m i j θ ph i k) = 0 := by
            intro k _
            by_cases hka : k = a
            · rw [hka]
              rw [loBS_val_off i j θ ph hij a a hai haj, if_pos rfl, one_mul,
                loBS_zero_col i j θ ph hij i a hai haj (fun h => hai h.symm)]
              simp
            · rw [loBS_val_off i j θ ph hij a k hai haj, if_neg (fun h => hka h.symm)]
              simp
          rw [Finset.sum_eq_zero hzero, Matrix.one_apply_ne hai]
        · by_cases hbj : b = j
          · rw [hbj]

            have hzero : ∀ k ∈ Finset.univ,
                loBeamSplitter m i j θ ph a k * conj (loBeamSplitter m i j θ ph j k) = 0 := by
              intro k _
              by_cases hka : k = a
              · rw [hka]
                rw [loBS_val_off i j θ ph hij a a hai haj, if_pos rfl, one_mul,
                  loBS_zero_col i j θ ph hij j a hai haj (fun h => haj h.symm)]
                simp
              · rw [loBS_val_off i j θ ph hij a k hai haj, if_neg (fun h => hka h.symm)]
                simp
            rw [Finset.sum_eq_zero hzero, Matrix.one_apply_ne haj]
          · by_cases hab : a = b
            · rw [← hab]

              have hzero : ∀ k ∈ Finset.univ, k ≠ a →
                  loBeamSplitter m i j θ ph a k * conj (loBeamSplitter m i j θ ph a k) = 0 := by
                intro k _ hka
                rw [loBS_val_off i j θ ph hij a k hai haj, if_neg (fun h => hka h.symm)]
                simp
              rw [Finset.sum_eq_single a hzero (by simp),
                loBS_val_off i j θ ph hij a a hai haj, if_pos rfl,
                Matrix.one_apply_eq]
              simp
            · have hzero : ∀ k ∈ Finset.univ,
                  loBeamSplitter m i j θ ph a k * conj (loBeamSplitter m i j θ ph b k) = 0 := by
                intro k _
                by_cases hka : k = a
                · rw [hka]
                  rw [loBS_val_off i j θ ph hij a a hai haj, if_pos rfl, one_mul,
                    loBS_val_off i j θ ph hij b a hbi hbj, if_neg (fun h => hab h.symm)]
                  simp
                · rw [loBS_val_off i j θ ph hij a k hai haj, if_neg (fun h => hka h.symm)]
                  simp
              rw [Finset.sum_eq_zero hzero, Matrix.one_apply_ne hab]

def loInterferometer (m : ℕ) : Type := List (Fin m × Fin m × ℝ × ℝ)

noncomputable def loInterferometerMatrix (m : ℕ) (G : loInterferometer m) :
    Matrix (Fin m) (Fin m) ℂ :=
  G.foldl (fun acc g => loBeamSplitter m g.1 g.2.1 g.2.2.1 g.2.2.2 * acc) 1

theorem loInterferometerMatrix_mem_unitaryGroup (m : ℕ) (G : loInterferometer m) :
    loInterferometerMatrix m G ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  unfold loInterferometerMatrix
  have h : ∀ (init : Matrix (Fin m) (Fin m) ℂ), init ∈ Matrix.unitaryGroup (Fin m) ℂ →
      G.foldl (fun acc g => loBeamSplitter m g.1 g.2.1 g.2.2.1 g.2.2.2 * acc) init
        ∈ Matrix.unitaryGroup (Fin m) ℂ := by
    induction G with
    | nil => intro init hinit; exact hinit
    | cons g G ih =>
        intro init hinit
        exact ih _ (Submonoid.mul_mem _
          (loBeamSplitter_mem_unitaryGroup m g.1 g.2.1 g.2.2.1 g.2.2.2) hinit)
  exact h 1 (Submonoid.one_mem _)

noncomputable def loFockDist (m n : ℕ) (hnm : n ≤ m) (U : Matrix (Fin m) (Fin m) ℂ) :
    FockOccupation m n → ℝ :=
  fun S => bosonWeight (U.submatrix id (Fin.castLE hnm)) S

noncomputable def loIsometryDist (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ) :
    FockOccupation m n → ℝ :=
  bosonWeight A

structure LoCompletedUnitary (m n : ℕ) (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℂ) :
    Type where

  U : Matrix (Fin m) (Fin m) ℂ

  unitary : U ∈ Matrix.unitaryGroup (Fin m) ℂ

  extendCols : ∀ (i : Fin m) (j : Fin n), U i (Fin.castLE hnm j) = A i j

theorem loFockDist_eq_of_extendCols {m n : ℕ} {hnm : n ≤ m} {A : Matrix (Fin m) (Fin n) ℂ}
    (W : LoCompletedUnitary m n hnm A) (S : FockOccupation m n) :
    loFockDist m n hnm W.U S = loIsometryDist m n A S := by
  have h : W.U.submatrix id (Fin.castLE hnm) = A := by
    ext i j
    simpa [Matrix.submatrix_apply] using W.extendCols i j
  simp only [loFockDist, loIsometryDist]
  rw [h]

noncomputable def loPhysicalDist (m n : ℕ) (hnm : n ≤ m) (G : loInterferometer m) :
    FockOccupation m n → ℝ :=
  loFockDist m n hnm (loInterferometerMatrix m G)

theorem loPhysicalDist_eq_loFockDist (m n : ℕ) (hnm : n ≤ m) (G : loInterferometer m)
    (S : FockOccupation m n) :
    loPhysicalDist m n hnm G S = loFockDist m n hnm (loInterferometerMatrix m G) S := rfl

def ratBitSize (q : ℚ) : ℕ := max (Nat.log2 q.num.natAbs + 1) (Nat.log2 q.den + 1)

structure LoDyadicEncoding (m n b : ℕ) : Type where

  mat : Matrix (Fin m) (Fin n) ℚ

  width : ∀ i j, ratBitSize (mat i j) ≤ b

noncomputable def loRoundToDyadicEntry (b : ℕ) (x : ℝ) : ℚ :=
  ((Int.floor (((2 : ℕ) ^ b : ℝ) * x) : ℤ) : ℚ) / ((2 : ℕ) ^ b : ℚ)

theorem loRoundToDyadicEntry_err (b : ℕ) (x : ℝ) :
    |x - (loRoundToDyadicEntry b x : ℝ)| ≤ 1 / (((2 : ℕ) ^ b : ℝ)) := by
  have hp : (0 : ℝ) < ((2 : ℕ) ^ b : ℝ) := by positivity
  have hfl : ((Int.floor (((2 : ℕ) ^ b : ℝ) * x) : ℤ) : ℝ)
      ≤ ((2 : ℕ) ^ b : ℝ) * x := by exact_mod_cast Int.floor_le _
  have hfu : ((2 : ℕ) ^ b : ℝ) * x
      < ((Int.floor (((2 : ℕ) ^ b : ℝ) * x) : ℤ) : ℝ) + 1 := by
    have h := Int.lt_floor_add_one (((2 : ℕ) ^ b : ℝ) * x)
    exact_mod_cast h
  have hcast : (loRoundToDyadicEntry b x : ℝ)
      = ((Int.floor (((2 : ℕ) ^ b : ℝ) * x) : ℤ) : ℝ) / (((2 : ℕ) ^ b : ℝ)) := by
    rw [loRoundToDyadicEntry, Rat.cast_div]
    simp
  rw [hcast]
  have hdiv : x - ((Int.floor (((2 : ℕ) ^ b : ℝ) * x) : ℤ) : ℝ) / (((2 : ℕ) ^ b : ℝ))
      = ((((2 : ℕ) ^ b : ℝ)) * x - ((Int.floor (((2 : ℕ) ^ b : ℝ) * x) : ℤ) : ℝ))
        / (((2 : ℕ) ^ b : ℝ)) := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos hp, div_le_iff₀ hp, div_mul_cancel₀ _ (ne_of_gt hp)]
  exact abs_le.2 ⟨by linarith, by linarith⟩

noncomputable def loRoundToDyadic (m n b : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℚ :=
  Matrix.of fun i j => loRoundToDyadicEntry b (A i j)

noncomputable def loOfRat (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) : Matrix (Fin m) (Fin n) ℂ :=
  A.map (algebraMap ℚ ℂ)

noncomputable def loGaussianDensity (z : ℂ) : ℝ :=
  Real.pi⁻¹ * Real.exp (-(Complex.normSq z))

noncomputable def loGaussianMatDensity (n : ℕ) (X : Fin n → Fin n → ℂ) : ℝ :=
  ∏ i, ∏ j, loGaussianDensity (X i j)

def LoPaccHypothesis : Prop :=
  ∃ (c₁ c₂ : ℝ), 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (n : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      (∫ X : Fin n → Fin n → ℂ,
          (if Complex.normSq (Matrix.permanent (Matrix.of fun i j => X i j))
              ≤ δ * (n ! : ℝ)
            then (1 : ℝ) else 0) * loGaussianMatDensity n X
        ∂MeasureTheory.volume) ≤ c₂ * δ ^ c₁

structure LoSampler (m n : ℕ) : Type where

  L : ℕ

  O : (Fin L → Bool) → FockOccupation m n

noncomputable def loSamplerDist {m n : ℕ} (Sam : LoSampler m n) (S : FockOccupation m n) : ℝ :=
  (∑ r : (Fin Sam.L → Bool), if Sam.O r = S then (1 : ℝ) else 0) / ((2 : ℕ) ^ Sam.L : ℝ)

structure LoFbppEstimator (m n : ℕ) : Type where

  q : ℕ

  qlen : ℕ

  out : (List Bool → Bool) → (Fin q → Bool) → ℚ

end Qatlib.Concepts.CountingClasses.ClassTransport
