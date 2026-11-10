/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TemplMatch01.MainResults.MultiTemplate.MaximumAverageScore
import Qatlib.Papers.TemplMatch01.MainResults.MultiTemplate.SquareRootMeasurement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Field.GeomSum
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
set_option warningAsError false

namespace Qatlib.Papers.TemplMatch01.MainResults.MultiTemplate

open Finset
open scoped ComplexOrder Matrix BigOperators

set_option autoImplicit false

noncomputable section

def zeta (M : ℕ) : ℂ := Complex.exp (2 * (Real.pi / M : ℝ) * Complex.I)

theorem zeta_isPrimitiveRoot (M : ℕ) (hM : 0 < M) : IsPrimitiveRoot (zeta M) M := by
  have h := Complex.isPrimitiveRoot_exp M (Nat.pos_iff_ne_zero.mp hM)
  unfold zeta
  convert h using 2
  push_cast
  ring

theorem zeta_ne_zero (M : ℕ) : zeta M ≠ 0 := fun h => by
  unfold zeta at h
  exact Complex.exp_ne_zero _ h

theorem norm_zeta (M : ℕ) : ‖zeta M‖ = 1 := by
  unfold zeta
  rw [Complex.norm_exp]
  have hre : (2 * (Real.pi / M : ℝ) : ℂ) * Complex.I = (2 * (Real.pi / M) : ℝ) * Complex.I := by
    push_cast; ring
  rw [hre]
  simp

theorem conj_zeta_pow_eq_inv (M a : ℕ) : (starRingEnd ℂ) (zeta M ^ a) = (zeta M ^ a)⁻¹ := by
  have h2 : ((Complex.normSq (zeta M ^ a) : ℝ) : ℂ)
      = (starRingEnd ℂ) (zeta M ^ a) * (zeta M ^ a) := Complex.normSq_eq_conj_mul_self
  have h1 : ((Complex.normSq (zeta M ^ a) : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow, norm_zeta, one_pow]
    norm_num
  have hmul : (starRingEnd ℂ) (zeta M ^ a) * (zeta M ^ a) = 1 := by rw [← h2, h1]
  exact eq_inv_of_mul_eq_one_left hmul

theorem geom_zeta_of_not_dvd (M : ℕ) (_hM : 0 < M) (hζ : IsPrimitiveRoot (zeta M) M)
    (d : ℤ) (hd : ¬ ((M : ℤ) ∣ d)) : ∑ m ∈ range M, (zeta M) ^ ((m : ℤ) * d) = 0 := by
  have hxd : zeta M ^ d ≠ 1 := fun h => hd ((hζ.zpow_eq_one_iff_dvd d).mp h)
  have hxM : (zeta M ^ d) ^ M = 1 := by
    rw [← zpow_natCast ((zeta M) ^ d) M, ← zpow_mul', zpow_mul, zpow_natCast,
      hζ.pow_eq_one]
    exact one_zpow d
  have hsum := geom_sum_eq hxd M
  have hshift : ∑ m ∈ range M, (zeta M) ^ ((m : ℤ) * d)
      = ∑ m ∈ range M, (zeta M ^ d) ^ m := by
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [zpow_mul', zpow_natCast]
  rw [hshift, hsum, hxM]
  simp

variable (N M : ℕ)

def acoeff (k : ℕ) : ℝ := Real.sqrt ((N - k) * (k + 1)) / (N + 2)

def gammaW0 : Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  ((2 * (N + 1) : ℕ) : ℂ)⁻¹ •
    (1 + (∑ k : Fin N, (acoeff N k : ℂ) •
      (Matrix.single (Fin.succ k) (Fin.castSucc k) 1 + Matrix.single (Fin.castSucc k) (Fin.succ k) 1)))

def gammaV (m : ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  Matrix.diagonal (fun k : Fin (N+1) => zeta M ^ (m * k.1))

def gammaWm (m : ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  gammaV N M m * gammaW0 N * (gammaV N M m).conjTranspose

def gammaMu (m : ℕ) : Fin (N+1) → ℂ := fun k => (Real.sqrt M : ℂ)⁻¹ * zeta M ^ (m * k.1)

def gammaSrm (m : ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  Matrix.vecMulVec (gammaMu N M m) (star (gammaMu N M m))

lemma gammaWm_apply (m : ℕ) (i j : Fin (N+1)) :
    gammaWm N M m i j
      = zeta M ^ (m * i.1) * gammaW0 N i j * (starRingEnd ℂ) (zeta M ^ (m * j.1)) := by
  unfold gammaWm gammaV
  rw [Matrix.diagonal_conjTranspose]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp

lemma sqrt_inv_sq (M : ℕ) : ((Real.sqrt M : ℂ))⁻¹ * ((Real.sqrt M : ℂ))⁻¹ = (M : ℂ)⁻¹ := by
  have hsq : ((Real.sqrt M : ℂ)) * ((Real.sqrt M : ℂ)) = (M : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    exact Real.mul_self_sqrt (Nat.cast_nonneg M)
  rw [← mul_inv, hsq]

lemma gammaMu_apply (m : ℕ) (k : Fin (N+1)) :
    gammaMu N M m k = (Real.sqrt M : ℂ)⁻¹ * zeta M ^ (m * k.1) := rfl

lemma gammaMu_star (m : ℕ) (j : Fin (N+1)) :
    star (gammaMu N M m) j = (Real.sqrt M : ℂ)⁻¹ * (zeta M ^ (m * j.1))⁻¹ := by
  unfold gammaMu
  rw [Pi.star_apply]
  rw [show star ((Real.sqrt M : ℂ)⁻¹ * zeta M ^ (m * j.1))
      = (starRingEnd ℂ) ((Real.sqrt M : ℂ)⁻¹) * (starRingEnd ℂ) (zeta M ^ (m * j.1))
      from map_mul (starRingEnd ℂ) _ _]
  rw [conj_zeta_pow_eq_inv]
  congr 1
  simp

lemma mulPi_apply (hM : 0 < M) (m : ℕ) (i j : Fin (N+1)) :
    (gammaWm N M m * gammaSrm N M m) i j
      = (M : ℂ)⁻¹ * (zeta M ^ (m * i.1) * (zeta M ^ (m * j.1))⁻¹) * (∑ p, gammaW0 N i p) := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [gammaWm_apply]
  unfold gammaSrm
  rw [Matrix.vecMulVec_apply, gammaMu_star, gammaMu_apply]
  have hx : (zeta M ^ (m * p.1)) ≠ 0 := pow_ne_zero _ (zeta_ne_zero M)
  have hD : (zeta M ^ (m * j.1)) ≠ 0 := pow_ne_zero _ (zeta_ne_zero M)
  have hMne : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hs : (Real.sqrt M : ℂ) ≠ 0 := by
    have hpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
    have := Real.sqrt_pos.2 hpos
    exact_mod_cast this.ne'
  rw [conj_zeta_pow_eq_inv]
  field_simp
  rw [pow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg M)]
  push_cast
  ring

lemma phase_pow (m : ℕ) (i j : Fin (N+1)) :
    zeta M ^ (m * i.1) * (zeta M ^ (m * j.1))⁻¹
      = (zeta M ^ i.1 * (zeta M ^ j.1)⁻¹) ^ m := by
  rw [mul_comm m i.1, mul_comm m j.1, pow_mul, pow_mul, ← inv_pow, ← mul_pow]

theorem Gamma_apply (hM : 0 < M) (hNM : N < M) (hζ : IsPrimitiveRoot (zeta M) M)
    (i j : Fin (N+1)) :
    (∑ m ∈ range M, (gammaWm N M m * gammaSrm N M m) i j)
      = if i = j then (∑ p, gammaW0 N i p) else 0 := by
  have hx : ∀ m, (gammaWm N M m * gammaSrm N M m) i j
      = (M : ℂ)⁻¹ * (zeta M ^ i.1 * (zeta M ^ j.1)⁻¹) ^ m * (∑ p, gammaW0 N i p) := by
    intro m
    rw [mulPi_apply N M hM, phase_pow]
  rw [Finset.sum_congr rfl (fun m _ => hx m)]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hMne : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  by_cases hij : i = j
  · subst hij
    have hx1 : zeta M ^ i.1 * (zeta M ^ i.1)⁻¹ = 1 := by
      rw [mul_inv_cancel₀]
      exact pow_ne_zero _ (zeta_ne_zero M)
    have hsum1 : ∑ m ∈ range M, (zeta M ^ i.1 * (zeta M ^ i.1)⁻¹) ^ m = (M : ℂ) := by
      rw [hx1]
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [if_pos rfl, hsum1, inv_mul_cancel₀ hMne, one_mul]
  · have hbase_ne : zeta M ^ i.1 * (zeta M ^ j.1)⁻¹ ≠ 1 := by
      intro h
      have hji : zeta M ^ i.1 = zeta M ^ j.1 := by
        have h' := congrArg (fun t => t * zeta M ^ j.1) h
        simp only [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (zeta_ne_zero M)), mul_one,
          one_mul] at h'
        exact h'
      have hi : i.1 < M := lt_of_le_of_lt (Nat.lt_succ_iff.mp i.2) hNM
      have hj : j.1 < M := lt_of_le_of_lt (Nat.lt_succ_iff.mp j.2) hNM
      exact hij (Fin.ext (hζ.pow_inj hi hj hji))
    have hbase_M : (zeta M ^ i.1 * (zeta M ^ j.1)⁻¹) ^ M = 1 := by
      have hiM : zeta M ^ (i.1 * M) = 1 := by
        rw [mul_comm i.1 M, pow_mul, hζ.pow_eq_one, one_pow]
      have hjM : zeta M ^ (j.1 * M) = 1 := by
        rw [mul_comm j.1 M, pow_mul, hζ.pow_eq_one, one_pow]
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, hiM, hjM, inv_one, mul_one]
    have hsum0 : ∑ m ∈ range M, (zeta M ^ i.1 * (zeta M ^ j.1)⁻¹) ^ m = 0 := by
      rw [geom_sum_eq hbase_ne M, hbase_M]
      simp
    rw [if_neg hij, hsum0]
    simp

def gammaD (N : ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  ((2 * (N + 1) : ℕ) : ℂ)⁻¹ •
    (1 + ∑ k : Fin N, (acoeff N k : ℂ) •
      (Matrix.single (Fin.castSucc k) (Fin.castSucc k) 1 + Matrix.single (Fin.succ k) (Fin.succ k) 1))

def vvec (N : ℕ) (k : Fin N) : Fin (N+1) → ℂ :=
  fun i => (if i = Fin.castSucc k then (1:ℂ) else 0) - (if i = Fin.succ k then (1:ℂ) else 0)

lemma star_vvec (N : ℕ) (k : Fin N) (i : Fin (N+1)) : star (vvec N k i) = vvec N k i := by
  simp [vvec]

lemma vecMulVec_vvec (N : ℕ) (k : Fin N) :
    Matrix.vecMulVec (vvec N k) (star (vvec N k))
      = Matrix.single (Fin.castSucc k) (Fin.castSucc k) 1
        - Matrix.single (Fin.castSucc k) (Fin.succ k) 1
        - Matrix.single (Fin.succ k) (Fin.castSucc k) 1
        + Matrix.single (Fin.succ k) (Fin.succ k) 1 := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, Matrix.single_apply, vvec,
    Matrix.sub_apply, Matrix.add_apply]
  by_cases h1 : Fin.castSucc k = i <;> by_cases h2 : Fin.succ k = i <;>
    by_cases h3 : Fin.castSucc k = j <;> by_cases h4 : Fin.succ k = j <;>
    simp_all [eq_comm]

theorem gammaD_sub_gammaW0 (N : ℕ) :
    gammaD N - gammaW0 N = ((2 * (N + 1) : ℕ) : ℂ)⁻¹ •
      ∑ k : Fin N, (acoeff N k : ℂ) • Matrix.vecMulVec (vvec N k) (star (vvec N k)) := by
  unfold gammaD gammaW0
  rw [smul_add, smul_add, add_sub_add_left_eq_sub, ← smul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [← smul_sub, vecMulVec_vvec]
  congr 1
  abel

lemma gammaW0_apply (i j : Fin (N+1)) :
    gammaW0 N i j = ((2 * (N + 1) : ℕ) : ℂ)⁻¹ *
      ((if i = j then (1 : ℂ) else 0) +
        ∑ k : Fin N, (acoeff N k : ℂ) *
          ((if Fin.succ k = i ∧ Fin.castSucc k = j then 1 else 0) +
           (if Fin.castSucc k = i ∧ Fin.succ k = j then 1 else 0))) := by
  unfold gammaW0
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.sum_apply,
    Matrix.single_apply, smul_eq_mul, mul_add, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib]

lemma sum_ite_row (a b : Fin (N+1)) (i : Fin (N+1)) :
    (∑ p : Fin (N+1), (if a = i ∧ b = p then (1 : ℂ) else 0))
      = if a = i then (1 : ℂ) else 0 := by
  by_cases ha : a = i
  · rw [if_pos ha]
    simp only [ha, true_and]
    simpa using (Finset.sum_ite_eq (Finset.univ : Finset (Fin (N+1))) b (1 : ℂ))
  · rw [if_neg ha]
    refine Finset.sum_eq_zero ?_
    intro p _
    simp [ha]

lemma gammaW0_rowsum (i : Fin (N+1)) :
    (∑ p, gammaW0 N i p) = ((2 * (N + 1) : ℕ) : ℂ)⁻¹ *
      (1 + ∑ k : Fin N, (acoeff N k : ℂ) *
        ((if Fin.succ k = i then 1 else 0) + (if Fin.castSucc k = i then 1 else 0))) := by
  rw [Finset.sum_congr rfl (fun p _ => gammaW0_apply N i p)]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib]
  have h1 : (∑ p, if i = p then (1 : ℂ) else 0) = 1 := by
    rw [Finset.sum_ite_eq]
    simp
  rw [h1]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [← Finset.mul_sum, Finset.sum_add_distrib,
    sum_ite_row N (Fin.succ k) (Fin.castSucc k) i,
    sum_ite_row N (Fin.castSucc k) (Fin.succ k) i]

lemma gammaD_apply (i j : Fin (N+1)) :
    gammaD N i j = ((2 * (N + 1) : ℕ) : ℂ)⁻¹ *
      ((if i = j then (1 : ℂ) else 0) +
        ∑ k : Fin N, (acoeff N k : ℂ) *
          ((if Fin.castSucc k = i ∧ Fin.castSucc k = j then 1 else 0) +
           (if Fin.succ k = i ∧ Fin.succ k = j then 1 else 0))) := by
  unfold gammaD
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.sum_apply,
    Matrix.single_apply, smul_eq_mul, mul_add, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib]

theorem Gamma_eq_gammaD (hM : 0 < M) (hNM : N < M) (hζ : IsPrimitiveRoot (zeta M) M) :
    (∑ m ∈ range M, gammaWm N M m * gammaSrm N M m) = gammaD N := by
  ext i j
  rw [Matrix.sum_apply i j (Finset.range M) (fun m => gammaWm N M m * gammaSrm N M m),
    Gamma_apply N M hM hNM hζ i j, gammaD_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl, gammaW0_rowsum]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    simp only [and_self]
    ac_rfl
  · rw [if_neg hij, if_neg hij]
    have hz : (∑ k : Fin N, (acoeff N k : ℂ) *
        ((if Fin.castSucc k = i ∧ Fin.castSucc k = j then 1 else 0) +
         (if Fin.succ k = i ∧ Fin.succ k = j then 1 else 0))) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k _
      have h1 : ¬ (Fin.castSucc k = i ∧ Fin.castSucc k = j) :=
          fun ⟨h1, h2⟩ => hij (h1.symm.trans h2)
      have h2 : ¬ (Fin.succ k = i ∧ Fin.succ k = j) := fun ⟨h1, h2⟩ => hij (h1.symm.trans h2)
      simp [h1, h2]
    rw [hz, add_zero, mul_zero]

lemma acoeff_nonneg (k : Fin N) : 0 ≤ acoeff N k := by
  unfold acoeff
  positivity

theorem posSemidef_gammaD_sub_gammaW0 (N : ℕ) : (gammaD N - gammaW0 N).PosSemidef := by
  rw [gammaD_sub_gammaW0]
  refine Matrix.PosSemidef.smul ?_ ?_
  · refine Matrix.posSemidef_sum Finset.univ ?_
    intro k _
    exact Matrix.PosSemidef.smul (Matrix.posSemidef_vecMulVec_self_star (vvec N k))
      (by exact_mod_cast (acoeff_nonneg N k))
  · positivity

lemma star_ite_one (P : Prop) [Decidable P] :
    star ((if P then (1 : ℂ) else 0)) = (if P then (1 : ℂ) else 0) := by
  split_ifs <;> simp

lemma star_ofReal (r : ℝ) : star ((r : ℂ)) = (r : ℂ) := by
  simp

lemma star_inv_natCast (n : ℕ) : star (((n : ℕ) : ℂ)⁻¹) = (((n : ℕ) : ℂ)⁻¹) := by
  rw [star_inv₀, star_natCast]

theorem gammaD_isHermitian (N : ℕ) : (gammaD N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  rw [gammaD_apply N j i, gammaD_apply N i j]
  rw [star_mul, star_inv_natCast, mul_comm]
  congr 1
  rw [star_add, star_sum]
  congr 1
  · rw [star_ite_one]
    simp only [eq_comm]
  · refine Finset.sum_congr rfl ?_
    intro k _
    rw [star_mul, star_add, star_ite_one, star_ite_one, star_ofReal]
    simp only [and_comm]
    ring

theorem gammaMu_eq_mulVec (m : ℕ) :
    gammaV N M m *ᵥ (fun _ : Fin (N+1) => (Real.sqrt M : ℂ)⁻¹) = gammaMu N M m := by
  ext k
  simp only [gammaV, gammaMu, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single k]
  · simp [mul_comm]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), zero_mul]
  · intro hk
    simp at hk

lemma overlap_eq (N : ℕ) (k : Fin N) :
    overlap N k = Real.sqrt (((N - (k : ℕ)) * ((k : ℕ) + 1) : ℕ) : ℝ) := rfl

lemma acoeff_mul_eq (N : ℕ) (k : Fin N) :
    ((2 * (N + 1) : ℕ) : ℂ)⁻¹ * (acoeff N k : ℂ)
      = ((2 * ((N:ℝ)+1) * ((N:ℝ)+2) : ℝ)⁻¹ : ℂ) * ((overlap N k : ℝ) : ℂ) := by
  have hk : (k : ℕ) ≤ N := le_of_lt k.2
  have hsqrt : Real.sqrt (((N:ℝ) - (k:ℝ)) * ((k:ℝ) + 1)) = overlap N k := by
    rw [overlap_eq]
    congr 1
    push_cast [hk]
    ring
  unfold acoeff
  rw [hsqrt]
  have hc1 : (((2 * (N + 1) : ℕ) : ℂ)⁻¹) = ((((2 * (N + 1) : ℕ) : ℝ))⁻¹ : ℂ) := by
    push_cast; ring
  rw [hc1]
  push_cast
  field_simp

lemma wZero_apply (N : ℕ) (i j : Fin (N+1)) :
    wZero N i j = ((2 * ((N:ℝ)+1) : ℝ)⁻¹ : ℂ) * (if i = j then (1:ℂ) else 0) +
      ((2 * ((N:ℝ)+1) * ((N:ℝ)+2) : ℝ)⁻¹ : ℂ) *
        ∑ k : Fin N, ((overlap N k : ℝ) : ℂ) *
          ((if Fin.castSucc k = i ∧ Fin.succ k = j then 1 else 0) +
           (if Fin.succ k = i ∧ Fin.castSucc k = j then 1 else 0)) := by
  unfold wZero
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sum_apply,
    Matrix.single_apply, smul_eq_mul, mul_add, mul_ite, mul_one, mul_zero,
    Finset.mul_sum]

theorem gammaW0_eq_wZero (N : ℕ) : gammaW0 N = wZero N := by
  ext i j
  rw [gammaW0_apply, wZero_apply]
  have hc1 : ((2 * ((N:ℝ)+1) : ℝ)⁻¹ : ℂ) = ((2 * (N + 1) : ℕ) : ℂ)⁻¹ := by
    push_cast; ring
  rw [hc1, mul_add]
  have hS : ((2 * (N + 1) : ℕ) : ℂ)⁻¹ *
      (∑ k : Fin N, (acoeff N k : ℂ) *
        ((if Fin.succ k = i ∧ Fin.castSucc k = j then 1 else 0) +
         (if Fin.castSucc k = i ∧ Fin.succ k = j then 1 else 0)))
      = ((2 * ((N:ℝ)+1) * ((N:ℝ)+2) : ℝ)⁻¹ : ℂ) *
        (∑ k : Fin N, ((overlap N k : ℝ) : ℂ) *
          ((if Fin.castSucc k = i ∧ Fin.succ k = j then 1 else 0) +
           (if Fin.succ k = i ∧ Fin.castSucc k = j then 1 else 0))) := by
    conv_lhs => rw [Finset.mul_sum]
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [← mul_assoc, acoeff_mul_eq]
    ring
  rw [hS]

end

end Qatlib.Papers.TemplMatch01.MainResults.MultiTemplate
