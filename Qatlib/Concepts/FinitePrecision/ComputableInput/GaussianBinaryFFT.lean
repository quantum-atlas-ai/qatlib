/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BinaryArithmetic

set_option autoImplicit false
namespace Qatlib.Concepts.FinitePrecision.ComputableInput
open scoped BigOperators

def gaussianButterflyCharge (x y : GaussianDyadicScalar) : ℕ :=
  2 * (max x.1.natAbs.size y.1.natAbs.size + 1) +
    2 * (max x.2.natAbs.size y.2.natAbs.size + 1)

structure GaussianBinaryFFTRun (k : ℕ) where
  run : GaussianDyadicFFTRun k
  charge : ℕ

def gaussianBinaryFFT (D : ℕ) : (k : ℕ) → GaussianTwiddleTable k →
    (Fin (2 ^ k) → GaussianDyadicScalar) → GaussianBinaryFFTRun k
  | 0, _, f => ⟨⟨Vector.ofFn f, 0, 0⟩, 0⟩
  | k + 1, t, f =>
    let lower : GaussianTwiddleTable k := fun l => t l.castSucc
    let e := gaussianBinaryFFT D k lower
      (fun j => f ⟨2 * j.val, by rw [pow_succ]; have := j.isLt; omega⟩)
    let o := gaussianBinaryFFT D k lower
      (fun j => f ⟨2 * j.val + 1, by rw [pow_succ]; have := j.isLt; omega⟩)
    let products := Vector.ofFn (fun j : Fin (2 ^ k) =>
      gaussianBinaryComplexMul D (t (Fin.last k) j) o.run.values[j.val])
    let atIndex (j : Fin (2 ^ (k + 1))) : Fin (2 ^ k) :=
      ⟨j.val % 2 ^ k, Nat.mod_lt _ (by positivity)⟩
    ⟨⟨Vector.ofFn (fun j =>
        if j.val < 2 ^ k then gaussianScalarAdd e.run.values[(atIndex j).val] products[(atIndex j).val].value
          else gaussianScalarSub e.run.values[(atIndex j).val] products[(atIndex j).val].value),
        e.run.products + o.run.products + 2 ^ k,
        e.run.additions + o.run.additions + 2 ^ (k + 1)⟩,
      e.charge + o.charge + (∑ j : Fin (2 ^ k), products[j.val].charge) +
        (∑ j : Fin (2 ^ (k + 1)), gaussianButterflyCharge e.run.values[(atIndex j).val]
          products[(atIndex j).val].value)⟩

def gaussianBinaryPositiveFFT (D k : ℕ) (t : GaussianTwiddleTable k)
    (f : Fin (2 ^ k) → GaussianDyadicScalar) : GaussianBinaryFFTRun k :=
  let r := gaussianBinaryFFT D k t (fun j => gaussianScalarConj (f j))
  ⟨⟨r.run.values.map gaussianScalarConj, r.run.products, r.run.additions⟩,
    r.charge + (∑ j : Fin (2 ^ k), ((f j).2.natAbs.size + 1)) +
      (∑ j : Fin (2 ^ k), (r.run.values[j.val].2.natAbs.size + 1))⟩

theorem gaussian_shared_fft_counts (D : ℤ) (k : ℕ) (t : GaussianTwiddleTable k)
    (x : Fin (2 ^ k) → GaussianDyadicScalar) :
    2 * (gaussianSharedFFT D k t x).products = k * 2 ^ k ∧
    (gaussianSharedFFT D k t x).additions = k * 2 ^ k := by
  induction k with
  | zero => simp [gaussianSharedFFT]
  | succ k ih =>
    have he := ih (fun l => t l.castSucc)
      (fun j => x ⟨2 * j.val, by rw [pow_succ]; have := j.isLt; omega⟩)
    have ho := ih (fun l => t l.castSucc)
      (fun j => x ⟨2 * j.val + 1, by rw [pow_succ]; have := j.isLt; omega⟩)
    change 2 * (_ + _ + 2 ^ k) = (k + 1) * 2 ^ (k + 1) ∧
      _ + _ + 2 ^ (k + 1) = (k + 1) * 2 ^ (k + 1)
    constructor <;> nlinarith [he.1, he.2, ho.1, ho.2, pow_succ 2 k]

theorem gaussian_binary_fft_value (D k : ℕ) (t : GaussianTwiddleTable k)
    (f : Fin (2 ^ k) → GaussianDyadicScalar) :
    (gaussianBinaryFFT D k t f).run = gaussianSharedFFT (D : ℤ) k t f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [gaussianBinaryFFT, gaussianSharedFFT, ih, Vector.getElem_ofFn,
      gaussian_binary_complex_value]

theorem gaussian_binary_positive_value (D k : ℕ) (t : GaussianTwiddleTable k)
    (f : Fin (2 ^ k) → GaussianDyadicScalar) :
    (gaussianBinaryPositiveFFT D k t f).run = gaussianSharedPositiveFFT (D : ℤ) k t f := by
  simp only [gaussianBinaryPositiveFFT, gaussianSharedPositiveFFT, gaussian_binary_fft_value]

theorem gaussian_binary_fft_both_value (D k : ℕ) (t : GaussianTwiddleTable k)
    (f : Fin (2 ^ k) → GaussianDyadicScalar) :
    (gaussianBinaryFFT D k t f).run = gaussianSharedFFT (D : ℤ) k t f ∧
    (gaussianBinaryPositiveFFT D k t f).run = gaussianSharedPositiveFFT (D : ℤ) k t f :=
  ⟨gaussian_binary_fft_value D k t f, gaussian_binary_positive_value D k t f⟩

private theorem bits_of_bound (z : ℤ) (W : ℕ) (h : z.natAbs ≤ 2 ^ W - 1) :
    z.natAbs.size ≤ W := by
  have hp : 0 < (2 : ℕ) ^ W := by positivity
  exact Nat.size_le.mpr (by omega)

private theorem scalar_bits_of_bound (z : GaussianDyadicScalar) (W : ℕ)
    (h : GaussianScalarBound z (2 ^ W - 1)) : GaussianScalarBits z W :=
  ⟨bits_of_bound z.1 W h.1, bits_of_bound z.2 W h.2⟩

theorem gaussian_fft_audit_output_bits (D : ℤ) (k W : ℕ) (t : GaussianTwiddleTable k)
    (f : Fin (2 ^ k) → GaussianDyadicScalar)
    (h : GaussianFFTIntegerBounded D k t f (2 ^ W - 1)) :
    ∀ j : Fin (2 ^ k), GaussianScalarBits (gaussianSharedFFT D k t f).values[j.val] W := by
  cases k with
  | zero =>
    intro j
    simpa only [gaussianSharedFFT, Vector.getElem_ofFn] using scalar_bits_of_bound (f j) W (h.2 j)
  | succ k => exact fun j => scalar_bits_of_bound _ W (h.2.2.2 j)

theorem gaussian_fft_audit_input_bits (D : ℤ) (k W : ℕ) (t : GaussianTwiddleTable k)
    (f : Fin (2 ^ k) → GaussianDyadicScalar)
    (h : GaussianFFTIntegerBounded D k t f (2 ^ W - 1)) :
    ∀ j : Fin (2 ^ k), GaussianScalarBits (f j) W := by
  induction k with
  | zero => exact fun j => scalar_bits_of_bound _ W (h.2 j)
  | succ k ih =>
    intro j
    let i : Fin (2 ^ k) :=
        ⟨j.val / 2, by have hjlt := lt_of_lt_of_eq j.isLt (pow_succ (2 : ℕ) k); omega⟩
    by_cases he : j.val % 2 = 0
    · have hx := ih _ _ h.1 i
      have hj : (⟨2 * i.val, by rw [pow_succ]; have := i.isLt; omega⟩ : Fin (2 ^ (k + 1))) = j := by
        apply Fin.ext; dsimp only [i]; omega
      simpa only [hj] using hx
    · have hx := ih _ _ h.2.1 i
      have hj : (⟨2 * i.val + 1, by rw [pow_succ]; have := i.isLt; omega⟩ : Fin (2 ^ (k + 1))) = j := by
        apply Fin.ext; dsimp only [i]; omega
      simpa only [hj] using hx

private theorem butterfly_charge_bound (x y : GaussianDyadicScalar) (W : ℕ)
    (hx : GaussianScalarBits x W) (hy : GaussianScalarBits y W) :
    gaussianButterflyCharge x y ≤ 4 * (W + 1) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  dsimp only [gaussianButterflyCharge]
  omega

theorem gaussian_binary_fft_charge (D k W : ℕ) (t : GaussianTwiddleTable k)
    (f : Fin (2 ^ k) → GaussianDyadicScalar)
    (h : GaussianFFTIntegerBounded (D : ℤ) k t f (2 ^ W - 1)) :
    (gaussianBinaryFFT D k t f).charge ≤ 2048 * k * 2 ^ k * (W + 1) ^ 2 := by
  induction k with
  | zero => simp [gaussianBinaryFFT]
  | succ k ih =>
    let lower : GaussianTwiddleTable k := fun l => t l.castSucc
    let ev : Fin (2 ^ k) → GaussianDyadicScalar := fun j =>
      f ⟨2 * j.val, by rw [pow_succ]; have := j.isLt; omega⟩
    let od : Fin (2 ^ k) → GaussianDyadicScalar := fun j =>
      f ⟨2 * j.val + 1, by rw [pow_succ]; have := j.isLt; omega⟩
    let e := gaussianSharedFFT (D : ℤ) k lower ev
    let o := gaussianSharedFFT (D : ℤ) k lower od
    let product (j : Fin (2 ^ k)) :=
        gaussianScalarMulShared (D : ℤ) (t (Fin.last k) j) o.values[j.val]
    let atIndex (j : Fin (2 ^ (k + 1))) : Fin (2 ^ k) :=
        ⟨j.val % 2 ^ k, Nat.mod_lt _ (by positivity)⟩
    have he := ih lower ev h.1
    have ho := ih lower od h.2.1
    have hwork (j : Fin (2 ^ k)) :
        ∀ z ∈ gaussianMulWork (D : ℤ) (t (Fin.last k) j) o.values[j.val], z.natAbs.size ≤ W :=
      fun z hz => bits_of_bound z W (h.2.2.1 j z hz)
    have hprod (j : Fin (2 ^ k)) : GaussianScalarBits (product j) W :=
      ⟨hwork j _ (by simp [gaussianMulWork, product]), hwork j _ (by simp [gaussianMulWork, product])⟩
    have hevals := gaussian_fft_audit_output_bits (D : ℤ) k W lower ev h.1
    have hmul (j : Fin (2 ^ k)) :
        (gaussianBinaryComplexMul D (t (Fin.last k) j) o.values[j.val]).charge ≤ 2048 * (W + 1) ^ 2 :=
      (gaussian_binary_complex_certificate D _ _).2 W (hwork j)
    have hadd (j : Fin (2 ^ (k + 1))) :
        gaussianButterflyCharge e.values[(atIndex j).val] (product (atIndex j)) ≤ 4 * (W + 1) :=
      butterfly_charge_bound _ _ W (hevals (atIndex j)) (hprod (atIndex j))
    have hmulSum :=
        Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (2 ^ k)))) => hmul j)
    have haddSum :=
        Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (2 ^ (k + 1))))) => hadd j)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hmulSum haddSum
    simp only [gaussianBinaryFFT, Vector.getElem_ofFn, gaussian_binary_fft_value,
        gaussian_binary_complex_value]
    change (gaussianBinaryFFT D k lower ev).charge + (gaussianBinaryFFT D k lower od).charge +
      (∑ j : Fin (2 ^ k), (gaussianBinaryComplexMul D (t (Fin.last k) j) o.values[j.val]).charge) +
      (∑ j : Fin (2 ^ (k + 1)), gaussianButterflyCharge e.values[(atIndex j).val] (product (atIndex j))) ≤ _
    have hs : W + 1 ≤ (W + 1) ^ 2 := by nlinarith
    have hscaled := Nat.mul_le_mul_left ((2 : ℕ) ^ k) hs
    conv at haddSum => rhs; rw [pow_succ]
    conv_rhs => rw [pow_succ]
    have hnonneg : 0 ≤ (2 : ℕ) ^ k * (W + 1) ^ 2 := Nat.zero_le _
    nlinarith only [he, ho, hmulSum, haddSum, hscaled, hnonneg]

theorem gaussian_binary_positive_charge (D k W : ℕ) (t : GaussianTwiddleTable k)
    (f : Fin (2 ^ k) → GaussianDyadicScalar)
    (h : GaussianFFTIntegerBounded (D : ℤ) k t (fun j => gaussianScalarConj (f j)) (2 ^ W - 1)) :
    (gaussianBinaryPositiveFFT D k t f).charge ≤ 4096 * (k + 1) * 2 ^ k * (W + 1) ^ 2 := by
  have hneg := gaussian_binary_fft_charge D k W t _ h
  have hi := gaussian_fft_audit_input_bits (D : ℤ) k W t _ h
  have ho := gaussian_fft_audit_output_bits (D : ℤ) k W t _ h
  have hinput (j : Fin (2 ^ k)) : (f j).2.natAbs.size + 1 ≤ W + 1 := by
    have hh := (hi j).2
    simpa only [gaussianScalarConj, Int.natAbs_neg] using Nat.add_le_add_right hh 1
  have houtput (j : Fin (2 ^ k)) :
      (gaussianBinaryFFT D k t (fun j => gaussianScalarConj (f j))).run.values[j.val].2.natAbs.size + 1 ≤ W + 1 := by
    rw [gaussian_binary_fft_value]
    exact Nat.add_le_add_right (ho j).2 1
  have h1 := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (2 ^ k)))) => hinput j)
  have h2 := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (2 ^ k)))) => houtput j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
  dsimp only [gaussianBinaryPositiveFFT]
  have hs : W + 1 ≤ (W + 1) ^ 2 := by nlinarith
  have hscaled := Nat.mul_le_mul_left ((2 : ℕ) ^ k) hs
  calc
    _ ≤ 2048 * k * 2 ^ k * (W + 1) ^ 2 + 2 ^ k * (W + 1) + 2 ^ k * (W + 1) :=
      Nat.add_le_add (Nat.add_le_add hneg h1) h2
    _ ≤ 2048 * k * 2 ^ k * (W + 1) ^ 2 + 2 ^ k * (W + 1) ^ 2 + 2 ^ k * (W + 1) ^ 2 :=
      Nat.add_le_add (Nat.add_le_add_left hscaled _) hscaled
    _ = (2048 * k + 2) * 2 ^ k * (W + 1) ^ 2 := by ring
    _ ≤ 4096 * (k + 1) * 2 ^ k * (W + 1) ^ 2 := by gcongr; omega

theorem gaussian_binary_fft_scan_certificate (D k W : ℕ) (t : GaussianTwiddleTable k)
    (f : Fin (2 ^ k) → GaussianDyadicScalar) :
    (GaussianFFTIntegerBounded (D : ℤ) k t f (2 ^ W - 1) →
      (gaussianBinaryFFT D k t f).charge ≤ 2048 * k * 2 ^ k * (W + 1) ^ 2) ∧
    (GaussianFFTIntegerBounded (D : ℤ) k t (fun j => gaussianScalarConj (f j)) (2 ^ W - 1) →
      (gaussianBinaryPositiveFFT D k t f).charge ≤ 4096 * (k + 1) * 2 ^ k * (W + 1) ^ 2) :=
  ⟨gaussian_binary_fft_charge D k W t f, gaussian_binary_positive_charge D k W t f⟩

end Qatlib.Concepts.FinitePrecision.ComputableInput
