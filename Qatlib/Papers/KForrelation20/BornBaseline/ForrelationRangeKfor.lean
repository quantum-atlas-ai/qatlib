/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.KForrelation20.BornBaseline.ForrelationRangeStat

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.KForrelation20.BornBaseline

open Qatlib.Papers.CheatSheet15.BornBaseline

open scoped Matrix BigOperators

private noncomputable def pathTerm {N : ℕ} (k : ℕ) (H : Matrix (Fin N) (Fin N) ℝ)
    (z : Fin k → Fin N → Bool) (i : Fin k → Fin N) : ℝ :=
  (∏ j, toSign (z j (i j))) *
    (∏ j : Fin k, if h : j.val + 1 < k then H (i j) (i ⟨j.val + 1, h⟩) else 1)

private noncomputable def forrVector {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) :
    (k : ℕ) → (Fin (k + 1) → Fin N → Bool) → Fin N → ℝ
  | 0, z => fun i => toSign (z 0 i)
  | k + 1, z => fun i => toSign (z 0 i) *
      (H.mulVec (forrVector H k (Fin.tail z))) i

/-- An orthogonal real matrix preserves the sum of squared vector coordinates. -/
private theorem orthogonal_square_sum {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    (hH : Hᵀ * H = 1) (v : Fin N → ℝ) :
    (∑ i, (H.mulVec v i) ^ 2) = ∑ i, v i ^ 2 := by
  have he : dotProduct (H.mulVec v) (H.mulVec v) = dotProduct v v := by
    calc
      _ = dotProduct v ((Hᵀ * H).mulVec v) := by
        conv_rhs => rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ = _ := by rw [hH, Matrix.one_mulVec]
  simpa only [dotProduct, pow_two] using he

/-- The sum of squared coordinates of `forrVector` is `N` when `H` is orthogonal. -/
private theorem forrVector_square_sum {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    (hH : Hᵀ * H = 1) (k : ℕ) (z : Fin (k + 1) → Fin N → Bool) :
    (∑ i, forrVector H k z i ^ 2) = N := by
  induction k with
  | zero => simp [forrVector, toSign]
  | succ k ih =>
    have he (i : Fin N) : forrVector H (k + 1) z i ^ 2 =
        (H.mulVec (forrVector H k (Fin.tail z)) i) ^ 2 := by
      dsimp [forrVector]
      cases z 0 i <;> norm_num [toSign]
    rw [Finset.sum_congr rfl (fun i _ => he i), orthogonal_square_sum H hH]
    exact ih (Fin.tail z)

/-- Factors the first sign and matrix entry out of `pathTerm` for a path built with `Fin.cons`. -/
private theorem pathTerm_cons {N k : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    (z : Fin (k + 2) → Fin N → Bool) (a : Fin N) (b : Fin (k + 1) → Fin N) :
    pathTerm (k + 2) H z ((Fin.cons a b : Fin (k + 2) → Fin N)) =
      toSign (z 0 a) * H a (b 0) * pathTerm (k + 1) H (Fin.tail z) b := by
  unfold pathTerm
  rw [Fin.prod_univ_succ (fun j : Fin (k + 2) => toSign (z j ((Fin.cons a b : Fin (k + 2) → Fin N) j))),
    Fin.prod_univ_succ (fun j : Fin (k + 2) => if h : j.val + 1 < k + 2 then
      H ((Fin.cons a b : Fin (k + 2) → Fin N) j) ((Fin.cons a b : Fin (k + 2) → Fin N) ⟨j.val + 1, h⟩) else 1)]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have hhead : (if h : (0 : Fin (k + 2)).val + 1 < k + 2 then
      H a (((Fin.cons a b : Fin (k + 2) → Fin N) : Fin (k + 2) → Fin N) ⟨(0 : Fin (k + 2)).val + 1, h⟩) else 1) = H a (b 0) := by
    simp
  rw [hhead]
  have ht : (∏ j : Fin (k + 1), if h : j.succ.val + 1 < k + 2 then
        H (b j) ((Fin.cons a b : Fin (k + 2) → Fin N) ⟨j.succ.val + 1, h⟩) else 1) =
      ∏ j : Fin (k + 1), if h : j.val + 1 < k + 1 then H (b j) (b ⟨j.val + 1, h⟩) else 1 := by
    apply Finset.prod_congr rfl
    intro j _
    by_cases h : j.val + 1 < k + 1
    · have hs : j.succ.val + 1 < k + 2 := by simpa using Nat.succ_lt_succ h
      rw [dite_eq_left hs, dite_eq_left h]
      have hi : (⟨j.succ.val + 1, hs⟩ : Fin (k + 2)) = (⟨j.val + 1, h⟩ : Fin (k + 1)).succ := by
        apply Fin.ext
        rfl
      rw [hi, Fin.cons_succ]
    · have hs : ¬j.succ.val + 1 < k + 2 := by simpa using h
      rw [dite_eq_right hs, dite_eq_right h]
  rw [ht]
  simp only [Fin.tail]
  ring

/-- Decomposes a sum over finite sequences into sums over the first entry and the remaining
tail. -/
private theorem sumCons {N k : ℕ} (f : (Fin (k + 1) → Fin N) → ℝ) :
    (∑ b : Fin (k + 1) → Fin N, f b) =
      ∑ j : Fin N, ∑ t : Fin k → Fin N, f (Fin.cons j t) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 1) => Fin N)), Fintype.sum_prod_type]
  rfl

/-- Expresses each coordinate of `forrVector` as a sum of path terms with that initial
coordinate. -/
private theorem forrVector_eq_sum {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    (k : ℕ) (z : Fin (k + 1) → Fin N → Bool) (a : Fin N) :
    forrVector H k z a = ∑ b : Fin k → Fin N, pathTerm (k + 1) H z (Fin.cons a b) := by
  induction k generalizing a with
  | zero => simp [forrVector, pathTerm]
  | succ k ih =>
    rw [forrVector]
    simp_rw [pathTerm_cons, mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    rw [sumCons]
    unfold Matrix.mulVec dotProduct
    apply Finset.sum_congr rfl
    intro j _
    rw [ih (Fin.tail z) j, Finset.mul_sum]
    rfl

/-- Expresses `forrK` as the coordinate sum of `forrVector` divided by `N`. -/
private theorem forrK_eq_vector {N k : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    (z : Fin (k + 1) → Fin N → Bool) :
    forrK (k + 1) H z = (N : ℝ)⁻¹ * ∑ a : Fin N, forrVector H k z a := by
  change (N : ℝ)⁻¹ * ∑ i : Fin (k + 1) → Fin N, pathTerm (k + 1) H z i = _
  rw [sumCons]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact (forrVector_eq_sum H k z a).symm

/-- The absolute value of `forrK` is at most one when its matrix is orthogonal. -/
theorem forrelationRange : ForrelationRange := by
  intro N k H z hH
  by_cases hN : N = 0
  · subst N
    simp [forrK]
  have hn : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  cases k with
  | zero =>
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
    have hz : forrK 0 H z = (N : ℝ)⁻¹ := by simp [forrK]
    rw [hz]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)]
    exact (inv_le_one₀ hn).mpr hn1
  | succ k =>
    have hs := forrVector_square_sum H hH k z
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin N => (1 : ℝ))
      (forrVector H k z)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, hs] at hc
    have hb : |∑ i : Fin N, forrVector H k z i| ≤ (N : ℝ) := by
      nlinarith [sq_abs (∑ i : Fin N, forrVector H k z i),
        abs_nonneg (∑ i : Fin N, forrVector H k z i)]
    rw [forrK_eq_vector H z, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹),
      ← div_eq_inv_mul]
    exact (div_le_one hn).mpr hb

end Qatlib.Papers.KForrelation20.BornBaseline
