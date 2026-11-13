/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Aux4
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-!
# Forward norm of the V2 Taylor matrix

A Schur norm estimate bounds the jump and shift matrices on history labels. The decomposition
`taylorV2_forward_decomposition` separates these contributions from the identity and gives
`‖taylorStepMatrixV2 m k p M‖ ≤ 2 * sqrt k` for `k ≥ 5` and `‖M‖ ≤ 1`. See [BerryEtAl2017ODE]
for the paper's setting.

## Main statements

* `weighted_sum_sq`: The square of a weighted finite sum is bounded by the total nonnegative
  weight times the weighted sum of squares.
* `taylorV2_forward_norm_le`: For `k ≥ 5` and `‖M‖ ≤ 1`, the V2 Taylor matrix has operator norm
  at most `2 * sqrt k`.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ReferenceError.RefTraceError

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator Kronecker

/-- The square of a weighted finite sum is bounded by the total nonnegative weight times the
weighted sum of squares. -/
private theorem weighted_sum_sq {I : Type} [Fintype I]
    (a x : I → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i*x i)^2 ≤ (∑ i,a i)*(∑ i,a i*(x i)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (a i)) (fun i => Real.sqrt (a i)*x i)
  simpa only [mul_pow,Real.sq_sqrt (ha _),← mul_assoc,
    ← pow_two,Real.sq_sqrt (ha _)] using! h

/-- If row and column sums of entry norms are bounded by nonnegative `r` and `c`, then the
operator norm is at most `sqrt (r*c)`. -/
theorem taylor_schur_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (r c : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (hrow : ∀ i, ∑ j,‖M i j‖ ≤ r) (hcol : ∀ j, ∑ i,‖M i j‖ ≤ c) :
    ‖M‖ ≤ Real.sqrt (r*c) := by
  apply taylor_opNorm_le_of_vec_sq (Real.sqrt_nonneg _)
  intro x
  rw [Real.sq_sqrt (mul_nonneg hr hc)]
  have hpoint (i : I) : ‖(M *ᵥ x) i‖^2 ≤ r*(∑ j,‖M i j‖*‖x j‖^2) := by
    have hn : ‖(M *ᵥ x) i‖ ≤ ∑ j,‖M i j‖*‖x j‖ := by
      simpa only [Matrix.mulVec,dotProduct,norm_mul] using!
        norm_sum_le (Finset.univ : Finset I) (fun j => M i j*x j)
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
      ((weighted_sum_sq (fun j => ‖M i j‖) (fun j => ‖x j‖) (fun _ => norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hrow i) (Finset.sum_nonneg (fun _ _ => by positivity))))
  calc
    _ ≤ ∑ i,r*(∑ j,‖M i j‖*‖x j‖^2) := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = r*(∑ j,(∑ i,‖M i j‖)*‖x j‖^2) := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ ≤ r*(∑ j,c*‖x j‖^2) := by
      gcongr with j
      exact hcol j
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- For `k ≥ 5`, the quantity `2 + sqrt (k+1)` is at most `2 * sqrt k`. -/
theorem taylor_forward_sqrt_arithmetic (k : ℕ) (hk : 5 ≤ k) :
    2 + Real.sqrt (k+1 : ℕ) ≤ 2*Real.sqrt (k : ℝ) := by
  have hkr : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ k by positivity)
  have ht := Real.sq_sqrt (show (0 : ℝ) ≤ (k+1 : ℕ) by positivity)
  have hspos : 2 ≤ Real.sqrt (k : ℝ) := by nlinarith [Real.sqrt_nonneg (k : ℝ)]
  have har : 8*Real.sqrt (k : ℝ) ≤ 3*(k : ℝ)+3 := by
    have hpoly : 0 ≤ 9*(k : ℝ)^2-46*k+9 := by nlinarith [sq_nonneg ((k : ℝ)-5)]
    nlinarith [Real.sqrt_nonneg (k : ℝ)]
  norm_num only [Nat.cast_add,Nat.cast_one] at ht ⊢
  nlinarith [Real.sqrt_nonneg (k+1 : ℕ)]

/-- The number of labels in the half-open natural interval `[a, b)` is at most `b-a`. -/
private theorem label_interval_card (d a b : ℕ) :
    (Finset.univ.filter (fun l : Fin d => a ≤ l.val ∧ l.val < b)).card ≤ b-a := by
  have hsub : (Finset.univ.filter (fun l : Fin d => a ≤ l.val ∧ l.val < b)).image Fin.val ⊆
      Finset.Ico a b := by
    intro x hx
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hx
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Ico] using! hl
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective,Nat.card_Ico] at hc
  exact hc

/-- The label matrix whose boundary rows sum the entries of the preceding Taylor block. -/
def taylorJumpLabels (m k p : ℕ) :
    Matrix (Fin (m*(k+1)+p+1)) (Fin (m*(k+1)+p+1)) ℂ := fun r c =>
  if r.val ≤ m*(k+1) ∧ 0 < r.val ∧ (k+1) ∣ r.val ∧
    r.val-(k+1) ≤ c.val ∧ c.val < r.val then 1 else 0

/-- A column in the block preceding a positive multiple `r` of `k+1` determines that boundary as
`(c/(k+1)+1)*(k+1)`. -/
private theorem jump_label_target (k r c : ℕ) (hr : 0 < r) (hd : (k+1) ∣ r)
    (hlo : r-(k+1) ≤ c) (hi : c < r) : r=(c/(k+1)+1)*(k+1) := by
  obtain ⟨a,rfl⟩ := hd
  have ha : 1 ≤ a := by nlinarith
  have hlo' : (a-1)*(k+1) ≤ c := by
    rw [Nat.sub_mul,one_mul]
    simpa only [Nat.mul_comm] using! hlo
  have hi' : c < (a-1+1)*(k+1) := by
    simpa only [Nat.sub_add_cancel ha,Nat.mul_comm] using! hi
  rw [Nat.div_eq_of_lt_le hlo' hi',Nat.sub_add_cancel ha,Nat.mul_comm]

/-- The operator norm of the jump-label matrix is at most `sqrt (k+1)`. -/
theorem taylorJumpLabels_norm (m k p : ℕ) :
    ‖taylorJumpLabels m k p‖ ≤ Real.sqrt (k+1 : ℕ) := by
  classical
  apply (taylor_schur_norm_le _ (k+1 : ℕ) 1 (by positivity) (by positivity) ?_ ?_).trans_eq
    (by rw [mul_one])
  · intro r
    by_cases hr : r.val ≤ m*(k+1) ∧ 0 < r.val ∧ (k+1) ∣ r.val
    · have he : (∑ c,‖taylorJumpLabels m k p r c‖) =
          ((Finset.univ.filter (fun c : Fin (m*(k+1)+p+1) =>
            r.val-(k+1) ≤ c.val ∧ c.val < r.val)).card : ℝ) := by
        simp [taylorJumpLabels,apply_ite norm,hr.1,hr.2.1,hr.2.2]
      rw [he]
      exact_mod_cast (label_interval_card _ _ _).trans (show r.val-(r.val-(k+1)) ≤ k+1 by omega)
    · have hz (c) : taylorJumpLabels m k p r c=0 := by
        unfold taylorJumpLabels
        split_ifs with h
        · exact False.elim (hr ⟨h.1,h.2.1,h.2.2.1⟩)
        · rfl
      simp only [hz,norm_zero,Finset.sum_const_zero]
      positivity
  · intro c
    let target : Fin (m*(k+1)+p+1) :=
      if ht : (c.val/(k+1)+1)*(k+1) < m*(k+1)+p+1 then
        ⟨(c.val/(k+1)+1)*(k+1),ht⟩ else c
    have hpoint (r : Fin (m*(k+1)+p+1)) :
        ‖taylorJumpLabels m k p r c‖ ≤ if r=target then (1 : ℝ) else 0 := by
      by_cases h : r.val ≤ m*(k+1) ∧ 0 < r.val ∧ (k+1) ∣ r.val ∧
          r.val-(k+1) ≤ c.val ∧ c.val < r.val
      · have he := jump_label_target k r.val c.val h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
        have ht : (c.val/(k+1)+1)*(k+1) < m*(k+1)+p+1 := by rw [← he]; exact r.isLt
        have heq : r=target := by apply Fin.ext; simp only [target,dif_pos ht]; exact he
        simp only [taylorJumpLabels,if_pos h,if_pos heq,norm_one,le_refl]
      · simp only [taylorJumpLabels,if_neg h,norm_zero]
        split_ifs <;> norm_num
    exact (Finset.sum_le_sum (fun r _ => hpoint r)).trans_eq (by simp)

/-- The one-step forward shift on the finite label register. -/
def taylorShiftLabels (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun r c => if c.val+1=r.val then 1 else 0

/-- The operator norm of the finite forward shift is at most one. -/
theorem taylorShiftLabels_norm (d : ℕ) : ‖taylorShiftLabels d‖ ≤ 1 := by
  classical
  have hmass (f : Fin d → ℕ) (hf : Function.Injective f) (a : ℕ) :
      (∑ i : Fin d,if f i=a then (1 : ℝ) else 0) ≤ 1 := by
    by_cases he : ∃ i,f i=a
    · obtain ⟨i,hi⟩ := he
      have heq (j) : f j=a ↔ j=i := by rw [← hi]; exact hf.eq_iff
      simp only [heq]; simp
    · have hn (i) : f i≠a := by intro h; exact he ⟨i,h⟩
      simp [hn]
  have h := taylor_schur_norm_le (taylorShiftLabels d) 1 1 (by norm_num) (by norm_num)
    (fun r => by simpa [taylorShiftLabels,apply_ite norm] using!
      (hmass (fun c : Fin d => c.val+1) (fun a b h => Fin.ext (by dsimp at h; omega)) r.val))
    (fun c => by simpa [taylorShiftLabels,apply_ite norm,eq_comm] using!
      (hmass Fin.val Fin.val_injective (c.val+1)))
  simpa using! h

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The row coefficient for a forward shift: the scaled Taylor matrix at positive history
orders, the identity in padding rows, and zero elsewhere. -/
def taylorForwardRowBlock (m k p : ℕ) (M : Matrix N N ℂ)
    (l : Fin (m*(k+1)+p+1)) : Matrix N N ℂ :=
  if l.val < m*(k+1) ∧ 1 ≤ l.val%(k+1) then
    ((l.val%(k+1) : ℕ) : ℂ)⁻¹ • M
  else if m*(k+1) < l.val then 1 else 0

/-- The block diagonal matrix of forward-row coefficients. -/
def taylorForwardRowMatrix (m k p : ℕ) (M : Matrix N N ℂ) :
    Matrix (Fin (m*(k+1)+p+1) × N) (Fin (m*(k+1)+p+1) × N) ℂ :=
  fun r c => if r.1=c.1 then taylorForwardRowBlock m k p M r.1 r.2 c.2 else 0

/-- When `‖M‖ ≤ 1`, every forward-row coefficient has operator norm at most one. -/
theorem taylorForwardRowBlock_norm (m k p : ℕ) (M : Matrix N N ℂ) (hM : ‖M‖≤1)
    (l : Fin (m*(k+1)+p+1)) : ‖taylorForwardRowBlock m k p M l‖ ≤ 1 := by
  unfold taylorForwardRowBlock
  split_ifs with hs hp
  · have hj : (1 : ℝ) ≤ (l.val%(k+1) : ℕ) := by exact_mod_cast hs.2
    rw [norm_smul,norm_inv,Complex.norm_natCast,inv_mul_eq_div]
    exact (div_le_one (by linarith : (0 : ℝ)<(l.val%(k+1) : ℕ))).mpr (hM.trans hj)
  · exact l2_norm_unitary_le_one (Submonoid.one_mem _)
  · simp

/-- When `‖M‖ ≤ 1`, the block diagonal matrix of forward-row coefficients has operator norm at
most one. -/
theorem taylorForwardRowMatrix_norm (m k p : ℕ) (M : Matrix N N ℂ) (hM : ‖M‖≤1) :
    ‖taylorForwardRowMatrix m k p M‖ ≤ 1 := by
  apply taylor_opNorm_le_of_vec_sq (by norm_num)
  intro x
  have hact (l : Fin (m*(k+1)+p+1)) (n : N) :
      (taylorForwardRowMatrix m k p M *ᵥ x) (l,n) =
        (taylorForwardRowBlock m k p M l *ᵥ taylorBlock x l) n := by
    simp [taylorForwardRowMatrix,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
      ite_mul,Finset.sum_ite_irrel,taylorBlock]
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  simp only [one_pow,one_mul]
  apply Finset.sum_le_sum
  intro l _
  simp_rw [hact]
  have h := taylor_mulVec_sq_le (taylorForwardRowBlock m k p M l) (taylorBlock x l)
  have hn := pow_le_pow_left₀ (norm_nonneg _) (taylorForwardRowBlock_norm m k p M hM l) 2
  simpa only [one_pow,one_mul] using! h.trans (mul_le_mul_of_nonneg_right hn
    (Finset.sum_nonneg (fun _ _ => by positivity)))

/-- The product of the forward-row matrix and the lifted label shift has only the indicated
subdiagonal blocks. -/
theorem taylorForwardRow_shift_entry (m k p : ℕ) (M : Matrix N N ℂ)
    (r c : Fin (m*(k+1)+p+1) × N) :
    (taylorForwardRowMatrix m k p M *
      (taylorShiftLabels (m*(k+1)+p+1) ⊗ₖ (1 : Matrix N N ℂ))) r c =
      if c.1.val+1=r.1.val then taylorForwardRowBlock m k p M r.1 r.2 c.2 else 0 := by
  simp [Matrix.mul_apply,taylorForwardRowMatrix,taylorShiftLabels,
    Fintype.sum_prod_type,mul_ite,Matrix.one_apply]
  rw [Finset.sum_eq_single r.1]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- The V2 Taylor matrix is the identity minus the weighted forward shift and the lifted
jump-label matrix. -/
theorem taylorV2_forward_decomposition (m k p : ℕ) (M : Matrix N N ℂ) :
    taylorStepMatrixV2 m k p M = 1 -
      taylorForwardRowMatrix m k p M *
        (taylorShiftLabels (m*(k+1)+p+1) ⊗ₖ (1 : Matrix N N ℂ)) -
      taylorJumpLabels m k p ⊗ₖ (1 : Matrix N N ℂ) := by
  ext r c
  rw [Matrix.sub_apply,Matrix.sub_apply,taylorForwardRow_shift_entry]
  have hJ : (taylorJumpLabels m k p ⊗ₖ (1 : Matrix N N ℂ)) r c =
      if r.1.val ≤ m*(k+1) ∧ 0 < r.1.val ∧ (k+1) ∣ r.1.val ∧
        r.1.val-(k+1) ≤ c.1.val ∧ c.1.val < r.1.val then
        (if r.2=c.2 then (1 : ℂ) else 0) else 0 := by
    change (if _ then (1 : ℂ) else 0) * (if r.2=c.2 then (1 : ℂ) else 0) = _
    split_ifs <;> norm_num
  have hB : (if c.1.val+1=r.1.val then taylorForwardRowBlock m k p M r.1 r.2 c.2 else 0) =
      (if r.1.val < m*(k+1) ∧ 1 ≤ r.1.val%(k+1) ∧ c.1.val+1=r.1.val then
        M r.2 c.2 / (r.1.val%(k+1) : ℕ) else 0) +
      (if m*(k+1)<r.1.val ∧ c.1.val+1=r.1.val then
        (if r.2=c.2 then (1 : ℂ) else 0) else 0) := by
    by_cases hshift : c.1.val+1=r.1.val
    · by_cases hs : r.1.val < m*(k+1) ∧ 1 ≤ r.1.val%(k+1)
      · have hp : ¬ m*(k+1)<r.1.val := by omega
        simp [taylorForwardRowBlock,hshift,hs.1,hs.2,hp,Matrix.smul_apply,
          smul_eq_mul,div_eq_mul_inv,mul_comm]
      · by_cases hp : m*(k+1)<r.1.val
        · have hnot : ¬ r.1.val < m*(k+1) := by omega
          simp [taylorForwardRowBlock,hshift,hnot,hp,Matrix.one_apply]
        · simp only [hshift,and_true,taylorForwardRowBlock,if_neg hs,if_neg hp,
            if_true,Matrix.zero_apply,add_zero]
    · simp [hshift]
  rw [hJ,hB]
  simp only [taylorStepMatrixV2,Matrix.one_apply]
  ring

/-- For `k ≥ 5` and `‖M‖ ≤ 1`, the V2 Taylor matrix has operator norm at most `2 * sqrt k`. -/
theorem taylorV2_forward_norm_le (m k p : ℕ) (M : Matrix N N ℂ)
    (hk : 5 ≤ k) (hM : ‖M‖≤1) : ‖taylorStepMatrixV2 m k p M‖ ≤ 2*Real.sqrt (k : ℝ) := by
  have hI : ‖(1 : Matrix N N ℂ)‖ ≤ 1 := l2_norm_unitary_le_one (Submonoid.one_mem _)
  have hJ : ‖taylorJumpLabels m k p ⊗ₖ (1 : Matrix N N ℂ)‖ ≤ Real.sqrt (k+1 : ℕ) := by
    rw [l2_norm_kronecker]
    calc _ ≤ ‖taylorJumpLabels m k p‖*1 := mul_le_mul_of_nonneg_left hI (norm_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact taylorJumpLabels_norm m k p
  have hS : ‖taylorShiftLabels (m*(k+1)+p+1) ⊗ₖ (1 : Matrix N N ℂ)‖ ≤ 1 := by
    rw [l2_norm_kronecker]
    calc _ ≤ 1*1 := mul_le_mul (taylorShiftLabels_norm _) hI (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  have hB : ‖taylorForwardRowMatrix m k p M *
      (taylorShiftLabels (m*(k+1)+p+1) ⊗ₖ (1 : Matrix N N ℂ))‖ ≤ 1 := by
    exact (Matrix.l2_opNorm_mul _ _).trans (by
      have hd := taylorForwardRowMatrix_norm m k p M hM
      nlinarith [norm_nonneg (taylorForwardRowMatrix m k p M)])
  rw [taylorV2_forward_decomposition]
  calc
    _ ≤ ‖(1 : Matrix _ _ ℂ)‖ + ‖taylorForwardRowMatrix m k p M *
        (taylorShiftLabels (m*(k+1)+p+1) ⊗ₖ (1 : Matrix N N ℂ))‖ +
        ‖taylorJumpLabels m k p ⊗ₖ (1 : Matrix N N ℂ)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 2+Real.sqrt (k+1 : ℕ) := by
      have hi : ‖(1 : Matrix (Fin (m*(k+1)+p+1) × N) _ ℂ)‖ ≤ 1 :=
        l2_norm_unitary_le_one (Submonoid.one_mem _)
      linarith
    _ ≤ _ := taylor_forward_sqrt_arithmetic k hk

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
