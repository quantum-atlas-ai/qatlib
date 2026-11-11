/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CryptoDisting99.Equivalence.Defs
import Qatlib.Papers.CryptoDisting99.Equivalence.Proposition3

/-!
# Parity mixtures and their trace distance

The operators `bmsPhoton`, `bmsState`, and `bmsMixture` describe the single-system encoding, its
finite product, and parity-selected sums studied in [FuchsVanDeGraaf1999]. A signed-product
calculation reduces the difference of the parity mixtures to a scalar multiple of the
bit-complement matrix.

## Main statements

* `bmsMixture_diff_eq`: the mixture difference is a scaled complement matrix.
* `parityBit_kolmogorov`: for positive length, the trace distance is `|sin (2 * α)| ^ n`.

## References

* [Fuchs and van de Graaf, 1999][FuchsVanDeGraaf1999]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CryptoDisting99.Equivalence

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open scoped Matrix ComplexOrder
open MatrixOrder
open Matrix
set_option warningAsError false

/-- Defines the two-dimensional encoding operator with diagonal entries `cos α ^ 2` and `sin α ^
2` and off-diagonal sign determined by `z`. -/
def bmsPhoton (α : ℝ) (z : Bool) : Operator 2 :=
  fun i j =>
    if i = j then
      (if i = 0 then ((Real.cos α) ^ 2 : ℂ) else ((Real.sin α) ^ 2 : ℂ))
    else
      (if z then ((-(Real.cos α * Real.sin α)) : ℂ) else ((Real.cos α * Real.sin α) : ℂ))

/-- Defines the product encoding matrix with entries equal to the product of the single-system
matrix entries selected by the bit string. -/
noncomputable def bmsState (α : ℝ) (n : ℕ) (z : Fin n → Bool) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun u v => ∏ i, bmsPhoton α (z i) (u i) (v i)

/-- Defines the parity bit by testing whether the number of true entries is odd. -/
def parity (n : ℕ) (z : Fin n → Bool) : Bool :=
  decide ((∑ i : Fin n, (if z i then 1 else 0)) % 2 = 1)

/-- Defines the sum of product encoding matrices of parity `j`, scaled by `1 / 2 ^ (n - 1)`. -/
noncomputable def bmsMixture (α : ℝ) (n : ℕ) (j : Bool) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ((1 : ℂ) / (2 : ℂ) ^ (n - 1)) •
    ∑ z ∈ (Finset.univ.filter (fun z : Fin n → Bool => parity n z = j)), bmsState α n z

/-- Defines half the trace norm of the difference of two matrices on a finite index type. -/
noncomputable def traceDistanceOn {I : Type} [Fintype I] (A B : Matrix I I ℂ) : ℝ :=
  Matrix.traceNorm (A - B) / 2

/-- Defines complementation on `Fin 2`, exchanging zero and one. -/
def bc2 (b : Fin 2) : Fin 2 := if b = 0 then 1 else 0

/-- If two elements of `Fin 2` differ, the first is the complement of the second. -/
lemma bc2_eq_of_ne {a b : Fin 2} (h : a ≠ b) : a = bc2 b := by
  fin_cases a <;> fin_cases b <;> simp_all [bc2]

/-- The complement of an element of `Fin 2` differs from that element. -/
lemma bc2_ne (b : Fin 2) : bc2 b ≠ b := by
  fin_cases b <;> simp [bc2]

/-- Complementing an element of `Fin 2` twice returns it. -/
lemma bc2_involutive (b : Fin 2) : bc2 (bc2 b) = b := by
  fin_cases b <;> simp [bc2]

/-- Defines coordinatewise complementation of a binary-valued function. -/
def bcFun (n : ℕ) : (Fin n → Fin 2) → (Fin n → Fin 2) := fun v i => bc2 (v i)

/-- Coordinatewise complementation is involutive. -/
lemma bcFun_involutive (n : ℕ) : Function.Involutive (bcFun n) := by
  intro v
  funext i
  exact bc2_involutive (v i)

/-- Coordinatewise complementation is injective. -/
lemma bcFun_injective (n : ℕ) : Function.Injective (bcFun n) :=
  (bcFun_involutive n).injective

/-- Two binary-valued functions differ at every coordinate exactly when the first is the
coordinatewise complement of the second. -/
lemma forall_ne_iff_eq_bcFun {n : ℕ} (u v : Fin n → Fin 2) :
    (∀ i, u i ≠ v i) ↔ u = bcFun n v := by
  constructor
  · intro h
    funext i
    exact bc2_eq_of_ne (h i)
  · intro h i
    rw [h]
    show bc2 (v i) ≠ v i
    exact bc2_ne (v i)

/-- Defines the complex sign that is negative one for true and one for false. -/
def bsign (b : Bool) : ℂ := if b then -1 else 1

/-- The product of the bit signs is negative one for odd parity and one for even parity. -/
lemma prod_bsign_eq (n : ℕ) (z : Fin n → Bool) :
    (∏ i, bsign (z i)) = if parity n z then -1 else 1 := by
  have h1 : (∏ i, bsign (z i)) = ∏ i, (-1 : ℂ) ^ (if z i then 1 else 0) := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases hz : z i <;> simp [bsign, hz]
  rw [h1, Finset.prod_pow_eq_pow_sum]
  set m : ℕ := ∑ i, if z i then 1 else 0 with hm
  rw [neg_one_pow_eq_pow_mod_two]
  have hlt : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
  unfold parity
  interval_cases h : m % 2 <;> simp

/-- Expands a product of differences into a sum over Boolean choices with the corresponding
product signs. -/
lemma prod_sub_eq_sum_sign {n : ℕ} (A B : Fin n → ℂ) :
    (∏ i, (A i - B i)) =
      ∑ z : Fin n → Bool, (∏ i, bsign (z i)) * ∏ i, (if z i then B i else A i) := by
  have h1 : (∏ i, (A i - B i)) =
      ∏ i, ∑ b : Bool, (if b then (- B i) else A i) := by
    apply Finset.prod_congr rfl
    intro i _
    simp
    ring
  rw [h1]
  have h2 : (∏ i, ∑ b : Bool, (if b then (- B i) else A i)) =
      ∑ x : Fin n → Bool, ∏ i, (if x i then (- B i) else A i) := by
    simpa using! (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
      (fun i b => (if b then (- B i) else A i)))
  rw [h2]
  apply Finset.sum_congr rfl
  intro z _
  calc ∏ i, (if z i then (- B i) else A i)
      = ∏ i, (bsign (z i) * (if z i then B i else A i)) := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hz : z i <;> simp [bsign, hz]
    _ = (∏ i, bsign (z i)) * ∏ i, (if z i then B i else A i) := by
        rw [Finset.prod_mul_distrib]

/-- The difference between the false-filtered and true-filtered sums equals the sum with signs
determined by the Boolean predicate. -/
lemma sum_filter_false_sub_true {ι M : Type*} [Fintype ι] [AddCommGroup M]
    (p : ι → Bool) (f : ι → M) :
    (∑ x ∈ (Finset.univ.filter (fun x => p x = false)), f x) -
      (∑ x ∈ (Finset.univ.filter (fun x => p x = true)), f x)
    = ∑ x, (if p x then - f x else f x) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : p x <;> simp [h]

/-- Expresses a Boolean signed sum as a sum of scalar multiples by `bsign`. -/
lemma sum_bsign_smul {ι M : Type*} [Fintype ι] [AddCommGroup M] [Module ℂ M]
    (p : ι → Bool) (f : ι → M) :
    (∑ x, (if p x then - f x else f x)) = ∑ x, bsign (p x) • f x := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : p x <;> simp [bsign, h]

/-- The difference between the two single-system encodings is zero on the diagonal and `2 * cos
α * sin α` off the diagonal. -/
lemma bmsPhoton_false_sub_true (α : ℝ) (a b : Fin 2) :
    bmsPhoton α false a b - bmsPhoton α true a b =
      if a = b then 0 else ((2 * (Real.cos α * Real.sin α) : ℝ) : ℂ) := by
  unfold bmsPhoton
  by_cases hab : a = b
  · subst hab; simp
  · fin_cases a <;> fin_cases b <;> simp_all <;> ring

/-- Computes each entry of the parity-signed product-state sum as the product of the
single-system off-diagonal differences. -/
lemma signed_entry (α : ℝ) (n : ℕ) (u v : Fin n → Fin 2) :
    (∑ z : Fin n → Bool, bsign (parity n z) • bmsState α n z) u v =
      ∏ i, (if u i = v i then (0 : ℂ) else ((2 * (Real.cos α * Real.sin α) : ℝ) : ℂ)) := by
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, bmsState, smul_eq_mul]
  set A : Fin n → ℂ := fun i => bmsPhoton α false (u i) (v i) with hA
  set B : Fin n → ℂ := fun i => bmsPhoton α true (u i) (v i) with hB
  calc (∑ z : Fin n → Bool, bsign (parity n z) * ∏ i, bmsPhoton α (z i) (u i) (v i))
      = ∑ z : Fin n → Bool, ∏ i, (bsign (z i) * (if z i then B i else A i)) := by
        apply Finset.sum_congr rfl
        intro z _
        have hp : (∏ i, bmsPhoton α (z i) (u i) (v i)) = ∏ i, (if z i then B i else A i) := by
          apply Finset.prod_congr rfl
          intro i _
          by_cases hz : z i <;> simp [hA, hB, hz]
        rw [show bsign (parity n z) = ∏ i, bsign (z i) from (prod_bsign_eq n z).symm,
          hp, ← Finset.prod_mul_distrib]
    _ = ∑ z : Fin n → Bool, (∏ i, bsign (z i)) * ∏ i, (if z i then B i else A i) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.prod_mul_distrib]
    _ = ∏ i, (A i - B i) := (prod_sub_eq_sum_sign A B).symm
    _ = ∏ i, (if u i = v i then (0 : ℂ) else ((2 * (Real.cos α * Real.sin α) : ℝ) : ℂ)) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [hA, hB, bmsPhoton_false_sub_true]

/-- Defines the matrix obtained by complementing the column index of the identity matrix. -/
def complMat (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.submatrix (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) id (bcFun n)

/-- The trace norm of the identity on length-`n` binary strings is `2 ^ n`. -/
lemma traceNorm_one_fin (n : ℕ) :
    Matrix.traceNorm (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) = 2 ^ n := by
  have h := Matrix.PosSemidef.traceNorm_eq_trace
    (A := (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)) Matrix.PosSemidef.one
  rw [Matrix.trace_one] at h
  have h' : ((Matrix.traceNorm (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : ℝ) : ℂ) =
      ((Fintype.card (Fin n → Fin 2) : ℝ) : ℂ) := by simpa using! h
  have hreal : Matrix.traceNorm (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) =
      (Fintype.card (Fin n → Fin 2) : ℝ) := Complex.ofReal_injective h'
  rw [hreal]
  simp

/-- The trace norm of the bit-complement matrix on length-`n` binary strings is `2 ^ n`. -/
lemma traceNorm_complMat (n : ℕ) : Matrix.traceNorm (complMat n) = 2 ^ n := by
  have hiso : (complMat n)ᴴ * complMat n = 1 := by
    unfold complMat
    rw [Matrix.conjTranspose_submatrix]
    simp only [Matrix.conjTranspose_one]
    rw [← Matrix.submatrix_mul
      (M := (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ))
      (N := (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ))
      (e₁ := bcFun n) (e₂ := id) (e₃ := bcFun n) Function.bijective_id]
    rw [one_mul, Matrix.submatrix_one _ (bcFun_injective n)]
  unfold Matrix.traceNorm
  rw [hiso, CFC.sqrt_one, Matrix.trace_one]
  have hcard : ((Fintype.card (Fin n → Fin 2) : ℂ)) = ((2 : ℝ)^n : ℂ) := by
    push_cast
    simp
  rw [hcard]
  rw [← Complex.ofReal_pow]
  exact RCLike.ofReal_re ((2:ℝ)^n)

/-- Each entry of the parity-signed product-state sum equals `(2 * cos α * sin α) ^ n` times the
corresponding complement-matrix entry. -/
lemma signed_entry_compl (α : ℝ) (n : ℕ) (u v : Fin n → Fin 2) :
    (∑ z : Fin n → Bool, bsign (parity n z) • bmsState α n z) u v =
      ((((2 * (Real.cos α * Real.sin α)) ^ n : ℝ) : ℂ)) * complMat n u v := by
  rw [signed_entry]
  simp only [complMat, Matrix.submatrix_apply, Matrix.one_apply, id]
  by_cases h : ∀ i, u i ≠ v i
  · rw [if_pos ((forall_ne_iff_eq_bcFun u v).mp h)]
    rw [Finset.prod_congr rfl (g := fun _ => ((2 * (Real.cos α * Real.sin α) : ℝ) : ℂ))
      (fun i _ => by simp [h i])]
    rw [Finset.prod_const, ← Complex.ofReal_pow]
    simp
  · rw [if_neg (fun hh => h ((forall_ne_iff_eq_bcFun u v).mpr hh))]
    simp only [mul_zero]
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The difference of the even and odd mixtures is the parity-signed sum of product encoding
matrices scaled by `1 / 2 ^ (n - 1)`. -/
lemma bmsMixture_sub (α : ℝ) (n : ℕ) :
    bmsMixture α n false - bmsMixture α n true
      = ((1:ℂ) / (2:ℂ)^(n-1)) • (∑ z, bsign (parity n z) • bmsState α n z) := by
  unfold bmsMixture
  rw [← smul_sub]
  congr 1
  rw [sum_filter_false_sub_true]
  exact sum_bsign_smul (parity n) (bmsState α n)

/-- The difference of the parity mixtures is the complement matrix scaled by `(2 * cos α * sin
α) ^ n / 2 ^ (n - 1)`. -/
lemma bmsMixture_diff_eq (α : ℝ) (n : ℕ) :
    bmsMixture α n false - bmsMixture α n true
      = ((1:ℂ) / (2:ℂ)^(n-1)) •
          (((((2 * (Real.cos α * Real.sin α)) ^ n : ℝ) : ℂ)) • complMat n) := by
  rw [bmsMixture_sub]
  have hS : (∑ z, bsign (parity n z) • bmsState α n z)
      = ((((2 * (Real.cos α * Real.sin α)) ^ n : ℝ) : ℂ)) • complMat n := by
    ext u v
    rw [Matrix.smul_apply, signed_entry_compl]
    simp [smul_eq_mul]
  rw [hS]

/-- For `n ≥ 1`, the trace distance between the even and odd parity mixtures is `|sin (2 * α)| ^
n`. This is the parity-bit distinguishability formula in [FuchsVanDeGraaf1999]. -/
theorem parityBit_kolmogorov (α : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    traceDistanceOn (bmsMixture α n false) (bmsMixture α n true)
      = |Real.sin (2 * α)| ^ n := by
  unfold traceDistanceOn
  rw [bmsMixture_diff_eq]
  rw [Matrix.traceNorm_smul, Matrix.traceNorm_smul, traceNorm_complMat]
  have hc0 : ‖((1:ℂ) / (2:ℂ)^(n-1))‖ = 1 / (2:ℝ)^(n-1) := by
    rw [norm_div, norm_one, norm_pow]
    norm_num
  have hs : ‖((((2 * (Real.cos α * Real.sin α)) ^ n : ℝ) : ℂ))‖ =
      |2 * (Real.cos α * Real.sin α)| ^ n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_pow]
  rw [hc0, hs]
  have hpow : (2:ℝ) * 2^(n-1) = 2^n := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hn]
  rw [← hpow]
  field_simp
  have hsin : Real.sin (2 * α) = (2:ℝ) * Real.cos α * Real.sin α := by
    rw [Real.sin_two_mul]; ring
  rw [← hsin]

end Qatlib.Papers.CryptoDisting99.Equivalence
