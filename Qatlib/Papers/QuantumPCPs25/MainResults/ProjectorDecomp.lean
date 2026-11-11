/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option backward.isDefEq.respectTransparency false

/-!
# Projector decomposition into Pauli-`Z` unitaries — Lemma 7

Paper: *Quantum PCPs: on Adaptivity, Multiple Provers and Reductions to Local
Hamiltonians* (arXiv:2403.04841), Lemma 7 (Eq. (35)).

A basis projector `Π_q = |q⟩⟨q|` on `k` qubits factors as a tensor product of
single-qubit terms and expands as `(2^k)⁻¹ ∑_S a_S U_S` where each `U_S` is a
diagonal sign matrix (an element of `{I, Z}^⊗k`) and `a_S ∈ {±1}`.

Sign correction: the paper prints `Π_q = ⊗_i (Z_i + (1−2q_i)I)/2`, whose
diagonal value at `x = q` is `∏_i (−1)^{q_i} = (−1)^{|q|_H}` rather than `1`;
the correct term is `(I + (−1)^{q_i} Z_i)/2`, which is what is formalised here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumPCPs25.MainResults.ProjectorDecomp

open Matrix

abbrev F2k (k : ℕ) := Fin k → ZMod 2

/-- Case split on `ZMod 2`. -/
lemma z2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The sign `(−1)^b ∈ {±1} ⊆ ℂ` of a bit. -/
def sgn (b : ZMod 2) : ℂ := 1 - 2 * ((b.val : ℕ) : ℂ)

/-- The `Z` operator on qubit `i` of `k` qubits (diagonal sign matrix). -/
def zMat (k : ℕ) (i : Fin k) : Matrix (F2k k) (F2k k) ℂ :=
  Matrix.diagonal fun x => sgn (x i)

/-- The basis projector `Π_q = |q⟩⟨q|` as a diagonal matrix. -/
def piQ (k : ℕ) (q : F2k k) : Matrix (F2k k) (F2k k) ℂ :=
  Matrix.diagonal fun x => if x = q then 1 else 0

/-- The diagonal sign matrix `U_S = ⊗_{i ∈ S} Z_i ∈ {I, Z}^⊗k`. -/
def uS (k : ℕ) (S : Finset (Fin k)) : Matrix (F2k k) (F2k k) ℂ :=
  Matrix.diagonal fun x => ∏ i ∈ S, sgn (x i)

/-! ### Diagonal-matrix plumbing -/

/-- The sign of a bit is `±1`. -/
lemma z2_cases' (b : ZMod 2) : sgn b = 1 ∨ sgn b = -1 := by
  rcases z2_cases b with rfl | rfl
  · exact Or.inl (by simp [sgn])
  · have hv : (ZMod.val (1 : ZMod 2)) = 1 := by decide
    exact Or.inr (by simp only [sgn, hv]; norm_num)

/-- The identity matrix is the diagonal of the constant-one function. -/
lemma one_diagonal (k : ℕ) :
    (1 : Matrix (F2k k) (F2k k) ℂ) = Matrix.diagonal (fun _ => 1) := by
  ext x y
  by_cases h : x = y
  · subst h
    simp only [Matrix.one_apply, Matrix.diagonal_apply]
  · simp [Matrix.one_apply_ne h, Matrix.diagonal_apply, if_neg h]

/-- Pointwise sums of diagonal matrices are diagonal. -/
lemma add_diagonal (k : ℕ) (f g : F2k k → ℂ) :
    Matrix.diagonal f + Matrix.diagonal g = Matrix.diagonal (f + g) := by
  ext x y
  by_cases h : x = y
  · subst h; simp [Matrix.diagonal]
  · simp [Matrix.diagonal_apply, if_neg h]

/-- Scalar multiples of diagonal matrices are diagonal. -/
lemma smul_diagonal (k : ℕ) (c : ℂ) (f : F2k k → ℂ) :
    c • Matrix.diagonal f = Matrix.diagonal (c • f) := by
  ext x y
  by_cases h : x = y
  · subst h; simp [Matrix.diagonal]
  · simp [Matrix.diagonal_apply, if_neg h]

/-- Products of diagonal matrices are diagonal (pointwise product). -/
lemma mul_diagonal (k : ℕ) (f g : F2k k → ℂ) :
    Matrix.diagonal f * Matrix.diagonal g = Matrix.diagonal (f * g) := by
  ext x y
  by_cases h : x = y
  · subst h
    simp only [Matrix.mul_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb
      simp [if_neg (Ne.symm hb), if_neg hb]
    · intro h
      exact absurd (Finset.mem_univ x) h
  · simp [Matrix.diagonal_apply, if_neg h]

/-- Pointwise factor identity:
`(1 + (−1)^{q_i} (−1)^{x_i})/2 = 1[x_i = q_i]`. -/
lemma factor_eq_indicator (b c : ZMod 2) :
    (2 : ℂ)⁻¹ * (1 + sgn b * sgn c) = if c = b then 1 else 0 := by
  have hv0 : (ZMod.val (0 : ZMod 2)) = 0 := by decide
  have hv1 : (ZMod.val (1 : ZMod 2)) = 1 := by decide
  rcases z2_cases b with rfl | rfl <;> rcases z2_cases c with rfl | rfl
  all_goals simp only [sgn, hv0, hv1]
  all_goals try rw [if_neg (by decide)]
  all_goals norm_num

/-- **Lemma 7, product form (corrected sign)**:
`Π_q = ⊗_{i∈[k]} (I + (−1)^{q_i} Z_i)/2`.  The tensor product of the diagonal
single-qubit operators is encoded as the pointwise product in the diagonal
(datum) representation. -/
theorem lemma7_product (k : ℕ) (q : F2k k) :
    piQ k q = Matrix.diagonal
      (∏ i : Fin k, fun x => (2 : ℂ)⁻¹ * (1 + sgn (q i) * sgn (x i))) := by
  ext x y
  by_cases h : x = y
  · subst h
    simp only [piQ, Matrix.diagonal_apply, Finset.prod_apply]
    rw [Finset.prod_congr rfl (fun i _ => factor_eq_indicator (q i) (x i))]
    by_cases hxq : x = q
    · subst hxq
      rw [Finset.prod_eq_one (fun i _ => if_pos rfl)]
      simp
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ q i := by
        by_contra hc
        push Not at hc
        exact hxq (funext fun i => hc i)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), if_neg hxq]
  · simp [piQ, Matrix.diagonal_apply, if_neg h]

/-- Finite sums of diagonal matrices are the diagonals of pointwise sums. -/
lemma sum_diagonal (k : ℕ) (ι : Type*) [Fintype ι] (g : ι → (F2k k → ℂ)) :
    ∑ S, Matrix.diagonal (g S) = Matrix.diagonal (∑ S, g S) := by
  classical
  let e : (F2k k → ℂ) →+ Matrix (F2k k) (F2k k) ℂ :=
    { toFun := Matrix.diagonal
      map_zero' := by
        ext a b
        by_cases hab : a = b <;> simp [Matrix.diagonal, hab]
      map_add' := fun f g => (add_diagonal k f g).symm }
  calc ∑ S, Matrix.diagonal (g S) = ∑ S, e (g S) := rfl
    _ = e (∑ S, g S) := (map_sum e g Finset.univ).symm
    _ = Matrix.diagonal (∑ S, g S) := rfl

/-! ### Lemma 7, unitary-expansion form -/

/-- Pointwise subset expansion of the product of corrected single-qubit terms. -/
lemma prod_eq_subset_sum (k : ℕ) (q x : F2k k) :
    (∏ i : Fin k, (2 : ℂ)⁻¹ * (1 + sgn (q i) * sgn (x i)))
      = ((2 ^ k : ℕ) : ℂ)⁻¹ * ∑ S : Finset (Fin k),
          (∏ i ∈ S, sgn (q i)) * (∏ i ∈ S, sgn (x i)) := by
  classical
  have hpow : ((2 ^ k : ℕ) : ℂ)⁻¹ = ((2 : ℂ)⁻¹ ^ k) := by
    rw [Nat.cast_pow, inv_pow]
    norm_num
  have hsplit : ∀ i : Fin k,
      (2 : ℂ)⁻¹ * (1 + sgn (q i) * sgn (x i))
        = ((2 : ℂ)⁻¹ * sgn (q i) * sgn (x i)) + (2 : ℂ)⁻¹ := by
    intro i; ring
  have hc : ∀ S : Finset (Fin k),
      ∏ i ∈ S, ((2 : ℂ)⁻¹ * sgn (q i) * sgn (x i))
        = ((2 : ℂ)⁻¹ ^ S.card)
            * ((∏ i ∈ S, sgn (q i)) * (∏ i ∈ S, sgn (x i))) := by
    intro S
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const]
    ring
  have hd : ∀ S : Finset (Fin k),
      ∏ i ∈ Finset.univ \ S, (2 : ℂ)⁻¹
        = ((2 : ℂ)⁻¹ ^ (Finset.univ \ S).card) := fun S => Finset.prod_const _
  have hcard : ∀ S : Finset (Fin k),
      S.card + (Finset.univ \ S).card = k := by
    intro S
    have h := Finset.card_add_card_compl S
    rw [Finset.compl_eq_univ_sdiff, Fintype.card_fin] at h
    exact h
  have hterm : ∀ S : Finset (Fin k),
      (∏ i ∈ S, ((2 : ℂ)⁻¹ * sgn (q i) * sgn (x i)))
          * ∏ i ∈ Finset.univ \ S, (2 : ℂ)⁻¹
        = ((2 : ℂ)⁻¹ ^ k)
            * ((∏ i ∈ S, sgn (q i)) * (∏ i ∈ S, sgn (x i))) := by
    intro S
    calc (∏ i ∈ S, ((2 : ℂ)⁻¹ * sgn (q i) * sgn (x i)))
            * ∏ i ∈ Finset.univ \ S, (2 : ℂ)⁻¹
        = (((2 : ℂ)⁻¹ ^ S.card)
              * ((∏ i ∈ S, sgn (q i)) * (∏ i ∈ S, sgn (x i))))
            * ((2 : ℂ)⁻¹ ^ (Finset.univ \ S).card) := by rw [hc S, hd S]
      _ = ((2 : ℂ)⁻¹ ^ k)
              * ((∏ i ∈ S, sgn (q i)) * (∏ i ∈ S, sgn (x i))) := by
            have h2 : ((2 : ℂ)⁻¹ ^ S.card) * ((2 : ℂ)⁻¹ ^ (Finset.univ \ S).card)
                = ((2 : ℂ)⁻¹ ^ k) := by rw [← pow_add, hcard S]
            rw [← h2]
            ring
  rw [Finset.prod_congr rfl (fun i _ => hsplit i), Finset.prod_add,
    Finset.powerset_univ, Finset.sum_congr rfl (fun S _ => hterm S), hpow,
    ← Finset.mul_sum]

/-- A scalar times a sum of diagonal matrices is the diagonal of the scaled
pointwise sum. -/
lemma smul_sum_diagonal (k : ℕ) (c : ℂ) (g : Finset (Fin k) → (F2k k → ℂ)) :
    c • ∑ S, Matrix.diagonal (g S)
      = Matrix.diagonal (fun x => c * ∑ S, g S x) := by
  rw [Finset.smul_sum, Finset.sum_congr rfl (fun S _ => smul_diagonal k c (g S)),
    sum_diagonal]
  have hFn : (∑ S, c • g S) = fun x => c * ∑ S, g S x := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
  rw [hFn]

/-- **Lemma 7, unitary expansion**:
`Π_q = (2^k)⁻¹ ∑_S a_S U_S` with `a_S = ∏_{i∈S} (−1)^{q_i} ∈ {±1}` and
`U_S = ⊗_{i∈S} Z_i ∈ {I, Z}^⊗k`. -/
theorem lemma7_unitary_sum (k : ℕ) (q : F2k k) :
    piQ k q = ((2 ^ k : ℕ) : ℂ)⁻¹ • ∑ S : Finset (Fin k),
      (∏ i ∈ S, sgn (q i)) • uS k S := by
  have h1 : ∀ S : Finset (Fin k),
      (∏ i ∈ S, sgn (q i)) • uS k S
        = Matrix.diagonal (fun x => (∏ i ∈ S, sgn (q i)) * ∏ i ∈ S, sgn (x i)) := by
    intro S
    rw [uS, smul_diagonal]
    rfl
  calc piQ k q = Matrix.diagonal
          (∏ i : Fin k, fun x => (2 : ℂ)⁻¹ * (1 + sgn (q i) * sgn (x i))) :=
        lemma7_product k q
    _ = Matrix.diagonal
          (fun x => ((2 ^ k : ℕ) : ℂ)⁻¹ * ∑ S : Finset (Fin k),
            (∏ i ∈ S, sgn (q i)) * ∏ i ∈ S, sgn (x i)) := by
          have hFn : (∏ i : Fin k, fun t : F2k k =>
                (2 : ℂ)⁻¹ * (1 + sgn (q i) * sgn (t i)))
              = fun x : F2k k => ((2 ^ k : ℕ) : ℂ)⁻¹ * ∑ S : Finset (Fin k),
                  (∏ i ∈ S, sgn (q i)) * ∏ i ∈ S, sgn (x i) := by
            funext x
            rw [Finset.prod_apply]
            exact prod_eq_subset_sum k q x
          rw [hFn]
    _ = ((2 ^ k : ℕ) : ℂ)⁻¹ • ∑ S : Finset (Fin k),
          Matrix.diagonal (fun x => (∏ i ∈ S, sgn (q i)) * ∏ i ∈ S, sgn (x i)) := by
          exact (smul_sum_diagonal k _ fun S x =>
            (∏ i ∈ S, sgn (q i)) * ∏ i ∈ S, sgn (x i)).symm
    _ = ((2 ^ k : ℕ) : ℂ)⁻¹ • ∑ S : Finset (Fin k),
          (∏ i ∈ S, sgn (q i)) • uS k S := by
          refine congrArg (((2 ^ k : ℕ) : ℂ)⁻¹ • ·) ?_
          exact Finset.sum_congr rfl (fun S _ => (h1 S).symm)

/-- Every `U_S` is self-inverse; in particular it is unitary (as a diagonal
matrix with `±1` entries). -/
theorem uS_selfinv (k : ℕ) (S : Finset (Fin k)) :
    uS k S * uS k S = 1 := by
  have hU : uS k S = Matrix.diagonal (fun x => ∏ i ∈ S, sgn (x i)) := rfl
  rw [hU, mul_diagonal, one_diagonal]
  ext x y
  by_cases h : x = y
  · subst h
    have hsq : ∀ i ∈ S, sgn (x i) * sgn (x i) = 1 := by
      intro i _
      rcases z2_cases' (x i) with h | h <;> rw [h] <;> simp
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Pi.mul_apply,
      ← Finset.prod_mul_distrib, Finset.prod_eq_one hsq]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]
