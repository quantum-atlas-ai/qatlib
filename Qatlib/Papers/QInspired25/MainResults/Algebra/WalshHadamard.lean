/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QInspired25.MainResults.Model.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# The `n`-qubit Hadamard matrix `H^{⊗n}` on bit strings

Fixed source: arXiv:2402.15686v3, proof of Proposition 13 (p. 9).

The paper writes `D_f H^{⊗n}` with `H = 1/√2 [[1,1],[1,-1]]` the one-qubit Hadamard.
We represent `H^{⊗n}` by its entries on bit strings, which is the standard Walsh–Hadamard
matrix

`H^{⊗n} x y = (1/√2)^n · ∏_{i<n} (-1)^{x_i y_i}`,

written recursively as

* `walsh 0 x y = 1`,
* `walsh (n+1) x y = (1/√2) · eps (x 0) (y 0) · walsh n (tail x) (tail y)`.

The two facts used in the proof of Proposition 13 are proved here:

* `walsh_orthogonal` : the rows are orthonormal, equivalently `(H^{⊗n})ᵀ (H^{⊗n}) = 1`
  (`walsh_transpose_mul`); this yields `κ = σ_min = 1`;
* `walsh_frobSq` : `‖H^{⊗n}‖_F² = 2ⁿ`, which together with orthonormality gives
  `κ_F² = 2ⁿ` (`walsh_condFSq`).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QInspired25.MainResults.Algebra

open Qatlib.Papers.QInspired25.MainResults.Model

/-! ## §1. Signs and the recursive matrix -/

/-- The sign `(-1)^{a ∧ b}` for bits `a b`. -/
def epsSign (a b : Bool) : ℝ := if a = true ∧ b = true then -1 else 1

/-- The sign `epsSign a b` is `±1`, so its square is one. -/
theorem epsSign_sq (a b : Bool) : epsSign a b * epsSign a b = 1 := by
  unfold epsSign
  by_cases h : a = true ∧ b = true <;> simp [h]

/-- The sign attached to a pair of bits is symmetric. -/
theorem epsSign_comm (a b : Bool) : epsSign a b = epsSign b a := by
  unfold epsSign
  by_cases h : a = true ∧ b = true
  · have h' : b = true ∧ a = true := ⟨h.2, h.1⟩
    simp [h, h']
  · have h' : ¬(b = true ∧ a = true) := fun hh => h ⟨hh.2, hh.1⟩
    simp [h, h']

/-- The squared normalization `(1/√2)^2` equals `1/2`. -/
theorem half_sqrt_two_sq : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
  have h : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  linarith

/-- The `n`-qubit Walsh–Hadamard matrix on bit strings, i.e. `H^{⊗n}`. -/
noncomputable def walsh : (n : ℕ) → Matrix (Fin n → Bool) (Fin n → Bool) ℝ
  | 0 => fun _ _ => 1
  | n + 1 => fun x y =>
      (1 / Real.sqrt 2) * epsSign (x 0) (y 0) * walsh n (Fin.tail x) (Fin.tail y)

/-- The empty Walsh–Hadamard matrix has the single entry one. -/
@[simp] theorem walsh_zero (x y : Fin 0 → Bool) : walsh 0 x y = 1 := rfl

/-- Recursive entry formula for the Walsh–Hadamard matrix at `n+1`. -/
theorem walsh_succ {n : ℕ} (x y : Fin (n + 1) → Bool) :
    walsh (n + 1) x y =
      (1 / Real.sqrt 2) * epsSign (x 0) (y 0) * walsh n (Fin.tail x) (Fin.tail y) := rfl

/-- `H^{⊗n}` is symmetric. -/
theorem walsh_comm : ∀ (n : ℕ) (x y : Fin n → Bool), walsh n x y = walsh n y x
  | 0, _, _ => rfl
  | n + 1, x, y => by
      rw [walsh_succ, walsh_succ, epsSign_comm (x 0) (y 0),
        walsh_comm n (Fin.tail y) (Fin.tail x)]

/-! ## §2. Orthogonality of the rows -/

/-- Walsh–Hadamard rows are orthogonal. -/
theorem walsh_orthogonal : ∀ (n : ℕ) (x x' : Fin n → Bool),
    (∑ y : Fin n → Bool, walsh n x y * walsh n x' y) = if x = x' then 1 else 0
  | 0, x, x' => by
      have h : x = x' := Subsingleton.elim x x'
      simp [walsh, h]
  | n + 1, x, x' => by
      classical
      -- reindex `Fin (n+1) → Bool` by a bit and a tail
      have hreindex :
          (∑ y : Fin (n + 1) → Bool, walsh (n + 1) x y * walsh (n + 1) x' y)
            = ∑ p : Bool × (Fin n → Bool),
                walsh (n + 1) x (Fin.cons p.1 p.2) * walsh (n + 1) x' (Fin.cons p.1 p.2) := by
        rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
          (fun y => walsh (n + 1) x y * walsh (n + 1) x' y)]
        rfl
      rw [hreindex, Fintype.sum_prod_type]
      -- inner sum over the tail keeps the `1/2` from the two `1/√2` factors
      have hinner : ∀ b : Bool,
          (∑ u : Fin n → Bool,
              walsh (n + 1) x (Fin.cons b u) * walsh (n + 1) x' (Fin.cons b u))
            = (1 / 2 : ℝ) * (epsSign (x 0) b * epsSign (x' 0) b) *
                (if Fin.tail x = Fin.tail x' then 1 else 0) := by
        intro b
        have hpt : ∀ u : Fin n → Bool,
            walsh (n + 1) x (Fin.cons b u) * walsh (n + 1) x' (Fin.cons b u)
              = (1 / 2 : ℝ) * (epsSign (x 0) b * epsSign (x' 0) b) *
                  (walsh n (Fin.tail x) u * walsh n (Fin.tail x') u) := by
          intro u
          rw [walsh_succ, walsh_succ]
          simp only [Fin.cons_zero, Fin.tail_cons]
          calc ((1 / Real.sqrt 2) * epsSign (x 0) b * walsh n (Fin.tail x) u) *
                ((1 / Real.sqrt 2) * epsSign (x' 0) b * walsh n (Fin.tail x') u)
              = ((1 / Real.sqrt 2) * (1 / Real.sqrt 2)) *
                  (epsSign (x 0) b * epsSign (x' 0) b) *
                  (walsh n (Fin.tail x) u * walsh n (Fin.tail x') u) := by ring
            _ = (1 / 2 : ℝ) * (epsSign (x 0) b * epsSign (x' 0) b) *
                  (walsh n (Fin.tail x) u * walsh n (Fin.tail x') u) := by
                rw [half_sqrt_two_sq]
        simp only [hpt, ← Finset.mul_sum]
        rw [walsh_orthogonal n (Fin.tail x) (Fin.tail x')]
      simp only [hinner]
      -- outer sum over the leading bit
      have hsum_b :
          (∑ b : Bool, epsSign (x 0) b * epsSign (x' 0) b) = if x 0 = x' 0 then 2 else 0 := by
        cases hx : x 0 <;> cases hx' : x' 0 <;>
          simp [hx, hx', epsSign, Fintype.sum_bool] <;> norm_num
      have hstep :
          (∑ b : Bool, (1 / 2 : ℝ) * (epsSign (x 0) b * epsSign (x' 0) b) *
              (if Fin.tail x = Fin.tail x' then 1 else 0))
            = (1 / 2 : ℝ) * (if Fin.tail x = Fin.tail x' then 1 else 0) *
                (∑ b : Bool, epsSign (x 0) b * epsSign (x' 0) b) := by
        have hrearr : (∑ b : Bool, (1 / 2 : ℝ) * (epsSign (x 0) b * epsSign (x' 0) b) *
              (if Fin.tail x = Fin.tail x' then 1 else 0))
            = ∑ b : Bool, ((1 / 2 : ℝ) * (if Fin.tail x = Fin.tail x' then 1 else 0)) *
                (epsSign (x 0) b * epsSign (x' 0) b) := by
          apply Finset.sum_congr rfl
          intro b _
          ring
        rw [hrearr, ← Finset.mul_sum]
      rw [hstep, hsum_b]
      -- assemble `if x = x' then 1 else 0`
      by_cases h0 : x 0 = x' 0
      · by_cases ht : Fin.tail x = Fin.tail x'
        · have hxx' : x = x' := by
            rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail x', h0, ht]
          rw [if_pos hxx']
          simp [h0, ht]
        · have hne : x ≠ x' := fun h => ht (by rw [h])
          rw [if_neg hne]
          simp [h0, ht]
      · have hne : x ≠ x' := fun h => h0 (by rw [h])
        rw [if_neg hne]
        simp [h0]

/-- `(H^{⊗n})ᵀ (H^{⊗n}) = 1`: the columns are orthonormal, so `σ_min = σ_max = 1`. -/
theorem walsh_transpose_mul (n : ℕ) : (walsh n)ᵀ * walsh n = 1 := by
  classical
  ext y y'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h : (∑ x : Fin n → Bool, walsh n y x * walsh n y' x) = if y = y' then 1 else 0 :=
    walsh_orthogonal n y y'
  calc (∑ x : Fin n → Bool, (walsh n)ᵀ y x * walsh n x y')
      = ∑ x : Fin n → Bool, walsh n y x * walsh n y' x := by
        apply Finset.sum_congr rfl
        intro x _
        show walsh n x y * walsh n x y' = walsh n y x * walsh n y' x
        rw [walsh_comm n x y, walsh_comm n x y']
    _ = if y = y' then 1 else 0 := h

/-! ## §3. The Frobenius norm -/

/-- Squared Frobenius norm over arbitrary finite index types. -/
def frobSqMatGen {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- `‖H^{⊗n}‖_F² = 2ⁿ`, the computation used for `κ_F²` in Proposition 13. -/
theorem walsh_frobSq (n : ℕ) : frobSqMatGen (walsh n) = (2 : ℝ) ^ n := by
  classical
  unfold frobSqMatGen
  have hrow : ∀ x : Fin n → Bool, (∑ y : Fin n → Bool, walsh n x y ^ 2) = 1 := by
    intro x
    have h := walsh_orthogonal n x x
    rw [if_pos rfl] at h
    simpa [sq] using h
  simp only [hrow, Finset.sum_const, Finset.card_univ]
  rw [Fintype.card_pi_const]
  simp

/-- **Proposition 13, parameter computation (p. 9).**  For `A = D_f H^{⊗n}` the squared
Frobenius norm is `2ⁿ` and `σ_min = 1`, so `κ_F² = ‖A‖_F²/σ_min² = 2ⁿ`. -/
theorem walsh_condFSq (n : ℕ) : frobSqMatGen (walsh n) / 1 = (2 : ℝ) ^ n := by
  rw [walsh_frobSq, div_one]

end Qatlib.Papers.QInspired25.MainResults.Algebra
