/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSPIto26.MainResults.Core.MQSPCore
import Mathlib.Algebra.MonoidAlgebra.Support

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4 — the per-variable degrees of `P` and `Q` coincide

Ito--Mori--Sakamoto--Fujii, fixed arXiv:2410.02332v3, Lemma 4 (Appendix A, p. 11), Eq. (28).

Lemma 4. If `(P,Q)` is constructible by m-variable M-QSP in `n` steps, then
`deg_{a_j} P = deg_{a_j} Q` for every `j ∈ {1,…,m}`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSPIto26.MainResults.Lemma4

open Qatlib.Papers.QSPIto26.MainResults.Core

/-! ### The determinant identity (Eqs. (29)--(33)) -/

/-- Multiplication of constants. -/
lemma C'_mul_C' {m : ℕ} (a b : ℂ) : (C' a : MLaurent m) * C' b = C' (a * b) := by
  simp [C', AddMonoidAlgebra.single_mul_single]

/-- A constant times a polynomial is a scalar multiple. -/
lemma C'_smul {m : ℕ} (c : ℂ) (P : MLaurent m) : C' c * P = c • P := by
  have h1 : C' c = c • (1 : MLaurent m) := by
    simp [C', AddMonoidAlgebra.one_def, smul_eq_mul]
  rw [h1, smul_mul_assoc, one_mul]

/-- A polynomial times a constant is a scalar multiple. -/
lemma C'_smul_right {m : ℕ} (c : ℂ) (P : MLaurent m) : P * C' c = c • P := by
  have h1 : C' c = c • (1 : MLaurent m) := by
    simp [C', AddMonoidAlgebra.one_def, smul_eq_mul]
  rw [h1, mul_smul_comm, mul_one]

/-- The monomials `a_j` and `a_j^{-1}` multiply to `1`. -/
lemma var_mul_varInv {m : ℕ} (j : Fin m) : var j * varInv j = 1 := by
  simp only [var, varInv, mono, AddMonoidAlgebra.single_mul_single, mul_one,
    AddMonoidAlgebra.one_def]
  congr 1
  funext i
  by_cases hi : i = j
  · subst hi; simp [Pi.single]
  · simp [hi]

/-- The determinant of the signal operator is `1`: `det A(a_j) = a_j · a_j^{-1} = 1`
(Eq. (29) of the paper). -/
lemma det_signalOp {m : ℕ} (j : Fin m) : Matrix.det (signalOp j) = 1 := by
  have key : ∀ (c : ℂ) (X Y : MLaurent m), C' c * X * (C' c * Y) = C' (c * c) * (X * Y) := by
    intro c X Y
    rw [mul_mul_mul_comm, C'_mul_C']
  have h4 : (4 : MLaurent m) = C' (4 : ℂ) := rfl
  have hC1 : C' (1 : ℂ) = (1 : MLaurent m) := rfl
  have hsd : (var j + varInv j) * (var j + varInv j) - (var j - varInv j) * (var j - varInv j)
      = 4 * (var j * varInv j) := by
    ring
  simp only [signalOp, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [key, key, ← mul_sub, hsd, h4, ← mul_assoc, C'_mul_C',
    show (1 / 2 : ℂ) * (1 / 2 : ℂ) * 4 = 1 by norm_num, hC1, one_mul, var_mul_varInv]

/-- The determinant of a phase operator is `1`: `e^{iφ} · e^{-iφ} = 1`. -/
lemma det_phaseOp {m : ℕ} (φ : ℝ) :
    Matrix.det (phaseOp φ : Matrix (Fin 2) (Fin 2) (MLaurent m)) = 1 := by
  simp only [phaseOp, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [C'_mul_C', mul_zero, sub_zero,
    show Complex.exp (Complex.I * (φ : ℂ)) * Complex.exp (-(Complex.I * (φ : ℂ))) = 1 by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]]
  rfl

/-- The determinant of an M-QSP word is `1`: the word lies in `SL(2)`. -/
lemma det_wordMatrix {m n : ℕ} (φ : Fin (n + 1) → ℝ) (s : Fin n → Fin m) :
    Matrix.det (wordMatrix n φ s) = 1 := by
  have key : ∀ L : List (Matrix (Fin 2) (Fin 2) (MLaurent m)),
      (∀ X ∈ L, Matrix.det X = 1) → Matrix.det L.prod = 1 := by
    intro L
    induction L with
    | nil => simp
    | cons X L ih =>
        intro h
        rw [List.prod_cons, Matrix.det_mul, h X List.mem_cons_self, one_mul]
        exact ih fun Y hY => h Y (List.mem_cons_of_mem _ hY)
  rw [wordMatrix, Matrix.det_mul, det_phaseOp, one_mul]
  refine key _ fun X hX => ?_
  rw [List.mem_ofFn] at hX
  obtain ⟨k, hk⟩ := hX
  rw [← hk, Matrix.det_mul, det_signalOp, det_phaseOp, one_mul]

/-- The normalization identity (Eq. (33)): `P · P^* + Q · Q^* = 1` for every constructible
pair, obtained by taking the determinant of the word factorization. -/
theorem det_identity {m n : ℕ} (P Q : MLaurent m) (h : Constructible n P Q) :
    P * starOp P + Q * starOp Q = 1 := by
  obtain ⟨φ, s, hw⟩ := h
  have hd := det_wordMatrix (m := m) φ s
  rw [hw, Matrix.det_fin_two] at hd
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg,
    sub_neg_eq_add] at hd
  exact hd

/-! ### Degree arithmetic on the support -/

/-- The `a_j`-degree of a sum is bounded by the maximum of the degrees. -/
lemma degVar_add_le {m : ℕ} (j : Fin m) (X Y : MLaurent m) :
    degVar j (X + Y) ≤ degVar j X ⊔ degVar j Y := by
  simp only [degVar]
  have hs : (X + Y).coeff.support ⊆ X.coeff.support ∪ Y.coeff.support := by
    simpa only [AddMonoidAlgebra.coeff_add] using
      (show (X.coeff + Y.coeff).support ⊆ X.coeff.support ∪ Y.coeff.support from
        Finsupp.support_add)
  exact le_trans (Finset.sup_mono hs) (by rw [Finset.sup_union])

/-- The `a_j`-degree of a product is subadditive. -/
lemma degVar_mul_le {m : ℕ} (j : Fin m) (X Y : MLaurent m) :
    degVar j (X * Y) ≤ degVar j X + degVar j Y := by
  simp only [degVar]
  refine Finset.sup_le fun k hk => ?_
  obtain ⟨p, hp, q, hq, heq⟩ := Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset X Y hk)
  subst heq
  exact Nat.le_trans (Int.natAbs_add_le (p j) (q j))
    (Nat.add_le_add (Finset.le_sup (f := fun k => Int.natAbs (k j)) hp)
      (Finset.le_sup (f := fun k => Int.natAbs (k j)) hq))

/-- The `a_j`-degree of the constant `1` is zero. -/
lemma degVar_one {m : ℕ} (j : Fin m) : degVar j (1 : MLaurent m) = 0 := by
  simp [degVar, AddMonoidAlgebra.one_def]

/-- The `a_j`-degree of the constant `0` is zero. -/
lemma degVar_zero {m : ℕ} (j : Fin m) : degVar j (0 : MLaurent m) = 0 := by
  simp [degVar]

/-- Interface version of Lemma 4. The missing general ingredient is the
lex-leading-monomial computation of Eqs. (31)--(32): the top `a_j`-slice of
`X · X^*` is nonzero, i.e. `deg_{a_j}(X · X^*) = 2 deg_{a_j} X` whenever `X ≠ 0`.
Everything else — the `SU(2)` determinant identity and the support degree
arithmetic — is proved above. -/
theorem lemma4_degree_eq {m n : ℕ} (P Q : MLaurent m) (h : Constructible n P Q)
    (hlead : ∀ (X : MLaurent m) (j : Fin m), X ≠ 0 →
      degVar j (X * starOp X) = 2 * degVar j X) :
    ∀ j : Fin m, degVar j P = degVar j Q := by
  have hid := det_identity P Q h
  intro j
  by_cases hp : P = 0
  · subst hp
    rw [zero_mul, zero_add] at hid
    by_cases hq : Q = 0
    · subst hq
      rfl
    · have h2 := hlead Q j hq
      rw [hid, degVar_one] at h2
      have hq0 : degVar j Q = 0 := by omega
      rw [hq0, degVar_zero]
  · by_cases hq : Q = 0
    · subst hq
      rw [zero_mul, add_zero] at hid
      have h2 := hlead P j hp
      rw [hid, degVar_one] at h2
      rw [degVar_zero]
      omega
    · -- both nonzero: `P · P^* = 1 - Q · Q^*` bounds `2 deg P` by `2 deg Q`, and vice versa
      have hnegQ : degVar j (-(Q * starOp Q)) = degVar j (Q * starOp Q) := by simp [degVar]
      have hnegP : degVar j (-(P * starOp P)) = degVar j (P * starOp P) := by simp [degVar]
      have hrwP : P * starOp P = 1 - Q * starOp Q := by linear_combination hid
      have hrwQ : Q * starOp Q = 1 - P * starOp P := by linear_combination hid
      have hleP : degVar j (P * starOp P) ≤ degVar j (Q * starOp Q) := by
        calc degVar j (P * starOp P) = degVar j (1 - Q * starOp Q) := by rw [hrwP]
          _ = degVar j (1 + -(Q * starOp Q)) := by rw [sub_eq_add_neg]
          _ ≤ degVar j (1 : MLaurent m) ⊔ degVar j (-(Q * starOp Q)) :=
              degVar_add_le j _ _
          _ = degVar j (Q * starOp Q) := by rw [hnegQ, degVar_one]; simp
      have hleQ : degVar j (Q * starOp Q) ≤ degVar j (P * starOp P) := by
        calc degVar j (Q * starOp Q) = degVar j (1 - P * starOp P) := by rw [hrwQ]
          _ = degVar j (1 + -(P * starOp P)) := by rw [sub_eq_add_neg]
          _ ≤ degVar j (1 : MLaurent m) ⊔ degVar j (-(P * starOp P)) :=
              degVar_add_le j _ _
          _ = degVar j (P * starOp P) := by rw [hnegP, degVar_one]; simp
      have hA := hlead P j hp
      have hB := hlead Q j hq
      omega

end Qatlib.Papers.QSPIto26.MainResults.Lemma4
