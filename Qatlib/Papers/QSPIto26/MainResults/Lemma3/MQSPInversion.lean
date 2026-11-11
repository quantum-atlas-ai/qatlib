/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSPIto26.MainResults.Core.MQSPCore
import Mathlib.Tactic.Module

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3 — symmetry under inversion of the variables

Ito--Mori--Sakamoto--Fujii, fixed arXiv:2410.02332v3, Lemma 3 (Appendix A, pp. 10--11),
Eqs. (20)--(21).

Lemma 3. If `(P,Q)` is constructible by m-variable M-QSP in `n` steps, then
`P(a^{-1}) = P(a)` and `Q(a^{-1}) = -Q(a)`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSPIto26.MainResults.Lemma3

open Qatlib.Papers.QSPIto26.MainResults.Core

/-! ### Generators under `substInv` -/

/-- `substInv` sends the monomial `a^k` to `a^{-k}`. -/
lemma substInv_mono {m : ℕ} (k : ExpVec m) : substInv m (mono k) = mono (-k) := by
  show AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single k 1) = AddMonoidAlgebra.single (-k) 1
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

/-- `substInv` sends the constant `c` to itself. -/
lemma substInv_C' {m : ℕ} (c : ℂ) : substInv m (C' c) = C' c := by
  show AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single 0 c)
      = AddMonoidAlgebra.single 0 c
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

/-- `substInv` exchanges `a_j` and `a_j^{-1}`. -/
lemma substInv_var {m : ℕ} (j : Fin m) : substInv m (var j) = varInv j := by
  simp only [var, varInv, substInv_mono]
  congr 1
  funext i
  by_cases h : i = j
  · subst h; simp [Pi.single]
  · simp [h]

/-- `substInv` exchanges `a_j^{-1}` and `a_j`. -/
lemma substInv_varInv {m : ℕ} (j : Fin m) : substInv m (varInv j) = var j := by
  simp only [var, varInv, substInv_mono]
  congr 1
  funext i
  by_cases h : i = j
  · subst h; simp [Pi.single]
  · simp [h]

/-! ### The phase operators -/

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

/-- The two exponent merges used for the phase-operator product. -/
lemma exp_pos_add (φ ψ : ℝ) :
    Complex.exp (Complex.I * (φ : ℂ)) * Complex.exp (Complex.I * (ψ : ℂ))
      = Complex.exp (Complex.I * ((φ + ψ : ℝ) : ℂ)) := by
  rw [← Complex.exp_add, Complex.ofReal_add]
  congr 1
  ring

/-- Product of two negative-phase exponentials merges the phases. -/
lemma exp_neg_add (φ ψ : ℝ) :
    Complex.exp (-(Complex.I * (φ : ℂ))) * Complex.exp (-(Complex.I * (ψ : ℂ)))
      = Complex.exp (-(Complex.I * ((φ + ψ : ℝ) : ℂ))) := by
  rw [← Complex.exp_add, Complex.ofReal_add]
  congr 1
  ring

/-- `phaseOp` multiplies by adding angles. -/
lemma phaseOp_mul {m : ℕ} (φ ψ : ℝ) :
    (phaseOp φ : Matrix (Fin 2) (Fin 2) (MLaurent m)) * phaseOp ψ = phaseOp (φ + ψ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseOp, C'_mul_C', exp_pos_add, exp_neg_add]

/-- `phaseOp 0` is the identity matrix. -/
lemma phaseOp_zero {m : ℕ} : (phaseOp (0 : ℝ) : Matrix (Fin 2) (Fin 2) (MLaurent m)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseOp, Complex.exp_zero, C', AddMonoidAlgebra.one_def]

/-- `e^{iπ/2} = i`, in the cast-normalized form produced by `simp`. -/
lemma exp_I_pi_half : Complex.exp (Complex.I * (((Real.pi : ℝ) : ℂ) / 2)) = Complex.I := by
  have h : Complex.I * (((Real.pi : ℝ) : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_mul_I]
  simp

/-- `e^{-iπ/2} = -i`, in the cast-normalized form produced by `simp`. -/
lemma exp_neg_I_pi_half :
    Complex.exp (-(Complex.I * (((Real.pi : ℝ) : ℂ) / 2))) = -Complex.I := by
  have h : -(Complex.I * (((Real.pi : ℝ) : ℂ) / 2))
      = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_mul_I]
  simp

/-- `i · (i · z) = -z`. -/
lemma II_neg (z : ℂ) : Complex.I * (Complex.I * z) = -z := by
  rw [← mul_assoc, Complex.I_mul_I]
  ring

/-! ### The signal operator under `substInv` -/

/-- Entrywise action of `substInv` on the signal operator `A(a_j)`: it exchanges
`a_j ↔ a_j^{-1}`, i.e. negates the off-diagonal entries. -/
lemma map_signalOp {m : ℕ} (j : Fin m) :
    (substInv m).mapMatrix (signalOp j)
      = phaseOp (Real.pi / 2) * signalOp j * phaseOp (-(Real.pi / 2)) := by
  classical
  rw [RingHom.mapMatrix_apply]
  have hoff : C' (2⁻¹ : ℂ) * (varInv j - var j) = -(C' (2⁻¹ : ℂ) * (var j - varInv j)) := by
    ring
  have hmap : Matrix.map (signalOp j) (⇑(substInv m))
      = !![C' (1 / 2 : ℂ) * (varInv j + var j), -(C' (1 / 2 : ℂ) * (var j - varInv j));
           -(C' (1 / 2 : ℂ) * (var j - varInv j)), C' (1 / 2 : ℂ) * (varInv j + var j)] := by
    ext i j'
    fin_cases i <;> fin_cases j' <;>
      simp [Matrix.cons_val', signalOp, Matrix.map_apply, substInv_C', substInv_var,
        substInv_varInv, hoff]
  rw [hmap]
  symm
  ext i j'
  fin_cases i <;> fin_cases j' <;>
    simp [signalOp, phaseOp, exp_I_pi_half, exp_neg_I_pi_half, C'_smul, C'_smul_right]
  all_goals simp only [II_neg]
  all_goals ring

/-- `substInv` fixes the phase operators (they are constant). -/
lemma map_phaseOp {m : ℕ} (φ : ℝ) :
    (substInv m).mapMatrix (phaseOp φ : Matrix (Fin 2) (Fin 2) (MLaurent m)) = phaseOp φ := by
  rw [RingHom.mapMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, Matrix.cons_val', phaseOp, substInv_C']

/-! ### Telescoping -/

/-- The key telescoping identity: mapping `substInv` over a product of mixed
signal/phase factors conjugates the whole product by `phaseOp (π/2)`, because all
phase operators are diagonal and hence commute past each other. -/
lemma telescope {m : ℕ} (L : List (Fin m × ℝ)) :
    (substInv m).mapMatrix ((L.map (fun p => signalOp p.1 * phaseOp p.2)).prod)
      = phaseOp (Real.pi / 2) * ((L.map (fun p => signalOp p.1 * phaseOp p.2)).prod)
          * phaseOp (-(Real.pi / 2)) := by
  induction L with
  | nil =>
      rw [List.map_nil, List.prod_nil, map_one, mul_one, phaseOp_mul,
        add_neg_cancel, phaseOp_zero]
  | cons p L ih =>
      rw [List.map_cons, List.prod_cons, (substInv m).mapMatrix.map_mul,
        (substInv m).mapMatrix.map_mul, map_signalOp, map_phaseOp, ih]
      have hcore : phaseOp (-(Real.pi / 2)) * phaseOp p.2 * phaseOp (Real.pi / 2)
          = (phaseOp p.2 : Matrix (Fin 2) (Fin 2) (MLaurent m)) := by
        rw [phaseOp_mul, phaseOp_mul]
        congr 1
        ring
      have key : ∀ Y : Matrix (Fin 2) (Fin 2) (MLaurent m),
          phaseOp (-(Real.pi / 2)) * (phaseOp p.2 * (phaseOp (Real.pi / 2) * Y))
            = phaseOp p.2 * Y := by
        intro Y
        calc phaseOp (-(Real.pi / 2)) * (phaseOp p.2 * (phaseOp (Real.pi / 2) * Y))
            = phaseOp (-(Real.pi / 2)) * phaseOp p.2 * phaseOp (Real.pi / 2) * Y := by
              rw [Matrix.mul_assoc, Matrix.mul_assoc]
          _ = phaseOp p.2 * Y := by rw [hcore]
      simp only [Matrix.mul_assoc]
      rw [key]

/-- Mapping `substInv` over a full M-QSP word conjugates it by `phaseOp (π/2)`. -/
lemma map_wordMatrix {m n : ℕ} (φ : Fin (n + 1) → ℝ) (s : Fin n → Fin m) :
    (substInv m).mapMatrix (wordMatrix n φ s)
      = phaseOp (Real.pi / 2) * wordMatrix n φ s * phaseOp (-(Real.pi / 2)) := by
  have hlist : (List.ofFn fun k : Fin n => signalOp (s k) * phaseOp (φ k.succ))
      = (List.ofFn fun k : Fin n => (s k, φ k.succ)).map
          (fun p => signalOp p.1 * phaseOp p.2) := by
    rw [List.map_ofFn]
    congr 1
  have ht := telescope (List.ofFn fun k : Fin n => (s k, φ k.succ))
  have hcomm : phaseOp (φ 0) * phaseOp (Real.pi / 2)
      = (phaseOp (Real.pi / 2) : Matrix (Fin 2) (Fin 2) (MLaurent m)) * phaseOp (φ 0) := by
    rw [phaseOp_mul, phaseOp_mul]
    congr 1
    ring
  simp only [wordMatrix, hlist]
  rw [(substInv m).mapMatrix.map_mul, map_phaseOp, ht]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc]

/-! ### Lemma 3 -/

/-- Lemma 3 (arXiv:2410.02332v3, pp. 10--11, Eqs. (20)--(21)): the substitution
`a_j ↦ a_j^{-1}` fixes `P` and negates `Q`. -/
theorem lemma3_inversion {m n : ℕ} (P Q : MLaurent m) (h : Constructible n P Q) :
    substInv m P = P ∧ substInv m Q = -Q := by
  obtain ⟨φ, s, hw⟩ := h
  set W : Matrix (Fin 2) (Fin 2) (MLaurent m) := !![P, Q; -starOp Q, starOp P] with hW
  have h1 := map_wordMatrix (m := m) φ s
  rw [hw] at h1
  have h2 : (substInv m).mapMatrix W
      = !![substInv m P, substInv m Q; -(substInv m (starOp Q)), substInv m (starOp P)] := by
    rw [RingHom.mapMatrix_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, Matrix.cons_val', hW]
  have h3 : phaseOp (Real.pi / 2) * W * phaseOp (-(Real.pi / 2))
      = !![P, -Q; starOp Q, starOp P] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hW, phaseOp, exp_I_pi_half, exp_neg_I_pi_half, C'_smul, C'_smul_right]
    all_goals simp only [II_neg]
    all_goals ring
  rw [h2, h3] at h1
  have e00 := congrFun (congrFun h1 0) 0
  have e01 := congrFun (congrFun h1 0) 1
  exact ⟨e00, e01⟩

end Qatlib.Papers.QSPIto26.MainResults.Lemma3
