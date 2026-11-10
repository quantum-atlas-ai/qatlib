/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.LieStrang

namespace Qatlib.Papers.AdiabPower02.MainResults
namespace Theorem1

def hadamardGate : Matrix (Fin 2) (Fin 2) ℂ := (Real.sqrt 2 : ℂ)⁻¹ • !![1,1;1,-1]

theorem hadamardGate_mul_self : hadamardGate * hadamardGate = 1 := by
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hM : (!![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℂ) * !![1,1;1,-1] = (2 : ℂ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  unfold hadamardGate
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hM, smul_smul]
  have hs2 : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * 2 = 1 := by
    rw [← mul_inv, hs]
    norm_num
  rw [hs2, one_smul]

theorem kronecker_mul_self {l n : Type} [Fintype l] [Fintype n]
    [DecidableEq l] [DecidableEq n]
    (A : Matrix l l ℂ) (B : Matrix n n ℂ) (hA : A * A = 1) (hB : B * B = 1) :
    (A ⊗ₖ B) * (A ⊗ₖ B) = 1 := by
  rw [← Matrix.mul_kronecker_mul, hA, hB, Matrix.one_kronecker_one]

theorem exp_diagonal_smul {I : Type} [Fintype I] [DecidableEq I] (v : I → ℂ) (c : ℂ) :
    NormedSpace.exp (c • Matrix.diagonal v)
      = Matrix.diagonal (fun i => NormedSpace.exp (c * v i)) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext i
  simp [Pi.smul_apply, smul_eq_mul]

theorem phase_gate_diagonal {I : Type} [Fintype I] [DecidableEq I] (v : I → ℝ) (t : ℝ) :
    HamiltonianEvolution (Matrix.diagonal (fun i => (v i : ℂ))) t
      = Matrix.diagonal (fun i => NormedSpace.exp ((-Complex.I * (t : ℂ)) * (v i : ℂ))) := by
  unfold HamiltonianEvolution
  rw [exp_diagonal_smul]

theorem gate_factorization {I : Type} [Fintype I] [DecidableEq I]
    (W D0 Df : Matrix I I ℂ) (hW : W * W = 1) (a b : ℝ) :
    HamiltonianEvolution (W * D0 * W) a * HamiltonianEvolution Df b
      = W * HamiltonianEvolution D0 a * W * HamiltonianEvolution Df b := by
  have hconj : HamiltonianEvolution (W * D0 * W) a
      = W * HamiltonianEvolution D0 a * W := by
    unfold HamiltonianEvolution
    have hsmul : (-Complex.I * (a : ℂ)) • (W * D0 * W)
        = W * ((-Complex.I * (a : ℂ)) • D0) * W := by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    rw [hsmul]
    let u : (Matrix I I ℂ)ˣ := ⟨W, W, hW, hW⟩
    have h := Matrix.exp_units_conj u ((-Complex.I * (a : ℂ)) • D0)
    simpa [u] using! h
  rw [hconj]

theorem hadamard_step_factorization (D0 Df : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℝ) :
    HamiltonianEvolution (hadamardGate * D0 * hadamardGate) a * HamiltonianEvolution Df b
      = hadamardGate * HamiltonianEvolution D0 a * hadamardGate
          * HamiltonianEvolution Df b :=
  gate_factorization hadamardGate D0 Df hadamardGate_mul_self a b

theorem norm_pfComm_le {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) :
    ‖pfComm A B‖ ≤ 2 * ‖A‖ * ‖B‖ := by
  unfold pfComm
  calc ‖A * B - B * A‖ ≤ ‖A * B‖ + ‖B * A‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ := by
        gcongr
        · exact Matrix.l2_opNorm_mul _ _
        · exact Matrix.l2_opNorm_mul _ _
    _ = 2 * ‖A‖ * ‖B‖ := by ring

theorem pfCommutatorSum_pair {D : ℕ} (A B : Operator D) :
    pfCommutatorSum ![A, B] = ‖pfComm A B‖ := by
  unfold pfCommutatorSum
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem two_term_product_formula {D : ℕ} (A B : Operator D) (t : ℝ) (r : ℕ)
    (hr : 0 < r) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖pfFamily ![A, B] t r - HamiltonianEvolution (A + B) t‖
      ≤ t ^ 2 / (2 * r) * ‖pfComm A B‖ := by
  have h := product_formula_finite_family_segmented D 2 r ![A, B] t hr
    (by intro j; fin_cases j
        · simpa using! hA
        · simpa using! hB)
  rw [pfCommutatorSum_pair A B] at h
  simpa [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using! h

theorem two_term_product_formula_norm {D : ℕ} (A B : Operator D) (t : ℝ) (r : ℕ)
    (hr : 0 < r) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖pfFamily ![A, B] t r - HamiltonianEvolution (A + B) t‖
      ≤ t ^ 2 / (2 * r) * (2 * ‖A‖ * ‖B‖) := by
  refine le_trans (two_term_product_formula A B t r hr hA hB) ?_
  gcongr
  exact norm_pfComm_le A B

theorem interpolation_step_bound {I : Type} [Fintype I] [DecidableEq I]
    (H0 Hf : Matrix I I ℂ) {T t : ℝ} (r : ℕ)
    (hr : 0 < r) (hT : 0 < T) (ht : 0 ≤ t) :
    ‖((1 - t / T) • H0 + (t / T) • Hf)
        - ((1 - ((⌈(r : ℝ) * t / T⌉₊ : ℕ) : ℝ) / r) • H0
            + (((⌈(r : ℝ) * t / T⌉₊ : ℕ) : ℝ) / r) • Hf)‖
      ≤ ‖Hf - H0‖ / r := by
  set j : ℕ := ⌈(r : ℝ) * t / T⌉₊ with hj
  have hx0 : 0 ≤ (r : ℝ) * t / T := by positivity
  have hlo : (r : ℝ) * t / T ≤ (j : ℝ) := Nat.le_ceil _
  have hhi : (j : ℝ) < (r : ℝ) * t / T + 1 := Nat.ceil_lt_add_one hx0
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hTne : T ≠ 0 := ne_of_gt hT
  have hdiff : ((1 - t / T) • H0 + (t / T) • Hf)
      - ((1 - (j : ℝ) / r) • H0 + ((j : ℝ) / r) • Hf)
      = -((j : ℝ) / r - t / T) • (Hf - H0) := by
    rw [sub_smul, sub_smul, smul_sub, neg_smul, neg_smul]
    module
  have hδ0 : (0 : ℝ) ≤ (j : ℝ) / r - t / T := by
    have hle : t / T ≤ (j : ℝ) / r := by
      rw [le_div_iff₀ hrR]
      calc t / T * (r : ℝ) = (r : ℝ) * t / T := by ring
        _ ≤ (j : ℝ) := hlo
    linarith
  have hδ1 : (j : ℝ) / r - t / T < 1 / r := by
    have hlt : (j : ℝ) / r < t / T + 1 / r := by
      rw [div_lt_iff₀ hrR]
      have h2 : ((r : ℝ) * t / T + 1) = (t / T + 1 / r) * r := by
        field_simp
      rw [h2] at hhi
      exact hhi
    linarith
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hδ0]
  calc ((j : ℝ) / r - t / T) * ‖Hf - H0‖ ≤ (1 / r) * ‖Hf - H0‖ := by
        gcongr
    _ = ‖Hf - H0‖ / r := by ring

end Theorem1
end Qatlib.Papers.AdiabPower02.MainResults
