/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.ProductError.ActualWord
import Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.WeightedNested
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.ProductError
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
variable {N R M k d : ℕ} {J : ℝ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

structure LieTerm (M : ℕ) where
  coefficient : ℂ
  seed : Fin M
  outer : List (Fin M)

def LieTerm.evaluate (h : Hamiltonian N R M k d J) (term : LieTerm M) :=
  term.coefficient • RetainedError.nested h term.seed term.outer

def LieTerm.raise (stage : ℝ × Fin M) (n : ℕ) (term : LieTerm M) : LieTerm M :=
  ⟨(((-stage.1 : ℂ)*Complex.I)^n)*term.coefficient, term.seed,
    List.replicate n stage.2 ++ term.outer⟩

def LieTerm.scale (c : ℝ) (term : LieTerm M) : LieTerm M :=
  ⟨(c : ℂ)*term.coefficient, term.seed, term.outer⟩

theorem adIter_complex_smul (H A : Matrix (Register N) (Register N) ℂ) (c : ℂ) (n : ℕ) :
    adIter H n (c • A) = c • adIter H n A := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [adIter, ih, ad, mul_smul_comm, smul_mul_assoc, smul_sub]

theorem adIter_complex_generator (H A : Matrix (Register N) (Register N) ℂ) (c : ℂ) (n : ℕ) :
    adIter (c • H) n A = c^n • adIter H n A := by
  induction n with
  | zero => simp only [adIter, pow_zero, one_smul]
  | succ n ih =>
    simp only [adIter, ih, ad, mul_smul_comm, smul_mul_assoc, smul_smul, smul_sub, pow_succ',
        mul_comm (c^n) c]

theorem adIter_group_nested (h : Hamiltonian N R M k d J) (m seed : Fin M)
    (xs : List (Fin M)) (n : ℕ) :
    adIter (h.grouped m) n (RetainedError.nested h seed xs) =
      RetainedError.nested h seed (List.replicate n m ++ xs) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [adIter, ih, List.replicate_succ, List.cons_append, RetainedError.nested, ad]

theorem LieTerm.raise_evaluate (h : Hamiltonian N R M k d J) (stage : ℝ × Fin M)
    (n : ℕ) (term : LieTerm M) :
    (term.raise stage n).evaluate h = adIter (stageGenerator h stage) n (term.evaluate h) := by
  rw [LieTerm.raise, LieTerm.evaluate, LieTerm.evaluate, stageGenerator,
    adIter_complex_smul, adIter_complex_generator, adIter_group_nested, smul_smul]
  rw [mul_comm]

theorem LieTerm.raise_mass (stage : ℝ × Fin M) (n : ℕ) (term : LieTerm M) :
    ‖(term.raise stage n).coefficient‖ = |stage.1|^n*‖term.coefficient‖ := by
  simp only [LieTerm.raise, norm_mul, norm_pow, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one]

theorem LieTerm.scale_mass (c : ℝ) (term : LieTerm M) :
    ‖(term.scale c).coefficient‖ = |c| *‖term.coefficient‖ := by
  simp only [LieTerm.scale, norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem LieTerm.actual_weighted_bound (h : Hamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ) (term : LieTerm M)
    (hL : (h.labels term.seed).card ≤ L) :
    ‖weighted h.total (term.evaluate h) (1/(2*J*k*d))‖ ≤
      ‖term.coefficient‖*((L : ℝ)*((k*d)^term.outer.length*term.outer.length.factorial : ℕ)*(2*J)^(term.outer.length+1)) := by
  have he : weighted h.total (term.evaluate h) (1/(2*J*k*d)) =
      term.coefficient • weighted h.total (RetainedError.nested h term.seed term.outer) (1/(2*J*k*d)) := by
    simp only [weighted, LieTerm.evaluate, mul_smul_comm, smul_mul_assoc]
  rw [he, norm_smul]
  exact mul_le_mul_of_nonneg_left (actual_weighted_nested h hJ hk hd L term.seed hL term.outer)
      (norm_nonneg _)
end Qatlib.Papers.LowEnergyProd24.ProductError
