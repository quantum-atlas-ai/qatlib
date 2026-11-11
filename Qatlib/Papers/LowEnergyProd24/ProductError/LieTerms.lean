/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.ProductError.ActualWord
import Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.WeightedNested

/-!
# Symbolic Lie terms and weighted evaluation

The structure `LieTerm` represents a complex coefficient multiplying a nested commutator of
grouped Hamiltonians. Raising and scaling operations match repeated stage commutators and real
scalar multiplication, and `LieTerm.actual_weighted_bound` controls their evaluated matrices
using the outer-list length and seed-group size. See [HejaziZiniArrazola2024].

## Main statements

* `LieTerm.raise_evaluate`: Evaluating a raised Lie term equals applying the indicated number of
  commutators with the stage generator to the original evaluation.
* `LieTerm.raise_mass`: Raising a Lie term by `n` multiplies its coefficient norm by
  `|stage.1|^n`.
* `LieTerm.actual_weighted_bound`: For positive `J`, `k`, and `d` and at most `L` seed labels,
  the weighted norm of an evaluated Lie term is bounded by its coefficient norm times `L * (k *
  d)^term.outer.length * term.outer.length! * (2 * J)^(term.outer.length + 1)`.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

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

/-- A symbolic nested commutator specified by a complex coefficient, a seed group, and a list of
outer group indices. -/
structure LieTerm (M : ℕ) where
  coefficient : ℂ
  seed : Fin M
  outer : List (Fin M)

/-- The complex coefficient times the grouped nested commutator specified by the seed and
outer-index list. -/
def LieTerm.evaluate (h : Hamiltonian N R M k d J) (term : LieTerm M) :=
  term.coefficient • RetainedError.nested h term.seed term.outer

/-- The Lie term obtained by prepending `n` copies of the stage group and multiplying the
coefficient by the `n`th power of `-i * stage.1`. -/
def LieTerm.raise (stage : ℝ × Fin M) (n : ℕ) (term : LieTerm M) : LieTerm M :=
  ⟨(((-stage.1 : ℂ)*Complex.I)^n)*term.coefficient, term.seed,
    List.replicate n stage.2 ++ term.outer⟩

/-- The Lie term with its coefficient multiplied by the real scalar `c` and its commutator
indices unchanged. -/
def LieTerm.scale (c : ℝ) (term : LieTerm M) : LieTerm M :=
  ⟨(c : ℂ)*term.coefficient, term.seed, term.outer⟩

/-- Repeated commutation with a fixed matrix commutes with complex scalar multiplication of the
operand. -/
theorem adIter_complex_smul (H A : Matrix (Register N) (Register N) ℂ) (c : ℂ) (n : ℕ) :
    adIter H n (c • A) = c • adIter H n A := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [adIter, ih, ad, mul_smul_comm, smul_mul_assoc, smul_sub]

/-- Multiplying the commutator generator by a complex scalar multiplies its `n`-fold iterated
commutator by the scalar to the power `n`. -/
theorem adIter_complex_generator (H A : Matrix (Register N) (Register N) ℂ) (c : ℂ) (n : ℕ) :
    adIter (c • H) n A = c^n • adIter H n A := by
  induction n with
  | zero => simp only [adIter, pow_zero, one_smul]
  | succ n ih =>
    simp only [adIter, ih, ad, mul_smul_comm, smul_mul_assoc, smul_smul, smul_sub, pow_succ',
        mul_comm (c^n) c]

/-- Repeated commutation with a grouped Hamiltonian prepends the corresponding repeated group
index to the outer list of a grouped nested commutator. -/
theorem adIter_group_nested (h : Hamiltonian N R M k d J) (m seed : Fin M)
    (xs : List (Fin M)) (n : ℕ) :
    adIter (h.grouped m) n (RetainedError.nested h seed xs) =
      RetainedError.nested h seed (List.replicate n m ++ xs) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [adIter, ih, List.replicate_succ, List.cons_append, RetainedError.nested, ad]

/-- Evaluating a raised Lie term equals applying the indicated number of commutators with the
stage generator to the original evaluation. -/
theorem LieTerm.raise_evaluate (h : Hamiltonian N R M k d J) (stage : ℝ × Fin M)
    (n : ℕ) (term : LieTerm M) :
    (term.raise stage n).evaluate h = adIter (stageGenerator h stage) n (term.evaluate h) := by
  rw [LieTerm.raise, LieTerm.evaluate, LieTerm.evaluate, stageGenerator,
    adIter_complex_smul, adIter_complex_generator, adIter_group_nested, smul_smul]
  rw [mul_comm]

/-- Raising a Lie term by `n` multiplies its coefficient norm by `|stage.1|^n`. -/
theorem LieTerm.raise_mass (stage : ℝ × Fin M) (n : ℕ) (term : LieTerm M) :
    ‖(term.raise stage n).coefficient‖ = |stage.1|^n*‖term.coefficient‖ := by
  simp only [LieTerm.raise, norm_mul, norm_pow, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one]

/-- Scaling a Lie term by a real number multiplies its coefficient norm by the absolute value of
that number. -/
theorem LieTerm.scale_mass (c : ℝ) (term : LieTerm M) :
    ‖(term.scale c).coefficient‖ = |c| *‖term.coefficient‖ := by
  simp only [LieTerm.scale, norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- For positive `J`, `k`, and `d` and at most `L` seed labels, the weighted norm of an
evaluated Lie term is bounded by its coefficient norm times `L * (k * d)^term.outer.length *
term.outer.length! * (2 * J)^(term.outer.length + 1)`. -/
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
