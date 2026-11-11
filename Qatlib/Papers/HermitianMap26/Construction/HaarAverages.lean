/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Trainability23.HaarAverages.HaarMeasure
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Haar averages of conjugated states

This module proves Haar integration identities used in the variance analysis of [CaiEtAl2026].
It evaluates entrywise and trace averages of unitary conjugation and defines coordinate
projectors `seed` and their unitary conjugates `pureState`.

For qubits, tensor and swap trace identities give the second moment of a pure-state trace
pairing and the entrywise condition `PureEntrySecondMoment`. These statements concern the
specified Haar moments of the conjugated coordinate state.

## Main statements

* `conjugation_average`: computes the entrywise first moment of unitary conjugation.
* `conjugation_trace_average`: computes the averaged trace pairing.
* `qubit_pure_second`: evaluates the squared trace-pairing average.
* `qubit_pure_entry_second`: establishes the qubit entrywise second-moment formula.

## References

* [Cai et al., 2026][CaiEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HermitianMap26.Construction.HaarAverages
open Matrix MeasureTheory
open Qatlib.Papers.Trainability23.HaarAverages
open scoped BigOperators Matrix Kronecker

local instance measurableMatrix (m n : Type*) [Fintype m] [Fintype n] :
    MeasurableSpace (Matrix m n ℂ) := inferInstanceAs (MeasurableSpace (m → n → ℂ))
local instance borelMatrix (m n : Type*) [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) := inferInstanceAs (BorelSpace (m → n → ℂ))

/-- Each entry of `V * A * V.conjTranspose` is the double sum of the entries of `A` times the
corresponding conjugated products of entries of `V`. -/
theorem conj_entry_expand {n : Type*} [Fintype n] [DecidableEq n]
    (V A : Matrix n n ℂ) (i j : n) :
    (V * A * V.conjTranspose) i j =
      ∑ a, ∑ b, A a b * (V i a * star (V j b)) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Each entry of a fixed matrix conjugated by a unitary matrix is integrable with respect to
the unitary Haar measure. -/
theorem conjugation_integrable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (i j : n) :
    Integrable (fun V : Matrix.unitaryGroup n ℂ =>
      ((V : Matrix n n ℂ) * A * (V : Matrix n n ℂ).conjTranspose) i j)
      (haarUnitaryGroup n) := by
  simp_rw [conj_entry_expand]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (haarIntegrable_entryPair n a b i j).const_mul _

/-- The Haar average of an entry of a unitary conjugate is the trace divided by the dimension on
the diagonal and zero off the diagonal. -/
theorem conjugation_average {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (i j : n) :
    (∫ V : Matrix.unitaryGroup n ℂ,
      ((V : Matrix n n ℂ) * A * (V : Matrix n n ℂ).conjTranspose) i j
      ∂haarUnitaryGroup n) = if i = j then A.trace / (Fintype.card n : ℂ) else 0 := by
  simp_rw [conj_entry_expand]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ =>
    (haarIntegrable_entryPair n a b i j).const_mul _)]
  simp_rw [integral_finsetSum _ (fun b _ =>
    (haarIntegrable_entryPair n _ b i j).const_mul _), integral_const_mul, haar_entryPair_eq]
  by_cases hij : i = j
  · subst j
    have htr (a b : n) : (Matrix.single a b (1 : ℂ)).trace = if a = b then 1 else 0 := by
      split_ifs with hab
      · subst b; exact Matrix.trace_single_eq_same a 1
      · exact Matrix.trace_single_eq_of_ne a b 1 hab
    simp_rw [htr]
    simp only [ite_true]
    have hrow (a : n) : (∑ b, A a b * ((if a = b then 1 else 0) /
        (Fintype.card n : ℂ))) = A a a / (Fintype.card n : ℂ) := by
      simp [mul_ite, div_eq_mul_inv]
    rw [Finset.sum_congr rfl (fun a _ => hrow a), ← Finset.sum_div]
    rfl
  · simp [hij]

/-- The Haar average of `trace (B * V * A * Vᴴ)` equals the product of the two traces divided by
the dimension. [CaiEtAl2026]. -/
theorem conjugation_trace_average {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) :
    (∫ V : Matrix.unitaryGroup n ℂ,
      (B * ((V : Matrix n n ℂ) * A * (V : Matrix n n ℂ).conjTranspose)).trace
        ∂haarUnitaryGroup n) = B.trace * A.trace / (Fintype.card n : ℂ) := by
  have hterm (i j : n) := (conjugation_integrable A j i).const_mul (B i j)
  have hexpand : (fun V : Matrix.unitaryGroup n ℂ =>
      (B * ((V : Matrix n n ℂ) * A * (V : Matrix n n ℂ).conjTranspose)).trace) =
      (fun V : Matrix.unitaryGroup n ℂ => ∑ i, ∑ j, B i j *
        ((V : Matrix n n ℂ) * A * (V : Matrix n n ℂ).conjTranspose) j i) := by
    funext V; rfl
  rw [hexpand, integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hterm i j)]
  simp_rw [integral_finsetSum _ (fun j _ => hterm _ j), integral_const_mul,
    conjugation_average]
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul]
  simp only [Matrix.trace, Matrix.diag_apply, div_eq_mul_inv, mul_assoc]

/-- The coordinate projector with a single nonzero entry, equal to one at `(a, a)`. -/
def seed {n : Type*} [DecidableEq n] (a : n) : Matrix n n ℂ := Matrix.single a a 1

/-- The coordinate projector `seed a` conjugated by the unitary matrix `V`. -/
def pureState {n : Type*} [Fintype n] [DecidableEq n]
    (a : n) (V : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ :=
  (V : Matrix n n ℂ) * seed a * (V : Matrix n n ℂ).conjTranspose

/-- The tensor product of two qubit zero-coordinate projectors has trace one, and its product
with the swap operator also has trace one. -/
theorem qubit_tensor_seed :
    let P := Matrix.kroneckerMap (· * ·) (seed (0 : Fin 2)) (seed (0 : Fin 2))
    P.trace = 1 ∧ (P * swapOp (Fin 2)).trace = 1 := by
  simp [seed, Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.kroneckerMap_apply, swapOp, permMatrix]

/-- Conjugating the two-qubit seed by `V ⊗ V` gives the tensor square of the pure state obtained
from `V`. -/
theorem qubit_pure_tensor (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    unitaryKronecker V *
        Matrix.kroneckerMap (· * ·) (seed (0 : Fin 2)) (seed (0 : Fin 2)) *
        (unitaryKronecker V).conjTranspose =
      Matrix.kroneckerMap (· * ·) (pureState 0 V) (pureState 0 V) := by
  simp only [unitaryKronecker, Matrix.conjTranspose_kronecker,
    kroneckerMap_mul, pureState]

/-- The trace of the tensor product of two qubit matrices is the product of their traces. -/
theorem tensor_trace (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (Matrix.kroneckerMap (· * ·) A B).trace = A.trace * B.trace :=
  Matrix.trace_kronecker A B

/-- The trace of the swap operator times `A ⊗ B` equals the trace of `A * B`. -/
theorem swap_tensor_trace (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (swapOp (Fin 2) * Matrix.kroneckerMap (· * ·) A B).trace = (A * B).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, swapOp_mul_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply]
  dsimp only [Prod.swap]
  rw [Finset.sum_comm]

/-- The Haar average of the square of `trace (pureState 0 V * A)` for a qubit is `(A.trace ^ 2 +
(A ^ 2).trace) / 6`. [CaiEtAl2026]. -/
theorem qubit_pure_second (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (∫ V : Matrix.unitaryGroup (Fin 2) ℂ, (pureState 0 V * A).trace ^ 2
      ∂haarUnitaryGroup (Fin 2)) = (A.trace ^ 2 + (A ^ 2).trace) / 6 := by
  let P := Matrix.kroneckerMap (· * ·) (seed (0 : Fin 2)) (seed (0 : Fin 2))
  have hseed := qubit_tensor_seed
  have htensor (V : Matrix.unitaryGroup (Fin 2) ℂ) :
      (pureState 0 V * A).trace ^ 2 =
        ((unitaryKronecker V * P * (unitaryKronecker V).conjTranspose) *
          Matrix.kroneckerMap (· * ·) A A).trace := by
    rw [show P = Matrix.kroneckerMap (· * ·) (seed (0 : Fin 2)) (seed (0 : Fin 2)) from rfl,
      qubit_pure_tensor, kroneckerMap_mul, tensor_trace, pow_two]
  calc
    (∫ V : Matrix.unitaryGroup (Fin 2) ℂ, (pureState 0 V * A).trace ^ 2
      ∂haarUnitaryGroup (Fin 2)) =
      ∫ V : Matrix.unitaryGroup (Fin 2) ℂ,
        ((unitaryKronecker V * P * (unitaryKronecker V).conjTranspose) *
          Matrix.kroneckerMap (· * ·) A A).trace ∂haarUnitaryGroup (Fin 2) := by
            exact integral_congr_ae (Filter.Eventually.of_forall htensor)
    _ = (haarKroneckerAverage P * Matrix.kroneckerMap (· * ·) A A).trace :=
      (haarKroneckerAverage_mul_trace P _).symm
    _ = (A.trace ^ 2 + (A ^ 2).trace) / 6 := by
      rw [haarKroneckerAverage_eq_one_plus_swap P hseed.1 hseed.2,
        add_mul, Matrix.smul_mul, Matrix.smul_mul, one_mul,
        Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
        tensor_trace, swap_tensor_trace]
      simp only [smul_eq_mul, pow_two]
      ring

/-- The condition that products of two entries of a Haar-random coordinate pure state have the
stated second-moment formula with denominator `d * (d + 1)`. -/
def PureEntrySecondMoment (d : ℕ) (a : Fin d) : Prop :=
  ∀ i j k l : Fin d,
    (∫ V : Matrix.unitaryGroup (Fin d) ℂ,
      pureState a V i j * pureState a V k l ∂haarUnitaryGroup (Fin d)) =
        (((if i = j then 1 else 0) * (if k = l then 1 else 0) +
          (if i = l then 1 else 0) * (if k = j then 1 else 0)) : ℂ) /
          ((d : ℂ) * (d + 1))

/-- The qubit zero-coordinate pure state satisfies `PureEntrySecondMoment 2 0`. -/
theorem qubit_pure_entry_second : PureEntrySecondMoment 2 0 := by
  intro i j k l
  let P := Matrix.kroneckerMap (· * ·) (seed (0 : Fin 2)) (seed (0 : Fin 2))
  have hseed := qubit_tensor_seed
  have h := congrArg (fun M => M (i,k) (j,l))
    (haarKroneckerAverage_eq_one_plus_swap P hseed.1 hseed.2)
  have hleft : haarKroneckerAverage P (i,k) (j,l) =
      ∫ V : Matrix.unitaryGroup (Fin 2) ℂ,
        pureState 0 V i j * pureState 0 V k l ∂haarUnitaryGroup (Fin 2) := by
    unfold haarKroneckerAverage
    apply integral_congr_ae
    filter_upwards with V
    rw [show P = Matrix.kroneckerMap (· * ·) (seed (0 : Fin 2)) (seed (0 : Fin 2)) from rfl,
      qubit_pure_tensor]
    rfl
  try dsimp only at h
  rw [hleft] at h
  rw [h]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      swapOp, permMatrix]

end Qatlib.Papers.HermitianMap26.Construction.HaarAverages
