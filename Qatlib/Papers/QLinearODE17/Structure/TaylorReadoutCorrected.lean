/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.Structure.Theorem9Aux
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Corrected Taylor jumps and measured readout

This module defines a Taylor matrix with negative jump couplings and the measured readout
`taylorMeasuredDensity`, which sums the outer products of successful label blocks. Its trace is
the success-set mass and the matrix is positive semidefinite, matching the measurement
interpretation needed in the ODE algorithm of [BerryEtAl2017ODE].

Explicit zero-generator and opposite-sign examples verify the corrected jump sign and show that
a normalized state can have full success-set mass while its coherent extraction vanishes.

## Main statements

* `taylorMeasuredDensity_trace`: Measured-density trace equals success-set mass.
* `correctedZeroSolution_solves`: An explicit zero-generator solution for the corrected jump
  sign.
* `normalizedOpposite_extract_zero`: Coherent extraction can vanish for a normalized state of
  success-set mass one.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QLinearODE17.StructureCore
open Matrix
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- The Taylor-system matrix with identity diagonal and negative Taylor-step, jump-sum, and
padding couplings. -/
def taylorStepMatrixCorrected {N : Type} [Fintype N] [DecidableEq N]
    (m k p : ℕ) (M : Matrix N N ℂ) :
    Matrix (Fin (m*(k+1)+p+1) × N) (Fin (m*(k+1)+p+1) × N) ℂ :=
  fun r c => (if r = c then 1 else 0)
    - (if r.1.val < m*(k+1) ∧ 1 ≤ r.1.val % (k+1) ∧ c.1.val+1 = r.1.val then
        M r.2 c.2 / (r.1.val % (k+1) : ℕ) else 0)
    - (if r.1.val ≤ m*(k+1) ∧ 0 < r.1.val ∧ (k+1) ∣ r.1.val ∧
        r.1.val-(k+1) ≤ c.1.val ∧ c.1.val < r.1.val then
        (if r.2 = c.2 then 1 else 0) else 0)
    - (if m*(k+1) < r.1.val ∧ c.1.val+1 = r.1.val then
        (if r.2 = c.2 then 1 else 0) else 0)

/-- The unnormalized measured output matrix obtained by summing the outer products of all
successful label blocks. -/
def taylorMeasuredDensity {N : Type} [Fintype N] [DecidableEq N]
    (m k p : ℕ) (φ : QState (Fin (m*(k+1)+p+1) × N)) : Matrix N N ℂ :=
  ∑ l : Fin (m*(k+1)+p+1), if m*(k+1) ≤ l.val then outerProduct (taylorBlock φ l) else 0

/-- The trace of the measured output matrix equals the complex embedding of the success-set
mass. -/
theorem taylorMeasuredDensity_trace {N : Type} [Fintype N] [DecidableEq N]
    (m k p : ℕ) (φ : QState (Fin (m*(k+1)+p+1) × N)) :
    Matrix.trace (taylorMeasuredDensity m k p φ) =
      (MeasureProb φ (taylorSuccessSet m k p) : ℂ) := by
  simp only [taylorMeasuredDensity, Matrix.trace_sum, apply_ite Matrix.trace,
    trace_outerProduct, Matrix.trace_zero]
  simp only [MeasureProb, BornProb, taylorSuccessSet, Finset.sum_filter,
    Fintype.sum_prod_type, Complex.ofReal_sum, apply_ite, Complex.ofReal_zero,
    taylorBlock]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp

/-- The measured output matrix is positive semidefinite. -/
theorem taylorMeasuredDensity_posSemidef {N : Type} [Fintype N] [DecidableEq N]
    (m k p : ℕ) (φ : QState (Fin (m*(k+1)+p+1) × N)) :
    (taylorMeasuredDensity m k p φ).PosSemidef := by
  unfold taylorMeasuredDensity
  apply Matrix.posSemidef_sum
  intro l _
  split_ifs
  · exact outerProduct_posSemidef _
  · exact Matrix.PosSemidef.zero

/-- The state on eight labels with amplitude 1 at label zero and labels six and seven, and zero
elsewhere. -/
def correctedZeroSolution : QState (Fin 8 × Unit) :=
  fun r => if r.1.val = 0 ∨ 6 ≤ r.1.val then 1 else 0

/-- The explicit state `correctedZeroSolution` solves the corrected Taylor system for a zero
generator, unit initial scalar, and zero source with parameters (1, 5, 1). -/
theorem correctedZeroSolution_solves :
    taylorStepMatrixCorrected 1 5 1 (0 : Matrix Unit Unit ℂ) *ᵥ correctedZeroSolution =
      taylorRHS 1 5 1 1 (fun _ : Unit => 1) 0 := by
  ext ⟨r, n⟩
  cases n
  fin_cases r <;> simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Fintype.sum_unique] <;>
    norm_num [taylorStepMatrixCorrected, taylorRHS, correctedZeroSolution, Fin.ext_iff]

/-- The corrected zero-generator Taylor matrix with parameters (1, 5, 1) has entry -1 at row
label six and column label zero. -/
theorem corrected_jump_entry :
    taylorStepMatrixCorrected 1 5 1 (0 : Matrix Unit Unit ℂ) (6, ()) (0, ()) = -1 := by
  norm_num [taylorStepMatrixCorrected, Fin.ext_iff]

/-- The measured density of `extractionOppositeSign` has trace 2. -/
theorem opposite_sign_density_trace :
    Matrix.trace (taylorMeasuredDensity 1 5 1 extractionOppositeSign) = 2 := by
  rw [taylorMeasuredDensity_trace, extractionOppositeSign_mass]
  norm_num

/-- The state on ten labels with amplitudes 1/2 at labels six and eight, -1/2 at labels seven
and nine, and zero elsewhere. -/
def normalizedOpposite : QState (Fin 10 × Unit) :=
  fun r => if r.1.val = 6 ∨ r.1.val = 8 then 1/2
    else if r.1.val = 7 ∨ r.1.val = 9 then -1/2 else 0

/-- The opposite-sign state `normalizedOpposite` is normalized. -/
theorem normalizedOpposite_normalized : Normalized normalizedOpposite := by
  norm_num [Normalized, normalizedOpposite, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Coherent extraction of `normalizedOpposite` with parameters (1, 5, 3) is zero. -/
theorem normalizedOpposite_extract_zero : taylorExtract 1 5 3 normalizedOpposite = 0 := by
  ext n
  norm_num [taylorExtract, normalizedOpposite, Fin.sum_univ_succ]

/-- The success-set mass of `normalizedOpposite` with parameters (1, 5, 3) is 1. -/
theorem normalizedOpposite_mass_one : MeasureProb normalizedOpposite (taylorSuccessSet 1 5 3) = 1 := by
  norm_num [MeasureProb, BornProb, taylorSuccessSet, normalizedOpposite,
    Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- The measured output density of `normalizedOpposite` with parameters (1, 5, 3) has trace 1. -/
theorem normalizedOpposite_density_trace_one :
    Matrix.trace (taylorMeasuredDensity 1 5 3 normalizedOpposite) = 1 := by
  rw [taylorMeasuredDensity_trace, normalizedOpposite_mass_one]
  norm_num

end Qatlib.Papers.QLinearODE17.StructureCore
