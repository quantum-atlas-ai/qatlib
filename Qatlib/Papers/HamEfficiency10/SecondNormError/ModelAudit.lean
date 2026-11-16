/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamEfficiency10.SuzukiWord.SourceDefinitions
public import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterLowerBoundFamily

@[expose] public section


/-! # A literal legacy second-norm model diagnostic

The old header permits the designated second generator to be zero while
another generator has nonzero norm. A genuine symmetric splitting on actual
Pauli matrices then has positive error although the old right-hand side is
zero. The fixed source orders all generator norms; this is not a refutation
of arXiv:1005.1318v3 or a proof of its repaired high-order estimates.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Papers.HamEfficiency10.SuzukiWord
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterLowerBoundFamily
open Qatlib.Foundations.OperatorErrors.OperatorError

namespace Qatlib.Papers.HamEfficiency10.SecondNormError.ModelAudit

/-- Actual Hermitian generators with the incorrectly designated second term equal to zero. -/
def generators : Fin 3 → Mat := ![hZ, 0, hX]

/-- A symmetric Strang word with an identity factor for the zero generator. -/
def shortSchedule : ManyTermSchedule 3 1 := {
  word := [(1/2, 0), (1, 2), (1/2, 0), (1, 1)]
  mass_le := by norm_num [manyTermScalingConstant]
  sum_one := by intro j; fin_cases j <;> norm_num }

/-- Its literal many-term word has exactly the actual Pauli Strang error. -/
theorem actualError (t : ℝ) :
    ‖hamiltonianEvolution (∑ j, generators j) (-t) -
      manyTermWord generators shortSchedule.word (-t)‖ = ‖error t‖ := by
  rw [actual_execution, norm_sub_rev]
  congr 1
  simp [generators, shortSchedule, manyTermWord, Fin.sum_univ_succ,
    hamiltonianEvolution, total, genZ, genX, smul_add, ← smul_assoc, Complex.real_smul, mul_assoc, mul_comm,
    div_eq_mul_inv]

/-- The largest generator has operator norm exactly one. -/
theorem firstNorm : ‖generators 0‖ = 1 := by
  change ‖hZ‖ = 1
  apply CStarRing.norm_of_mem_unitary
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

/-- The concrete input satisfies every legacy Hermiticity and largest-norm premise. -/
theorem sourcePremises :
    (∀ j, (generators j).IsHermitian) ∧
      (∀ j, ‖generators j‖ ≤ ‖generators 0‖) := by
  constructor
  · intro j
    fin_cases j
    · exact hermitian_hZ
    · exact Matrix.isHermitian_zero
    · exact hermitian_hX
  · intro j
    rw [firstNorm]
    fin_cases j
    · exact firstNorm.le
    · simp [generators]
    · simpa [generators, genX, norm_smul] using gen_norms.2

/-- At a strictly nonzero admissible step, the actual error exceeds the old zero bound. -/
theorem violatesOld :
    ∃ dt : ℝ, manyTermScalingConstant 3 1 * |dt| ≤ (1 : ℝ) + 1 ∧
      4 * ‖generators 1‖ / (Nat.factorial (2 * 1 + 1) : ℝ) *
          (manyTermScalingConstant 3 1 * |dt|) ^ (2 * 1 + 1) <
        ‖hamiltonianEvolution (∑ j, generators j) dt -
          manyTermWord generators shortSchedule.word dt‖ := by
  let t := radius / 2
  have ht : 0 < t := half_pos radius_pos
  have htr : t ≤ radius := by dsimp [t]; linarith [radius_pos]
  have hth : t ≤ 1/4 := by dsimp [t]; linarith [radius_le_half]
  refine ⟨-t, ?_, ?_⟩
  · norm_num [manyTermScalingConstant, abs_neg, abs_of_pos ht]
    linarith
  · rw [actualError]
    have hl := (frontier1 t (by rwa [abs_of_pos ht])).1
    have hp : 0 < (1/6 : ℝ) * |t|^3 := by positivity
    simpa [generators] using hp.trans_le hl

/-- All nontrivial premises of the full old Lemma 2 header hold in this countermodel. -/
theorem fullCountermodel :
    (∀ j, (generators j).IsHermitian) ∧ (0 : Fin 3) ≠ 1 ∧
      ‖generators 0‖ = 1 ∧ (∀ j, ‖generators j‖ ≤ ‖generators 0‖) ∧
      ∃ dt : ℝ, manyTermScalingConstant 3 1 * |dt| ≤ (1 : ℝ) + 1 ∧
        ¬ ‖hamiltonianEvolution (∑ j, generators j) dt -
            manyTermWord generators shortSchedule.word dt‖ ≤
          4 * ‖generators 1‖ / (Nat.factorial (2 * 1 + 1) : ℝ) *
            (manyTermScalingConstant 3 1 * |dt|) ^ (2 * 1 + 1) := by
  refine ⟨sourcePremises.1, by decide, firstNorm, sourcePremises.2, ?_⟩
  obtain ⟨dt, hs, hv⟩ := violatesOld
  exact ⟨dt, hs, not_le_of_gt hv⟩

end Qatlib.Papers.HamEfficiency10.SecondNormError.ModelAudit
