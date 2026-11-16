/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.ClassicalAux

@[expose] public section


/-! # Singular-state counterexamples to the legacy real entropy projection

The source quantum relative entropy of orthogonal pure states is infinite.
The legacy `relEntR` projects infinity to zero. Thus its equality condition
and real Pinsker inequality are false, even on genuine normalized densities.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QShannonWilde11.MainResults.QEntropy.SingularProbe

open Qatlib.Papers.QShannonWilde11.MainResults.Model
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open scoped BigOperators ComplexOrder

/-- The computational-basis pure density on a two-dimensional register. -/
def basisDensity (k : Fin 2) : Dens (Fin 2) :=
  ⟨Matrix.diagonal (fun i => if i = k then (1 : ℂ) else 0),
    Matrix.posSemidef_diagonal_iff.mpr (fun _ => by split_ifs <;> norm_num),
    by simp [Matrix.trace_diagonal]⟩

/-- The two basis densities are distinct matrices. -/
theorem basis_distinct : (basisDensity 0).val ≠ (basisDensity 1).val := by
  intro h
  have h₀ := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  norm_num [basisDensity] at h₀

/-- Orthogonal basis densities have infinite extended quantum relative entropy. -/
theorem basis_relative_top : relEnt (basisDensity 0) (basisDensity 1) = ⊤ := by
  let e₀ : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, 0]
  have hσ : e₀ ∈ (state (basisDensity 1)).M.ker := by
    rw [HermitianMat.mem_ker_iff_mulVec_zero]
    change (basisDensity 1).val.mulVec e₀ = 0
    ext i
    fin_cases i <;> norm_num [basisDensity, e₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hρ : e₀ ∉ (state (basisDensity 0)).M.ker := by
    intro h
    rw [HermitianMat.mem_ker_iff_mulVec_zero] at h
    change (basisDensity 0).val.mulVec e₀ = 0 at h
    have h₀ := congrFun h 0
    norm_num [basisDensity, e₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h₀
  exact (relative_entropy_density_bridge.1 _ (basisDensity 0) (basisDensity 1)).2.1
    (fun h => hρ (h hσ))

/-- The same actual states refute both the old zero characterization and Pinsker bound. -/
theorem singular_failures :
    relEntR (basisDensity 0) (basisDensity 1) = 0 ∧
    (basisDensity 0).val ≠ (basisDensity 1).val ∧
    ¬ (1 / (2 * Real.log 2)) *
        (traceNormDiff (basisDensity 0).val (basisDensity 1).val) ^ 2 ≤
      relEntR (basisDensity 0) (basisDensity 1) := by
  have hz : relEntR (basisDensity 0) (basisDensity 1) = 0 := by
    simp [relEntR, show relative (basisDensity 0) (basisDensity 1) = ⊤ from basis_relative_top]
  refine ⟨hz, basis_distinct, ?_⟩
  rw [hz]
  apply not_le_of_gt
  have hn : 0 < traceNormDiff (basisDensity 0).val (basisDensity 1).val := by
    apply lt_of_le_of_ne (Matrix.traceNorm_nonneg _)
    intro h
    apply basis_distinct
    exact sub_eq_zero.mp ((Matrix.traceNorm_zero_iff _).mp h.symm)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

end Qatlib.Papers.QShannonWilde11.MainResults.QEntropy.SingularProbe
