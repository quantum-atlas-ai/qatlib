/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Trainability23.HaarAverages.HaarMeasure
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section


/-!
# HaarMoments source results

These finite probability identities and conditional estimates preserve closed
results from arXiv:2305.02881v2. They do not assert the missing full Haar-product
MMD variance identity or an unconditional trainability theorem.
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.Trainability23.HaarAverages
open scoped BigOperators Matrix
namespace Qatlib.Papers.Trainability23.HaarAverages.HaarMoments

/-- The measurable structure on the matrix algebra transported from the product of its entries
(`Matrix m n ℂ` is definitionally `m → n → ℂ`).  The Frozen Haar development uses the same local
instance; it is repeated here because it is file-local there and must be in scope for the product
measure `Measure.pi`. -/
local instance instMeasMatrix (m n : Type*) :
    MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

/-! ## Equations (205)–(208): single-qubit Haar moments -/

/-- **Eq. (205).**  In dimension two the conjugated matrix unit averages to half the identity:
for all `i j : Fin 2`,
`∫ dV (V i 0) (V j 0)* = ((1/2) • 1) i j`.
The statement is entrywise because the Frozen development defines the Haar average entrywise
(`haarKroneckerAverage`, `haarTensorAverage`) and no matrix-valued Bochner integral is set up. -/
theorem one_copy (i j : Fin 2) :
    MeasureTheory.integral (haarUnitaryGroup (Fin 2)) (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        (V : Matrix (Fin 2) (Fin 2) ℂ) i 0 * star ((V : Matrix (Fin 2) (Fin 2) ℂ) j 0))
      = ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) i j := by
  rw [haar_entryPair_eq]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.trace_single_eq_same,
      Fintype.card_fin]
    norm_num
  · rw [ite_eq_right hij, Matrix.smul_apply, Matrix.one_apply_ne hij]
    ring

/-- **Eq. (206).**  The two-copy Haar average of `P = |00⟩⟨00|` is `(1/6)(1⊗1 + S₁₂)`, where
`S₁₂ = swapOp (Fin 2)` is the swap of the two tensor factors.  This instantiates the Frozen
`haarKroneckerAverage_eq_one_plus_swap`, whose two trace hypotheses hold for the rank-one
projector `|00⟩⟨00|` because both `tr P` and `tr (P S)` count one unit of mass. -/
theorem two_copy :
    haarKroneckerAverage
        (Matrix.single ((0, 0) : Fin 2 × Fin 2) ((0, 0) : Fin 2 × Fin 2) (1 : ℂ))
      = (1 / 6 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
        + (1 / 6 : ℂ) • swapOp (Fin 2) := by
  refine haarKroneckerAverage_eq_one_plus_swap _ ?_ ?_
  · rw [Matrix.trace_single_eq_same]
  · rw [Matrix.trace_single_mul]
    simp [swapOp, permMatrix, Matrix.of_apply]

/-- **Eq. (207).**  The three-copy Haar average of `|000⟩⟨000|` is `(1/24)` times the sum of the
six permutation operators of `S₃`: `1⊗1⊗1`, `S₁₂`, `S₁₃`, `S₂₃`, `S₂₃S₁₂`, `S₂₃S₁₃`.  This is
exactly the Frozen `haarTensorAverage_three_eq_permSum`, whose `Σ_{σ∈S₃} P_σ` is the paper's
six-term expansion. -/
theorem three_copy :
    haarTensorAverage 3 (zeroProj 3)
      = ((24 : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin 3), tensorPerm 3 σ := by
  have h := haarTensorAverage_three_eq_permSum
  rw [h]
  norm_num

/-- **Eq. (208).**  The four-copy Haar average of `|0000⟩⟨0000|` is `(1/120)` times the sum of the
`24` permutation operators of `S₄`, i.e. the Frozen `haarTensorAverage_four_eq_permSum`.  The
paper's printed list of `24` terms has no typo (retracted suspicion, `r78`). -/
theorem four_copy :
    haarTensorAverage 4 (zeroProj 4)
      = ((120 : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin 4), tensorPerm 4 σ := by
  have h := haarTensorAverage_four_eq_permSum
  rw [h]
  norm_num
end Qatlib.Papers.Trainability23.HaarAverages.HaarMoments
