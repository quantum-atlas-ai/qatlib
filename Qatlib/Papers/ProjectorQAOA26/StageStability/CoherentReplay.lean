/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.StageStability.ActualStages

/-!
# Coherent replay of frozen state preparations

This module constructs `frozenPreparation` for a prefix of actual stages and shows that it
prepares the corresponding actual state. Covariance of learned mixers under unitary preparation
gives the coherent uncompute, selective-phase, and reprepare identity used in [ZhouAnLiu2026].

## Main statements

* `learnedMixer_prepared`: The learned mixer exponential for a unitarily prepared state is the
  conjugate of the seed's mixer exponential by the preparation unitary.
* `frozenPreparation_action`: Applying the frozen prefix preparation to the seed produces the
  actual state after that prefix.
* `actual_prefix_replay`: The learned mixer for an actual prefix state equals the seed mixer
  conjugated by the full frozen prefix preparation, implementing coherent replay as in
  [ZhouAnLiu2026].

## References

* [Zhou et al., 2026][ZhouAnLiu2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.StageStability
open scoped Matrix Matrix.Norms.L2Operator
open Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel
variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- The rank-one operator of `U *ᵥ v` is `U * rankOne v * Uᴴ`. -/
theorem rankOne_prepared (U : Matrix I I ℂ) (v : I → ℂ) :
    rankOne (U*ᵥv)=U*rankOne v*Uᴴ := by
  simp only [rankOne,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,Matrix.star_mulVec]

/-- For unitary `U`, the learned generator of the prepared vector is the conjugate by `U` of the
seed's learned generator. -/
theorem learnedGenerator_prepared (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (v : I → ℂ) :
    learnedGenerator (U*ᵥv)=U*learnedGenerator v*Uᴴ := by
  have hu : U*Uᴴ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hU
  simp only [learnedGenerator,rankOne_prepared,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hu]

/-- The learned mixer exponential for a unitarily prepared state is the conjugate of the seed's
mixer exponential by the preparation unitary. -/
theorem learnedMixer_prepared (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (v : I → ℂ) (β : ℝ) :
    mixerExp (learnedGenerator (U*ᵥv)) β=U*mixerExp (learnedGenerator v) β*Uᴴ := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := .restrictScalars ℚ ℝ _
  let V : Matrix.unitaryGroup I ℂ:=⟨U,hU⟩
  let Q : (Matrix I I ℂ)ˣ:=Unitary.toUnits V
  have hinv : (↑Q⁻¹ : Matrix I I ℂ)=Uᴴ := rfl
  have hu : (↑Q : Matrix I I ℂ)=U := rfl
  unfold mixerExp evolution
  rw [learnedGenerator_prepared U hU v]
  have hscale : (-β)•(Complex.I•(U*learnedGenerator v*Uᴴ))=
      (↑Q : Matrix I I ℂ)*((-β)•(Complex.I•learnedGenerator v))*(↑Q⁻¹ : Matrix I I ℂ) := by
    rw [hu,hinv]
    simp only [Matrix.mul_smul,Matrix.smul_mul]
  rw [hscale,Matrix.exp_units_conj,hu,hinv]

/-- The preparation matrix obtained by composing the initial preparation with the actual stage
words in chronological order. -/
def frozenPreparation (stages : ℕ → StageData I) (P0 : Matrix I I ℂ) (seed : I → ℂ) :
    ℕ → Matrix I I ℂ
  | 0 => P0
  | n+1 => stageWord (stages n) (actualStates stages (P0*ᵥseed) n)*frozenPreparation stages P0 seed n

/-- Applying the frozen prefix preparation to the seed produces the actual state after that
prefix. -/
theorem frozenPreparation_action (stages : ℕ → StageData I) (P0 : Matrix I I ℂ) (seed : I → ℂ) :
    ∀ n,frozenPreparation stages P0 seed n*ᵥseed=actualStates stages (P0*ᵥseed) n
  | 0 => rfl
  | n+1 => by rw [frozenPreparation,← Matrix.mulVec_mulVec,frozenPreparation_action,actualStates]

/-- Every frozen prefix preparation is unitary when the initial preparation is unitary. -/
theorem frozenPreparation_unitary (stages : ℕ → StageData I) (P0 : Matrix I I ℂ)
    (hP0 : P0∈Matrix.unitaryGroup I ℂ) (seed : I → ℂ) :
    ∀ n,frozenPreparation stages P0 seed n∈Matrix.unitaryGroup I ℂ
  | 0 => hP0
  | n+1 => (Matrix.unitaryGroup I ℂ).mul_mem (stageWord_unitary _ _)
      (frozenPreparation_unitary stages P0 hP0 seed n)

/-- The learned mixer for an actual prefix state equals the seed mixer conjugated by the full
frozen prefix preparation, implementing coherent replay as in [ZhouAnLiu2026]. -/
theorem actual_prefix_replay (stages : ℕ → StageData I) (P0 : Matrix I I ℂ)
    (hP0 : P0∈Matrix.unitaryGroup I ℂ) (seed : I → ℂ) (n : ℕ) (β : ℝ) :
    mixerExp (learnedGenerator (actualStates stages (P0*ᵥseed) n)) β=
      frozenPreparation stages P0 seed n*mixerExp (learnedGenerator seed) β*
        (frozenPreparation stages P0 seed n)ᴴ := by
  rw [← frozenPreparation_action stages P0 seed n]
  exact learnedMixer_prepared _ (frozenPreparation_unitary stages P0 hP0 seed n) _ _
end Qatlib.Papers.ProjectorQAOA26.StageStability
