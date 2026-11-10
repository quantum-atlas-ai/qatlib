/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.StageStability.ActualStages
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.StageStability
open scoped Matrix Matrix.Norms.L2Operator
open Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel
variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

theorem rankOne_prepared (U : Matrix I I ℂ) (v : I → ℂ) :
    rankOne (U*ᵥv)=U*rankOne v*Uᴴ := by
  simp only [rankOne,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,Matrix.star_mulVec]

theorem learnedGenerator_prepared (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (v : I → ℂ) :
    learnedGenerator (U*ᵥv)=U*learnedGenerator v*Uᴴ := by
  have hu : U*Uᴴ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hU
  simp only [learnedGenerator,rankOne_prepared,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hu]

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

def frozenPreparation (stages : ℕ → StageData I) (P0 : Matrix I I ℂ) (seed : I → ℂ) :
    ℕ → Matrix I I ℂ
  | 0 => P0
  | n+1 => stageWord (stages n) (actualStates stages (P0*ᵥseed) n)*frozenPreparation stages P0 seed n

theorem frozenPreparation_action (stages : ℕ → StageData I) (P0 : Matrix I I ℂ) (seed : I → ℂ) :
    ∀ n,frozenPreparation stages P0 seed n*ᵥseed=actualStates stages (P0*ᵥseed) n
  | 0 => rfl
  | n+1 => by rw [frozenPreparation,← Matrix.mulVec_mulVec,frozenPreparation_action,actualStates]

theorem frozenPreparation_unitary (stages : ℕ → StageData I) (P0 : Matrix I I ℂ)
    (hP0 : P0∈Matrix.unitaryGroup I ℂ) (seed : I → ℂ) :
    ∀ n,frozenPreparation stages P0 seed n∈Matrix.unitaryGroup I ℂ
  | 0 => hP0
  | n+1 => (Matrix.unitaryGroup I ℂ).mul_mem (stageWord_unitary _ _)
      (frozenPreparation_unitary stages P0 hP0 seed n)

theorem actual_prefix_replay (stages : ℕ → StageData I) (P0 : Matrix I I ℂ)
    (hP0 : P0∈Matrix.unitaryGroup I ℂ) (seed : I → ℂ) (n : ℕ) (β : ℝ) :
    mixerExp (learnedGenerator (actualStates stages (P0*ᵥseed) n)) β=
      frozenPreparation stages P0 seed n*mixerExp (learnedGenerator seed) β*
        (frozenPreparation stages P0 seed n)ᴴ := by
  rw [← frozenPreparation_action stages P0 seed n]
  exact learnedMixer_prepared _ (frozenPreparation_unitary stages P0 hP0 seed n) _ _
end Qatlib.Papers.ProjectorQAOA26.StageStability
