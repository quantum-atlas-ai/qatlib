/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVariableTimePaidStages
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVariableTime

/-!
# Coherent prefixes as paid circuits

This module forms `paidPrefix` by concatenating paid stage words and proves that it realizes
`CoherentVtFrame.stageState` with a clean flag. Legality and adjoint recovery connect coherent
variable-time prefixes to the paid circuit model used for [Ambainis2012].

## Main statements

* `paidPrefix_clean`: exact clean-input prefix semantics.
* `paidPrefix_legal`: legality of every valid prefix.
* `paidPrefix_reverse_clean`: recovery of the initial clean state.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Matrix
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.QlsReadoutSpec.ProgramModel
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVtFrame
open scoped Classical BigOperators
set_option warningAsError false
noncomputable section
set_option linter.unusedSectionVars false
variable {H : Type} [Fintype H] [DecidableEq H] {m : ℕ}

/-- The paid word implementing stage `j` of a coherent variable-time frame. -/
def frameStageWord (f : CoherentVtFrame H m) (j : Fin m) : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H 2 :=
  paidStageWord (f.stopAt j) f.target j.val

/-- The base-oracle family agrees with the frame's base matrix at every valid stage index. -/
theorem baseOracles_at (f : CoherentVtFrame H m) (j : Fin m) :
    baseOracles f j.val = f.base j := by simp [baseOracles, j.isLt]

/-- Executing a frame stage word on a clean workspace applies its coherent stage operator to the
payload and returns a clean flag. -/
theorem frameStage_clean (f : CoherentVtFrame H m) (j : Fin m) (ψ : QState H) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix (baseOracles f) (frameStageWord f j) *ᵥ Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide) ψ =
      Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide) (ApplyGate (f.stageOp j) ψ) := by
  have hcomm : (ReflectionAbout f.target * baseOracles f j.val * ReflectionAbout f.target) *
      f.stopAt j = f.stopAt j *
        (ReflectionAbout f.target * baseOracles f j.val * ReflectionAbout f.target) := by
    simpa only [baseOracles_at, CoherentVtFrame.round, stageRound] using! f.round_comm j
  simpa only [frameStageWord, baseOracles_at, CoherentVtFrame.stageOp,
    CoherentVtFrame.round, stageRound, ApplyGate] using!
    paidStage_clean (baseOracles f) (f.stopAt j) f.target j.val
      (f.stopNested.1 ⟨j.val, by omega⟩) f.targetOrth hcomm ψ

/-- Each frame stage word is legal with respect to the frame's `m` oracle slots. -/
theorem frameStage_legal (f : CoherentVtFrame H m) (j : Fin m) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.legal m (frameStageWord f j) :=
  paidStage_legal (f.stopAt j) f.target j.val m
    (f.stopNested.1 ⟨j.val, by omega⟩) f.targetOrth j.isLt

/-- The concatenation of the first `n` paid frame stage words. -/
def paidPrefix (f : CoherentVtFrame H m) : (n : ℕ) → n ≤ m → Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H 2
  | 0, _ => []
  | n + 1, hn => paidPrefix f n (by omega) ++ frameStageWord f ⟨n, by omega⟩

/-- Executing a paid prefix on a clean workspace gives the clean embedding of the coherent
prefix state. -/
theorem paidPrefix_clean (f : CoherentVtFrame H m) (ψ : QState H)
    (n : ℕ) (hn : n ≤ m) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix (baseOracles f) (paidPrefix f n hn) *ᵥ Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide) ψ =
      Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide) (f.stageState ψ n hn) := by
  induction n with
  | zero => simp [paidPrefix, Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix, CoherentVtFrame.stageState,
      CoherentVtFrame.stageStateFrom]
  | succ n ih =>
    rw [paidPrefix, wordMatrix_append, ← Matrix.mulVec_mulVec, ih, frameStage_clean]
    rfl

/-- Every valid paid prefix is legal. -/
theorem paidPrefix_legal (f : CoherentVtFrame H m) (n : ℕ) (hn : n ≤ m) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.legal m (paidPrefix f n hn) := by
  induction n with
  | zero => intro s hs; simp [paidPrefix] at hs
  | succ n ih =>
    intro s hs
    rw [paidPrefix, List.mem_append] at hs
    rcases hs with hs | hs
    · exact ih (by omega) s hs
    · exact frameStage_legal f _ s hs

/-- Every in-range member of the frame's base-oracle family is unitary. -/
theorem frame_oracles_unitary (f : CoherentVtFrame H m) :
    ∀ k < m, baseOracles f k ∈ unitaryGroup H ℂ := by
  intro k hk
  simp only [baseOracles, dif_pos hk]
  exact f.baseUnitary ⟨k, hk⟩

/-- Executing the adjoint paid prefix after the forward prefix restores any workspace state. -/
theorem paidPrefix_adjoint_undo (f : CoherentVtFrame H m) (n : ℕ) (hn : n ≤ m)
    (Φ : QState (Qatlib.Concepts.QlsReadoutSpec.Amplification.Space H 2)) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix (baseOracles f) (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint (paidPrefix f n hn)) *ᵥ
      (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix (baseOracles f) (paidPrefix f n hn) *ᵥ Φ) = Φ := by
  have hU := wordMatrix_unitary (baseOracles f) (paidPrefix f n hn)
    (frame_oracles_unitary f) (paidPrefix_legal f n hn)
  have hu : (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix (baseOracles f) (paidPrefix f n hn))ᴴ *
      Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix (baseOracles f) (paidPrefix f n hn) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hU
  rw [wordMatrix_wordAdjoint, Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]

/-- Executing the adjoint paid prefix on the clean coherent prefix state recovers the initial
clean state. -/
theorem paidPrefix_reverse_clean (f : CoherentVtFrame H m) (ψ : QState H)
    (n : ℕ) (hn : n ≤ m) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix (baseOracles f) (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint (paidPrefix f n hn)) *ᵥ
      Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide) (f.stageState ψ n hn) = Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide) ψ := by
  rw [← paidPrefix_clean f ψ n hn]
  exact paidPrefix_adjoint_undo f n hn _

end
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
