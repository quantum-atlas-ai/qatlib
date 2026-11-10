/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenVariableTimeAlgorithmStat
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenCascadeAux
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.AverageStopTailBoundVari
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.NormNum.RealSqrt
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option maxHeartbeats 900000
open Matrix
open scoped Classical BigOperators

variable {C : Type} [Fintype C] [DecidableEq C]

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
noncomputable section

theorem rdvt_live_aa_born (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (hl : GrowingVtLegal stages history)
    (word : List DataVtStep) (hw : DataVtWordLegal stages word)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hmass : MeasureProb (dataVtWordState stages history j₀ word) (liveSet C) = a) (k : ℕ) :
    MeasureProb (dataVtWordState stages history j₀ (liveAAWord word k)) (liveSet C)
      = (Real.sin ((2*(k:ℝ)+1)*Real.arcsin (Real.sqrt a)))^2 := by
  have hA : dataVtWordMatrix stages history j₀ word ∈ Matrix.unitaryGroup (VtSpace C) ℂ :=
    dataVtWordMatrix_unitary stages history j₀ hl word hw
  have hsq1 : Real.sqrt a < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith)
  have hpre : MeasureProb (preparedAAState (dataVtWordMatrix stages history j₀ word) j₀)
      (liveSet C) = (Real.sin (Real.arcsin (Real.sqrt a)))^2 := by
    show MeasureProb (dataVtWordState stages history j₀ word) (liveSet C) = _
    rw [hmass, Real.sin_arcsin (by linarith [Real.sqrt_nonneg a]) (by linarith)]
    exact (Real.sq_sqrt ha0.le).symm
  rw [liveAAWord_state stages history j₀ hl word hw k,
    prepared_aa_born_success (dataVtWordMatrix stages history j₀ word) j₀ (liveSet C)
      (Real.arcsin (Real.sqrt a)) k hA (Real.arcsin_pos.2 (Real.sqrt_pos.mpr ha0))
      (Real.arcsin_lt_pi_div_two.2 hsq1) hpre]
end
noncomputable section

theorem rdvt_good_aa_state (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (hl : GrowingVtLegal stages history)
    (word : List DataVtStep) (hw : DataVtWordLegal stages word) (k : ℕ) :
    dataVtWordState stages history j₀ (goodAAWord word k) =
      Run (preparedMark (goodSet C))
        (preparedAACircuit (dataVtWordMatrix stages history j₀ word) j₀ k) (Qatlib.Foundations.PureStateMath.Ket j₀) := by
  rw [(prepared_aa_actual_circuit (dataVtWordMatrix stages history j₀ word) j₀ (goodSet C) k
    (dataVtWordMatrix_unitary stages history j₀ hl word hw)).2.2.2]
  simp only [dataVtWordState, goodAAWord_matrix, preparedAAState, ApplyGate, Matrix.mulVec_mulVec]
end
noncomputable section

theorem rdvt_good_aa_born (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (hl : GrowingVtLegal stages history)
    (word : List DataVtStep) (hw : DataVtWordLegal stages word)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hmass : MeasureProb (dataVtWordState stages history j₀ word) (goodSet C) = a) (k : ℕ) :
    MeasureProb (dataVtWordState stages history j₀ (goodAAWord word k)) (goodSet C)
      = (Real.sin ((2*(k:ℝ)+1)*Real.arcsin (Real.sqrt a)))^2 := by
  have hA : dataVtWordMatrix stages history j₀ word ∈ Matrix.unitaryGroup (VtSpace C) ℂ :=
    dataVtWordMatrix_unitary stages history j₀ hl word hw
  have hsq1 : Real.sqrt a < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith)
  have hpre : MeasureProb (preparedAAState (dataVtWordMatrix stages history j₀ word) j₀)
      (goodSet C) = (Real.sin (Real.arcsin (Real.sqrt a)))^2 := by
    show MeasureProb (dataVtWordState stages history j₀ word) (goodSet C) = _
    rw [hmass, Real.sin_arcsin (by linarith [Real.sqrt_nonneg a]) (by linarith)]
    exact (Real.sq_sqrt ha0.le).symm
  rw [rdvt_good_aa_state stages history j₀ hl word hw k,
    prepared_aa_born_success (dataVtWordMatrix stages history j₀ word) j₀ (goodSet C)
      (Real.arcsin (Real.sqrt a)) k hA (Real.arcsin_pos.2 (Real.sqrt_pos.mpr ha0))
      (Real.arcsin_lt_pi_div_two.2 hsq1) hpre]

end
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
