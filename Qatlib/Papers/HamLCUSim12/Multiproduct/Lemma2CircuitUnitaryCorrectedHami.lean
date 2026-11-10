/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2CircuitUnitaryCorrectedStat
import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedAlgebra
set_option warningAsError false

open Qatlib.Papers.HamLCUSim12.LCUDeferred
open Qatlib.Concepts.CoherentSim.ResetDiscard

open Qatlib.Concepts.GateVocabulary.GateVocab

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open Matrix
open scoped Classical Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

theorem lemma2CircuitUnitaryCorrected : Lemma2CircuitUnitaryCorrected := by
  intro I _ _ κ hκ Ua Ub hUa hUb
  rw [lemma2CircuitCorrected_fig3]
  apply (relabelGate_mem_unitaryGroup _ _).mpr
  apply fig3CircuitUnitary
  · intro b; split_ifs <;> assumption
  · exact vKappaSource_unitary κ hκ
  · simpa only [Matrix.star_eq_conjTranspose] using Unitary.star_mem (vKappaSource_unitary κ hκ)

end Qatlib.Papers.HamLCUSim12.Multiproduct
