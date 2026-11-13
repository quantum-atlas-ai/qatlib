/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2CircuitUnitaryCorrectedStat
import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedAlgebra

/-!
# Unitarity of the corrected two-unitary LCU circuit

This module proves `lemma2CircuitUnitaryCorrected`: for nonnegative κ and unitary inputs, the
corrected two-unitary LCU circuit is unitary. The proof expresses the circuit using the Figure 3
construction and its unitary ancilla rotations. See [ChildsWiebe2012] for the multiproduct and
linear-combination simulation framework.

## Main statements

* `lemma2CircuitUnitaryCorrected`: For κ ≥ 0 and unitary inputs, the corrected two-unitary LCU
  circuit is unitary, as specified by `Lemma2CircuitUnitaryCorrected`.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

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

/-- For κ ≥ 0 and unitary inputs, the corrected two-unitary LCU circuit is unitary, as specified
by `Lemma2CircuitUnitaryCorrected`. See [ChildsWiebe2012]. -/
theorem lemma2CircuitUnitaryCorrected : Lemma2CircuitUnitaryCorrected := by
  intro I _ _ κ hκ Ua Ub hUa hUb
  rw [lemma2CircuitCorrected_fig3]
  apply (relabelGate_mem_unitaryGroup _ _).mpr
  apply fig3CircuitUnitary
  · intro b; split_ifs <;> assumption
  · exact vKappaSource_unitary κ hκ
  · simpa only [Matrix.star_eq_conjTranspose] using Unitary.star_mem (vKappaSource_unitary κ hκ)

end Qatlib.Papers.HamLCUSim12.Multiproduct
