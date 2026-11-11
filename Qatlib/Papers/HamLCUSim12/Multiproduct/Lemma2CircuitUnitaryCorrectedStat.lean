/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedDefinitions

/-!
# Corrected two-unitary circuit unitarity statement

The proposition `Lemma2CircuitUnitaryCorrected` states that `lemma2CircuitCorrected` is unitary
for any finite system, nonnegative κ, and unitary matrices `Ua` and `Ub`. It records the
unitarity requirement for the corrected two-unitary LCU construction. See [ChildsWiebe2012] for
the multiproduct and linear-combination simulation framework.

## Main statements

* `Lemma2CircuitUnitaryCorrected`: The proposition that `lemma2CircuitCorrected κ Ua Ub` is
  unitary whenever κ ≥ 0 and both input matrices are unitary.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false

open Qatlib.Papers.HamLCUSim12.LCUDeferred

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open Matrix

/-- The proposition that `lemma2CircuitCorrected κ Ua Ub` is unitary whenever κ ≥ 0 and both
input matrices are unitary. -/
def Lemma2CircuitUnitaryCorrected : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (κ : ℝ), 0 ≤ κ →
    ∀ (Ua Ub : Matrix I I ℂ), Ua ∈ Matrix.unitaryGroup I ℂ → Ub ∈ Matrix.unitaryGroup I ℂ →
      lemma2CircuitCorrected κ Ua Ub ∈ Matrix.unitaryGroup ((Fin 1 → Bool) × I) ℂ

end Qatlib.Papers.HamLCUSim12.Multiproduct
