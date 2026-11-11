/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedDefinitions

/-!
# Corrected two-unitary output-fiber statement

The proposition `Lemma2FiberCorrected` specifies the success and failure fibers of
`lemma2OutputCorrected` for nonnegative κ and unitary inputs. Its identities hold for every
input state, without a normalization requirement. See [ChildsWiebe2012] for the multiproduct and
linear-combination simulation framework.

## Main statements

* `Lemma2FiberCorrected`: The proposition that the corrected output fibers equal ((κUa + Ub)/(κ
  + 1))ψ and (√κ/(κ + 1))(Ub − Ua)ψ for κ ≥ 0, unitary inputs, and every state ψ.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.HamLCUSim12.LCUDeferred

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open Matrix

/-- The proposition that the corrected output fibers equal ((κUa + Ub)/(κ + 1))ψ and (√κ/(κ +
1))(Ub − Ua)ψ for κ ≥ 0, unitary inputs, and every state ψ. -/
def Lemma2FiberCorrected : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (κ : ℝ), 0 ≤ κ →
    ∀ (Ua Ub : Matrix I I ℂ), Ua ∈ Matrix.unitaryGroup I ℂ → Ub ∈ Matrix.unitaryGroup I ℂ →
      ∀ ψ : QState I,
        (∀ x : I, lemma2OutputCorrected κ Ua Ub ψ (fun _ => false, x)
            = ((((κ : ℂ) / (κ + 1)) • Ua + (((1 : ℂ) / (κ + 1)) • Ub)) *ᵥ ψ) x)
        ∧ (∀ x : I, lemma2OutputCorrected κ Ua Ub ψ (fun _ => true, x)
            = (((((Real.sqrt κ / (κ + 1) : ℝ) : ℂ)) • (Ub - Ua)) *ᵥ ψ) x)

end Qatlib.Papers.HamLCUSim12.Multiproduct
