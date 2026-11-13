/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemGates95.MultiControl.Section7.MultibitNetworks
import Qatlib.Concepts.GateTables.GrayUniversal.Section8GrayUniversalityElem

/-!
# Exact universality on a qubit register

This module states the final exact universality construction of Section 8 of [BarencoEtAl1995].
For every positive register size and every unitary on that register, `section8_universality`
produces a legal list of local elementary gates whose compiled action agrees with the unitary on
every state.

The explicit list-length bound comes from the imported two-level decomposition and Gray-code
implementation. The compiled list makes no oracle queries, and its gate count equals its length.

## Main statements

* `section8_universality`: exact implementation of an arbitrary `n`-qubit unitary with the
  displayed finite bound `2^(n-1) * (2^n + 1) * (2*n - 1) * (256*n^2 + 2*n - 2)`.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Papers.ElemGates95.Universality

/-- The exact universality construction of Section 8 of [BarencoEtAl1995]: every unitary on a
register of `n ≥ 1` qubits has a legal elementary gate list implementing its action on all
states. The list satisfies the displayed explicit length bound, uses no queries, and has
gate count equal to its length. -/
theorem section8_universality (n : ℕ) (hn : 1 ≤ n)
    (U : Matrix (Reg n) (Reg n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Reg n) ℂ) :
    ∃ gs : List (ReflectionGate n), reflectionLegal gs ∧
      gs.length ≤ 2 ^ (n - 1) * (2 ^ n + 1) * ((2 * n - 1) * (256 * n ^ 2 + 2 * n - 2)) ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n),
        Run (1 : Matrix (Reg n) (Reg n) ℂ) (reflectionCompile gs) ψ =
          Matrix.mulVec U ψ :=
  Qatlib.Concepts.GateTables.GrayUniversal.section8GrayUniversality n hn U hU

end Qatlib.Papers.ElemGates95.Universality
