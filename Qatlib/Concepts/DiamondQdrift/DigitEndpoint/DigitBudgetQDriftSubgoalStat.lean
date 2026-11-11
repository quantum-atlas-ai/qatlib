/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DiamondQdrift.DigitEndpoint.DigitBudgetQDriftProgram

/-!
# Specification of digit budget qDRIFT

This module states `DigitBudgetQDriftSubgoal` for rational lower coefficient oracles and sign
flags. The specification combines finite diamond approximation with digit access, simulation
step, circuit, and fair coin sampling bounds in the qDRIFT setting of [Campbell2019].

## Main statements

* `DigitBudgetQDriftSubgoal`: the combined numerical and circuit resource specification.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.DiamondQdrift.QuantizerCert
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.EffectiveInput
open Qatlib.Concepts.RandCompile.FairBitSampling

namespace Qatlib.Concepts.DiamondQdrift.DigitEndpoint
open Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-- The digit budget compiler reads one coefficient column, satisfies the stated step bound and
finite diamond tolerance, and produces unitary branches with the specified query, gate,
coin, and comparison counts [Campbell2019]. -/
def DigitBudgetQDriftSubgoal : Prop :=
  ∀ (L D : ℕ) (a : Fin L → ℝ) (K : Fin L → Operator D)
    (t ε : ℚ) (j0 : Fin L) (q : Fin L → ℕ → ℚ) (sgn : Fin L → Bool),
    (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) → 0 < ε → ε ≤ 1 →
    (∀ j, RatLowerOracle |a j| (q j)) →
    (∀ j, (if sgn j then -(a j) else a j) = |a j|) →
    let r := digitBudgetQDriftData q sgn t ε
    let W := weightTotal r.weights
    let terms := dyadicSignedTerms r.precision r.table K
    r.digitReads = L ∧
    r.digits = List.ofFn (fun j => q j r.precision) ∧
    r.steps ≤ Nat.ceil (32 * (∑ j, |a j|) ^ 2 * (t : ℝ) ^ 2 / (ε : ℝ)) + 3 ∧
    finiteDiamondDistance (fairQdriftActualMap r.weights j0 r.steps r.fuel terms r.baseTime)
      (conjBranch (HamiltonianEvolution (∑ j, (a j : ℂ) • K j) t)) ≤
      ENNReal.ofReal (ε : ℝ) ∧
    (∀ ω : Fin r.steps → Fin r.fuel → Reg (Nat.clog 2 W),
      IsUnitaryCircuit (fairQdriftCircuit r.weights j0 r.steps r.fuel terms r.baseTime ω) ∧
      QueryCount (fairQdriftCircuit r.weights j0 r.steps r.fuel terms r.baseTime ω) = 0 ∧
      GateCount (fairQdriftCircuit r.weights j0 r.steps r.fuel terms r.baseTime ω) =
        (if W = 0 then 0 else r.steps) ∧
      (∑ i, (fairQdriftPick r.weights j0 r.fuel (ω i)).2.1) ≤
        r.steps * Nat.clog 2 W * r.fuel ∧
      (∑ i, (fairQdriftPick r.weights j0 r.fuel (ω i)).2.2) ≤ r.steps * L * r.fuel)

end Qatlib.Concepts.DiamondQdrift.DigitEndpoint
