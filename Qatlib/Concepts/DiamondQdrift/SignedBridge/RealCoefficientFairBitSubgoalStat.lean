/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQDrift

/-!
# Real coefficient finite coin specification

This module defines the integer weights and numerical parameters for finite coin qDRIFT with
real coefficients. `RealCoefficientFairBitSubgoal` combines magnitude law approximation, finite
diamond error, and branchwise circuit and sampling bounds for the simulation framework of
[Campbell2019].

## Main statements

* `realCoefQdriftWeights`: ceiling weights for the scaled coefficient law.
* `RealCoefficientFairBitSubgoal`: the combined finite coin simulation specification.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.FairBitSampling
open Qatlib.Concepts.RandCompile.ReferenceModel

namespace Qatlib.Concepts.DiamondQdrift.SignedBridge

open Matrix
open scoped ENNReal Matrix.Norms.L2Operator

/-- The natural ceiling weights `ceil (M * h j / lam)`. -/
noncomputable def realCoefQdriftWeights {L : ℕ} (h : Fin L → ℝ) (lam : ℝ) (M : ℕ) :
    Fin L → ℕ := fun j => Nat.ceil ((M : ℝ) * h j / lam)

/-- The positive simulation step count `max 1 (ceil (12 * lam² * t² / ε))`. -/
noncomputable def realCoefQdriftSteps (lam t ε : ℝ) : ℕ :=
  max 1 Nat.ceil (12 * lam ^ 2 * t ^ 2 / ε)

/-- The weight precision parameter `Nat.log2 (Nat.ceil (6 * n * L / ε) + 1)`. -/
noncomputable def realCoefQdriftBits (L n : ℕ) (ε : ℝ) : ℕ :=
  Nat.log2 (Nat.ceil (6 * (n : ℝ) * L / ε) + 1)

/-- The rejection success precision parameter `Nat.log2 (Nat.ceil (6 / ε) + 1)`. -/
noncomputable def realCoefQdriftSuccess (ε : ℝ) : ℕ :=
  Nat.log2 (Nat.ceil (6 / ε) + 1)

/-- For positive coefficient magnitude sum and tolerance, the quantized signed term construction
satisfies the stated probability law error and finite diamond bound, with unitary branches
and explicit query, gate, coin, and comparison counts [Campbell2019]. -/
def RealCoefficientFairBitSubgoal : Prop :=
  ∀ (L D : ℕ) (a : Fin L → ℝ) (K : Fin L → Operator D) (t ε : ℝ) (j0 : Fin L),
    0 < ∑ j, |a j| → (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) → 0 < ε →
    let lam := ∑ j, |a j|
    let n := realCoefQdriftSteps lam t ε
    let b := realCoefQdriftBits L n ε
    let M := 2 ^ b
    let s := realCoefQdriftSuccess ε
    let R := fairQdriftFuel n s
    let w := realCoefQdriftWeights (fun j => |a j|) lam M
    let W := weightTotal w
    let Ks := qdriftSignedTerms a K
    (M ≤ W ∧
      ∑ j, |((w j : ℝ) / (W : ℝ)) - |a j| / lam| ≤ (2 : ℝ) * L / M) ∧
    finiteDiamondDistance
        (fairQdriftActualMap w j0 n R Ks (t * lam / (W : ℝ)))
        (conjBranch (HamiltonianEvolution (∑ j, (a j : ℂ) • K j) t))
      ≤ ENNReal.ofReal ε ∧
    (∀ ω : Fin n → Fin R → Reg (Nat.clog 2 W),
      IsUnitaryCircuit (fairQdriftCircuit w j0 n R Ks (t * lam / (W : ℝ)) ω) ∧
      QueryCount (fairQdriftCircuit w j0 n R Ks (t * lam / (W : ℝ)) ω) = 0 ∧
      GateCount (fairQdriftCircuit w j0 n R Ks (t * lam / (W : ℝ)) ω) = n ∧
      (∑ k, (fairQdriftPick w j0 R (ω k)).2.1) ≤ n * Nat.clog 2 W * R ∧
      (∑ k, (fairQdriftPick w j0 R (ω k)).2.2) ≤ n * L * R)

end Qatlib.Concepts.DiamondQdrift.SignedBridge
