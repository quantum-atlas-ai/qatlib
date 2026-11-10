/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DiamondQdrift.QuantizerCert.EffectiveCeilQuantizerLawStat
import Qatlib.Concepts.DiamondQdrift.SignedBridge.RealCoefficientFairBitSubgoalStat
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.DiamondQdrift.QuantizerCert
open Qatlib.Concepts.DiamondQdrift.SignedBridge
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.FairBitSampling

namespace Qatlib.Concepts.DiamondQdrift.DigitEndpoint

open Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

noncomputable def effectiveQdriftBits (L n : ℕ) (ε : ℝ) : ℕ :=
  Nat.log2 (Nat.ceil (12*(n : ℝ)*(L : ℝ)/ε)+1)

def EffectiveQuantizerFairBitSubgoal : Prop :=
  ∀ (L D : ℕ) (a : Fin L → ℝ) (K : Fin L → Operator D) (t ε : ℝ) (j0 : Fin L)
    (q : Fin L → ℕ → ℚ) (sgn : Fin L → Bool),
    0 < ∑ j, |a j| → (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) → 0 < ε →
    (∀ j, RatLowerOracle |a j| (q j)) →
    (∀ j, (if sgn j then -(a j) else a j) = |a j|) →
    let lam := ∑ j, |a j|
    let n := realCoefQdriftSteps lam t ε
    let M := 2^effectiveQdriftBits L n ε
    let s := realCoefQdriftSuccess ε
    let R := fairQdriftFuel n s
    let kq := effectiveQuantizerPrecision M q
    let w := effectiveCeilQuantizer q kq M
    let W := weightTotal w
    let Ks := fun j => (if sgn j then (-1 : ℂ) else 1) • K j
    (kq ≤ Nat.clog 2 (Nat.ceil ((L : ℝ)*(2*(M : ℝ)+3)/lam))) ∧
    (M ≤ W ∧ ∑ j, |((w j : ℝ)/(W : ℝ))-|a j|/lam| ≤ 4*(L : ℝ)/M) ∧
    finiteDiamondDistance (fairQdriftActualMap w j0 n R Ks (t*lam/(W : ℝ)))
      (conjBranch (HamiltonianEvolution (∑ j, (a j : ℂ) • K j) t)) ≤
      ENNReal.ofReal ε ∧
    (∀ ω : Fin n → Fin R → Reg (Nat.clog 2 W),
      IsUnitaryCircuit (fairQdriftCircuit w j0 n R Ks (t*lam/(W : ℝ)) ω) ∧
      QueryCount (fairQdriftCircuit w j0 n R Ks (t*lam/(W : ℝ)) ω) = 0 ∧
      GateCount (fairQdriftCircuit w j0 n R Ks (t*lam/(W : ℝ)) ω) = n ∧
      (∑ m, (fairQdriftPick w j0 R (ω m)).2.1) ≤ n*Nat.clog 2 W*R ∧
      (∑ m, (fairQdriftPick w j0 R (ω m)).2.2) ≤ n*L*R)

end Qatlib.Concepts.DiamondQdrift.DigitEndpoint
