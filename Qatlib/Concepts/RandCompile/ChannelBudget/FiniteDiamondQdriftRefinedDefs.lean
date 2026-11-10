/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQDrift
import Qatlib.Concepts.RandCompile.EffectiveInput.QuantizedCoefficientQDrift
import Qatlib.Concepts.RandCompile.ChannelBudget.FairBitQDriftConsumers
import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis
open Qatlib.Concepts.SchattenDiamond.DiamondNorm
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false

namespace Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs

open Matrix Qatlib
open scoped BigOperators Classical ENNReal Matrix.Norms.L2Operator

def ratBits (r : ℚ) : ℕ := r.num.natAbs + r.den

def ratOpBits (r s : ℚ) : ℕ := (ratBits r + 2) * (ratBits s + 2)

structure DyadicRead (x : ℝ) (q : ℕ → ℚ) : Prop where

  exact_form : ∀ k, ∃ m : ℤ, q k = m / ((2 : ℚ) ^ k)

  accuracy : ∀ k, |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k

  numerator_bound : ∀ k (m : ℤ), q k = m / ((2 : ℚ) ^ k) →
    |m| ≤ ((2 : ℕ) ^ k) * (Nat.ceil |x| + 1)

structure DyadicLowerRead (x : ℝ) (q : ℕ → ℚ) : Prop where

  exact_form : ∀ k, ∃ m : ℤ, q k = m / ((2 : ℚ) ^ k)

  lower : ∀ k, (q k : ℝ) ≤ x

  deficit : ∀ k, x - (q k : ℝ) ≤ (1 / 2 : ℝ) ^ k

  numerator_bound : ∀ k (m : ℤ), q k = m / ((2 : ℚ) ^ k) →
    |m| ≤ ((2 : ℕ) ^ k) * (Nat.ceil |x| + 1)

noncomputable def dyadicReadSpace (x : ℝ) (k : ℕ) : ℕ :=
  ((2 : ℕ) ^ k) * (Nat.ceil |x| + 1) + k + 1

structure RatCost where

  ringOps : ℕ

  ceilOps : ℕ

  logOps : ℕ

  digitOps : ℕ
  deriving Repr, DecidableEq

def RatCost.total (c : RatCost) : ℕ := c.ringOps + c.ceilOps + c.logOps + c.digitOps

inductive RatProgram where

  | lit (q : ℚ)

  | add (a b : RatProgram)

  | mul (a b : RatProgram)

  | div (a b : RatProgram)

  | ceil (a : RatProgram)

  | log2 (a : RatProgram)

  | digits (a : RatProgram) (k : ℕ)
  deriving Repr, DecidableEq

def RatProgram.eval : RatProgram → ℚ
  | .lit q => q
  | .add a b => RatProgram.eval a + RatProgram.eval b
  | .mul a b => RatProgram.eval a * RatProgram.eval b
  | .div a b => RatProgram.eval a / RatProgram.eval b
  | .ceil a => Rat.ceil (RatProgram.eval a)
  | .log2 a => (Nat.clog 2 (RatProgram.eval a).num.natAbs : ℚ)
  | .digits a k => ((⌊RatProgram.eval a * (2 : ℚ) ^ k⌋ : ℤ) : ℚ) / (2 : ℚ) ^ k

def RatProgram.cost : RatProgram → RatCost
  | .lit _ => ⟨0, 0, 0, 0⟩
  | .add a b =>
      let ca := RatProgram.cost a
      let cb := RatProgram.cost b
      ⟨ca.ringOps + cb.ringOps + 1, ca.ceilOps + cb.ceilOps, ca.logOps + cb.logOps,
        ca.digitOps + cb.digitOps⟩
  | .mul a b =>
      let ca := RatProgram.cost a
      let cb := RatProgram.cost b
      ⟨ca.ringOps + cb.ringOps + 1, ca.ceilOps + cb.ceilOps, ca.logOps + cb.logOps,
        ca.digitOps + cb.digitOps⟩
  | .div a b =>
      let ca := RatProgram.cost a
      let cb := RatProgram.cost b
      ⟨ca.ringOps + cb.ringOps + 1, ca.ceilOps + cb.ceilOps, ca.logOps + cb.logOps,
        ca.digitOps + cb.digitOps⟩
  | .ceil a =>
      let ca := RatProgram.cost a
      ⟨ca.ringOps, ca.ceilOps + 1, ca.logOps, ca.digitOps⟩
  | .log2 a =>
      let ca := RatProgram.cost a
      ⟨ca.ringOps, ca.ceilOps, ca.logOps + 1, ca.digitOps⟩
  | .digits a _ =>
      let ca := RatProgram.cost a
      ⟨ca.ringOps, ca.ceilOps, ca.logOps, ca.digitOps + 1⟩

def RatProgram.nodes : RatProgram → ℕ
  | .lit _ => 0
  | .add a b => RatProgram.nodes a + RatProgram.nodes b + 1
  | .mul a b => RatProgram.nodes a + RatProgram.nodes b + 1
  | .div a b => RatProgram.nodes a + RatProgram.nodes b + 1
  | .ceil a => RatProgram.nodes a + 1
  | .log2 a => RatProgram.nodes a + 1
  | .digits a _ => RatProgram.nodes a + 1

def RatCost.bitTime (c : RatCost) (B : ℕ) : ℕ := c.total * (B + 2) * (B + 2)

def RatCost.bitSpace (_c : RatCost) (B : ℕ) : ℕ := 3 * (B + 2)

def digitTable {L : ℕ} (q : Fin L → ℕ → ℚ) (sgn : Fin L → Bool) (k : ℕ) : Fin L → ℚ :=
  fun j => if sgn j then -(q j k) else q j k

noncomputable def digitTableSpace (L : ℕ) (x : ℝ) (k : ℕ) : ℕ := L * dyadicReadSpace x k

noncomputable def digitTableBitTime (L : ℕ) (x : ℝ) (k : ℕ) : ℕ := L * dyadicReadSpace x k

def scanCert (tq eq : ℚ) (T : ℕ) (k : ℕ) : Bool :=
  decide (0 < eq - 1 / ((2 : ℚ) ^ k) ∧ |tq| ≤ (T : ℚ))

def correctedBudget (eq : ℚ) (k : ℕ) : ℚ := eq - 1 / ((2 : ℚ) ^ k)

def scanPrecision (fuel : ℕ) (tq eq : ℕ → ℚ) (T : ℕ) : ℕ :=
  ((List.range (fuel + 1)).find? (fun k => scanCert (tq k) (eq k) T k)).getD (max 1 fuel)

structure ScanLedger where

  scanned : ℕ

  paramReads : ℕ

  digitReads : ℕ

  bitTime : ℕ

  bitSpace : ℕ
  deriving Repr, DecidableEq

noncomputable def scanRunBitLength (L : ℕ) (x : ℝ) (k : ℕ) : ℕ :=
  dyadicReadSpace x k + digitTableSpace L x k + 2 * (Nat.clog 2 (L + 1)) + 64

noncomputable def scanLedger (L : ℕ) (x : ℝ) (k : ℕ) (prog : RatProgram) : ScanLedger :=
  let ops := (RatProgram.cost prog).total
  let B := scanRunBitLength L x k
  { scanned := k + 1
    paramReads := 2 * (k + 1)
    digitReads := L * (k + 1)
    bitTime := (ops + L * (k + 1)) * (B + 2) * (B + 2)
    bitSpace := B + digitTableSpace L x k + 16 }

noncomputable def fairBitBudget (W T R : ℕ) (n : ℕ) : ℝ :=
  2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (n : ℝ) + (n : ℝ) / ((2 : ℝ) ^ R)

noncomputable def fairBitBudgetMin (W T R : ℕ) : ℝ :=
  2 * Real.sqrt 2 * (W : ℝ) * (T : ℝ) / Real.sqrt ((2 : ℝ) ^ R)

noncomputable def fairBitBudgetArgmin (W T R : ℕ) : ℝ :=
  Real.sqrt 2 * (W : ℝ) * (T : ℝ) * Real.sqrt ((2 : ℝ) ^ R)

noncomputable def tightFairBitCount (W T R : ℕ) : ℕ :=
  max 1 (Nat.ceil (fairBitBudgetArgmin W T R))

noncomputable def tightFairBitFuel (W T : ℕ) (eps : ℚ) : ℕ :=
  Nat.clog 2 (Nat.ceil ((2 * Real.sqrt 2 * (W : ℝ) * (T : ℝ) / (eps : ℝ)) ^ 2))

def synthGateBudget (m : ℕ) : ℕ := 128 * (m + 1) ^ 2 * 4 ^ m

def synthSpaceBudget (m : ℕ) : ℕ := m + (m + 1)

def protocolGateBudget (m n : ℕ) : ℕ := n * synthGateBudget m

def protocolSpaceBudget (m : ℕ) : ℕ := synthSpaceBudget m

def protocolClassicalSpace (n : ℕ) : ℕ := Nat.clog 2 (max 1 n)

noncomputable def unitaryProduct {m : ℕ} :
    List (Matrix (Reg m) (Reg m) ℂ) → Matrix (Reg m) (Reg m) ℂ
  | [] => 1
  | V :: U => unitaryProduct U * V

noncomputable def postSelectAmplify (delta : ℝ) : ℕ :=
  2 * (Nat.clog 2 (Nat.ceil (1 / delta)) + 1)

noncomputable def tableIQdriftCount (lam t eps : ℝ) : ℕ :=
  max 1 (Nat.ceil (2 * lam ^ 2 * t ^ 2 / eps))

noncomputable def tableIQdriftPeCount (lam deltaE pf : ℝ) : ℕ :=
  Nat.ceil (133 * lam ^ 2 / (deltaE ^ 2 * pf ^ 3))

noncomputable def tableITrotterBaseline (L : ℕ) (bigLam deltaE pf : ℝ) : ℕ :=
  Nat.ceil (69 * (L : ℝ) ^ 2 * bigLam * Real.sqrt bigLam /
    (deltaE * Real.sqrt deltaE * pf ^ 2))

def tableIBudget (deltaE pf : ℝ) : ℝ := deltaE ^ 2 * pf ^ 2

noncomputable def peChainBits (deltaE : ℝ) : ℕ :=
  Nat.clog 2 (Nat.ceil (1 / deltaE)) + 2

noncomputable def peChainRounds (pf : ℝ) : ℕ :=
  2 * (25 * Nat.clog 2 (Nat.ceil (4 / pf))) + 1

noncomputable def peChainTimes (j : ℕ) : ℝ := (2 : ℝ) ^ j

noncomputable def peChainTimeSq (deltaE : ℝ) : ℝ :=
  ∑ j : Fin (peChainBits deltaE + 1), (peChainTimes j.val) ^ 2

noncomputable def peChainErrorShare (deltaE pf : ℝ) (j : ℕ) : ℝ :=
  deltaE ^ 2 * pf ^ 3 * (peChainTimes j) ^ 2 /
    (2 * (peChainBits deltaE + 1) * peChainTimeSq deltaE)

noncomputable def peChainQuerySteps (lam deltaE pf : ℝ) (j : ℕ) : ℕ :=
  max 1 (Nat.ceil (2 * lam ^ 2 * (peChainTimes j) ^ 2 / peChainErrorShare deltaE pf j))

noncomputable def peChainTotalCount (lam deltaE pf : ℝ) : ℕ :=
  peChainRounds pf * ∑ j : Fin (peChainBits deltaE + 1), peChainQuerySteps lam deltaE pf j.val

def majorityFailure (q : ℝ) (R : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (R + 1),
    if R / 2 < i then (Nat.choose R i : ℝ) * q ^ i * (1 - q) ^ (R - i) else 0

end Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs
