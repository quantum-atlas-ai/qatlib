/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftCore
import Qatlib.Concepts.RandCompile.EffectiveInput.QuantizedCoefficientQDrift
import Qatlib.Concepts.RandCompile.ChannelBudget.FairBitQDriftConsumers
import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis

/-!
# Dyadic inputs and rational programs for qDRIFT

This module defines dyadic approximation streams, rational expression programs, and explicit
cost ledgers for finite qDRIFT parameter selection. `DyadicRead` and `DyadicLowerRead` include
numerator bounds, while `RatProgram` records both evaluation and operation counts for the
arithmetic used in the scan.

The combined budget `fairBitBudget` separates the simulation term from the bounded fair-bit
sampling term in the qDRIFT setting [Campbell2019]. Further definitions record synthesis
allowances and phase-estimation chain count expressions.

## Main statements

* `scanPrecision`: search for a positive corrected tolerance and a bounded time read.
* `scanLedger`: assemble scan and storage resource allowances.
* `tightFairBitCount`: round the real balancing value upward to a positive step count.

## References

* [Campbell, 2019][Campbell2019]
-/

open Qatlib.Concepts.SchattenDiamond.DiamondNorm
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false

namespace Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs

open Matrix Qatlib
open scoped BigOperators Classical ENNReal Matrix.Norms.L2Operator

/-- The size measure given by the absolute numerator plus the denominator of a rational number. -/
def ratBits (r : ℚ) : ℕ := r.num.natAbs + r.den

/-- The product `(ratBits r + 2) * (ratBits s + 2)`, used as a rational-operation size
allowance. -/
def ratOpBits (r s : ℚ) : ℕ := (ratBits r + 2) * (ratBits s + 2)

/-- A rational read stream with dyadic denominator `2^k`, absolute error at most `2⁻ᵏ`, and a
specified numerator magnitude bound. -/
structure DyadicRead (x : ℝ) (q : ℕ → ℚ) : Prop where

  exact_form : ∀ k, ∃ m : ℤ, q k = m / ((2 : ℚ) ^ k)

  accuracy : ∀ k, |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k

  numerator_bound : ∀ k (m : ℤ), q k = m / ((2 : ℚ) ^ k) →
    |m| ≤ ((2 : ℕ) ^ k) * (Nat.ceil |x| + 1)

/-- A dyadic read stream lying below the real parameter, with deficit at most `2⁻ᵏ` and a
specified numerator magnitude bound. -/
structure DyadicLowerRead (x : ℝ) (q : ℕ → ℚ) : Prop where

  exact_form : ∀ k, ∃ m : ℤ, q k = m / ((2 : ℚ) ^ k)

  lower : ∀ k, (q k : ℝ) ≤ x

  deficit : ∀ k, x - (q k : ℝ) ≤ (1 / 2 : ℝ) ^ k

  numerator_bound : ∀ k (m : ℤ), q k = m / ((2 : ℚ) ^ k) →
    |m| ≤ ((2 : ℕ) ^ k) * (Nat.ceil |x| + 1)

/-- The dyadic-read space allowance `2^k * (ceil |x| + 1) + k + 1`. -/
noncomputable def dyadicReadSpace (x : ℝ) (k : ℕ) : ℕ :=
  ((2 : ℕ) ^ k) * (Nat.ceil |x| + 1) + k + 1

/-- Records counts of ring, ceiling, logarithm, and digit operations. -/
structure RatCost where

  ringOps : ℕ

  ceilOps : ℕ

  logOps : ℕ

  digitOps : ℕ
  deriving Repr, DecidableEq

/-- The sum of the four operation counts in a rational cost ledger. -/
def RatCost.total (c : RatCost) : ℕ := c.ringOps + c.ceilOps + c.logOps + c.digitOps

/-- Rational expression programs built from literals, addition, multiplication, division,
ceiling, binary logarithm, and dyadic digit extraction. -/
inductive RatProgram where

  | lit (q : ℚ)

  | add (a b : RatProgram)

  | mul (a b : RatProgram)

  | div (a b : RatProgram)

  | ceil (a : RatProgram)

  | log2 (a : RatProgram)

  | digits (a : RatProgram) (k : ℕ)
  deriving Repr, DecidableEq

/-- Evaluates a rational program, interpreting logarithm through the absolute numerator and
digit extraction by downward dyadic rounding. -/
def RatProgram.eval : RatProgram → ℚ
  | .lit q => q
  | .add a b => RatProgram.eval a + RatProgram.eval b
  | .mul a b => RatProgram.eval a * RatProgram.eval b
  | .div a b => RatProgram.eval a / RatProgram.eval b
  | .ceil a => Rat.ceil (RatProgram.eval a)
  | .log2 a => (Nat.clog 2 (RatProgram.eval a).num.natAbs : ℚ)
  | .digits a k => ((⌊RatProgram.eval a * (2 : ℚ) ^ k⌋ : ℤ) : ℚ) / (2 : ℚ) ^ k

/-- Counts each operation category recursively, assigning zero cost to literal nodes. -/
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

/-- Counts nonliteral operation nodes in a rational program. -/
def RatProgram.nodes : RatProgram → ℕ
  | .lit _ => 0
  | .add a b => RatProgram.nodes a + RatProgram.nodes b + 1
  | .mul a b => RatProgram.nodes a + RatProgram.nodes b + 1
  | .div a b => RatProgram.nodes a + RatProgram.nodes b + 1
  | .ceil a => RatProgram.nodes a + 1
  | .log2 a => RatProgram.nodes a + 1
  | .digits a _ => RatProgram.nodes a + 1

/-- The total operation count multiplied by `(B + 2)²`. -/
def RatCost.bitTime (c : RatCost) (B : ℕ) : ℕ := c.total * (B + 2) * (B + 2)

/-- The space allowance `3 * (B + 2)`, independent of the operation counts. -/
def RatCost.bitSpace (_c : RatCost) (B : ℕ) : ℕ := 3 * (B + 2)

/-- Forms the rational table at precision `k`, negating entries whose sign flag is true. -/
def digitTable {L : ℕ} (q : Fin L → ℕ → ℚ) (sgn : Fin L → Bool) (k : ℕ) : Fin L → ℚ :=
  fun j => if sgn j then -(q j k) else q j k

/-- The digit-table space allowance `L * dyadicReadSpace x k`. -/
noncomputable def digitTableSpace (L : ℕ) (x : ℝ) (k : ℕ) : ℕ := L * dyadicReadSpace x k

/-- The digit-table time allowance `L * dyadicReadSpace x k`. -/
noncomputable def digitTableBitTime (L : ℕ) (x : ℝ) (k : ℕ) : ℕ := L * dyadicReadSpace x k

/-- Tests positivity of `eq - 2⁻ᵏ` and the time constraint `|tq| ≤ T` using rational arithmetic. -/
def scanCert (tq eq : ℚ) (T : ℕ) (k : ℕ) : Bool :=
  decide (0 < eq - 1 / ((2 : ℚ) ^ k) ∧ |tq| ≤ (T : ℚ))

/-- The rational tolerance value reduced by `2⁻ᵏ`. -/
def correctedBudget (eq : ℚ) (k : ℕ) : ℚ := eq - 1 / ((2 : ℚ) ^ k)

/-- Selects the first level up to `fuel` passing `scanCert`, with default `max 1 fuel`. -/
def scanPrecision (fuel : ℕ) (tq eq : ℕ → ℚ) (T : ℕ) : ℕ :=
  ((List.range (fuel + 1)).find? (fun k => scanCert (tq k) (eq k) T k)).getD (max 1 fuel)

/-- Records the number of scanned levels, parameter and digit reads, and bit-time and bit-space
allowances. -/
structure ScanLedger where

  scanned : ℕ

  paramReads : ℕ

  digitReads : ℕ

  bitTime : ℕ

  bitSpace : ℕ
  deriving Repr, DecidableEq

/-- Combines the dyadic-read and digit-table space allowances with a label-length term and
constant overhead. -/
noncomputable def scanRunBitLength (L : ℕ) (x : ℝ) (k : ℕ) : ℕ :=
  dyadicReadSpace x k + digitTableSpace L x k + 2 * (Nat.clog 2 (L + 1)) + 64

/-- Builds a scan resource ledger from the precision, label count, real size parameter, and
rational program. -/
noncomputable def scanLedger (L : ℕ) (x : ℝ) (k : ℕ) (prog : RatProgram) : ScanLedger :=
  let ops := (RatProgram.cost prog).total
  let B := scanRunBitLength L x k
  { scanned := k + 1
    paramReads := 2 * (k + 1)
    digitReads := L * (k + 1)
    bitTime := (ops + L * (k + 1)) * (B + 2) * (B + 2)
    bitSpace := B + digitTableSpace L x k + 16 }

/-- The combined error expression `2 W² T² / n + n / 2^R` for simulation and bounded fair-bit
sampling. -/
noncomputable def fairBitBudget (W T R : ℕ) (n : ℕ) : ℝ :=
  2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (n : ℝ) + (n : ℝ) / ((2 : ℝ) ^ R)

/-- The real-valued lower-envelope expression `2 sqrt(2) W T / sqrt(2^R)`. -/
noncomputable def fairBitBudgetMin (W T R : ℕ) : ℝ :=
  2 * Real.sqrt 2 * (W : ℝ) * (T : ℝ) / Real.sqrt ((2 : ℝ) ^ R)

/-- The real balancing value `sqrt(2) W T sqrt(2^R)` for the two terms of `fairBitBudget`. -/
noncomputable def fairBitBudgetArgmin (W T R : ℕ) : ℝ :=
  Real.sqrt 2 * (W : ℝ) * (T : ℝ) * Real.sqrt ((2 : ℝ) ^ R)

/-- The positive integer obtained by rounding `fairBitBudgetArgmin` upward. -/
noncomputable def tightFairBitCount (W T R : ℕ) : ℕ :=
  max 1 (Nat.ceil (fairBitBudgetArgmin W T R))

/-- The binary ceiling logarithm of the natural ceiling of `(2 sqrt(2) W T / eps)²`. -/
noncomputable def tightFairBitFuel (W T : ℕ) (eps : ℚ) : ℕ :=
  Nat.clog 2 (Nat.ceil ((2 * Real.sqrt 2 * (W : ℝ) * (T : ℝ) / (eps : ℝ)) ^ 2))

/-- The synthesis gate allowance `128 * (m + 1)² * 4^m`. -/
def synthGateBudget (m : ℕ) : ℕ := 128 * (m + 1) ^ 2 * 4 ^ m

/-- The synthesis space allowance `m + (m + 1)`. -/
def synthSpaceBudget (m : ℕ) : ℕ := m + (m + 1)

/-- The gate allowance for `n` synthesis steps, equal to `n * synthGateBudget m`. -/
def protocolGateBudget (m n : ℕ) : ℕ := n * synthGateBudget m

/-- The protocol space allowance inherited from `synthSpaceBudget m`. -/
def protocolSpaceBudget (m : ℕ) : ℕ := synthSpaceBudget m

/-- The binary ceiling logarithm of `max 1 n`, used as a classical-space allowance. -/
def protocolClassicalSpace (n : ℕ) : ℕ := Nat.clog 2 (max 1 n)

/-- Multiplies a list of register matrices with the first list entry acting first, using
identity for the empty list. -/
noncomputable def unitaryProduct {m : ℕ} :
    List (Matrix (Reg m) (Reg m) ℂ) → Matrix (Reg m) (Reg m) ℂ
  | [] => 1
  | V :: U => unitaryProduct U * V

/-- The even repetition allowance `2 * (clog₂(ceil(1 / delta)) + 1)`. -/
noncomputable def postSelectAmplify (delta : ℝ) : ℕ :=
  2 * (Nat.clog 2 (Nat.ceil (1 / delta)) + 1)

/-- The qDRIFT count expression `max 1 (ceil(2 lam² t² / eps))` in the setting of
[Campbell2019]. -/
noncomputable def tableIQdriftCount (lam t eps : ℝ) : ℕ :=
  max 1 (Nat.ceil (2 * lam ^ 2 * t ^ 2 / eps))

/-- The natural ceiling of `133 lam² / (deltaE² pf³)`. -/
noncomputable def tableIQdriftPeCount (lam deltaE pf : ℝ) : ℕ :=
  Nat.ceil (133 * lam ^ 2 / (deltaE ^ 2 * pf ^ 3))

/-- The natural ceiling of the comparison expression `69 L² bigLam^(3/2) / (deltaE^(3/2) pf²)`,
written using square roots. -/
noncomputable def tableITrotterBaseline (L : ℕ) (bigLam deltaE pf : ℝ) : ℕ :=
  Nat.ceil (69 * (L : ℝ) ^ 2 * bigLam * Real.sqrt bigLam /
    (deltaE * Real.sqrt deltaE * pf ^ 2))

/-- The error-budget expression `deltaE² * pf²`. -/
def tableIBudget (deltaE pf : ℝ) : ℝ := deltaE ^ 2 * pf ^ 2

/-- The binary ceiling logarithm of `ceil(1 / deltaE)`, increased by two. -/
noncomputable def peChainBits (deltaE : ℝ) : ℕ :=
  Nat.clog 2 (Nat.ceil (1 / deltaE)) + 2

/-- The odd repetition count `2 * (25 * clog₂(ceil(4 / pf))) + 1`. -/
noncomputable def peChainRounds (pf : ℝ) : ℕ :=
  2 * (25 * Nat.clog 2 (Nat.ceil (4 / pf))) + 1

/-- The evolution time `2^j` for the phase-estimation chain. -/
noncomputable def peChainTimes (j : ℕ) : ℝ := (2 : ℝ) ^ j

/-- The sum of squared chain evolution times through index `peChainBits deltaE`. -/
noncomputable def peChainTimeSq (deltaE : ℝ) : ℝ :=
  ∑ j : Fin (peChainBits deltaE + 1), (peChainTimes j.val) ^ 2

/-- Allocates `deltaE² pf³` proportionally to squared chain evolution time, divided by twice the
number of times and their squared-time sum. -/
noncomputable def peChainErrorShare (deltaE pf : ℝ) (j : ℕ) : ℝ :=
  deltaE ^ 2 * pf ^ 3 * (peChainTimes j) ^ 2 /
    (2 * (peChainBits deltaE + 1) * peChainTimeSq deltaE)

/-- The positive qDRIFT step count computed from a chain evolution time and its allocated error
share. -/
noncomputable def peChainQuerySteps (lam deltaE pf : ℝ) (j : ℕ) : ℕ :=
  max 1 (Nat.ceil (2 * lam ^ 2 * (peChainTimes j) ^ 2 / peChainErrorShare deltaE pf j))

/-- The chain repetition count multiplied by the sum of its qDRIFT step counts. -/
noncomputable def peChainTotalCount (lam deltaE pf : ℝ) : ℕ :=
  peChainRounds pf * ∑ j : Fin (peChainBits deltaE + 1), peChainQuerySteps lam deltaE pf j.val

/-- The binomial tail for strictly more than half of `R` trials failing. -/
def majorityFailure (q : ℝ) (R : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (R + 1),
    if R / 2 < i then (Nat.choose R i : ℝ) * q ^ i * (1 - q) ^ (R - i) else 0

end Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs
