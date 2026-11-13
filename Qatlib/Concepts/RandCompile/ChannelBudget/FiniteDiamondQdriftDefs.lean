/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftCore
import Qatlib.Concepts.RandCompile.ChannelBudget.FairBitQDriftConsumers
import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis

/-!
# Finite qDRIFT input and postselection definitions

This module defines rational parameter streams, finite precision searches, and resource ledgers
for qDRIFT simulation in the setting of [Campbell2019]. `QdriftInputRun` stores the selected
inputs and costs, while `tightCountCertified` tests a combined simulation and fair-bit error
inequality.

Controlled operators, selective outputs, and explicit witness matrices support later channel and
postselection estimates. The phase-estimation definitions record concrete evolution times, error
shares, and count expressions.

## Main statements

* `qdriftInputRun`: assemble a finite input run from rational approximation streams.
* `ctrlBlockMap`: apply a linear map to one diagonal control block.
* `postSelectedQdriftMap`: form the exact qDRIFT map for the weighted importance law.

## References

* [Campbell, 2019][Campbell2019]
* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Concepts.SchattenDiamond.DiamondNorm
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.FairBitSampling

set_option autoImplicit false

namespace Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs

open Matrix Qatlib
open scoped BigOperators Classical ENNReal Matrix.Norms.L2Operator

/-- A rational approximation stream whose error at level `k` is at most `2⁻ᵏ`. -/
def RelParamRead (x : ℝ) (q : ℕ → ℚ) : Prop :=
  ∀ k : ℕ, |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k

/-- A rational approximation stream lying below `x` with error at most `2⁻ᵏ` at level `k`. -/
def RelLowerParamRead (x : ℝ) (q : ℕ → ℚ) : Prop :=
  ∀ k : ℕ, (q k : ℝ) ≤ x ∧ |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k

/-- The rational tolerance estimate at level `k`, reduced by `2⁻ᵏ`. -/
def epsBudget (q : ℕ → ℚ) (k : ℕ) : ℚ := q k - (1 / 2 : ℚ) ^ k

/-- Tests whether the corrected tolerance `epsBudget q k` is positive. -/
def epsCertified (q : ℕ → ℚ) (k : ℕ) : Bool := decide (0 < epsBudget q k)

/-- Returns the first level in `0, …, fuel` satisfying the Boolean certificate, if one exists. -/
def precScan (cert : ℕ → Bool) (fuel : ℕ) : Option ℕ :=
  (List.range (fuel + 1)).find? cert

/-- Selects the first certified level up to `fuel`, using `fuel` when the search fails. -/
def scanPrecision (fuel : ℕ) (cert : ℕ → Bool) : ℕ :=
  (precScan cert fuel).getD fuel

/-- The natural ceiling of `|tQ| + 2⁻ᵏ`, used as a time bound. -/
def timeBound (tQ : ℚ) (k : ℕ) : ℕ := Nat.ceil (max tQ (-tQ) + (1 / 2 : ℚ) ^ k)

/-- Tests the rational inequality `1 ≤ 2^(s + 1) * eQ`. -/
def successCertified (eQ : ℚ) (s : ℕ) : Bool :=
  decide ((1 : ℚ) ≤ (2 : ℚ) ^ (s + 1) * eQ)

/-- The natural ceiling of `1 / eQ`, used as fuel for the success-level search. -/
def successFuel (eQ : ℚ) : ℕ := Nat.ceil (1 / eQ)

/-- Searches for a level satisfying `successCertified`, with fuel `successFuel eQ`. -/
def successLevel (eQ : ℚ) : ℕ :=
  scanPrecision (successFuel eQ) (successCertified eQ)

/-- Rounds `c` downward to the dyadic grid of spacing `2⁻ᵏ`. -/
def ratTrunc (c : ℚ) (k : ℕ) : ℚ :=
  ((Rat.floor (c * ((2 : ℚ) ^ k)) : ℤ) : ℚ) / ((2 : ℚ) ^ k)

/-- States that the real number `x` lies between the rational endpoints `lo` and `hi`. -/
def RelBracket (x : ℝ) (lo hi : ℚ) : Prop :=
  (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)

/-- A stream of rational brackets containing `x`, with width at most `2⁻ᵏ` at level `k`. -/
def RelBracketStream (x : ℝ) (lo hi : ℕ → ℚ) : Prop :=
  ∀ k, RelBracket x (lo k) (hi k) ∧ (hi k - lo k : ℝ) ≤ (1 / 2 : ℝ) ^ k

/-- Rounds the lower bracket endpoint downward at dyadic precision `k + 1`. -/
def bracketRead (lo : ℚ) (k : ℕ) : ℚ := ratTrunc lo (k + 1)

/-- The bracket width plus the dyadic rounding allowance `2^(-(k + 1))`. -/
noncomputable def bracketError (lo hi : ℚ) (k : ℕ) : ℝ :=
  (hi : ℝ) - (lo : ℝ) + (1 / 2 : ℝ) ^ (k + 1)

/-- The rounded lower endpoint reduced by the bracket width and the dyadic rounding allowance. -/
def epsBudgetBracket (lo hi : ℚ) (k : ℕ) : ℚ :=
  bracketRead lo k - (hi - lo) - (1 / 2 : ℚ) ^ (k + 1)

/-- Tests positivity of the corrected bracket tolerance `epsBudgetBracket lo hi k`. -/
def epsCertifiedBracket (lo hi : ℚ) (k : ℕ) : Bool :=
  decide (0 < epsBudgetBracket lo hi k)

/-- The natural ceiling of the larger absolute value of the two bracket endpoints. -/
noncomputable def bracketTimeBound (lo hi : ℚ) : ℕ :=
  Nat.ceil (max |(lo : ℝ)| |(hi : ℝ)|)

/-- The binary ceiling logarithm of the sum of the absolute numerator and denominator of `r`. -/
def qdRatBits (r : ℚ) : ℕ := Nat.clog 2 (r.num.natAbs + r.den)

/-- The binary ceiling logarithm of `n + 1`. -/
def qdNatBits (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

/-- Records parameter reads, digit reads, arithmetic operations, and a bit-length allowance for
a qDRIFT input run. -/
structure QdriftRunCost where

  paramReads : ℕ

  digitReads : ℕ

  ringOps : ℕ

  ceilOps : ℕ

  logOps : ℕ

  bitLength : ℕ
  deriving DecidableEq

/-- The sum of ring, ceiling, and logarithm operation counts multiplied by the square of
`bitLength + 2`. -/
def QdriftRunCost.bitTime (c : QdriftRunCost) : ℕ :=
  (c.ringOps + c.ceilOps + c.logOps) * (c.bitLength + 2) * (c.bitLength + 2)

/-- The bit-space allowance `bitLength + digitReads * bitLength + 16`. -/
def QdriftRunCost.bitSpace (c : QdriftRunCost) : ℕ :=
  c.bitLength + c.digitReads * c.bitLength + 16

/-- A bit-length allowance combining rational reads through level `k`, the success level, and
the label count. -/
def runBitLength (k s : ℕ) (L : ℕ) (tq eq : ℕ → ℚ) : ℕ :=
  2 * ((Finset.range (k + 1)).sup fun k' =>
        max (qdRatBits (tq k')) (qdRatBits (eq k')))
    + 4 * (k + 1) + 4 * qdNatBits s + 4 * Nat.clog 2 (L + 1) + 64

/-- Builds the qDRIFT input cost ledger from the precision, success level, label count, and
parameter streams. -/
def inputRunCost (k s : ℕ) (L : ℕ) (tq eq : ℕ → ℚ) : QdriftRunCost :=
  { paramReads := 2 * (k + 1)
    digitReads := L * (k + 1) + L
    ringOps := 4 * (k + 1) + 2 + 2 * (s + 1)
    ceilOps := 2
    logOps := s + 1
    bitLength := runBitLength k s L tq eq }

/-- Stores the selected precision, rational parameter values, time bound, success level, and
cost ledger for a qDRIFT input run. -/
structure QdriftInputRun (L : ℕ) where

  precision : ℕ

  storedTime : ℚ

  storedEps : ℚ

  timeBound : ℕ

  successLevel : ℕ

  cost : QdriftRunCost

/-- Selects a tolerance precision and success level, then assembles the stored qDRIFT parameters
and cost ledger. -/
def qdriftInputRun (fuel : ℕ) (L : ℕ) (tq eq : ℕ → ℚ) : QdriftInputRun L :=
  let k := scanPrecision fuel (epsCertified eq)
  let eQ := epsBudget eq k
  let s := successLevel eQ
  { precision := k
    storedTime := tq k
    storedEps := eQ
    timeBound := timeBound (tq k) k
    successLevel := s
    cost := inputRunCost k s L tq eq }

/-- Tests positivity of `n` and the rational inequality obtained by clearing denominators in the
combined simulation and fair-bit budget. -/
def tightCountCertified (W T : ℕ) (eQ : ℚ) (R n : ℕ) : Bool :=
  decide (0 < n ∧
    2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 * ((2 : ℚ) ^ R) + (n : ℚ) ^ 2
      ≤ eQ * (n : ℚ) * ((2 : ℚ) ^ R))

/-- The search allowance `ceil(4 W² T² / eQ) + 2` for selecting a step count. -/
def tightCountFuel (W T : ℕ) (eQ : ℚ) : ℕ := Nat.ceil (4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ) + 2

/-- Searches for a step count satisfying `tightCountCertified` within `tightCountFuel`. -/
def tightCount (W T : ℕ) (eQ : ℚ) (R : ℕ) : ℕ :=
  scanPrecision (tightCountFuel W T eQ) (tightCountCertified W T eQ R)

/-- The natural ceiling of `2 W² T² / eQ`, used as the source step count. -/
def sourceTightCount (W T : ℕ) (eQ : ℚ) : ℕ :=
  Nat.ceil (2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ)

/-- The wire allowance `Nat.log2 (max 1 D) + 1` for a system of dimension `D`. -/
def systemWires (D : ℕ) : ℕ := Nat.log2 (max 1 D) + 1

/-- Interprets a Boolean register as a binary natural number, with the first wire most
significant. -/
def regIndex {m : ℕ} (z : Reg m) : ℕ :=
  ∑ i, (if z i then (2 : ℕ) ^ (m - 1 - i.val) else 0)

/-- Embeds `A` into the register basis on indices below `D` and uses the identity on the
remaining indices. -/
noncomputable def embedOperator {D m : ℕ} (_hD : D ≤ 2 ^ m) (A : Operator D) :
    Matrix (Reg m) (Reg m) ℂ :=
  Matrix.of fun z w =>
    if hz : regIndex z < D ∧ regIndex w < D then A ⟨regIndex z, hz.1⟩ ⟨regIndex w, hz.2⟩
    else if regIndex z = regIndex w then 1 else 0

/-- The synthesis gate allowance `128 * (m + 1)² * 4^m`. -/
def synthGateBudget (m : ℕ) : ℕ := 128 * (m + 1) ^ 2 * 4 ^ m

/-- The synthesis space allowance `m + (m + 1)`. -/
def synthSpaceBudget (m : ℕ) : ℕ := m + (m + 1)

/-- Extracts the control-row-zero, control-column-one block of `M`. -/
noncomputable def ctrlCrossBlock {D : ℕ} (M : Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun i j => M (0, i) (1, j)

/-- Extracts the control-one diagonal block of `M`. -/
noncomputable def ctrlDiagBlock1 {D : ℕ} (M : Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun i j => M (1, i) (1, j)

/-- Preserves the control-zero diagonal block, applies `Λ` to the control-one diagonal block,
and sets cross blocks to zero. -/
noncomputable def ctrlBlockMapIdx {D : ℕ} (Λ : Operator D →ₗ[ℂ] Operator D)
    (M : Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ) :
    Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ :=
  Matrix.of fun z w =>
    if z.1 = 0 ∧ w.1 = 0 then M z w
    else if z.1 = 1 ∧ w.1 = 1 then (Λ (ctrlDiagBlock1 M)) z.2 w.2
    else 0

/-- The diagonal matrix with entries one in the control-zero sector and the corresponding
diagonal entries of `U` in the control-one sector. -/
noncomputable def ctrlOperatorIdx {D : ℕ} (U : Operator D) :
    Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ :=
  Matrix.of fun z w =>
    if w = z then (if z.1 = 0 then (if z.2 = w.2 then 1 else 0) else U z.2 w.2)
    else 0

/-- The block diagonal matrix with identity on the control-zero block and `U` on the control-one
block. -/
noncomputable def ctrlOperatorBlk {D : ℕ} (U : Operator D) :
    Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ :=
  Matrix.blockDiagonal (fun b => if b = 0 then 1 else U)

/-- The block diagonal matrix with zero on the control-zero block and `K` on the control-one
block. -/
noncomputable def dilatedTermBlk {D : ℕ} (K : Operator D) :
    Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ :=
  Matrix.blockDiagonal (fun b => if b = 0 then 0 else K)

/-- The constant four-by-four matrix with every entry equal to the fourth power of `1 / sqrt 2`. -/
noncomputable def coherentWitness : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun _ _ => (Complex.ofReal ((Real.sqrt 2)⁻¹)) ^ 4

/-- The computational basis projector selected by the Boolean control value. -/
noncomputable def ctrlProjector (b : Bool) : Operator 2 :=
  outerProduct (Ket (if b then 1 else 0))

/-- The controlled operator acting as identity for control zero and as `U` for control one,
reindexed to `Fin (2 * D)`. -/
noncomputable def ctrlOperator {D : ℕ} (U : Operator D) : Operator (2 * D) :=
  (TensorGate (ctrlProjector false) 1 + TensorGate (ctrlProjector true) U).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- The operator `|1⟩⟨1| ⊗ K`, reindexed to dimension `2 * D`. -/
noncomputable def dilatedTerm {D : ℕ} (K : Operator D) : Operator (2 * D) :=
  (TensorGate (ctrlProjector true) K).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- The complex linear map extracting the diagonal control block selected by `b`. -/
noncomputable def ctrlBlockLinear {D : ℕ} (b : Bool) :
    Operator (2 * D) →ₗ[ℂ] Operator D where
  toFun Y := Matrix.of fun i j =>
    Y (finProdFinEquiv (if b then 1 else 0, i)) (finProdFinEquiv (if b then 1 else 0, j))
  map_add' Y Z := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply]
  map_smul' c Y := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, RingHom.id_apply]

/-- The complex linear map tensoring an operator with the control projector selected by `b`. -/
noncomputable def tensorCtrlProjector {D : ℕ} (b : Bool) :
    Operator D →ₗ[ℂ] Operator (2 * D) where
  toFun Z := (TensorGate (ctrlProjector b) Z).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm
  map_add' Y Z := by
    ext a c
    simp only [Matrix.submatrix_apply, TensorGate, Matrix.kronecker_add, Matrix.add_apply]
  map_smul' c Y := by
    ext a b
    simp only [Matrix.submatrix_apply, TensorGate, Matrix.kroneckerMap_apply,
      Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The linear map preserving the control-zero block, applying `Λ` to the control-one block, and
discarding cross blocks. -/
noncomputable def ctrlBlockMap {D : ℕ} (Λ : Operator D →ₗ[ℂ] Operator D) :
    Operator (2 * D) →ₗ[ℂ] Operator (2 * D) :=
  (tensorCtrlProjector (D := D) false).comp (ctrlBlockLinear false) +
    (tensorCtrlProjector true).comp (Λ.comp (ctrlBlockLinear true))

/-- The projector onto the first computational basis state of a two-dimensional system. -/
noncomputable def witnessTerm : Operator 2 := outerProduct (Ket 0)

/-- The two-dimensional vector with both amplitudes equal to `1 / sqrt 2`. -/
noncomputable def plusState : QState (Fin 2) := fun _ => Complex.ofReal ((Real.sqrt 2)⁻¹)

/-- The tensor product of two `plusState` projectors, reindexed to dimension four. -/
noncomputable def freeLunchWitness : Operator (2 * 2) :=
  (TensorGate (outerProduct plusState) (outerProduct plusState)).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- The compressed output `P * Φ X * P` of the linear map `Φ`. -/
noncomputable def selectiveOutput {D : ℕ} (Φ : Operator D →ₗ[ℂ] Operator D)
    (P : Operator D) (X : Operator D) : Operator D := P * Φ X * P

/-- The real part of the trace of `selectiveOutput Φ P X`. -/
noncomputable def selectiveMass {D : ℕ} (Φ : Operator D →ₗ[ℂ] Operator D)
    (P : Operator D) (X : Operator D) : ℝ := (Matrix.trace (selectiveOutput Φ P X)).re

/-- The selective output scaled by the inverse of its real trace. -/
noncomputable def conditionalOutput {D : ℕ} (Φ : Operator D →ₗ[ℂ] Operator D)
    (P : Operator D) (X : Operator D) : Operator D :=
  Complex.ofReal (selectiveMass Φ P X)⁻¹ • selectiveOutput Φ P X

/-- States that an operator is Hermitian and every quadratic form has nonnegative real part. -/
def IsPSDOperator {D : ℕ} (X : Operator D) : Prop :=
  X.IsHermitian ∧ ∀ v : QState (Fin D), 0 ≤ (Qatlib.Foundations.PureStateMath.Inner v (X *ᵥ v)).re

/-- States that an operator is self-adjoint and idempotent. -/
def IsEventProjection {D : ℕ} (P : Operator D) : Prop :=
  Pᴴ = P ∧ P * P = P

/-- Adds `2 * δ` times the bottom-right entry of the input to its middle computational basis
projector component. -/
noncomputable def postSelectPerturb (δ : ℝ) : Operator 3 →ₗ[ℂ] Operator 3 where
  toFun ρ := ρ + (Complex.ofReal (2 * δ) * ρ 2 2) • outerProduct (Ket 1)
  map_add' := by
    intro Y Z
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul, outerProduct]
    ring
  map_smul' := by
    intro c Y
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.add_apply,
      outerProduct, RingHom.id_apply]
    ring

/-- The diagonal three-dimensional operator with diagonal entries `p`, zero, and `1 - p`. -/
noncomputable def postSelectState (p : ℝ) : Operator 3 :=
  Matrix.of fun i j =>
    if i = 0 ∧ j = 0 then Complex.ofReal p
    else if i = 2 ∧ j = 2 then Complex.ofReal (1 - p) else 0

/-- The projector onto the first two computational basis states in dimension three. -/
def postSelectEvent : Operator 3 :=
  Matrix.of fun i j => if i.val < 2 ∧ i = j then (1 : ℂ) else 0

/-- The qDRIFT step-count expression `max 1 (ceil(2 lam² t² / eps))` associated with
[Campbell2019]. -/
noncomputable def tableQdriftCount (lam t eps : ℝ) : ℕ :=
  max 1 (Nat.ceil (2 * lam ^ 2 * t ^ 2 / eps))

/-- The natural ceiling of the phase-estimation count expression `133 lam² / (deltaE² pf³)`. -/
noncomputable def tableQdriftPeCount (lam deltaE pf : ℝ) : ℕ :=
  Nat.ceil (133 * lam ^ 2 / (deltaE ^ 2 * pf ^ 3))

/-- The natural ceiling of the comparison expression `69 L² bigLam^(3/2) / (deltaE^(3/2) pf²)`,
written using square roots. -/
noncomputable def tableTrotterBaseline (L : ℕ) (bigLam deltaE pf : ℝ) : ℕ :=
  Nat.ceil (69 * (L : ℝ) ^ 2 * bigLam * Real.sqrt bigLam /
    (deltaE * Real.sqrt deltaE * pf ^ 2))

/-- The binary ceiling logarithm of `ceil(1 / deltaE)`, increased by two. -/
noncomputable def peBits (deltaE : ℝ) : ℕ :=
  Nat.clog 2 (Nat.ceil (1 / deltaE)) + 2

/-- The odd repetition count `2 * ceil(70 / pf) + 1`. -/
noncomputable def peRounds (pf : ℝ) : ℕ := 2 * (Nat.ceil (70 / pf)) + 1

/-- The phase-estimation evolution time `2^j`. -/
noncomputable def peTimes (j : ℕ) : ℝ := (2 : ℝ) ^ j

/-- The sum of squared evolution times through index `peBits deltaE`. -/
noncomputable def peTimeSq (deltaE : ℝ) : ℝ :=
  ∑ j : Fin (peBits deltaE + 1), (peTimes j.val) ^ 2

/-- Allocates the error expression `deltaE² pf³` in proportion to squared evolution time, with
denominator `2 * (peBits deltaE + 1) * peTimeSq deltaE`. -/
noncomputable def peErrorShare (deltaE pf : ℝ) (j : ℕ) : ℝ :=
  deltaE ^ 2 * pf ^ 3 * (peTimes j) ^ 2 /
    (2 * (peBits deltaE + 1) * peTimeSq deltaE)

/-- The positive qDRIFT step count obtained from the evolution time and its allocated error
share. -/
noncomputable def peQuerySteps (lam deltaE pf : ℝ) (j : ℕ) : ℕ :=
  max 1 (Nat.ceil (2 * lam ^ 2 * (peTimes j) ^ 2 / peErrorShare deltaE pf j))

/-- The phase-estimation repetition count multiplied by the sum of its qDRIFT step counts. -/
noncomputable def peTotalCount (lam deltaE pf : ℝ) : ℕ :=
  peRounds pf * ∑ j : Fin (peBits deltaE + 1), peQuerySteps lam deltaE pf j.val

/-- The binomial tail summing outcomes with more than `R / 2` failures. -/
def majorityFailure (q : ℝ) (R : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (R + 1),
    if R / 2 < i then (Nat.choose R i : ℝ) * q ^ i * (1 - q) ^ (R - i) else 0

/-- Tests whether a randomized execution configuration belongs to the unfinished configuration
summand. -/
def fairQdriftExhausted {L : ℕ}
    (c : RandomizedExecution.Configuration (ℕ × ℕ) (Fin L × ℕ × ℕ)) : Bool :=
  match c with
  | .inl _ => false
  | .inr _ => true

/-- Reports exhaustion of the bounded fair-bit qDRIFT sampler, returning true when the total
weight is zero. -/
def fairQdriftPickReport {L : ℕ} (w : Fin L → ℕ) (j0 : Fin L) (R : ℕ)
    (ω : Fin R → Reg (Nat.clog 2 (weightTotal w))) : Bool :=
  if weightTotal w = 0 then true else
    fairQdriftExhausted
      (fairQdriftRawRun w (Nat.clog 2 (weightTotal w)) R ω (.inr (0, 0))).1

/-- The expression `(1 - weightTotal w / 2^clog₂(weightTotal w))^R` for exhaustion after `R`
rejection trials. -/
noncomputable def fairBitExhaustProb {L : ℕ} (w : Fin L → ℕ) (R : ℕ) : ℝ :=
  (1 - (weightTotal w : ℝ) / (2 ^ (Nat.clog 2 (weightTotal w)) : ℝ)) ^ R

/-- One minus the fair-bit exhaustion probability expression. -/
noncomputable def fairBitCleanProb {L : ℕ} (w : Fin L → ℕ) (R : ℕ) : ℝ :=
  1 - fairBitExhaustProb w R

/-- The `n`th power of the clean-sampling probability expression. -/
noncomputable def postSelectSuccessMass {L : ℕ} (w : Fin L → ℕ) (R n : ℕ) : ℝ :=
  fairBitCleanProb w R ^ n

/-- The exact qDRIFT map for the importance law induced by the positive total weight. -/
noncomputable def postSelectedQdriftMap {L D : ℕ} (w : Fin L → ℕ)
    (hW : 0 < weightTotal w) (n : ℕ) (K : Fin L → Operator D) (t : ℝ) :
    Operator D →ₗ[ℂ] Operator D :=
  exactQdriftMap (fairQdriftImportanceLaw w hW) K (weightTotal w : ℝ) t n

/-- The qDRIFT diamond-error budget expression `2 * (weightTotal w)² * t² / n`. -/
noncomputable def postSelectDiamondBudget {L : ℕ} (w : Fin L → ℕ) (n : ℕ) (t : ℝ) : ℝ :=
  2 * (weightTotal w : ℝ) ^ 2 * t ^ 2 / (n : ℝ)

end Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs
