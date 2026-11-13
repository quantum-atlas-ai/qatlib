/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftCore
import Qatlib.Concepts.DiamondQdrift.DigitEndpoint.DigitBudgetQDriftSubgoalCamp
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription

/-!
# qDRIFT parameters and implementation cost models

This module defines dyadic parameter oracles, finite precision searches, and resource ledgers
for qDRIFT compilation. It also supplies register embeddings, controlled operator maps, and
postselection witness data.

The count formulas `tableIQdriftCount` and `tableIQdriftPeCount` encode qDRIFT estimates from
[Campbell2019]; the phase estimation chain and synthesis parameters provide explicit objects for
subsequent validation and counterexamples.

## Main statements

* `realParamQdriftData`: rational parameter data with a bit resource ledger.
* `fairBitTightCert`: a rational simulation and rejection error certificate.
* `controlBlockMap`: a linear map on the two diagonal control blocks.
* `peChainTotalCount`: the total count of the defined phase estimation chain.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.DiamondQdrift.QuantizerCert
open Qatlib.Concepts.DiamondQdrift.SignedBridge

set_option autoImplicit false

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.RandCompile.EffectiveInput

namespace Qatlib.Concepts.DiamondQdrift.DigitEndpoint

open Matrix Qatlib.Concepts.DiamondQdrift.QuantizerCert Qatlib.Concepts.DiamondQdrift.SignedBridge
open scoped BigOperators Classical

/-- A rational oracle giving a denominator `2 ^ k` approximation to `x` within `2⁻ᵏ` at every
precision `k`. -/
def DyadicRealOracle (x : ℝ) (q : ℕ → ℚ) : Prop :=
  ∀ k : ℕ, ∃ m : ℤ, q k = m / ((2 : ℚ) ^ k) ∧
    |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k

/-- A nonnegative rational lower oracle with denominator `2 ^ k` and deficit at most `2⁻ᵏ` at
precision `k`. -/
def DyadicLowerOracle (x : ℝ) (q : ℕ → ℚ) : Prop :=
  ∀ k : ℕ, ∃ m : ℤ, q k = m / ((2 : ℚ) ^ k) ∧ 0 ≤ q k ∧
    (q k : ℝ) ≤ x ∧ x - (q k : ℝ) ≤ (1 / 2 : ℝ) ^ k

/-- The binary ceiling logarithm of the sum of the absolute numerator and denominator of a
rational number. -/
def ratBitLength (r : ℚ) : ℕ := Nat.clog 2 (r.num.natAbs + r.den)

/-- The binary operation cost model `(ratBitLength r + 2) * (ratBitLength s + 2)`. -/
def ratOpBits (r s : ℚ) : ℕ :=
  (ratBitLength r + 2) * (ratBitLength s + 2)

/-- The unary rational operation cost model `(ratBitLength r + 2)²`. -/
def ratUnaryBits (r : ℚ) : ℕ :=
  (ratBitLength r + 2) * (ratBitLength r + 2)

/-- The squared padded binary logarithm cost model for the natural input `n`. -/
def natLogBits (n : ℕ) : ℕ :=
  (Nat.clog 2 (n + 1) + 2) * (Nat.clog 2 (n + 1) + 2)

/-- The coefficient oracle column at precision `k`, negated exactly at the true sign flags. -/
def signedDigitColumn {L : ℕ} (q : Fin L → ℕ → ℚ) (sgn : Fin L → Bool)
    (k : ℕ) : Fin L → ℚ :=
  fun j => if sgn j then -(q j k) else q j k

/-- The dyadic integer weights obtained from the signed coefficient oracle column at precision
`k`. -/
def columnWeights {L : ℕ} (q : Fin L → ℕ → ℚ) (sgn : Fin L → Bool)
    (k : ℕ) : Fin L → ℕ :=
  dyadicWeights k (signedDigitColumn q sgn k)

/-- Test positivity of the reduced rational tolerance and the stated mass and dimension
precision budget at precision `k`. -/
def realParamCert (L : ℕ) (_tq eq : ℚ) (W : ℕ) (k : ℕ) : Bool :=
  decide (0 < eq - 1 / ((2 : ℚ) ^ k) ∧
    2 * (W : ℚ) / ((2 : ℚ) ^ k) ^ 2 + 4 * (L : ℚ) / ((2 : ℚ) ^ k) ^ 2
      ≤ (eq - 1 / ((2 : ℚ) ^ k)) / 4)

/-- Search precisions from zero through `fuel` for the first successful parameter certificate,
using `max 1 fuel` if none is found. -/
def realParamPrecision (fuel L : ℕ) (q : Fin L → ℕ → ℚ) (sgn : Fin L → Bool)
    (tq eq : ℕ → ℚ) : ℕ :=
  match (List.range (fuel + 1)).find?
    (fun k => realParamCert L (tq k) (eq k) (weightTotal (columnWeights q sgn k)) k) with
  | some k => k
  | none => max 1 fuel

/-- Resource counts for parameter reads, coefficient reads, arithmetic operations, ceilings,
logarithms, bit time, and bit space. -/
structure QdriftBitLedger where
  paramReads : ℕ
  digitReads : ℕ
  ringOps : ℕ
  ceilOps : ℕ
  logOps : ℕ
  bitTime : ℕ
  bitSpace : ℕ

/-- Stored rational time and tolerance, selected parameter precision, digit budget compilation
data, and a resource ledger. -/
structure RealParamQdriftRun (L : ℕ) where
  paramPrecision : ℕ
  storedTime : ℚ
  storedEps : ℚ
  data : DigitBudgetQDriftData L
  ledger : QdriftBitLedger

/-- The prescribed ring operation count for `L` coefficients and parameter search precision
`k₀`. -/
def qdriftRingOpCount (L k₀ : ℕ) : ℕ := (k₀ + 1) * (3 * L + 8) + 3 * L + 12

/-- The prescribed ceiling operation count for `L` coefficients and parameter search precision
`k₀`. -/
def qdriftCeilOpCount (L k₀ : ℕ) : ℕ := (k₀ + 1) * L + L + 2

/-- The prescribed logarithm operation count, equal to two. -/
def qdriftLogOpCount (_k₀ : ℕ) : ℕ := 2

/-- A padded bit length parameter computed from parameter approximants, coefficient columns,
table entries, and the selected precisions. -/
def qdriftRunBitLength {L : ℕ} (k₀ : ℕ) (r : DigitBudgetQDriftData L)
    (tq eq : ℕ → ℚ) (q : Fin L → ℕ → ℚ) : ℕ :=
  2 * ((Finset.range (k₀ + 1)).sup fun k =>
          max (ratBitLength (tq k)) (ratBitLength (eq k)) ⊔
        (Finset.univ.sup fun j => ratBitLength (q j k₀)) ⊔
        (Finset.univ.sup fun j => ratBitLength (q j r.precision)) ⊔
        (Finset.univ.sup fun j => ratBitLength (r.table j)))
    + 4 * (k₀ + r.precision) + 4 * Nat.clog 2 (L + 1) + 64

/-- The bit time cost model obtained by multiplying the total prescribed operation count by the
squared padded bit length. -/
def qdriftRunBitTime {L : ℕ} (k₀ : ℕ) (r : DigitBudgetQDriftData L)
    (tq eq : ℕ → ℚ) (q : Fin L → ℕ → ℚ) : ℕ :=
  let B := qdriftRunBitLength k₀ r tq eq q
  (qdriftRingOpCount L k₀ + qdriftCeilOpCount L k₀ + qdriftLogOpCount k₀) *
    (B + 2) * (B + 2)

/-- The bit space cost model combining parameter storage, coefficient digit storage, the padded
bit length, and a constant allowance. -/
def qdriftRunBitSpace {L : ℕ} (k₀ : ℕ) (r : DigitBudgetQDriftData L)
    (tq eq : ℕ → ℚ) (q : Fin L → ℕ → ℚ) : ℕ :=
  (Finset.range (k₀ + 1)).sup fun k => max (ratBitLength (tq k)) (ratBitLength (eq k))
  + ∑ j, ratBitLength (q j r.precision)
  + qdriftRunBitLength k₀ r tq eq q + 16

/-- Choose a parameter precision, reduce the rational tolerance by its dyadic uncertainty,
construct digit budget data, and attach the prescribed resource ledger. -/
def realParamQdriftData (fuel L : ℕ) (q : Fin L → ℕ → ℚ) (sgn : Fin L → Bool)
    (tq eq : ℕ → ℚ) : RealParamQdriftRun L :=
  let k := realParamPrecision fuel L q sgn tq eq
  let tQ := tq k
  let eQ := eq k - 1 / ((2 : ℚ) ^ k)
  let r := digitBudgetQDriftData q sgn tQ (eQ / 2)
  { paramPrecision := k
    storedTime := tQ
    storedEps := eQ
    data := r
    ledger :=
      { paramReads := 2 * (k + 1)
        digitReads := L * (k + 1) + L
        ringOps := qdriftRingOpCount L k
        ceilOps := qdriftCeilOpCount L k
        logOps := qdriftLogOpCount k
        bitTime := qdriftRunBitTime k r tq eq q
        bitSpace := qdriftRunBitSpace k r tq eq q } }

/-- Test that the step count is positive and the rational analytic plus rejection error
expression is at most `εQ`. -/
def fairBitTightCert (W : ℕ) (tQ εQ : ℚ) (R n : ℕ) : Bool :=
  decide (0 < n ∧
    4 * (W : ℚ) ^ 2 * tQ ^ 2 / (n : ℚ) + (n : ℚ) / ((2 : ℚ) ^ R) ≤ εQ)

/-- The explicit rejection fuel parameter formed from binary ceiling logarithms of the error,
weighted time, and total weight. -/
def fairBitTightFuel (W : ℕ) (tQ εQ : ℚ) : ℕ :=
  4 + 2 * Nat.clog 2 (Nat.ceil (64 / εQ))
    + 2 * Nat.clog 2 (Nat.ceil ((W : ℚ) ^ 2 * tQ ^ 2 / εQ + 1))
    + Nat.clog 2 (max 1 W)

/-- Search for the first step count satisfying `fairBitTightCert` up to the search fuel, with
fallback `max 1 fuel`. -/
def fairBitTightSteps (W : ℕ) (tQ εQ : ℚ) (R fuel : ℕ) : ℕ :=
  match (List.range (fuel + 1)).find? (fun n => fairBitTightCert W tQ εQ R n) with
  | some n => n
  | none => max 1 fuel

/-- Interpret an `m` bit register as a natural number with the first coordinate most
significant. -/
def regIdx {m : ℕ} (z : Reg m) : ℕ :=
  ∑ i, (if z i then (2 : ℕ) ^ (m - 1 - i.val) else 0)

/-- Embed a `D` dimensional operator into `m` bit registers, using the identity on the remaining
basis indices. -/
noncomputable def regEmbed {D m : ℕ} (_hD : D ≤ 2 ^ m) (A : Operator D) :
    Matrix (Reg m) (Reg m) ℂ :=
  Matrix.of fun z w =>
    if hz : regIdx z < D ∧ regIdx w < D then A ⟨regIdx z, hz.1⟩ ⟨regIdx w, hz.2⟩
    else if regIdx z = regIdx w then 1 else 0

/-- The binary ceiling logarithm of `max 1 D`, used as the system wire count. -/
def systemWires (D : ℕ) : ℕ := Nat.clog 2 (max 1 D)

/-- The explicit natural valued expression used as a proposed exponential synthesis gate bound. -/
noncomputable def expSynthGateBound (m : ℕ) (θ η : ℝ) : ℕ :=
  (2 ^ m) ^ 4 * (Nat.ceil |θ| + 2) ^ 2 * (Nat.ceil (1 / η) + 2) ^ 11 + 64

/-- The matrix of a finite gate code word, formed as the reversed product of its gate matrices. -/
noncomputable def fixedGateWordMatrix (n : ℕ) (W : List FiniteGateCode) :
    Matrix (Reg n) (Reg n) ℂ := (W.map (finiteCodeMatrix n)).reverse.prod

/-- The computational basis projector selected by Boolean control `b`. -/
noncomputable def controlProjector (b : Bool) : Operator 2 :=
  outerProduct (Ket (if b then 1 else 0))

/-- The operator with identity on the false control block and `U` on the true control block. -/
noncomputable def controlledOperator {D : ℕ} (U : Operator D) : Operator (2 * D) :=
  (TensorGate (controlProjector false) 1 + TensorGate (controlProjector true) U).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- The operator with zero on the false control block and `K` on the true control block. -/
noncomputable def dilatedTerm {D : ℕ} (K : Operator D) : Operator (2 * D) :=
  (TensorGate (controlProjector true) K).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- Map a Boolean control to basis index zero or one. -/
def controlIdx (b : Bool) : Fin 2 := if b then 1 else 0

/-- Extract the diagonal operator block selected by the Boolean control as a complex linear map. -/
noncomputable def controlBlockLinear {D : ℕ} (b : Bool) :
    Operator (2 * D) →ₗ[ℂ] Operator D where
  toFun Y := Matrix.of fun i j =>
    Y (finProdFinEquiv (controlIdx b, i)) (finProdFinEquiv (controlIdx b, j))
  map_add' Y Z := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply]
  map_smul' c Y := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, RingHom.id_apply]

/-- Insert an operator into the diagonal block selected by the control projector as a complex
linear map. -/
noncomputable def tensorControlProjector {D : ℕ} (b : Bool) :
    Operator D →ₗ[ℂ] Operator (2 * D) where
  toFun Z := (TensorGate (controlProjector b) Z).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm
  map_add' Y Z := by
    ext a c
    simp only [Matrix.submatrix_apply, TensorGate, Matrix.kronecker_add,
      Matrix.add_apply]
  map_smul' c Y := by
    ext a b
    simp only [Matrix.submatrix_apply, TensorGate, Matrix.kroneckerMap_apply,
      Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Preserve the false diagonal control block and apply `Λ` to the true diagonal block, with
both off diagonal blocks zero. -/
noncomputable def controlBlockMap {D : ℕ} (Λ : Operator D →ₗ[ℂ] Operator D) :
    Operator (2 * D) →ₗ[ℂ] Operator (2 * D) :=
  (tensorControlProjector (D := D) false).comp (controlBlockLinear false) +
    (tensorControlProjector true).comp (Λ.comp (controlBlockLinear true))

/-- The projector onto computational basis state zero in dimension two. -/
noncomputable def witnessProjectorTerm : Operator 2 := outerProduct (Ket 0)

/-- The two component vector whose entries are `1 / sqrt 2`. -/
noncomputable def plusState : QState (Fin 2) := fun _ => Complex.ofReal ((Real.sqrt 2)⁻¹)

/-- The tensor product of two plus state projectors, indexed as an operator of dimension four. -/
noncomputable def noFreeLunchWitness : Operator (2 * 2) :=
  (TensorGate (outerProduct plusState) (outerProduct plusState)).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- The compressed output `P * Φ X * P` of the linear map `Φ`. -/
noncomputable def selectiveOutput {D : ℕ} (Φ : Operator D →ₗ[ℂ] Operator D)
    (P : Operator D) (X : Operator D) : Operator D := P * Φ X * P

/-- The real part of the trace of the selective output. -/
noncomputable def selectiveMass {D : ℕ} (Φ : Operator D →ₗ[ℂ] Operator D)
    (P : Operator D) (X : Operator D) : ℝ := (Matrix.trace (selectiveOutput Φ P X)).re

/-- Scale the selective output by the inverse of its real trace mass, using the field inverse
also when that mass is zero. -/
noncomputable def conditionalOutput {D : ℕ} (Φ : Operator D →ₗ[ℂ] Operator D)
    (P : Operator D) (X : Operator D) : Operator D :=
  Complex.ofReal (selectiveMass Φ P X)⁻¹ • selectiveOutput Φ P X

/-- The operator is Hermitian and its quadratic form has nonnegative real part on every vector. -/
def IsPSDOperator {D : ℕ} (X : Operator D) : Prop :=
  X.IsHermitian ∧ ∀ v : QState (Fin D), 0 ≤ (Inner v (X *ᵥ v)).re

/-- The linear perturbation adding `2 * δ * ρ 2 2` times the basis one projector to `ρ`. -/
noncomputable def postSelectWitnessPerturb (δ : ℝ) : Operator 3 →ₗ[ℂ] Operator 3 where
  toFun ρ := ρ + (Complex.ofReal (2 * δ) * ρ 2 2) • outerProduct (Ket 1)
  map_add' := by
    intro Y Z
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul, outerProduct]
    ring
  map_smul' := by
    intro c Y
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul, Matrix.add_apply, outerProduct, RingHom.id_apply]
    ring

/-- The diagonal three dimensional operator with entries `p`, zero, and `1 - p`. -/
noncomputable def postSelectWitnessState (p : ℝ) : Operator 3 :=
  Matrix.of fun i j =>
    if i = 0 ∧ j = 0 then Complex.ofReal p else if i = 2 ∧ j = 2 then Complex.ofReal (1 - p) else 0

/-- The diagonal projector onto the first two computational basis states in dimension three. -/
def postSelectWitnessEvent : Operator 3 :=
  Matrix.of fun i j => if i.val < 2 ∧ i = j then (1 : ℂ) else 0

/-- The qDRIFT step count `max 1 (ceil (2 * lam² * t² / eps))` associated with [Campbell, Table
I][Campbell2019]. -/
noncomputable def tableIQdriftCount (lam t eps : ℝ) : ℕ :=
  max 1 (Nat.ceil (2 * lam ^ 2 * t ^ 2 / eps))

/-- The phase estimation count `ceil (133 * lam² / (deltaE² * pf³))` associated with [Campbell,
Table I][Campbell2019]. -/
noncomputable def tableIQdriftPeCount (lam deltaE pf : ℝ) : ℕ :=
  Nat.ceil (133 * lam ^ 2 / (deltaE ^ 2 * pf ^ 3))

/-- The natural ceiling of the stated Trotter phase estimation baseline expression with
coefficient `69` [Campbell2019]. -/
noncomputable def tableITrotterBaseline (L : ℕ) (bigLam deltaE pf : ℝ) : ℕ :=
  Nat.ceil (69 * (L : ℝ) ^ 2 * bigLam * Real.sqrt bigLam / (deltaE * Real.sqrt deltaE * pf ^ 2))

/-- The phase estimation precision parameter `Nat.clog 2 (Nat.ceil (1 / deltaE)) + 2`. -/
noncomputable def peChainBits (deltaE : ℝ) : ℕ :=
  Nat.clog 2 (Nat.ceil (1 / deltaE)) + 2

/-- The odd repetition count `50 * Nat.clog 2 (Nat.ceil (4 / pf)) + 1`. -/
noncomputable def peChainRounds (pf : ℝ) : ℕ :=
  2 * (25 * Nat.clog 2 (Nat.ceil (4 / pf))) + 1

/-- The phase estimation evolution time `2 ^ j`. -/
noncomputable def peChainTimes (j : ℕ) : ℝ := (2 : ℝ) ^ j

/-- The sum of squared evolution times over indices zero through `peChainBits deltaE`. -/
noncomputable def peChainTimeSq (deltaE : ℝ) : ℝ :=
  ∑ j : Fin (peChainBits deltaE + 1), (peChainTimes j.val) ^ 2

/-- Allocate the phase estimation error expression proportionally to the squared evolution time
at index `j`. -/
noncomputable def peChainErrorShare (deltaE pf : ℝ) (j : ℕ) : ℝ :=
  deltaE ^ 2 * pf ^ 3 * (peChainTimes j) ^ 2 /
    (2 * (peChainBits deltaE + 1) * peChainTimeSq deltaE)

/-- The positive qDRIFT step count determined by the evolution time and allocated error at index
`j`. -/
noncomputable def peChainQuerySteps (lam deltaE pf : ℝ) (j : ℕ) : ℕ :=
  max 1 (Nat.ceil (2 * lam ^ 2 * (peChainTimes j) ^ 2 /
    peChainErrorShare deltaE pf j))

/-- Multiply the repetition count by the sum of qDRIFT step counts across the defined phase
estimation chain. -/
noncomputable def peChainTotalCount (lam deltaE pf : ℝ) : ℕ :=
  peChainRounds pf * ∑ j : Fin (peChainBits deltaE + 1),
    peChainQuerySteps lam deltaE pf j.val

/-- The binomial probability expression for strictly more than half of `R` trials to fail with
parameter `q`. -/
def majorityFailure (q : ℝ) (R : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (R + 1),
    if R / 2 < i then (Nat.choose R i : ℝ) * q ^ i * (1 - q) ^ (R - i) else 0

end Qatlib.Concepts.DiamondQdrift.DigitEndpoint
