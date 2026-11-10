/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQDrift
import Qatlib.Concepts.DiamondQdrift.DigitEndpoint.DigitBudgetQDriftSubgoalCamp
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
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

def DyadicRealOracle (x : ℝ) (q : ℕ → ℚ) : Prop :=
  ∀ k : ℕ, ∃ m : ℤ, q k = m / ((2 : ℚ) ^ k) ∧
    |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k

def DyadicLowerOracle (x : ℝ) (q : ℕ → ℚ) : Prop :=
  ∀ k : ℕ, ∃ m : ℤ, q k = m / ((2 : ℚ) ^ k) ∧ 0 ≤ q k ∧
    (q k : ℝ) ≤ x ∧ x - (q k : ℝ) ≤ (1 / 2 : ℝ) ^ k

def ratBitLength (r : ℚ) : ℕ := Nat.clog 2 (r.num.natAbs + r.den)

def ratOpBits (r s : ℚ) : ℕ :=
  (ratBitLength r + 2) * (ratBitLength s + 2)

def ratUnaryBits (r : ℚ) : ℕ :=
  (ratBitLength r + 2) * (ratBitLength r + 2)

def natLogBits (n : ℕ) : ℕ :=
  (Nat.clog 2 (n + 1) + 2) * (Nat.clog 2 (n + 1) + 2)

def signedDigitColumn {L : ℕ} (q : Fin L → ℕ → ℚ) (sgn : Fin L → Bool)
    (k : ℕ) : Fin L → ℚ :=
  fun j => if sgn j then -(q j k) else q j k

def columnWeights {L : ℕ} (q : Fin L → ℕ → ℚ) (sgn : Fin L → Bool)
    (k : ℕ) : Fin L → ℕ :=
  dyadicWeights k (signedDigitColumn q sgn k)

def realParamCert (L : ℕ) (_tq eq : ℚ) (W : ℕ) (k : ℕ) : Bool :=
  decide (0 < eq - 1 / ((2 : ℚ) ^ k) ∧
    2 * (W : ℚ) / ((2 : ℚ) ^ k) ^ 2 + 4 * (L : ℚ) / ((2 : ℚ) ^ k) ^ 2
      ≤ (eq - 1 / ((2 : ℚ) ^ k)) / 4)

def realParamPrecision (fuel L : ℕ) (q : Fin L → ℕ → ℚ) (sgn : Fin L → Bool)
    (tq eq : ℕ → ℚ) : ℕ :=
  match (List.range (fuel + 1)).find?
    (fun k => realParamCert L (tq k) (eq k) (weightTotal (columnWeights q sgn k)) k) with
  | some k => k
  | none => max 1 fuel

structure QdriftBitLedger where
  paramReads : ℕ
  digitReads : ℕ
  ringOps : ℕ
  ceilOps : ℕ
  logOps : ℕ
  bitTime : ℕ
  bitSpace : ℕ

structure RealParamQdriftRun (L : ℕ) where
  paramPrecision : ℕ
  storedTime : ℚ
  storedEps : ℚ
  data : DigitBudgetQDriftData L
  ledger : QdriftBitLedger

def qdriftRingOpCount (L k₀ : ℕ) : ℕ := (k₀ + 1) * (3 * L + 8) + 3 * L + 12

def qdriftCeilOpCount (L k₀ : ℕ) : ℕ := (k₀ + 1) * L + L + 2

def qdriftLogOpCount (_k₀ : ℕ) : ℕ := 2

def qdriftRunBitLength {L : ℕ} (k₀ : ℕ) (r : DigitBudgetQDriftData L)
    (tq eq : ℕ → ℚ) (q : Fin L → ℕ → ℚ) : ℕ :=
  2 * ((Finset.range (k₀ + 1)).sup fun k =>
          max (ratBitLength (tq k)) (ratBitLength (eq k)) ⊔
        (Finset.univ.sup fun j => ratBitLength (q j k₀)) ⊔
        (Finset.univ.sup fun j => ratBitLength (q j r.precision)) ⊔
        (Finset.univ.sup fun j => ratBitLength (r.table j)))
    + 4 * (k₀ + r.precision) + 4 * Nat.clog 2 (L + 1) + 64

def qdriftRunBitTime {L : ℕ} (k₀ : ℕ) (r : DigitBudgetQDriftData L)
    (tq eq : ℕ → ℚ) (q : Fin L → ℕ → ℚ) : ℕ :=
  let B := qdriftRunBitLength k₀ r tq eq q
  (qdriftRingOpCount L k₀ + qdriftCeilOpCount L k₀ + qdriftLogOpCount k₀) *
    (B + 2) * (B + 2)

def qdriftRunBitSpace {L : ℕ} (k₀ : ℕ) (r : DigitBudgetQDriftData L)
    (tq eq : ℕ → ℚ) (q : Fin L → ℕ → ℚ) : ℕ :=
  (Finset.range (k₀ + 1)).sup fun k => max (ratBitLength (tq k)) (ratBitLength (eq k))
  + ∑ j, ratBitLength (q j r.precision)
  + qdriftRunBitLength k₀ r tq eq q + 16

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

def fairBitTightCert (W : ℕ) (tQ εQ : ℚ) (R n : ℕ) : Bool :=
  decide (0 < n ∧
    4 * (W : ℚ) ^ 2 * tQ ^ 2 / (n : ℚ) + (n : ℚ) / ((2 : ℚ) ^ R) ≤ εQ)

def fairBitTightFuel (W : ℕ) (tQ εQ : ℚ) : ℕ :=
  4 + 2 * Nat.clog 2 (Nat.ceil (64 / εQ))
    + 2 * Nat.clog 2 (Nat.ceil ((W : ℚ) ^ 2 * tQ ^ 2 / εQ + 1))
    + Nat.clog 2 (max 1 W)

def fairBitTightSteps (W : ℕ) (tQ εQ : ℚ) (R fuel : ℕ) : ℕ :=
  match (List.range (fuel + 1)).find? (fun n => fairBitTightCert W tQ εQ R n) with
  | some n => n
  | none => max 1 fuel

def regIdx {m : ℕ} (z : Reg m) : ℕ :=
  ∑ i, (if z i then (2 : ℕ) ^ (m - 1 - i.val) else 0)

noncomputable def regEmbed {D m : ℕ} (_hD : D ≤ 2 ^ m) (A : Operator D) :
    Matrix (Reg m) (Reg m) ℂ :=
  Matrix.of fun z w =>
    if hz : regIdx z < D ∧ regIdx w < D then A ⟨regIdx z, hz.1⟩ ⟨regIdx w, hz.2⟩
    else if regIdx z = regIdx w then 1 else 0

def systemWires (D : ℕ) : ℕ := Nat.clog 2 (max 1 D)

noncomputable def expSynthGateBound (m : ℕ) (θ η : ℝ) : ℕ :=
  (2 ^ m) ^ 4 * (Nat.ceil |θ| + 2) ^ 2 * (Nat.ceil (1 / η) + 2) ^ 11 + 64

noncomputable def fixedGateWordMatrix (n : ℕ) (W : List FiniteGateCode) :
    Matrix (Reg n) (Reg n) ℂ := (W.map (finiteCodeMatrix n)).reverse.prod

noncomputable def controlProjector (b : Bool) : Operator 2 :=
  outerProduct (Ket (if b then 1 else 0))

noncomputable def controlledOperator {D : ℕ} (U : Operator D) : Operator (2 * D) :=
  (TensorGate (controlProjector false) 1 + TensorGate (controlProjector true) U).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

noncomputable def dilatedTerm {D : ℕ} (K : Operator D) : Operator (2 * D) :=
  (TensorGate (controlProjector true) K).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

def controlIdx (b : Bool) : Fin 2 := if b then 1 else 0

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

noncomputable def controlBlockMap {D : ℕ} (Λ : Operator D →ₗ[ℂ] Operator D) :
    Operator (2 * D) →ₗ[ℂ] Operator (2 * D) :=
  (tensorControlProjector (D := D) false).comp (controlBlockLinear false) +
    (tensorControlProjector true).comp (Λ.comp (controlBlockLinear true))

noncomputable def witnessProjectorTerm : Operator 2 := outerProduct (Ket 0)

noncomputable def plusState : QState (Fin 2) := fun _ => Complex.ofReal ((Real.sqrt 2)⁻¹)

noncomputable def noFreeLunchWitness : Operator (2 * 2) :=
  (TensorGate (outerProduct plusState) (outerProduct plusState)).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

noncomputable def selectiveOutput {D : ℕ} (Φ : Operator D →ₗ[ℂ] Operator D)
    (P : Operator D) (X : Operator D) : Operator D := P * Φ X * P

noncomputable def selectiveMass {D : ℕ} (Φ : Operator D →ₗ[ℂ] Operator D)
    (P : Operator D) (X : Operator D) : ℝ := (Matrix.trace (selectiveOutput Φ P X)).re

noncomputable def conditionalOutput {D : ℕ} (Φ : Operator D →ₗ[ℂ] Operator D)
    (P : Operator D) (X : Operator D) : Operator D :=
  Complex.ofReal (selectiveMass Φ P X)⁻¹ • selectiveOutput Φ P X

def IsPSDOperator {D : ℕ} (X : Operator D) : Prop :=
  X.IsHermitian ∧ ∀ v : QState (Fin D), 0 ≤ (Inner v (X *ᵥ v)).re

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

noncomputable def postSelectWitnessState (p : ℝ) : Operator 3 :=
  Matrix.of fun i j =>
    if i = 0 ∧ j = 0 then Complex.ofReal p else if i = 2 ∧ j = 2 then Complex.ofReal (1 - p) else 0

def postSelectWitnessEvent : Operator 3 :=
  Matrix.of fun i j => if i.val < 2 ∧ i = j then (1 : ℂ) else 0

noncomputable def tableIQdriftCount (lam t eps : ℝ) : ℕ :=
  max 1 (Nat.ceil (2 * lam ^ 2 * t ^ 2 / eps))

noncomputable def tableIQdriftPeCount (lam deltaE pf : ℝ) : ℕ :=
  Nat.ceil (133 * lam ^ 2 / (deltaE ^ 2 * pf ^ 3))

noncomputable def tableITrotterBaseline (L : ℕ) (bigLam deltaE pf : ℝ) : ℕ :=
  Nat.ceil (69 * (L : ℝ) ^ 2 * bigLam * Real.sqrt bigLam / (deltaE * Real.sqrt deltaE * pf ^ 2))

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
  max 1 (Nat.ceil (2 * lam ^ 2 * (peChainTimes j) ^ 2 /
    peChainErrorShare deltaE pf j))

noncomputable def peChainTotalCount (lam deltaE pf : ℝ) : ℕ :=
  peChainRounds pf * ∑ j : Fin (peChainBits deltaE + 1),
    peChainQuerySteps lam deltaE pf j.val

def majorityFailure (q : ℝ) (R : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (R + 1),
    if R / 2 < i then (Nat.choose R i : ℝ) * q ^ i * (1 - q) ^ (R - i) else 0

end Qatlib.Concepts.DiamondQdrift.DigitEndpoint
