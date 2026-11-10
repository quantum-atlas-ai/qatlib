/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQDrift
import Qatlib.Concepts.RandCompile.ChannelBudget.FairBitQDriftConsumers
import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis
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

def RelParamRead (x : ℝ) (q : ℕ → ℚ) : Prop :=
  ∀ k : ℕ, |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k

def RelLowerParamRead (x : ℝ) (q : ℕ → ℚ) : Prop :=
  ∀ k : ℕ, (q k : ℝ) ≤ x ∧ |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k

def epsBudget (q : ℕ → ℚ) (k : ℕ) : ℚ := q k - (1 / 2 : ℚ) ^ k

def epsCertified (q : ℕ → ℚ) (k : ℕ) : Bool := decide (0 < epsBudget q k)

def precScan (cert : ℕ → Bool) (fuel : ℕ) : Option ℕ :=
  (List.range (fuel + 1)).find? cert

def scanPrecision (fuel : ℕ) (cert : ℕ → Bool) : ℕ :=
  (precScan cert fuel).getD fuel

def timeBound (tQ : ℚ) (k : ℕ) : ℕ := Nat.ceil (max tQ (-tQ) + (1 / 2 : ℚ) ^ k)

def successCertified (eQ : ℚ) (s : ℕ) : Bool :=
  decide ((1 : ℚ) ≤ (2 : ℚ) ^ (s + 1) * eQ)

def successFuel (eQ : ℚ) : ℕ := Nat.ceil (1 / eQ)

def successLevel (eQ : ℚ) : ℕ :=
  scanPrecision (successFuel eQ) (successCertified eQ)

def ratTrunc (c : ℚ) (k : ℕ) : ℚ :=
  ((Rat.floor (c * ((2 : ℚ) ^ k)) : ℤ) : ℚ) / ((2 : ℚ) ^ k)

def RelBracket (x : ℝ) (lo hi : ℚ) : Prop :=
  (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)

def RelBracketStream (x : ℝ) (lo hi : ℕ → ℚ) : Prop :=
  ∀ k, RelBracket x (lo k) (hi k) ∧ (hi k - lo k : ℝ) ≤ (1 / 2 : ℝ) ^ k

def bracketRead (lo : ℚ) (k : ℕ) : ℚ := ratTrunc lo (k + 1)

noncomputable def bracketError (lo hi : ℚ) (k : ℕ) : ℝ :=
  (hi : ℝ) - (lo : ℝ) + (1 / 2 : ℝ) ^ (k + 1)

def epsBudgetBracket (lo hi : ℚ) (k : ℕ) : ℚ :=
  bracketRead lo k - (hi - lo) - (1 / 2 : ℚ) ^ (k + 1)

def epsCertifiedBracket (lo hi : ℚ) (k : ℕ) : Bool :=
  decide (0 < epsBudgetBracket lo hi k)

noncomputable def bracketTimeBound (lo hi : ℚ) : ℕ :=
  Nat.ceil (max |(lo : ℝ)| |(hi : ℝ)|)

def qdRatBits (r : ℚ) : ℕ := Nat.clog 2 (r.num.natAbs + r.den)

def qdNatBits (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

structure QdriftRunCost where

  paramReads : ℕ

  digitReads : ℕ

  ringOps : ℕ

  ceilOps : ℕ

  logOps : ℕ

  bitLength : ℕ
  deriving DecidableEq

def QdriftRunCost.bitTime (c : QdriftRunCost) : ℕ :=
  (c.ringOps + c.ceilOps + c.logOps) * (c.bitLength + 2) * (c.bitLength + 2)

def QdriftRunCost.bitSpace (c : QdriftRunCost) : ℕ :=
  c.bitLength + c.digitReads * c.bitLength + 16

def runBitLength (k s : ℕ) (L : ℕ) (tq eq : ℕ → ℚ) : ℕ :=
  2 * ((Finset.range (k + 1)).sup fun k' =>
        max (qdRatBits (tq k')) (qdRatBits (eq k')))
    + 4 * (k + 1) + 4 * qdNatBits s + 4 * Nat.clog 2 (L + 1) + 64

def inputRunCost (k s : ℕ) (L : ℕ) (tq eq : ℕ → ℚ) : QdriftRunCost :=
  { paramReads := 2 * (k + 1)
    digitReads := L * (k + 1) + L
    ringOps := 4 * (k + 1) + 2 + 2 * (s + 1)
    ceilOps := 2
    logOps := s + 1
    bitLength := runBitLength k s L tq eq }

structure QdriftInputRun (L : ℕ) where

  precision : ℕ

  storedTime : ℚ

  storedEps : ℚ

  timeBound : ℕ

  successLevel : ℕ

  cost : QdriftRunCost

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

def tightCountCertified (W T : ℕ) (eQ : ℚ) (R n : ℕ) : Bool :=
  decide (0 < n ∧
    2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 * ((2 : ℚ) ^ R) + (n : ℚ) ^ 2
      ≤ eQ * (n : ℚ) * ((2 : ℚ) ^ R))

def tightCountFuel (W T : ℕ) (eQ : ℚ) : ℕ := Nat.ceil (4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ) + 2

def tightCount (W T : ℕ) (eQ : ℚ) (R : ℕ) : ℕ :=
  scanPrecision (tightCountFuel W T eQ) (tightCountCertified W T eQ R)

def sourceTightCount (W T : ℕ) (eQ : ℚ) : ℕ :=
  Nat.ceil (2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ)

def systemWires (D : ℕ) : ℕ := Nat.log2 (max 1 D) + 1

def regIndex {m : ℕ} (z : Reg m) : ℕ :=
  ∑ i, (if z i then (2 : ℕ) ^ (m - 1 - i.val) else 0)

noncomputable def embedOperator {D m : ℕ} (_hD : D ≤ 2 ^ m) (A : Operator D) :
    Matrix (Reg m) (Reg m) ℂ :=
  Matrix.of fun z w =>
    if hz : regIndex z < D ∧ regIndex w < D then A ⟨regIndex z, hz.1⟩ ⟨regIndex w, hz.2⟩
    else if regIndex z = regIndex w then 1 else 0

def synthGateBudget (m : ℕ) : ℕ := 128 * (m + 1) ^ 2 * 4 ^ m

def synthSpaceBudget (m : ℕ) : ℕ := m + (m + 1)

noncomputable def ctrlCrossBlock {D : ℕ} (M : Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun i j => M (0, i) (1, j)

noncomputable def ctrlDiagBlock1 {D : ℕ} (M : Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun i j => M (1, i) (1, j)

noncomputable def ctrlBlockMapIdx {D : ℕ} (Λ : Operator D →ₗ[ℂ] Operator D)
    (M : Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ) :
    Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ :=
  Matrix.of fun z w =>
    if z.1 = 0 ∧ w.1 = 0 then M z w
    else if z.1 = 1 ∧ w.1 = 1 then (Λ (ctrlDiagBlock1 M)) z.2 w.2
    else 0

noncomputable def ctrlOperatorIdx {D : ℕ} (U : Operator D) :
    Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ :=
  Matrix.of fun z w =>
    if w = z then (if z.1 = 0 then (if z.2 = w.2 then 1 else 0) else U z.2 w.2)
    else 0

noncomputable def ctrlOperatorBlk {D : ℕ} (U : Operator D) :
    Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ :=
  Matrix.blockDiagonal (fun b => if b = 0 then 1 else U)

noncomputable def dilatedTermBlk {D : ℕ} (K : Operator D) :
    Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ :=
  Matrix.blockDiagonal (fun b => if b = 0 then 0 else K)

noncomputable def coherentWitness : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun _ _ => (Complex.ofReal ((Real.sqrt 2)⁻¹)) ^ 4

noncomputable def ctrlProjector (b : Bool) : Operator 2 :=
  outerProduct (Ket (if b then 1 else 0))

noncomputable def ctrlOperator {D : ℕ} (U : Operator D) : Operator (2 * D) :=
  (TensorGate (ctrlProjector false) 1 + TensorGate (ctrlProjector true) U).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

noncomputable def dilatedTerm {D : ℕ} (K : Operator D) : Operator (2 * D) :=
  (TensorGate (ctrlProjector true) K).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

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

noncomputable def ctrlBlockMap {D : ℕ} (Λ : Operator D →ₗ[ℂ] Operator D) :
    Operator (2 * D) →ₗ[ℂ] Operator (2 * D) :=
  (tensorCtrlProjector (D := D) false).comp (ctrlBlockLinear false) +
    (tensorCtrlProjector true).comp (Λ.comp (ctrlBlockLinear true))

noncomputable def witnessTerm : Operator 2 := outerProduct (Ket 0)

noncomputable def plusState : QState (Fin 2) := fun _ => Complex.ofReal ((Real.sqrt 2)⁻¹)

noncomputable def freeLunchWitness : Operator (2 * 2) :=
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
  X.IsHermitian ∧ ∀ v : QState (Fin D), 0 ≤ (Qatlib.Foundations.PureStateMath.Inner v (X *ᵥ v)).re

def IsEventProjection {D : ℕ} (P : Operator D) : Prop :=
  Pᴴ = P ∧ P * P = P

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

noncomputable def postSelectState (p : ℝ) : Operator 3 :=
  Matrix.of fun i j =>
    if i = 0 ∧ j = 0 then Complex.ofReal p
    else if i = 2 ∧ j = 2 then Complex.ofReal (1 - p) else 0

def postSelectEvent : Operator 3 :=
  Matrix.of fun i j => if i.val < 2 ∧ i = j then (1 : ℂ) else 0

noncomputable def tableQdriftCount (lam t eps : ℝ) : ℕ :=
  max 1 (Nat.ceil (2 * lam ^ 2 * t ^ 2 / eps))

noncomputable def tableQdriftPeCount (lam deltaE pf : ℝ) : ℕ :=
  Nat.ceil (133 * lam ^ 2 / (deltaE ^ 2 * pf ^ 3))

noncomputable def tableTrotterBaseline (L : ℕ) (bigLam deltaE pf : ℝ) : ℕ :=
  Nat.ceil (69 * (L : ℝ) ^ 2 * bigLam * Real.sqrt bigLam /
    (deltaE * Real.sqrt deltaE * pf ^ 2))

noncomputable def peBits (deltaE : ℝ) : ℕ :=
  Nat.clog 2 (Nat.ceil (1 / deltaE)) + 2

noncomputable def peRounds (pf : ℝ) : ℕ := 2 * (Nat.ceil (70 / pf)) + 1

noncomputable def peTimes (j : ℕ) : ℝ := (2 : ℝ) ^ j

noncomputable def peTimeSq (deltaE : ℝ) : ℝ :=
  ∑ j : Fin (peBits deltaE + 1), (peTimes j.val) ^ 2

noncomputable def peErrorShare (deltaE pf : ℝ) (j : ℕ) : ℝ :=
  deltaE ^ 2 * pf ^ 3 * (peTimes j) ^ 2 /
    (2 * (peBits deltaE + 1) * peTimeSq deltaE)

noncomputable def peQuerySteps (lam deltaE pf : ℝ) (j : ℕ) : ℕ :=
  max 1 (Nat.ceil (2 * lam ^ 2 * (peTimes j) ^ 2 / peErrorShare deltaE pf j))

noncomputable def peTotalCount (lam deltaE pf : ℝ) : ℕ :=
  peRounds pf * ∑ j : Fin (peBits deltaE + 1), peQuerySteps lam deltaE pf j.val

def majorityFailure (q : ℝ) (R : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (R + 1),
    if R / 2 < i then (Nat.choose R i : ℝ) * q ^ i * (1 - q) ^ (R - i) else 0

def fairQdriftExhausted {L : ℕ}
    (c : RandomizedExecution.Configuration (ℕ × ℕ) (Fin L × ℕ × ℕ)) : Bool :=
  match c with
  | .inl _ => false
  | .inr _ => true

def fairQdriftPickReport {L : ℕ} (w : Fin L → ℕ) (j0 : Fin L) (R : ℕ)
    (ω : Fin R → Reg (Nat.clog 2 (weightTotal w))) : Bool :=
  if weightTotal w = 0 then true else
    fairQdriftExhausted
      (fairQdriftRawRun w (Nat.clog 2 (weightTotal w)) R ω (.inr (0, 0))).1

noncomputable def fairBitExhaustProb {L : ℕ} (w : Fin L → ℕ) (R : ℕ) : ℝ :=
  (1 - (weightTotal w : ℝ) / (2 ^ (Nat.clog 2 (weightTotal w)) : ℝ)) ^ R

noncomputable def fairBitCleanProb {L : ℕ} (w : Fin L → ℕ) (R : ℕ) : ℝ :=
  1 - fairBitExhaustProb w R

noncomputable def postSelectSuccessMass {L : ℕ} (w : Fin L → ℕ) (R n : ℕ) : ℝ :=
  fairBitCleanProb w R ^ n

noncomputable def postSelectedQdriftMap {L D : ℕ} (w : Fin L → ℕ)
    (hW : 0 < weightTotal w) (n : ℕ) (K : Fin L → Operator D) (t : ℝ) :
    Operator D →ₗ[ℂ] Operator D :=
  exactQdriftMap (fairQdriftImportanceLaw w hW) K (weightTotal w : ℝ) t n

noncomputable def postSelectDiamondBudget {L : ℕ} (w : Fin L → ℕ) (n : ℕ) (t : ℝ) : ℝ :=
  2 * (weightTotal w : ℝ) ^ 2 * t ^ 2 / (n : ℝ)

end Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs
