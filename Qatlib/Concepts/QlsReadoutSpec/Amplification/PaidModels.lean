/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.PreconditioningParameters
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Concepts.ClassicalTape.TapeCompilation.ClockedTapeDecision
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

abbrev Space (H : Type) (r : ℕ) := H × Fin r

inductive Step (H : Type) (r : ℕ) where
  | known : Matrix (Space H r) (Space H r) ℂ → Step H r
  | call : ℕ → Finset (Fin r) → Bool → Step H r

abbrev Word (H : Type) (r : ℕ) := List (Step H r)

def calls {H : Type} {r : ℕ} (C : Word H r) (slot : ℕ) : ℕ :=
  C.countP (fun s =>  match s with | .call i _ _ =>  i=slot | _ =>  false)

def gateCount {H : Type} {r : ℕ} (C : Word H r) : ℕ :=
  C.countP (fun s =>  match s with | .known _ =>  true | _ =>  false)

def legal {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (slots : ℕ) (C : Word H r) : Prop :=
  ∀ s ∈ C, match s with
    | .known U =>  U ∈ Matrix.unitaryGroup _ ℂ
    | .call i _ _ =>  i < slots

def controlled {H : Type} [DecidableEq H] {r : ℕ}
    (U : Matrix H H ℂ) (T : Finset (Fin r)) : Matrix (Space H r) (Space H r) ℂ :=
  fun p t =>  if p.2=t.2 then
    if p.2 ∈ T then U p.1 t.1 else if p.1=t.1 then 1 else 0
  else 0

def wordMatrix {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (oracles : ℕ → Matrix H H ℂ) (C : Word H r) : Matrix (Space H r) (Space H r) ℂ :=
  (C.map (fun s =>  match s with
    | .known U =>  U
    | .call i T adj =>  controlled (if adj then (oracles i)ᴴ else oracles i) T)).reverse.prod

def wordAdjoint {H : Type} {r : ℕ} (C : Word H r) : Word H r :=
  C.reverse.map (fun s =>  match s with | .known U =>  .known Uᴴ | .call i T a =>  .call i T (!a))

def clean {H : Type} (r : ℕ) (hr : 0 < r) (ψ : QState H) : QState (Space H r) :=
  fun p =>  if p.2=⟨0,hr⟩ then ψ p.1 else 0

def normVec {H : Type} [Fintype H] (ψ : QState H) : ℝ := ‖toEuclidean_fromVec ψ‖
def normState {H : Type} [Fintype H] (ψ : QState H) : QState H :=
  ((normVec ψ : ℂ)⁻¹) • ψ

def run {H : Type} [Fintype H] [DecidableEq H] {r : ℕ} (hr : 0 < r)
    (oracles : ℕ → Matrix H H ℂ) (C : Word H r) (ω : QState H) : QState (Space H r) :=
  wordMatrix oracles C *ᵥ clean r hr ω

def outputBranch {H I : Type} [Fintype H] {r : ℕ}
    (R : Matrix H I ℂ) (ψ : QState (Space H r)) (k : Fin r) : QState I :=
  Rᴴ *ᵥ (fun h =>  ψ (h,k))

def outputMass {H I : Type} [Fintype H] [Fintype I] {r : ℕ}
    (R : Matrix H I ℂ) (T : Finset (Fin r)) (ψ : QState (Space H r)) : ℝ :=
  ∑ k ∈ T, (normVec (outputBranch R ψ k))^2

def pureDensity {I : Type} (ψ : QState I) : Matrix I I ℂ :=
  fun i j =>  ψ i * star (ψ j)

def outputDensity {H I : Type} [Fintype H] [Fintype I] {r : ℕ}
    (R : Matrix H I ℂ) (T : Finset (Fin r)) (ψ : QState (Space H r)) : Matrix I I ℂ :=
  ((outputMass R T ψ : ℂ)⁻¹) • ∑ k ∈ T, pureDensity (outputBranch R ψ k)

def stateGuarantee {H I : Type} [Fintype H] [Fintype I] [DecidableEq I] {r : ℕ}
    (R : Matrix H I ℂ) (T : Finset (Fin r)) (ψ : QState (Space H r))
    (target : QState I) (ε : ℝ) : Prop :=
  1/2 < outputMass R T ψ ∧
    Matrix.traceNorm (outputDensity R T ψ-pureDensity (normState target)) ≤ ε

def pairOracles {H : Type} (A B : Matrix H H ℂ) : ℕ → Matrix H H ℂ :=
  fun i =>  if i=0 then A else B

def projectedCorner {H I O : Type} [Fintype H] [Fintype I] {r : ℕ}
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (hr : 0 < r)
    (M : Matrix (Space H r) (Space H r) ℂ) : Matrix O I ℂ :=
  fun o i =>  ∑ h, ∑ t, star (L h o)*M (h,⟨0,hr⟩) (t,⟨0,hr⟩)*R t i

def logPrice (x : ℝ) : ℝ := Real.log (2+max 0 x)
def inversePrice (κ ε : ℝ) : ℝ := κ*logPrice (1/ε)
def normEstimationAPrice (κ α : ℝ) : ℝ :=
  κ*logPrice (1/Real.sqrt α)*logPrice (logPrice (1/Real.sqrt α))
def qlsAPrice (κ z ε : ℝ) : ℝ := κ*logPrice z*logPrice (logPrice z/ε)

def linearAccess {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (UA UB : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (ω : QState H) (b : QState O) (αA αInv : ℝ) : Prop :=
  0 < αA ∧ 0 < αInv ∧ 1 ≤ αA*αInv ∧
  ProjectedUnitaryEncoding ((αA : ℂ)⁻¹ • A) UA L R ∧
  UB ∈ Matrix.unitaryGroup H ℂ ∧ UB *ᵥ ω=L *ᵥ b ∧ Normalized b ∧
  (∃ z : QState I, A *ᵥ z=b) ∧ ‖matrixPseudoinverse A‖ ≤ αInv

def successProbability {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    (A : Matrix O I ℂ) (b : QState O) (αInv : ℝ) : ℝ :=
  (normVec (matrixPseudoinverse A *ᵥ b)/αInv)^2

def clockLegal {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ) : Prop :=
  (∀ j, IsOrthogonalProjector (P j)) ∧ P 0=0 ∧ P ⟨m,by omega⟩=1 ∧
  (∀ j k, j.val ≤ k.val → (P k-P j).PosSemidef) ∧
  IsOrthogonalProjector bad ∧ ∀ j, P j*bad=bad*P j

def potential {H : Type} [Fintype H] [DecidableEq H]
    (P bad : Matrix H H ℂ) : Matrix H H ℂ := 1-P*bad

def stageLegal {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (U : ℕ → Matrix H H ℂ) : Prop :=
  (∀ j : Fin (m+1), U j.val ∈ Matrix.unitaryGroup H ℂ) ∧
  ∀ j : Fin m, U (j.val+1)*P ⟨j.val,by omega⟩=P ⟨j.val,by omega⟩

def stageWord {H : Type} (j : ℕ) : Word H 1 := [.call j Finset.univ false]
def plainPrefix {H : Type} (j : ℕ) : Word H 1 :=
  (List.range (j+1)).map (fun k =>  .call k Finset.univ false)

def seedProjector {H : Type} (ω : QState H) : Matrix H H ℂ := pureDensity ω

def aaWord {H : Type} [Fintype H] [DecidableEq H]
    (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) (r : ℕ) : Word H 1 :=
  B ++ (List.replicate r
    ([.known (controlled (ReflectionAbout G) Finset.univ)] ++ wordAdjoint B ++
      [.known (controlled (ReflectionAbout (seedProjector ω)) Finset.univ)] ++ B ++
      [.known (-1)])).flatten

def nestedWord {H : Type} [Fintype H] [DecidableEq H]
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (ω : QState H)
    (rounds : ℕ → ℕ) : ℕ → Word H 1
  | 0 =>  stageWord 0
  | j+1 =>  aaWord (nestedWord P bad ω rounds j ++ stageWord (j+1))
      ω (potential (P (j+1)) bad) (rounds (j+1))

def extendClock {H : Type} (m : ℕ) (P : Fin (m+1) → Matrix H H ℂ) : ℕ → Matrix H H ℂ :=
  fun j =>  if h : j ≤ m then P ⟨j,by omega⟩ else P ⟨m,by omega⟩

def clockState {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (C : Word H 1) (ω : QState H) : QState H :=
  fun h =>  run (by omega) U C ω (h,0)

def preAmplitude {H : Type} [Fintype H] [DecidableEq H]
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (ω : QState H)
    (U : ℕ → Matrix H H ℂ) (rounds : ℕ → ℕ) (j : ℕ) : ℝ :=
  normVec (potential (P (j+1)) bad *ᵥ
    clockState U (nestedWord P bad ω rounds j ++ stageWord (j+1)) ω)

def postAmplitude {H : Type} [Fintype H] [DecidableEq H]
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (ω : QState H)
    (U : ℕ → Matrix H H ℂ) (rounds : ℕ → ℕ) (j : ℕ) : ℝ :=
  normVec (potential (P j) bad *ᵥ clockState U (nestedWord P bad ω rounds j) ω)

def gainLoss (ρ : ℕ) (a : ℝ) : ℝ :=
  if a=0 then 1 else Real.sin (ρ*Real.arcsin a)/(ρ*a)

def weightedCost {H : Type} {r : ℕ} (prices : ℕ → ℕ) (C : Word H r) : ℕ :=
  (C.map (fun s =>  match s with | .call j _ _ =>  prices j | _ =>  0)).sum

def quasinorm23 {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  (∑ j, (max 0 (w j)).rpow (2/3)).rpow (3/2)

def suffixWord {H : Type} (j k : ℕ) : Word H 1 :=
  (List.range (k-j)).map (fun i =>  .call (j+i+1) Finset.univ false)

def suffixState {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (j k : ℕ) (ψ : QState H) : QState H :=
  clockState U (suffixWord j k) ψ

def plainAmplitude {H : Type} [Fintype H] [DecidableEq H]
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (j : ℕ) : ℝ :=
  normVec (potential (P j) bad *ᵥ clockState U (plainPrefix j) ω)

def tunable {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ) : Prop :=
  α 0=1 ∧ ∀ j < m,
    0 ≤ α (j+1) ∧
    Real.sqrt (α (j+1))/3 ≤ (2*rs (j+1)+1)*preAmplitude P bad ω U rs j ∧
    ∀ s < rs (j+1), (2*s+1)*preAmplitude P bad ω U rs j < Real.sqrt (α (j+1))/3

def totalLoss {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (rs : ℕ → ℕ) : ℝ :=
  ∏ j : Fin m, gainLoss (2*rs (j.val+1)+1) (preAmplitude P bad ω U rs j.val)

def reverseThreshold {H : Type} [Fintype H] [DecidableEq H]
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (rs : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j=0 then 1 else if rs j=0 then 0 else
    9*((2*rs j+1 : ℕ) : ℝ)^2*(preAmplitude P bad ω U rs (j-1))^2

def blockFee (prices : ℕ → ℕ) (m a b : ℕ) : ℕ :=
  ∑ j : Fin (m+1), if a < j.val ∧ j.val ≤ min b m then prices j.val else 0

end Qatlib.Concepts.QlsReadoutSpec.Amplification
