/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.Postselection.RationalHHLNoiseRetry
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.QlsReadoutSpec.LowRankHHL
open Qatlib.Concepts.HhlAlgorithms.RationalProgram
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.HhlAlgorithms.Postselection
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

abbrev Space (D M : ℕ) := Fin M × (Bool × (Bool × Fin D))

def seedBits (d theta : ℚ) : ℕ := Nat.clog 2 (max 1 ⌈4/(d*theta)⌉₊)
def window (d theta : ℚ) : ℕ := 2 ^ seedBits d theta

def seedOfBits (d theta : ℚ) (x : Fin (seedBits d theta+1) → Bool) :
    Fin (2*window d theta) :=
  ⟨(∑ i, if x i then 2^i.val else 0) % (2*window d theta),
    Nat.mod_lt _ (by dsimp [window]; positivity)⟩

def depth (m : ℕ) (s : Fin (2*m)) : ℕ := if s.val<m then 0 else s.val-m

def inverseStep {I : Type} : PreparedStep I → PreparedStep I
  | .gate U => .gate Uᴴ
  | .dataForward => .dataBackward
  | .dataBackward => .dataForward
  | .prepareForward => .prepareBackward
  | .prepareBackward => .prepareForward

def inverseWord {I : Type} (cs : List (PreparedStep I)) : List (PreparedStep I) :=
  cs.reverse.map inverseStep

def dataForwardCalls {I : Type} (cs : List (PreparedStep I)) : ℕ :=
  cs.countP (fun s => match s with | .dataForward => true | _ => false)
def dataBackwardCalls {I : Type} (cs : List (PreparedStep I)) : ℕ :=
  cs.countP (fun s => match s with | .dataBackward => true | _ => false)
def inputForwardCalls {I : Type} (cs : List (PreparedStep I)) : ℕ :=
  cs.countP (fun s => match s with | .prepareForward => true | _ => false)
def inputBackwardCalls {I : Type} (cs : List (PreparedStep I)) : ℕ :=
  cs.countP (fun s => match s with | .prepareBackward => true | _ => false)

def core (D M bits : ℕ) (d : ℚ) : List (AdjointStep (Space D M)) :=
  adjointCircuit (countedQPEWord D M) ++
    [.gate (countedHHLLiftGate (rationalHHLFlag d bits))] ++ countedQPEWord D M

def base (D M bits : ℕ) (d : ℚ) : List (PreparedStep (Space D M)) :=
  preparedTrial (core D M bits d)

def source {D M : ℕ} (hM : 2≤M) (j : Fin D) : Space D M :=
  (⟨0,by omega⟩,(false,(false,j)))

def inputLift {D M : ℕ} (B : Operator D) : Matrix (Space D M) (Space D M) ℂ :=
  countedHHLLiftGate (countedHHLPrepMain B)

def amplified {I : Type} [Fintype I] [DecidableEq I]
    (cs : List (PreparedStep I)) (j : I) (S : Finset I) (k : ℕ) :
    List (PreparedStep I) :=
  (List.replicate k (cs ++ [.gate (ReflectionAbout (outerProduct (Ket j)))] ++
    inverseWord cs ++ [.gate (preparedMark S)])).flatten ++ cs

def output {D M : ℕ} (hM : 2≤M) (W B : Operator D) (j : Fin D)
    (d : ℚ) (bits k : ℕ) : QState (Space D M) :=
  evaluatePrepared (countedHHLOracleLift W) (inputLift B)
    (amplified (base D M bits d) (source hM j) (flagSuccessSet D M) k) *ᵥ
      Ket (source hM j)

def Trace (m : ℕ) : ℕ → Type
  | 0 => PUnit
  | r+1 => Fin (2*m) × Option (Trace m r)

instance traceFintype (m r : ℕ) : Fintype (Trace m r) := by
  induction r with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ r ih =>
      letI : Fintype (Trace m r) := ih
      exact inferInstanceAs (Fintype (Fin (2*m) × Option (Trace m r)))

def weight {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (out : Fin (2*m) → QState I) (S : Finset I) :
    (r : ℕ) → Trace m r → ℝ
  | 0, _ => 1
  | r+1, tr => (1/(2*m : ℝ)) *
      match tr.2 with
      | none => ProjectiveBranchMass (Projector S) true (out tr.1)
      | some tail => ProjectiveBranchMass (Projector S) false (out tr.1) *
          weight m out S r tail

def history {m : ℕ} : (r : ℕ) → Trace m r → List (Fin (2*m) × Bool)
  | 0, _ => []
  | r+1, tr => match tr.2 with
    | none => [(tr.1,true)]
    | some tail => (tr.1,false) :: history r tail

def selected {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (out : Fin (2*m) → QState I) (S : Finset I) :
    (r : ℕ) → Trace m r → Option (QState I)
  | 0, _ => none
  | r+1, tr => match tr.2 with
    | none => some (PostMeasure (out tr.1) S)
    | some tail => selected out S r tail

def totalData {I : Type} {m r : ℕ} (words : Fin (2*m) → List (PreparedStep I))
    (tr : Trace m r) : ℕ :=
  ((history r tr).map (fun z => preparedDataQueries (words z.1))).sum

def totalInput {I : Type} {m r : ℕ} (words : Fin (2*m) → List (PreparedStep I))
    (tr : Trace m r) : ℕ :=
  ((history r tr).map (fun z => preparedInputQueries (words z.1))).sum

def totalFixed {I : Type} {m r : ℕ} (words : Fin (2*m) → List (PreparedStep I))
    (tr : Trace m r) : ℕ :=
  ((history r tr).map (fun z => preparedFixedGates (words z.1))).sum

def FiniteComputedUnknownSuccess : Prop :=
  ∀ (D : ℕ) (eig : Fin D → ℝ) (V B W : Operator D) (j : Fin D)
    (d theta : ℚ) (k : ℕ),
    V∈Matrix.unitaryGroup (Fin D) ℂ → B∈Matrix.unitaryGroup (Fin D) ℂ →
    W∈Matrix.unitaryGroup (Fin D) ℂ → 0<d → d≤1/4 → 0<theta → theta≤1 →
    (∀ i, eig i=0 ∨ ((d : ℝ)≤|eig i| ∧ |eig i|≤1/4)) →
    (theta : ℝ)≤leastSquaresOverlap (continuousHHLMatrix eig V) (B*ᵥKet j) →
    ‖W-continuousHHLOracle eig V‖≤(numericHHLNoise d theta k : ℝ) →
    ∃ hM : 2≤numericHHLGrid d theta k,
    let M := numericHHLGrid d theta k
    let bits := numericHHLBits d theta k
    let m := window d theta
    let S := flagSuccessSet D M
    let cs := base D M bits d
    let A := evaluatePrepared (countedHHLOracleLift W) (inputLift B) cs
    let words := fun s : Fin (2*m) => amplified cs (source hM j) S (depth m s)
    let out := fun s : Fin (2*m) => output hM W B j d bits (depth m s)
    let mass := weight m out S 16
    Function.Bijective (seedOfBits d theta) ∧
    1≤m ∧ m≤2*max 1 ⌈4/(d*theta)⌉₊ ∧
    ((4/(d*theta) : ℚ)≤m) ∧
    (rationalHHLTable M d bits).size=M ∧
    (∀ y : Fin M, (rationalHHLTable M d bits)[y.val]? =
      some (rationalHHLCS d (rationalHHLDecode M y) bits)) ∧
    (∑ y : Fin M,
      ((rationalSqrtBracket ((rationalHHLGamma d (rationalHHLDecode M y))^2) bits).2.2 +
       (rationalSqrtBracket (1-(rationalHHLGamma d (rationalHHLDecode M y))^2) bits).2.2)) =
      2*M*bits ∧
    A∈Matrix.unitaryGroup (Space D M) ℂ ∧
    A*ᵥKet (source hM j)=rationalHHLRun M hM W d bits B j ∧
    (∀ s : Fin (2*m), PreparedCircuitValid (words s) ∧ Normalized (out s) ∧
      out s=Run (preparedMark S) (preparedAACircuit A (source hM j) (depth m s))
        (Ket (source hM j)) ∧
      preparedDataQueries (words s)=(2*depth m s+1)*(2*(M-1)) ∧
      preparedInputQueries (words s)=2*depth m s+1 ∧
      dataForwardCalls (words s)=(2*depth m s+1)*(M-1) ∧
      dataBackwardCalls (words s)=(2*depth m s+1)*(M-1) ∧
      inputForwardCalls (words s)=depth m s+1 ∧
      inputBackwardCalls (words s)=depth m s ∧
      preparedFixedGates (words s)=(2*depth m s+1)*(4*(M-1)+5)+2*depth m s) ∧
    (1/8 : ℝ)≤(∑ s : Fin (2*m), MeasureProb (out s) S)/(2*m : ℝ) ∧
    (∀ tr : Trace m 16, 0≤mass tr) ∧ (∑ tr : Trace m 16, mass tr)=1 ∧
    (∑ tr : Trace m 16, if (selected out S 16 tr).isNone then mass tr else 0) =
      (1-(∑ s : Fin (2*m), MeasureProb (out s) S)/(2*m : ℝ))^16 ∧
    (∑ tr : Trace m 16, if (selected out S 16 tr).isSome then mass tr else 0) ≥
      1-(7/8 : ℝ)^16 ∧ (2/3 : ℝ)≤1-(7/8 : ℝ)^16 ∧
    (∀ tr : Trace m 16,
      (history 16 tr).length≤16 ∧
      totalInput words tr≤16*(2*m-1) ∧
      totalData words tr=(2*(M-1))*totalInput words tr ∧
      totalFixed words tr≤16*((2*m-1)*(4*(M-1)+5)+2*(m-1)) ∧
      (history 16 tr).length*(seedBits d theta+1)≤16*(seedBits d theta+1)) ∧
    (∀ (tr : Trace m 16) (φ : QState (Space D M)),
      0<mass tr → selected out S 16 tr=some φ → Normalized φ ∧
      ∃ z : ℂ, ‖z‖=1 ∧ ‖toEuclidean_fromVec
        (z • φ-uniformHHLSolutionTarget M hM eig V B j)‖≤(1/2 : ℝ)^k)

end Qatlib.Concepts.HhlAlgorithms.Postselection
