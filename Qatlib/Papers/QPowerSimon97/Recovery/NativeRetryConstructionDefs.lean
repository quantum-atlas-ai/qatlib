/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.HspRecovery.Distinguisher.BoundedErrorNearPeriodStat
import Qatlib.Concepts.AbelianDecoders.SimonDecoding.VerifiedSimonRetry
import Qatlib.Concepts.UniformBqp.Phi3Compile.QtmPhi3WindowSimulationStat
import Qatlib.Concepts.QtmSimulation.Phi3Compilation.QtmPhi3WireTransport
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
import Mathlib.Probability.Distributions.Uniform
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Concepts.AbelianDecoders.SimonDecoding Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.QtmSimulation.Phi3Compilation
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.CircuitImpl.Phi3Universal
open scoped Classical BigOperators ENNReal

def simonWireLayout (n m : ℕ) : ℕ := (2 * (n + m) + 1) + 3

def simonEncodeContext {n m : ℕ} (x : BooleanVec n) (y : BooleanVec m)
    (ctx : Reg (simonWireLayout n m)) : Reg (simonWireLayout n m) :=
  fun i => if h : i.val < n then decide (x ⟨i.val,h⟩ = 1)
    else if h : i.val < n+m then decide (y ⟨i.val-n,by omega⟩ = 1)
    else ctx i

def simonEncodePair {n m : ℕ} (x : BooleanVec n) (y : BooleanVec m) :
    Reg (simonWireLayout n m) := simonEncodeContext x y (fun _ => false)

noncomputable def simonEncodeState {n m : ℕ}
    (ψ : QState (BooleanVec n × BooleanVec m)) : QState (Reg (simonWireLayout n m)) :=
  ∑ p : BooleanVec n × BooleanVec m, ψ p • Qatlib.Foundations.PureStateMath.Ket (simonEncodePair p.1 p.2)

def SimonQueryWordRealizes {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (Gq : List (Phi3Gate (simonWireLayout n m))) : Prop :=
  ∀ (x : BooleanVec n) (y : BooleanVec m) (ctx : Reg (simonWireLayout n m)),
    Run (1 : Matrix (Reg (simonWireLayout n m)) (Reg (simonWireLayout n m)) ℂ)
      (phi3Compile Gq) (Qatlib.Foundations.PureStateMath.Ket (simonEncodeContext x y ctx)) =
    Qatlib.Foundations.PureStateMath.Ket (simonEncodeContext x (y+f x) ctx)

def SimonExperimentWordRealizes {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (B : List (Phi3Gate (simonWireLayout n m))) : Prop :=
  ∀ (x : BooleanVec n) (y : BooleanVec m),
    Run (1 : Matrix (Reg (simonWireLayout n m)) (Reg (simonWireLayout n m)) ℂ)
      (phi3Compile B) (Qatlib.Foundations.PureStateMath.Ket (simonEncodePair x y)) =
    simonEncodeState
      (Run (AddOracle f) (simonPreparedCircuit (R := BooleanVec m) n) (Qatlib.Foundations.PureStateMath.Ket (x,y)))

def SimonVerifyWordRealizes {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (Wv : List (Phi3Gate (simonWireLayout n m))) : Prop :=
  ∀ cand : BooleanVec n,
    Run (1 : Matrix (Reg (simonWireLayout n m)) (Reg (simonWireLayout n m)) ℂ)
      (phi3Compile Wv) (Qatlib.Foundations.PureStateMath.Ket (simonEncodePair cand 0)) =
    Qatlib.Foundations.PureStateMath.Ket (fun i => if i.val=2*(n+m) then decide (f cand=f 0)
      else simonEncodePair cand 0 i)

def simonExperimentPadGates (n : ℕ) : ℕ := 2*n

def simonVerifyPadGates (n m : ℕ) : ℕ := 6*n+32*m+6

def simonDecodePadGates (n : ℕ) : ℕ := 64*(n+1)*simonBlockOpsBound n

def Clause4StandardModelBridge : Prop :=
  ∀ (n m : ℕ) (f : BooleanVec n → BooleanVec m) (s : Reg n),
    BooleanSimonPromise f (regBooleanEquiv n s) →
    ∀ (Gq : List (Phi3Gate (simonWireLayout n m))) (Tf : ℕ),
      SimonQueryWordRealizes f Gq → Gq.length ≤ Tf →
      ∃ (B Wv : List (Phi3Gate (simonWireLayout n m))),
        SimonExperimentWordRealizes f B ∧ SimonVerifyWordRealizes f Wv ∧
        B.length ≤ Tf+simonExperimentPadGates n ∧
        Wv.length ≤ 4*Tf+simonVerifyPadGates n m ∧
        (generalUnboundedTime (simonVerifiedRetryKernel f) (Sum.inr ()) : ℝ≥0∞) *
          ((n+1)*B.length+Wv.length+simonDecodePadGates n : ℕ) ≤
        (2 : ℝ≥0∞)*((n+1)*(Tf+simonExperimentPadGates n)+
          (4*Tf+simonVerifyPadGates n m)+simonDecodePadGates n : ℕ)

noncomputable def simonFreshRuns {n : ℕ} {R : Type} [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) (m : ℕ) :
    (r : ℕ) → PMF (Fin r → Option (Reg n))
  | 0 => PMF.pure default
  | r + 1 => PMF.bind ((simonDecodedRun f m).1) fun a =>
      PMF.map (Fin.cons a) (simonFreshRuns f m r)

def simonAnyRejectBits {n : ℕ} {r : ℕ} (v : Fin r → Option (Reg n)) : Bool :=
  decide (∃ i : Fin r, v i ≠ some (ZeroStr n))

noncomputable def simonAmplifiedReject {n : ℕ} {R : Type} [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) (m r : ℕ) : PMF Bool :=
  PMF.map simonAnyRejectBits (simonFreshRuns f m r)

inductive SimonQueryTree (n : ℕ) where
  | halt : Bool → SimonQueryTree n
  | ask : BooleanVec n → (BooleanVec n → SimonQueryTree n) → SimonQueryTree n

namespace SimonQueryTree

variable {n : ℕ}

def maxQueries : SimonQueryTree n → ℕ
  | .halt _ => 0
  | .ask _ next => 1 + Finset.sup (Finset.univ : Finset (BooleanVec n))
      (fun y => (next y).maxQueries)

def run (f : BooleanVec n → BooleanVec n) : SimonQueryTree n → Bool × ℕ
  | .halt b => (b, 0)
  | .ask x next =>
      let r := run f (next (f x))
      (r.1, r.2 + 1)

noncomputable def guessMass (P : PMF (SimonQueryTree n))
    (f : BooleanVec n → BooleanVec n) (b : Bool) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation P
    (fun τ => if (run f τ).1 = b then (1 : ℝ≥0∞) else 0)

def bounded (P : PMF (SimonQueryTree n)) (T : ℕ) : Prop :=
  ∀ τ, (P τ).toReal > 0 → τ.maxQueries ≤ T

end SimonQueryTree

def SimonStrictTwoToOne {n : ℕ} (s : BooleanVec n)
    (f : BooleanVec n → BooleanVec n) : Prop :=
  (∀ x, f x = f (x + s)) ∧
    ∀ y, Nat.card {x : BooleanVec n | f x = y} = 2 ∨
      Nat.card {x : BooleanVec n | f x = y} = 0

noncomputable def simonTwoToOneDist {n : ℕ} (s : BooleanVec n) :
    PMF (BooleanVec n → BooleanVec n) :=
  if h : Nonempty {f : BooleanVec n → BooleanVec n // SimonStrictTwoToOne s f} then
    PMF.map (fun g => (g : BooleanVec n → BooleanVec n))
      (@PMF.uniformOfFintype' {f : BooleanVec n → BooleanVec n // SimonStrictTwoToOne s f}
        (Fintype.ofFinite _) h)
  else PMF.pure id

noncomputable def simonOracleConstruction (n : ℕ) :
    PMF (Bool × (BooleanVec n → BooleanVec n)) :=
  PMF.bind (PMF.uniformOfFintype' (BooleanVec n)) fun s =>
    PMF.bind (PMF.uniformOfFintype' Bool) fun b =>
      if b then PMF.map (fun g => (true, (g : BooleanVec n → BooleanVec n)))
          (simonTwoToOneDist s)
        else PMF.map (fun π => (false, (π : BooleanVec n → BooleanVec n)))
          (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n)))

noncomputable def simonOracleGuessMass {n : ℕ} (P : PMF (SimonQueryTree n)) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonOracleConstruction n)
    (fun ob => SimonQueryTree.guessMass P ob.2 ob.1)

def Clause5TwoSidedAmplification : Prop :=
  (∀ (n : ℕ) (R : Type) [AddCommGroup R] [Fintype R] [DecidableEq R]
      (f : BooleanVec n → R) (k r : ℕ), 2 ≤ n + k →
    (Function.Injective f →
      (simonAmplifiedReject f (n + k) r) true ≤ ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k)) ∧
    (∀ s : BooleanVec n, s ≠ 0 →
      Nat.card {x : BooleanVec n | f x ≠ f (x + s)} * (n + k) ≤ 2 ^ n →
        (simonAmplifiedReject f (n + k) r) false ≤ ENNReal.ofReal ((3 / 4 : ℝ) ^ r)) ∧
    ((simonDecodedRun f (n + k)).2 = (n + k, 2 * (n + k), n + k) ∧
      (∀ (i : Fin r), PMF.map (fun v => v i) (simonFreshRuns f (n + k) r) =
        (simonDecodedRun f (n + k)).1)))
  ∧ (∀ (n : ℕ), 1 ≤ n → ∀ P : PMF (SimonQueryTree n),
      SimonQueryTree.bounded P (2 ^ (n / 4)) →
        simonOracleGuessMass P ≤ ENNReal.ofReal (1 / 2 + (2 : ℝ) ^ (-(n : ℝ) / 2)))

def simonRowBits {n : ℕ} (row : Reg n) : List Bool := (List.finRange n).map row

def simonRecordTape {n m : ℕ} (rows : Fin m → Reg n) : List (List Bool) :=
  (List.finRange m).map (fun i => simonRowBits (rows i))

def simonSerializeSteps {n m : ℕ} (_rows : Fin m → Reg n) : ℕ := m * n

def simonSerializeBit {n : ℕ} (xs : Fin (n+1) → AddChar (BooleanVec n) ℂ)
    (i : Fin (n+1)) (j : Fin n) : Bool :=
  boolZModEquiv.symm (booleanDecodedSamples xs i j)

def simonCompare {m : ℕ} (a b : Reg m) : Bool :=
  (List.finRange m).all (fun j => decide (a j = b j))

def simonCompareSteps (m : ℕ) : ℕ := m

def simonBitOpsBound (n : ℕ) : ℕ := 10*((n+1)*n^2+(n+1)*n+(n+1))

noncomputable def simonClassicalBitLedger {n : ℕ} (m : ℕ) (Tf : ℕ)
    (xs : Fin (n+1) → AddChar (BooleanVec n) ℂ) : ℕ :=
  2*Tf + simonSerializeSteps (simonRecordBits xs) + simonCompareSteps m
    + (booleanEchelonRun (List.ofFn (simonRecordBits xs))).bitOps

end Qatlib.Papers.QPowerSimon97.Recovery
