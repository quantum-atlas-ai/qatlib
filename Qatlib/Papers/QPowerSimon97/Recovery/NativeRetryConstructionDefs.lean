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

/-!
# Native Simon retry and query-model definitions

Defines register encodings and gate-word realization predicates for Simon experiments, together
with classical serialization and work ledgers. It also defines independent repeated runs,
adaptive classical query trees, and the amplification statement used in the recovery development
associated with [Simon1997].

The random-oracle construction chooses its mask uniformly from all Boolean vectors, including
zero. Its strict two-to-one predicate imposes shift invariance and fibers of size zero or two;
the distribution uses the identity function as a fallback when that class is empty.

## Main statements

* `Clause4StandardModelBridge`: The bridge statement requiring experiment and verification gate
  words with the prescribed realization properties, length bounds, and expected retry-weighted
  gate bound from a supplied oracle implementation under the Simon promise.
* `simonOracleConstruction`: The random-oracle branch law obtained by choosing a uniform mask,
  including zero, and a fair Boolean branch, then sampling from `simonTwoToOneDist` on the true
  branch or a uniform permutation on the false branch [Simon1997].
* `Clause5TwoSidedAmplification`: The combined statement of injective and near-period
  amplification errors, exact single-run ledgers and fresh-run marginals, and the classical
  random-oracle branch-guessing bound [Simon1997].

## References

* [Simon, 1997][Simon1997]
-/

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

/-- The wire count `(2 * (n + m) + 1) + 3` used for the encoded Simon registers and workspace. -/
def simonWireLayout (n m : ℕ) : ℕ := (2 * (n + m) + 1) + 3

/-- Encodes the two Boolean vectors into the first `n + m` wires while preserving the remaining
context wires. -/
def simonEncodeContext {n m : ℕ} (x : BooleanVec n) (y : BooleanVec m)
    (ctx : Reg (simonWireLayout n m)) : Reg (simonWireLayout n m) :=
  fun i => if h : i.val < n then decide (x ⟨i.val,h⟩ = 1)
    else if h : i.val < n+m then decide (y ⟨i.val-n,by omega⟩ = 1)
    else ctx i

/-- Encodes a pair of Boolean vectors with all remaining context wires set to `false`. -/
def simonEncodePair {n m : ℕ} (x : BooleanVec n) (y : BooleanVec m) :
    Reg (simonWireLayout n m) := simonEncodeContext x y (fun _ => false)

/-- The linear extension of the pair encoding to states, obtained by summing encoded basis kets
with the original amplitudes. -/
noncomputable def simonEncodeState {n m : ℕ}
    (ψ : QState (BooleanVec n × BooleanVec m)) : QState (Reg (simonWireLayout n m)) :=
  ∑ p : BooleanVec n × BooleanVec m, ψ p • Qatlib.Foundations.PureStateMath.Ket (simonEncodePair p.1 p.2)

/-- The predicate that a compiled gate word implements the additive oracle on encoded registers
for every context. -/
def SimonQueryWordRealizes {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (Gq : List (Phi3Gate (simonWireLayout n m))) : Prop :=
  ∀ (x : BooleanVec n) (y : BooleanVec m) (ctx : Reg (simonWireLayout n m)),
    Run (1 : Matrix (Reg (simonWireLayout n m)) (Reg (simonWireLayout n m)) ℂ)
      (phi3Compile Gq) (Qatlib.Foundations.PureStateMath.Ket (simonEncodeContext x y ctx)) =
    Qatlib.Foundations.PureStateMath.Ket (simonEncodeContext x (y+f x) ctx)

/-- The predicate that a compiled gate word implements the prepared Simon experiment on every
encoded input pair. -/
def SimonExperimentWordRealizes {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (B : List (Phi3Gate (simonWireLayout n m))) : Prop :=
  ∀ (x : BooleanVec n) (y : BooleanVec m),
    Run (1 : Matrix (Reg (simonWireLayout n m)) (Reg (simonWireLayout n m)) ℂ)
      (phi3Compile B) (Qatlib.Foundations.PureStateMath.Ket (simonEncodePair x y)) =
    simonEncodeState
      (Run (AddOracle f) (simonPreparedCircuit (R := BooleanVec m) n) (Qatlib.Foundations.PureStateMath.Ket (x,y)))

/-- The predicate that a compiled gate word writes the test `f cand = f 0` to wire `2 * (n + m)`
while otherwise preserving the encoded candidate input. -/
def SimonVerifyWordRealizes {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (Wv : List (Phi3Gate (simonWireLayout n m))) : Prop :=
  ∀ cand : BooleanVec n,
    Run (1 : Matrix (Reg (simonWireLayout n m)) (Reg (simonWireLayout n m)) ℂ)
      (phi3Compile Wv) (Qatlib.Foundations.PureStateMath.Ket (simonEncodePair cand 0)) =
    Qatlib.Foundations.PureStateMath.Ket (fun i => if i.val=2*(n+m) then decide (f cand=f 0)
      else simonEncodePair cand 0 i)

/-- The experiment gate-padding allowance `2 * n`. -/
def simonExperimentPadGates (n : ℕ) : ℕ := 2*n

/-- The verification gate-padding allowance `6 * n + 32 * m + 6`. -/
def simonVerifyPadGates (n m : ℕ) : ℕ := 6*n+32*m+6

/-- The decoding gate-padding allowance `64 * (n + 1) * simonBlockOpsBound n`. -/
def simonDecodePadGates (n : ℕ) : ℕ := 64*(n+1)*simonBlockOpsBound n

/-- The bridge statement requiring experiment and verification gate words with the prescribed
realization properties, length bounds, and expected retry-weighted gate bound from a
supplied oracle implementation under the Simon promise. -/
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

/-- The joint distribution of `r` independent decoded Simon runs, each using `m` samples. -/
noncomputable def simonFreshRuns {n : ℕ} {R : Type} [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) (m : ℕ) :
    (r : ℕ) → PMF (Fin r → Option (Reg n))
  | 0 => PMF.pure default
  | r + 1 => PMF.bind ((simonDecodedRun f m).1) fun a =>
      PMF.map (Fin.cons a) (simonFreshRuns f m r)

/-- The Boolean test that some decoded run differs from `some (ZeroStr n)`, counting `none` as a
rejecting result. -/
def simonAnyRejectBits {n : ℕ} {r : ℕ} (v : Fin r → Option (Reg n)) : Bool :=
  decide (∃ i : Fin r, v i ≠ some (ZeroStr n))

/-- The Boolean law obtained by testing whether any of `r` independent decoded runs differs from
the zero result. -/
noncomputable def simonAmplifiedReject {n : ℕ} {R : Type} [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) (m r : ℕ) : PMF Bool :=
  PMF.map simonAnyRejectBits (simonFreshRuns f m r)

/-- Finite adaptive classical oracle-query trees whose leaves return a Boolean value and whose
query nodes branch on a Boolean-vector response. -/
inductive SimonQueryTree (n : ℕ) where
  | halt : Bool → SimonQueryTree n
  | ask : BooleanVec n → (BooleanVec n → SimonQueryTree n) → SimonQueryTree n

namespace SimonQueryTree

variable {n : ℕ}

/-- The maximum number of queries along any path in a classical query tree. -/
def maxQueries : SimonQueryTree n → ℕ
  | .halt _ => 0
  | .ask _ next => 1 + Finset.sup (Finset.univ : Finset (BooleanVec n))
      (fun y => (next y).maxQueries)

/-- Evaluates a classical query tree against `f`, returning its Boolean result and the number of
queries made. -/
def run (f : BooleanVec n → BooleanVec n) : SimonQueryTree n → Bool × ℕ
  | .halt b => (b, 0)
  | .ask x next =>
      let r := run f (next (f x))
      (r.1, r.2 + 1)

/-- The probability that a randomized classical query tree returns the specified Boolean value
against `f`. -/
noncomputable def guessMass (P : PMF (SimonQueryTree n))
    (f : BooleanVec n → BooleanVec n) (b : Bool) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation P
    (fun τ => if (run f τ).1 = b then (1 : ℝ≥0∞) else 0)

/-- The predicate that every query tree of positive probability has maximum query count at most
`T`. -/
def bounded (P : PMF (SimonQueryTree n)) (T : ℕ) : Prop :=
  ∀ τ, (P τ).toReal > 0 → τ.maxQueries ≤ T

end SimonQueryTree

/-- The predicate that `f` is invariant under addition of `s` and every fiber has cardinality
zero or two; `s` may be zero. -/
def SimonStrictTwoToOne {n : ℕ} (s : BooleanVec n)
    (f : BooleanVec n → BooleanVec n) : Prop :=
  (∀ x, f x = f (x + s)) ∧
    ∀ y, Nat.card {x : BooleanVec n | f x = y} = 2 ∨
      Nat.card {x : BooleanVec n | f x = y} = 0

/-- The uniform law on strict two-to-one functions invariant under addition of `s` when this
class is nonempty, and the point mass at the identity function otherwise. -/
noncomputable def simonTwoToOneDist {n : ℕ} (s : BooleanVec n) :
    PMF (BooleanVec n → BooleanVec n) :=
  if h : Nonempty {f : BooleanVec n → BooleanVec n // SimonStrictTwoToOne s f} then
    PMF.map (fun g => (g : BooleanVec n → BooleanVec n))
      (@PMF.uniformOfFintype' {f : BooleanVec n → BooleanVec n // SimonStrictTwoToOne s f}
        (Fintype.ofFinite _) h)
  else PMF.pure id

/-- The random-oracle branch law obtained by choosing a uniform mask, including zero, and a fair
Boolean branch, then sampling from `simonTwoToOneDist` on the true branch or a uniform
permutation on the false branch [Simon1997]. -/
noncomputable def simonOracleConstruction (n : ℕ) :
    PMF (Bool × (BooleanVec n → BooleanVec n)) :=
  PMF.bind (PMF.uniformOfFintype' (BooleanVec n)) fun s =>
    PMF.bind (PMF.uniformOfFintype' Bool) fun b =>
      if b then PMF.map (fun g => (true, (g : BooleanVec n → BooleanVec n)))
          (simonTwoToOneDist s)
        else PMF.map (fun π => (false, (π : BooleanVec n → BooleanVec n)))
          (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n)))

/-- The expected mass of correctly guessing the sampled Boolean branch of
`simonOracleConstruction` with the randomized query tree law `P`. -/
noncomputable def simonOracleGuessMass {n : ℕ} (P : PMF (SimonQueryTree n)) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonOracleConstruction n)
    (fun ob => SimonQueryTree.guessMass P ob.2 ob.1)

/-- The combined statement of injective and near-period amplification errors, exact single-run
ledgers and fresh-run marginals, and the classical random-oracle branch-guessing bound
[Simon1997]. -/
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

/-- The list of a register's Boolean entries in increasing index order. -/
def simonRowBits {n : ℕ} (row : Reg n) : List Bool := (List.finRange n).map row

/-- The list of serialized row registers in increasing row order. -/
def simonRecordTape {n m : ℕ} (rows : Fin m → Reg n) : List (List Bool) :=
  (List.finRange m).map (fun i => simonRowBits (rows i))

/-- The serialization step count `m * n` for `m` rows of length `n`. -/
def simonSerializeSteps {n m : ℕ} (_rows : Fin m → Reg n) : ℕ := m * n

/-- The Boolean encoding of coordinate `j` in decoded character sample `i`. -/
def simonSerializeBit {n : ℕ} (xs : Fin (n+1) → AddChar (BooleanVec n) ℂ)
    (i : Fin (n+1)) (j : Fin n) : Bool :=
  boolZModEquiv.symm (booleanDecodedSamples xs i j)

/-- The Boolean test that all corresponding entries of two registers are equal. -/
def simonCompare {m : ℕ} (a b : Reg m) : Bool :=
  (List.finRange m).all (fun j => decide (a j = b j))

/-- The register comparison step count `m`. -/
def simonCompareSteps (m : ℕ) : ℕ := m

/-- The explicit Boolean elimination operation bound `10 * ((n + 1) * n^2 + (n + 1) * n + (n +
1))`. -/
def simonBitOpsBound (n : ℕ) : ℕ := 10*((n+1)*n^2+(n+1)*n+(n+1))

/-- The classical work ledger adding two oracle-evaluation charges, row serialization, register
comparison, and the recorded Boolean echelon bit operations. -/
noncomputable def simonClassicalBitLedger {n : ℕ} (m : ℕ) (Tf : ℕ)
    (xs : Fin (n+1) → AddChar (BooleanVec n) ℂ) : ℕ :=
  2*Tf + simonSerializeSteps (simonRecordBits xs) + simonCompareSteps m
    + (booleanEchelonRun (List.ofFn (simonRecordBits xs))).bitOps

end Qatlib.Papers.QPowerSimon97.Recovery
