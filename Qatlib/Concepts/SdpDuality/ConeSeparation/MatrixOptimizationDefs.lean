/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationSharedDefs
import Qatlib.Concepts.RationalScan.Step2Scan.MatrixOptimizationAlgorithmsDefs
import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationAlgorithmsDefs

/-!
# Execution records and resource contracts for SDP optimization

This module defines finite execution data and predicates for Step 2 scans, sparsification,
rejection timeouts, and resource accounting in the quantum SDP setting of [BrandaoSvore2017].
`Step2Scan.sound` describes the first accepted candidate or universal rejection, while
`Step2Run.legal` combines this condition with a sample ledger and an entry-query bound.
Concentration events and their failure expressions are kept explicit.

The propositions `noOutputUnconditionalBoundary` and `widthWrongStrongBoundary` describe
potential witnesses to failures of stronger conclusions, including failure of the good event or
of a unit-interval payoff condition. `RunEventLedger`, `HistoryCopyLedger`, and
`RunPathCompile.legal` specify separate event, copy, and compilation accounting requirements,
and `Alg3DegenerateBranch.legal` uses a guarded logarithmic failure budget.

## Main statements

* `Step2Scan.sound` and `Step2Run.legal`: scan acceptance, ordering, and resource requirements.
* `step2TableConcentrates` and `Step2UnifiedGoodEvent`: concentration and legal-loop conditions.
* `noOutputUnconditionalBoundary` and `widthWrongStrongBoundary`: existential boundary
  propositions with explicit failed conclusions.
* `SparsifySample.boundedSummands` and `sparsifyOperatorError`: operator norm requirements for
  sparsification.
* `RunEventLedger.legal`, `HistoryCopyLedger.legal`, and `RunPathCompile.legal`: event, copy,
  and componentwise cost contracts.
* `safeFailureBudget` and `Alg3DegenerateBranch.legal`: failure accounting with `safeLog`.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option autoImplicit false

namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.RationalScan.Step2Scan
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.RationalScan.Step2Scan
noncomputable section

/-- Represents a Step 2 scan outcome as either a hit at candidate `k` and grid index `N`, or
`noOutput`. -/
inductive Step2Scan (γ Nmax : ℕ) where

  | hit (k : Fin γ) (N : Fin Nmax)

  | noOutput

namespace Step2Scan

variable {γ Nmax : ℕ}

/-- On a hit, forms the round vector by scaling the selected loop law by `step2Mass κ N`; on
`noOutput`, returns the zero vector. -/
def roundVector (m : ℕ) (κ : ℝ) {M : ℕ} (loop : Step2Loop m γ Nmax M) :
    Step2Scan γ Nmax → Fin m → ℝ
  | hit k N => step2RoundVector m (step2Mass κ N) (loop.law k)
  | noOutput => fun _ => 0

/-- For a hit, requires acceptance of the selected pair and rejection of every pair with smaller
`step2PairIndex`. For `noOutput`, requires `Step2NoOutput` for the loop. -/
def sound (m : ℕ) (b : Fin m → ℝ) {M : ℕ} (loop : Step2Loop m γ Nmax M)
    (α R κ ν : ℝ) : Step2Scan γ Nmax → Prop
  | hit k N =>
      step2Accepts m M b (loop.estA k N) (loop.estC k N) (loop.draws k N) α R κ ν
        (step2Mass κ N) ∧
      ∀ (k' : Fin γ) (N' : Fin Nmax),
        step2PairIndex k' N' < step2PairIndex k N →
          ¬ step2Accepts m M b (loop.estA k' N') (loop.estC k' N') (loop.draws k' N')
            α R κ ν (step2Mass κ N')
  | noOutput => Step2NoOutput m γ Nmax M b loop α R κ ν

end Step2Scan

/-- Stores a Step 2 loop and scan outcome together with counts of visited pairs, Gibbs copies,
distribution draws, state copies, and entry queries. -/
structure Step2Run (m γ Nmax M L : ℕ) where

  loop : Step2Loop m γ Nmax M

  scan : Step2Scan γ Nmax

  pairs : ℕ

  gibbsCopies : ℕ

  qDraws : ℕ

  stateCopies : ℕ

  entryQueries : ℕ

/-- Requires a sound scan and the `Step2SampleLedger` relations for the recorded counts. It also
bounds entry queries by `(gibbsCopies + stateCopies)*s + qDraws`. -/
def Step2Run.legal {m γ Nmax M L : ℕ} (b : Fin m → ℝ) (run : Step2Run m γ Nmax M L)
    (α R κ ν : ℝ) (s : ℕ) : Prop :=
  Step2Scan.sound m b run.loop α R κ ν run.scan ∧
    Step2SampleLedger γ Nmax M L run.pairs run.gibbsCopies run.qDraws run.stateCopies ∧
    run.entryQueries ≤ (run.gibbsCopies + run.stateCopies) * s + run.qDraws

/-- Requires equality of two loops' candidate laws, `estA` tables, and `estC` tables; it places
no equality condition on their draw tables. -/
def Step2Loop.sameProgram {m γ Nmax M : ℕ} (L₁ L₂ : Step2Loop m γ Nmax M) : Prop :=
  L₁.law = L₂.law ∧ L₁.estA = L₂.estA ∧ L₁.estC = L₂.estC

/-- For every candidate and grid index, requires the empirical mean of `b` to be within
`R*(κ+ν)` of its law expectation. It also requires the empirical mean of the `estA` entries
to be within `κ+ν` of their law expectation. -/
def step2TableConcentrates {m γ Nmax M : ℕ} (b : Fin m → ℝ)
    (law : Fin γ → Fin m → ℝ) (estA : Fin γ → Fin Nmax → Fin m → ℝ)
    (tab : Fin γ → Fin Nmax → Fin M → Fin m) (κ R ν : ℝ) : Prop :=
  ∀ (k : Fin γ) (N : Fin Nmax),
    |(∑ i : Fin m, law k i * b i) - (∑ j : Fin M, b (tab k N j)) / (M : ℝ)| ≤ R * (κ + ν) ∧
    |(∑ j : Fin M, estA k N (tab k N j)) / (M : ℝ) - (∑ i : Fin m, law k i * estA k N i)| ≤
      κ + ν

/-- Defines the `loopEventProb` mass of draw tables for which `step2TableConcentrates` fails. -/
def step2GoodFailProb (m γ Nmax M : ℕ) (b : Fin m → ℝ)
    (law : Fin γ → Fin m → ℝ) (estA : Fin γ → Fin Nmax → Fin m → ℝ) (κ R ν : ℝ) : ℝ :=
  loopEventProb m γ Nmax M law
    (fun tab => ¬ step2TableConcentrates b law estA tab κ R ν)

/-- Defines the expression `2*(γ*Nmax)*(matrixHoeffdingTail 1 M (κ+ν) R + matrixHoeffdingTail 1
M (κ+ν) 2)`, with natural counts cast to the reals. -/
def step2GoodFailBound (γ Nmax M : ℕ) (κ ν R : ℝ) : ℝ :=
  2 * (γ * Nmax : ℝ) *
    (matrixHoeffdingTail 1 M (κ + ν) R + matrixHoeffdingTail 1 M (κ + ν) 2)

/-- Combines `Step2LoopLegal` for the supplied matrices, state, and parameters with the loop's
`Step2GoodEvent`. -/
def Step2UnifiedGoodEvent {D m γ Nmax M : ℕ} (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (ρ : Operator D) (loop : Step2Loop m γ Nmax M) (κ R ν : ℝ) : Prop :=
  Step2LoopLegal D m γ Nmax M A Cv b ρ loop κ R ν ∧
    Step2GoodEvent m γ Nmax M b loop κ R ν

/-- Stores a natural timeout budget, a truncation mass, an expected cost, and a real tail
function on natural cutoffs. -/
structure TimeoutSupport where

  budget : ℕ

  truncMass : ℝ

  expectedCost : ℝ

  tail : ℕ → ℝ

/-- Requires nonnegative truncation mass, expected cost, and tail values. A zero budget forces
zero truncation mass, while a positive budget requires the tail at that budget to be at most
the truncation mass. -/
def TimeoutSupport.legal (S : TimeoutSupport) : Prop :=
  0 ≤ S.truncMass ∧ 0 ≤ S.expectedCost ∧ (∀ k, 0 ≤ S.tail k) ∧
    (S.budget = 0 → S.truncMass = 0) ∧
    (0 < S.budget → S.tail S.budget ≤ S.truncMass)

/-- Defines the natural grid endpoint as `Nat.ceil (α/κ)`. -/
def step2CeilGridPoint (α κ : ℝ) : ℕ := Nat.ceil (α / κ)

/-- Asserts the strict inequalities `α < κ*step2CeilGridPoint α κ` and `Nat.floor (α/κ) <
step2CeilGridPoint α κ`, with natural values cast to the reals. -/
def step2CeilOverBound (α κ : ℝ) : Prop :=
  α < κ * (step2CeilGridPoint α κ : ℝ) ∧
    (Nat.floor (α / κ) : ℝ) < (step2CeilGridPoint α κ : ℝ)

/-- Requires every nonnegative vector `z` whose matrix payoff reaches `Re(trace(Cv*ρ)) - 3*α*ε`
to have cost `∑ i, z i*b i` at least `α*(1-3*R*ε)`. -/
def noCheapAt (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (ρ : Operator D) (α R ε : ℝ) : Prop :=
  ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
    ((Matrix.trace (Cv * ρ)).re - 3 * α * ε ≤
      ∑ i, z i * (Matrix.trace (A i * ρ)).re) →
    α * (1 - 3 * R * ε) ≤ ∑ i, z i * b i

/-- States the existence of positive-dimensional data with Hermitian contraction matrices, `b i
≥ 1`, a density state, positive scalar parameters, and `3*R*ε < 1`. The loop is legal and
has no output, but its good event fails and `noCheapAt` fails. -/
def noOutputUnconditionalBoundary : Prop :=
  ∃ (D m γ Nmax M : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
      (ρ : Operator D) (loop : Step2Loop m γ Nmax M) (α R κ ν ε : ℝ),
    0 < D ∧ 0 < m ∧ 0 < α ∧ 0 < R ∧ 0 < ε ∧ 0 < κ ∧ 0 < ν ∧ 3 * R * ε < 1 ∧
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) ∧
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 ∧
    (∀ i, 1 ≤ b i) ∧
    IsDensityOperator ρ ∧
    Step2LoopLegal D m γ Nmax M A Cv b ρ loop κ R ν ∧
    ¬ Step2GoodEvent m γ Nmax M b loop κ R ν ∧
    Step2NoOutput m γ Nmax M b loop α R κ ν ∧
    ¬ noCheapAt D m A Cv b ρ α R ε

/-- States the existence of Hermitian contraction data with `A j₀ = 1`, `b j₀ = R`, `b i ≥ 1`,
`α ≥ 2`, positive `R,ε`, and `2*R*ε ≤ 1/2`, together with nonnegative round vectors of cost
at most `α*(1+4*R*ε)`. The initial cost exceeds `α*(1+2*R*ε)` and its `dualPayoff` fails
`payoffUnitInterval`. -/
def widthWrongStrongBoundary : Prop :=
  ∃ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
      (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R ε : ℝ),
    0 < D ∧ 0 < m ∧ 2 ≤ α ∧ 0 < R ∧ 0 < ε ∧ 2 * R * ε ≤ 1 / 2 ∧
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) ∧
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 ∧
    (∀ i, 1 ≤ b i) ∧ A j₀ = 1 ∧ b j₀ = R ∧
    (∀ t, (∀ i, 0 ≤ y t i) ∧ ∑ i, b i * y t i ≤ α * (1 + 4 * R * ε)) ∧
    α * (1 + 2 * R * ε) < ∑ i, b i * y 0 i ∧
    ¬ payoffUnitInterval D (dualPayoff D m A Cv α y 0)

/-- Stores a real vector `q` on `Fin m` and a table of `Q` selected indices, without additional
probability or sampling conditions. -/
structure SparsifySample (m Q : ℕ) where

  q : Fin m → ℝ

  idx : Fin Q → Fin m

/-- Requires `IsSamplingLaw m S.q`. The predicate imposes no joint-distribution or independence
condition on the stored indices. -/
def SparsifySample.independent {m Q : ℕ} (S : SparsifySample m Q) : Prop :=
  IsSamplingLaw m S.q

/-- Requires each sampled matrix centered at `∑ i, S.q i • A i` and scaled by `mass/(4*α)` to
have operator norm at most `sparsifySummandBound mass α`. -/
def SparsifySample.boundedSummands {D m Q : ℕ} (A : Fin m → Operator D)
    (S : SparsifySample m Q) (mass α : ℝ) : Prop :=
  ∀ j : Fin Q,
    ‖((mass / (4 * α) : ℝ)) • (A (S.idx j) - (∑ i, S.q i • A i))‖ ≤
      sparsifySummandBound mass α

/-- Requires the operator norm distance between `sdpScaledSparsifiedPayoff` for the sampled
indices and `sourceScaledPayoff` for `y` to be at most `bound`. -/
def sparsifyOperatorError {D m Q : ℕ} (A : Fin m → Operator D) (Cv : Operator D)
    (y : Fin m → ℝ) (S : SparsifySample m Q) (α mass bound : ℝ) : Prop :=
  ‖sdpScaledSparsifiedPayoff D m Q A Cv α mass S.idx -
    Qatlib.Concepts.SdpDuality.ConeSeparation.sourceScaledPayoff A Cv α y‖ ≤ bound

/-- Stores a union-failure charge, a stopping-tail function, and a timeout-mass charge for a
run. -/
structure RunEventLedger where

  unionFail : ℝ

  stopTail : ℕ → ℝ

  timeoutMass : ℝ

/-- Requires nonnegative union-failure and timeout charges and nonnegative stopping tails, with
`unionFail + timeoutMass ≤ budget`. -/
def RunEventLedger.legal (L : RunEventLedger) (budget : ℝ) : Prop :=
  0 ≤ L.unionFail ∧ 0 ≤ L.timeoutMass ∧ (∀ k, 0 ≤ L.stopTail k) ∧
    L.unionFail + L.timeoutMass ≤ budget

/-- Defines `lawTV p q` as half the L1 distance `l1Dist p q`, for arbitrary real vectors on the
finite outcome set. -/
def lawTV {m : ℕ} (p q : Fin m → ℝ) : ℝ := l1Dist p q / 2

/-- Stores natural counts of Gibbs calls, measurement copies, and sample draws across a history. -/
structure HistoryCopyLedger where

  gibbsCalls : ℕ

  measCopies : ℕ

  sampleDraws : ℕ

/-- Requires the exact accounting identities `gibbsCalls = T*(Q+1)`, `measCopies = T*2*L`, and
`sampleDraws = T*Q`. -/
def HistoryCopyLedger.legal (T Q L : ℕ) (H : HistoryCopyLedger) : Prop :=
  H.gibbsCalls = T * (Q + 1) ∧ H.measCopies = T * 2 * L ∧ H.sampleDraws = T * Q

/-- Enumerates run-path categories for controlled entry and sparse-row access, Hamiltonian
oracles, Gibbs preparation, estimation, rejection sampling, binary shells, inverse words,
classical arithmetic, and timeout truncation. -/
inductive Alg3RunPath where

  | controlledEntry

  | controlledSparseRow

  | hOracle

  | gibbsPrepare

  | estimation

  | sampleReject

  | binaryShell

  | inverseWord

  | classicalArith

  | timeoutTrunc
  deriving DecidableEq, Repr

/-- Stores dimension, constraint count, sparsity, input-word and truncation-bit sizes, and the
real precision, failure, exponent, and radius parameters used for resource accounting. -/
structure SdpResourceParams where

  dim : ℕ

  constraints : ℕ

  sparsity : ℕ

  inputWord : ℕ

  truncBits : ℕ

  eps : ℝ

  delta : ℝ

  xi : ℝ

  sizeR : ℝ

/-- Requires positive dimension, constraint count, sparsity, and input-word size, together with
`0 < eps ≤ 1/2`, `0 < delta ≤ 1`, `1 < xi`, and `1 ≤ sizeR`. -/
def SdpResourceParams.legal (P : SdpResourceParams) : Prop :=
  0 < P.dim ∧ 0 < P.constraints ∧ 0 < P.sparsity ∧ 0 < P.inputWord ∧
    0 < P.eps ∧ P.eps ≤ 1 / 2 ∧ 0 < P.delta ∧ P.delta ≤ 1 ∧ 1 < P.xi ∧ 1 ≤ P.sizeR

/-- Stores natural costs for queries, two-qubit gates, fair random bits, bit time, peak space,
and integer bits along a run path. -/
structure PathCost where

  queries : ℕ

  twoQubitGates : ℕ

  fairBits : ℕ

  bitTime : ℕ

  peakSpace : ℕ

  intBits : ℕ

/-- Stores real bounds for queries, two-qubit gates, fair bits, bit time, and peak space,
together with a natural bound for integer bits. -/
structure PathBound where

  queries : ℝ

  twoQubitGates : ℝ

  fairBits : ℝ

  bitTime : ℝ

  peakSpace : ℝ

  intBits : ℕ

/-- Stores a register width, a finite gate word, its recorded `PathCost`, and a `PathBound` for
the compilation. -/
structure RunPathCompile where

  width : ℕ

  word : List FiniteGateCode

  cost : PathCost

  bound : PathBound

/-- Requires the gate word to be legal at the recorded width and each of the six recorded
resource costs to be at most its corresponding bound. -/
def RunPathCompile.legal (C : RunPathCompile) : Prop :=
  finiteWordLegal C.width C.word = true ∧
    (C.cost.queries : ℝ) ≤ C.bound.queries ∧
    (C.cost.twoQubitGates : ℝ) ≤ C.bound.twoQubitGates ∧
    (C.cost.fairBits : ℝ) ≤ C.bound.fairBits ∧
    (C.cost.bitTime : ℝ) ≤ C.bound.bitTime ∧
    (C.cost.peakSpace : ℝ) ≤ C.bound.peakSpace ∧
    C.cost.intBits ≤ C.bound.intBits

/-- Defines the gate-bound expression `calls*(64*D+128)*(Nat.ceil ((1/prec)^2)+1)`, with the
natural ceiling cast to the reals. -/
def runGateBound (D : ℕ) (prec calls : ℝ) : ℝ :=
  calls * (64 * D + 128) * (((Nat.ceil ((1 / prec) ^ 2) : ℕ) : ℝ) + 1)

/-- Defines the integer-bit charge as `sdpIntegerBits (2*P.inputWord + P.truncBits + 8)
(sdpPrecisionBits P.eps)`. -/
def runIntegerBitBound (P : SdpResourceParams) : ℕ :=
  sdpIntegerBits (2 * P.inputWord + P.truncBits + 8) (sdpPrecisionBits P.eps)

/-- Requires `C ≥ 1`, `N ≥ 1`, and `actual ≤ C*budget*(max 1 (Real.log N))^k`. -/
def SoftOBounded (actual budget C N : ℝ) (k : ℕ) : Prop :=
  1 ≤ C ∧ 1 ≤ N ∧ actual ≤ C * budget * (max 1 (Real.log N)) ^ k

/-- Defines the guarded logarithm `max 1 (Real.log x)`. -/
def safeLog (x : ℝ) : ℝ := max 1 (Real.log x)

/-- Defines `cO*((R/δ)^18*(safeLog (n*m))^10*Real.exp (-(safeLog (n*m))^ξ))`, with the natural
dimensions coerced to the reals. -/
def safeFailureBudget (n m : ℕ) (R δ ξ cO : ℝ) : ℝ :=
  cO * ((R / δ) ^ 18 * (safeLog ((n : ℝ) * (m : ℝ))) ^ 10 *
    Real.exp (-(safeLog ((n : ℝ) * (m : ℝ))) ^ ξ))

/-- Stores natural round, `M`-sample, and `L`-sample counts and a real failure charge for a
degenerate Algorithm 3 branch. -/
structure Alg3DegenerateBranch (n m : ℕ) where

  rounds : ℕ

  samplesM : ℕ

  samplesL : ℕ

  failCharge : ℝ

/-- Requires positive round and sample counts and a nonnegative failure charge bounded by
`safeFailureBudget n m R δ ξ cO`. -/
def Alg3DegenerateBranch.legal {n m : ℕ} (B : Alg3DegenerateBranch n m)
    (R δ ξ cO : ℝ) : Prop :=
  0 < B.rounds ∧ 0 < B.samplesM ∧ 0 < B.samplesL ∧ 0 ≤ B.failCharge ∧
    B.failCharge ≤ safeFailureBudget n m R δ ξ cO

end

end Qatlib.Concepts.SdpDuality.ConeSeparation
