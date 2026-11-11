/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Qatlib.Concepts.CoherentSim.TaylorEncoding.TaylorLCUProgram
import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorConsumers
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.CoherentSim.TimeDependent.Equation28Stat
import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation16Stat

/-!
# Finite data Taylor simulation specifications

This module defines finite magnitude and phase data, complex Taylor coefficients, Pauli word
actions, sparse oracle access contracts, and time ordered cube sums for truncated Taylor
simulation [BerryEtAl2015Taylor]. `ComplexTaylorCorner` specifies the Taylor polynomial identity
and a segment error bound, while the gate access predicates describe concrete register actions
and resource constraints.

Separate reset and backend contracts track finite gate preparation, workspace transfer, integer
data storage, and approximation of unitary basis outputs. `factorialWordQPEConsumer` packages
forward and adjoint resource counts with an embedded Hamiltonian evolution error target.

## Main definitions

* `HasFiniteDataPrepare`: approximate preparation with gate and space bounds.
* `HasPauliSelectAccess`: controlled selected Pauli action on basis inputs.
* `HasSparseOracleSimulation`: sparse row access and circuit resource requirements.
* `equation28CubeSegment`: a truncated discrete time ordered expansion.
* `factorialWordQPEConsumer`: the costed evolution approximation contract.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.CoherentSim.FactorialTaylor
open Qatlib.Concepts.CoherentSim.TaylorBounds
open Qatlib.Concepts.CoherentSim.ResetDiscard
open Qatlib.Concepts.CoherentSim.TaylorEncoding

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TimeDependent

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib.Concepts.CoherentSim.TimeDependent
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- A magnitude index and a phase index with prescribed finite bit widths. -/
structure FiniteDataTerm (magBits phaseBits : ℕ) where

  mag : Fin (2 ^ magBits)

  phase : Fin (2 ^ phaseBits)

/-- A family of finite coefficient data with common magnitude and phase bit widths. -/
structure FiniteDataTerms (J : Type) where

  magBits : ℕ

  phaseBits : ℕ

  term : J → FiniteDataTerm magBits phaseBits

/-- Decodes each magnitude index as a nonnegative dyadic fraction. -/
noncomputable def finiteDataMagnitudes {J : Type} (T : FiniteDataTerms J) : J → ℝ :=
  fun j => (T.term j).mag / (2 : ℝ) ^ T.magBits

/-- Decodes each phase index as the complex exponential of its fraction of a full turn. -/
noncomputable def finiteDataPhases {J : Type} (T : FiniteDataTerms J) (j : J) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((T.term j).phase / (2 : ℝ) ^ T.phaseBits))

/-- The complex coefficient obtained by multiplying the decoded magnitude and phase. -/
noncomputable def finiteDataCoefficient {J : Type} (T : FiniteDataTerms J) (j : J) : ℂ :=
  (finiteDataMagnitudes T j : ℂ) * finiteDataPhases T j

/-- The sum of the norms of the finitely many complex coefficients. -/
noncomputable def complexTaylorLambda {J : Type} [Fintype J] (c : J → ℂ) : ℝ :=
  ∑ j, ‖c j‖

/-- The Taylor ancilla size expression `K + K * Nat.clog 2 (max 1 L) + 1`. -/
def simTaylorAncillaBits (K L : ℕ) : ℕ :=
  K + K * Nat.clog 2 (max 1 L) + 1

/-- The preparation gate budget expression `16 * K + 16 * K * L + 64`. -/
def simTaylorPrepareGates (K L : ℕ) : ℕ :=
  16 * K + 16 * K * L + 64

/-- The preparation space expression combining Taylor ancillas, coefficient data widths, and two
additional bits. -/
def simTaylorPrepareSpace (K L magBits phaseBits : ℕ) : ℕ :=
  simTaylorAncillaBits K L + magBits + phaseBits + 2

/-- Embeds or truncates a Boolean register to width `w`, filling positions beyond the source
width with false. -/
def simPad (w a : ℕ) (r : Reg a) : Reg w :=
  fun i => if h : (i : ℕ) < a then r ⟨i, h⟩ else false

/-- For positive `ε`, requires an injective Taylor label encoding and a legal finite gate word
whose zero input output approximates the specified amplitude sum within squared Euclidean
error `ε ^ 2`, with the stated size bounds. -/
def HasFiniteDataPrepare {J : Type} [Fintype J] [DecidableEq J] (K : ℕ) (τ : ℝ)
    (T : FiniteDataTerms J) (ε : ℝ) : Prop :=
  0 < ε →
    ∃ (aw w : ℕ) (enc : TaylorWordLabel J K → Reg aw) (gs : List FiniteGateCode)
        (φ : QState (Reg w)),
      Function.Injective enc ∧
        finiteWordLegal w gs = true ∧
        gs.length ≤
          simTaylorPrepareGates K (Fintype.card J) * (K + 1) *
            (Nat.ceil ((1 / ε) ^ 2) + 1) ∧
        aw ≤ simTaylorAncillaBits K (Fintype.card J) + 1 ∧
        w ≤ simTaylorPrepareSpace K (Fintype.card J) T.magBits T.phaseBits ∧
        finiteWordRun w gs (Ket (fun _ : Fin w => false)) = some φ ∧
        ∑ i, ‖φ i -
          (∑ x : TaylorWordLabel J K,
            (taylorAmplitudeReal (finiteDataMagnitudes T) τ K x : ℂ) •
              Ket (simPad w aw (enc x)) : QState (Reg w)) i‖ ^ 2 ≤ ε ^ 2

/-- The coefficient of a complex Taylor word, with factorial scaling for ordinary words and
opposite signed padding coefficients for the two extra branches. -/
noncomputable def complexTaylorCoefficient {J : Type} [Fintype J] (c : J → ℂ) (τ : ℝ)
    (K : ℕ) : TaylorWordLabel J K → ℂ :=
  fun x => match x with
    | Sum.inl w =>
        ((-Complex.I * (τ : ℂ)) ^ (w.1.val : ℕ) / (w.1.val.factorial : ℂ)) *
          ∏ i, c (w.2 i)
    | Sum.inr b =>
        if b then (2 - taylorS0 (fun j => ‖c j‖) τ K) / 2
        else -(2 - taylorS0 (fun j => ‖c j‖) τ K) / 2

/-- The finite sum of Taylor branch matrices weighted by `complexTaylorCoefficient`. -/
noncomputable def complexTaylorSum {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (c : J → ℂ) (U : J → Matrix I I ℂ) (τ : ℝ) (K : ℕ) :
    Matrix I I ℂ :=
  ∑ x : TaylorWordLabel J K,
    complexTaylorCoefficient c τ K x • taylorBranchWord U K K le_rfl x

/-- The branchwise proposition that an ordinary finite data Taylor coefficient factors into its
magnitude based coefficient and product of decoded phases; padding branches impose no
condition. -/
noncomputable def complexPhaseSplit {J : Type} [Fintype J] (T : FiniteDataTerms J) (τ : ℝ)
    (K : ℕ) : TaylorWordLabel J K → Prop :=
  fun x => match x with
    | Sum.inl w =>
        complexTaylorCoefficient (finiteDataCoefficient T) τ K (Sum.inl w) =
          taylorWordCoefficient (finiteDataMagnitudes T) τ w *
            ∏ i, finiteDataPhases T (w.2 i)
    | Sum.inr _ => True

/-- Specifies equality of the complex Taylor sum with the truncated exponential polynomial and
error at most `(1 / 2) ^ K` when the coefficient norm sum times `|τ|` is at most one half. -/
def ComplexTaylorCorner : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
      (c : J → ℂ) (U : J → Matrix I I ℂ) (τ : ℝ) (K : ℕ),
    (∀ j, U j ∈ Matrix.unitaryGroup I ℂ) →
      complexTaylorLambda c * |τ| ≤ 1 / 2 →
      complexTaylorSum c U τ K =
        Polynomial.aeval (∑ j, c j • U j) (exponentialTaylorPolynomial τ (K + 1)) ∧
        (‖Polynomial.aeval (∑ j, c j • U j) (exponentialTaylorPolynomial τ (K + 1)) -
            hamiltonianEvolution (∑ j, c j • U j) τ‖ ≤ (1 / 2 : ℝ) ^ K)

/-- The four Pauli symbols for identity, X, Y, and Z. -/
inductive PauliLetter where
  | i | x | y | z
  deriving DecidableEq, Repr

/-- An assignment of a Pauli symbol to each of `n` qubit positions. -/
def PauliTerm (n : ℕ) : Type := Fin n → PauliLetter

/-- The gate budget expression for selecting among `L` Pauli terms on `n` qubits with parameter
`K`. -/
def pauliSelectGateBudget (n L K : ℕ) : ℕ :=
  K * (L * (8 * n + 8 * Nat.clog 2 (max 2 L) + 64) + 64)

/-- The output bit and complex phase of a single Pauli symbol acting on a computational basis
bit. -/
def pauliLetterAct (p : PauliLetter) (b : Bool) : Bool × ℂ :=
  match p with
  | .i => (b, 1)
  | .x => (!b, 1)
  | .y => (!b, if b then -Complex.I else Complex.I)
  | .z => (b, if b then -1 else 1)

/-- The componentwise basis bit action of a Pauli term together with the product of its local
phases. -/
def pauliTermAct {n : ℕ} (t : PauliTerm n) (r : Reg n) : Reg n × ℂ :=
  ((fun i => (pauliLetterAct (t i) (r i)).1),
    ∏ i, (pauliLetterAct (t i) (r i)).2)

/-- Concatenates two Boolean registers using the finite sum index equivalence. -/
def simCat {a b : ℕ} (x : Reg a) (y : Reg b) : Reg (a + b) :=
  fun i => (finSumFinEquiv.symm i).elim x y

/-- Concatenates three Boolean registers in order. -/
def simCat3 {a b c : ℕ} (x : Reg a) (y : Reg b) (z : Reg c) : Reg (a + b + c) :=
  simCat (simCat x y) z

/-- The binary register representation of a finite index at width `Nat.clog 2 (max 2 L)`. -/
def indexBits (L : ℕ) (ℓ : Fin L) : Reg (Nat.clog 2 (max 2 L)) :=
  fun i => (ℓ.val.testBit i)

/-- Requires a legal finite gate word within the stated budget that applies the selected Pauli
term when the activity bit is true and preserves the basis input when it is false. -/
def HasPauliSelectAccess (n L K : ℕ) (terms : Fin L → PauliTerm n) : Prop :=
  ∃ (w : ℕ) (gs : List FiniteGateCode),
    finiteWordLegal w gs = true ∧
      gs.length ≤ pauliSelectGateBudget n L K ∧
      Nat.clog 2 (max 2 L) + 1 + n ≤ w ∧
      (∀ (ℓ : Fin L) (b : Reg n) (active : Bool),
        let lb := Nat.clog 2 (max 2 L)
        let input : Reg w :=
          simPad w (lb + 1 + n) (simCat (simCat (indexBits L ℓ) (fun _ : Fin 1 => active)) b)
        let act := pauliTermAct (terms ℓ) b
        ∃ φ : QState (Reg w),
          finiteWordRun w gs (Ket input) = some φ ∧
            (active = true →
              φ = (act.2 : ℂ) • Ket (simPad w (lb + 1 + n)
                (simCat (simCat (indexBits L ℓ) (fun _ : Fin 1 => true)) act.1))) ∧
            (active = false → φ = Ket input))

/-- The supremum of the norms of all entries of the finite matrix `H`. -/
noncomputable def sparseMaxEntry {n : ℕ} (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : ℝ :=
  ⨆ (i : Fin (2 ^ n)) (j : Fin (2 ^ n)), ‖H i j‖

/-- Requires the supplied row positions and values to match matrix entries, at most `d` nonzero
entries per row, and the stated entry norm bound. -/
def SparseRowOracle (n d : ℕ) (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (f : Fin (2 ^ n) → Fin d → Fin (2 ^ n)) (v : Fin (2 ^ n) → Fin d → ℂ) : Prop :=
  (∀ i k, H i (f i k) = v i k) ∧
    (∀ i, (Finset.univ.filter (fun j => H i j ≠ 0)).card ≤ d) ∧
    (∀ i j, ‖H i j‖ ≤ sparseMaxEntry H)

/-- The sparse segment gate budget expression determined by `n` and the logarithmic precision
term in `2 * T / ε`. -/
noncomputable def sparseSegmentGateBudget (n : ℕ) (T ε : ℝ) : ℕ :=
  64 * n * (Nat.clog 2 (Nat.ceil (2 * T / ε)) ^ 2 + 1) + 64

/-- Sparse decomposition parameters with a prescribed `gamma` for positive time and an upper
bound on the number of parts. -/
structure SparseEqParts (n d : ℕ) (t ε : ℝ) (Hmax : ℝ) where

  gamma : ℝ

  L : ℕ

  gamma_eq : t > 0 → gamma = ε / (8 * t)

  L_bound : L ≤ 8 * d * d * Hmax * t / ε + 1

/-- Encodes an index below `2 ^ n` as its `n` binary bits. -/
def finBits (n : ℕ) (x : Fin (2 ^ n)) : Reg n :=
  fun i => x.val.testBit i

/-- Requires sparse row data, a positive error parameter at most one half, and a well formed
oracle circuit with the specified basis row lookup action, query count, gate budget, and
workspace lower bound. -/
def HasSparseOracleSimulation (n d : ℕ) (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (f : Fin (2 ^ n) → Fin d → Fin (2 ^ n)) (v : Fin (2 ^ n) → Fin d → ℂ)
    (t ε : ℝ) (parts : SparseEqParts n d t ε (sparseMaxEntry H)) : Prop :=
  SparseRowOracle n d H f v ∧
    0 < ε ∧ ε ≤ 1 / 2 ∧
      ∃ (w : ℕ) (body : List (AdjointStep (Reg w))) (O : Matrix (Reg w) (Reg w) ℂ),
        WellFormedAdjointCircuit body ∧
          O ∈ Matrix.unitaryGroup (Reg w) ℂ ∧
          (∀ (x : Fin (2 ^ n)) (k : Fin d),
            O *ᵥ Ket (simPad w (n + Nat.clog 2 (max 2 d) + n)
                (simCat3 (finBits n x) (indexBits d k) (finBits n 0))) =
              Ket (simPad w (n + Nat.clog 2 (max 2 d) + n)
                (simCat3 (finBits n x) (indexBits d k) (finBits n (f x k))))) ∧
          1 ≤ adjointQueryCount body ∧
          adjointQueryCount body ≤ 2 * (Nat.clog 2 (max 2 parts.L) + 2) ∧
          adjointGateCount body ≤
            sparseSegmentGateBudget n (t * sparseMaxEntry H * (d : ℝ) ^ 2) ε ∧
          n + Nat.clog 2 (max 2 parts.L) + 2 * n + 16 ≤ w ∧
          (∀ (x : Fin (2 ^ n)) (k : Fin d),
            evaluate O body *ᵥ Ket (simPad w (n + Nat.clog 2 (max 2 d) + n)
                (simCat3 (finBits n x) (indexBits d k) (finBits n 0))) =
              Ket (simPad w (n + Nat.clog 2 (max 2 d) + n)
                (simCat3 (finBits n x) (indexBits d k) (finBits n (f x k)))))

/-- Multiplies Hamiltonian samples at the selected grid times, sorted in descending time index
order. -/
noncomputable def cubeTimeOrderedProd {I : Type} [Fintype I] [DecidableEq I]
    {M k : ℕ} (H : ℝ → Matrix I I ℂ) (τ : ℝ) (t : Fin k → Fin M) : Matrix I I ℂ :=
  (((List.ofFn (fun a : Fin k => ((t a : ℕ), H (τ * (t a : ℝ) / (M : ℝ)))))
      |>.mergeSort (fun x y => y.1 ≤ x.1)).map (·.2)).prod

/-- The cube grid time ordered Taylor sum through order `K`, with factorial and grid
normalization factors [BerryEtAl2015Taylor]. -/
noncomputable def equation28CubeSegment {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (τ : ℝ) (M K : ℕ) : Matrix I I ℂ :=
  ∑ k ∈ Finset.range (K + 1),
    (((-Complex.I * (τ : ℂ)) ^ k / ((k.factorial : ℕ) : ℂ) / ((M : ℂ) ^ k)) : ℂ) •
      ∑ t : Fin k → Fin M, cubeTimeOrderedProd H τ t

/-- The ancilla size expression `1 + K * Nat.clog 2 (max 1 L) + K * Nat.clog 2 (max 1 M)`. -/
def timeDependentAncillaBits (K L M : ℕ) : ℕ :=
  1 + K * Nat.clog 2 (max 1 L) + K * Nat.clog 2 (max 1 M)

/-- The time grid size expression `Nat.ceil ((2 * Λ ^ 2 + L) * τ ^ 2 / ε) + 1`. -/
noncomputable def effectiveTimeGrid (Λ L τ ε : ℝ) : ℕ :=
  Nat.ceil ((2 * Λ ^ 2 + L) * τ ^ 2 / ε) + 1

/-- Requires a well formed circuit and its adjoint to each have exactly `3 * K` queries and
satisfy the specified common gate bound. -/
def HasTimeDependentSegmentRates {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (K L M : ℕ) : Prop := by
  classical
  exact
    ∃ (body : List (AdjointStep
          (TaylorWordLabel J K × (Bool × ((Fin K → Fin M) × (J × I)))))),
      WellFormedAdjointCircuit body ∧
        adjointQueryCount body = 3 * K ∧
        adjointGateCount body ≤
          (3 * K + 3) * (64 * Nat.clog 2 (max 2 L) + 64 * Nat.clog 2 (max 2 M) + 512) + 1024 ∧
        adjointQueryCount (adjointCircuit body) = 3 * K ∧
        adjointGateCount (adjointCircuit body) ≤
          (3 * K + 3) * (64 * Nat.clog 2 (max 2 L) + 64 * Nat.clog 2 (max 2 M) + 512) + 1024

/-- The linear reset expression mapping an operator to its trace times the all false basis
projector. -/
noncomputable def physicalResetChannel (a : ℕ) :
    Matrix (Reg a) (Reg a) ℂ → Matrix (Reg a) (Reg a) ℂ :=
  fun σ => Matrix.trace σ • vecOuter (Ket (fun _ : Fin a => false))

/-- Requires a legal bounded length gate word that transfers a basis register into an initially
zero companion register and resets the original register to zero. -/
def HasPhysicalResetDiscard (a : ℕ) : Prop :=
  ∃ (w : ℕ) (gs : List FiniteGateCode),
    finiteWordLegal w gs = true ∧
      a + a ≤ w ∧
      gs.length ≤ 8 * a + 8 ∧
      (∀ r : Reg a,
        finiteWordRun w gs
            (Ket (simPad w (a + a) (simCat r (fun _ : Fin a => false)))) =
          some (Ket (simPad w (a + a) (simCat (fun _ : Fin a => false) r))))

/-- The storage expression `L * (magBits + phaseBits)` for coefficient data. -/
def integerDataBits (L magBits phaseBits : ℕ) : ℕ := L * (magBits + phaseBits)

/-- Combines a physical reset transfer contract with per segment reset cost and peak space
accounting for Taylor ancillas and integer data. -/
def HasSourceResetDiscardProgram (r K L magBits phaseBits : ℕ) : Prop :=
  HasPhysicalResetDiscard (simTaylorAncillaBits K L + 1) ∧
    (∃ (perSegment peakSpace : ℕ),
      perSegment ≤ 8 * (simTaylorAncillaBits K L + 1) + 8 ∧
        peakSpace = simTaylorAncillaBits K L + 1 + integerDataBits L magBits phaseBits ∧
        (0 < r → r * perSegment ≤ r * (8 * (simTaylorAncillaBits K L + 1) + 8)))

/-- Requires legal finite gate approximations to every qubit unitary on basis inputs, with
squared error at most `ε ^ 2` and length bounded by a width dependent constant times
`Nat.ceil ((1 / ε) ^ 2) + 1`. -/
def HasFixedGateBackend : Prop :=
  ∃ C : ℕ → ℕ,
    ∀ (w : ℕ) (U : Matrix (Reg w) (Reg w) ℂ),
      U ∈ Matrix.unitaryGroup (Reg w) ℂ →
        ∀ ε : ℝ, 0 < ε →
          ∃ gs : List FiniteGateCode,
            finiteWordLegal w gs = true ∧
              gs.length ≤ C w * (Nat.ceil (((1 : ℝ) / ε) ^ 2) + 1) ∧
              ∀ r : Reg w, ∃ φ : QState (Reg w),
                finiteWordRun w gs (Ket r) = some φ ∧
                  ∑ i, ‖φ i - (U *ᵥ Ket r) i‖ ^ 2 ≤ ε ^ 2

/-- Specifies well formed factorial Taylor evolution words with exact forward and adjoint query
and gate counts and relative embedded evolution error at most `(1 / 2) ^ k` under the stated
Hermitian unitary and coefficient bounds. -/
def factorialWordQPEConsumer : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
      (h : J → ℝ) (U : J → Matrix I I ℂ) (j₀ : J) (t : ℝ) (Λ T k : ℕ),
    (∀ j, U j ∈ unitaryGroup I ℂ ∧ (U j).IsHermitian) →
      (∑ j, |h j|) ≤ Λ → |t| ≤ T →
        let s := taylorSegments Λ T
        let K := factorialTaylorCutoff (factorialTaylorPrecision s k)
        let cs := factorialTaylorWord (I := I) h j₀ t Λ T k
        WellFormedAdjointCircuit cs ∧
          adjointQueryCount cs = 3 * s * K ∧
          adjointGateCount cs = s * (6 * K + 13) ∧
          adjointQueryCount (adjointCircuit cs) = 3 * s * K ∧
          adjointGateCount (adjointCircuit cs) = s * (6 * K + 13) ∧
          (∀ ψ : QState I,
            ‖toEuclidean_fromVec
              (evaluate (taylorQuery U K) cs *ᵥ (taylorFrame j₀ K *ᵥ ψ) -
                taylorFrame j₀ K *ᵥ (hamiltonianEvolution (∑ j, (h j : ℂ) • U j) t *ᵥ ψ))‖ ≤
              (1 / 2 : ℝ) ^ k * ‖toEuclidean_fromVec ψ‖)

end Qatlib.Concepts.RiskEstimation.PopulationGap
