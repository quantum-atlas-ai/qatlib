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

/-!
# Paid oracle words and tunable amplification models

This module defines oracle words, their matrix semantics, output states, and cost measures
through `Step`, `Word`, `wordMatrix`, and `weightedCost`. It also defines the clock and stage
legality conditions, recursively nested amplification words, threshold schedules, and amplitude
quantities used in variable-time linear-system readout specifications.

The clocked amplification and cost models are motivated by variable-time amplitude amplification
[Ambainis2012]. For tunable VTAA schedules, see [LowSu2026].

## Main statements

* `wordMatrix`: Interprets a word as a matrix acting on the data and clock registers.
* `nestedWord`: Builds a recursively amplified sequence of stages.
* `tunable`: Requires minimal round counts for the prescribed thresholds.
* `quasinorm23`: Defines the nonnegative-part 2/3 quasinorm used in cost allocation.

## References

* [Ambainis, 2012][Ambainis2012]
* [Low and Su, 2026][LowSu2026]
-/

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

/-- The joint index type of the data register and an `r`-valued clock register. -/
abbrev Space (H : Type) (r : ℕ) := H × Fin r

/-- A word step is either a known matrix on the joint space or an oracle call specified by a
slot, a set of clock values, and an adjoint flag. -/
inductive Step (H : Type) (r : ℕ) where
  | known : Matrix (Space H r) (Space H r) ℂ → Step H r
  | call : ℕ → Finset (Fin r) → Bool → Step H r

/-- An oracle word is a finite list of steps on the data and clock registers. -/
abbrev Word (H : Type) (r : ℕ) := List (Step H r)

/-- The number of calls to a given oracle slot in a word, counting both forward and adjoint
calls. -/
def calls {H : Type} {r : ℕ} (C : Word H r) (slot : ℕ) : ℕ :=
  C.countP (fun s =>  match s with | .call i _ _ =>  i=slot | _ =>  false)

/-- The number of known-matrix steps in a word. -/
def gateCount {H : Type} {r : ℕ} (C : Word H r) : ℕ :=
  C.countP (fun s =>  match s with | .known _ =>  true | _ =>  false)

/-- A word is legal when every known matrix is unitary and every oracle index is below the
number of available slots. -/
def legal {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (slots : ℕ) (C : Word H r) : Prop :=
  ∀ s ∈ C, match s with
    | .known U =>  U ∈ Matrix.unitaryGroup _ ℂ
    | .call i _ _ =>  i < slots

/-- The matrix acting as `U` on clock sectors in `T` and as the identity on the other sectors,
without mixing clock values. -/
def controlled {H : Type} [DecidableEq H] {r : ℕ}
    (U : Matrix H H ℂ) (T : Finset (Fin r)) : Matrix (Space H r) (Space H r) ℂ :=
  fun p t =>  if p.2=t.2 then
    if p.2 ∈ T then U p.1 t.1 else if p.1=t.1 then 1 else 0
  else 0

/-- The matrix interpretation of a word, applying its known matrices and controlled oracle calls
in list order. -/
def wordMatrix {H : Type} [Fintype H] [DecidableEq H] {r : ℕ}
    (oracles : ℕ → Matrix H H ℂ) (C : Word H r) : Matrix (Space H r) (Space H r) ℂ :=
  (C.map (fun s =>  match s with
    | .known U =>  U
    | .call i T adj =>  controlled (if adj then (oracles i)ᴴ else oracles i) T)).reverse.prod

/-- The formal adjoint word reverses the step order, conjugate-transposes known matrices, and
reverses oracle adjoint flags. -/
def wordAdjoint {H : Type} {r : ℕ} (C : Word H r) : Word H r :=
  C.reverse.map (fun s =>  match s with | .known U =>  .known Uᴴ | .call i T a =>  .call i T (!a))

/-- The embedding of a data state into clock value zero, with zero amplitudes in all other clock
sectors. -/
def clean {H : Type} (r : ℕ) (hr : 0 < r) (ψ : QState H) : QState (Space H r) :=
  fun p =>  if p.2=⟨0,hr⟩ then ψ p.1 else 0

/-- The Euclidean norm of a finite complex state vector. -/
def normVec {H : Type} [Fintype H] (ψ : QState H) : ℝ := ‖toEuclidean_fromVec ψ‖
/-- The state vector scaled by the inverse of its norm, with the zero vector sent to zero. -/
def normState {H : Type} [Fintype H] (ψ : QState H) : QState H :=
  ((normVec ψ : ℂ)⁻¹) • ψ

/-- The state obtained by applying a word's matrix interpretation to the clean embedding of the
input state. -/
def run {H : Type} [Fintype H] [DecidableEq H] {r : ℕ} (hr : 0 < r)
    (oracles : ℕ → Matrix H H ℂ) (C : Word H r) (ω : QState H) : QState (Space H r) :=
  wordMatrix oracles C *ᵥ clean r hr ω

/-- The output state in clock sector `k`, compressed through the conjugate transpose of `R`. -/
def outputBranch {H I : Type} [Fintype H] {r : ℕ}
    (R : Matrix H I ℂ) (ψ : QState (Space H r)) (k : Fin r) : QState I :=
  Rᴴ *ᵥ (fun h =>  ψ (h,k))

/-- The sum of squared norms of the compressed output branches over the selected clock values. -/
def outputMass {H I : Type} [Fintype H] [Fintype I] {r : ℕ}
    (R : Matrix H I ℂ) (T : Finset (Fin r)) (ψ : QState (Space H r)) : ℝ :=
  ∑ k ∈ T, (normVec (outputBranch R ψ k))^2

/-- The rank-at-most-one matrix with entries `ψ i * star (ψ j)`. -/
def pureDensity {I : Type} (ψ : QState I) : Matrix I I ℂ :=
  fun i j =>  ψ i * star (ψ j)

/-- The sum of the selected output branches' pure density matrices, divided by their total
output mass. -/
def outputDensity {H I : Type} [Fintype H] [Fintype I] {r : ℕ}
    (R : Matrix H I ℂ) (T : Finset (Fin r)) (ψ : QState (Space H r)) : Matrix I I ℂ :=
  ((outputMass R T ψ : ℂ)⁻¹) • ∑ k ∈ T, pureDensity (outputBranch R ψ k)

/-- The output guarantee requires selected output mass greater than `1 / 2` and trace-norm error
at most `ε` from the normalized target's pure density matrix. -/
def stateGuarantee {H I : Type} [Fintype H] [Fintype I] [DecidableEq I] {r : ℕ}
    (R : Matrix H I ℂ) (T : Finset (Fin r)) (ψ : QState (Space H r))
    (target : QState I) (ε : ℝ) : Prop :=
  1/2 < outputMass R T ψ ∧
    Matrix.traceNorm (outputDensity R T ψ-pureDensity (normState target)) ≤ ε

/-- The oracle family assigning `A` to slot zero and `B` to every other slot. -/
def pairOracles {H : Type} (A B : Matrix H H ℂ) : ℕ → Matrix H H ℂ :=
  fun i =>  if i=0 then A else B

/-- The zero-clock matrix corner compressed between the output frame `L` and input frame `R`. -/
def projectedCorner {H I O : Type} [Fintype H] [Fintype I] {r : ℕ}
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (hr : 0 < r)
    (M : Matrix (Space H r) (Space H r) ℂ) : Matrix O I ℂ :=
  fun o i =>  ∑ h, ∑ t, star (L h o)*M (h,⟨0,hr⟩) (t,⟨0,hr⟩)*R t i

/-- The regularized logarithmic price `Real.log (2 + max 0 x)`. -/
def logPrice (x : ℝ) : ℝ := Real.log (2+max 0 x)
/-- The inverse-transformation price `κ * logPrice (1 / ε)`. -/
def inversePrice (κ ε : ℝ) : ℝ := κ*logPrice (1/ε)
/-- The norm-estimation oracle price obtained by multiplying `κ` by logarithmic and iterated
logarithmic factors in `1 / Real.sqrt α`. -/
def normEstimationAPrice (κ α : ℝ) : ℝ :=
  κ*logPrice (1/Real.sqrt α)*logPrice (logPrice (1/Real.sqrt α))
/-- The linear-system oracle price `κ * logPrice z * logPrice (logPrice z / ε)`. -/
def qlsAPrice (κ z ε : ℝ) : ℝ := κ*logPrice z*logPrice (logPrice z/ε)

/-- The linear-access promise combines positive scaling bounds, a projected unitary encoding of
scaled `A`, unitary preparation of normalized `b`, consistency, and a pseudoinverse norm
bound. -/
def linearAccess {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (UA UB : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (ω : QState H) (b : QState O) (αA αInv : ℝ) : Prop :=
  0 < αA ∧ 0 < αInv ∧ 1 ≤ αA*αInv ∧
  ProjectedUnitaryEncoding ((αA : ℂ)⁻¹ • A) UA L R ∧
  UB ∈ Matrix.unitaryGroup H ℂ ∧ UB *ᵥ ω=L *ᵥ b ∧ Normalized b ∧
  (∃ z : QState I, A *ᵥ z=b) ∧ ‖matrixPseudoinverse A‖ ≤ αInv

/-- The squared norm of `matrixPseudoinverse A *ᵥ b`, divided by `αInv` squared. -/
def successProbability {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    (A : Matrix O I ℂ) (b : QState O) (αInv : ℝ) : ℝ :=
  (normVec (matrixPseudoinverse A *ᵥ b)/αInv)^2

/-- A legal clock is an increasing family of orthogonal projectors from zero to identity,
commuting with an orthogonal bad-state projector. -/
def clockLegal {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ) : Prop :=
  (∀ j, IsOrthogonalProjector (P j)) ∧ P 0=0 ∧ P ⟨m,by omega⟩=1 ∧
  (∀ j k, j.val ≤ k.val → (P k-P j).PosSemidef) ∧
  IsOrthogonalProjector bad ∧ ∀ j, P j*bad=bad*P j

/-- The potential matrix `1 - P * bad`, excluding the stopped bad component when the projectors
are compatible. -/
def potential {H : Type} [Fintype H] [DecidableEq H]
    (P bad : Matrix H H ℂ) : Matrix H H ℂ := 1-P*bad

/-- Legal stages are unitary through index `m` and fix the range of the preceding clock
projector at each subsequent stage. -/
def stageLegal {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (U : ℕ → Matrix H H ℂ) : Prop :=
  (∀ j : Fin (m+1), U j.val ∈ Matrix.unitaryGroup H ℂ) ∧
  ∀ j : Fin m, U (j.val+1)*P ⟨j.val,by omega⟩=P ⟨j.val,by omega⟩

/-- The one-step word calling oracle slot `j` forward on all clock values. -/
def stageWord {H : Type} (j : ℕ) : Word H 1 := [.call j Finset.univ false]
/-- The unamplified word calling oracle slots zero through `j` in order. -/
def plainPrefix {H : Type} (j : ℕ) : Word H 1 :=
  (List.range (j+1)).map (fun k =>  .call k Finset.univ false)

/-- The pure density matrix of the seed state, which is an orthogonal projector when the seed is
normalized. -/
def seedProjector {H : Type} (ω : QState H) : Matrix H H ℂ := pureDensity ω

/-- The word applying `B` followed by `r` amplification rounds using the target and seed
reflections and a negative identity gate. -/
def aaWord {H : Type} [Fintype H] [DecidableEq H]
    (B : Word H 1) (ω : QState H) (G : Matrix H H ℂ) (r : ℕ) : Word H 1 :=
  B ++ (List.replicate r
    ([.known (controlled (ReflectionAbout G) Finset.univ)] ++ wordAdjoint B ++
      [.known (controlled (ReflectionAbout (seedProjector ω)) Finset.univ)] ++ B ++
      [.known (-1)])).flatten

/-- The recursively amplified word starting at stage zero and amplifying each appended stage
with its potential projector and prescribed round count. -/
def nestedWord {H : Type} [Fintype H] [DecidableEq H]
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (ω : QState H)
    (rounds : ℕ → ℕ) : ℕ → Word H 1
  | 0 =>  stageWord 0
  | j+1 =>  aaWord (nestedWord P bad ω rounds j ++ stageWord (j+1))
      ω (potential (P (j+1)) bad) (rounds (j+1))

/-- The extension of a finite clock to natural indices, held constant at its final projector
beyond stage `m`. -/
def extendClock {H : Type} (m : ℕ) (P : Fin (m+1) → Matrix H H ℂ) : ℕ → Matrix H H ℂ :=
  fun j =>  if h : j ≤ m then P ⟨j,by omega⟩ else P ⟨m,by omega⟩

/-- The data-state slice at clock value zero after running a word with a single clock value. -/
def clockState {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (C : Word H 1) (ω : QState H) : QState H :=
  fun h =>  run (by omega) U C ω (h,0)

/-- The potential norm after appending stage `j + 1` to the nested word through stage `j`,
before amplifying that new stage. -/
def preAmplitude {H : Type} [Fintype H] [DecidableEq H]
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (ω : QState H)
    (U : ℕ → Matrix H H ℂ) (rounds : ℕ → ℕ) (j : ℕ) : ℝ :=
  normVec (potential (P (j+1)) bad *ᵥ
    clockState U (nestedWord P bad ω rounds j ++ stageWord (j+1)) ω)

/-- The potential norm of the nested word through stage `j`. -/
def postAmplitude {H : Type} [Fintype H] [DecidableEq H]
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (ω : QState H)
    (U : ℕ → Matrix H H ℂ) (rounds : ℕ → ℕ) (j : ℕ) : ℝ :=
  normVec (potential (P j) bad *ᵥ clockState U (nestedWord P bad ω rounds j) ω)

/-- The ratio of the sine-amplified amplitude to the linearized amplitude, defined to be one
when the input amplitude is zero. -/
def gainLoss (ρ : ℕ) (a : ℝ) : ℝ :=
  if a=0 then 1 else Real.sin (ρ*Real.arcsin a)/(ρ*a)

/-- The sum of the assigned prices of all oracle calls in a word, with zero cost for
known-matrix steps. -/
def weightedCost {H : Type} {r : ℕ} (prices : ℕ → ℕ) (C : Word H r) : ℕ :=
  (C.map (fun s =>  match s with | .call j _ _ =>  prices j | _ =>  0)).sum

/-- The 3/2 power of the sum of the 2/3 powers of the nonnegative parts of the weights. -/
def quasinorm23 {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  (∑ j, (max 0 (w j)).rpow (2/3)).rpow (3/2)

/-- The forward-call word for oracle slots `j + 1` through `k`, empty when `k ≤ j`. -/
def suffixWord {H : Type} (j k : ℕ) : Word H 1 :=
  (List.range (k-j)).map (fun i =>  .call (j+i+1) Finset.univ false)

/-- The state obtained by running the suffix word from stage `j + 1` through stage `k` on the
supplied state. -/
def suffixState {H : Type} [Fintype H] [DecidableEq H]
    (U : ℕ → Matrix H H ℂ) (j k : ℕ) (ψ : QState H) : QState H :=
  clockState U (suffixWord j k) ψ

/-- The potential norm after the unamplified prefix through stage `j`. -/
def plainAmplitude {H : Type} [Fintype H] [DecidableEq H]
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (j : ℕ) : ℝ :=
  normVec (potential (P j) bad *ᵥ clockState U (plainPrefix j) ω)

/-- A tunable schedule has initial threshold one and chooses at each stage the least round count
reaching the square-root threshold divided by three in the linearized amplitude. -/
def tunable {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ) : Prop :=
  α 0=1 ∧ ∀ j < m,
    0 ≤ α (j+1) ∧
    Real.sqrt (α (j+1))/3 ≤ (2*rs (j+1)+1)*preAmplitude P bad ω U rs j ∧
    ∀ s < rs (j+1), (2*s+1)*preAmplitude P bad ω U rs j < Real.sqrt (α (j+1))/3

/-- The product of the stage gain loss factors through stage `m`. -/
def totalLoss {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (rs : ℕ → ℕ) : ℝ :=
  ∏ j : Fin m, gainLoss (2*rs (j.val+1)+1) (preAmplitude P bad ω U rs j.val)

/-- The reconstructed threshold is one at zero, zero at a positive stage with no rounds, and
nine times the squared linearized pre-amplitude otherwise. -/
def reverseThreshold {H : Type} [Fintype H] [DecidableEq H]
    (P : ℕ → Matrix H H ℂ) (bad : Matrix H H ℂ) (U : ℕ → Matrix H H ℂ)
    (ω : QState H) (rs : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j=0 then 1 else if rs j=0 then 0 else
    9*((2*rs j+1 : ℕ) : ℝ)^2*(preAmplitude P bad ω U rs (j-1))^2

/-- The sum of stage prices over indices strictly greater than `a` and at most `min b m`. -/
def blockFee (prices : ℕ → ℕ) (m a b : ℕ) : ℕ :=
  ∑ j : Fin (m+1), if a < j.val ∧ j.val ≤ min b m then prices j.val else 0

end Qatlib.Concepts.QlsReadoutSpec.Amplification
