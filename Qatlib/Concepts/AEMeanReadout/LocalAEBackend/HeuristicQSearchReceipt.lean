/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.UnboundedSourceSearch
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchBudget

/-!
# Receipts for heuristic quantum search

This module lifts a seed-based heuristic to reversible computation and validated quantum search,
following the amplitude-amplification framework of [BrassardEtAl2002]. `consumer` records the
raw search outcome together with the heuristic output, while `Prices` and `totalCost` account
separately for preparation, phase queries, validation, and heuristic computation.

The source and shifted depth conventions share soundness, ledger identities, finite execution
semantics, and geometric failure bounds. For positive initial success probability, the
finite-horizon failure probability tends to zero.

## Main statements

* `compute_phase_uncompute`: implement the good-seed phase oracle with clean workspace.
* `frontier1`: combine receipt soundness and ledger identities with an expected cost bound.
* `consumer_terminates`: show failure tends to zero as the search horizon grows.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.HeuristicQSearchReceipt
open Matrix
open scoped Classical BigOperators ENNReal

variable {R Y : Type} [Fintype R] [DecidableEq R] [Fintype Y] [DecidableEq Y]

/-- The seeds whose heuristic output satisfies the Boolean predicate `F`. -/
def goodSeeds (F : Y → Bool) (G : (Y → Bool) → R → Y) : Finset R :=
  Finset.univ.filter fun r => F (G F r) = true

/-- The reversible map that preserves the seed and swaps the workspace value `y₀` with `G F r`. -/
def computeSwap (F : Y → Bool) (G : (Y → Bool) → R → Y) (y₀ : Y) (z : R × Y) : R × Y :=
  (z.1, Equiv.swap y₀ (G F z.1) z.2)

/-- Applying `computeSwap` twice restores both the seed and workspace. -/
theorem compute_involutive (F : Y → Bool) (G : (Y → Bool) → R → Y) (y₀ : Y) :
    Function.Involutive (computeSwap F G y₀) := by
  intro z
  simp [computeSwap]

/-- The permutation matrix implementing `computeSwap` on the seed and workspace registers. -/
def computeMatrix (F : Y → Bool) (G : (Y → Bool) → R → Y) (y₀ : Y) :
    Matrix (R × Y) (R × Y) ℂ := permMatrix (computeSwap F G y₀)

/-- The reversible heuristic computation `computeMatrix` is unitary. -/
theorem compute_unitary (F : Y → Bool) (G : (Y → Bool) → R → Y) (y₀ : Y) :
    computeMatrix F G y₀ ∈ Matrix.unitaryGroup (R × Y) ℂ :=
  permMatrix_unitary (compute_involutive F G y₀)

/-- On a basis state with workspace `y₀`, `computeMatrix` writes the heuristic output `G F r`
and preserves the seed. -/
theorem compute_output (F : Y → Bool) (G : (Y → Bool) → R → Y) (y₀ : Y) (r : R) :
    ApplyGate (computeMatrix F G y₀) (Qatlib.Foundations.PureStateMath.Ket (r,y₀)) = Qatlib.Foundations.PureStateMath.Ket (r,G F r) := by
  rw [computeMatrix, applyGate_permMatrix_ket (compute_involutive F G y₀)]
  simp [computeSwap]

/-- Embed a seed state into the joint register with workspace fixed to `y₀`. -/
def cleanLift (y₀ : Y) (ψ : QState R) : QState (R × Y) :=
  fun z => if z.2 = y₀ then ψ z.1 else 0

/-- Computing the heuristic, querying its output in phase, and uncomputing implements the
good-seed phase oracle while restoring the clean workspace. -/
theorem compute_phase_uncompute (F : Y → Bool) (G : (Y → Bool) → R → Y)
    (y₀ : Y) (ψ : QState R) :
    ApplyGate ((computeMatrix F G y₀)ᴴ)
      (ApplyGate (PhaseOracle (fun z : R × Y => F z.2))
        (ApplyGate (computeMatrix F G y₀) (cleanLift y₀ ψ))) =
      cleanLift y₀ (ApplyGate (PhaseOracle (fun r => F (G F r))) ψ) := by
  ext z
  rw [computeMatrix, permMatrix_conjTranspose (compute_involutive F G y₀),
    applyGate_permMatrix (compute_involutive F G y₀), applyGate_phaseOracle,
    applyGate_permMatrix (compute_involutive F G y₀)]
  have hi := compute_involutive F G y₀ z
  rw [hi]
  by_cases hz : z.2 = y₀
  · simp [cleanLift, hz, computeSwap, applyGate_phaseOracle]
  · simp [cleanLift, hz]

/-- The heuristic computation matrix extended by the identity on a Boolean validation register. -/
def flagCompute (F : Y → Bool) (G : (Y → Bool) → R → Y) (y₀ : Y) :
    Matrix ((R × Y) × Bool) ((R × Y) × Bool) ℂ :=
  permMatrix (fun z => (computeSwap F G y₀ z.1, z.2))

/-- The heuristic workspace swap remains involutive when extended by an unchanged Boolean
register. -/
theorem flagCompute_involutive (F : Y → Bool) (G : (Y → Bool) → R → Y) (y₀ : Y) :
    Function.Involutive (fun z : (R × Y) × Bool => (computeSwap F G y₀ z.1,z.2)) := by
  intro z
  simp [compute_involutive F G y₀ z.1]

/-- The heuristic computation extended to the validation register is unitary. -/
theorem flagCompute_unitary (F : Y → Bool) (G : (Y → Bool) → R → Y) (y₀ : Y) :
    flagCompute F G y₀ ∈ Matrix.unitaryGroup ((R × Y) × Bool) ℂ :=
  permMatrix_unitary (flagCompute_involutive F G y₀)

/-- Compute-query-uncompute writes `F (G F r)` into an initially false flag and restores the
workspace to `y₀`. -/
theorem validation_action (F : Y → Bool) (G : (Y → Bool) → R → Y) (y₀ : Y) (r : R) :
    ApplyGate ((flagCompute F G y₀)ᴴ)
      (ApplyGate (BitOracleOn (fun z : R × Y => F z.2))
        (ApplyGate (flagCompute F G y₀) (Qatlib.Foundations.PureStateMath.Ket ((r,y₀),false)))) =
      Qatlib.Foundations.PureStateMath.Ket ((r,y₀),F (G F r)) := by
  rw [flagCompute, permMatrix_conjTranspose (flagCompute_involutive F G y₀),
    applyGate_permMatrix_ket (flagCompute_involutive F G y₀), applyGate_bitOracleOn_ket,
    applyGate_permMatrix_ket (flagCompute_involutive F G y₀)]
  simp [computeSwap]

/-- The validation circuit contains one oracle query and two ordinary gates. -/
theorem validation_counts (F : Y → Bool) (G : (Y → Bool) → R → Y) (y₀ : Y) :
    QueryCount ([Step.gate (flagCompute F G y₀), Step.query, Step.gate ((flagCompute F G y₀)ᴴ)] : Circuit ((R × Y) × Bool)) = 1 ∧
    GateCount ([Step.gate (flagCompute F G y₀), Step.query, Step.gate ((flagCompute F G y₀)ᴴ)] : Circuit ((R × Y) × Bool)) = 2 := by
  constructor <;> rfl

/-- The phase oracle for successful heuristic seeds equals the prepared marking reflection for
`goodSeeds`. -/
theorem good_phase_eq (F : Y → Bool) (G : (Y → Bool) → R → Y) :
    PhaseOracle (fun r => F (G F r)) = preparedMark (goodSeeds F G) := by
  ext i j
  simp only [PhaseOracle, preparedMark, Projector, Matrix.diagonal_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, goodSeeds, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases hij : i = j
  · subst j
    by_cases hf : F (G F i) = true <;> norm_num [hf]
  · simp [hij]
open Qatlib
/-- The choice between the source and shifted search-depth conventions. -/
inductive DepthConvention where
  | source
  | shifted
  deriving DecidableEq

/-- The costed search-round distribution selected by the depth convention. -/
def roundLaw (c : DepthConvention) (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ)
    (r₀ : R) (S : Finset R) (l : ℕ) : PMF (Option R × ℕ × ℕ) :=
  match c with
  | .source => sourceQSearchRound A hA r₀ S l
  | .shifted => shiftedQSearchRound A hA r₀ S l

/-- The finite-horizon search loop with the selected round law and starting offset. -/
def rawLoop (c : DepthConvention) (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ)
    (r₀ : R) (S : Finset R) (fuel off : ℕ) : PMF (Option R × ℕ × ℕ) :=
  windowLoop A hA r₀ S (roundLaw c A hA r₀ S) fuel off

/-- A raw optional seed and two cost counters, together with an optional heuristic output. -/
structure Receipt (R Y : Type) where
  raw : Option R × ℕ × ℕ
  output : Option Y

/-- Attach the heuristic image of the optional seed to a raw search outcome. -/
def makeReceipt (F : Y → Bool) (G : (Y → Bool) → R → Y)
    (out : Option R × ℕ × ℕ) : Receipt R Y := ⟨out, out.1.map (G F)⟩

/-- The receipt distribution obtained by searching for seeds in `goodSeeds` and mapping
successful seeds through the heuristic. -/
def consumer (c : DepthConvention) (F : Y → Bool) (G : (Y → Bool) → R → Y)
    (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ) (r₀ : R) (fuel off : ℕ) : PMF (Receipt R Y) :=
  (rawLoop c A hA r₀ (goodSeeds F G) fuel off).map (makeReceipt F G)

/-- Every supported consumer receipt obtains its output by applying `G F` to its raw optional
seed. -/
theorem receipt_origin (c : DepthConvention) (F : Y → Bool) (G : (Y → Bool) → R → Y)
    (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ) (r₀ : R) (fuel off : ℕ)
    (tr : Receipt R Y) (ht : tr ∈ (consumer c F G A hA r₀ fuel off).support) :
    tr.output = tr.raw.1.map (G F) := by
  obtain ⟨x, _, hx⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
  rw [← hx]
  rfl

/-- The forward preparation count recovered from the second raw cost counter. -/
def prepareForward (tr : Receipt R Y) : ℕ := tr.raw.2.2
/-- The adjoint preparation count given by the first raw cost counter minus the second. -/
def prepareAdjoint (tr : Receipt R Y) : ℕ := tr.raw.2.1 - tr.raw.2.2
/-- The phase-query count given by the difference of the two raw cost counters. -/
def phaseCalls (tr : Receipt R Y) : ℕ := tr.raw.2.1 - tr.raw.2.2
/-- The validation-query count given by twice the second raw counter minus the first. -/
def validationCalls (tr : Receipt R Y) : ℕ := 2*tr.raw.2.2 - tr.raw.2.1
/-- The forward heuristic-computation count, equal to the sum of phase and validation calls. -/
def gForward (tr : Receipt R Y) : ℕ := phaseCalls tr + validationCalls tr
/-- The adjoint heuristic-computation count, equal to the sum of phase and validation calls. -/
def gAdjoint (tr : Receipt R Y) : ℕ := phaseCalls tr + validationCalls tr

/-- Natural-number prices for preparation, unpreparation, phase queries, validation queries, and
forward and adjoint heuristic computation. -/
structure Prices where
  prepare : ℕ
  unprepare : ℕ
  phaseF : ℕ
  validateF : ℕ
  forwardG : ℕ
  adjointG : ℕ

/-- The sum of the six receipt operation counts weighted by their respective prices. -/
def totalCost (w : Prices) (tr : Receipt R Y) : ℕ :=
  w.prepare*prepareForward tr + w.unprepare*prepareAdjoint tr +
  w.phaseF*phaseCalls tr + w.validateF*validationCalls tr +
  w.forwardG*gForward tr + w.adjointG*gAdjoint tr

/-- Under the raw counter ratio bounds, preparation and predicate-query counts recover the raw
counters, and both heuristic counts equal the forward preparation count. -/
theorem ledger_identities (tr : Receipt R Y)
    (h₁ : tr.raw.2.2 ≤ tr.raw.2.1) (h₂ : tr.raw.2.1 ≤ 2*tr.raw.2.2) :
    prepareForward tr + prepareAdjoint tr = tr.raw.2.1 ∧
    phaseCalls tr + validationCalls tr = tr.raw.2.2 ∧
    gForward tr = prepareForward tr ∧ gAdjoint tr = prepareForward tr := by
  dsimp [prepareForward, prepareAdjoint, phaseCalls, validationCalls, gForward, gAdjoint]
  omega

/-- A direct successful receipt records one forward preparation, no adjoint preparation, one
validation, and one forward heuristic computation. -/
theorem direct_receipt (F : Y → Bool) (G : (Y → Bool) → R → Y) (r : R) :
    prepareForward (makeReceipt F G (some r,1,1)) = 1 ∧
    prepareAdjoint (makeReceipt F G (some r,1,1)) = 0 ∧
    validationCalls (makeReceipt F G (some r,1,1)) = 1 ∧
    gForward (makeReceipt F G (some r,1,1)) = 1 := by
  simp [prepareForward, prepareAdjoint, validationCalls, gForward, phaseCalls, makeReceipt]

/-- An amplified receipt with depth `k` records `k + 2` forward preparations, `k` adjoint
preparations and phase calls, two validations, and `k + 2` forward heuristic computations. -/
theorem amplified_receipt (F : Y → Bool) (G : (Y → Bool) → R → Y) (out : Option R) (k : ℕ) :
    prepareForward (makeReceipt F G (out,2+2*k,2+k)) = 2+k ∧
    prepareAdjoint (makeReceipt F G (out,2+2*k,2+k)) = k ∧
    phaseCalls (makeReceipt F G (out,2+2*k,2+k)) = k ∧
    validationCalls (makeReceipt F G (out,2+2*k,2+k)) = 2 ∧
    gForward (makeReceipt F G (out,2+2*k,2+k)) = k+2 := by
  dsimp [prepareForward, prepareAdjoint, phaseCalls, validationCalls, gForward, makeReceipt]
  omega

namespace LedgerBridge
variable {I : Type} [Fintype I] [DecidableEq I]

/-- If every trial ledger satisfies the counter ratio bounds, every supported window-round
outcome satisfies them as well. -/
theorem windowRound_ratio
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) (trial : Fin M → CostedLaw (I × ℕ))
    (ledger : Fin M → ℕ × ℕ)
    (hl : ∀ j, (ledger j).2 ≤ (ledger j).1 ∧ (ledger j).1 ≤ 2 * (ledger j).2)
    (out : Option I × ℕ × ℕ)
    (hout : out ∈ (windowRound A hA j₀ S M hM trial ledger).support) :
    out.2.2 ≤ out.2.1 ∧ out.2.1 ≤ 2 * out.2.2 := by
  rw [windowRound] at hout
  obtain ⟨st, _, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  by_cases hS : st.1.1 ∈ S
  · rw [if_pos hS] at hout
    have heq : out = (some st.1.1, 1, 1) := by
      simpa [PMF.mem_support_pure_iff] using! hout
    subst out
    norm_num
  · rw [if_neg hS] at hout
    obtain ⟨j, _, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    obtain ⟨st2, _, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    have heq : out = (if st2.1.1 ∈ S then some st2.1.1 else none,
        (ledger j).1, (ledger j).2) := by
      simpa [PMF.mem_support_pure_iff] using! hout
    subst out
    exact hl j

/-- Every supported source-round outcome has its first cost counter between the second counter
and twice that counter. -/
theorem sourceRound_ratio (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) (out : Option I × ℕ × ℕ)
    (hout : out ∈ (sourceQSearchRound A hA j₀ S l).support) :
    out.2.2 ≤ out.2.1 ∧ out.2.1 ≤ 2 * out.2.2 := by
  exact windowRound_ratio A hA j₀ S _ _ _ _ (fun _ => by dsimp; omega) out hout

/-- Every supported shifted-round outcome has its first cost counter between the second counter
and twice that counter. -/
theorem shiftedRound_ratio (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) (out : Option I × ℕ × ℕ)
    (hout : out ∈ (shiftedQSearchRound A hA j₀ S l).support) :
    out.2.2 ≤ out.2.1 ∧ out.2.1 ≤ 2 * out.2.2 := by
  exact windowRound_ratio A hA j₀ S _ _ _ _ (fun _ => by dsimp; omega) out hout

/-- Counter ratio bounds for all supported round outcomes are preserved by the finite window
loop. -/
theorem windowLoop_ratio
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (round : ℕ → PMF (Option I × ℕ × ℕ))
    (hr : ∀ l out, out ∈ (round l).support →
      out.2.2 ≤ out.2.1 ∧ out.2.1 ≤ 2 * out.2.2) :
    ∀ T off out, out ∈ (windowLoop A hA j₀ S round T off).support →
      out.2.2 ≤ out.2.1 ∧ out.2.1 ≤ 2 * out.2.2 := by
  intro T
  induction T with
  | zero =>
    intro off out hout
    have heq : out = (none, 0, 0) := by
      simpa [windowLoop, PMF.mem_support_pure_iff] using! hout
    subst out
    simp
  | succ T ih =>
    intro off out hout
    rw [windowLoop_succ_eq] at hout
    obtain ⟨r, hr', hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    have hratio := hr (off + 1) r hr'
    cases heq : r.1 with
    | some y =>
      rw [heq] at hout
      have ho : out = r := by simpa [PMF.mem_support_pure_iff] using! hout
      subst out
      exact hratio
    | none =>
      rw [heq] at hout
      obtain ⟨r', hr', ho⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
      have hi := ih (off + 1) r' hr'
      subst out
      dsimp
      omega

/-- Recover the two raw counters from their difference and complementary difference under the
counter ratio bounds. -/
theorem recover (c1 c2 : ℕ) (h1 : c2 ≤ c1) (h2 : c1 ≤ 2*c2) :
    c2 + (c1-c2) = c1 ∧
    (c1-c2) + (2*c2-c1) = c2 := by omega

/-- The window loop using shifted rounds equals the BHMT quantum-search loop. -/
theorem shiftedLoop_eq (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (T off : ℕ) :
    windowLoop A hA j₀ S (shiftedQSearchRound A hA j₀ S) T off
      = BHMTQSearch.qSearchLoop A hA j₀ S T off := by
  induction T generalizing off with
  | zero => rfl
  | succ T ih =>
    simp only [windowLoop_succ_eq, shiftedRound_eq_frozenRound, BHMTQSearch.qSearchLoop]
    congr 1
    funext out
    cases out.1 <;> simp only [ih]

/-- The failure probability for a nonempty window loop factors into the first round's failure
probability and the remaining loop's failure probability. -/
theorem windowLoop_none_succ
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (round : ℕ → PMF (Option I × ℕ × ℕ)) (T off : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (windowLoop A hA j₀ S round (T+1) off) (fun out => out.1=none)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (round (off+1)) (fun out => out.1=none) *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (windowLoop A hA j₀ S round T (off+1)) (fun out => out.1=none) := by
  classical
  rw [windowLoop_succ_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  have hsplit : ∀ out : Option I × ℕ × ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (match out.1 with
        | some _ => PMF.pure out
        | none => (windowLoop A hA j₀ S round T (off+1)).map
            (fun r => (r.1, r.2.1+out.2.1, r.2.2+out.2.2)))
        (fun out => out.1=none)
      = if out.1=none then
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (windowLoop A hA j₀ S round T (off+1)) (fun r => r.1=none)
        else 0 := by
    intro out
    cases h : out.1 with
    | none => simp only [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map, ite_true]
    | some y => simp only [h, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure,
        reduceCtorEq, ite_false]
  trans Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (round (off+1)) (fun out => if out.1=none then
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (windowLoop A hA j₀ S round T (off+1)) (fun r => r.1=none) else 0)
  · exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hsplit
  · rw [expectation_indicator_mul']
    exact mul_comm _ _

/-- The finite window loop's failure probability equals the product of the scheduled round
failure probabilities expressed by `reachMass`. -/
theorem windowLoop_none_eq_reachMass
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (round : ℕ → PMF (Option I × ℕ × ℕ)) (T off : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (windowLoop A hA j₀ S round T off) (fun out => out.1=none)
      = reachMass (fun l => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (round l) (fun out => out.1=none)) (off+1) T := by
  classical
  induction T generalizing off with
  | zero => simp [windowLoop, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, reachMass]
  | succ T ih => rw [windowLoop_none_succ, ih, reachMass_succ]

/-- The zero-offset source loop's failure probability equals `sourceSurvival` at the same
horizon. -/
theorem sourceLoop_none_eq_survival
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (T : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchLoop A hA j₀ S T 0) (fun out => out.1=none)
      = sourceSurvival A hA j₀ S T := by
  rw [sourceQSearchLoop, windowLoop_none_eq_reachMass, sourceSurvival_eq_reachMass]
  rfl

end LedgerBridge

/-- Every supported round outcome satisfies the counter ratio bounds for either depth
convention. -/
theorem round_ratio (c : DepthConvention) (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ)
    (r₀ : R) (S : Finset R) (l : ℕ) (out : Option R × ℕ × ℕ)
    (ho : out ∈ (roundLaw c A hA r₀ S l).support) : out.2.2 ≤ out.2.1 ∧ out.2.1 ≤ 2*out.2.2 := by
  cases c
  · exact LedgerBridge.sourceRound_ratio A hA r₀ S l out ho
  · exact LedgerBridge.shiftedRound_ratio A hA r₀ S l out ho

/-- Every seed returned by a supported round outcome belongs to the marked set `S`. -/
theorem round_sound (c : DepthConvention) (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ)
    (r₀ : R) (S : Finset R) (l : ℕ) (out : Option R × ℕ × ℕ)
    (ho : out ∈ (roundLaw c A hA r₀ S l).support) : ∀ r, out.1 = some r → r ∈ S := by
  cases c <;> exact windowRound_shape A hA r₀ S _ (qSearchWindow_pos l) _ _ out ho

/-- Supported consumer receipts satisfy the preparation, predicate-query, and
heuristic-computation ledger identities. -/
theorem consumer_ledgers (c : DepthConvention) (F : Y → Bool) (G : (Y → Bool) → R → Y)
    (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ) (r₀ : R) (fuel off : ℕ)
    (tr : Receipt R Y) (ht : tr ∈ (consumer c F G A hA r₀ fuel off).support) :
    prepareForward tr + prepareAdjoint tr = tr.raw.2.1 ∧
    phaseCalls tr + validationCalls tr = tr.raw.2.2 ∧
    gForward tr = prepareForward tr ∧ gAdjoint tr = prepareForward tr := by
  obtain ⟨x, hx, hxt⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
  have hr := LedgerBridge.windowLoop_ratio A hA r₀ (goodSeeds F G) _
    (round_ratio c A hA r₀ (goodSeeds F G)) fuel off x hx
  rw [← hxt]
  exact ledger_identities _ hr.1 hr.2

/-- Every output returned by a supported consumer receipt satisfies `F`. -/
theorem consumer_sound (c : DepthConvention) (F : Y → Bool) (G : (Y → Bool) → R → Y)
    (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ) (r₀ : R) (fuel off : ℕ)
    (tr : Receipt R Y) (ht : tr ∈ (consumer c F G A hA r₀ fuel off).support)
    (y : Y) (hy : tr.output = some y) : F y = true := by
  obtain ⟨x, hx, hxt⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
  rw [← hxt] at hy
  have hs := windowLoop_shape A hA r₀ (goodSeeds F G) _
    (round_sound c A hA r₀ (goodSeeds F G)) fuel off x hx
  cases hr : x.1 with
  | none => simp [makeReceipt, hr] at hy
  | some r =>
    have hy' : G F r = y := by
      simpa only [makeReceipt, hr, Option.map_some, Option.some.injEq] using! hy
    rw [← hy']
    exact (Finset.mem_filter.mp (hs r hr)).2

/-- The probability of an absent consumer output equals the scheduled product of round failure
probabilities. -/
theorem consumer_failure (c : DepthConvention) (F : Y → Bool) (G : (Y → Bool) → R → Y)
    (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ) (r₀ : R) (fuel off : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (consumer c F G A hA r₀ fuel off) (fun tr => tr.output = none) =
      reachMass (fun l => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (roundLaw c A hA r₀ (goodSeeds F G) l) (fun out => out.1=none))
        (off+1) fuel := by
  rw [consumer, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  simpa only [makeReceipt, Option.map_eq_none_iff] using!
    LedgerBridge.windowLoop_none_eq_reachMass A hA r₀ (goodSeeds F G) _ fuel off

/-- The sum of the six operation prices in `Prices`. -/
def priceSum (w : Prices) : ℕ := w.prepare+w.unprepare+w.phaseF+w.validateF+w.forwardG+w.adjointG

/-- Under the counter ratio bounds, the weighted receipt cost is at most `priceSum` times the
second raw cost counter. -/
theorem totalCost_le (w : Prices) (tr : Receipt R Y)
    (h₁ : tr.raw.2.2 ≤ tr.raw.2.1) (h₂ : tr.raw.2.1 ≤ 2*tr.raw.2.2) :
    totalCost w tr ≤ priceSum w * tr.raw.2.2 := by
  have hp : prepareAdjoint tr ≤ tr.raw.2.2 := by dsimp [prepareAdjoint]; omega
  have hq : phaseCalls tr ≤ tr.raw.2.2 := by dsimp [phaseCalls]; omega
  have hv : validationCalls tr ≤ tr.raw.2.2 := by dsimp [validationCalls]; omega
  have hg := (ledger_identities tr h₁ h₂).2.2
  unfold totalCost
  rw [hg.1, hg.2]
  dsimp [prepareForward]
  calc
    _ ≤ w.prepare*tr.raw.2.2+w.unprepare*tr.raw.2.2+w.phaseF*tr.raw.2.2+
        w.validateF*tr.raw.2.2+w.forwardG*tr.raw.2.2+w.adjointG*tr.raw.2.2 := by
      gcongr
    _ = _ := by dsimp [priceSum]; ring

/-- For positive initial marked probability `a`, the expected second raw cost counter is at most
`400 / √a`, uniformly in the finite horizon. -/
theorem rawLoop_budget (c : DepthConvention) (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ)
    (r₀ : R) (S : Finset R) (fuel : ℕ) (ha : 0 < MeasureProb (preparedAAState A r₀) S) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rawLoop c A hA r₀ S fuel 0) (fun out => (out.2.2 : ℝ≥0∞)) ≤
      ENNReal.ofReal (400/Real.sqrt (MeasureProb (preparedAAState A r₀) S)) := by
  cases c
  · exact sourceLoop_ledger2_expectation_le A hA r₀ S fuel ha
  · change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (windowLoop A hA r₀ S (shiftedQSearchRound A hA r₀ S) fuel 0) _ ≤ _
    rw [LedgerBridge.shiftedLoop_eq]
    exact ((BHMTQSearch.bhmt_theorem3_qsearch R A hA r₀ S fuel).2.2 ha).2

/-- For positive good-seed probability `a`, the expected consumer cost is at most `priceSum w`
times `400 / √a`. -/
theorem expected_cost (c : DepthConvention) (F : Y → Bool) (G : (Y → Bool) → R → Y)
    (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ) (r₀ : R) (fuel : ℕ) (w : Prices)
    (ha : 0 < MeasureProb (preparedAAState A r₀) (goodSeeds F G)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (consumer c F G A hA r₀ fuel 0) (fun tr => (totalCost w tr : ℝ≥0∞)) ≤
      (priceSum w : ℝ≥0∞) * ENNReal.ofReal (400/Real.sqrt (MeasureProb (preparedAAState A r₀) (goodSeeds F G))) := by
  rw [consumer, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  calc
    _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rawLoop c A hA r₀ (goodSeeds F G) fuel 0)
        (fun out => (priceSum w : ℝ≥0∞)*(out.2.2 : ℝ≥0∞)) := by
      apply ENNReal.tsum_le_tsum
      intro out
      by_cases ho : out ∈ (rawLoop c A hA r₀ (goodSeeds F G) fuel 0).support
      · have hr := LedgerBridge.windowLoop_ratio A hA r₀ (goodSeeds F G) _
          (round_ratio c A hA r₀ (goodSeeds F G)) fuel 0 out ho
        have hb := totalCost_le w (makeReceipt F G out) hr.1 hr.2
        dsimp only [makeReceipt] at hb
        apply mul_le_mul_right
        change (totalCost w (makeReceipt F G out) : ℝ≥0∞) ≤
          (priceSum w : ℝ≥0∞)*(out.2.2 : ℝ≥0∞)
        exact_mod_cast hb
      · have hz : (rawLoop c A hA r₀ (goodSeeds F G) fuel 0) out = 0 := by
          simpa [PMF.mem_support_iff] using! ho
        simp [hz]
    _ = (priceSum w : ℝ≥0∞)*Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rawLoop c A hA r₀ (goodSeeds F G) fuel 0)
        (fun out => (out.2.2 : ℝ≥0∞)) := by
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
    _ ≤ _ := mul_le_mul_right (rawLoop_budget c A hA r₀ (goodSeeds F G) fuel ha) _

namespace StopAdapter
open LedgerBridge
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
variable {I : Type} [Fintype I] [DecidableEq I]
/-- One scheduled search transition, terminating on a returned seed and otherwise advancing the
round index while accumulating both cost counters. -/
noncomputable def scheduleNext (round : ℕ → PMF (Option I × ℕ × ℕ))
    (st : SourceRunState) : PMF (Configuration SourceRunState (SourceRunOutcome I)) :=
  (round st.1).map fun out =>
    if out.1.isSome then Sum.inl (out.1, st.2.1+out.2.1, st.2.2+out.2.2)
    else Sum.inr (st.1+1, st.2.1+out.2.1, st.2.2+out.2.2)

/-- Extract a terminal outcome or convert a pending state into an absent output with its
accumulated costs. -/
def collapse : Configuration SourceRunState (SourceRunOutcome I) → SourceRunOutcome I
  | .inl out => out
  | .inr st => (none, st.2.1, st.2.2)

/-- Add fixed initial costs to the two counters of a search outcome. -/
def translate (c1 c2 : ℕ) (out : SourceRunOutcome I) : SourceRunOutcome I :=
  (out.1,c1+out.2.1,c2+out.2.2)

/-- The source search transition equals the generic scheduled transition instantiated with
source rounds. -/
theorem sourceNext_eq_scheduleNext (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) :
    sourceNext A hA j₀ S = scheduleNext (sourceQSearchRound A hA j₀ S) := rfl

omit [Fintype I] [DecidableEq I] in

/-- For `1 ≤ k ≤ fuel`, the probability of first stopping at step `k` equals the drop in finite
survival between steps `k - 1` and `k`. -/
theorem schedule_first_stop
    (round : ℕ → PMF (Option I × ℕ × ℕ)) (off c1 c2 fuel k : ℕ)
    (hk : 1 ≤ k) (hkf : k ≤ fuel) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (scheduleNext round) fuel (Sum.inr (off+1,c1,c2)))
      (fun x => (∃ out, x.1=Sum.inl out) ∧ x.2=k)
    = finiteSurvival (scheduleNext round) (k-1) (Sum.inr (off+1,c1,c2))
        - finiteSurvival (scheduleNext round) k (Sum.inr (off+1,c1,c2)) :=
  finite_first_stop_mass (scheduleNext round) (off+1,c1,c2) fuel k hk hkf

/-- Collapsing bounded scheduled execution gives the window-loop distribution with the initial
costs added to each outcome. -/
theorem runFor_collapse_eq_loop
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (round : ℕ → PMF (Option I × ℕ × ℕ)) (N off c1 c2 : ℕ) :
    (runFor (scheduleNext round) N (Sum.inr (off+1,c1,c2))).map (fun x => collapse x.1)
      = (windowLoop A hA j₀ S round N off).map (translate c1 c2) := by
  induction N generalizing off c1 c2 with
  | zero => simp [runFor_zero, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_map, collapse,
      windowLoop_zero_eq, translate]
  | succ N ih =>
    simp only [runFor, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind, PMF.map_bind, tick, PMF.bind_map,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge, PMF.map_comp, Function.comp_def, scheduleNext,
      windowLoop_succ_eq]
    congr 1
    funext out
    cases ho : out.1 with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
      rw [show off+1+1=(off+1)+1 by omega, ih]
      simp only [PMF.map_comp, Function.comp_def]
      congr 1
      funext z
      simp only [translate]
      simp [Nat.add_comm, Nat.add_left_comm]
    | some y =>
      simp only [ho, Option.isSome_some, ite_true,
        runFor_halted, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_map, collapse, translate]

omit [Fintype I] [DecidableEq I] in

/-- Finite survival of scheduled execution equals `reachMass` for the round failure
probabilities. -/
theorem schedule_survival_eq_reachMass
    (round : ℕ → PMF (Option I × ℕ × ℕ)) (N r c1 c2 : ℕ) :
    finiteSurvival (scheduleNext round) N (Sum.inr (r,c1,c2))
      = reachMass (fun l => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (round l) (fun out => out.1=none)) r N := by
  induction N generalizing r c1 c2 with
  | zero => rw [finiteSurvival_zero_running, reachMass_zero]
  | succ N ih =>
    rw [finiteSurvival_succ_running]
    rw [scheduleNext, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    have hsplit : ∀ out : Option I × ℕ × ℕ,
        finiteSurvival (scheduleNext round) N
          (if out.1.isSome then Sum.inl (out.1,c1+out.2.1,c2+out.2.2)
           else Sum.inr (r+1,c1+out.2.1,c2+out.2.2))
        = if out.1=none then
            reachMass (fun l => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (round l) (fun out => out.1=none)) (r+1) N
          else 0 := by
      intro out
      rcases Option.eq_none_or_eq_some out.1 with hn | ⟨y, hy⟩
      · rw [hn, Option.isSome_none, if_neg (by simp), ih, if_pos rfl]
      · rw [hy, Option.isSome_some, if_pos (by simp), finiteSurvival_halted, if_neg (by simp)]
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hsplit,
        expectation_indicator_mul', reachMass_succ]
    exact mul_comm _ _

/-- The probability of first stopping at step `k` in bounded scheduled execution equals the drop
in window-loop failure probability at that step. -/
theorem actual_first_stop_eq_loop_failure_drop
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (round : ℕ → PMF (Option I × ℕ × ℕ)) (off fuel k : ℕ)
    (hk : 1 ≤ k) (hkf : k ≤ fuel) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (scheduleNext round) fuel (Sum.inr (off+1,0,0)))
      (fun x => (∃ out, x.1=Sum.inl out) ∧ x.2=k)
    = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (windowLoop A hA j₀ S round (k-1) off) (fun out => out.1=none)
      - Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (windowLoop A hA j₀ S round k off) (fun out => out.1=none) := by
  rw [schedule_first_stop round off 0 0 fuel k hk hkf,
    schedule_survival_eq_reachMass, schedule_survival_eq_reachMass,
    windowLoop_none_eq_reachMass, windowLoop_none_eq_reachMass]

/-- Mapping collapsed scheduled execution through any receipt function agrees with mapping the
corresponding finite window loop. -/
theorem runFor_receipt_eq_loop_receipt
    {R : Type} (receipt : SourceRunOutcome I → R)
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (round : ℕ → PMF (Option I × ℕ × ℕ)) (N off : ℕ) :
    (runFor (scheduleNext round) N (Sum.inr (off+1,0,0))).map (fun x => receipt (collapse x.1))
      = (windowLoop A hA j₀ S round N off).map receipt := by
  have h := congrArg (PMF.map receipt) (runFor_collapse_eq_loop A hA j₀ S round N off 0 0)
  simpa [PMF.map_comp, Function.comp_def, translate] using! h

end StopAdapter

/-- The receipts of bounded scheduled execution have exactly the consumer distribution. -/
theorem actual_receipt (c : DepthConvention) (F : Y → Bool) (G : (Y → Bool) → R → Y)
    (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ) (r₀ : R) (fuel off : ℕ) :
    (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.runFor
      (StopAdapter.scheduleNext (roundLaw c A hA r₀ (goodSeeds F G))) fuel
      (Sum.inr (off+1,0,0))).map (fun x => makeReceipt F G (StopAdapter.collapse x.1)) =
      consumer c F G A hA r₀ fuel off :=
  StopAdapter.runFor_receipt_eq_loop_receipt (makeReceipt F G) A hA r₀ (goodSeeds F G) _ fuel off

/-- For `1 ≤ k ≤ fuel`, the actual first-stop probability equals the drop in consumer failure
probability from horizon `k - 1` to horizon `k`. -/
theorem actual_first_stop (c : DepthConvention) (F : Y → Bool) (G : (Y → Bool) → R → Y)
    (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ) (r₀ : R)
    (off fuel k : ℕ) (hk : 1 ≤ k) (hkf : k ≤ fuel) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.runFor
      (StopAdapter.scheduleNext (roundLaw c A hA r₀ (goodSeeds F G))) fuel (Sum.inr (off+1,0,0)))
      (fun x => (∃ out, x.1=Sum.inl out) ∧ x.2=k) =
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (consumer c F G A hA r₀ (k-1) off) (fun tr => tr.output=none) -
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (consumer c F G A hA r₀ k off) (fun tr => tr.output=none) := by
  simpa only [consumer, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map, makeReceipt, Option.map_eq_none_iff] using!
    StopAdapter.actual_first_stop_eq_loop_failure_drop A hA r₀ (goodSeeds F G)
      (roundLaw c A hA r₀ (goodSeeds F G)) off fuel k hk hkf

/-- For positive good-seed probability, combine receipt provenance, output validity, and ledger
identities with the expected weighted cost bound from amplitude-amplified search
[BrassardEtAl2002]. -/
theorem frontier1 (c : DepthConvention) (F : Y → Bool) (G : (Y → Bool) → R → Y)
    (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ) (r₀ : R) (fuel : ℕ) (w : Prices)
    (ha : 0 < MeasureProb (preparedAAState A r₀) (goodSeeds F G)) :
    (∀ tr ∈ (consumer c F G A hA r₀ fuel 0).support,
      tr.output = tr.raw.1.map (G F) ∧
      (∀ y, tr.output=some y → F y=true) ∧
      prepareForward tr + prepareAdjoint tr = tr.raw.2.1 ∧
      phaseCalls tr + validationCalls tr = tr.raw.2.2 ∧
      gForward tr = prepareForward tr ∧ gAdjoint tr = prepareForward tr) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (consumer c F G A hA r₀ fuel 0) (fun tr => (totalCost w tr : ℝ≥0∞)) ≤
      (priceSum w : ℝ≥0∞)*ENNReal.ofReal (400/Real.sqrt (MeasureProb (preparedAAState A r₀) (goodSeeds F G))) := by
  constructor
  · intro tr ht
    exact ⟨receipt_origin c F G A hA r₀ fuel 0 tr ht,
      consumer_sound c F G A hA r₀ fuel 0 tr ht, consumer_ledgers c F G A hA r₀ fuel 0 tr ht⟩
  · exact expected_cost c F G A hA r₀ fuel w ha

namespace GeometricAdapter

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib
open StopAdapter
variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in

/-- A lower bound `a ≥ 0` on a round's success probability gives the complementary upper bound
`ENNReal.ofReal (1 - a)` on failure. -/
theorem round_failure_le_of_success_lower
    (p : PMF (Option I × ℕ × ℕ)) (a : ℝ) (ha0 : 0 ≤ a)
    (hs : ENNReal.ofReal a ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun out => ∃ y, out.1=some y)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun out => out.1=none) ≤ ENNReal.ofReal (1-a) := by
  have hp := event_compl p (fun out => ∃ y, out.1=some y)
  have hc : ∀ out : Option I × ℕ × ℕ,
      (¬ ∃ y, out.1=some y) ↔ out.1=none := by
    intro out
    cases out.1 <;> simp
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr hc] at hp
  rw [ENNReal.ofReal_sub 1 ha0, ENNReal.ofReal_one]
  exact ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top
    ((add_le_add hs le_rfl).trans_eq hp)

omit [Fintype I] [DecidableEq I] in

/-- The probability that a scheduled transition remains pending equals the failure probability
of its current round. -/
theorem schedule_running_mass
    (round : ℕ → PMF (Option I × ℕ × ℕ)) (st : SourceRunState) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (scheduleNext round st) (fun cfg => ∃ s, cfg=Sum.inr s)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (round st.1) (fun out => out.1=none) := by
  rw [scheduleNext, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr
  intro out
  cases out.1 <;> simp

omit [Fintype I] [DecidableEq I] in

/-- A uniform round success lower bound `a ≥ 0` gives a geometric upper bound `ENNReal.ofReal (1
- a) ^ N` on finite survival. -/
theorem schedule_pending_le_geometric
    (round : ℕ → PMF (Option I × ℕ × ℕ)) (a : ℝ) (ha0 : 0 ≤ a)
    (hs : ∀ l, ENNReal.ofReal a ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (round l) (fun out => ∃ y, out.1=some y))
    (N r c1 c2 : ℕ) :
    finiteSurvival (scheduleNext round) N (Sum.inr (r,c1,c2))
      ≤ ENNReal.ofReal (1-a) ^ N := by
  have hq : ENNReal.ofReal (1-a) ≤ 1 := by
    calc ENNReal.ofReal (1-a) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (by linarith)
         _ = 1 := ENNReal.ofReal_one
  apply (finite_survival_geometric_bound (scheduleNext round) (r,c1,c2)
    (ENNReal.ofReal (1-a)) N hq ?_).1
  intro st
  rw [schedule_running_mass]
  exact round_failure_le_of_success_lower (round st.1) a ha0 (hs st.1)

/-- Every source round succeeds with probability at least the initial prepared marked
probability. -/
theorem source_success_lower (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) :
    ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceQSearchRound A hA j₀ S l) (fun out => ∃ y, out.1=some y) := by
  rw [sourceRound_success_mass]
  exact le_add_of_nonneg_right (by positivity)

/-- Every shifted round succeeds with probability at least the initial prepared marked
probability. -/
theorem shifted_success_lower (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) :
    ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (shiftedQSearchRound A hA j₀ S l) (fun out => ∃ y, out.1=some y) := by
  rw [shiftedRound_success_mass]
  exact le_add_of_nonneg_right (by positivity)

/-- A shifted round's failure probability is at most one minus the initial prepared marked
probability. -/
theorem shifted_failure_le (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (shiftedQSearchRound A hA j₀ S l) (fun out => out.1=none)
      ≤ ENNReal.ofReal (1-MeasureProb (preparedAAState A j₀) S) :=
  round_failure_le_of_success_lower _ _ (measureProb_nonneg _ _) (shifted_success_lower A hA j₀ S l)

/-- Both source and shifted scheduled executions have survival probability at most `(1 - a)^N`,
expressed in extended nonnegative reals. -/
theorem both_actual_pending_le (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (N r c1 c2 : ℕ) :
    finiteSurvival (scheduleNext (sourceQSearchRound A hA j₀ S)) N (Sum.inr (r,c1,c2))
        ≤ ENNReal.ofReal (1-MeasureProb (preparedAAState A j₀) S) ^ N ∧
    finiteSurvival (scheduleNext (shiftedQSearchRound A hA j₀ S)) N (Sum.inr (r,c1,c2))
        ≤ ENNReal.ofReal (1-MeasureProb (preparedAAState A j₀) S) ^ N := by
  constructor
  · exact schedule_pending_le_geometric _ _ (measureProb_nonneg _ _)
      (source_success_lower A hA j₀ S) N r c1 c2
  · exact schedule_pending_le_geometric _ _ (measureProb_nonneg _ _)
      (shifted_success_lower A hA j₀ S) N r c1 c2

/-- If the initial marked probability is one, both depth conventions have zero survival
probability after any positive number of rounds. -/
theorem both_pending_one_endpoint (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (N r c1 c2 : ℕ)
    (ha : MeasureProb (preparedAAState A j₀) S = 1) :
    finiteSurvival (scheduleNext (sourceQSearchRound A hA j₀ S)) (N+1) (Sum.inr (r,c1,c2)) = 0 ∧
    finiteSurvival (scheduleNext (shiftedQSearchRound A hA j₀ S)) (N+1) (Sum.inr (r,c1,c2)) = 0 := by
  have h := both_actual_pending_le A hA j₀ S (N+1) r c1 c2
  simpa [ha] using! h

omit [Fintype I] [DecidableEq I] in

/-- If every round has zero success probability, scheduled execution remains pending with
probability one at every finite horizon. -/
theorem schedule_pending_eq_one_of_no_success
    (round : ℕ → PMF (Option I × ℕ × ℕ))
    (hs : ∀ l, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (round l) (fun out => ∃ y, out.1=some y) = 0)
    (N r c1 c2 : ℕ) :
    finiteSurvival (scheduleNext round) N (Sum.inr (r,c1,c2)) = 1 := by
  have hf : ∀ l, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (round l) (fun out => out.1=none) = 1 := by
    intro l
    have hp := event_compl (round l) (fun out => ∃ y, out.1=some y)
    have hc : ∀ out : Option I × ℕ × ℕ,
        (¬ ∃ y, out.1=some y) ↔ out.1=none := by
      intro out
      cases out.1 <;> simp
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr hc, hs l, zero_add] at hp
    exact hp
  rw [schedule_survival_eq_reachMass]
  induction N generalizing r with
  | zero => rfl
  | succ N ih => rw [reachMass_succ, hf, ih, one_mul]

/-- If the initial marked probability is zero, source and shifted scheduled execution both
remain pending with probability one. -/
theorem both_pending_zero_endpoint (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (N r c1 c2 : ℕ)
    (ha : MeasureProb (preparedAAState A j₀) S = 0) :
    finiteSurvival (scheduleNext (sourceQSearchRound A hA j₀ S)) N (Sum.inr (r,c1,c2)) = 1 ∧
    finiteSurvival (scheduleNext (shiftedQSearchRound A hA j₀ S)) N (Sum.inr (r,c1,c2)) = 1 := by
  constructor
  · exact schedule_pending_eq_one_of_no_success _
      (fun l => sourceRound_success_mass_zero A hA j₀ S l ha) N r c1 c2
  · apply schedule_pending_eq_one_of_no_success
    intro l
    rw [shiftedRound_success_mass]
    have hsum : ∑ j : Fin (BHMTQSearch.qSearchWindow l), ENNReal.ofReal
        (depthSuccessMass A j₀ S j.val) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [depthSuccessMass_eq_zero_of_zero A j₀ S j.val hA ha, ENNReal.ofReal_zero]
    rw [ha, ENNReal.ofReal_zero, hsum]
    simp

end GeometricAdapter

/-- The consumer failure probability is bounded by `(1 - a)^fuel`, where `a` is the prepared
good-seed probability. -/
theorem consumer_failure_le (c : DepthConvention) (F : Y → Bool) (G : (Y → Bool) → R → Y)
    (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ) (r₀ : R) (fuel off : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (consumer c F G A hA r₀ fuel off) (fun tr => tr.output=none) ≤
      ENNReal.ofReal (1-MeasureProb (preparedAAState A r₀) (goodSeeds F G))^fuel := by
  rw [consumer_failure, ← StopAdapter.schedule_survival_eq_reachMass _ fuel (off+1) 0 0]
  cases c
  · exact (GeometricAdapter.both_actual_pending_le A hA r₀ (goodSeeds F G) fuel (off+1) 0 0).1
  · exact (GeometricAdapter.both_actual_pending_le A hA r₀ (goodSeeds F G) fuel (off+1) 0 0).2

/-- If the prepared good-seed probability is zero, the consumer returns no output with
probability one. -/
theorem consumer_failure_zero (c : DepthConvention) (F : Y → Bool) (G : (Y → Bool) → R → Y)
    (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ) (r₀ : R) (fuel off : ℕ)
    (ha : MeasureProb (preparedAAState A r₀) (goodSeeds F G) = 0) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (consumer c F G A hA r₀ fuel off) (fun tr => tr.output=none) = 1 := by
  rw [consumer_failure, ← StopAdapter.schedule_survival_eq_reachMass _ fuel (off+1) 0 0]
  cases c
  · exact (GeometricAdapter.both_pending_zero_endpoint A hA r₀ (goodSeeds F G) fuel (off+1) 0 0 ha).1
  · exact (GeometricAdapter.both_pending_zero_endpoint A hA r₀ (goodSeeds F G) fuel (off+1) 0 0 ha).2

/-- For positive prepared good-seed probability, consumer failure probability tends to zero as
the finite horizon tends to infinity. -/
theorem consumer_terminates (c : DepthConvention) (F : Y → Bool) (G : (Y → Bool) → R → Y)
    (A : Matrix R R ℂ) (hA : A ∈ Matrix.unitaryGroup R ℂ) (r₀ : R)
    (ha : 0 < MeasureProb (preparedAAState A r₀) (goodSeeds F G)) :
    Filter.Tendsto (fun fuel => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (consumer c F G A hA r₀ fuel 0) (fun tr => tr.output=none))
      Filter.atTop (nhds 0) := by
  have ha1 : MeasureProb (preparedAAState A r₀) (goodSeeds F G) ≤ 1 :=
    measureProb_le_one ((prepared_aa_reflection_and_access A r₀ (goodSeeds F G) hA).2.1) _
  have hq : ENNReal.ofReal (1-MeasureProb (preparedAAState A r₀) (goodSeeds F G)) < 1 := by
    rw [show (1:ℝ≥0∞) = ENNReal.ofReal ((1:ℝ)) from ENNReal.ofReal_one.symm]
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)]
    linarith
  exact Filter.Tendsto.squeeze' tendsto_const_nhds (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun n => consumer_failure_le c F G A hA r₀ n 0)

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.HeuristicQSearchReceipt
