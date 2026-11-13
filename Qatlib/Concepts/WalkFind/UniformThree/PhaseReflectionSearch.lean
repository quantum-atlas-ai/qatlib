/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.CountedPhaseReflection
import Qatlib.Concepts.WalkSearch.CountedWalk.CountedSzegedyAccess
import Qatlib.Concepts.SpectralFilter.WalkBoundary.SzegedyAccessConsumers
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation
import Qatlib.Concepts.WalkFind.UniformThree.HiddenSubgroupOracle
import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws

/-!
# Search with Fresh Phase Reflection Registers

`phaseSearchState` alternates the marked-state sign flip with a phase-estimation reflection
using a fresh register batch at each round. For a unitary with a distinguished zero-phase
eigenstate and a separated orthonormal eigenfamily whose span is preserved by marking, the
module bounds the distance to ideal amplitude amplification and the resulting marked probability
[BrassardEtAl2002].

The access accounting includes `phaseSearchLedger` and the expanded Szegedy reflection word,
connecting the construction to quantized Markov-chain walks [Szegedy2004]. The uniform
three-point example prepares its input with `phaseSearchUniformThreeSetup` and proves marked
probability `25 / 27` with ledger `(2, 1, 1)` for phase queries, marked checks, and setup
charges.

## Main statements

* `phase_search_reachable_state_error` bounds accumulated state error by `2 * t * (1 / (2 * M *
  eta)) ^ k`.
* `phase_search_actual_marked_success` subtracts the corresponding probability error from the
  ideal amplification formula.
* `szegedy_phase_reflection_expanded_update_counts` counts the expanded queries and gates.
* `phase_search_uniform_three_prepared_consumer` gives the prepared three-point example and its
  ledger.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.WalkSearch.CountedWalk
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.WalkFind.UniformThree

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical Matrix.Norms.L2Operator BigOperators

set_option autoImplicit false

/-- The search ledger records phase-reflection query occurrences across `t` rounds, one marked
check per round, and one setup charge. -/
noncomputable def phaseSearchLedger (M k t : ℕ) : ℕ × ℕ × ℕ :=
  (t * adjointQueryCount (phaseReflectionWord (I := Unit) M k),
    (List.replicate t ()).length, 1)

/-- For `M >= 2`, the fresh-register search ledger is exactly `(2 * k * t * (M - 1), t, 1)`. -/
theorem phase_search_fresh_access_ledger (M k t : ℕ) (hM : 2 ≤ M) :
    phaseSearchLedger M k t = (2 * k * t * (M - 1), t, 1) := by
  rw [phaseSearchLedger, (phase_reflection_actual_queries_and_macros (I := Unit) M k hM).2.1,
    List.length_replicate]
  congr 1
  ring

/-- The phase-reflection word with each oracle occurrence expanded into the controlled counted
Szegedy walk word and lifted across the phase registers. -/
noncomputable def szegedyPhaseReflectionWord {I : Type} [Fintype I] [DecidableEq I]
    (j : I) (M k : ℕ) : List (AdjointStep (PhaseReflectionSpace (I × I) M k)) :=
  substituteAdjointCircuit
    (phaseLiftWord (fun U => TensorGate (1 : Matrix (Fin k → Fin M) (Fin k → Fin M) ℂ) U)
      (compileControlled (countedSzegedyWord j)))
    (phaseReflectionWord M k)

/-- For `M >= 2`, the expanded Szegedy phase-reflection word uses exactly `8 * k * (M - 1)`
queries and `12 * k * (M - 1) + 4 * k + 1` gates. -/
theorem szegedy_phase_reflection_expanded_update_counts {I : Type} [Fintype I] [DecidableEq I]
    (j : I) (M k : ℕ) (hM : 2 ≤ M) :
    adjointQueryCount (szegedyPhaseReflectionWord j M k) = 8 * k * (M - 1) ∧
      adjointGateCount (szegedyPhaseReflectionWord j M k) = 12 * k * (M - 1) + 4 * k + 1 := by
  let body := phaseLiftWord
    (fun U => TensorGate (1 : Matrix (Fin k → Fin M) (Fin k → Fin M) ℂ) U)
    (compileControlled (countedSzegedyWord j))
  have hb : adjointQueryCount body = 4 ∧ adjointGateCount body = 4 := by
    dsimp only [body]
    rw [(phaseLiftWord_counts _ _).1, (phaseLiftWord_counts _ _).2,
      queryCount_compileControlled, gateCount_compileControlled]
    exact (counted_szegedy_actual_word_and_counts j).2
  have hs := substitute_adjoint_evaluate_cost
    (1 : Matrix (PhaseReflectionSpace (I × I) M k) (PhaseReflectionSpace (I × I) M k) ℂ)
    body (phaseReflectionWord M k)
  have hc := (phase_reflection_actual_queries_and_macros (I := I × I) M k hM).2
  change adjointQueryCount (substituteAdjointCircuit body (phaseReflectionWord M k)) = _ ∧
    adjointGateCount (substituteAdjointCircuit body (phaseReflectionWord M k)) = _
  rw [hs.2.1, hs.2.2.1, hb.1, hb.2, hc.1, hc.2]
  constructor <;> ring

/-- The register equivalence separating `k * (t + 1)` phase registers into a fresh batch of `k`
registers and the previous `k * t` registers. -/
def phaseBatchRegisters (M k t : ℕ) :
    (Fin (k * (t + 1)) → Fin M) ≃ (Fin k → Fin M) × (Fin (k * t) → Fin M) :=
  (Equiv.arrowCongr
    ((finCongr (by ring : k * (t + 1) = k + k * t)).trans
      (finSumFinEquiv : Fin k ⊕ Fin (k * t) ≃ Fin (k + k * t)).symm)
    (Equiv.refl (Fin M))).trans (Equiv.sumArrowEquivProdArrow (Fin k) (Fin (k * t)) (Fin M))

/-- The state-space equivalence that places the fresh phase-register batch before the previous
phase-reflection state space. -/
def phaseFreshSplit (I : Type) (M k t : ℕ) :
    PhaseReflectionSpace I M (k * (t + 1)) ≃
      (Fin k → Fin M) × PhaseReflectionSpace I M (k * t) :=
  (Equiv.prodCongr (phaseBatchRegisters M k t) (Equiv.refl (Bool × I))).trans
    (Equiv.prodAssoc _ _ _)

/-- The state-space equivalence that places the old phase registers before the fresh registers,
flag, and system on which the next reflection acts. -/
def phaseFreshActionSplit (I : Type) (M k t : ℕ) :
    PhaseReflectionSpace I M (k * (t + 1)) ≃
      (Fin (k * t) → Fin M) × PhaseReflectionSpace I M k :=
  (Equiv.prodCongr ((phaseBatchRegisters M k t).trans (Equiv.prodComm _ _))
    (Equiv.refl (Bool × I))).trans (Equiv.prodAssoc _ _ _)

section FreshSearch

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The marked-state sign-flip matrix `preparedMark S` is unitary. -/
private theorem phase_mark_unitary (S : Finset I) :
    preparedMark S ∈ Matrix.unitaryGroup I ℂ := by
  have he : preparedMark S = ReflectionAbout (1 - Projector S) := by
    unfold preparedMark ReflectionAbout
    module
  rw [he]
  exact reflectionAbout_unitary (isOrthogonalProjector_compl (projector_isOrthogonalProjector S))

/-- Appends a fresh batch of `k` zero phase registers to the current search state, using
`phaseFreshSplit` to restore the combined register indexing. -/
noncomputable def phaseFreshAppend (M k t : ℕ) (hM : 0 < M)
    (ψ : QState (PhaseReflectionSpace I M (k * t))) :
    QState (PhaseReflectionSpace I M (k * (t + 1))) :=
  relabelState (phaseFreshSplit I M k t).symm (TensorState (Ket (phaseZeroIndex M k hM)) ψ)

/-- The phase-reflection matrix acting on the fresh phase-register batch, flag, and system while
acting identically on all old phase registers. -/
noncomputable def phaseFreshReflectionMatrix (W : Matrix I I ℂ) (M k t : ℕ) :
    Matrix (PhaseReflectionSpace I M (k * (t + 1))) (PhaseReflectionSpace I M (k * (t + 1))) ℂ :=
  relabelGate (phaseFreshActionSplit I M k t).symm
    (TensorGate (1 : Matrix (Fin (k * t) → Fin M) (Fin (k * t) → Fin M) ℂ)
      (evaluate (parallelOracle (controlOracle W)) (phaseReflectionWord M k)))

/-- The marked-state sign flip lifted to the full phase-reflection space, acting identically on
the phase registers and flag. -/
noncomputable def phaseSearchCheck (S : Finset I) (M n : ℕ) :
    Matrix (PhaseReflectionSpace I M n) (PhaseReflectionSpace I M n) ℂ :=
  parallelOracle (TensorGate (1 : Matrix Bool Bool ℂ) (preparedMark S))

/-- The search state obtained by repeatedly appending fresh phase registers, flipping the marked
system states, and applying a phase reflection. For `M = 0`, every successor state is
defined to be zero. -/
noncomputable def phaseSearchState (W : Matrix I I ℂ) (ψ : QState I) (S : Finset I)
    (M k : ℕ) : (t : ℕ) → QState (PhaseReflectionSpace I M (k * t))
  | 0 => phaseReflectionEmbed M (k * 0) ψ
  | t + 1 => if hM : 0 < M then
      ApplyGate (phaseFreshReflectionMatrix W M k t)
        (ApplyGate (phaseSearchCheck S M (k * (t + 1)))
          (phaseFreshAppend M k t hM (phaseSearchState W ψ S M k t)))
    else 0

/-- Relabeling a finite state by an equivalence preserves its Euclidean norm. -/
private theorem phaseRelabel_norm {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (e : H ≃ K) (ψ : QState H) :
    ‖toEuclidean_fromVec (relabelState e ψ)‖ = ‖toEuclidean_fromVec ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_toEuclidean_sq_eq_re_inner, norm_toEuclidean_sq_eq_re_inner, inner_relabelState]

/-- Appending the fresh zero-register batch preserves the Euclidean norm of the search state. -/
theorem phaseFreshAppend_norm (M k t : ℕ) (hM : 0 < M)
    (ψ : QState (PhaseReflectionSpace I M (k * t))) :
    ‖toEuclidean_fromVec (phaseFreshAppend M k t hM ψ)‖ = ‖toEuclidean_fromVec ψ‖ := by
  rw [phaseFreshAppend, phaseRelabel_norm, tensorState_l2_norm,
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket _), one_mul]

/-- For a unitary walk and `M >= 2`, the reflection acting on a fresh register batch is unitary
on the enlarged search space. -/
theorem phaseFreshReflectionMatrix_unitary (W : Matrix I I ℂ) (M k t : ℕ)
    (hW : W ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M) :
    phaseFreshReflectionMatrix W M k t ∈ Matrix.unitaryGroup (PhaseReflectionSpace I M (k * (t + 1))) ℂ :=
  (relabelGate_mem_unitaryGroup _ _).mpr (tensorGate_unitary (by simp)
    ((phase_reflection_actual_queries_and_macros M k hM).1.evaluate_unitary
      (parallelOracle_unitary (controlOracle_unitary hW))))

/-- The lifted marked-state check is unitary for every choice of phase-register parameters. -/
theorem phaseSearchCheck_unitary (S : Finset I) (M n : ℕ) :
    phaseSearchCheck S M n ∈ Matrix.unitaryGroup (PhaseReflectionSpace I M n) ℂ :=
  parallelOracle_unitary (tensorGate_unitary (by simp) (phase_mark_unitary S))

omit [Fintype I] [DecidableEq I] in

/-- A phase embedding factors into a zero-register ket and a smaller phase embedding under any
register equivalence that sends the zero index to the corresponding pair of zero indices. -/
private theorem phase_split_embed (M n a b : ℕ) (hM : 0 < M)
    (e : (Fin n → Fin M) ≃ (Fin a → Fin M) × (Fin b → Fin M))
    (he : e (phaseZeroIndex M n hM) = (phaseZeroIndex M a hM, phaseZeroIndex M b hM))
    (ψ : QState I) :
    phaseReflectionEmbed M n ψ =
      relabelState ((Equiv.prodCongr e (Equiv.refl (Bool × I))).trans (Equiv.prodAssoc _ _ _)).symm
        (TensorState (Ket (phaseZeroIndex M a hM)) (phaseReflectionEmbed M b ψ)) := by
  rw [phaseReflectionEmbed_tensor M n hM, phaseReflectionEmbed_tensor M b hM]
  funext ⟨x, flag, i⟩
  have hx : x = phaseZeroIndex M n hM ↔
      (e x).1 = phaseZeroIndex M a hM ∧ (e x).2 = phaseZeroIndex M b hM := by
    constructor
    · rintro rfl
      rw [he]
      exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      apply e.injective
      rw [he]
      exact Prod.ext h1 h2
  dsimp [relabelState, TensorState, Ket]
  by_cases h1 : (e x).1 = phaseZeroIndex M a hM <;>
    by_cases h2 : (e x).2 = phaseZeroIndex M b hM <;> simp [hx, h1, h2]

omit [Fintype I] [DecidableEq I] in

/-- Appending fresh zero registers to an embedded system state gives its embedding into the
enlarged phase-reflection space. -/
theorem phaseFreshAppend_embed (M k t : ℕ) (hM : 0 < M) (ψ : QState I) :
    phaseFreshAppend M k t hM (phaseReflectionEmbed M (k * t) ψ) =
      phaseReflectionEmbed M (k * (t + 1)) ψ :=
  (phase_split_embed M (k * (t + 1)) k (k * t) hM (phaseBatchRegisters M k t) (by rfl) ψ).symm

/-- On an embedded system state, the lifted search check agrees with embedding the result of
`preparedMark S`. -/
theorem phaseSearchCheck_embed (S : Finset I) (M n : ℕ) (hM : 0 < M) (ψ : QState I) :
    ApplyGate (phaseSearchCheck S M n) (phaseReflectionEmbed M n ψ) =
      phaseReflectionEmbed M n (ApplyGate (preparedMark S) ψ) := by
  rw [phaseReflectionEmbed_tensor M n hM, phaseSearchCheck, parallelOracle_eq_kronecker]
  change ApplyGate (TensorGate (1 : Matrix (Fin n → Fin M) (Fin n → Fin M) ℂ)
    (TensorGate (1 : Matrix Bool Bool ℂ) (preparedMark S)))
      (TensorState (Ket (phaseZeroIndex M n hM)) (TensorState (Ket false) ψ)) = _
  rw [applyGate_tensorGate, applyGate_one, applyGate_tensorGate, applyGate_one,
    ← phaseReflectionEmbed_tensor M n hM]

/-- On a fully zero-register embedding, the fresh reflection produces `phaseReflectionState` on
the fresh batch while leaving the old register batch in its zero ket. -/
theorem phaseFreshReflectionMatrix_embed (W : Matrix I I ℂ) (M k t : ℕ)
    (hM : 0 < M) (ψ : QState I) :
    ApplyGate (phaseFreshReflectionMatrix W M k t)
      (phaseReflectionEmbed M (k * (t + 1)) ψ) =
      relabelState (phaseFreshActionSplit I M k t).symm
        (TensorState (Ket (phaseZeroIndex M (k * t) hM)) (phaseReflectionState W M k ψ)) := by
  have he := phase_split_embed M (k * (t + 1)) (k * t) k hM
    ((phaseBatchRegisters M k t).trans (Equiv.prodComm _ _)) (by rfl) ψ
  rw [phaseFreshReflectionMatrix, phaseFreshActionSplit, he, applyGate_relabelGate,
    applyGate_tensorGate, applyGate_one]
  rfl

/-- For a unitary walk and `M >= 2`, every fresh-register search state has the same Euclidean
norm as its system input. -/
theorem phaseSearchState_norm (W : Matrix I I ℂ) (ψ : QState I) (S : Finset I) (M k t : ℕ)
    (hW : W ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M) :
    ‖toEuclidean_fromVec (phaseSearchState W ψ S M k t)‖ = ‖toEuclidean_fromVec ψ‖ := by
  induction t with
  | zero => exact phaseReflectionEmbed_norm M (k * 0) (by omega) ψ
  | succ t ih =>
    rw [phaseSearchState, dif_pos (by omega : 0 < M),
      norm_applyGate_of_mem_unitaryGroup (phaseFreshReflectionMatrix_unitary W M k t hW hM),
      norm_applyGate_of_mem_unitaryGroup (phaseSearchCheck_unitary S M (k * (t + 1))),
      phaseFreshAppend_norm, ih]

omit [Fintype I] [DecidableEq I] in

/-- Appending fresh zero registers commutes with subtraction of states. -/
private theorem phaseFreshAppend_sub (M k t : ℕ) (hM : 0 < M)
    (x y : QState (PhaseReflectionSpace I M (k * t))) :
    phaseFreshAppend M k t hM (x - y) =
      phaseFreshAppend M k t hM x - phaseFreshAppend M k t hM y := by
  funext p
  simp [phaseFreshAppend, relabelState, TensorState, mul_sub]

/-- For a unitary walk and `M >= 2`, a complete fresh-register search round preserves the
Euclidean distance between two input states. -/
private theorem phase_fresh_round_norm_sub (W : Matrix I I ℂ) (S : Finset I) (M k t : ℕ)
    (hW : W ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M)
    (x y : QState (PhaseReflectionSpace I M (k * t))) :
    ‖toEuclidean_fromVec
      (ApplyGate (phaseFreshReflectionMatrix W M k t)
        (ApplyGate (phaseSearchCheck S M (k * (t + 1))) (phaseFreshAppend M k t (by omega) x)) -
       ApplyGate (phaseFreshReflectionMatrix W M k t)
        (ApplyGate (phaseSearchCheck S M (k * (t + 1))) (phaseFreshAppend M k t (by omega) y)))‖ =
      ‖toEuclidean_fromVec (x - y)‖ := by
  change ‖toEuclidean_fromVec
    (phaseFreshReflectionMatrix W M k t *ᵥ
      (phaseSearchCheck S M (k * (t + 1)) *ᵥ phaseFreshAppend M k t (by omega) x) -
     phaseFreshReflectionMatrix W M k t *ᵥ
      (phaseSearchCheck S M (k * (t + 1)) *ᵥ phaseFreshAppend M k t (by omega) y))‖ = _
  rw [← Matrix.mulVec_sub]
  change ‖toEuclidean_fromVec (ApplyGate (phaseFreshReflectionMatrix W M k t)
    (phaseSearchCheck S M (k * (t + 1)) *ᵥ phaseFreshAppend M k t (by omega) x -
     phaseSearchCheck S M (k * (t + 1)) *ᵥ phaseFreshAppend M k t (by omega) y))‖ = _
  rw [norm_applyGate_of_mem_unitaryGroup (phaseFreshReflectionMatrix_unitary W M k t hW hM)]
  rw [← Matrix.mulVec_sub]
  change ‖toEuclidean_fromVec (ApplyGate (phaseSearchCheck S M (k * (t + 1)))
    (phaseFreshAppend M k t (by omega) x - phaseFreshAppend M k t (by omega) y))‖ = _
  rw [norm_applyGate_of_mem_unitaryGroup (phaseSearchCheck_unitary S M (k * (t + 1))),
    ← phaseFreshAppend_sub, phaseFreshAppend_norm]

/-- On a normalized linear combination of the stated orthonormal eigenfamily, the fresh phase
reflection differs from the embedded reflection about the distinguished zero-phase
eigenstate by at most `2 * (1 / (2 * M * η)) ^ k`. This assumes a unitary walk, `M >= 2`,
and phase distance at least `η > 0` for every other family member. -/
private theorem phase_fresh_reflection_reachable_error (J : Type) [Fintype J] [DecidableEq J]
    (j0 : J) (v : J → QState I) (p : J → ℝ) (W : Matrix I I ℂ) (M k t : ℕ) (η : ℝ)
    (hM : 2 ≤ M) (hη : 0 < η) (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (hv : ∀ a b, Inner (v a) (v b) = if a = b then 1 else 0)
    (heigen : ∀ a, ApplyGate W (v a) = Complex.exp (2 * Real.pi * Complex.I * p a) • v a)
    (hp0 : p j0 = 0) (hgap : ∀ a, a ≠ j0 → η ≤ phaseDistance (p a) 0)
    (c : J → ℂ) (hn : Normalized (∑ a, c a • v a)) :
    let ψ := ∑ a, c a • v a
    ‖toEuclidean_fromVec
      (ApplyGate (phaseFreshReflectionMatrix W M k t) (phaseReflectionEmbed M (k * (t + 1)) ψ) -
        phaseReflectionEmbed M (k * (t + 1))
          (ApplyGate (ReflectionAbout (outerProduct (v j0))) ψ))‖ ≤
      2 * (1 / (2 * (M : ℝ) * η)) ^ k := by
  intro ψ
  have he := phase_split_embed M (k * (t + 1)) (k * t) k (by omega)
    ((phaseBatchRegisters M k t).trans (Equiv.prodComm _ _)) (by rfl)
    (ApplyGate (ReflectionAbout (outerProduct (v j0))) ψ)
  change phaseReflectionEmbed M (k * (t + 1))
      (ApplyGate (ReflectionAbout (outerProduct (v j0))) ψ) =
    relabelState (phaseFreshActionSplit I M k t).symm
      (TensorState (Ket (phaseZeroIndex M (k * t) (by omega)))
        (phaseReflectionEmbed M k (ApplyGate (ReflectionAbout (outerProduct (v j0))) ψ))) at he
  rw [phaseFreshReflectionMatrix_embed W M k t (by omega), he]
  have hdiff :
      relabelState (phaseFreshActionSplit I M k t).symm
          (TensorState (Ket (phaseZeroIndex M (k * t) (by omega))) (phaseReflectionState W M k ψ)) -
      relabelState (phaseFreshActionSplit I M k t).symm
          (TensorState (Ket (phaseZeroIndex M (k * t) (by omega)))
            (phaseReflectionEmbed M k (ApplyGate (ReflectionAbout (outerProduct (v j0))) ψ))) =
      relabelState (phaseFreshActionSplit I M k t).symm
          (TensorState (Ket (phaseZeroIndex M (k * t) (by omega)))
            (phaseReflectionState W M k ψ -
              phaseReflectionEmbed M k (ApplyGate (ReflectionAbout (outerProduct (v j0))) ψ))) := by
    funext q
    simp [relabelState, TensorState, mul_sub]
  rw [hdiff, phaseRelabel_norm, tensorState_l2_norm,
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket _), one_mul]
  have h : ‖toEuclidean_fromVec (phaseReflectionState W M k ψ -
      phaseReflectionEmbed M k (ApplyGate (ReflectionAbout (outerProduct (v j0))) ψ))‖ ≤
      2 * (1 / (2 * (M : ℝ) * η)) ^ k * ‖toEuclidean_fromVec ψ‖ :=
    phase_reflection_reachable_source_error J j0 v p W M k η hM hη hW hv heigen hp0 hgap c
  have hnorm : ‖toEuclidean_fromVec ψ‖ = 1 := (normalized_iff_norm_toEuclidean_fromVec _).mp hn
  rw [hnorm, mul_one] at h
  exact h

/-- Embedding a system state with zero phase registers and flag preserves the probability of
every event depending only on the system index. -/
theorem phaseReflectionEmbed_measureProb (M n : ℕ) (hM : 0 < M) (ψ : QState I) (S : Finset I) :
    MeasureProb (phaseReflectionEmbed M n ψ) (Finset.univ.filter (fun q => q.2.2 ∈ S)) =
      MeasureProb ψ S := by
  have he : (Finset.univ.filter (fun q : PhaseReflectionSpace I M n => q.2.2 ∈ S)) =
      Finset.univ ×ˢ (Finset.univ ×ˢ S) := by
    ext ⟨x, flag, i⟩
    simp
  rw [phaseReflectionEmbed_tensor M n hM, he,
    measureProb_tensorState_right (normalized_ket _),
    measureProb_tensorState_right (normalized_ket false)]

/-- Every normalized finite state can be obtained as `preparedAAState A j` for some basis index
`j` and unitary matrix `A`. -/
private theorem phase_source_preparation_exists (ψ : QState I) (hψ : Normalized ψ) :
    ∃ (j : I) (A : Matrix I I ℂ), A ∈ Matrix.unitaryGroup I ℂ ∧ preparedAAState A j = ψ := by
  have hne : ∃ i : I, ψ i ≠ 0 := by
    by_contra h
    push Not at h
    simp [Normalized, h] at hψ
  obtain ⟨j, _⟩ := hne
  let D : Matrix I I ℂ := Matrix.diagonal (fun i => coefficientPhase (ψ i))
  have hD : D ∈ Matrix.unitaryGroup I ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    dsimp only [D]
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    calc
      _ = Matrix.diagonal (1 : I → ℂ) := by
        congr 1
        funext i
        exact coefficientPhase_unit (ψ i)
      _ = 1 := Matrix.diagonal_one
  let A := D * nonnegativePrepare (fun i => ‖ψ i‖) j
  have hn : ∑ i, ‖ψ i‖ ^ 2 = 1 := hψ
  have hA : A ∈ Matrix.unitaryGroup I ℂ :=
    (Matrix.unitaryGroup I ℂ).mul_mem hD
      (nonnegativePrepare_unitary _ j (fun i => norm_nonneg (ψ i)) hn)
  refine ⟨j, A, hA, ?_⟩
  change A *ᵥ Ket j = ψ
  dsimp only [A]
  rw [← Matrix.mulVec_mulVec,
    nonnegativePrepare_mulVec_ket _ j (fun i => norm_nonneg (ψ i))]
  funext i
  dsimp only [D]
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp only [if_true]
    rw [mul_comm, norm_mul_coefficientPhase]
  · intro l _ hl
    simp [Ne.symm hl]
  · simp

/-- The state after `t` iterations of the marked sign flip followed by reflection about the
input state's outer product, starting from that input state. -/
noncomputable def phaseIdealSearchState (ψ : QState I) (S : Finset I) (t : ℕ) : QState I :=
  ApplyGate ((ReflectionAbout (outerProduct ψ) * preparedMark S) ^ t) ψ

/-- For a normalized input with marked probability `sin(θ)^2` and `0 < θ < Real.pi / 2`, the
ideal iterate has marked probability `sin((2 * t + 1) * θ)^2`, the amplitude-amplification
formula [BrassardEtAl2002]. -/
private theorem phase_ideal_search_born (ψ : QState I) (S : Finset I) (θ : ℝ) (t : ℕ)
    (hψ : Normalized ψ) (hθ : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hp : MeasureProb ψ S = (Real.sin θ) ^ 2) :
    MeasureProb (phaseIdealSearchState ψ S t) S = (Real.sin ((2 * (t : ℝ) + 1) * θ)) ^ 2 := by
  obtain ⟨j, A, hA, hs⟩ := phase_source_preparation_exists ψ hψ
  have hi : preparedAAIterate A j S = ReflectionAbout (outerProduct ψ) * preparedMark S := by
    unfold preparedAAIterate
    rw [(prepared_aa_reflection_and_access A j S hA).2.2.1, hs]
  have hprob := prepared_aa_born_success A j S θ t hA hθ hθ1 (by simpa only [hs] using hp)
  rw [(prepared_aa_actual_circuit A j S t hA).2.2.2, hs, hi] at hprob
  exact hprob

/-- The ideal search state has Euclidean norm one whenever its input state is normalized. -/
theorem phaseIdealSearchState_norm (ψ : QState I) (S : Finset I) (t : ℕ)
    (hψ : Normalized ψ) : ‖toEuclidean_fromVec (phaseIdealSearchState ψ S t)‖ = 1 := by
  have hB := (Matrix.unitaryGroup I ℂ).mul_mem (outerProduct_reflection_unitary hψ)
    (phase_mark_unitary S)
  rw [phaseIdealSearchState, norm_applyGate_of_mem_unitaryGroup
    ((Matrix.unitaryGroup I ℂ).pow_mem hB t)]
  exact (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ

/-- One further ideal search iteration applies the marked sign flip and then the reflection
about the input state's outer product. -/
theorem phaseIdealSearchState_succ (ψ : QState I) (S : Finset I) (t : ℕ) :
    phaseIdealSearchState ψ S (t + 1) =
      ApplyGate (ReflectionAbout (outerProduct ψ))
        (ApplyGate (preparedMark S) (phaseIdealSearchState ψ S t)) := by
  rw [phaseIdealSearchState, pow_succ', applyGate_mul, applyGate_mul]
  rfl

/-- If marking preserves the span of the stated orthonormal family, every ideal iterate starting
at its distinguished member remains a linear combination of that family. -/
private theorem phase_ideal_search_reachable (J : Type) [Fintype J] [DecidableEq J]
    (j0 : J) (v : J → QState I) (S : Finset I)
    (hv : ∀ a b, Inner (v a) (v b) = if a = b then 1 else 0)
    (hmark : ∀ c : J → ℂ, ∃ d : J → ℂ,
      ApplyGate (preparedMark S) (∑ a, c a • v a) = ∑ a, d a • v a) (t : ℕ) :
    ∃ c : J → ℂ, phaseIdealSearchState (v j0) S t = ∑ a, c a • v a := by
  induction t with
  | zero =>
    refine ⟨fun a => if a = j0 then 1 else 0, ?_⟩
    simp [phaseIdealSearchState, applyGate_one, ite_smul]
  | succ t ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ := hmark c
    refine ⟨fun a => (if a = j0 then 2 * d j0 else 0) - d a, ?_⟩
    rw [phaseIdealSearchState_succ, hc, hd, phase_source_reflection_sum j0 v d hv]
    simp [sub_smul, Finset.sum_sub_distrib, ite_smul]

/-- With a unitary walk, `M >= 2`, a distinguished zero-phase member of an orthonormal
eigenfamily, phase separation `η > 0`, and marking that preserves the family span, the
actual search state is within `2 * t * (1 / (2 * M * η)) ^ k` of the embedded ideal iterate
in Euclidean norm. -/
theorem phase_search_reachable_state_error (J : Type) [Fintype J] [DecidableEq J]
    (j0 : J) (v : J → QState I) (p : J → ℝ) (W : Matrix I I ℂ) (S : Finset I)
    (M k t : ℕ) (η : ℝ) (hM : 2 ≤ M) (hη : 0 < η)
    (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (hv : ∀ a b, Inner (v a) (v b) = if a = b then 1 else 0)
    (heigen : ∀ a, ApplyGate W (v a) = Complex.exp (2 * Real.pi * Complex.I * p a) • v a)
    (hp0 : p j0 = 0) (hgap : ∀ a, a ≠ j0 → η ≤ phaseDistance (p a) 0)
    (hmark : ∀ c : J → ℂ, ∃ d : J → ℂ,
      ApplyGate (preparedMark S) (∑ a, c a • v a) = ∑ a, d a • v a) :
    ‖toEuclidean_fromVec (phaseSearchState W (v j0) S M k t -
      phaseReflectionEmbed M (k * t) (phaseIdealSearchState (v j0) S t))‖ ≤
      2 * (t : ℝ) * (1 / (2 * (M : ℝ) * η)) ^ k := by
  have hsource : Normalized (v j0) := (normalized_iff_inner_self _).mpr (by simpa using hv j0 j0)
  have hMp : 0 < M := by omega
  let C : ℝ := (1 / (2 * (M : ℝ) * η)) ^ k
  induction t with
  | zero => simp [phaseSearchState, phaseIdealSearchState, applyGate_one, toEuclidean_fromVec]
  | succ t ih =>
    let a := phaseSearchState W (v j0) S M k t
    let b := phaseReflectionEmbed M (k * t) (phaseIdealSearchState (v j0) S t)
    let s := ApplyGate (preparedMark S) (phaseIdealSearchState (v j0) S t)
    let r := ApplyGate (ReflectionAbout (outerProduct (v j0))) s
    let Z : QState (PhaseReflectionSpace I M (k * t)) →
        QState (PhaseReflectionSpace I M (k * (t + 1))) := fun q =>
      ApplyGate (phaseFreshReflectionMatrix W M k t)
        (ApplyGate (phaseSearchCheck S M (k * (t + 1))) (phaseFreshAppend M k t hMp q))
    have hfirst : ‖toEuclidean_fromVec (Z a - Z b)‖ = ‖toEuclidean_fromVec (a - b)‖ :=
      phase_fresh_round_norm_sub W S M k t hW hM a b
    have hZb : Z b = ApplyGate (phaseFreshReflectionMatrix W M k t)
        (phaseReflectionEmbed M (k * (t + 1)) s) := by
      dsimp only [Z, b, s]
      rw [phaseFreshAppend_embed, phaseSearchCheck_embed S M (k * (t + 1)) hMp]
    have hsecond : ‖toEuclidean_fromVec (Z b - phaseReflectionEmbed M (k * (t + 1)) r)‖ ≤ 2 * C := by
      obtain ⟨c, hc⟩ := phase_ideal_search_reachable J j0 v S hv hmark t
      obtain ⟨d, hd⟩ := hmark c
      have hs : s = ∑ a, d a • v a := by dsimp only [s]; rw [hc, hd]
      have hi : Normalized (phaseIdealSearchState (v j0) S t) :=
        (normalized_iff_norm_toEuclidean_fromVec _).mpr (phaseIdealSearchState_norm _ S t hsource)
      have hn : Normalized s := normalized_applyGate (phase_mark_unitary S) hi
      rw [hs] at hn
      rw [hZb]
      change ‖toEuclidean_fromVec
        (ApplyGate (phaseFreshReflectionMatrix W M k t) (phaseReflectionEmbed M (k * (t + 1)) s) -
         phaseReflectionEmbed M (k * (t + 1)) (ApplyGate (ReflectionAbout (outerProduct (v j0))) s))‖ ≤ _
      rw [hs]
      exact phase_fresh_reflection_reachable_error J j0 v p W M k t η hM hη hW hv heigen hp0 hgap d hn
    have he : phaseSearchState W (v j0) S M k (t + 1) -
        phaseReflectionEmbed M (k * (t + 1)) (phaseIdealSearchState (v j0) S (t + 1)) =
        (Z a - Z b) + (Z b - phaseReflectionEmbed M (k * (t + 1)) r) := by
      rw [phaseSearchState, dif_pos hMp, phaseIdealSearchState_succ]
      change Z a - phaseReflectionEmbed M (k * (t + 1)) r = _
      abel
    rw [he]
    change ‖toEuclidean_fromVec (Z a - Z b) +
      toEuclidean_fromVec (Z b - phaseReflectionEmbed M (k * (t + 1)) r)‖ ≤ _
    calc
      _ ≤ ‖toEuclidean_fromVec (Z a - Z b)‖ +
          ‖toEuclidean_fromVec (Z b - phaseReflectionEmbed M (k * (t + 1)) r)‖ := norm_add_le _ _
      _ ≤ 2 * (t : ℝ) * C + 2 * C := add_le_add (by rw [hfirst]; exact ih) hsecond
      _ = _ := by dsimp only [C]; push_cast; ring

/-- Under the reachable-eigenfamily and phase-gap hypotheses, initial marked mass `sin(θ)^2`
with `0 < θ < Real.pi / 2` yields actual marked mass at least `sin((2 * t + 1) * θ)^2 - 4 *
t * (1 / (2 * M * η)) ^ k`. The ideal term is the amplitude-amplification probability
[BrassardEtAl2002]. -/
theorem phase_search_actual_marked_success (J : Type) [Fintype J] [DecidableEq J]
    (j0 : J) (v : J → QState I) (p : J → ℝ) (W : Matrix I I ℂ) (S : Finset I)
    (M k t : ℕ) (η θ : ℝ) (hM : 2 ≤ M) (hη : 0 < η)
    (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (hv : ∀ a b, Inner (v a) (v b) = if a = b then 1 else 0)
    (heigen : ∀ a, ApplyGate W (v a) = Complex.exp (2 * Real.pi * Complex.I * p a) • v a)
    (hp0 : p j0 = 0) (hgap : ∀ a, a ≠ j0 → η ≤ phaseDistance (p a) 0)
    (hmark : ∀ c : J → ℂ, ∃ d : J → ℂ,
      ApplyGate (preparedMark S) (∑ a, c a • v a) = ∑ a, d a • v a)
    (hθ : 0 < θ) (hθ1 : θ < Real.pi / 2) (hp : MeasureProb (v j0) S = (Real.sin θ) ^ 2) :
    MeasureProb (phaseSearchState W (v j0) S M k t)
      (Finset.univ.filter (fun q => q.2.2 ∈ S)) ≥
      (Real.sin ((2 * (t : ℝ) + 1) * θ)) ^ 2 -
        4 * (t : ℝ) * (1 / (2 * (M : ℝ) * η)) ^ k := by
  have hsource : Normalized (v j0) := (normalized_iff_inner_self _).mpr (by simpa using hv j0 j0)
  have hactual : Normalized (phaseSearchState W (v j0) S M k t) :=
    (normalized_iff_norm_toEuclidean_fromVec _).mpr (by
      rw [phaseSearchState_norm W (v j0) S M k t hW hM]
      exact (normalized_iff_norm_toEuclidean_fromVec _).mp hsource)
  have hideal : Normalized (phaseReflectionEmbed M (k * t) (phaseIdealSearchState (v j0) S t)) :=
    (normalized_iff_norm_toEuclidean_fromVec _).mpr (by
      rw [phaseReflectionEmbed_norm M (k * t) (by omega)]
      exact phaseIdealSearchState_norm (v j0) S t hsource)
  have he :=
      phase_search_reachable_state_error J j0 v p W S M k t η hM hη hW hv heigen hp0 hgap hmark
  have hb := measureProb_sub_le_two_mul_l2
    (phaseSearchState W (v j0) S M k t)
    (phaseReflectionEmbed M (k * t) (phaseIdealSearchState (v j0) S t))
    (Finset.univ.filter (fun q => q.2.2 ∈ S)) hactual hideal
  rw [phaseReflectionEmbed_measureProb M (k * t) (by omega),
    phase_ideal_search_born (v j0) S θ t hsource hθ hθ1 hp] at hb
  have hbound := hb.trans (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2))
  have hl := (neg_le_abs _).trans hbound
  linarith

/-- For a unitary involution `W`, the phase-reflection construction with `M = 2` and `k = 1`
acts exactly as `W` on the system and returns the auxiliary registers to their embedding
state. -/
theorem phase_reflection_involutive_walk_exact (W : Matrix I I ℂ) (ψ : QState I)
    (hW : W ∈ Matrix.unitaryGroup I ℂ) (hWW : W * W = 1) :
    phaseReflectionState W 2 1 ψ = phaseReflectionEmbed 2 1 (ApplyGate W ψ) := by
  let plus := (1 / 2 : ℂ) • (ψ + ApplyGate W ψ)
  let minus := (1 / 2 : ℂ) • (ψ - ApplyGate W ψ)
  have hc : ApplyGate W (ApplyGate W ψ) = ψ := by rw [← applyGate_mul, hWW, applyGate_one]
  have hplus : ApplyGate W plus = Complex.exp (2 * Real.pi * Complex.I * (0 : ℝ)) • plus := by
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul]
    dsimp only [plus]
    simp only [ApplyGate, Matrix.mulVec_smul, Matrix.mulVec_add]
    change (1 / 2 : ℂ) • (ApplyGate W ψ + ApplyGate W (ApplyGate W ψ)) = _
    rw [hc]
    change (1 / 2 : ℂ) • (ApplyGate W ψ + ψ) = (1 / 2 : ℂ) • (ψ + ApplyGate W ψ)
    module
  have hex : Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℝ)) = -1 := by
    rw [show (2 * Real.pi * Complex.I * (1 / 2 : ℝ) : ℂ) = Real.pi * Complex.I by push_cast; ring,
      Complex.exp_pi_mul_I]
  have hminus : ApplyGate W minus = Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℝ)) • minus := by
    rw [hex]
    dsimp only [minus]
    simp only [ApplyGate, Matrix.mulVec_smul, Matrix.mulVec_sub]
    change (1 / 2 : ℂ) • (ApplyGate W ψ - ApplyGate W (ApplyGate W ψ)) = _
    rw [hc]
    change (1 / 2 : ℂ) • (ApplyGate W ψ - ψ) =
      (-1 : ℂ) • ((1 / 2 : ℂ) • (ψ - ApplyGate W ψ))
    module
  have hp := (phase_reflection_actual_eigenstate_error 2 1 (by norm_num) W plus 0 hW hplus).1
    (by norm_num [phaseDistance])
  have hk : qpeKernel 2 (1 / 2) (⟨0, by decide⟩ : Fin 2) = 0 := by
    have h := (offgrid_phase_geometric_and_periodic 2 0 (0 : Fin 2) (by norm_num)).2.2 (1 : Fin 2)
    simpa [Ket] using h
  have hm := phase_reflection_eigenstate_residual 2 1 (by norm_num) W minus (1 / 2) hW hminus
  have hz : phaseReflectionState W 2 1 minus + phaseReflectionEmbed 2 1 minus = 0 := by
    simp only [pow_one] at hm
    rw [hk] at hm
    simpa only [zero_smul, smul_zero, ApplyGate, Matrix.mulVec_zero] using hm
  have hn : phaseReflectionState W 2 1 minus = -phaseReflectionEmbed 2 1 minus := by
    calc
      _ = (phaseReflectionState W 2 1 minus + phaseReflectionEmbed 2 1 minus) -
          phaseReflectionEmbed 2 1 minus := by abel
      _ = _ := by rw [hz]; simp
  have hψ : ψ = plus + minus := by dsimp only [plus, minus]; module
  have hWψ : ApplyGate W ψ = plus - minus := by dsimp only [plus, minus]; module
  calc
    _ = phaseReflectionState W 2 1 plus + phaseReflectionState W 2 1 minus := by
      rw [hψ, phaseReflectionState_add]
    _ = phaseReflectionEmbed 2 1 plus - phaseReflectionEmbed 2 1 minus := by rw [hp, hn]; rfl
    _ = _ := by rw [hWψ, phaseReflectionEmbed_sub]

omit [Fintype I] [DecidableEq I] in

/-- With one fresh register and no old phase registers, relabeling the tensor product with the
empty zero-register ket leaves the fresh phase-reflection state unchanged. -/
private theorem phase_fresh_action_empty_old (M : ℕ) (hM : 0 < M)
    (ψ : QState (PhaseReflectionSpace I M 1)) :
    relabelState (phaseFreshActionSplit I M 1 0).symm
      (TensorState (Ket (phaseZeroIndex M 0 hM)) ψ) = ψ := by
  funext q
  have hz : (phaseFreshActionSplit I M 1 0 q).1 = phaseZeroIndex M 0 hM := by
    funext j
    have := j.isLt
    omega
  simp only [relabelState, Equiv.symm_symm, Function.comp_apply, TensorState, Ket, hz,
    ite_true, one_mul]
  congr 1

/-- A single search round with one fresh phase register is exactly `phaseReflectionState`
applied to the marked-sign-flipped input, for every positive `M`. -/
theorem phaseSearchState_one_register_round (W : Matrix I I ℂ) (ψ : QState I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) :
    phaseSearchState W ψ S M 1 1 = phaseReflectionState W M 1 (ApplyGate (preparedMark S) ψ) := by
  rw [phaseSearchState, dif_pos hM, phaseSearchState, phaseFreshAppend_embed,
    phaseSearchCheck_embed S M (1 * (0 + 1)) hM,
    phaseFreshReflectionMatrix_embed W M 1 0 hM, phase_fresh_action_empty_old]

end FreshSearch

/-- The tensor product of two three-dimensional QFT matrices used to prepare the uniform state
on pairs of three-point indices. -/
noncomputable def phaseSearchUniformThreeSetup :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := TensorGate (QFTMatrix 3) (QFTMatrix 3)

/-- The three-point setup matrix is unitary and maps the tensor product of two zero kets to the
state with constant amplitude `1 / 3`. -/
theorem phaseSearchUniformThreeSetup_prepares :
    phaseSearchUniformThreeSetup ∈ Matrix.unitaryGroup (Fin 3 × Fin 3) ℂ ∧
    ApplyGate phaseSearchUniformThreeSetup (TensorState (Ket (0 : Fin 3)) (Ket (0 : Fin 3))) =
      (fun _ => (1 / 3 : ℂ)) := by
  refine ⟨tensorGate_unitary (qftMatrix_unitary (by decide)) (qftMatrix_unitary (by decide)), ?_⟩
  rw [phaseSearchUniformThreeSetup, applyGate_tensorGate]
  change TensorState (ApplyGate (QFTMatrix 3) (Ket (⟨0, by decide⟩ : Fin 3)))
    (ApplyGate (QFTMatrix 3) (Ket (⟨0, by decide⟩ : Fin 3))) = _
  rw [qftMatrix_ket_zero 3 (by decide)]
  funext p
  change (Real.sqrt (3 : ℝ) : ℂ)⁻¹ * (Real.sqrt (3 : ℝ) : ℂ)⁻¹ = 1 / 3
  rw [← mul_inv, ← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (by norm_num)]
  norm_num

/-- For the uniform three-point transition matrix, the Szegedy isometry range projector is
identity on the first register tensored with the uniform-state projector on the second. -/
private theorem phase_uniform_three_projector :
    let P : Fin 3 → Fin 3 → ℝ := fun _ _ => 1 / 3
    SzegedyIsometry P * (SzegedyIsometry P)ᴴ =
      TensorGate (1 : Matrix (Fin 3) (Fin 3) ℂ) (AverageProjection (Fin 3)) := by
  (try dsimp only)
  have hs : (Real.sqrt (1 / 3 : ℝ) : ℂ) * (Real.sqrt (1 / 3 : ℝ) : ℂ) = 1 / 3 := by
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
    SzegedyIsometry, Matrix.of_apply,
    apply_ite, Complex.conj_ofReal, map_zero, TensorGate, Matrix.kronecker_apply,
    Matrix.one_apply, AverageProjection, Fintype.card_fin]
  rw [Finset.sum_eq_single a]
  · by_cases h : a = c
    · subst c
      simp only [ite_true, hs, one_mul]
      norm_num
    · simp only [ite_true, if_neg (Ne.symm h), if_neg h, mul_zero, zero_mul]
  · intro x _ hxa
    simp only [if_neg (Ne.symm hxa), zero_mul, ite_self]
  · simp

/-- Conjugating a tensor product of two gates by `SwapGate` exchanges the two tensor factors. -/
private theorem phase_swap_tensor {I : Type} [Fintype I] [DecidableEq I]
    (U V : Matrix I I ℂ) : SwapGate * TensorGate U V * SwapGate = TensorGate V U := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [SwapGate, permMatrix, Matrix.mul_apply, TensorGate, Fintype.sum_prod_type,
    Prod.ext_iff, ite_and, eq_comm, mul_comm]

/-- The Szegedy walk for the uniform three-point transition matrix is the tensor product of the
two three-dimensional diffusion gates. -/
private theorem phase_uniform_three_walk :
    SzegedyWalk (fun _ _ : Fin 3 => (1 / 3 : ℝ)) =
      TensorGate (Diffusion (Fin 3)) (Diffusion (Fin 3)) := by
  have hr : SzegedyReflection (fun _ _ : Fin 3 => (1 / 3 : ℝ)) =
      TensorGate (1 : Matrix (Fin 3) (Fin 3) ℂ) (Diffusion (Fin 3)) := by
    rw [SzegedyReflection, phase_uniform_three_projector]
    ext ⟨a, b⟩ ⟨c, d⟩
    simp [ReflectionAbout, Diffusion, TensorGate, Matrix.one_apply, mul_sub, mul_comm]
    by_cases h : a = c <;> simp [h]
  rw [SzegedyWalk, hr, phase_swap_tensor, tensorGate_mul, Matrix.mul_one, Matrix.one_mul]

/-- For the uniform three-point Szegedy walk and constant pair-state input, one search round
with `M = 2` and `k = 1` gives probability `25 / 27` of a zero first system coordinate. Its
phase-query, marked-check, and setup ledger is `(2, 1, 1)`. -/
theorem phase_search_uniform_three_actual_consumer :
    let P : Fin 3 → Fin 3 → ℝ := fun _ _ => 1 / 3
    let ψ : QState (Fin 3 × Fin 3) := fun _ => (1 / 3 : ℂ)
    let S := Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 = 0)
    MeasureProb (phaseSearchState (SzegedyWalk P) ψ S 2 1 1)
      (Finset.univ.filter (fun x => x.2.2 ∈ S)) = 25 / 27 ∧
      phaseSearchLedger 2 1 1 = (2, 1, 1) := by
  (try dsimp only)
  let P : Fin 3 → Fin 3 → ℝ := fun _ _ => 1 / 3
  let ψ : QState (Fin 3 × Fin 3) := fun _ => (1 / 3 : ℂ)
  let S := Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 = 0)
  have hP : IsTransitionMatrix P := by norm_num [IsTransitionMatrix, P, Fin.sum_univ_succ]
  have hW := szegedyWalk_unitary P hP
  have hWW : SzegedyWalk P * SzegedyWalk P = 1 := by
    dsimp only [P]
    rw [phase_uniform_three_walk, tensorGate_mul, diffusion_mul_self (by simp), tensorGate_one]
  refine ⟨?_, phase_search_fresh_access_ledger 2 1 1 (by decide)⟩
  change MeasureProb (phaseSearchState (SzegedyWalk P) ψ S 2 1 1) _ = _
  rw [phaseSearchState_one_register_round _ _ _ 2 (by decide),
    phase_reflection_involutive_walk_exact _ _ hW hWW,
    phaseReflectionEmbed_measureProb 2 1 (by decide)]
  have ha : ApplyGate (SzegedyWalk P) (ApplyGate (preparedMark S) ψ) =
      (fun q => if q.1 = 0 then (5 / 9 : ℂ) else (-1 / 9 : ℂ)) := by
    have hm : ApplyGate (preparedMark S) ψ =
        TensorState (fun a : Fin 3 => if a = 0 then (-1 / 3 : ℂ) else (1 / 3 : ℂ))
          (fun _ : Fin 3 => (1 : ℂ)) := by
      simp only [preparedMark, ApplyGate, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec]
      change ψ - (2 : ℂ) • Collapse ψ S = _
      funext q
      by_cases h : q.1 = 0 <;> simp [collapse_apply, TensorState, ψ, S, h]
      ring
    dsimp only [P]
    rw [phase_uniform_three_walk, hm, applyGate_tensorGate]
    funext ⟨a, b⟩
    simp only [TensorState, applyGate_diffusion, Fintype.card_fin]
    fin_cases a <;> norm_num [Fin.sum_univ_succ]
  rw [ha]
  norm_num [MeasureProb, BornProb, S, Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Starting from the state produced by `phaseSearchUniformThreeSetup` on two zero kets, the
uniform three-point search attains marked probability `25 / 27` with ledger `(2, 1, 1)` for
`M = 2`, `k = 1`, and one round. -/
theorem phase_search_uniform_three_prepared_consumer :
    let P : Fin 3 → Fin 3 → ℝ := fun _ _ => 1 / 3
    let S := Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 = 0)
    MeasureProb (phaseSearchState (SzegedyWalk P)
      (ApplyGate phaseSearchUniformThreeSetup (TensorState (Ket (0 : Fin 3)) (Ket (0 : Fin 3))))
      S 2 1 1) (Finset.univ.filter (fun x => x.2.2 ∈ S)) = 25 / 27 ∧
      phaseSearchLedger 2 1 1 = (2, 1, 1) := by
  (try dsimp only)
  rw [phaseSearchUniformThreeSetup_prepares.2]
  exact phase_search_uniform_three_actual_consumer

end Qatlib.Concepts.WalkFind.UniformThree
