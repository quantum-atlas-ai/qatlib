/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.GridExactHHL.GridHHLSolutionOutput
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.QueryWordCore.AdjointCircuits
import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.BlockEncoding.Postselection

/-!
# Counted HHL words and clean-branch stability

This module expresses finite-grid HHL preparation, phase estimation, reciprocal flag rotation,
and uncomputation as an adjoint-step word. It relates the evaluated word to the grid circuit and
identifies its unnormalized clean branch with a scaled matrix-pseudoinverse action, following
the inverse-eigenvalue construction of [HarrowHassidimLloyd2009].

The module also proves exact query and gate counts and a perturbation bound linear in the query
count. In particular, the clean branch changes by at most `2 * (M - 1) * δ` when the unitary
data oracle changes by operator norm at most `δ`, under the stated preparation and rotation
hypotheses.

## Main statements

* `counted_hhl_actual_word_and_access_counts`: well-formedness, `2 * (M - 1)` queries, and `4 *
  (M - 1) + 6` gates.
* `countedHHLWord_apply`: agreement of word evaluation with the grid HHL circuit.
* `counted_hhl_exact_grid_clean_branch`: the exact scaled pseudoinverse branch on the spectral
  grid.
* `norm_evaluate_sub_evaluate_le`: the query-count perturbation bound for adjoint words.
* `counted_hhl_unitary_oracle_clean_branch_noise`: the resulting clean-branch error bound.

## References

* [Harrow, Hassidim, and Lloyd, 2009][HarrowHassidimLloyd2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.BlockEncoding.Postselection

namespace Qatlib.Concepts.NativeNumerics.LayeredMean

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical Matrix.Norms.L2Operator

/-- Embed a circuit step into adjoint-step syntax, preserving gates and turning each oracle
query into a forward query. -/
def stepToAdjoint {I : Type*} : Step I → AdjointStep I
  | .gate U => .gate U
  | .query => .forward

/-- Embedding a circuit into adjoint-step syntax preserves its oracle query count. -/
theorem adjointQueryCount_map_stepToAdjoint {I : Type*} (C : Circuit I) :
    adjointQueryCount (C.map stepToAdjoint) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [stepToAdjoint, adjointQueryCount, QueryCount, ih]

/-- Embedding a circuit into adjoint-step syntax preserves its gate count. -/
theorem adjointGateCount_map_stepToAdjoint {I : Type*} (C : Circuit I) :
    adjointGateCount (C.map stepToAdjoint) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [stepToAdjoint, adjointGateCount, GateCount, ih]

/-- Reversing an adjoint-step list preserves its query count. -/
theorem adjointQueryCount_reverse {I : Type*} (cs : List (AdjointStep I)) :
    adjointQueryCount cs.reverse = adjointQueryCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.reverse_cons, adjointQueryCount_append, ih]
    cases c <;> simp [adjointQueryCount]

/-- Reversing an adjoint-step list preserves its gate count. -/
theorem adjointGateCount_reverse {I : Type*} (cs : List (AdjointStep I)) :
    adjointGateCount cs.reverse = adjointGateCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.reverse_cons, adjointGateCount_append, ih]
    cases c <;> simp [adjointGateCount]

/-- Embedding and reversing a unitary circuit produces a well-formed adjoint circuit. -/
theorem wellFormedAdjointCircuit_stepToAdjoint_reverse {I : Type*} [Fintype I] [DecidableEq I]
    (C : Circuit I) (hC : IsUnitaryCircuit C) :
    WellFormedAdjointCircuit ((C.map stepToAdjoint).reverse) := by
  intro V hV
  rw [List.mem_reverse] at hV
  obtain ⟨t, ht, hte⟩ := List.mem_map.mp hV
  cases t with
  | gate U =>
      simp only [stepToAdjoint, AdjointStep.gate.injEq] at hte
      exact hte ▸ hC _ ht
  | query => simp [stepToAdjoint] at hte

/-- Running a circuit equals applying the matrix obtained by evaluating its reversed
adjoint-step embedding. -/
theorem run_eq_evaluate {I : Type*} [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) :
    ∀ (C : Circuit I) (ψ : QState I),
    Run O C ψ = ApplyGate (evaluate O ((C.map stepToAdjoint).reverse)) ψ := by
  intro C
  induction C with
  | nil => intro ψ; simp [evaluate, applyGate_one]
  | cons s C ih =>
    intro ψ
    have hmap : ∀ (s : Step I), (List.map stepToAdjoint (s :: C)).reverse
        = (C.map stepToAdjoint).reverse ++ [stepToAdjoint s] := by
      intro s
      simp [List.map_cons, List.reverse_cons]
    have key : ∀ (X Y : Matrix I I ℂ) (v : QState I),
        ApplyGate X (ApplyGate Y v) = ApplyGate (X * Y) v := by
      intro X Y v
      show X *ᵥ (Y *ᵥ v) = (X * Y) *ᵥ v
      exact Matrix.mulVec_mulVec v X Y
    cases s with
    | gate U =>
        rw [run_gate, ih (ApplyGate U ψ), hmap (Step.gate U), evaluate_append]
        simp only [evaluate, instructionMatrix, stepToAdjoint]
        rw [key, mul_one]
    | query =>
        rw [run_query, ih (ApplyGate O ψ), hmap (Step.query), evaluate_append]
        simp only [evaluate, instructionMatrix, stepToAdjoint]
        rw [key, mul_one]

/-- The register equivalence moving an extra Boolean sector register between the phase register
and the flag-data pair. -/
def countedHHLSectorEquiv (D M : ℕ) :
    Bool × (Fin M × (Bool × Fin D)) ≃ Fin M × (Bool × (Bool × Fin D)) :=
  (Equiv.prodComm Bool (Fin M × (Bool × Fin D))).trans
    ((Equiv.prodAssoc (Fin M) (Bool × Fin D) Bool).trans
      (Equiv.prodCongr (Equiv.refl (Fin M)) (Equiv.prodComm (Bool × Fin D) Bool)))

/-- The phase-flag embedding is the relabelling of the state tensored with an extra sector qubit
in `Ket false`. -/
theorem phaseFlagEmbed_eq_sector (D M : ℕ) (φ : QState (Fin M × (Bool × Fin D))) :
    phaseFlagEmbed (I := Bool × Fin D) M φ
      = relabelState (countedHHLSectorEquiv D M) (TensorState (Ket false) φ) := by
  funext p
  obtain ⟨a, s, f, i⟩ := p
  cases s <;>
    simp [phaseFlagEmbed, relabelState, countedHHLSectorEquiv, TensorState, Ket]

/-- Lift a gate to the counted HHL registers by tensoring with the identity on the extra sector
qubit and relabelling. -/
noncomputable def countedHHLLiftGate {D M : ℕ}
    (G : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) :
    Matrix (Fin M × (Bool × (Bool × Fin D))) (Fin M × (Bool × (Bool × Fin D))) ℂ :=
  relabelGate (countedHHLSectorEquiv D M) (TensorGate (1 : Matrix Bool Bool ℂ) G)

/-- Lifting a unitary gate to the counted HHL registers preserves unitarity. -/
theorem countedHHLLiftGate_unitary {D M : ℕ}
    {G : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ}
    (hG : G ∈ Matrix.unitaryGroup (Fin M × (Bool × Fin D)) ℂ) :
    countedHHLLiftGate (D := D) (M := M) G
      ∈ Matrix.unitaryGroup (Fin M × (Bool × (Bool × Fin D))) ℂ :=
  (relabelGate_mem_unitaryGroup _ _).2 (tensorGate_unitary (Submonoid.one_mem _) hG)

/-- A lifted gate acts on a phase-flag embedded state by embedding the result of the original
gate. -/
theorem countedHHLLiftGate_apply {D M : ℕ}
    (G : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
    (φ : QState (Fin M × (Bool × Fin D))) :
    ApplyGate (countedHHLLiftGate (D := D) (M := M) G) (phaseFlagEmbed (I := Bool × Fin D) M φ)
      = phaseFlagEmbed M (ApplyGate G φ) := by
  rw [countedHHLLiftGate, phaseFlagEmbed_eq_sector, applyGate_relabelGate, applyGate_tensorGate,
    applyGate_one, ← phaseFlagEmbed_eq_sector]

/-- The controlled data oracle on the counted HHL registers, acting trivially on the phase
register and the original flag qubit. -/
noncomputable def countedHHLOracleLift {D M : ℕ} (U : Operator D) :
    Matrix (Fin M × (Bool × (Bool × Fin D))) (Fin M × (Bool × (Bool × Fin D))) ℂ :=
  TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
    (controlOracle (TensorGate (1 : Matrix Bool Bool ℂ) U))

/-- The counted HHL oracle lift of a unitary data operator is unitary. -/
theorem countedHHLOracleLift_unitary {D M : ℕ} {U : Operator D}
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    countedHHLOracleLift (D := D) (M := M) U
      ∈ Matrix.unitaryGroup (Fin M × (Bool × (Bool × Fin D))) ℂ :=
  tensorGate_unitary (Submonoid.one_mem _)
    (controlOracle_unitary (tensorGate_unitary (Submonoid.one_mem _) hU))

/-- The adjoint-step word obtained by embedding and reversing the counted phase-estimation
circuit. -/
noncomputable def countedQPEWord (D M : ℕ) :
    List (AdjointStep (Fin M × (Bool × (Bool × Fin D)))) :=
  ((countedPhaseCircuit (I := Bool × Fin D) M).map stepToAdjoint).reverse

/-- For positive phase-register size, the counted phase-estimation word is well formed. -/
theorem countedQPEWord_wellFormed (D M : ℕ) (hM : 0 < M) :
    WellFormedAdjointCircuit (countedQPEWord D M) :=
  wellFormedAdjointCircuit_stepToAdjoint_reverse _
    (counted_offgrid_qpe_clean_flag (I := Bool × Fin D) M hM
      (1 : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) 0).2.2.2

/-- For positive `M`, the counted phase-estimation word has `M - 1` queries and `2 * (M - 1) +
2` gates. -/
theorem countedQPEWord_counts (D M : ℕ) (hM : 0 < M) :
    adjointQueryCount (countedQPEWord D M) = M - 1 ∧
      adjointGateCount (countedQPEWord D M) = 2 * (M - 1) + 2 := by
  have h := counted_offgrid_qpe_clean_flag (I := Bool × Fin D) M hM
    (1 : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) 0
  constructor
  · rw [countedQPEWord, adjointQueryCount_reverse, adjointQueryCount_map_stepToAdjoint]
    exact h.2.1
  · rw [countedQPEWord, adjointGateCount_reverse, adjointGateCount_map_stepToAdjoint]
    exact h.2.2.1

/-- The preparation gate applying `B` to the data register and identities to the phase and flag
registers. -/
noncomputable def countedHHLPrepMain {D M : ℕ} (B : Operator D) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  relabelGate (gridHHLPhaseData (D := D) (M := M))
    (TensorGate (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) B) (1 : Matrix Bool Bool ℂ))

/-- The HHL preparation gate is unitary whenever the data preparation operator `B` is unitary. -/
theorem countedHHLPrepMain_unitary {D M : ℕ} {B : Operator D}
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    countedHHLPrepMain (D := D) (M := M) B
      ∈ Matrix.unitaryGroup (Fin M × (Bool × Fin D)) ℂ :=
  (relabelGate_mem_unitaryGroup _ _).2
    (tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) hB) (Submonoid.one_mem _))

/-- The HHL preparation gate applies `B` to `Ket j` while preserving the zero phase state and
false flag. -/
theorem countedHHLPrepMain_apply {D M : ℕ} (hM : 0 < M) (B : Operator D) (j : Fin D) :
    ApplyGate (countedHHLPrepMain (D := D) (M := M) B)
        (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket false) (Ket j)))
      = TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket false) (ApplyGate B (Ket j))) := by
  have hprod (χ : QState (Fin D)) : TensorState (Ket (⟨0, hM⟩ : Fin M))
        (TensorState (Ket false) χ)
      = relabelState (gridHHLPhaseData (D := D) (M := M))
          (TensorState (TensorState (Ket (⟨0, hM⟩ : Fin M)) χ) (Ket false)) := by
    funext p
    obtain ⟨a, f, i⟩ := p
    simp [TensorState, Ket, relabelState, gridHHLPhaseData]
  rw [countedHHLPrepMain, hprod (Ket j), applyGate_relabelGate, applyGate_tensorGate,
    applyGate_tensorGate, applyGate_one, applyGate_one, hprod]

/-- The adjoint-step word encoding data preparation, phase estimation, the reciprocal flag
rotation, and phase uncomputation. -/
noncomputable def countedHHLWord {D : ℕ} (M : ℕ) (c : ℝ) (B : Operator D) :
    List (AdjointStep (Fin M × (Bool × (Bool × Fin D)))) :=
  adjointCircuit (countedQPEWord D M) ++ [.gate (countedHHLLiftGate (gridHHLFlag (D := D) c))] ++
    countedQPEWord D M ++ [.gate (countedHHLLiftGate (countedHHLPrepMain (D := D) (M := M) B))]

/-- For positive `M`, the counted HHL word uses exactly `2 * (M - 1)` oracle queries. -/
theorem countedHHLWord_queryCount {D : ℕ} (M : ℕ) (c : ℝ) (B : Operator D) (hM : 0 < M) :
    adjointQueryCount (countedHHLWord (D := D) M c B) = 2 * (M - 1) := by
  rw [countedHHLWord, adjointQueryCount_append, adjointQueryCount_append,
    adjointQueryCount_append, adjointQueryCount_adjointCircuit,
    (countedQPEWord_counts D M hM).1]
  simp only [adjointQueryCount]
  omega

/-- For positive `M`, the counted HHL word contains exactly `4 * (M - 1) + 6` gates. -/
theorem countedHHLWord_gateCount {D : ℕ} (M : ℕ) (c : ℝ) (B : Operator D) (hM : 0 < M) :
    adjointGateCount (countedHHLWord (D := D) M c B) = 4 * (M - 1) + 6 := by
  rw [countedHHLWord, adjointGateCount_append, adjointGateCount_append,
    adjointGateCount_append, adjointGateCount_adjointCircuit,
    (countedQPEWord_counts D M hM).2]
  simp only [adjointGateCount]
  omega

/-- For `2 ≤ M`, unitary preparation, and `0 ≤ c ≤ 1 / M`, the counted HHL word is well formed
with `2 * (M - 1)` queries and `4 * (M - 1) + 6` gates. -/
theorem counted_hhl_actual_word_and_access_counts :
    ∀ (D M : ℕ) (c : ℝ) (B : Operator D), 2 ≤ M → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
      0 ≤ c → c ≤ 1 / (M : ℝ) →
      WellFormedAdjointCircuit (countedHHLWord M c B) ∧
        adjointQueryCount (countedHHLWord M c B) = 2 * (M - 1) ∧
        adjointGateCount (countedHHLWord M c B) = 4 * (M - 1) + 6 := by
  intro D M c B hM hB hc0 hc1
  have hMpos : 0 < M := by omega
  have hwf := countedQPEWord_wellFormed D M hMpos
  have hrot : gridHHLRotation M c ∈ Matrix.unitaryGroup (Fin M × Bool) ℂ :=
    (grid_hhl_reciprocal_rotation_unitary M c hMpos hc0 hc1).1
  refine ⟨?_, countedHHLWord_queryCount M c B hMpos, countedHHLWord_gateCount M c B hMpos⟩
  simp only [countedHHLWord, WellFormedAdjointCircuit.append_iff,
    WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
  exact ⟨⟨⟨hwf.adjointCircuit, countedHHLLiftGate_unitary (gridHHLFlag_unitary c hrot)⟩, hwf⟩,
    countedHHLLiftGate_unitary (countedHHLPrepMain_unitary hB)⟩

/-- The unnormalized data branch of the evaluated HHL word with phase zero, sector false, and
flag true, defined as zero when `M = 0`. -/
noncomputable def countedHHLCleanBranch {D : ℕ} (U : Operator D) (M : ℕ) (c : ℝ)
    (B : Operator D) (j : Fin D) : QState (Fin D) :=
  fun i =>
    if hM : 0 < M then
      (ApplyGate (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedHHLWord M c B))
        (TensorState (Ket (⟨0, hM⟩ : Fin M))
          (TensorState (Ket false) (TensorState (Ket false) (Ket j)))))
        ((⟨0, hM⟩ : Fin M), (false, (true, i)))
    else 0

/-- A phase-only gate on the counted registers equals the lift of the corresponding phase-only
gate on the original registers. -/
theorem countedHHL_phaseLift_eq (D M : ℕ) (Q : Matrix (Fin M) (Fin M) ℂ) :
    TensorGate Q (1 : Matrix (Bool × (Bool × Fin D)) (Bool × (Bool × Fin D)) ℂ)
      = countedHHLLiftGate (D := D) (M := M) (TensorGate Q
          (1 : Matrix (Bool × Fin D) (Bool × Fin D) ℂ)) := by
  ext p q
  obtain ⟨a, s, f, i⟩ := p
  obtain ⟨a', s', f', i'⟩ := q
  simp only [TensorGate, Matrix.kroneckerMap, Matrix.of_apply, Matrix.one_apply,
    countedHHLLiftGate, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    countedHHLSectorEquiv]
  by_cases hss : s = s'
  · subst hss
    by_cases hrest : (f, i) = (f', i')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest
      simp
    · simp [hrest]
  · simp [hss]

/-- Applying a phase-only gate commutes with the phase-flag embedding. -/
theorem countedHHL_phaseLift_apply (D M : ℕ) (Q : Matrix (Fin M) (Fin M) ℂ)
    (φ : QState (Fin M × (Bool × Fin D))) :
    ApplyGate (TensorGate Q (1 : Matrix (Bool × (Bool × Fin D)) (Bool × (Bool × Fin D)) ℂ))
        (phaseFlagEmbed (I := Bool × Fin D) M φ)
      = phaseFlagEmbed M (ApplyGate (TensorGate Q
          (1 : Matrix (Bool × Fin D) (Bool × Fin D) ℂ)) φ) := by
  rw [countedHHL_phaseLift_eq]
  exact countedHHLLiftGate_apply _ _

/-- The grid HHL Fourier lift is the tensor product of the given phase matrix with the identity
on flag and data. -/
theorem gridHHLFourier_eq (D M : ℕ) (Q : Matrix (Fin M) (Fin M) ℂ) :
    gridHHLFourier (D := D) (M := M) Q
      = TensorGate Q (1 : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) := by
  ext p q
  obtain ⟨a, f, i⟩ := p
  obtain ⟨a', f', i'⟩ := q
  simp only [gridHHLFourier, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    gridHHLPhaseData_symm_apply, TensorGate, Matrix.kroneckerMap, Matrix.of_apply,
    Matrix.one_apply]
  by_cases hf : f = f'
  · subst hf
    by_cases hi : i = i'
    · subst hi
      simp
    · simp [hi]
  · simp [hf]

/-- Tensoring a data operator with the Boolean identity applies that operator independently in
each Boolean sector. -/
theorem tensorGate_one_mulVec {D : ℕ} (W : Operator D) (ξ : QState (Bool × Fin D))
    (f : Bool) (i : Fin D) :
    (TensorGate (1 : Matrix Bool Bool ℂ) W *ᵥ ξ) (f, i)
      = (W *ᵥ (fun i' => ξ (f, i'))) i := by
  show ∑ q : Bool × Fin D,
      (TensorGate (1 : Matrix Bool Bool ℂ) W) (f, i) q * ξ q = _
  simp only [TensorGate, Matrix.kroneckerMap, Matrix.of_apply, Fintype.sum_prod_type,
    Matrix.one_apply]
  rw [Finset.sum_eq_single f]
  · simp [Matrix.mulVec, dotProduct]
  · intro f' _ hf'
    simp [show f ≠ f' from fun e => hf' e.symm]
  · intro h
    exact absurd (Finset.mem_univ f) h

/-- Powers of a data operator tensored with the Boolean identity are obtained by tensoring its
powers with that identity. -/
theorem tensorGate_one_pow {D : ℕ} (W : Operator D) (k : ℕ) :
    (TensorGate (1 : Matrix Bool Bool ℂ) W) ^ k
      = TensorGate (1 : Matrix Bool Bool ℂ) (W ^ k) := by
  induction k with
  | zero => simp [pow_zero, tensorGate_one]
  | succ k ih =>
    rw [pow_succ, ih, tensorGate_mul, pow_succ]
    simp

/-- In phase sector `a`, the grid HHL power gate applies `U ^ a.val` to the data slice and
preserves the flag. -/
theorem gridHHLPowers_mulVec {D M : ℕ} (U : Operator D)
    (φ : QState (Fin M × (Bool × Fin D))) (a : Fin M) (f : Bool) (i : Fin D) :
    (gridHHLPowers (D := D) (M := M) U *ᵥ φ) (a, (f, i))
      = (U ^ (a.val : ℕ) *ᵥ (fun i' => φ (a, (f, i')))) i := by
  have hentry : ∀ (a' : Fin M) (f' : Bool) (i' : Fin D),
      (gridHHLPowers (D := D) (M := M) U) (a, (f, i)) (a', (f', i'))
        = if a = a' then if f = f' then (U ^ (a.val : ℕ)) i i' else 0 else 0 := by
    intro a' f' i'
    rw [gridHHLPowers, relabelGate_submatrix]
    simp only [gridHHLPhaseData_symm_apply, TensorGate, Matrix.kroneckerMap, Matrix.of_apply,
      Matrix.one_apply, ControlledPowers]
    by_cases ha : a = a'
    · subst ha
      by_cases hf : f = f'
      · subst hf
        simp
      · simp [hf]
    · simp [ha]
  show ∑ q : Fin M × (Bool × Fin D),
      (gridHHLPowers (D := D) (M := M) U) (a, (f, i)) q * φ q = _
  simp only [Fintype.sum_prod_type, hentry]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single f]
    · simp [Matrix.mulVec, dotProduct]
    · intro f' _ hf'
      simp [show f ≠ f' from fun e => hf' e.symm]
    · intro h
      exact absurd (Finset.mem_univ f) h
  · intro a' _ ha'
    simp [show a ≠ a' from fun e => ha' e.symm]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The counted phase-estimation circuit with the lifted oracle acts on embedded states as the
embedded grid HHL phase-estimation block. -/
theorem countedPhaseCircuit_run_eq (D M : ℕ) (hM : 0 < M) (U : Operator D)
    (φ : QState (Fin M × (Bool × Fin D))) :
    Run (countedHHLOracleLift (D := D) (M := M) U) (countedPhaseCircuit (I := Bool × Fin D) M)
        (phaseFlagEmbed (I := Bool × Fin D) M φ)
      = phaseFlagEmbed M (Run 1 (gridHHLQPEBlock (D := D) (M := M) U) φ) := by
  have hstep1 : ApplyGate (TensorGate (QFTMatrix M)
          (1 : Matrix (Bool × (Bool × Fin D)) (Bool × (Bool × Fin D)) ℂ))
        (phaseFlagEmbed (I := Bool × Fin D) M φ)
      = phaseFlagEmbed M (ApplyGate (TensorGate (QFTMatrix M)
          (1 : Matrix (Bool × Fin D) (Bool × Fin D) ℂ)) φ) :=
    countedHHL_phaseLift_apply D M _ φ
  have hstep1' : ∀ (ψ : QState (Fin M × (Bool × Fin D))),
      ApplyGate (TensorGate (QFTMatrix M)ᴴ
          (1 : Matrix (Bool × (Bool × Fin D)) (Bool × (Bool × Fin D)) ℂ))
        (phaseFlagEmbed (I := Bool × Fin D) M ψ)
      = phaseFlagEmbed M (ApplyGate (TensorGate (QFTMatrix M)ᴴ
          (1 : Matrix (Bool × Fin D) (Bool × Fin D) ℂ)) ψ) :=
    fun ψ => countedHHL_phaseLift_apply D M _ ψ
  set Ξ : QState (Fin M × (Bool × Fin D)) :=
    ApplyGate (TensorGate (QFTMatrix M) (1 : Matrix (Bool × Fin D) (Bool × Fin D) ℂ)) φ with hΞ
  have hloop := phaseThresholdLoop_action (I := Bool × Fin D) M (M - 1)
    (TensorGate (1 : Matrix Bool Bool ℂ) U) Ξ
  have hloopEq : (fun p : Fin M × (Bool × Fin D) =>
        ApplyGate ((TensorGate (1 : Matrix Bool Bool ℂ) U) ^ min (M - 1) p.1.val)
          (fun i => Ξ (p.1, i)) p.2)
      = ApplyGate (gridHHLPowers (D := D) (M := M) U) Ξ := by
    funext p
    obtain ⟨a, f, i⟩ := p
    have hmin : min (M - 1) a.val = a.val := by have := a.isLt; omega
    show ((TensorGate (1 : Matrix Bool Bool ℂ) U) ^ min (M - 1) a.val *ᵥ
        (fun q : Bool × Fin D => Ξ (a, q))) (f, i) = _
    rw [tensorGate_one_pow, hmin, tensorGate_one_mulVec]
    exact (gridHHLPowers_mulVec U Ξ a f i).symm
  simp only [countedHHLOracleLift] at hloop ⊢
  rw [countedPhaseCircuit, run_append, run_append]
  simp only [Run]
  rw [hstep1, hloop, hloopEq, hstep1']
  simp only [gridHHLQPEBlock, Run]
  rw [gridHHLFourier_eq, gridHHLFourier_eq]

/-- Evaluating the counted phase-estimation word on an embedded state reproduces the embedded
grid HHL phase-estimation block. -/
theorem countedQPEWord_apply (D M : ℕ) (hM : 0 < M) (U : Operator D)
    (φ : QState (Fin M × (Bool × Fin D))) :
    ApplyGate (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M))
        (phaseFlagEmbed (I := Bool × Fin D) M φ)
      = phaseFlagEmbed M (Run 1 (gridHHLQPEBlock (D := D) (M := M) U) φ) := by
  rw [countedQPEWord, ← run_eq_evaluate]
  exact countedPhaseCircuit_run_eq D M hM U φ

/-- Applying `Y` and then `X` to a state equals applying their matrix product `X * Y`. -/
theorem applyGate_comp {I : Type*} [Fintype I] [DecidableEq I] (X Y : Matrix I I ℂ)
    (v : QState I) : ApplyGate X (ApplyGate Y v) = ApplyGate (X * Y) v :=
  Matrix.mulVec_mulVec v X Y

/-- The grid HHL phase-estimation matrix formed by conjugating the controlled-power gate with
the lifted Fourier matrix. -/
noncomputable def gridHHLBlockOp {D M : ℕ} (U : Operator D) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  gridHHLFourier (D := D) (QFTMatrix M)ᴴ * (gridHHLPowers (D := D) (M := M) U *
    gridHHLFourier (D := D) (QFTMatrix M))

/-- For positive phase-register size and unitary `U`, the grid HHL phase-estimation matrix is
unitary. -/
theorem gridHHLBlockOp_unitary {D M : ℕ} (hM : 0 < M) (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    gridHHLBlockOp (D := D) (M := M) U
      ∈ Matrix.unitaryGroup (Fin M × (Bool × Fin D)) ℂ :=
  (Matrix.unitaryGroup _ ℂ).mul_mem
    (gridHHLFourier_unitary _ (mem_unitaryGroup_adjoint (qftMatrix_unitary hM)))
    ((Matrix.unitaryGroup _ ℂ).mul_mem (gridHHLPowers_unitary U hU)
      (gridHHLFourier_unitary _ (qftMatrix_unitary hM)))

/-- Taking the conjugate transpose commutes with the grid HHL Fourier lift. -/
theorem gridHHLFourier_conjTranspose {D M : ℕ} (Q : Matrix (Fin M) (Fin M) ℂ) :
    (gridHHLFourier (D := D) (M := M) Q)ᴴ = gridHHLFourier (D := D) (M := M) Qᴴ := by
  rw [gridHHLFourier_eq, tensorGate_conjTranspose, one_conjTranspose, gridHHLFourier_eq]

/-- Running the grid HHL phase-estimation block equals multiplying the state by `gridHHLBlockOp
U`. -/
theorem run_qpeBlock_eq {D M : ℕ} (U : Operator D) (φ : QState (Fin M × (Bool × Fin D))) :
    Run 1 (gridHHLQPEBlock (D := D) (M := M) U) φ
      = (gridHHLBlockOp (D := D) (M := M) U) *ᵥ φ := by
  simp only [gridHHLQPEBlock, Run]
  rw [applyGate_comp, applyGate_comp, Matrix.mul_assoc]
  rfl

/-- Running the inverse grid HHL phase-estimation block equals multiplying by the conjugate
transpose of `gridHHLBlockOp U`. -/
theorem run_qpeBlockInv_eq {D M : ℕ} (U : Operator D) (χ : QState (Fin M × (Bool × Fin D))) :
    Run 1 (gridHHLQPEBlockInv (D := D) (M := M) U) χ
      = ((gridHHLBlockOp (D := D) (M := M) U)ᴴ) *ᵥ χ := by
  have hstar : (gridHHLBlockOp (D := D) (M := M) U)ᴴ
      = gridHHLFourier (D := D) (QFTMatrix M)ᴴ *
        ((gridHHLPowers (D := D) (M := M) U)ᴴ * gridHHLFourier (D := D) (QFTMatrix M)) := by
    rw [gridHHLBlockOp, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      gridHHLFourier_conjTranspose, gridHHLFourier_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  simp only [gridHHLQPEBlockInv, Run]
  rw [applyGate_comp, applyGate_comp, hstar, Matrix.mul_assoc]
  rfl

/-- For a unitary oracle and positive phase-register size, the adjoint of the counted
phase-estimation matrix reproduces the embedded inverse grid block. -/
theorem countedQPEWord_apply_adjoint (D M : ℕ) (hM : 0 < M) (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (χ : QState (Fin M × (Bool × Fin D))) :
    ApplyGate (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M))ᴴ
        (phaseFlagEmbed (I := Bool × Fin D) M χ)
      = phaseFlagEmbed M (Run 1 (gridHHLQPEBlockInv (D := D) (M := M) U) χ) := by
  have hWF : evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M)
      ∈ Matrix.unitaryGroup (Fin M × (Bool × (Bool × Fin D))) ℂ :=
    WellFormedAdjointCircuit.evaluate_unitary (countedQPEWord_wellFormed D M hM)
      (countedHHLOracleLift_unitary hU)
  have hFstar : (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M))ᴴ
      * (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M)) = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff'.mp hWF)
    rwa [Matrix.star_eq_conjTranspose] at h
  have hkey : ApplyGate (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M))
        (phaseFlagEmbed M ((gridHHLBlockOp (D := D) (M := M) U)ᴴ *ᵥ χ))
      = phaseFlagEmbed M χ := by
    have hBO : (gridHHLBlockOp (D := D) (M := M) U)
        * ((gridHHLBlockOp (D := D) (M := M) U)ᴴ) = 1 := by
      have h := (Matrix.mem_unitaryGroup_iff.mp (gridHHLBlockOp_unitary hM U hU))
      rwa [Matrix.star_eq_conjTranspose] at h
    rw [countedQPEWord_apply D M hM U _, run_qpeBlock_eq, Matrix.mulVec_mulVec, hBO,
      Matrix.one_mulVec]
  calc ApplyGate (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M))ᴴ
          (phaseFlagEmbed M χ)
      = ApplyGate (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M))ᴴ
          (ApplyGate (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M))
            (phaseFlagEmbed M ((gridHHLBlockOp (D := D) (M := M) U)ᴴ *ᵥ χ))) := by rw [hkey]
    _ = ApplyGate ((evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M))ᴴ
          * (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M)))
          (phaseFlagEmbed M ((gridHHLBlockOp (D := D) (M := M) U)ᴴ *ᵥ χ)) :=
        applyGate_comp _ _ _
    _ = phaseFlagEmbed M ((gridHHLBlockOp (D := D) (M := M) U)ᴴ *ᵥ χ) := by
        rw [hFstar, applyGate_one]
  rw [run_qpeBlockInv_eq]

/-- For a unitary oracle and positive phase-register size, the evaluated HHL word on its
embedded basis input equals the embedded preparation, phase-estimation, flag-rotation, and
uncomputation output. -/
theorem countedHHLWord_apply (D M : ℕ) (hM : 0 < M) (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (c : ℝ) (B : Operator D) (j : Fin D) :
    ApplyGate (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedHHLWord M c B))
        (phaseFlagEmbed (I := Bool × Fin D) M
          (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket false) (Ket j))))
      = phaseFlagEmbed M (Run 1 (gridHHLQPEBlock (D := D) (M := M) U
            ++ [Step.gate (gridHHLFlag (D := D) c)]
              ++ gridHHLQPEBlockInv (D := D) (M := M) U)
          (TensorState (Ket (⟨0, hM⟩ : Fin M))
            (TensorState (Ket false) (ApplyGate B (Ket j))))) := by
  have hEval : evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedHHLWord M c B)
      = (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M))ᴴ *
        (countedHHLLiftGate (gridHHLFlag (D := D) c) *
          (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M)
            * countedHHLLiftGate (countedHHLPrepMain (D := D) (M := M) B))) := by
    rw [countedHHLWord, evaluate_append, evaluate_append, evaluate_append,
      evaluate_adjointCircuit]
    simp only [evaluate, instructionMatrix, mul_one]
    noncomm_ring
  rw [hEval, ← applyGate_comp, ← applyGate_comp, ← applyGate_comp]
  rw [countedHHLLiftGate_apply (countedHHLPrepMain (D := D) (M := M) B),
    countedHHLPrepMain_apply hM B j]
  rw [countedQPEWord_apply D M hM U _]
  rw [countedHHLLiftGate_apply (gridHHLFlag (D := D) c)]
  rw [countedQPEWord_apply_adjoint D M hM U hU _]
  rw [run_append, run_append, run_gate, run_nil]

/-- The explicit counted HHL basis input equals the phase-flag embedding of the original phase,
flag, and data input. -/
theorem countedHHLBranchInput_eq (D M : ℕ) (hM : 0 < M) (j : Fin D) :
    TensorState (Ket (⟨0, hM⟩ : Fin M))
        (TensorState (Ket false) (TensorState (Ket false) (Ket j)))
      = phaseFlagEmbed (I := Bool × Fin D) M
          (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket false) (Ket j))) := by
  funext p
  obtain ⟨a, s, f, i⟩ := p
  cases s <;> simp [phaseFlagEmbed, TensorState, Ket]

/-- For `2 ≤ M`, unitary eigenbasis and preparation matrices, and `0 ≤ c ≤ 1 / M`, the
exact-grid clean HHL branch equals `c` times the matrix pseudoinverse applied to the
prepared input. This realizes the inverse-eigenvalue construction of [Harrow, Hassidim, and
Lloyd, 2009][HarrowHassidimLloyd2009]. -/
theorem counted_hhl_exact_grid_clean_branch :
    ∀ (D M : ℕ) (label : Fin D → Fin M) (V B : Operator D) (j : Fin D) (c : ℝ),
      2 ≤ M → V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
      0 ≤ c → c ≤ 1 / (M : ℝ) →
      countedHHLCleanBranch (gridHHLOracle label V) M c B j
        = (c : ℂ) • (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ (ApplyGate B (Ket j))) := by
  intro D M label V B j c hM hV hB hc0 hc1
  have hMpos : 0 < M := by omega
  have hU : gridHHLOracle label V ∈ Matrix.unitaryGroup (Fin D) ℂ :=
    (grid_hhl_spectral_matrix_and_oracle_unitary D M label V hMpos hV).2.2
  have hword := countedHHLWord_apply D M hMpos (gridHHLOracle label V) hU c B j
  obtain ⟨hpt, -⟩ := grid_hhl_uncompute_and_postselected_pseudoinverse hMpos label V c
    (ApplyGate B (Ket j)) hV hc0 hc1
  have hcirc : gridHHLCircuit (D := D) label V c
      = gridHHLQPEBlock (M := M) (gridHHLOracle label V)
          ++ [Step.gate (gridHHLFlag (D := D) c)]
          ++ gridHHLQPEBlockInv (M := M) (gridHHLOracle label V) := rfl
  rw [hcirc] at hpt
  funext i
  have hin := countedHHLBranchInput_eq D M hMpos j
  have hval := hpt (⟨0, hMpos⟩ : Fin M) i
  simp only [countedHHLCleanBranch, dif_pos hMpos]
  show (ApplyGate (evaluate (countedHHLOracleLift (D := D) (M := M) (gridHHLOracle label V))
        (countedHHLWord M c B))
      (TensorState (Ket (⟨0, hMpos⟩ : Fin M))
        (TensorState (Ket false) (TensorState (Ket false) (Ket j)))))
      ((⟨0, hMpos⟩ : Fin M), (false, (true, i)))
    = ((c : ℂ) • (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ (ApplyGate B (Ket j)))) i
  rw [hin, hword]
  simp only [phaseFlagEmbed]
  rw [hval]
  simp

/-- A controlled oracle applies `Z` in the true control sector and leaves the false sector
unchanged. -/
theorem controlOracle_mulVec {I : Type*} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ)
    (ψ : QState (Bool × I)) (b : Bool) (i : I) :
    (controlOracle Z *ᵥ ψ) (b, i)
      = if b then (Z *ᵥ (fun i' => ψ (b, i'))) i else ψ (false, i) := by
  show ∑ q : Bool × I, controlOracle Z (b, i) q * ψ q = _
  simp only [controlOracle, Qatlib.Concepts.BlockEncoding.LCU.select, Matrix.of_apply,
      Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · cases b <;> simp [Matrix.one_apply, Matrix.mulVec, dotProduct]
  · intro b' _ hb'
    simp [show b ≠ b' from fun e => hb' e.symm]
  · intro h
    exact absurd (Finset.mem_univ b) h

/-- The difference of two controlled oracles applies their data-operator difference in the true
sector and vanishes in the false sector. -/
theorem controlOracle_sub_mulVec {I : Type*} [Fintype I] [DecidableEq I] (W W' : Matrix I I ℂ)
    (ψ : QState (Bool × I)) (b : Bool) (i : I) :
    ((controlOracle W - controlOracle W') *ᵥ ψ) (b, i)
      = if b then ((W - W') *ᵥ (fun i' => ψ (true, i'))) i else 0 := by
  rw [Matrix.sub_mulVec]
  simp only [Pi.sub_apply]
  rw [controlOracle_mulVec, controlOracle_mulVec]
  cases b <;> simp [Matrix.sub_mulVec]

/-- Squaring preserves an inequality between nonnegative real numbers. -/
private theorem sq_le_sq_of_nonneg' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ b) :
    a ^ 2 ≤ b ^ 2 := by
  rw [sq_le_sq, abs_of_nonneg ha, abs_of_nonneg hb]
  exact h

/-- Adding a Boolean control does not increase the operator norm of the difference between two
operators. -/
theorem norm_controlOracle_sub {I : Type*} [Fintype I] [DecidableEq I] (W W' : Matrix I I ℂ) :
    ‖controlOracle W - controlOracle W'‖ ≤ ‖W - W'‖ := by
  refine l2_opNorm_le_of_mulVec_le (norm_nonneg _) _ fun ψ => ?_
  have hpart : ∑ i, ‖ψ (true, i)‖ ^ 2 ≤ ∑ p : Bool × I, ‖ψ p‖ ^ 2 := by
    have h0 : (0 : ℝ) ≤ ∑ i, ‖ψ (false, i)‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    linarith
  have htrue : ∑ i : I, ‖((W - W') *ᵥ (fun i' => ψ (true, i'))) i‖ ^ 2
      ≤ (‖W - W'‖ * ‖toEuclidean_fromVec ψ‖) ^ 2 := by
    have hle := l2_norm_mulVec_fromVec_le (W - W') (fun i' => ψ (true, i'))
    have h1 : ‖toEuclidean_fromVec (fun i' => ψ (true, i'))‖ ≤ ‖toEuclidean_fromVec ψ‖ := by
      have hsq1 : ‖toEuclidean_fromVec (fun i' => ψ (true, i'))‖ ^ 2
          ≤ ‖toEuclidean_fromVec ψ‖ ^ 2 := by
        rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq]
        exact hpart
      have hnn := norm_nonneg (toEuclidean_fromVec ψ)
      have hnm := norm_nonneg (toEuclidean_fromVec (fun i' => ψ (true, i')))
      nlinarith [hsq1, hnn, hnm]
    have hnn1 : 0 ≤ ‖W - W'‖ * ‖toEuclidean_fromVec (fun i' => ψ (true, i'))‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hnn2 : 0 ≤ ‖W - W'‖ * ‖toEuclidean_fromVec ψ‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc ∑ i : I, ‖((W - W') *ᵥ (fun i' => ψ (true, i'))) i‖ ^ 2
        = ‖toEuclidean_fromVec ((W - W') *ᵥ (fun i' => ψ (true, i')))‖ ^ 2 :=
          (norm_toEuclidean_fromVec_sq _).symm
      _ ≤ (‖W - W'‖ * ‖toEuclidean_fromVec (fun i' => ψ (true, i'))‖) ^ 2 :=
          sq_le_sq_of_nonneg' (norm_nonneg _) hnn1 hle
      _ ≤ (‖W - W'‖ * ‖toEuclidean_fromVec ψ‖) ^ 2 :=
          sq_le_sq_of_nonneg' hnn1 hnn2
          (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
  have hsq : ‖toEuclidean_fromVec ((controlOracle W - controlOracle W') *ᵥ ψ)‖ ^ 2
      ≤ (‖W - W'‖ * ‖toEuclidean_fromVec ψ‖) ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type]
    have hfalse : ∑ i : I, ‖((controlOracle W - controlOracle W') *ᵥ ψ) (false, i)‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [controlOracle_sub_mulVec]
      simp
    have hconv : ∑ i : I, ‖((controlOracle W - controlOracle W') *ᵥ ψ) (true, i)‖ ^ 2
        = ∑ i : I, ‖((W - W') *ᵥ (fun i' => ψ (true, i'))) i‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [controlOracle_sub_mulVec]
      simp
    rw [Fintype.sum_bool, hfalse, add_zero, hconv]
    exact htrue
  calc ‖toEuclidean_fromVec ((controlOracle W - controlOracle W') *ᵥ ψ)‖
      = Real.sqrt (‖toEuclidean_fromVec ((controlOracle W - controlOracle W') *ᵥ ψ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((‖W - W'‖ * ‖toEuclidean_fromVec ψ‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖W - W'‖ * ‖toEuclidean_fromVec ψ‖ :=
        Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- For positive `M`, lifting two data operators to the counted HHL oracle registers does not
increase their operator-norm distance. -/
theorem norm_oracleLift_sub (D M : ℕ) (hM : 0 < M) (U V : Operator D) :
    ‖countedHHLOracleLift (D := D) (M := M) U - countedHHLOracleLift (D := D) (M := M) V‖
      ≤ ‖U - V‖ := by
  have h1 : countedHHLOracleLift (D := D) (M := M) U - countedHHLOracleLift (D := D) (M := M) V
      = TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
          (controlOracle (TensorGate (1 : Matrix Bool Bool ℂ) U)
            - controlOracle (TensorGate (1 : Matrix Bool Bool ℂ) V)) := by
    rw [countedHHLOracleLift, countedHHLOracleLift, ← tensorGate_sub_right]
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hinner : ‖controlOracle (TensorGate (1 : Matrix Bool Bool ℂ) U)
      - controlOracle (TensorGate (1 : Matrix Bool Bool ℂ) V)‖ ≤ ‖U - V‖ := by
    calc ‖controlOracle (TensorGate (1 : Matrix Bool Bool ℂ) U)
          - controlOracle (TensorGate (1 : Matrix Bool Bool ℂ) V)‖
        ≤ ‖TensorGate (1 : Matrix Bool Bool ℂ) U - TensorGate (1 : Matrix Bool Bool ℂ) V‖ :=
          norm_controlOracle_sub _ _
      _ = ‖TensorGate (1 : Matrix Bool Bool ℂ) (U - V)‖ := by rw [tensorGate_sub_right]
      _ = (1 : ℝ) * ‖U - V‖ := by rw [l2_norm_tensorGate, l2_norm_one_eq]
      _ = ‖U - V‖ := one_mul _
  rw [h1, l2_norm_tensorGate, l2_norm_one_eq, one_mul]
  exact hinner

/-- Every computational basis ket has Euclidean norm one. -/
theorem norm_toEuclidean_fromVec_ket {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    ‖toEuclidean_fromVec (Ket i)‖ = 1 := by
  have hsq : ‖toEuclidean_fromVec (Ket i)‖ ^ 2 = 1 := by
    rw [norm_toEuclidean_fromVec_sq, Finset.sum_eq_single i]
    · simp [Ket]
    · intro j _ hj
      simp [Ket, hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hnn : 0 ≤ ‖toEuclidean_fromVec (Ket i)‖ := norm_nonneg _
  nlinarith [hnn]

/-- The tensor-product basis input of the counted HHL program has Euclidean norm one. -/
theorem norm_countedHHLBranchInput (D M : ℕ) (hM : 0 < M) (j : Fin D) :
    ‖toEuclidean_fromVec (TensorState (Ket (⟨0, hM⟩ : Fin M))
        (TensorState (Ket false) (TensorState (Ket false) (Ket j))))‖ = 1 := by
  rw [tensorState_l2_norm, tensorState_l2_norm, tensorState_l2_norm,
    norm_toEuclidean_fromVec_ket, norm_toEuclidean_fromVec_ket,
    norm_toEuclidean_fromVec_ket]
  norm_num

/-- Appending unitary operators at distance at most `ε` increases a state-error budget of `n *
ε` times the input norm to at most `(n + 1) * ε` times that norm. -/
theorem norm_query_step_le {I : Type*} [Fintype I] [DecidableEq I]
    {X Y EO EP : Matrix I I ℂ}
    (hX : X ∈ Matrix.unitaryGroup I ℂ) (hY : Y ∈ Matrix.unitaryGroup I ℂ)
    (hEO : EO ∈ Matrix.unitaryGroup I ℂ) (hEP : EP ∈ Matrix.unitaryGroup I ℂ)
    (ψ : QState I) {n ε : ℝ} (hε : 0 ≤ ε) (hXY : ‖X - Y‖ ≤ ε)
    (h : ‖toEuclidean_fromVec (EO *ᵥ ψ - EP *ᵥ ψ)‖ ≤ n * ε * ‖toEuclidean_fromVec ψ‖) :
    ‖toEuclidean_fromVec (X *ᵥ (EO *ᵥ ψ) - Y *ᵥ (EP *ᵥ ψ))‖
      ≤ (n + 1) * ε * ‖toEuclidean_fromVec ψ‖ := by
  have hnormX : ∀ v : QState I, ‖toEuclidean_fromVec (X *ᵥ v)‖ = ‖toEuclidean_fromVec v‖ :=
    fun v => norm_applyGate_of_mem_unitaryGroup hX v
  have hsplit : X *ᵥ (EO *ᵥ ψ) - Y *ᵥ (EP *ᵥ ψ)
      = X *ᵥ (EO *ᵥ ψ - EP *ᵥ ψ) + (X - Y) *ᵥ (EP *ᵥ ψ) := by
    rw [Matrix.mulVec_sub, Matrix.sub_mulVec]
    abel
  have hsum := norm_add_le (toEuclidean_fromVec (X *ᵥ (EO *ᵥ ψ - EP *ᵥ ψ)))
    (toEuclidean_fromVec ((X - Y) *ᵥ (EP *ᵥ ψ)))
  rw [hsplit]
  calc ‖toEuclidean_fromVec (X *ᵥ (EO *ᵥ ψ - EP *ᵥ ψ) + (X - Y) *ᵥ (EP *ᵥ ψ))‖
      = ‖toEuclidean_fromVec (X *ᵥ (EO *ᵥ ψ - EP *ᵥ ψ))
          + toEuclidean_fromVec ((X - Y) *ᵥ (EP *ᵥ ψ))‖ := rfl
    _ ≤ ‖toEuclidean_fromVec (X *ᵥ (EO *ᵥ ψ - EP *ᵥ ψ))‖
          + ‖toEuclidean_fromVec ((X - Y) *ᵥ (EP *ᵥ ψ))‖ := hsum
    _ ≤ ‖toEuclidean_fromVec (EO *ᵥ ψ - EP *ᵥ ψ)‖
          + ‖toEuclidean_fromVec ((X - Y) *ᵥ (EP *ᵥ ψ))‖ := by
          rw [hnormX]
    _ ≤ n * ε * ‖toEuclidean_fromVec ψ‖ + ‖X - Y‖ * ‖toEuclidean_fromVec (EP *ᵥ ψ)‖ :=
          add_le_add h (norm_applyGate_le _ _)
    _ = n * ε * ‖toEuclidean_fromVec ψ‖ + ‖X - Y‖ * ‖toEuclidean_fromVec ψ‖ := by
          rw [show ‖toEuclidean_fromVec (EP *ᵥ ψ)‖ = ‖toEuclidean_fromVec ψ‖ from
            norm_applyGate_of_mem_unitaryGroup hEP ψ]
    _ ≤ n * ε * ‖toEuclidean_fromVec ψ‖ + ε * ‖toEuclidean_fromVec ψ‖ :=
          add_le_add_right (mul_le_mul_of_nonneg_right hXY
            (norm_nonneg (toEuclidean_fromVec ψ))) (n * ε * ‖toEuclidean_fromVec ψ‖)
    _ = (n + 1) * ε * ‖toEuclidean_fromVec ψ‖ := by ring

/-- For unitary oracles and a well-formed adjoint word, the output distance is bounded by the
query count times the oracle distance times the input norm. -/
theorem norm_evaluate_sub_evaluate_le {I : Type*} [Fintype I] [DecidableEq I]
    (O P : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (hP : P ∈ Matrix.unitaryGroup I ℂ) (cs : List (AdjointStep I))
    (hcs : WellFormedAdjointCircuit cs) : ∀ (ψ : QState I),
    ‖toEuclidean_fromVec (evaluate O cs *ᵥ ψ - evaluate P cs *ᵥ ψ)‖
      ≤ (adjointQueryCount cs : ℝ) * ‖O - P‖ * ‖toEuclidean_fromVec ψ‖ := by
  induction cs with
  | nil =>
    intro ψ
    have h0 : toEuclidean_fromVec (0 : QState I) = 0 := rfl
    simp [evaluate, h0]
  | cons s cs ih =>
    have hcs' : WellFormedAdjointCircuit cs := by
      intro V hV
      exact hcs V (List.mem_cons_of_mem _ hV)
    have hih := ih hcs'
    intro ψ
    cases s with
    | gate W =>
      have hW : W ∈ Matrix.unitaryGroup I ℂ := hcs W (by simp)
      have hnormW : ∀ v : QState I,
          ‖toEuclidean_fromVec (W *ᵥ v)‖ = ‖toEuclidean_fromVec v‖ :=
        fun v => norm_applyGate_of_mem_unitaryGroup hW v
      simp only [evaluate, instructionMatrix]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, hnormW]
      exact hih ψ
    | forward =>
      simp only [adjointQueryCount, Nat.cast_add, Nat.cast_one]
      rw [evaluate, evaluate, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact norm_query_step_le hO hP (hcs'.evaluate_unitary hO) (hcs'.evaluate_unitary hP) ψ
        (norm_nonneg _) le_rfl (hih ψ)
    | backward =>
      simp only [adjointQueryCount, Nat.cast_add, Nat.cast_one]
      have hXY : ‖Oᴴ - Pᴴ‖ ≤ ‖O - P‖ := by
        rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
      rw [evaluate, evaluate, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact norm_query_step_le (mem_unitaryGroup_adjoint hO) (mem_unitaryGroup_adjoint hP)
        (hcs'.evaluate_unitary hO) (hcs'.evaluate_unitary hP) ψ (norm_nonneg _) hXY (hih ψ)

/-- For `2 ≤ M`, unitary `B`, and `0 ≤ c ≤ 1 / M`, the counted HHL word is a well-formed adjoint
circuit. -/
theorem countedHHLWord_wellFormed {D : ℕ} (M : ℕ) (c : ℝ) (B : Operator D)
    (hM : 2 ≤ M) (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1 / (M : ℝ)) :
    WellFormedAdjointCircuit (countedHHLWord (D := D) M c B) :=
  (counted_hhl_actual_word_and_access_counts D M c B hM hB hc0 hc1).1

/-- Extracting the branch with phase zero, sector false, and flag true does not increase the
Euclidean norm. -/
theorem branchExtract_norm_le {D M : ℕ} (hM : 0 < M)
    (w : QState (Fin M × (Bool × (Bool × Fin D)))) :
    ‖stateVector (fun i => w ((⟨0, hM⟩ : Fin M), (false, (true, i))))‖
      ≤ ‖toEuclidean_fromVec w‖ := by
  have hinj : Function.Injective
      (fun i : Fin D => ((⟨0, hM⟩ : Fin M), (false, (true, i)))) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact h.2.2.2
  have hsq : ‖stateVector (fun i => w ((⟨0, hM⟩ : Fin M), (false, (true, i))))‖ ^ 2
      ≤ ‖toEuclidean_fromVec w‖ ^ 2 := by
    rw [stateVector_norm_sq, norm_toEuclidean_fromVec_sq]
    calc (∑ i : Fin D, ‖w ((⟨0, hM⟩ : Fin M), (false, (true, i)))‖ ^ 2)
        = ∑ q ∈ Finset.univ.image
            (fun i : Fin D => ((⟨0, hM⟩ : Fin M), (false, (true, i)))), ‖w q‖ ^ 2 :=
          (Finset.sum_image (f := fun q => ‖w q‖ ^ 2) hinj.injOn).symm
      _ ≤ ∑ q : Fin M × (Bool × (Bool × Fin D)), ‖w q‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun q _ _ => sq_nonneg (‖w q‖))
  calc ‖stateVector (fun i => w ((⟨0, hM⟩ : Fin M), (false, (true, i))))‖
      = Real.sqrt (‖stateVector (fun i => w ((⟨0, hM⟩ : Fin M), (false, (true, i))))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖toEuclidean_fromVec w‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖toEuclidean_fromVec w‖ := Real.sqrt_sq (norm_nonneg _)

/-- For `2 ≤ M`, unitary oracles and preparation, and `0 ≤ c ≤ 1 / M`, oracle distance at most
`δ` gives clean-branch distance at most `2 * (M - 1) * δ`. -/
theorem counted_hhl_unitary_oracle_clean_branch_noise :
    ∀ (D M : ℕ) (U V B : Operator D) (j : Fin D) (c δ : ℝ),
      2 ≤ M → U ∈ Matrix.unitaryGroup (Fin D) ℂ → V ∈ Matrix.unitaryGroup (Fin D) ℂ →
      B ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 ≤ c → c ≤ 1 / (M : ℝ) → ‖U - V‖ ≤ δ →
      ‖stateVector (countedHHLCleanBranch U M c B j - countedHHLCleanBranch V M c B j)‖
        ≤ 2 * (M - 1 : ℕ) * δ := by
  intro D M U V B j c δ hM hU hV hB hc0 hc1 hδ
  have hMpos : 0 < M := by omega
  set ψ₀ : QState (Fin M × (Bool × (Bool × Fin D))) :=
    TensorState (Ket (⟨0, hMpos⟩ : Fin M))
      (TensorState (Ket false) (TensorState (Ket false) (Ket j))) with hψ₀def
  set runU : QState (Fin M × (Bool × (Bool × Fin D))) :=
    ApplyGate (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedHHLWord M c B)) ψ₀
    with hrunUdef
  set runV : QState (Fin M × (Bool × (Bool × Fin D))) :=
    ApplyGate (evaluate (countedHHLOracleLift (D := D) (M := M) V) (countedHHLWord M c B)) ψ₀
    with hrunVdef
  have hbrU : countedHHLCleanBranch U M c B j
      = (fun i => runU ((⟨0, hMpos⟩ : Fin M), (false, (true, i)))) := by
    funext i
    simp only [countedHHLCleanBranch, dif_pos hMpos, hrunUdef, hψ₀def]
  have hbrV : countedHHLCleanBranch V M c B j
      = (fun i => runV ((⟨0, hMpos⟩ : Fin M), (false, (true, i)))) := by
    funext i
    simp only [countedHHLCleanBranch, dif_pos hMpos, hrunVdef, hψ₀def]
  have hsub : (fun i : Fin D => runU ((⟨0, hMpos⟩ : Fin M), (false, (true, i))))
      - (fun i : Fin D => runV ((⟨0, hMpos⟩ : Fin M), (false, (true, i))))
      = (fun i : Fin D => (runU - runV) ((⟨0, hMpos⟩ : Fin M), (false, (true, i)))) := by
    funext i
    simp [Pi.sub_apply]
  have hhy := norm_evaluate_sub_evaluate_le
    (countedHHLOracleLift (D := D) (M := M) U) (countedHHLOracleLift (D := D) (M := M) V)
    (countedHHLOracleLift_unitary hU) (countedHHLOracleLift_unitary hV)
    (countedHHLWord M c B) (countedHHLWord_wellFormed M c B hM hB hc0 hc1) ψ₀
  have hcount := countedHHLWord_queryCount M c B hMpos
  have hdist := norm_oracleLift_sub D M hMpos U V
  have hnorm := norm_countedHHLBranchInput D M hMpos j
  rw [hbrU, hbrV, hsub]
  have hnorm' : ‖toEuclidean_fromVec ψ₀‖ = 1 := hnorm
  rw [hψ₀def] at hnorm'
  calc ‖stateVector (fun i : Fin D => (runU - runV)
          ((⟨0, hMpos⟩ : Fin M), (false, (true, i))))‖
      ≤ ‖toEuclidean_fromVec (runU - runV)‖ :=
          branchExtract_norm_le hMpos _
    _ = ‖toEuclidean_fromVec
          (ApplyGate (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedHHLWord M c B)) ψ₀
            - ApplyGate (evaluate (countedHHLOracleLift (D := D) (M := M) V)
              (countedHHLWord M c B)) ψ₀)‖ := rfl
    _ ≤ (adjointQueryCount (countedHHLWord M c B) : ℝ)
          * ‖countedHHLOracleLift (D := D) (M := M) U
              - countedHHLOracleLift (D := D) (M := M) V‖ * ‖toEuclidean_fromVec ψ₀‖ := hhy
    _ = (2 * (M - 1 : ℕ) : ℝ) * ‖countedHHLOracleLift (D := D) (M := M) U
          - countedHHLOracleLift (D := D) (M := M) V‖ := by
          rw [hcount, hnorm', mul_one, Nat.cast_mul, Nat.cast_two]
    _ ≤ (2 * (M - 1 : ℕ) : ℝ) * ‖U - V‖ :=
          mul_le_mul_of_nonneg_left hdist (by positivity)
    _ ≤ (2 * (M - 1 : ℕ) : ℝ) * δ :=
          mul_le_mul_of_nonneg_left hδ (by positivity)
    _ = 2 * (M - 1 : ℕ) * δ := by ring

end Qatlib.Concepts.NativeNumerics.LayeredMean
