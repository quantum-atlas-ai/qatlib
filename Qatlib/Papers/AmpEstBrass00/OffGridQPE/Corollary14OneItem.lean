/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AmpEstBrass00.OffGridQPE
public import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Corollary14Defs
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The one-item endpoint of rounded counting

For `N = 1`, the square-root grid of [BrassardEtAl2002], Corollary 14 is a
singleton. The rounded estimate is zero for either marked set. The padded
counting circuit appends one controlled marking query on the false flag. That
query preserves the output state. The only counter label occurs with certainty,
in agreement with the one-point phase kernel.

## Main statements

* `corollary14_one_item_endpoint`: the rounded error bound, exact phase-kernel
  and circuit success probabilities, and the padded circuit's query count.

## References

* [Brassard et al., Corollary 14][BrassardEtAl2002]
-/

set_option autoImplicit false

open Matrix
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.AmpEstBrass00.OffGridQPE

/-- The one-item state prepared by the counting circuit, with the Euclidean norm. -/
noncomputable def oneItemEuclideanState : EuclideanSpace ℂ (Fin 1) :=
  WithLp.toLp 2 (preparedAAState (QFTMatrix 1) (0 : Fin 1))

/-- The normalized eigenphase is zero for the empty marked set and one half when the
unique item is marked. -/
noncomputable def oneItemCountPhase (S : Finset (Fin 1)) : ℝ :=
  if S.card = 0 then 0 else 1 / 2

/-- The prepared counting state has the phase used by the one-point kernel. -/
private theorem one_item_count_eigenphase (S : Finset (Fin 1)) :
    let A := QFTMatrix 1
    let j : Fin 1 := 0
    ApplyGate (preparedAAIterate A j S) (preparedAAState A j) =
      Complex.exp (2 * Real.pi * Complex.I * (oneItemCountPhase S : ℂ)) •
        preparedAAState A j := by
  dsimp only
  have hU := qftMatrix_unitary (M := 1) (by norm_num)
  have hrun := (prepared_aa_actual_circuit (QFTMatrix 1) (0 : Fin 1) S 1 hU).2.2.2
  rw [pow_one] at hrun
  have he := prepared_aa_endpoint_states (QFTMatrix 1) (0 : Fin 1) S 1 hU
  by_cases h : S.card = 0
  · have hmass : MeasureProb (preparedAAState (QFTMatrix 1) (0 : Fin 1)) S = 0 := by
      simp [MeasureProb, Finset.card_eq_zero.mp h]
    simpa [oneItemCountPhase, h] using hrun.symm.trans (he.1 hmass)
  · have hfull : S = Finset.univ := by
      ext i
      have hne : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
      obtain ⟨j, hj⟩ := hne
      rw [Subsingleton.elim i j]
      exact iff_of_true hj (Finset.mem_univ j)
    have hmass : MeasureProb (preparedAAState (QFTMatrix 1) (0 : Fin 1)) S = 1 := by
      rw [hfull]
      exact measureProb_univ (prepared_aa_reflection_and_access _ _ S hU).2.1
    have hphase : (2 * Real.pi * Complex.I * (oneItemCountPhase S : ℂ) : ℂ) =
        (Real.pi : ℂ) * Complex.I := by
      rw [oneItemCountPhase, ite_eq_right h]
      norm_num; ring
    rw [hphase, Complex.exp_pi_mul_I, neg_one_smul]
    simpa only [pow_one, neg_one_smul] using hrun.symm.trans (he.2 hmass)

/-- The square-root counting grid for the one-item endpoint has exactly one point. -/
theorem approxCountCor14Grid_one : approxCountCor14Grid 1 = 1 := by
  unfold approxCountCor14Grid
  norm_num

/-- The rounded counting output transported to the canonical one-point counter type. -/
noncomputable def oneItemCor14Output (z : Fin 1) : ℤ :=
  approxCountCor14Output 1 (Fin.cast approxCountCor14Grid_one.symm z)

/-- The one-item counting preparation has Euclidean norm one, and its Fourier
operator has spectral norm one. -/
theorem oneItemEuclideanState_and_QFT_L2 :
    ‖oneItemEuclideanState‖ = 1 ∧ ‖QFTMatrix 1‖ = 1 := by
  have hU := qftMatrix_unitary (M := 1) (by norm_num)
  have hnorm :=
    (prepared_aa_reflection_and_access (QFTMatrix 1) (0 : Fin 1) ∅ hU).2.1
  have hsq : ‖oneItemEuclideanState‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact hnorm
  exact ⟨(Real.sqrt_sq (norm_nonneg _)).symm.trans (by rw [hsq, Real.sqrt_one]),
    CStarRing.norm_of_mem_unitary hU⟩

/-- The one-item counting circuit with an extra controlled marking query. -/
noncomputable def oneItemCountCircuit : Circuit (Fin 1 × (Bool × Fin 1)) :=
  countedAECircuit 1 (QFTMatrix 1) (0 : Fin 1) ++ [Step.query]

/-- The circuit output is the one-point phase kernel tensored with the prepared
state. The padding query preserves this state because the flag has returned to false. -/
theorem one_item_padded_run_eq_qpe (S : Finset (Fin 1)) :
    let oracle := aeControlledGate 1 (preparedMark S)
    let input := TensorState (Ket (⟨0, by decide⟩ : Fin 1))
      (TensorState (Ket false) (Ket (0 : Fin 1)))
    Run oracle oneItemCountCircuit input =
      phaseFlagEmbed 1 (TensorState (qpeKernel 1 (oneItemCountPhase S))
        (preparedAAState (QFTMatrix 1) (0 : Fin 1))) := by
  dsimp only
  rw [oneItemCountCircuit, run_append, countedAE_output 1 (by decide) (QFTMatrix 1) (0 : Fin 1) S,
    qpeOutput_eigen 1 _ _ (oneItemCountPhase S) (one_item_count_eigenphase S)]
  change ApplyGate (aeControlledGate 1 (preparedMark S)) (phaseFlagEmbed 1 _) =
    phaseFlagEmbed 1 _
  funext p
  rcases p with ⟨z, b, x⟩
  rw [aeControlledGate, phaseControlledOracle_apply]
  cases b
  · simp [phaseFlagEmbed, applyGate_one]
  · simp [phaseFlagEmbed, ApplyGate, Matrix.mulVec, dotProduct]

/-- Probability of a counter event on the actual padded one-item counting output. -/
noncomputable def oneItemCountEventMass (S : Finset (Fin 1)) (P : Fin 1 → Prop) : ℝ := by
  classical
  exact MeasureProb (Run (aeControlledGate 1 (preparedMark S)) oneItemCountCircuit
    (TensorState (Ket (0 : Fin 1)) (TensorState (Ket false) (Ket (0 : Fin 1)))))
    (Finset.univ.filter fun p => P p.1)

/-- The sole counter label decodes to zero under the rounded counting rule. -/
private theorem one_item_output_zero (z : Fin 1) : oneItemCor14Output z = 0 := by
  have hz : z.val = 0 := by
    have := z.isLt
    omega
  unfold oneItemCor14Output approxCountCor14Output aeEstimate
  simp only [Fin.cast, hz, approxCountCor14Grid_one, Nat.cast_zero, Nat.cast_one]
  norm_num

/-- At grid size one, the padded circuit consists of the preparation, two Fourier
gates and a single controlled marking query. -/
private theorem one_item_circuit_unitary_and_query :
    IsUnitaryCircuit oneItemCountCircuit ∧ QueryCount oneItemCountCircuit = 1 := by
  unfold oneItemCountCircuit countedAECircuit
  rw [aeAccessWord_split]
  simp only [aeFlagAccessWord, Nat.sub_self, phaseThresholdLoop, List.flatMap_nil,
    List.nil_append, List.cons_append, List.map_cons, List.map_nil, aeAccessInstruction,
    isUnitaryCircuit_gate, isUnitaryCircuit_query, isUnitaryCircuit_nil, and_true]
  have hU := qftMatrix_unitary (M := 1) (by norm_num)
  exact ⟨⟨tensorGate_unitary (by simp) (tensorGate_unitary (by simp) hU),
    tensorGate_unitary hU (by simp),
    tensorGate_unitary (conjTranspose_mem_unitaryGroup hU) (by simp)⟩, rfl⟩

/-- At `N = 1`, the error window of Corollary 14 is eleven. It contains the rounded
output for every marked set, so its probability is one under both the padded
circuit and the phase-kernel model. The padded circuit uses exactly one controlled
marking query. -/
theorem corollary14_one_item_endpoint :
    let C : ℝ := 11
    ∀ (S : Finset (Fin 1)) (z : Fin 1),
      let good := fun w => |(oneItemCor14Output w : ℝ) - (S.card : ℝ)| < C
      let mass := oneItemCountEventMass S good
      approxCountCor14Grid 1 = 1 ∧
      oneItemCor14Output z = 0 ∧ good z ∧
      mass = 1 ∧ 8 / Real.pi ^ 2 ≤ mass ∧
      (∑ w ∈ Finset.univ.filter good, ‖qpeKernel 1 (oneItemCountPhase S) w‖ ^ 2) = mass ∧
      QueryCount oneItemCountCircuit = 1 := by
  classical
  intro C S z
  dsimp only [C]
  have hcard : (S.card : ℝ) ≤ 1 := by
    exact_mod_cast (S.card_le_univ.trans_eq (Fintype.card_fin 1))
  have herr (w : Fin 1) : |(oneItemCor14Output w : ℝ) - (S.card : ℝ)| < 11 := by
    rw [one_item_output_zero, Int.cast_zero, abs_sub_comm, sub_zero,
      abs_of_nonneg (Nat.cast_nonneg _)]
    linarith
  obtain ⟨hcircuit, hquery⟩ := one_item_circuit_unitary_and_query
  have hmark := (prepared_aa_reflection_and_access (QFTMatrix 1) (0 : Fin 1) S
    (qftMatrix_unitary (by norm_num))).1
  have horacle : aeControlledGate 1 (preparedMark S) ∈
      Matrix.unitaryGroup (Fin 1 × (Bool × Fin 1)) ℂ :=
    tensorGate_unitary (by simp) (controlOracle_unitary hmark)
  have hnormalized := hcircuit.normalized_run horacle
    (normalized_tensorState (normalized_ket (0 : Fin 1))
      (normalized_tensorState (normalized_ket false) (normalized_ket (0 : Fin 1))))
  have hmass : oneItemCountEventMass S
      (fun w => |(oneItemCor14Output w : ℝ) - (S.card : ℝ)| < 11) = 1 := by
    unfold oneItemCountEventMass
    rw [Finset.filter_eq_self.mpr (fun p _ => herr p.1)]
    exact measureProb_univ hnormalized
  refine ⟨approxCountCor14Grid_one, one_item_output_zero z, herr z, hmass, ?_, ?_, hquery⟩
  · rw [hmass]
    have hpi : (8 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    exact (div_le_iff₀ (by positivity)).mpr (by simpa using hpi)
  · rw [hmass, Finset.filter_eq_self.mpr (fun w _ => herr w)]
    exact Qatlib.Papers.AmpEstBrass00.OffGridQPE.offgrid_phase_total_mass
        1 (oneItemCountPhase S) (by norm_num)

end Qatlib.Papers.AmpEstBrass00.OffGridQPE
