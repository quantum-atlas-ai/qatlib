/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniformThree.HiddenSubgroupOracle
import Qatlib.Concepts.LchsSimulation.StaticLchs.ReadoutError
set_option warningAsError false


open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Concepts.HspRecovery.Distinguisher

open Matrix
open scoped Classical

variable {G R : Type*}
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup R] [Fintype R] [DecidableEq R]

noncomputable def hiddenSubgroupSamplingCircuit (e : G ≃ AddChar G ℂ) : Circuit (G × R) :=
  [Step.query, Step.gate (TensorGate (fourierGate e) 1)]

theorem hiddenSubgroupSamplingCircuit_resources (e : G ≃ AddChar G ℂ) :
    QueryCount (hiddenSubgroupSamplingCircuit (R := R) e) = 1 ∧
      GateCount (hiddenSubgroupSamplingCircuit (R := R) e) = 1 ∧
        Size (hiddenSubgroupSamplingCircuit (R := R) e) = 2 := by
  exact ⟨rfl, rfl, rfl⟩

theorem hiddenSubgroupSamplingCircuit_unitary (e : G ≃ AddChar G ℂ) :
    IsUnitaryCircuit (hiddenSubgroupSamplingCircuit (R := R) e) := by
  simp only [hiddenSubgroupSamplingCircuit, isUnitaryCircuit_query,
    isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
  exact tensorGate_unitary (fourierGate_unitary e) (Submonoid.one_mem _)

private theorem applyGate_tensorGate_one_slice
    (U : Matrix G G ℂ) (ψ : QState (G × R)) (x : G) (z : R) :
    ApplyGate (TensorGate U 1) ψ (x, z) =
      ApplyGate U (fun y => ψ (y, z)) x := by
  simp only [ApplyGate, TensorGate, Matrix.kronecker_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.one_apply]
  simp

theorem run_hiddenSubgroupSamplingCircuit_apply
    (f : G → R) (e : G ≃ AddChar G ℂ) (x : G) (z : R) :
    Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
        (TensorState (Uniform G) (Ket 0)) (x, z) =
      fourier (addOracleLabelBranch f (Uniform G) z) (e x) := by
  simp only [hiddenSubgroupSamplingCircuit, Run]
  rw [applyGate_tensorGate_one_slice]
  exact applyGate_fourierGate e (addOracleLabelBranch f (Uniform G) z) x

theorem bornProb_run_hiddenSubgroupSamplingCircuit
    (f : G → R) (e : G ≃ AddChar G ℂ) (χ : AddChar G ℂ) (z : R) :
    BornProb
        (Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
          (TensorState (Uniform G) (Ket 0))) (e.symm χ, z) =
      BornProb (fourier (addOracleLabelBranch f (Uniform G) z)) χ := by
  unfold BornProb
  rw [run_hiddenSubgroupSamplingCircuit_apply]
  simp

theorem bornProb_fourier_addOracleLabelBranch
    (f : G → R) (H : AddSubgroup G) (hf : HidesSubgroup f H)
    (z : R) (χ : AddChar G ℂ) :
    BornProb (fourier (addOracleLabelBranch f (Uniform G) z)) χ =
      MarginalProbRight
          (Run (AddOracle f) [Step.query] (TensorState (Uniform G) (Ket 0))) {z} *
        (if χ ∈ characterAnnihilator H then
          1 / (Fintype.card (characterAnnihilator H) : ℝ) else 0) := by
  by_cases hz : ∃ s : G, f s = z
  · rcases hz with ⟨s, rfl⟩
    rw [addOracleLabelBranch_uniform_eq_smul_coset f H hf s,
      show fourier (cosetBranchScale H • abelianCosetState H s) =
          cosetBranchScale H • fourier (abelianCosetState H s) by
        exact (fourierEquiv (G := G)).map_smul (cosetBranchScale H)
          (abelianCosetState H s),
      addOracle_hidden_label_weight f H hf s]
    rw [show BornProb (cosetBranchScale H • fourier (abelianCosetState H s)) χ =
        ‖cosetBranchScale H‖ ^ 2 * BornProb (fourier (abelianCosetState H s)) χ by
      simp [BornProb, mul_pow],
      norm_cosetBranchScale_sq, bornProb_fourier_abelianCosetState]
  · have hunused : ∀ x : G, f x ≠ z := by
      intro x hx
      exact hz ⟨x, hx⟩
    rw [addOracleLabelBranch_eq_zero_of_unused f z hunused,
      addOracle_label_weight_eq_zero f (Uniform G) z hunused]
    simp [fourier, BornProb]

private theorem sum_actual_output_label_masses (f : G → R) :
    (∑ z : R,
      MarginalProbRight
        (Run (AddOracle f) [Step.query] (TensorState (Uniform G) (Ket 0))) {z}) = 1 := by
  let ψ := Run (AddOracle f) [Step.query] (TensorState (Uniform G) (Ket 0))
  calc
    (∑ z : R, MarginalProbRight ψ {z}) = MarginalProbRight ψ Finset.univ := by
      unfold MarginalProbRight MeasureProb
      simp only [Finset.sum_product, Finset.sum_singleton]
      rw [Finset.sum_comm]
    _ = MeasureProb (Uniform G) Finset.univ := by
      simpa [ψ] using marginalProbRight_run_addOracle_zero f (Uniform G) Finset.univ
    _ = 1 := measureProb_univ (normalized_uniform (by exact_mod_cast Fintype.card_pos))

theorem marginalProbLeft_hiddenSubgroupSampling_singleton
    (f : G → R) (H : AddSubgroup G) (hf : HidesSubgroup f H)
    (e : G ≃ AddChar G ℂ) (χ : AddChar G ℂ) :
    MarginalProbLeft
        (Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
          (TensorState (Uniform G) (Ket 0))) {e.symm χ} =
      if χ ∈ characterAnnihilator H then
        1 / (Fintype.card (characterAnnihilator H) : ℝ) else 0 := by
  unfold MarginalProbLeft MeasureProb
  simp only [Finset.sum_product, Finset.sum_singleton]
  simp_rw [bornProb_run_hiddenSubgroupSamplingCircuit f e χ,
    bornProb_fourier_addOracleLabelBranch f H hf]
  rw [← Finset.sum_mul, sum_actual_output_label_masses f, one_mul]

theorem marginalProbLeft_hiddenSubgroupSampling
    (f : G → R) (H : AddSubgroup G) (hf : HidesSubgroup f H)
    (e : G ≃ AddChar G ℂ) (S : Finset (AddChar G ℂ)) :
    MarginalProbLeft
        (Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
          (TensorState (Uniform G) (Ket 0))) (S.map e.symm.toEmbedding) =
      MeasureProb (fourier (abelianCosetState H 0)) S := by
  unfold MarginalProbLeft MeasureProb
  simp only [Finset.sum_product, Finset.sum_map, Equiv.toEmbedding_apply]
  apply Finset.sum_congr rfl
  intro χ hχ
  have hsingle := marginalProbLeft_hiddenSubgroupSampling_singleton f H hf e χ
  unfold MarginalProbLeft MeasureProb at hsingle
  simp only [Finset.sum_product, Finset.sum_singleton] at hsingle
  rw [hsingle, bornProb_fourier_abelianCosetState]

theorem normalized_run_hiddenSubgroupSampling
    (f : G → R) (e : G ≃ AddChar G ℂ) :
    Normalized
      (Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
        (TensorState (Uniform G) (Ket 0))) := by
  exact (hiddenSubgroupSamplingCircuit_unitary (R := R) e).normalized_run
    (addOracle_unitary f)
    (normalized_tensorState (normalized_uniform (by exact_mod_cast Fintype.card_pos))
      (normalized_ket 0))

open scoped Matrix.Norms.L2Operator

theorem marginalProbLeft_hiddenSubgroupSampling_oracle_error
    (f : G → R) (e : G ≃ AddChar G ℂ) (E : Finset G)
    (P : Matrix (G × R) (G × R) ℂ) (δ : ℝ)
    (hP : P ∈ Matrix.unitaryGroup (G × R) ℂ) (hδ : ‖AddOracle f - P‖ ≤ δ) :
    |MarginalProbLeft
        (Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
          (TensorState (Uniform G) (Ket 0))) E -
      MarginalProbLeft
        (Run P (hiddenSubgroupSamplingCircuit (R := R) e)
          (TensorState (Uniform G) (Ket 0))) E| ≤ 2 * δ := by
  have h := measureProb_run_sub_le_queryCount_of_le (AddOracle f) P
    (hiddenSubgroupSamplingCircuit (R := R) e) (TensorState (Uniform G) (Ket 0))
    (E ×ˢ Finset.univ) δ (addOracle_unitary f) hP
    (hiddenSubgroupSamplingCircuit_unitary (R := R) e)
    (normalized_tensorState (normalized_uniform (by exact_mod_cast Fintype.card_pos))
      (normalized_ket 0)) hδ
  simpa only [MarginalProbLeft, (hiddenSubgroupSamplingCircuit_resources (R := R) e).1,
    Nat.cast_one, mul_one] using h

end Qatlib.Concepts.HspRecovery.Distinguisher
