/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.PhaseReadout.CleanSubroutinePhaseReadout
import Qatlib.Concepts.QspSimulation.Achievability.CleanSignalSimulation
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyDrivenPhaseReadout
import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyPureReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopySpectralReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.CoherentSim.CleanQPEBands
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.GibbsMetropolis.EnergyReadout

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable def signalEnergyOracle {H : Type} [DecidableEq H]
    (U : Matrix H H ℂ) : Matrix (Bool × (Bool × (Bool × H)))
      (Bool × (Bool × (Bool × H))) ℂ :=
  TensorGate (1 : Matrix Bool Bool ℂ) (controlOracle (parallelOracle (J := Bool) U))

noncomputable def signalEnergyFrame {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) :
    Matrix (Bool × (Bool × (Bool × H))) I ℂ :=
  scaleEightFrame (hamiltonianFrame F)

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

private theorem signalEnergyFrame_isometry {F : Matrix H I ℂ} (hF : IsIsometry F) :
    IsIsometry (signalEnergyFrame F) :=
  scaleEightFrame_isometry _ (averageFrame_isIsometry (averageFrame_isIsometry hF))

theorem signalEnergy_evolution_spectral (D : ℕ) (A V : Operator D) (eig : Fin D → ℝ)
    (t : ℝ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : A = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ) :
    hamiltonianEvolution A t =
      V * Matrix.diagonal (fun i => Complex.exp (-Complex.I * (t : ℂ) * (eig i : ℂ))) * Vᴴ := by
  let W : unitary (Operator D) := ⟨V, hV⟩
  let f := Unitary.conjStarAlgAut ℂ (Operator D) W
  let B := Matrix.diagonal (fun i => -Complex.I * (t : ℂ) * (eig i : ℂ))
  letI : NormedAlgebra ℚ (Operator D) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hm := NormedSpace.map_exp f f.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional B
  have he : f B = (-Complex.I * (t : ℂ)) • A := by
    rw [hs]
    simp only [f, Unitary.conjStarAlgAut_apply, B]
    change V * Matrix.diagonal (fun i => -Complex.I * (t : ℂ) * (eig i : ℂ)) * Vᴴ = _
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
    rfl
  rw [he] at hm
  unfold hamiltonianEvolution
  refine hm.symm.trans ?_
  change V * NormedSpace.exp B * Vᴴ = _
  rw [Matrix.exp_diagonal]
  apply congrArg (fun B : Operator D => V * B * Vᴴ)
  apply congrArg (Matrix.diagonal : (Fin D → ℂ) → Operator D)
  funext i
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]

private theorem signalEnergy_eigen (D : ℕ) (A V : Operator D) (eig : Fin D → ℝ)
    (t : ℝ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : A = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ) (i : Fin D) :
    hamiltonianEvolution A t *ᵥ (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) =
      Complex.exp (2 * Real.pi * Complex.I * ((-t * eig i / (2 * Real.pi) : ℝ) : ℂ)) •
        (V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) := by
  have hVV : Vᴴ * V = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using! hV
  have huv : hamiltonianEvolution A t * V = V * Matrix.diagonal
    (fun i => Complex.exp (-Complex.I * (t : ℂ) * (eig i : ℂ))) := by
    rw [signalEnergy_evolution_spectral D A V eig t hV hs, Matrix.mul_assoc, hVV, Matrix.mul_one]
  have hp : -Complex.I * (t : ℂ) * (eig i : ℂ) =
      2 * Real.pi * Complex.I * ((-t * eig i / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [Matrix.mulVec_mulVec, huv, ← Matrix.mulVec_mulVec]
  have hd : Matrix.diagonal (fun j => Complex.exp (-Complex.I * (t : ℂ) * (eig j : ℂ))) *ᵥ Qatlib.Foundations.PureStateMath.Ket i =
      Complex.exp (-Complex.I * (t : ℂ) * (eig i : ℂ)) • Qatlib.Foundations.PureStateMath.Ket i := by
    funext j
    by_cases hj : j = i <;> simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, hj]
  rw [hd, Matrix.mulVec_smul, hp]

private theorem signalEnergy_program (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (t η : ℝ) (hA : A.IsHermitian)
    (h : ProjectedUnitaryEncoding A U F F) (hη : 0 < η) :
    ∃ (n : ℕ) (cs : List (AdjointStep (Bool × (Bool × H)))),
      WellFormedAdjointCircuit cs ∧
      WellFormedAdjointCircuit (scaleEightAmplifyWord (hamiltonianFrame F) cs) ∧
      adjointQueryCount (scaleEightAmplifyWord (hamiltonianFrame F) cs) = 27 * (4 * n + 1) ∧
      adjointGateCount (scaleEightAmplifyWord (hamiltonianFrame F) cs) = 27 * (4 * n + 6) + 79 ∧
      ∀ ξ : QState I, ‖toEuclidean_fromVec
        (evaluate (signalEnergyOracle U) (scaleEightAmplifyWord (hamiltonianFrame F) cs) *ᵥ
          (signalEnergyFrame F *ᵥ ξ) - signalEnergyFrame F *ᵥ (hamiltonianEvolution A t *ᵥ ξ))‖ ≤
        η * ‖toEuclidean_fromVec ξ‖ := by
  obtain ⟨n, cs, hcs, _, _, hq, hg, he⟩ :=
    signal_simulation_actual_clean_counted_consumer H I A U F t η hA h hη
  exact ⟨n, cs, hcs, (scale_eight_three_level_actual_counts _ _ _ cs
    (averageFrame_isIsometry (averageFrame_isIsometry h.right_isometry)) hcs).1, hq, hg, he⟩

theorem signal_energy_actual_compiled_qpe_window_and_resources
    (H : Type) [Fintype H] [DecidableEq H] (D M k : ℕ) (hM : 2 ≤ M)
    (A V : Operator D) (eig : Fin D → ℝ) (U : Matrix H H ℂ)
    (F : Matrix H (Fin D) ℂ) (t : ℝ) (hA : A.IsHermitian)
    (h : ProjectedUnitaryEncoding A U F F) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : A = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ) :
    ∃ (n : ℕ) (cs : List (AdjointStep (Bool × (Bool × H)))),
      WellFormedAdjointCircuit cs ∧
      let body := scaleEightAmplifyWord (hamiltonianFrame F) cs
      let word := cleanQPEWord M body
      WellFormedAdjointCircuit word ∧
        adjointQueryCount word = (M - 1) * 27 * (4 * n + 1) ∧
        adjointGateCount word = 2 * (M - 1) + 2 + (M - 1) * (27 * (4 * n + 6) + 79) ∧
        ∀ i : Fin D,
          let ψ := V *ᵥ Qatlib.Foundations.PureStateMath.Ket i
          let out := evaluate (TensorGate (1 : Operator M) (controlOracle (signalEnergyOracle U)))
            word *ᵥ cleanQPEInput M (by omega) (signalEnergyFrame F *ᵥ ψ)
          let E := Finset.univ.filter (fun z : Fin M =>
            phaseDistance (-t * eig i / (2 * Real.pi)) ((z.val : ℝ) / (M : ℝ)) ≤ 1 / (M : ℝ))
          8 / Real.pi ^ 2 - (1 / 2 : ℝ) ^ k ≤ cleanQPEEventMass M out E := by
  classical
  have hMp : 0 < M := by omega
  have hden : 0 < ((M - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < M - 1 by omega)
  let η := (1 / 2 : ℝ) ^ k / (2 * ((M - 1 : ℕ) : ℝ))
  have hη : 0 < η := by dsimp [η]; positivity
  have hbudget : 2 * ((M - 1 : ℕ) : ℝ) * η = (1 / 2 : ℝ) ^ k := by
    dsimp [η]
    field_simp
  obtain ⟨n, cs, hcs, hb, hq, hg, he⟩ := signalEnergy_program A U F t η hA h hη
  have hw := clean_qpe_actual_expansion_semantics_and_paid_inverse
    (Bool × (Bool × (Bool × H))) M (signalEnergyOracle U)
    (scaleEightAmplifyWord (hamiltonianFrame F) cs) hMp hb
  refine ⟨n, cs, hcs, hw.1, ?_, ?_, ?_⟩
  · rw [hw.2.1, hq]
    ring
  · rw [hw.2.2.1, hg]
  · intro i
    let E := Finset.univ.filter (fun z : Fin M =>
      phaseDistance (-t * eig i / (2 * Real.pi)) ((z.val : ℝ) / (M : ℝ)) ≤ 1 / (M : ℝ))
    have herr := clean_qpe_actual_spectral_born_event_error
      (Bool × (Bool × (Bool × H))) (Fin D) Unit M hMp (signalEnergyOracle U)
      (signalEnergyFrame F) (hamiltonianEvolution A t)
      (scaleEightAmplifyWord (hamiltonianFrame F) cs) η
      (fun _ => V *ᵥ Qatlib.Foundations.PureStateMath.Ket i) (fun _ => (1 : ℂ))
      (fun _ => -t * eig i / (2 * Real.pi))
      (tensorGate_unitary (Submonoid.one_mem _)
        (controlOracle_unitary (parallelOracle_unitary h.unitary)))
      (signalEnergyFrame_isometry h.right_isometry) (hamiltonianEvolution_unitary hA t)
      hb hη.le he
      (by intro j l; cases j; cases l; simpa [ApplyGate] using!
        (inner_applyGate hV (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket i)).trans (by simp [inner_ket_ket]))
      (by simp) (fun _ => signalEnergy_eigen D A V eig t hV hs i) E
    simp only [Fintype.sum_unique, norm_one, one_pow, one_mul, one_smul, hbudget] at herr
    have hl := offgrid_phase_window_probability M (-t * eig i / (2 * Real.pi)) hM
    (try dsimp only at herr ⊢)
    change 8 / Real.pi ^ 2 - (1 / 2 : ℝ) ^ k ≤ _
    have hh := (abs_le.mp herr).1
    dsimp [E] at hh
    linarith

private theorem signalEnergy_Z_encoding :
    pauliZ.IsHermitian ∧ ProjectedUnitaryEncoding pauliZ pauliZ (1 : Operator 2) 1 := by
  have hh : pauliZᴴ = pauliZ := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [pauliZ, Matrix.conjTranspose_apply]
  have hu : pauliZ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hh]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  exact ⟨hh, hu, by simp [IsIsometry], by simp [IsIsometry], by simp [compress]⟩

private theorem signalEnergy_Z_kernel (j : Fin 2) (z : Fin 4) :
    qpeKernel 4 (-(Real.pi / 2) * (if j = 0 then 1 else -1) / (2 * Real.pi)) z =
      Qatlib.Foundations.PureStateMath.Ket (if j = 0 then (3 : Fin 4) else 1) z := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  fin_cases j
  · have he : -(Real.pi / 2) * (1 : ℝ) / (2 * Real.pi) = -(1 / 4 : ℝ) := by
      field_simp
      norm_num
    simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
    rw [he, ← qpeKernel_int_add 4 (-(1 / 4 : ℝ)) z 1]
    convert! (offgrid_phase_geometric_and_periodic 4 0 z (by norm_num)).2.2 (3 : Fin 4) using 1
    norm_num
  · have he : -(Real.pi / 2) * (-1 : ℝ) / (2 * Real.pi) = (1 / 4 : ℝ) := by
      field_simp
      norm_num
    simp only [Fin.ext_iff, Fin.val_zero, Nat.one_ne_zero, if_false]
    rw [he]
    convert! (offgrid_phase_geometric_and_periodic 4 0 z (by norm_num)).2.2 (1 : Fin 4) using 1
    norm_num

theorem signal_energy_z_superposition_actual_consumer (k : ℕ) :
    ∃ (n : ℕ) (cs : List (AdjointStep (Bool × (Bool × Fin 2)))),
      WellFormedAdjointCircuit cs ∧
      let F : Operator 2 := 1
      let body := scaleEightAmplifyWord (hamiltonianFrame F) cs
      let word := cleanQPEWord 4 body
      let ψ : QState (Fin 2) := fun _ => (Real.sqrt 2 : ℂ)⁻¹
      let out := evaluate (TensorGate (1 : Operator 4) (controlOracle (signalEnergyOracle pauliZ)))
        word *ᵥ cleanQPEInput 4 (by norm_num) (signalEnergyFrame F *ᵥ ψ)
      WellFormedAdjointCircuit word ∧
        adjointQueryCount word = 81 * (4 * n + 1) ∧
        adjointGateCount word = 81 * (4 * n + 6) + 245 ∧
        1 - (1 / 2 : ℝ) ^ k ≤ cleanQPEEventMass 4 out {1,3} ∧
        |cleanQPEEventMass 4 out {1} - (1 / 2 : ℝ)| ≤ (1 / 2 : ℝ) ^ k ∧
        |cleanQPEEventMass 4 out {3} - (1 / 2 : ℝ)| ≤ (1 / 2 : ℝ) ^ k := by
  classical
  let F : Operator 2 := 1
  let η := (1 / 2 : ℝ) ^ k / 6
  have hη : 0 < η := by dsimp [η]; positivity
  have hbudget : 2 * (4 - 1 : ℕ) * η = (1 / 2 : ℝ) ^ k := by dsimp [η]; norm_num; ring
  obtain ⟨n, cs, hcs, hb, hq, hg, he⟩ := signalEnergy_program pauliZ pauliZ F
    (Real.pi / 2) η signalEnergy_Z_encoding.1 signalEnergy_Z_encoding.2 hη
  have hw := clean_qpe_actual_expansion_semantics_and_paid_inverse
    (Bool × (Bool × (Bool × Fin 2))) 4 (signalEnergyOracle pauliZ)
    (scaleEightAmplifyWord (hamiltonianFrame F) cs) (by norm_num) hb
  let eig : Fin 2 → ℝ := fun j => if j = 0 then 1 else -1
  have hs : pauliZ = (1 : Operator 2) * Matrix.diagonal (fun j => (eig j : ℂ)) * (1 : Operator 2)ᴴ := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [eig, pauliZ]
  let c : Fin 2 → ℂ := fun _ => (Real.sqrt 2 : ℂ)⁻¹
  have hc (j : Fin 2) : ‖c j‖ ^ 2 = (1 / 2 : ℝ) := by
    dsimp [c]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hψ : (∑ j : Fin 2, c j • Qatlib.Foundations.PureStateMath.Ket j) = (fun _ : Fin 2 => (Real.sqrt 2 : ℂ)⁻¹) := by
    funext i
    fin_cases i <;> simp [c, Qatlib.Foundations.PureStateMath.Ket]
  have herr (E : Finset (Fin 4)) := clean_qpe_actual_spectral_born_event_error
    (Bool × (Bool × (Bool × Fin 2))) (Fin 2) (Fin 2) 4 (by norm_num)
    (signalEnergyOracle pauliZ) (signalEnergyFrame F) (hamiltonianEvolution pauliZ (Real.pi / 2))
    (scaleEightAmplifyWord (hamiltonianFrame F) cs) η (fun j => Qatlib.Foundations.PureStateMath.Ket j) c
    (fun j => -(Real.pi / 2) * eig j / (2 * Real.pi))
    (tensorGate_unitary (Submonoid.one_mem _)
      (controlOracle_unitary (parallelOracle_unitary signalEnergy_Z_encoding.2.unitary)))
    (signalEnergyFrame_isometry (by simp [F, IsIsometry]))
    (hamiltonianEvolution_unitary signalEnergy_Z_encoding.1 (Real.pi / 2)) hb hη.le he
    (by intro j l; exact inner_ket_ket j l)
    (by simp [hc])
    (by intro j; simpa only [Matrix.one_mulVec] using!
      (signalEnergy_eigen 2 pauliZ 1 eig (Real.pi / 2) (Submonoid.one_mem _) hs j)) E
  have hmass (E : Finset (Fin 4)) :
      |cleanQPEEventMass 4
        (evaluate (TensorGate (1 : Operator 4) (controlOracle (signalEnergyOracle pauliZ)))
          (cleanQPEWord 4 (scaleEightAmplifyWord (hamiltonianFrame F) cs)) *ᵥ
            cleanQPEInput 4 (by norm_num) (signalEnergyFrame F *ᵥ
              (fun _ : Fin 2 => (Real.sqrt 2 : ℂ)⁻¹))) E -
          (∑ j : Fin 2, (1 / 2 : ℝ) * (∑ z ∈ E, ‖Qatlib.Foundations.PureStateMath.Ket (if j = 0 then (3 : Fin 4) else 1) z‖ ^ 2))| ≤
        (1 / 2 : ℝ) ^ k := by
    have hh := herr E
    (try dsimp only at hh)
    rw [hψ, hbudget] at hh
    simp only [hc] at hh
    simpa only [eig, signalEnergy_Z_kernel] using! hh
  have hj10 : (1 : Fin 2) ≠ 0 := by decide
  have hz13 : (1 : Fin 4) ≠ 3 := by decide
  have hz31 : (3 : Fin 4) ≠ 1 := Ne.symm hz13
  refine ⟨n, cs, hcs, hw.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw.2.1, hq]
    norm_num
    ring
  · rw [hw.2.2.1, hg]
    norm_num
    ring
  · have hh := hmass {1,3}
    have hs : (∑ j : Fin 2, (1 / 2 : ℝ) *
        (∑ z ∈ ({1,3} : Finset (Fin 4)), ‖Qatlib.Foundations.PureStateMath.Ket (if j = 0 then (3 : Fin 4) else 1) z‖ ^ 2)) = 1 := by
      norm_num [Fin.sum_univ_two, Qatlib.Foundations.PureStateMath.Ket, Finset.sum_insert, hj10, hz13, hz31]
    rw [hs] at hh
    have hb := (abs_le.mp hh).1
    dsimp only [F] at hb ⊢
    linarith
  · have hh := hmass {1}
    have hs : (∑ j : Fin 2, (1 / 2 : ℝ) *
        (∑ z ∈ ({1} : Finset (Fin 4)), ‖Qatlib.Foundations.PureStateMath.Ket (if j = 0 then (3 : Fin 4) else 1) z‖ ^ 2)) = 1 / 2 := by
      norm_num [Fin.sum_univ_two, Qatlib.Foundations.PureStateMath.Ket, hj10, hz13, hz31]
    rw [hs] at hh
    exact hh
  · have hh := hmass {3}
    have hs : (∑ j : Fin 2, (1 / 2 : ℝ) *
        (∑ z ∈ ({3} : Finset (Fin 4)), ‖Qatlib.Foundations.PureStateMath.Ket (if j = 0 then (3 : Fin 4) else 1) z‖ ^ 2)) = 1 / 2 := by
      norm_num [Fin.sum_univ_two, Qatlib.Foundations.PureStateMath.Ket, hj10, hz13, hz31]
    rw [hs] at hh
    exact hh

end Qatlib.Concepts.GibbsMetropolis.EnergyReadout
