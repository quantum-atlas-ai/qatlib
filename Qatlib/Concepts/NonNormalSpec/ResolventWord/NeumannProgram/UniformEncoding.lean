/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.SharedWord
public import Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.DefectPolynomial
public import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram
open Matrix
open scoped BigOperators Kronecker

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- The coefficient mass of `b` unit coefficients is `b`. -/
private theorem uniform_mass (b : ℕ) : Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass (fun _ : Fin b => (1 : ℂ)) = b := by
  simp [Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass]

def uniformNeumannPrepare (b : ℕ) (hb : 0 < b) :
    Matrix (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace (b-1) (Fin b × H)) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace (b-1) (Fin b × H)) ℂ :=
  Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle (b-1) (Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H)
    (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare (fun _ : Fin b => (1 : ℂ)) ⟨0,hb⟩))

def uniformNeumannWord (b : ℕ) (hb : 0 < b) (P : Matrix H H ℂ) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace (b-1) (Fin b × H))) :=
  [.gate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannPrepare b hb)ᴴ] ++ Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.sharedNeumannWord b P ++
    [.gate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannPrepare b hb)]

def uniformNeumannFrame (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ) :
    Matrix (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace (b-1) (Fin b × H)) I ℂ :=
  Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannFrame (b-1) (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) (⟨0,hb⟩ : Fin b) * F)

/-- The uniform Neumann preparation matrix is unitary for a positive branch count. -/
private theorem uniform_prepare_unitary (b : ℕ) (hb : 0 < b) :
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannPrepare (H := H) b hb ∈ unitaryGroup (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace (b-1) (Fin b × H)) ℂ := by
  have hm : 0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass (fun _ : Fin b => (1 : ℂ)) := by
    rw [uniform_mass]
    exact_mod_cast hb
  exact Qatlib.Foundations.PureStateMath.tensorGate_unitary (unitaryGroup _ ℂ).one_mem
    (Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister_unitary (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare_unitary _ _ hm))

/-- The uniform Neumann word has the stated linear query and gate counts and is well formed for
an orthogonal projector. -/
theorem uniform_neumann_word_cost_legal (b : ℕ) (hb : 0 < b) (P : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannWord b hb P) = 2*b-1 ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannWord b hb P) = 2*b ∧
    (Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P → Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannWord b hb P)) := by
  obtain ⟨hq,hg,hw⟩ :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.shared_neumann_word_cost_legal b hb P
  refine ⟨?_, ?_, ?_⟩
  · simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannWord, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_append, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount, hq]
    omega
  · simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannWord, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount_append, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount, hg]
    omega
  · intro hp
    have hu := uniform_prepare_unitary (H := H) b hb
    simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append_iff,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
    exact ⟨⟨Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hu, hw hp⟩, hu⟩

omit [Fintype H] in
/-- The preparation lift of the zero-label basis state equals its encoding fiber. -/
private theorem ket_fiber [Fintype H] (b : ℕ) (hb : 0 < b) :
    Qatlib.Concepts.BlockEncoding.LCU.prepareLift (I := H) (Qatlib.Foundations.PureStateMath.Ket (⟨0,hb⟩ : Fin b)) = Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) (⟨0,hb⟩ : Fin b) := by
  ext ⟨k,h⟩ i
  simp [Qatlib.Concepts.BlockEncoding.LCU.prepareLift,
      Qatlib.Foundations.PureStateMath.Ket, Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- Uniform preparation around a selected family compresses to the arithmetic mean of its
matrices. -/
private theorem uniform_average (b : ℕ) (hb : 0 < b)
    (V : Fin b → Matrix H H ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) (⟨0,hb⟩ : Fin b))
      ((Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare (fun _ : Fin b => (1 : ℂ)) ⟨0,hb⟩))ᴴ *
        Qatlib.Concepts.BlockEncoding.LCU.select V * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare (fun _ : Fin b => (1 : ℂ)) ⟨0,hb⟩))
      (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) (⟨0,hb⟩ : Fin b)) =
        ((b : ℂ)⁻¹) • ∑ k, V k := by
  have hm : 0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass (fun _ : Fin b => (1 : ℂ)) := by
    rw [uniform_mass]
    exact_mod_cast hb
  have h :=
      Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientLCUUnitary_compress
      (fun _ : Fin b => (1 : ℂ)) V ⟨0,hb⟩ hm
  have hp : Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed (fun _ : Fin b => (1 : ℂ)) V = V := by
    funext k
    simp [Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed,
        Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPhase]
  simp only [Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientLCUUnitary] at h
  rw [hp, ket_fiber] at h
  simpa only [uniform_mass, Complex.ofReal_natCast, one_div, Finset.smul_sum] using h

/-- Compression of the adjoint-oracle defect power gives the compressed adjoint times the
corresponding compressed left-defect power. -/
private theorem compressed_power (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) (k : ℕ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress F (Uᴴ*(Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F*U*(1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)*Uᴴ)^k) F =
      (Qatlib.Concepts.Execution.WorkspaceCP.compress F U F)ᴴ * (1-Qatlib.Concepts.Execution.WorkspaceCP.compress F U F*(Qatlib.Concepts.Execution.WorkspaceCP.compress F U F)ᴴ)^k := by
  have h :=
      congrArg (fun X : Matrix H I ℂ => Fᴴ*Uᴴ*X)
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumann_frame_power U F k)
  rw [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumann_frame_defect U F hU hF] at h
  simpa only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc] using h

/-- The uniform Neumann word exactly encodes the left-defect Neumann polynomial divided by the
positive branch count. -/
theorem uniform_neumann_word_encoding (b : ℕ) (hb : 0 < b)
    (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) :
    Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding (((b : ℂ)⁻¹) • Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann (Qatlib.Concepts.Execution.WorkspaceCP.compress F U F) b)
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle (b-1) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin b) U))
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannWord b hb (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)))
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F) := by
  let E :=
      Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := Fin b × H)
      (fun _ : Fin (b-1) => (false,false))
  let L := Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) (⟨0,hb⟩ : Fin b)
  let R :=
      Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H)
      (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare (fun _ : Fin b => (1 : ℂ)) ⟨0,hb⟩)
  let W := Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle (b-1) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin b) U))
    (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.sharedNeumannWord b (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F))
  have hp := Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector_isOrthogonalProjector hF
  have hw :=
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniform_neumann_word_cost_legal b hb (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)).2.2 hp
  have hu : Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle (b-1) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin b) U) ∈
      unitaryGroup (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace (b-1) (Fin b × H)) ℂ :=
    Qatlib.Foundations.PureStateMath.tensorGate_unitary (unitaryGroup _ ℂ).one_mem
      (Qatlib.Concepts.BlockEncoding.LCU.select_unitary _ (fun _ => hU))
  have hf : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F) :=
    Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_isIsometry _)
      (Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_isIsometry _) hF)
  refine ⟨hw.evaluate_unitary hu, hf, hf, ?_⟩
  have he : Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle (b-1) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin b) U))
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannWord b hb (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)) =
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannPrepare b hb)ᴴ * W * Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannPrepare b hb := by
    simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate_append, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix, Matrix.mul_one]
    rfl
  have hcorner :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.shared_neumann_word_corner b hb (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F) U hU hp
  have hcompress : Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F)
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle (b-1) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin b) U))
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannWord b hb (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F))) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F) =
      Qatlib.Concepts.Execution.WorkspaceCP.compress F (Qatlib.Concepts.Execution.WorkspaceCP.compress L (Rᴴ * Qatlib.Concepts.Execution.WorkspaceCP.compress E W E * R) L) F := by
    rw [he]
    simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannFrame, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannPrepare,
      Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.conjTranspose_mul, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle, Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose,
      Matrix.conjTranspose_one, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (fun _ : Fin (b-1) => (false,false)))ᴴ,
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumann_fiber_data_left]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix (Fin (b-1) → Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair)
      (Fin (b-1) → Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair) ℂ) R), Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumann_fiber_data]
    simp only [E, L, R, Matrix.mul_assoc]
  rw [hcompress]
  change Qatlib.Concepts.Execution.WorkspaceCP.compress F
      (Qatlib.Concepts.Execution.WorkspaceCP.compress L (Rᴴ * Qatlib.Concepts.Execution.WorkspaceCP.compress E W E * R) L) F = _
  rw [show Qatlib.Concepts.Execution.WorkspaceCP.compress E W E = Qatlib.Concepts.BlockEncoding.LCU.select (fun k : Fin b =>
      Uᴴ*(Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F*U*(1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)*Uᴴ)^k.val) from hcorner]
  rw [uniform_average b hb]
  rw [Qatlib.Concepts.Execution.WorkspaceCP.compress_smul]
  congr 1
  calc
    Qatlib.Concepts.Execution.WorkspaceCP.compress F (∑ k : Fin b, Uᴴ*(Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F*U*(1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)*Uᴴ)^k.val) F =
        ∑ k : Fin b, Qatlib.Concepts.Execution.WorkspaceCP.compress F (Uᴴ*(Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F*U*(1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)*Uᴴ)^k.val) F := by
      simp only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.mul_sum, Matrix.sum_mul]
    _ = (Qatlib.Concepts.Execution.WorkspaceCP.compress F U F)ᴴ * ∑ k : Fin b,
        (1-Qatlib.Concepts.Execution.WorkspaceCP.compress F U F*(Qatlib.Concepts.Execution.WorkspaceCP.compress F U F)ᴴ)^k.val := by
      simp only [compressed_power U F hU hF, Finset.mul_sum]
    _ = Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann (Qatlib.Concepts.Execution.WorkspaceCP.compress F U F) b := by
      unfold Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann
      congr 1
      exact Fin.sum_univ_eq_sum_range _ b

end Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram
