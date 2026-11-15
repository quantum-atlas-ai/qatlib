/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.SharedOriginalOracle
public import Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidSlot.CleanWordLCU

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram
open Matrix Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

def outerLabelEquiv (b : ℕ) :
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace (b-1) (Fin b × (J × H)) ≃
      J × Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace (b-1) (Fin b × H) where
  toFun x := (x.2.2.1, (x.1, (x.2.1, x.2.2.2)))
  invFun y := (y.2.1, (y.2.2.1, (y.1, y.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

def outerLabelWord (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ)
    (G₁ G₂ G₃ : J → Matrix H H ℂ) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (J × Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace (b-1) (Fin b × H))) :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord (Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelEquiv (J := J) (H := H) b))
    (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.sharedOriginalWord b hb F G₁ G₂ G₃)

omit [Fintype J] [Fintype H] [DecidableEq H] in

/-- Relabeling moves the outer label register past the uniform Neumann oracle construction. -/
theorem outerLabelOracle (b : ℕ) (U : Matrix H H ℂ) :
    Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelEquiv (J := J) (H := H) b)
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U)) =
      Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b U) := by
  ext ⟨j,f,k,h⟩ ⟨l,g,m,i⟩
  simp [Qatlib.Foundations.PureStateMath.BornBridge.relabelGate, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelEquiv, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle,
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle, Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, Qatlib.Concepts.BlockEncoding.LCU.select, Qatlib.Foundations.PureStateMath.TensorGate, Matrix.one_apply,
    ite_mul, mul_ite]
  split_ifs <;> simp_all

omit [DecidableEq I] in
/-- Evaluating the outer-label word equals the relabeled evaluation of the shared original word. -/
theorem outerLabelWord_evaluate [DecidableEq I] (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ)
    (G₁ G₂ G₃ : J → Matrix H H ℂ) (U : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b U))
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelWord b hb F G₁ G₂ G₃) =
      Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelEquiv (J := J) (H := H) b)
        (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U))
          (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.sharedOriginalWord b hb F G₁ G₂ G₃)) := by
  let e :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelEquiv (J := J)
      (H := H) b
  have h1 : Qatlib.Foundations.PureStateMath.BornBridge.relabelGate e 1 = 1 :=
      Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_one e
  have hm : ∀ U V, Qatlib.Foundations.PureStateMath.BornBridge.relabelGate e (U*V) = Qatlib.Foundations.PureStateMath.BornBridge.relabelGate e U * Qatlib.Foundations.PureStateMath.BornBridge.relabelGate e V :=
    fun U V => Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul e U V
  have ha : ∀ U, Qatlib.Foundations.PureStateMath.BornBridge.relabelGate e Uᴴ = (Qatlib.Foundations.PureStateMath.BornBridge.relabelGate e U)ᴴ := by
    intro U
    simp only [Qatlib.Foundations.PureStateMath.BornBridge.relabelGate, Matrix.conjTranspose_reindex]
  have h := Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_evaluate (Qatlib.Foundations.PureStateMath.BornBridge.relabelGate e) h1 hm ha
    (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U))
    (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.sharedOriginalWord b hb F G₁ G₂ G₃)
  simpa only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelWord, e,
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelOracle] using h

/-- Composing an encoding fiber with a frame gives that frame on the chosen fiber and zero
elsewhere. -/
private theorem fiber_frame_apply {K L M : Type} [Fintype L] [DecidableEq K] [DecidableEq L]
    (k₀ : K) (F : Matrix L M ℂ) (k : K) (l : L) (m : M) :
    (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := L) k₀ * F) (k,l) m = if k = k₀ then F l m else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single l]
  · by_cases hk : k = k₀ <;> simp [Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber, hk]
  · intro x _ hx
    simp [Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber, Ne.symm hx]
  · simp

omit [Fintype I] [DecidableEq I] in

/-- Reindexing the labeled uniform Neumann frame separates the label identity from the original
uniform frame. -/
theorem outerLabelFrame (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ) :
    Matrix.reindex (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelEquiv (J := J) (H := H) b) (Equiv.refl (J × I))
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.labelFrame (J := J) F)) =
      (1 : Matrix J J ℂ) ⊗ₖ Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F := by
  ext ⟨j,flags,slot,x⟩ ⟨l,i⟩
  simp [Matrix.reindex_apply, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelEquiv, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame,
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannFrame, fiber_frame_apply, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.labelFrame,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

omit [Fintype J] [Fintype I] [DecidableEq I] in
/-- Scalar multiplication of a selected family equals selecting the pointwise scalar multiples. -/
private theorem select_smul [Fintype J] [Fintype I] [DecidableEq I] (V : J → Matrix I I ℂ) (c : ℂ) :
    c • Qatlib.Concepts.BlockEncoding.LCU.select V = Qatlib.Concepts.BlockEncoding.LCU.select (fun j => c • V j) := by
  ext ⟨j,x⟩ ⟨k,y⟩
  by_cases h : j = k <;> simp [Qatlib.Concepts.BlockEncoding.LCU.select, Matrix.smul_apply, h]

/-- The clean outer-label corner selects the normalized left-defect Neumann approximant for each
compressed family body. -/
theorem outerLabel_clean_block (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ)
    (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) (G₁ G₂ G₃ : J → Matrix H H ℂ)
    (h₁ : ∀ j, G₁ j ∈ unitaryGroup H ℂ) (h₂ : ∀ j, G₂ j ∈ unitaryGroup H ℂ)
    (h₃ : ∀ j, G₃ j ∈ unitaryGroup H ℂ) (U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress ((1 : Matrix J J ℂ) ⊗ₖ Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F)
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b U))
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelWord b hb F G₁ G₂ G₃))
      ((1 : Matrix J J ℂ) ⊗ₖ Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F) =
      Qatlib.Concepts.BlockEncoding.LCU.select (fun j => ((b : ℂ)⁻¹) • Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann
        (Qatlib.Concepts.Execution.WorkspaceCP.compress F (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyMatrix G₁ G₂ G₃ U j) F) b) := by
  let e :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelEquiv (J := J)
      (H := H) b
  let L :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.labelFrame (J := J) F)
  let V := Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U))
    (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.sharedOriginalWord b hb F G₁ G₂ G₃)
  have hr : Qatlib.Concepts.Execution.WorkspaceCP.compress (Matrix.reindex e (Equiv.refl (J × I)) L)
      (Qatlib.Foundations.PureStateMath.BornBridge.relabelGate e V) (Matrix.reindex e (Equiv.refl (J × I)) L) = Qatlib.Concepts.Execution.WorkspaceCP.compress L V L := by
    simp only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Qatlib.Foundations.PureStateMath.BornBridge.relabelGate, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    rfl
  have hf : Matrix.reindex e (Equiv.refl (J × I)) L =
      (1 : Matrix J J ℂ) ⊗ₖ Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F := Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelFrame b hb F
  rw [hf] at hr
  rw [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelWord_evaluate]
  have hp :=
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.sharedOriginal_encoding_cost b hb F hF G₁ G₂ G₃ h₁ h₂ h₃ U hU).2.2.1.encoded
  rw [select_smul] at hp
  exact hr.trans hp

def weightedOriginalWord (b : ℕ) (hb : 0 < b) (F : Matrix H I ℂ)
    (G₁ G₂ G₃ : J → Matrix H H ℂ) (d : J → ℂ) (j₀ : J) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (J × Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace (b-1) (Fin b × H))) :=
  Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelWord b hb F G₁ G₂ G₃)

/-- The weighted original word exactly encodes the normalized weighted Neumann sum with the
stated linear query and gate counts. -/
theorem weightedOriginal_encoding_cost (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) (G₁ G₂ G₃ : J → Matrix H H ℂ)
    (h₁ : ∀ j, G₁ j ∈ unitaryGroup H ℂ) (h₂ : ∀ j, G₂ j ∈ unitaryGroup H ℂ)
    (h₃ : ∀ j, G₃ j ∈ unitaryGroup H ℂ) (U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (d : J → ℂ) (j₀ : J) (hmass : 0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d) :
    let O :=
        Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J)
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b U)
    let W :=
        Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.weightedOriginalWord b hb F G₁ G₂ G₃ d j₀
    O ∈ unitaryGroup _ ℂ ∧ Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit W ∧
    Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
      (∑ j, (d j / (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d : ℂ)) •
        (((b : ℂ)⁻¹) • Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann
          (Qatlib.Concepts.Execution.WorkspaceCP.compress F (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyMatrix G₁ G₂ G₃ U j) F) b))
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O W) (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F))
      (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F)) ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount W = 2*b-1 ∧ Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount W = 8*b := by
  (try dsimp only)
  let e :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelEquiv (J := J)
      (H := H) b
  let L :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannFrame b hb F
  let O :=
      Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J)
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle b U)
  let R :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabelWord b hb F G₁ G₂ G₃
  let Y := fun j => ((b : ℂ)⁻¹) • Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.leftDefectNeumann
    (Qatlib.Concepts.Execution.WorkspaceCP.compress F (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.familyBodyMatrix G₁ G₂ G₃ U j) F) b
  have h :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.sharedOriginal_encoding_cost b hb F hF G₁ G₂ G₃ h₁ h₂ h₃ U hU
  have hL : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry L := Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_isIsometry _)
    (Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_isIsometry _) hF)
  have hR : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit R := Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_wellFormed (Qatlib.Foundations.PureStateMath.BornBridge.relabelGate e)
    (fun _ hu => Qatlib.Concepts.BlockEncoding.EncodingCore.relabelGate_mem_unitary hu e) h.2.1
  have hO : O ∈ unitaryGroup _ ℂ := Qatlib.Concepts.BlockEncoding.LCU.select_unitary _
    (fun _ => Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.uniformNeumannOracle_unitary b U hU)
  have hblock : Qatlib.Concepts.Execution.WorkspaceCP.compress ((1 : Matrix J J ℂ) ⊗ₖ L) (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate O R)
      ((1 : Matrix J J ℂ) ⊗ₖ L) = Qatlib.Concepts.BlockEncoding.LCU.select Y :=
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.outerLabel_clean_block b hb F hF G₁ G₂ G₃ h₁ h₂ h₃ U hU
  have hc := Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.clean_word_lcu_encoding_cost L O R Y d j₀ hmass hL
    (hR.evaluate_unitary hO) hblock
  have hq : Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount R = 2*b-1 :=
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_counts _ _).1.trans h.2.2.2.1
  have hg : Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount R = 8*b-3 :=
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_counts _ _).2.trans h.2.2.2.2
  refine ⟨hO, hc.2.2.2 hR, hc.1, ?_, ?_⟩
  · exact hc.2.1.trans hq
  · have hh := hc.2.2.1
    rw [hg] at hh
    exact hh.trans (by omega)

end Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram
