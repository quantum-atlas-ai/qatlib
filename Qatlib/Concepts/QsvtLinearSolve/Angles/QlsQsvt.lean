/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtMain.ConventionBridge
import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT
import Qatlib.Concepts.QsvtCore.QsVtMain.CPPPhaseCompiler
import Qatlib.Concepts.QsvtCore.LinearSystems.FiniteInversePhaseProgram
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.ConventionBridgeConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.QsvtLinearSolve.AnglesCore

open Qatlib
open Matrix Polynomial

variable {H : Type} [Fintype H] [DecidableEq H]

def absorbedAngle (b : ℂ) (φ : ℝ) : ℝ := (b * anglePhase φ).arg

private theorem absorbed_product_isPhase (b : ℂ) (hb : IsPhase b) (φ : ℝ) :
    IsPhase (b * anglePhase φ) := by
  have hφ := anglePhase_isPhase φ
  unfold IsPhase at hb hφ ⊢
  rw [star_mul]
  calc star (anglePhase φ) * star b * (b * anglePhase φ)
      = (star b * b) * (star (anglePhase φ) * anglePhase φ) := by ring
    _ = 1 := by rw [hb, hφ]; simp

theorem absorbedAngle_phase (b : ℂ) (hb : IsPhase b) (φ : ℝ) :
    anglePhase (absorbedAngle b φ) = b * anglePhase φ :=
  anglePhase_arg_of_isPhase (absorbed_product_isPhase b hb φ)

theorem sourceDefWord_absorb_terminal_base (U P Q : Matrix H H ℂ)
    (hQ : IsOrthogonalProjector Q) (b : ℂ) (hb : IsPhase b) (φ : ℝ) (Φ : List ℝ) :
    sourceDefWord U P Q (absorbedAngle b φ :: Φ) =
      phaseRotation Q b * sourceDefWord U P Q (φ :: Φ) := by
  simp only [sourceDefWord, absorbedAngle_phase b hb φ, ← phaseRotation_mul hQ,
    Matrix.mul_assoc]

theorem sourcePhaseResponse_absorb (b : ℂ) (hb : IsPhase b) (φ : ℝ) (Φ : List ℝ) :
    sourcePhaseResponse (absorbedAngle b φ :: Φ) =
      C b * sourcePhaseResponse (φ :: Φ) := by
  simp only [sourcePhaseResponse, List.map_cons, absorbedAngle_phase b hb φ,
    responseP_cons, Polynomial.C_mul]
  ring

theorem sourceDefWord_absorb_range (U P Q : Matrix H H ℂ)
    (hQ : IsOrthogonalProjector Q) (b : ℂ) (hb : IsPhase b) (φ : ℝ) (Φ : List ℝ)
    {K : Type} (V : Matrix H K ℂ)
    (hV : Q * (sourceDefWord U P Q (φ :: Φ) * V) =
      sourceDefWord U P Q (φ :: Φ) * V) :
    sourceDefWord U P Q (absorbedAngle b φ :: Φ) * V =
      b • (sourceDefWord U P Q (φ :: Φ) * V) := by
  rw [sourceDefWord_absorb_terminal_base U P Q hQ b hb φ Φ, Matrix.mul_assoc,
    phaseRotation_mul_of_fixed hV b]

theorem sourceDefWord_absorb_kernel (U P Q : Matrix H H ℂ)
    (hQ : IsOrthogonalProjector Q) (b : ℂ) (hb : IsPhase b) (φ : ℝ) (Φ : List ℝ)
    {K : Type} (V : Matrix H K ℂ)
    (hV : Q * (sourceDefWord U P Q (φ :: Φ) * V) = 0) :
    sourceDefWord U P Q (absorbedAngle b φ :: Φ) * V =
      star b • (sourceDefWord U P Q (φ :: Φ) * V) := by
  rw [sourceDefWord_absorb_terminal_base U P Q hQ b hb φ Φ, Matrix.mul_assoc,
    phaseRotation_mul_of_zero hV b]

omit [Fintype H] in

theorem compileRealPartQSVT_absorb_counts (P Q : Matrix H H ℂ) (b z : ℂ)
    (zs : List ℂ) :
    adjointQueryCount (compileRealPartQSVT P Q 1 ((b * z) :: zs)) =
      adjointQueryCount (compileRealPartQSVT P Q b (z :: zs)) ∧
    adjointGateCount (compileRealPartQSVT P Q 1 ((b * z) :: zs)) =
      adjointGateCount (compileRealPartQSVT P Q b (z :: zs)) := by
  have h1 := counts_compileRealPartQSVT P Q 1 ((b * z) :: zs)
  have h2 := counts_compileRealPartQSVT P Q b (z :: zs)
  simp only [List.length_cons] at h1 h2
  exact ⟨h1.1.trans h2.1.symm, h1.2.trans h2.2.symm⟩

theorem fullComputedPhaseWord_absorb_counts (P Q : Matrix H H ℂ)
    (d₁ d₂ : PhaseData)
    (h₁ : WellFormedAdjointCircuit (computedPhaseWord P Q d₁))
    (h₂ : WellFormedAdjointCircuit (computedPhaseWord P Q d₂))
    (hlen : d₁.phases.length = d₂.phases.length) :
    adjointQueryCount (fullComputedPhaseWord P Q d₁) =
      adjointQueryCount (fullComputedPhaseWord P Q d₂) ∧
    adjointGateCount (fullComputedPhaseWord P Q d₁) =
      adjointGateCount (fullComputedPhaseWord P Q d₂) := by
  obtain ⟨_, e₁, f₁⟩ := fullComputedPhaseWord_wellFormed_counts P Q d₁ h₁
  obtain ⟨_, e₂, f₂⟩ := fullComputedPhaseWord_wellFormed_counts P Q d₂ h₂
  omega

theorem cppCompile_absorb_counts {J : Type} (f g : J → ℝ) (fs : List (J → ℝ)) :
    cppCounts (cppCompile (g :: fs)) = cppCounts (cppCompile (f :: fs)) := by
  simp only [cppCompile_counts, List.length_cons]

theorem frontier1 (U P Q : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q)
    (b : ℂ) (hb : IsPhase b) (φ : ℝ) (Φ : List ℝ) :
    ∃ θ : ℝ,
      anglePhase θ = b * anglePhase φ ∧
      sourceDefWord U P Q (θ :: Φ) = phaseRotation Q b * sourceDefWord U P Q (φ :: Φ) ∧
      (θ :: Φ).length = (φ :: Φ).length ∧
      sourcePhaseResponse (θ :: Φ) = C b * sourcePhaseResponse (φ :: Φ) :=
  ⟨absorbedAngle b φ, absorbedAngle_phase b hb φ,
    sourceDefWord_absorb_terminal_base U P Q hQ b hb φ Φ, rfl,
    sourcePhaseResponse_absorb b hb φ Φ⟩

section ConsumerChannel

open scoped Matrix.Norms.L2Operator

variable {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

private theorem isPhase_norm_one {b : ℂ} (hb : IsPhase b) : ‖b‖ = 1 := by
  have h2 : ‖b‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, IsPhase.normSq hb]
  have hnn : (0 : ℝ) ≤ ‖b‖ := norm_nonneg b
  have h4 : (‖b‖ - 1) * (‖b‖ + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h4 with h | h
  · linarith
  · linarith

private theorem toEuclidean_fromVec_smul {K : Type} [Fintype K] (c : ℂ) (v : QState K) :
    toEuclidean_fromVec (c • v) = c • toEuclidean_fromVec v := by
  ext i
  simp [toEuclidean_fromVec_apply]

private theorem toEuclidean_fromVec_sub {K : Type} [Fintype K] (u v : QState K) :
    toEuclidean_fromVec (u - v) = toEuclidean_fromVec u - toEuclidean_fromVec v := by
  ext i
  simp [toEuclidean_fromVec_apply]

private theorem toEuclidean_fromVec_rotated_diff {K : Type} [Fintype K] (b c d : ℂ)
    (u v : QState K) :
    toEuclidean_fromVec (c • (b • u) - d • (b • v)) =
      b • toEuclidean_fromVec (c • u - d • v) := by
  simp only [toEuclidean_fromVec_sub, toEuclidean_fromVec_smul]
  rw [smul_smul, smul_smul, mul_comm c b, mul_comm d b, ← smul_smul, ← smul_smul, ← smul_sub]

private theorem conjTranspose_mul_phaseRotation (L : Matrix H O ℂ) (hL : IsIsometry L)
    (b : ℂ) : Lᴴ * phaseRotation (rangeProjector L) b = b • Lᴴ := by
  have hL' : Lᴴ * L = 1 := hL
  have h1 : Lᴴ * rangeProjector L = Lᴴ := by
    unfold rangeProjector
    rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
  simp only [phaseRotation, Matrix.mul_add, Matrix.mul_smul, h1, Matrix.mul_sub,
    Matrix.mul_one, sub_self, smul_zero, add_zero]

omit [DecidableEq O] in

private theorem oddSingularTransform_const_smul (A : Matrix O I ℂ) (f : ℝ → ℂ) (b : ℂ) :
    oddSingularTransform A (fun x => b * f x) = b • oddSingularTransform A f := by
  have hd : Matrix.diagonal (fun i : Fin (Fintype.card I) => b * f (matrixSingularValues A i))
      = b • Matrix.diagonal (fun i : Fin (Fintype.card I) => f (matrixSingularValues A i)) := by
    rw [← Matrix.diagonal_smul]
    rfl
  unfold oddSingularTransform
  rw [hd, Matrix.mul_smul, Matrix.smul_mul]

theorem absorbed_channel_rotation (U : Matrix H H ℂ) (L : Matrix H O ℂ)
    (hL : IsIsometry L) (R : Matrix H I ℂ) (A : Matrix O I ℂ)
    (b : ℂ) (hb : IsPhase b) (φ : ℝ) (Φ : List ℝ) (ψ : QState I) :
    compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) 1
        ((absorbedAngle b φ :: Φ).map anglePhase)) R *ᵥ ψ =
      b • (compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) 1
        ((φ :: Φ).map anglePhase)) R *ᵥ ψ) ∧
    oddSingularTransform A
        (fun x : ℝ => (sourcePhaseResponse (absorbedAngle b φ :: Φ)).eval (x : ℂ)) *ᵥ ψ =
      b • (oddSingularTransform A
        (fun x : ℝ => (sourcePhaseResponse (φ :: Φ)).eval (x : ℂ)) *ᵥ ψ) ∧
    ‖toEuclidean_fromVec (oddSingularTransform A
        (fun x : ℝ => (sourcePhaseResponse (absorbedAngle b φ :: Φ)).eval (x : ℂ)) *ᵥ ψ)‖ =
      ‖toEuclidean_fromVec (oddSingularTransform A
        (fun x : ℝ => (sourcePhaseResponse (φ :: Φ)).eval (x : ℂ)) *ᵥ ψ)‖ := by
  have hy : compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) 1
        ((absorbedAngle b φ :: Φ).map anglePhase)) R *ᵥ ψ =
      b • (compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) 1
        ((φ :: Φ).map anglePhase)) R *ᵥ ψ) := by
    have hw := sourceDefWord_absorb_terminal_base U (rangeProjector R) (rangeProjector L)
      (rangeProjector_isOrthogonalProjector hL) b hb φ Φ
    simp only [sourceDefWord_eq_phasedAlternating, List.map_cons] at hw
    unfold compress
    simp only [List.map_cons]
    rw [hw, ← Matrix.mul_assoc, conjTranspose_mul_phaseRotation L hL b,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mulVec]
  have hv : oddSingularTransform A
      (fun x : ℝ => (sourcePhaseResponse (absorbedAngle b φ :: Φ)).eval (x : ℂ)) *ᵥ ψ =
    b • (oddSingularTransform A
      (fun x : ℝ => (sourcePhaseResponse (φ :: Φ)).eval (x : ℂ)) *ᵥ ψ) := by
    have hfun : (fun x : ℝ => (sourcePhaseResponse (absorbedAngle b φ :: Φ)).eval (x : ℂ)) =
        fun x : ℝ => b * (sourcePhaseResponse (φ :: Φ)).eval (x : ℂ) := by
      funext x
      rw [sourcePhaseResponse_absorb b hb φ Φ, Polynomial.eval_mul, Polynomial.eval_C]
    rw [hfun, oddSingularTransform_const_smul, Matrix.smul_mulVec]
  exact ⟨hy, hv, by
    rw [hv, toEuclidean_fromVec_smul, norm_smul, isPhase_norm_one hb, one_mul]⟩

private theorem channel_bound_transfer {K : Type} [Fintype K] {b : ℂ}
    (hb : IsPhase b) (yΘ yΨ vΘ vΨ : QState K) (η : ℝ)
    (hy : yΘ = b • yΨ) (hv : vΘ = b • vΨ)
    (hbound : η < ‖toEuclidean_fromVec vΨ‖ →
      (‖toEuclidean_fromVec vΨ‖ - η) ^ 2 ≤ ‖toEuclidean_fromVec yΨ‖ ^ 2 ∧
      ‖toEuclidean_fromVec (((‖toEuclidean_fromVec yΨ‖⁻¹ : ℝ) : ℂ) • yΨ -
        ((‖toEuclidean_fromVec vΨ‖⁻¹ : ℝ) : ℂ) • vΨ)‖ ≤
        2 * η / ‖toEuclidean_fromVec vΨ‖) :
    η < ‖toEuclidean_fromVec vΘ‖ →
      (‖toEuclidean_fromVec vΘ‖ - η) ^ 2 ≤ ‖toEuclidean_fromVec yΘ‖ ^ 2 ∧
      ‖toEuclidean_fromVec (((‖toEuclidean_fromVec yΘ‖⁻¹ : ℝ) : ℂ) • yΘ -
        ((‖toEuclidean_fromVec vΘ‖⁻¹ : ℝ) : ℂ) • vΘ)‖ ≤
        2 * η / ‖toEuclidean_fromVec vΘ‖ := by
  intro hη
  have hτ : ‖toEuclidean_fromVec vΘ‖ = ‖toEuclidean_fromVec vΨ‖ := by
    rw [hv, toEuclidean_fromVec_smul, norm_smul, isPhase_norm_one hb, one_mul]
  have hyτ : ‖toEuclidean_fromVec yΘ‖ = ‖toEuclidean_fromVec yΨ‖ := by
    rw [hy, toEuclidean_fromVec_smul, norm_smul, isPhase_norm_one hb, one_mul]
  rw [hτ] at hη
  obtain ⟨hm, hd⟩ := hbound hη
  refine ⟨?_, ?_⟩
  · rw [hτ, hyτ]
    exact hm
  · rw [hτ, hyτ, hy, hv, toEuclidean_fromVec_rotated_diff b _ _,
      norm_smul, isPhase_norm_one hb, one_mul]
    exact hd

set_option maxHeartbeats 800000 in

theorem absorbed_conditional_output_channel :
    ∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
      (α ε : ℝ) (p : Polynomial ℝ) (d : ℕ),
      BlockEncoding A U L R α ε → ‖(α⁻¹ : ℝ) • A‖ ≤ 1 → 0 < d → d % 2 = 1 →
      p.degree = (d : WithBot ℕ) → HasRealParity d p →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) →
      ∀ b : ℂ, IsPhase b →
      ∃ Ψ Θ : List ℝ,
        Ψ.length = d ∧ Θ.length = d ∧
        (∀ x : ℝ, ((sourcePhaseResponse Ψ).eval (x : ℂ)).re = p.eval x) ∧
        sourcePhaseResponse Θ = C b * sourcePhaseResponse Ψ ∧
        (phasedAlternating U (rangeProjector R) (rangeProjector L) 1 (Θ.map anglePhase) =
          phaseRotation (rangeProjector L) b *
            phasedAlternating U (rangeProjector R) (rangeProjector L) 1 (Ψ.map anglePhase)) ∧
        (cppCounts (cppCompile (sourceRealFamily Θ)) = (d, 2 * (d / 2), 2 * ((d + 1) / 2), d)) ∧
        (adjointQueryCount (compileQSVT (rangeProjector R) (rangeProjector L) 1
            (Θ.map anglePhase)) = d) ∧
        ∀ ψ : QState I, Normalized ψ →
          (compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) 1
              (Θ.map anglePhase)) R *ᵥ ψ =
            b • (compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) 1
              (Ψ.map anglePhase)) R *ᵥ ψ)) ∧
          (oddSingularTransform ((α⁻¹ : ℝ) • A)
              (fun x : ℝ => (sourcePhaseResponse Θ).eval (x : ℂ)) *ᵥ ψ =
            b • (oddSingularTransform ((α⁻¹ : ℝ) • A)
              (fun x : ℝ => (sourcePhaseResponse Ψ).eval (x : ℂ)) *ᵥ ψ)) ∧
          (4 * (d : ℝ) * Real.sqrt (ε / α) <
              ‖toEuclidean_fromVec (oddSingularTransform ((α⁻¹ : ℝ) • A)
                (fun x : ℝ => (sourcePhaseResponse Θ).eval (x : ℂ)) *ᵥ ψ)‖ →
            ((‖toEuclidean_fromVec (oddSingularTransform ((α⁻¹ : ℝ) • A)
                (fun x : ℝ => (sourcePhaseResponse Θ).eval (x : ℂ)) *ᵥ ψ)‖ -
              4 * (d : ℝ) * Real.sqrt (ε / α)) ^ 2 ≤
              ‖toEuclidean_fromVec (compress L (phasedAlternating U (rangeProjector R)
                (rangeProjector L) 1 (Θ.map anglePhase)) R *ᵥ ψ)‖ ^ 2 ∧
              ‖toEuclidean_fromVec
                  (((‖toEuclidean_fromVec (compress L (phasedAlternating U (rangeProjector R)
                    (rangeProjector L) 1 (Θ.map anglePhase)) R *ᵥ ψ)‖⁻¹ : ℝ) : ℂ) •
                    (compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) 1
                      (Θ.map anglePhase)) R *ᵥ ψ) -
                  ((‖toEuclidean_fromVec (oddSingularTransform ((α⁻¹ : ℝ) • A)
                    (fun x : ℝ => (sourcePhaseResponse Θ).eval (x : ℂ)) *ᵥ ψ)‖⁻¹ : ℝ) : ℂ) •
                    (oddSingularTransform ((α⁻¹ : ℝ) • A)
                      (fun x : ℝ => (sourcePhaseResponse Θ).eval (x : ℂ)) *ᵥ ψ))‖ ≤
                2 * (4 * (d : ℝ) * Real.sqrt (ε / α)) /
                  ‖toEuclidean_fromVec (oddSingularTransform ((α⁻¹ : ℝ) • A)
                    (fun x : ℝ => (sourcePhaseResponse Θ).eval (x : ℂ)) *ᵥ ψ)‖)) := by
  intro I O _ _ _ _ A U L R α ε p d h hA hd hodd hdeg hpar hbound b hb
  obtain ⟨Φ, hlen, hre, _hmin, hcounts, _hbe, hword⟩ :=
    source_convention_actual_word_consumer_spec I O A U L R α ε p d
      h hA hd hodd hdeg hpar hbound
  have hne : Φ ≠ [] := by
    intro hc
    rw [hc] at hlen
    simp at hlen
    omega
  obtain ⟨φ, Φ', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hLiso : IsIsometry L := h.left_isometry
  refine ⟨φ :: Φ', absorbedAngle b φ :: Φ', hlen, by
    simp only [List.length_cons] at hlen ⊢
    omega, hre,
    sourcePhaseResponse_absorb b hb φ Φ', ?_, ?_, ?_, ?_⟩
  · have hw := sourceDefWord_absorb_terminal_base U (rangeProjector R) (rangeProjector L)
      (rangeProjector_isOrthogonalProjector hLiso) b hb φ Φ'
    simpa only [sourceDefWord_eq_phasedAlternating, List.map_cons] using! hw
  · have hc := cppCompile_absorb_counts (J := Bool)
      (fun c : Bool => if c then -φ else φ)
      (fun c : Bool => if c then -(absorbedAngle b φ) else absorbedAngle b φ)
      (sourceRealFamily Φ')
    exact hc.trans hcounts
  · have hq := queryCount_compileQSVT (rangeProjector R) (rangeProjector L) 1
      ((absorbedAngle b φ :: Φ').map anglePhase)
    rw [List.length_map, List.length_cons] at hq
    simp only [List.length_cons] at hlen
    omega
  · intro ψ hψ
    obtain ⟨hy, hv, _hτ⟩ := absorbed_channel_rotation U L hLiso R ((α⁻¹ : ℝ) • A) b hb φ Φ' ψ
    obtain ⟨hb1, _hcppΘ, _hqcΘ⟩ := hword ψ hψ
    exact ⟨hy, hv, channel_bound_transfer hb _ _ _ _
      (4 * (d : ℝ) * Real.sqrt (ε / α)) hy hv hb1⟩

end ConsumerChannel

end Qatlib.Concepts.QsvtLinearSolve.AnglesCore
