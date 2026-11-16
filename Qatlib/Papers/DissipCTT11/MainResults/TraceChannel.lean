/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
public import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
public import QuantumInfo.Channels.Dual

@[expose] public section


/-! # Actual induced trace norm of CPTP channels

Lemma 3 of arXiv:1105.3986v4 concerns the induced Schatten-one norm,
not the Euclidean operator norm of a vectorized superoperator. Duality
against unitary matrices proves contraction on every complex input,
without assuming the desired contraction as a field of the channel.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Papers.DissipCTT11.MainResults.TraceChannel
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open scoped Matrix.Norms.L2Operator MatrixOrder

/-- A CPTP map contracts the actual trace norm on all complex operators. -/
theorem traceContract {D E : ℕ} [NeZero E]
    (T : QuantumChannel D E) (A : Operator D) :
    Matrix.traceNorm (T.map A) ≤ Matrix.traceNorm A := by
  classical
  obtain ⟨U,hU⟩ := (Matrix.traceNorm_eq_max_re_tr_U (T.map A)).left
  have hcp := ((completelyPositive_iff_physlib T.map).mp T.completelyPositive).dual
  have hun : (MatrixMap.dual T.map) 1 = 1 := MatrixMap.dual_Unital T.tracePreserving
  have hnorm : ‖(MatrixMap.dual T.map) U.val‖ ≤ 1 := by
    have h := MatrixMap.cp_subunital_opNorm_le_one hcp (le_of_eq hun) U.val
    have hu : U.val ∈ unitary (Matrix (Fin E) (Fin E) ℂ) := by
      constructor
      · ext i j
        have hij := congrArg (fun M : Operator E => M i j) U.property.1
        by_cases h : i = j <;> simpa [Matrix.one_apply,h] using hij
      · ext i j
        have hij := congrArg (fun M : Operator E => M i j) U.property.2
        by_cases h : i = j <;> simpa [Matrix.one_apply,h] using hij
    exact h.trans_eq (CStarRing.norm_of_mem_unitary hu)
  calc
    Matrix.traceNorm (T.map A) = ((U.val * T.map A).trace).re := hU.symm
    _ = ((A * (MatrixMap.dual T.map) U.val).trace).re := by
      rw [Matrix.trace_mul_comm,MatrixMap.Dual.trace_eq]
    _ ≤ ‖(A * (MatrixMap.dual T.map) U.val).trace‖ := Complex.re_le_norm _
    _ ≤ Matrix.traceNorm (A * (MatrixMap.dual T.map) U.val) := Matrix.abs_trace_le_traceNorm _
    _ ≤ Matrix.traceNorm A * ‖(MatrixMap.dual T.map) U.val‖ :=
      Matrix.traceNorm_mul_le_traceNorm_opNorm _ _
    _ ≤ Matrix.traceNorm A * 1 :=
      mul_le_mul_of_nonneg_left hnorm (Matrix.traceNorm_nonneg _)
    _ = Matrix.traceNorm A := mul_one _

/-- The Qatlib Schatten-one representation obeys the same actual contraction. -/
theorem schattenBound {D E : ℕ} [NeZero E]
    (T : QuantumChannel D E) (A : Operator D) : SchattenOne (T.map A) ≤ SchattenOne A := by
  simpa only [schattenOne_eq_physlib_traceNorm] using traceContract T A

/-- Every genuine density operator has Schatten-one norm one. -/
theorem densityOne {D : ℕ} {ρ : Operator D} (hρ : IsDensityOperator ρ) :
    SchattenOne ρ = 1 := by
  rw [schattenOne_eq_physlib_traceNorm]
  have h := congrArg Complex.re (Matrix.PosSemidef.traceNorm_eq_trace hρ.1)
  simpa [hρ.2] using h

/-- Lemma 3 in the actual induced trace norm, with nonempty physical spaces explicit. -/
theorem inducedOne {D E : ℕ} [NeZero D] [NeZero E] (T : QuantumChannel D E) :
    InducedTraceNorm T.map = 1 := by
  classical
  let ρ : Operator D := Reflection.outerProduct (Ket (0 : Fin D))
  have hρ : IsDensityOperator ρ := outerProduct_density (normalized_ket _)
  have hin : SchattenOne ρ = 1 := densityOne hρ
  have hout : SchattenOne (T.map ρ) = 1 := densityOne (T.preservesDensity hρ)
  have hmem : (1 : ℝ) ∈ {r : ℝ | ∃ A : Operator D,
      SchattenOne A = 1 ∧ r = SchattenOne (T.map A)} := ⟨ρ,hin,hout.symm⟩
  have hle : ∀ r ∈ {r : ℝ | ∃ A : Operator D,
      SchattenOne A = 1 ∧ r = SchattenOne (T.map A)}, r ≤ 1 := by
    rintro r ⟨A,hA,rfl⟩
    exact (schattenBound T A).trans_eq hA
  exact le_antisymm (csSup_le ⟨1,hmem⟩ hle) (le_csSup ⟨1,hle⟩ hmem)

/-- The actual operational Schatten-one distance is nonincreasing under a channel. -/
theorem distanceBound {D E : ℕ} [NeZero E]
    (T : QuantumChannel D E) (ρ σ : Operator D) :
    SchattenOne (T.map ρ - T.map σ) ≤ SchattenOne (ρ - σ) := by
  simpa only [map_sub] using schattenBound T (ρ - σ)

/-- A concrete positive-dimensional channel realizes the norm-one statement. -/
theorem identityCase : InducedTraceNorm (QuantumChannel.id 1).map = 1 :=
  inducedOne (QuantumChannel.id 1)

end Qatlib.Papers.DissipCTT11.MainResults.TraceChannel
