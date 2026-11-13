/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.VariableTimeAmplificationDefs
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.OptimalCoefficientBlockEncodingStat
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.BlockPrecondCorrectedSubgoalStat
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.OptimalCoefficientBlockEncodingLows
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.BlockPrecondCorrectedSubgoalLows

/-!
# Algebra for variable-time applications

This module supplies state normalization, pseudoinverse, and preconditioning identities used in
variable-time applications. It also constructs the zero-time evolution and zero-polynomial
endpoint cases, using a slot permutation with zero projected corner.

The variable-time amplification setting is described in [Ambainis2012].

## Main statements

* `clause115_preconditioned_algebra`: norm, direction, and amplitude bounds after state scaling.
* `clause116_zero_time`: preparation guarantee for zero evolution time.
* `clause118_zero_polynomial`: encoding guarantee for the zero polynomial.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false

set_option maxHeartbeats 800000

noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

open Matrix Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The vector norm `normVec` equals the norm of the corresponding `stateVector`. -/
theorem normVec_eq_stateVector_norm {I : Type} [Fintype I] (ψ : QState I) :
    normVec ψ = ‖stateVector ψ‖ := rfl

/-- Passing from a state to its state vector commutes with complex scalar multiplication. -/
theorem stateVector_smul {I : Type} (c : ℂ) (ψ : QState I) :
    stateVector (c • ψ) = c • stateVector ψ := rfl

/-- Scaling a state by a real scalar scales its norm by the scalar's absolute value. -/
theorem normVec_smul_real {I : Type} [Fintype I] (c : ℝ) (ψ : QState I) :
    normVec ((c : ℂ) • ψ) = |c| * normVec ψ := by
  rw [normVec_eq_stateVector_norm, stateVector_smul, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, normVec_eq_stateVector_norm]

/-- Normalizing a state is unchanged by multiplication by a positive real scalar. -/
theorem normState_smul_of_pos {I : Type} [Fintype I] {c : ℝ} (hc : 0 < c) (ψ : QState I) :
    normState ((c : ℂ) • ψ) = normState ψ := by
  rcases eq_or_ne ψ 0 with hψ | hψ
  · subst hψ
    rw [smul_zero]
  have hnv : 0 < normVec ψ := by
    rw [normVec_eq_stateVector_norm]
    exact norm_pos_iff.mpr fun h => hψ ((stateVector_eq_zero_iff ψ).mp h)
  have hsmul : normVec ((c : ℂ) • ψ) = c * normVec ψ := by
    rw [normVec_smul_real, abs_of_pos hc]
  have hmulc : ((c * normVec ψ : ℝ) : ℂ) = (c : ℂ) * ((normVec ψ : ℝ) : ℂ) :=
    Complex.ofReal_mul _ _
  have hcoef : (((c * normVec ψ : ℝ) : ℂ))⁻¹ * (c : ℂ) = ((normVec ψ : ℝ) : ℂ)⁻¹ := by
    have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
    rw [hmulc, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  unfold normState
  rw [hsmul, smul_smul, hcoef]

/-- Multiplying the pseudoinverse by the inverse state-scaling operator splits into the scaled
rank-one part and its complementary part. -/
theorem pseudoinverse_scalingInverse_decompose {I O : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (b : QState O) (s : ℝ) :
    matrixPseudoinverse A * stateScalingInverse s b =
      ((s : ℝ)⁻¹ : ℂ) • (matrixPseudoinverse A * outerProduct b) +
        matrixPseudoinverse A * ((1 : Matrix O O ℂ) - outerProduct b) := by
  have he : matrixPseudoinverse A * stateScalingInverse s b =
      ((s : ℝ)⁻¹ : ℂ) • (matrixPseudoinverse A * outerProduct b) +
        matrixPseudoinverse A * (1 - outerProduct b) := by
    simp only [stateScalingInverse, one_smul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
    module
  exact he

/-- For normalized `b`, the scaled rank-one pseudoinverse component times the conjugate
transpose of its complementary component is zero. -/
theorem preconditioned_cross_term_zero {I O : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (b : QState O) (s : ℝ)
    (hb : Normalized b) :
    (((s : ℝ)⁻¹ : ℂ) • (matrixPseudoinverse A * outerProduct b)) *
        (matrixPseudoinverse A * ((1 : Matrix O O ℂ) - outerProduct b))ᴴ = 0 := by
  have hp : outerProduct b * outerProduct b = outerProduct b :=
    (isOrthogonalProjector_outerProduct hb).1
  have hcross : outerProduct b * ((1 : Matrix O O ℂ) - outerProduct b) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hp]
    abel
  have hp2 : (outerProduct b)ᴴ = outerProduct b :=
    (isOrthogonalProjector_outerProduct hb).2
  have hYadj : (matrixPseudoinverse A * ((1 : Matrix O O ℂ) - outerProduct b))ᴴ =
      ((1 : Matrix O O ℂ) - outerProduct b) * (matrixPseudoinverse A)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hp2]
  have hmid : (matrixPseudoinverse A * outerProduct b) *
      (((1 : Matrix O O ℂ) - outerProduct b) * (matrixPseudoinverse A)ᴴ) = 0 := by
    have hreg : outerProduct b * (((1 : Matrix O O ℂ) - outerProduct b) *
          (matrixPseudoinverse A)ᴴ)
        = (outerProduct b * ((1 : Matrix O O ℂ) - outerProduct b)) *
          (matrixPseudoinverse A)ᴴ :=
      (Matrix.mul_assoc _ _ _).symm
    calc
      (matrixPseudoinverse A * outerProduct b) *
          (((1 : Matrix O O ℂ) - outerProduct b) * (matrixPseudoinverse A)ᴴ)
          = matrixPseudoinverse A *
            (outerProduct b * (((1 : Matrix O O ℂ) - outerProduct b) *
              (matrixPseudoinverse A)ᴴ)) := Matrix.mul_assoc _ _ _
      _ = matrixPseudoinverse A *
            ((outerProduct b * ((1 : Matrix O O ℂ) - outerProduct b)) *
              (matrixPseudoinverse A)ᴴ) := by rw [hreg]
      _ = matrixPseudoinverse A *
            ((0 : Matrix O O ℂ) * (matrixPseudoinverse A)ᴴ) := by rw [hcross]
      _ = 0 := by rw [Matrix.zero_mul, Matrix.mul_zero]
  rw [hYadj, Matrix.smul_mul, hmid, smul_zero]

/-- The operator norm of `M * Mᴴ` equals the square of the operator norm of `M`. -/
theorem norm_self_mul_conjTranspose {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M : Matrix m n ℂ) :
    ‖M * Mᴴ‖ = ‖M‖ * ‖M‖ := by
  have h := l2_opNorm_conjTranspose_mul_self (Mᴴ)
  rw [Matrix.conjTranspose_conjTranspose, l2_opNorm_conjTranspose] at h
  exact h

/-- The optimal coefficient block-encoding and corrected block-preconditioning subgoals both
hold. -/
theorem clause115_consumed_slices :
    OptimalCoefficientBlockEncodingSubgoal ∧ BlockPreconditioningCorrectedSubgoal :=
  ⟨optimalCoefficientBlockEncodingSubgoal, blockPreconditioningCorrectedSubgoal⟩

/-- Under consistency and the stated norm window, state scaling bounds the new pseudoinverse
norm, preserves the normalized solution, and gives a lower bound `1 / (c ^ 4 + 1)` on the
squared scaled solution norm. -/
theorem clause115_preconditioned_algebra {I O : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (b : QState O) (αInv t c : ℝ)
    (hb : Normalized b) (hαInv : 0 < αInv) (hc : 1 < c) (ht : 0 < t)
    (hconsistent : ∃ z : QState I, A *ᵥ z = b)
    (hpinv : ‖matrixPseudoinverse A‖ ≤ αInv)
    (hwindow : t / c < normVec (matrixPseudoinverse A *ᵥ b) ∧
      normVec (matrixPseudoinverse A *ᵥ b) < c * t) :
    (‖matrixPseudoinverse (stateScaling (t / (c * αInv)) b * A)‖ ≤
        Real.sqrt (c ^ 4 + 1) * αInv) ∧
      (normState (matrixPseudoinverse (stateScaling (t / (c * αInv)) b * A) *ᵥ b) =
        normState (matrixPseudoinverse A *ᵥ b)) ∧
      (1 / (c ^ 4 + 1) ≤
        (normVec (matrixPseudoinverse (stateScaling (t / (c * αInv)) b * A) *ᵥ b) /
          (Real.sqrt (c ^ 4 + 1) * αInv)) ^ 2) := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hs : 0 < t / (c * αInv) := by positivity
  have hsne : t / (c * αInv) ≠ 0 := ne_of_gt hs
  have hsinv : 0 < (t / (c * αInv))⁻¹ := inv_pos.mpr hs
  have hb1 : ‖stateVector b‖ = 1 := (normalized_iff_stateVector_norm b).mp hb
  have hle : ‖stateVector (matrixPseudoinverse A *ᵥ b)‖ ≤ αInv := by
    have h := stateVector_mulVec_norm_le (matrixPseudoinverse A) b
    rw [hb1, mul_one] at h
    exact le_trans h hpinv
  have hnle : normVec (matrixPseudoinverse A *ᵥ b) ≤ αInv := by
    rw [normVec_eq_stateVector_norm]
    exact hle
  have hposSp : 0 < c * αInv := mul_pos hc0 hαInv
  have hdir := stateScaling_pseudoinverse_direction_of_consistent A
    (t / (c * αInv)) b hsne hb hconsistent
  have hcons := stateScaling_pseudoinverse_of_consistent A
    (t / (c * αInv)) b hsne hb hconsistent
  refine ⟨?_, ?_, ?_⟩
  · have hdecomp := pseudoinverse_scalingInverse_decompose A b (t / (c * αInv))
    set X : Matrix I O ℂ := (((t / (c * αInv)) : ℝ)⁻¹ : ℂ) •
        (matrixPseudoinverse A * outerProduct b) with hX
    set Y : Matrix I O ℂ := matrixPseudoinverse A *
        ((1 : Matrix O O ℂ) - outerProduct b) with hY
    have hsum : matrixPseudoinverse A * stateScalingInverse (t / (c * αInv)) b = X + Y := by
      rw [hX, hY]
      exact hdecomp
    have hcross : X * Yᴴ = 0 := by
      rw [hX, hY]
      exact preconditioned_cross_term_zero A b (t / (c * αInv)) hb
    have hcross' : Y * Xᴴ = 0 := by
      have h := congrArg Matrix.conjTranspose hcross
      rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero,
        Matrix.conjTranspose_conjTranspose] at h
    have hnormX : ‖X‖ = (t / (c * αInv))⁻¹ * normVec (matrixPseudoinverse A *ᵥ b) := by
      rw [hX, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
        solved_outerProduct_norm (matrixPseudoinverse A) b hb, ← normVec_eq_stateVector_norm]
    have hsqXpos : 0 < c ^ 2 * αInv := by positivity
    have hnormX_le : ‖X‖ ≤ c ^ 2 * αInv := by
      rw [hnormX]
      have h : (t / (c * αInv))⁻¹ * normVec (matrixPseudoinverse A *ᵥ b) <
          (t / (c * αInv))⁻¹ * (c * t) :=
        mul_lt_mul_of_pos_left hwindow.2 hsinv
      have heq : (t / (c * αInv))⁻¹ * (c * t) = c ^ 2 * αInv := by
        rw [inv_div]
        field_simp
      rw [← heq]
      exact le_of_lt h
    have hnormY : ‖Y‖ ≤ αInv := by
      rw [hY]
      calc
        _ ≤ ‖matrixPseudoinverse A‖ * ‖((1 : Matrix O O ℂ) - outerProduct b)‖ :=
          Matrix.l2_opNorm_mul _ _
        _ ≤ αInv * 1 :=
          mul_le_mul hpinv (state_complement_norm_le_one b hb) (norm_nonneg _) (le_of_lt hαInv)
        _ = αInv := by ring
    have hprod : (X + Y) * (X + Y)ᴴ = X * Xᴴ + Y * Yᴴ := by
      simp only [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul,
        hcross, hcross', _root_.add_zero, _root_.zero_add]
    have hsq : ‖(X + Y) * (X + Y)ᴴ‖ = ‖X + Y‖ * ‖X + Y‖ :=
      norm_self_mul_conjTranspose (X + Y)
    have hXX : ‖X * Xᴴ‖ = ‖X‖ * ‖X‖ := norm_self_mul_conjTranspose X
    have hYY : ‖Y * Yᴴ‖ = ‖Y‖ * ‖Y‖ := norm_self_mul_conjTranspose Y
    have hle2 : ‖X + Y‖ * ‖X + Y‖ ≤ αInv ^ 2 * (c ^ 4 + 1) := by
      rw [← hsq, hprod]
      calc
        _ ≤ ‖X * Xᴴ‖ + ‖Y * Yᴴ‖ := norm_add_le _ _
        _ = ‖X‖ * ‖X‖ + ‖Y‖ * ‖Y‖ := by rw [hXX, hYY]
        _ ≤ (c ^ 2 * αInv) * (c ^ 2 * αInv) + αInv * αInv :=
          add_le_add (mul_le_mul hnormX_le hnormX_le (norm_nonneg _) (le_of_lt hsqXpos))
            (mul_le_mul hnormY hnormY (norm_nonneg _) (le_of_lt hαInv))
        _ = αInv ^ 2 * (c ^ 4 + 1) := by ring
    have hfinal : ‖X + Y‖ ≤ Real.sqrt (αInv ^ 2 * (c ^ 4 + 1)) := by
      have h := Real.sqrt_le_sqrt hle2
      rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
      exact h
    have hsqrt : Real.sqrt (αInv ^ 2 * (c ^ 4 + 1)) = Real.sqrt (c ^ 4 + 1) * αInv := by
      rw [Real.sqrt_mul (sq_nonneg αInv), Real.sqrt_sq_eq_abs, abs_of_pos hαInv]
      ring
    rw [hcons, hsum, ← hsqrt]
    exact hfinal
  · rw [hdir, ← Complex.ofReal_inv]
    exact normState_smul_of_pos hsinv (matrixPseudoinverse A *ᵥ b)
  · rw [hdir, ← Complex.ofReal_inv, normVec_smul_real, abs_of_pos hsinv]
    have hnormpos : 0 < normVec (matrixPseudoinverse A *ᵥ b) :=
      lt_of_lt_of_le (by positivity : (0 : ℝ) < t / c) (le_of_lt hwindow.1)
    have hgt : αInv <
        (t / (c * αInv))⁻¹ * normVec (matrixPseudoinverse A *ᵥ b) := by
      have hkey : (t / (c * αInv))⁻¹ * (t / c) = αInv := by
        rw [inv_div]
        field_simp
      calc
        αInv = (t / (c * αInv))⁻¹ * (t / c) := hkey.symm
        _ < (t / (c * αInv))⁻¹ * normVec (matrixPseudoinverse A *ᵥ b) :=
          mul_lt_mul_of_pos_left hwindow.1 hsinv
    have hden : 0 < Real.sqrt (c ^ 4 + 1) * αInv := by positivity
    have hle3 : αInv / (Real.sqrt (c ^ 4 + 1) * αInv) ≤
        ((t / (c * αInv))⁻¹ * normVec (matrixPseudoinverse A *ᵥ b)) /
          (Real.sqrt (c ^ 4 + 1) * αInv) :=
      div_le_div_of_nonneg_right (le_of_lt hgt) (le_of_lt hden)
    have hsqr : (1 / Real.sqrt (c ^ 4 + 1)) ^ 2 = 1 / (c ^ 4 + 1) := by
      rw [div_pow, one_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ c ^ 4 + 1)]
    have hcancel : αInv / (Real.sqrt (c ^ 4 + 1) * αInv) = 1 / Real.sqrt (c ^ 4 + 1) := by
      field_simp
    have hsqle : (1 / Real.sqrt (c ^ 4 + 1)) ^ 2 ≤
        (((t / (c * αInv))⁻¹ * normVec (matrixPseudoinverse A *ᵥ b)) /
          (Real.sqrt (c ^ 4 + 1) * αInv)) ^ 2 := by
      rw [← hcancel]
      exact pow_le_pow_left₀ (by positivity) hle3 2
    rw [← hsqr]
    exact hsqle

/-- Running the one-stage word with the paired oracles places `UB *ᵥ ω` in the unique flag slot. -/
theorem run_stageWord_one {H : Type} [Fintype H] [DecidableEq H]
    (UA UB : Matrix H H ℂ) (ω : QState H) (hr : 0 < 1) :
    run hr (pairOracles UA UB) (stageWord 1) ω
      = fun p => if p.2 = (⟨0, hr⟩ : Fin 1) then (UB *ᵥ ω) p.1 else 0 := by
  have hw : wordMatrix (pairOracles UA UB) (stageWord 1) = controlled UB Finset.univ := by
    simp [wordMatrix, stageWord, pairOracles]
  funext p
  have hp : p.2 = (⟨0, hr⟩ : Fin 1) := Subsingleton.elim _ _
  by_cases hpk : p.2 = (⟨0, hr⟩ : Fin 1)
  · rw [if_pos hpk]
    show (wordMatrix (pairOracles UA UB) (stageWord 1) *ᵥ clean 1 hr ω) p = _
    rw [hw]
    show (∑ q : H × Fin 1, controlled UB Finset.univ p q * clean 1 hr ω q) = _
    have hsum : (∑ q : H × Fin 1, controlled UB Finset.univ p q * clean 1 hr ω q)
        = ∑ h : H, (UB p.1 h) * (ω h) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.sum_eq_single ⟨0, hr⟩]
      · show controlled UB Finset.univ p (h, ⟨0, hr⟩) * clean 1 hr ω (h, ⟨0, hr⟩) = _
        simp only [controlled, clean, Finset.mem_univ, if_true]
        rw [hpk]
        simp
      · intro k _ hk
        show controlled UB Finset.univ p (h, k) * clean 1 hr ω (h, k) = _
        simp only [controlled, clean, Finset.mem_univ, if_true]
        rw [if_neg hk, mul_zero]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [hsum]
    rfl
  · exact absurd hp hpk

/-- At zero evolution time, there is a legal preparation word with the stated state guarantee
and oracle budgets, making no calls to the matrix oracle. -/
theorem clause116_zero_time : ∃ K : ℝ, 0 < K ∧
    ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      (L : Matrix H I ℂ) (αA t αexp αbmax αb ε : ℝ),
      0 < αA → 0 ≤ t → 0 < αexp → 0 < αbmax → 0 < αb → 0 < ε → ε < 1 / 4 →
      t = 0 →
      ∃ (r : ℕ) (hr : 0 < r) (C : Word H r) (T : Finset (Fin r)),
        legal 2 C ∧
        ∀ (A : Matrix I I ℂ) (UA UB : Matrix H H ℂ) (ω : QState H) (ψ : QState I),
          prepareAccess A UA UB L ω ψ αA →
          (∀ τ : ℝ, 0 ≤ τ → τ ≤ t → ‖NormedSpace.exp ((τ : ℂ) • A)‖ ≤ αexp) →
          (∀ τ : ℝ, 0 ≤ τ → τ ≤ t → normVec (expAction A τ ψ) ≤ αbmax) →
          (αb ≤ normVec (expAction A t ψ)) →
          stateGuarantee L T (run hr (pairOracles UA UB) C ω)
            (normState (expAction A t ψ)) ε ∧
          (calls C 1 : ℝ) ≤ K * odeBPrice αexp αb ∧
          (calls C 0 : ℝ) ≤ K * odeAPrice αA t αexp αbmax αb ε ∧
          (t = 0 → calls C 0 = 0) := by
  refine ⟨1, one_pos, ?_⟩
  intro H I _hF _hD _hFI _hDI L αA t αexp αbmax αb ε _hαA _ht hαexp _hbmax hαb hε _hε1 ht
  subst ht
  have hr1 : (0 : ℕ) < 1 := by norm_num
  have hlegal : legal 2 (stageWord (H := H) 1) := by
    intro s hs
    simp only [stageWord, List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    show (1 : ℕ) < 2
    norm_num
  have hc0 : calls (stageWord (H := H) 1) 0 = 0 := by simp [calls, stageWord]
  have hc1 : calls (stageWord (H := H) 1) 1 = 1 := by simp [calls, stageWord]
  refine ⟨1, hr1, stageWord 1, {⟨0, hr1⟩}, hlegal, ?_⟩
  · intro A UA UB ω ψ hprep hexp hbmax hb
    obtain ⟨_hαA', _hA, henc, hub, hubω, hψ⟩ := hprep
    have hL : IsIsometry L := henc.left_isometry
    have hLI : Lᴴ * L = 1 := hL
    have hrun : run hr1 (pairOracles UA UB) (stageWord 1) ω
        = fun p => if p.2 = (⟨0, hr1⟩ : Fin 1) then (UB *ᵥ ω) p.1 else 0 :=
      run_stageWord_one UA UB ω hr1
    have hslot : ∀ h : H, run hr1 (pairOracles UA UB) (stageWord 1) ω (h, ⟨0, hr1⟩) = (UB *ᵥ ω) h := by
      intro h
      rw [hrun]
      simp
    have hout : outputBranch L (run hr1 (pairOracles UA UB) (stageWord 1) ω) ⟨0, hr1⟩ = ψ := by
      show Lᴴ *ᵥ (fun h => run hr1 (pairOracles UA UB) (stageWord 1) ω (h, ⟨0, hr1⟩)) = _
      simp only [hslot]
      show Lᴴ *ᵥ (UB *ᵥ ω) = ψ
      rw [hubω, Matrix.mulVec_mulVec, hLI, Matrix.one_mulVec]
    have hnorm : normVec ψ = 1 := by
      rw [normVec_eq_stateVector_norm]
      exact (normalized_iff_stateVector_norm ψ).mp hψ
    have hne : Nonempty I := by
      by_contra hne
      haveI : IsEmpty I := not_nonempty_iff.mp hne
      have hsq : ‖stateVector ψ‖ ^ 2 = ∑ i : I, ‖ψ i‖ ^ 2 := norm_toEuclidean_fromVec_sq ψ
      simp at hsq
      have hn : ‖stateVector ψ‖ = 1 := (normalized_iff_stateVector_norm ψ).mp hψ
      rw [hsq] at hn
      simp at hn
    have hexp0 : expAction A 0 ψ = ψ := by
      simp [expAction, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]
    have hself : normState ψ = ψ := by
      simp [normState, hnorm]
    have htarget : normState (expAction A 0 ψ) = ψ := by
      rw [hexp0, hself]
    have htarget' : normState (normState (expAction A 0 ψ)) = ψ := by
      rw [htarget, hself]
    have hmass : outputMass L {⟨0, hr1⟩} (run hr1 (pairOracles UA UB) (stageWord 1) ω) = 1 := by
      show (∑ k ∈ {⟨0, hr1⟩},
          (normVec (outputBranch L (run hr1 (pairOracles UA UB) (stageWord 1) ω) k)) ^ 2) = _
      rw [Finset.sum_singleton, hout, hnorm]
      norm_num
    have hdens : outputDensity L {⟨0, hr1⟩} (run hr1 (pairOracles UA UB) (stageWord 1) ω)
        = pureDensity ψ := by
      show ((outputMass L {⟨0, hr1⟩} (run hr1 (pairOracles UA UB) (stageWord 1) ω) : ℂ)⁻¹) •
        ∑ k ∈ {⟨0, hr1⟩},
          pureDensity (outputBranch L (run hr1 (pairOracles UA UB) (stageWord 1) ω) k) = _
      rw [hmass, Complex.ofReal_one, inv_one, one_smul, Finset.sum_singleton, hout]
    have hgoal : stateGuarantee L {⟨0, hr1⟩} (run hr1 (pairOracles UA UB) (stageWord 1) ω)
        (normState (expAction A 0 ψ)) ε := by
      refine ⟨?_, ?_⟩
      · rw [hmass]
        norm_num
      · rw [hdens, htarget', sub_self, Matrix.traceNorm_zero]
        exact le_of_lt hε
    have h1le : (1 : ℝ) ≤ odeBPrice αexp αb := by
      have hexp1 : ‖(1 : Matrix I I ℂ)‖ ≤ αexp := by
        have h := hexp 0 (le_refl 0) (le_refl 0)
        simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero] at h
        exact h
      have hone : ‖(1 : Matrix I I ℂ)‖ = 1 := l2_norm_one_eq
      have hαexp1 : (1 : ℝ) ≤ αexp := by rwa [hone] at hexp1
      have hb1 : αb ≤ 1 := by
        have h := hb
        rw [hexp0, hnorm] at h
        exact h
      have hαbexp : αb ≤ αexp := le_trans hb1 hαexp1
      show (1 : ℝ) ≤ αexp / αb
      exact (le_div_iff₀ hαb).mpr (by linarith)
    have hcost1 : (calls (stageWord (H := H) 1) 1 : ℝ) ≤ (1 : ℝ) * odeBPrice αexp αb := by
      rw [hc1, Nat.cast_one, one_mul]
      exact h1le
    have hcost0 : (calls (stageWord (H := H) 1) 0 : ℝ) ≤
        (1 : ℝ) * odeAPrice αA 0 αexp αbmax αb ε := by
      have hz : odeAPrice αA 0 αexp αbmax αb ε = 0 := by simp [odeAPrice]
      rw [hc0, Nat.cast_zero, hz, mul_zero]
    exact ⟨hgoal, hcost1, hcost0, fun _ => hc0⟩

/-- The permutation that exchanges the two flag slots while preserving the data coordinate. -/
def slotFlip (H : Type) : Equiv.Perm (H × Fin 2) :=
  Equiv.prodCongr (Equiv.refl H) (Equiv.swap (0 : Fin 2) 1)

/-- The slot-flip permutation matrix has zero entries between pairs of states both in flag slot
zero. -/
theorem slotFlip_entry_zero {H : Type} [DecidableEq H] (hr : 0 < 2) (h t : H) :
    ((slotFlip H).permMatrix ℂ) (h, ⟨0, hr⟩) (t, ⟨0, hr⟩) = 0 := by
  have hne : ((t, ⟨0, hr⟩) : H × Fin 2) ≠ (slotFlip H) (h, ⟨0, hr⟩) := by
    intro heq
    have h2 := congrArg Prod.snd heq
    have h3 : ((slotFlip H) (h, ⟨0, hr⟩)).2 = (1 : Fin 2) := by
      show (Equiv.swap (0 : Fin 2) 1) (0 : Fin 2) = _
      rw [Equiv.swap_apply_left]
    rw [h3] at h2
    have hval := congrArg Fin.val h2
    simp at hval
  show ((slotFlip H).toPEquiv.toMatrix) (h, ⟨0, hr⟩) (t, ⟨0, hr⟩) = _
  rw [PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]
  exact if_neg hne

/-- The permutation matrix of `slotFlip` is unitary. -/
theorem slotFlip_unitary {H : Type} [Fintype H] [DecidableEq H] :
    ((slotFlip H).permMatrix ℂ) ∈ Matrix.unitaryGroup (H × Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  show ((slotFlip H).permMatrix ℂ) * ((slotFlip H).permMatrix ℂ)ᴴ = 1
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
    Matrix.permMatrix_one]

/-- The projected corner of the slot-flip permutation matrix is zero for arbitrary left and
right embeddings. -/
theorem slotFlip_projectedCorner {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [Fintype O] (L : Matrix H O ℂ) (R : Matrix H I ℂ) (hr : 0 < 2) :
    projectedCorner L R hr ((slotFlip H).permMatrix ℂ) = 0 := by
  ext o i
  show (∑ h, ∑ t,
      star (L h o) * ((slotFlip H).permMatrix ℂ) (h, ⟨0, hr⟩) (t, ⟨0, hr⟩) * R t i) = _
  apply Finset.sum_eq_zero
  intro h _
  apply Finset.sum_eq_zero
  intro t _
  rw [slotFlip_entry_zero hr h t, mul_zero, zero_mul]

/-- Evaluating a Chebyshev expansion with all coefficients zero gives zero. -/
theorem chebValue_zero {n : ℕ} (x : ℝ) :
    chebValue ((fun _ => (0 : ℂ)) : Fin n → ℂ) x = 0 := by
  simp [chebValue]

/-- The operator Chebyshev expansion with all coefficients zero is the zero matrix. -/
theorem chebOperator_zero {I : Type} [Fintype I] [DecidableEq I] {n : ℕ}
    (A : Matrix I I ℂ) :
    chebOperator ((fun _ => (0 : ℂ)) : Fin n → ℂ) A = 0 := by
  simp [chebOperator]

/-- The supremum quantity for the zero polynomial on the half-radius interval is zero. -/
theorem polynomialSup_zero_half {n : ℕ} :
    polynomialSup ((fun _ => (0 : ℂ)) : Fin n → ℂ) (1 / 2) = 0 := by
  have hcheb (x : ℝ) : chebValue ((fun _ => (0 : ℂ)) : Fin n → ℂ) x = 0 :=
    chebValue_zero x
  show sSup {y : ℝ | ∃ x : ℝ, -(1 / 2) ≤ x ∧ x ≤ 1 / 2 ∧
    y = ‖chebValue ((fun _ => (0 : ℂ)) : Fin n → ℂ) x‖} = 0
  have hmem : (0 : ℝ) ∈ {y : ℝ | ∃ x : ℝ, -(1 / 2) ≤ x ∧ x ≤ 1 / 2 ∧
      y = ‖chebValue ((fun _ => (0 : ℂ)) : Fin n → ℂ) x‖} :=
    ⟨0, by norm_num, by norm_num, by rw [hcheb, norm_zero]⟩
  have hle : ∀ y ∈ {y : ℝ | ∃ x : ℝ, -(1 / 2) ≤ x ∧ x ≤ 1 / 2 ∧
      y = ‖chebValue ((fun _ => (0 : ℂ)) : Fin n → ℂ) x‖}, y ≤ 0 := by
    rintro y ⟨x, _, _, rfl⟩
    rw [hcheb, norm_zero]
  exact le_antisymm (Real.sSup_le hle (by norm_num)) (le_csSup ⟨0, hle⟩ hmem)

/-- Under the stated encoding and spectral hypotheses, the zero polynomial has a legal word
satisfying the prescribed query budget and projected-corner approximation bound. -/
theorem clause118_zero_polynomial {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (L R : Matrix H I ℂ) (αA κ α ε : ℝ) (n : ℕ) :
    0 < n → 0 < αA → 1 ≤ κ → 0 < α → 0 < ε → ε < 1 / 4 →
    ∃ (r : ℕ) (hr : 0 < r) (C : Word H r),
      legal 1 C ∧
      (calls C 0 : ℝ) ≤ (1 : ℝ) * blockPolynomialPrice n
        (polynomialSup ((fun _ => (0 : ℂ)) : Fin n → ℂ) (1 / 2)) κ α ε ∧
      ∀ (A : Matrix I I ℂ) (UA : Matrix H H ℂ),
        ProjectedUnitaryEncoding ((αA : ℂ)⁻¹ • A) UA L R →
        (∃ (S : Matrix I I ℂ) (lam : I → ℝ), realSpectrum A S lam κ) →
        2 * ‖A‖ ≤ αA →
        ‖chebOperator ((fun _ => (0 : ℂ)) : Fin n → ℂ) ((αA : ℂ)⁻¹ • A)‖ ≤ α →
        ‖projectedCorner L R hr (wordMatrix (fun _ => UA) C) -
          (((2 * α : ℝ) : ℂ)⁻¹ •
            chebOperator ((fun _ => (0 : ℂ)) : Fin n → ℂ) ((αA : ℂ)⁻¹ • A))‖ ≤ ε := by
  intro _hn _hαA _hκ _hα hε _hε1
  have hr2 : 0 < 2 := by norm_num
  refine ⟨2, hr2, [.known ((slotFlip H).permMatrix ℂ)], ?_, ?_, ?_⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    show ((slotFlip H).permMatrix ℂ) ∈ Matrix.unitaryGroup (Space H 2) ℂ
    exact slotFlip_unitary
  · have hP : blockPolynomialPrice n
        (polynomialSup ((fun _ => (0 : ℂ)) : Fin n → ℂ) (1 / 2)) κ α ε = 0 := by
      rw [polynomialSup_zero_half]
      simp [blockPolynomialPrice]
    have hcalls : calls [.known ((slotFlip H).permMatrix ℂ)] 0 = 0 := by
      simp [calls]
    rw [hcalls, Nat.cast_zero, hP, mul_zero]
  · intro A UA _henc _hspec _hnA _hcheb
    have hword : wordMatrix (fun _ => (UA : Matrix H H ℂ))
        [.known ((slotFlip H).permMatrix ℂ)] = (slotFlip H).permMatrix ℂ := by
      simp [wordMatrix]
    have hcorner : projectedCorner L R hr2
        (wordMatrix (fun _ => UA) [.known ((slotFlip H).permMatrix ℂ)]) = 0 := by
      rw [hword]
      exact slotFlip_projectedCorner L R hr2
    rw [hcorner, chebOperator_zero, smul_zero, sub_zero, norm_zero]
    exact le_of_lt hε

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
