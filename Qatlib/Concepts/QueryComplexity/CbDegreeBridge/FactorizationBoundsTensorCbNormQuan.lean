/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.CbFormsAux
public import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.FactorizationBoundsTensorCbNormStat

@[expose] public section
open Qatlib.Concepts.QueryComplexity.CbDegreeBridge Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QueryComplexity.CbDegreeBridge

open Matrix

open scoped Classical BigOperators Matrix.Norms.L2Operator

section Dual

variable {m : Type} [Fintype m] [DecidableEq m]

/-- The complex norm of a coerced real number equals its absolute value. -/
private theorem norm_ofReal_complex (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h1 : ‖((r : ℝ) : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq_abs]
    ring
  rw [show ‖((r : ℝ) : ℂ)‖ = Real.sqrt (‖((r : ℝ) : ℂ)‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm, h1, Real.sqrt_sq (abs_nonneg r)]

omit [DecidableEq m] in
/-- Scaling the first argument of `Inner` multiplies the inner product by the conjugate scalar. -/
private theorem inner_smul_left [DecidableEq m] (c : ℂ) (ξ w : QState m) :
    Inner (c • ξ) w = (starRingEnd ℂ) c * Inner ξ w := by
  rw [inner_apply, inner_apply]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq m] in
/-- The Euclidean norm of a scaled state equals the scalar norm times the original Euclidean
norm. -/
private theorem norm_toEuclidean_fromVec_smul [DecidableEq m] (c : ℂ) (φ : QState m) :
    ‖toEuclidean_fromVec (c • φ)‖ = ‖c‖ * ‖toEuclidean_fromVec φ‖ := by
  have hsq : ‖toEuclidean_fromVec (c • φ)‖ ^ 2 = (‖c‖ * ‖toEuclidean_fromVec φ‖) ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq]
    calc ∑ i, ‖(c • φ) i‖ ^ 2 = ∑ i, ‖c‖ ^ 2 * ‖φ i‖ ^ 2 :=
            Finset.sum_congr rfl fun i _ => by
              rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
      _ = ‖c‖ ^ 2 * ∑ i, ‖φ i‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ = (‖c‖ * ‖toEuclidean_fromVec φ‖) ^ 2 := by
            rw [← norm_toEuclidean_fromVec_sq, mul_pow]
  rw [show ‖toEuclidean_fromVec (c • φ)‖ = Real.sqrt (‖toEuclidean_fromVec (c • φ)‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm, hsq,
    Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]

/-- A nonnegative bound on all matrix inner products between unit vectors bounds the matrix
operator norm. -/
private theorem l2_opNorm_le_of_inner_le {C : ℝ} (hC : 0 ≤ C) {A : Matrix m m ℂ}
    (h : ∀ ξ η : QState m, ‖toEuclidean_fromVec ξ‖ = 1 → ‖toEuclidean_fromVec η‖ = 1 →
      ‖Inner ξ (A *ᵥ η)‖ ≤ C) : ‖A‖ ≤ C := by
  refine l2_opNorm_le_of_mulVec_le hC A fun η => ?_
  by_cases hη : ‖toEuclidean_fromVec η‖ = 0
  · have hsum0 : ∑ i, ‖η i‖ ^ 2 = 0 := by
      rw [← norm_toEuclidean_fromVec_sq, hη]
      simp
    have hηi : ∀ i, η i = 0 := by
      intro i
      have hle : ‖η i‖ ^ 2 ≤ 0 := by
        have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (‖η j‖))
          (Finset.mem_univ i)
        rw [hsum0] at this
        exact this
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _)))
    have h0 : ‖toEuclidean_fromVec (A *ᵥ η)‖ = 0 := by
      have hsq : ‖toEuclidean_fromVec (A *ᵥ η)‖ ^ 2 = 0 := by
        rw [norm_toEuclidean_fromVec_sq]
        simp [Matrix.mulVec, dotProduct, hηi]
      rw [show ‖toEuclidean_fromVec (A *ᵥ η)‖ = Real.sqrt (‖toEuclidean_fromVec (A *ᵥ η)‖ ^ 2) from
          (Real.sqrt_sq (norm_nonneg _)).symm, hsq, Real.sqrt_zero]
    rw [h0]
    exact mul_nonneg hC (norm_nonneg _)
  · have hpos : 0 < ‖toEuclidean_fromVec η‖ :=
      lt_of_le_of_ne (norm_nonneg _) fun h0 => hη h0.symm
    have hη₁ : ‖toEuclidean_fromVec (((‖toEuclidean_fromVec η‖⁻¹ : ℝ) : ℂ) • η)‖ = 1 := by
      rw [norm_toEuclidean_fromVec_smul, norm_ofReal_complex,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hη]
    have hscale : A *ᵥ η
        = ((‖toEuclidean_fromVec η‖ : ℝ) : ℂ) • (A *ᵥ (((‖toEuclidean_fromVec η‖⁻¹ : ℝ) : ℂ) • η)) := by
      rw [← Matrix.mulVec_smul, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hη,
        Complex.ofReal_one, one_smul]
    set w : QState m := A *ᵥ (((‖toEuclidean_fromVec η‖⁻¹ : ℝ) : ℂ) • η) with hw
    by_cases hw0 : ‖toEuclidean_fromVec w‖ = 0
    · rw [hscale, hw]
      rw [show ‖toEuclidean_fromVec (((‖toEuclidean_fromVec η‖ : ℝ) : ℂ) • w)‖
          = ‖((‖toEuclidean_fromVec η‖ : ℝ) : ℂ)‖ * ‖toEuclidean_fromVec w‖ from
          norm_toEuclidean_fromVec_smul _ _, norm_ofReal_complex,
        abs_of_nonneg (norm_nonneg _), hw0, mul_zero]
      exact mul_nonneg hC (norm_nonneg _)
    · have hwpos : 0 < ‖toEuclidean_fromVec w‖ := by
        rcases eq_or_lt_of_le (norm_nonneg (toEuclidean_fromVec w)) with h0 | h0
        · exact absurd h0.symm hw0
        · exact h0
      have hξ₁ : ‖toEuclidean_fromVec (((‖toEuclidean_fromVec w‖⁻¹ : ℝ) : ℂ) • w)‖ = 1 := by
        rw [norm_toEuclidean_fromVec_smul, norm_ofReal_complex,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hw0]
      have hval : Inner (((‖toEuclidean_fromVec w‖⁻¹ : ℝ) : ℂ) • w)
          (A *ᵥ (((‖toEuclidean_fromVec η‖⁻¹ : ℝ) : ℂ) • η))
          = ((‖toEuclidean_fromVec w‖ : ℝ) : ℂ) := by
        rw [inner_smul_left, inner_self, ← Complex.ofReal_sum, ← norm_toEuclidean_fromVec_sq,
          Complex.conj_ofReal, Complex.ofReal_inv, Complex.ofReal_pow, sq,
          inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr hw0)]
      have hle := h (((‖toEuclidean_fromVec w‖⁻¹ : ℝ) : ℂ) • w)
        (((‖toEuclidean_fromVec η‖⁻¹ : ℝ) : ℂ) • η) hξ₁ hη₁
      rw [hval, norm_ofReal_complex, abs_of_nonneg (norm_nonneg _)] at hle
      rw [hscale, hw]
      rw [show ‖toEuclidean_fromVec (((‖toEuclidean_fromVec η‖ : ℝ) : ℂ) • w)‖
          = ‖((‖toEuclidean_fromVec η‖ : ℝ) : ℂ)‖ * ‖toEuclidean_fromVec w‖ from
          norm_toEuclidean_fromVec_smul _ _, norm_ofReal_complex,
        abs_of_nonneg (norm_nonneg _)]
      calc ‖toEuclidean_fromVec η‖ * ‖toEuclidean_fromVec w‖
          ≤ ‖toEuclidean_fromVec η‖ * C := mul_le_mul_of_nonneg_left hle hpos.le
        _ = C * ‖toEuclidean_fromVec η‖ := mul_comm _ _

end Dual

/-- A tensor admitting `HasCbFactorization` has completely bounded norm at most one. -/
theorem factorizationBoundsTensorCbNorm : FactorizationBoundsTensorCbNorm := by
  intro κ _ s T hfac
  obtain ⟨R, _, _, δ, u, v, W, hu, hv, hW, hcert⟩ := hfac
  have hfs : ∀ i : Fin s → κ, cbFiberSum W δ u v (fun j => some (i j)) = (T i : ℂ) :=
    cbFiberSum_full hcert
  have hu' : ‖toEuclidean_fromVec u‖ = 1 := (normalized_iff_norm_toEuclidean_fromVec u).mp hu
  have hv' : ‖toEuclidean_fromVec v‖ = 1 := (normalized_iff_norm_toEuclidean_fromVec v).mp hv
  refine csSup_le ?_ fun r hr => ?_
  · exact ⟨_, 1, fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ),
      fun _ _ => norm_zero.trans_le zero_le_one, rfl⟩
  · obtain ⟨d, A, hA, rfl⟩ := hr
    refine l2_opNorm_le_of_inner_le zero_le_one fun ξ η hξ hη => ?_
    rw [cbAmplified W δ u v T hfs A ξ η]
    calc ‖Inner (fun x : R × Fin d => u x.1 * ξ x.2)
            ((matProdFin (s + 1) (cbNbig W δ A)) *ᵥ (fun x : R × Fin d => v x.1 * η x.2))‖
        = ‖inner ℂ (toEuclidean_fromVec (fun x : R × Fin d => u x.1 * ξ x.2))
            (toEuclidean_fromVec ((matProdFin (s + 1) (cbNbig W δ A)) *ᵥ
              (fun x : R × Fin d => v x.1 * η x.2)))‖ := by
          rw [inner_euclidean_fromVec]
      _ ≤ ‖toEuclidean_fromVec (fun x : R × Fin d => u x.1 * ξ x.2)‖ *
            ‖toEuclidean_fromVec ((matProdFin (s + 1) (cbNbig W δ A)) *ᵥ
              (fun x : R × Fin d => v x.1 * η x.2))‖ := norm_inner_le_norm _ _
      _ ≤ ‖toEuclidean_fromVec (fun x : R × Fin d => u x.1 * ξ x.2)‖ *
            (‖matProdFin (s + 1) (cbNbig W δ A)‖ *
              ‖toEuclidean_fromVec (fun x : R × Fin d => v x.1 * η x.2)‖) :=
            mul_le_mul_of_nonneg_left (l2_norm_mulVec_fromVec_le _ _) (norm_nonneg _)
      _ ≤ ‖toEuclidean_fromVec (fun x : R × Fin d => u x.1 * ξ x.2)‖ *
            (1 * ‖toEuclidean_fromVec (fun x : R × Fin d => v x.1 * η x.2)‖) := by
            refine mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (cbNbig_prod_norm_le W δ A hW hA) (norm_nonneg _))
              (norm_nonneg _)
      _ = 1 := by
          rw [show (fun x : R × Fin d => u x.1 * ξ x.2) = TensorState u ξ from rfl,
            show (fun x : R × Fin d => v x.1 * η x.2) = TensorState v η from rfl,
            tensorState_l2_norm, tensorState_l2_norm, hu', hv', hξ, hη]
          norm_num

end Qatlib.Concepts.QueryComplexity.CbDegreeBridge
