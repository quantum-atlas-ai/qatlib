/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixWeights.WeightsCore

/-!
# Averaged matrix multiplicative weights for SDP feasibility

`mmwAverage_isDensityOperator` and `mmw_trace_average` expose the normalization and linearity of
the average of Gibbs iterates. `matrix_mw_same_history_sdp_average_consumer` combines these
identities with noncommuting regret, using the same selected constraint history for the states
and the comparison estimate.

The resulting constraint residual bound is an analytic ingredient in matrix multiplicative
weights SDP methods [BrandaoSvore2017].

## Main statements

* `mmwAverage_isDensityOperator` proves density normalization for a positive number of
  Hermitian-loss iterates in positive dimension.
* `mmw_trace_average` expresses a trace pairing with the average as an average of trace
  pairings.
* `matrix_mw_same_history_sdp_average_consumer` bounds every averaged constraint by its
  threshold plus `eta + log D / (eta*T)` under exact selection and a feasible density
  comparator.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017], *Quantum Speed-Ups for Solving Semidefinite
  Programs*.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixWeights.WeightsCore

namespace Qatlib.Concepts.MatrixWeights.SdpAlgorithm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The average of a positive number of Gibbs iterates is a density operator when the dimension
is positive and all losses are Hermitian. -/
theorem mmwAverage_isDensityOperator (D T : ℕ) (M : ℕ → Operator D) (η : ℝ)
    (hD : 0 < D) (hT : 0 < T) (hM : ∀ s, (M s).IsHermitian) :
    IsDensityOperator (mmwAverage D T M η) := by
  have hd (t : ℕ) := (matrix_mw_actual_gibbs_iterates_density D M η t hD hM).2
  have hs := Matrix.posSemidef_sum (Finset.range T) (fun t _ => (hd t).1)
  have ht (t : ℕ) : Matrix.trace (mmwState D M η t) = 1 := (hd t).2
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hT
  constructor
  · unfold mmwAverage
    apply hs.smul
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    exact_mod_cast (inv_nonneg.mpr (Nat.cast_nonneg T : (0:ℝ) ≤ T))
  · rw [mmwAverage, Matrix.trace_smul, Matrix.trace_sum]
    simp_rw [ht]
    simp [smul_eq_mul, hTc]

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

/-- A real trace pairing with `mmwAverage` equals the sum of the corresponding pairings with
individual Gibbs iterates divided by the number of rounds. -/
theorem mmw_trace_average (D T : ℕ) (M : ℕ → Operator D) (η : ℝ) (C : Operator D) :
    (Matrix.trace (C*mmwAverage D T M η)).re =
      (∑ t∈Finset.range T, (Matrix.trace (C*mmwState D M η t)).re)/(T:ℝ) := by
  simp only [mmwAverage, Matrix.mul_smul, Matrix.trace_smul, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, smul_eq_mul, Matrix.mul_sum, Matrix.trace_sum,
    Complex.mul_re, Complex.re_sum, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- For bounded Hermitian constraints, exact residual selection and a feasible density
comparator imply that the average is a density operator with every constraint bounded by its
threshold plus `eta + log D / (eta*T)`. This is a same-history feasibility estimate for
matrix multiplicative weights SDP methods [BrandaoSvore2017]. -/
theorem matrix_mw_same_history_sdp_average_consumer
    (D T m : ℕ) (C : Fin m → Operator D) (b : Fin m → ℝ)
    (a : ℕ → Fin m) (η : ℝ) (σ : Operator D)
    (hD : 0<D) (hT : 0<T) (hη : 0<η) (hη1 : η≤1)
    (hC : ∀ i, (C i).IsHermitian ∧ ‖C i‖≤1) (hσ : IsDensityOperator σ)
    (hfeas : ∀ i, (Matrix.trace (C i*σ)).re ≤ b i)
    (hselect : ∀ t<T, ∀ i, (Matrix.trace (C i*mmwState D (fun s => C (a s)) η t)).re-b i ≤
      (Matrix.trace (C (a t)*mmwState D (fun s => C (a s)) η t)).re-b (a t)) :
    IsDensityOperator (mmwAverage D T (fun s => C (a s)) η) ∧
      ∀ i, (Matrix.trace (C i*mmwAverage D T (fun s => C (a s)) η)).re ≤
        b i+η+Real.log D/(η*T) := by
  let M := fun s => C (a s)
  have hM (s : ℕ) : (M s).IsHermitian ∧ ‖M s‖≤1 := hC (a s)
  have hr := matrix_mw_noncommuting_regret D T M η σ hD hη hη1 hM hσ
  refine ⟨mmwAverage_isDensityOperator D T M η hD hT (fun s => (hM s).1), ?_⟩
  intro i
  have hv (t : ℕ) (ht : t∈Finset.range T) :
      (Matrix.trace (C i*mmwState D M η t)).re-b i ≤
        (Matrix.trace (M t*mmwState D M η t)).re-(Matrix.trace (M t*σ)).re := by
    have hs := hselect t (Finset.mem_range.mp ht) i
    have hf := hfeas (a t)
    dsimp [M] at *
    linarith
  have hsum := Finset.sum_le_sum hv
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hmul := mul_le_mul_of_nonneg_left hsum hη.le
  have hbound : η*(∑ t∈Finset.range T, (Matrix.trace (C i*mmwState D M η t)).re) ≤
      η*(b i*(T:ℝ))+η^2*T+Real.log D := by nlinarith
  rw [mmw_trace_average]
  have hTr : (0:ℝ)<T := by exact_mod_cast hT
  apply (div_le_iff₀ hTr).mpr
  apply (mul_le_mul_iff_right₀ hη).mp
  have he : η*((b i+η+Real.log D/(η*T))*(T:ℝ)) =
      η*(b i*(T:ℝ))+η^2*T+Real.log D := by
    field_simp
  rw [he]
  simpa only [mul_comm] using! hbound

end Qatlib.Concepts.MatrixWeights.SdpAlgorithm
