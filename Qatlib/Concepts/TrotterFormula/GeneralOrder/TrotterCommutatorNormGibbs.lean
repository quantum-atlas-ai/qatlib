/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-!
# Gibbs normalization and output error bounds

This module controls trace normalization of an approximation to an unnormalized Gibbs
exponential. It proves positivity and unit-trace properties, then bounds normalized operator
error and observable trace error under an explicit partition-function gap. The Gibbs sampling
setting is discussed in [ChowdhurySomma2017].

The theorem `clause57` packages a normalized density operator, its error estimates, and a
resource ledger. A logarithmic repetition selector ensures the stated repeated-failure bound,
while the ledger separately records preparation calls and readout shots.

## Main statements

* `normalizedDensity_isDensity`: density-operator property after normalization.
* `gibbs_normalized_output_bound`: normalized error estimate under the partition gap.
* `gibbs_observable_bound`: observable trace bound from operator norm.
* `clause57`: normalized output, error bounds, and resource ledger.

## References

* [Chowdhury and Somma, 2017][ChowdhurySomma2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs

set_option autoImplicit false
set_option maxHeartbeats 400000

open Matrix Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open scoped Classical BigOperators Matrix.Norms.L2Operator

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder

/-- The absolute value of the trace of a `D`-dimensional operator is at most `D` times its
operator norm. -/
theorem trace_abs_le_card_mul_opNorm {D : ℕ} (X : Operator D) :
    ‖Matrix.trace X‖ ≤ (D : ℝ) * ‖X‖ := by
  have h1 : ‖Matrix.trace X‖ ≤ Matrix.traceNorm X := Matrix.abs_trace_le_traceNorm X
  have h2 : Matrix.traceNorm X = ∑ i : Fin D, singularValues X i :=
    Matrix.traceNorm_eq_sum_singularValues X
  calc
    ‖Matrix.trace X‖ ≤ ∑ i : Fin D, singularValues X i := by rw [← h2]; exact h1
    _ ≤ ∑ i : Fin D, ‖X‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact Matrix.singularValues_le_opNorm X i
    _ = (D : ℝ) * ‖X‖ := by
      simp
open scoped ComplexOrder

/-- The trace of a positive semidefinite operator is the complex embedding of its real part. -/
theorem psd_trace_eq_ofReal {D : ℕ} (M : Operator D) (hM : M.PosSemidef) :
    Matrix.trace M = ((Matrix.trace M).re : ℂ) := by
  have hnn : (0 : ℂ) ≤ Matrix.trace M := hM.trace_nonneg
  obtain ⟨_, him⟩ := RCLike.nonneg_iff.mp hnn
  exact (Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr him)).symm

/-- Trace normalization preserves positive semidefiniteness. -/
theorem normalizedDensity_posSemidef {D : ℕ} (M : Operator D) (hM : M.PosSemidef) :
    (normalizedDensity M).PosSemidef := by
  have hreal := psd_trace_eq_ofReal M hM
  have hre : 0 ≤ (Matrix.trace M).re := by
    have hnn : (0 : ℂ) ≤ Matrix.trace M := hM.trace_nonneg
    exact (RCLike.nonneg_iff.mp hnn).1
  unfold normalizedDensity
  rw [hreal, ← Complex.ofReal_inv]
  exact Matrix.PosSemidef.smul hM (RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hre))

/-- An operator with nonzero trace has trace one after applying `normalizedDensity`. -/
theorem normalizedDensity_trace_eq_one {D : ℕ} (M : Operator D)
    (hne : Matrix.trace M ≠ 0) : Matrix.trace (normalizedDensity M) = 1 := by
  rw [normalizedDensity, Matrix.trace_smul, smul_eq_mul]
  exact inv_mul_cancel₀ hne

/-- A positive semidefinite operator with nonzero trace becomes a density operator after trace
normalization. -/
theorem normalizedDensity_isDensity {D : ℕ} (M : Operator D) (hM : M.PosSemidef)
    (hne : Matrix.trace M ≠ 0) : IsDensityOperator (normalizedDensity M) :=
  ⟨normalizedDensity_posSemidef M hM, normalizedDensity_trace_eq_one M hne⟩

/-- An operator within `η` of the unnormalized Gibbs operator satisfies the stated normalized
operator-norm error bound whenever `D * η` is smaller than the partition-function norm. -/
theorem gibbs_normalized_output_bound {D : ℕ} (H : Operator D) (β : ℝ)
    (Mword : Operator D) (η : ℝ)
    (hclose : ‖Mword - gibbsUnnormalized H β‖ ≤ η)
    (hgap : (D : ℝ) * η < ‖gibbsPartition H β‖) :
    ‖normalizedDensity Mword - gibbsDensity H β‖ ≤
      η / (‖gibbsPartition H β‖ - (D : ℝ) * η) +
        ‖gibbsUnnormalized H β‖ * (D : ℝ) * η /
          ((‖gibbsPartition H β‖ - (D : ℝ) * η) * ‖gibbsPartition H β‖) := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hclose
  have hZG : gibbsPartition H β = Matrix.trace (gibbsUnnormalized H β) := rfl
  have hTrDiff : ‖Matrix.trace (Mword - gibbsUnnormalized H β)‖ ≤ (D : ℝ) * η :=
    (trace_abs_le_card_mul_opNorm (Mword - gibbsUnnormalized H β)).trans (by gcongr)
  have hsz : ‖Matrix.trace Mword - gibbsPartition H β‖ ≤ (D : ℝ) * η := by
    have hsub : Matrix.trace (Mword - gibbsUnnormalized H β) =
        Matrix.trace Mword - gibbsPartition H β := by
      rw [Matrix.trace_sub, hZG]
    rw [← hsub]
    exact hTrDiff
  have htri : ‖gibbsPartition H β‖ ≤ ‖Matrix.trace Mword‖ +
      ‖Matrix.trace Mword - gibbsPartition H β‖ := by
    have hkey : gibbsPartition H β =
        Matrix.trace Mword + (gibbsPartition H β - Matrix.trace Mword) := by abel
    have h1 : ‖gibbsPartition H β‖ ≤ ‖Matrix.trace Mword‖ +
        ‖gibbsPartition H β - Matrix.trace Mword‖ := by
      nth_rw 1 [hkey]
      exact norm_add_le (Matrix.trace Mword) (gibbsPartition H β - Matrix.trace Mword)
    have h2 : ‖gibbsPartition H β - Matrix.trace Mword‖ =
        ‖Matrix.trace Mword - gibbsPartition H β‖ :=
      norm_sub_rev (gibbsPartition H β) (Matrix.trace Mword)
    rw [h2] at h1
    exact h1
  have hs_ge : ‖gibbsPartition H β‖ - (D : ℝ) * η ≤ ‖Matrix.trace Mword‖ := by
    nlinarith [hsz]
  have hspos : 0 < ‖Matrix.trace Mword‖ := by nlinarith [hgap]
  have hsne : Matrix.trace Mword ≠ 0 := by
    intro h
    simp [h] at hspos
  have hZpos : 0 < ‖gibbsPartition H β‖ := lt_of_le_of_lt (by positivity) hgap
  have hZne : gibbsPartition H β ≠ 0 := by
    intro h
    simp [h] at hZpos
  have hden : 0 < ‖gibbsPartition H β‖ - (D : ℝ) * η := by nlinarith [hgap]
  have key : normalizedDensity Mword - gibbsDensity H β =
      (Matrix.trace Mword)⁻¹ • (Mword - gibbsUnnormalized H β) +
        ((Matrix.trace Mword)⁻¹ - (gibbsPartition H β)⁻¹) • gibbsUnnormalized H β := by
    rw [normalizedDensity, gibbsDensity]
    rw [smul_sub, sub_smul]
    abel
  have hsplit : ‖(Matrix.trace Mword)⁻¹ - (gibbsPartition H β)⁻¹‖ =
      ‖gibbsPartition H β - Matrix.trace Mword‖ /
        (‖Matrix.trace Mword‖ * ‖gibbsPartition H β‖) := by
    rw [_root_.inv_sub_inv hsne hZne]
    have hnum : ‖(gibbsPartition H β - Matrix.trace Mword) /
        (Matrix.trace Mword * gibbsPartition H β)‖ =
        ‖gibbsPartition H β - Matrix.trace Mword‖ /
          ‖Matrix.trace Mword * gibbsPartition H β‖ := by
      rw [norm_div]
    rw [hnum, norm_mul]
  rw [key]
  calc
    ‖(Matrix.trace Mword)⁻¹ • (Mword - gibbsUnnormalized H β) +
        ((Matrix.trace Mword)⁻¹ - (gibbsPartition H β)⁻¹) • gibbsUnnormalized H β‖ ≤
        ‖(Matrix.trace Mword)⁻¹ • (Mword - gibbsUnnormalized H β)‖ +
          ‖((Matrix.trace Mword)⁻¹ - (gibbsPartition H β)⁻¹) • gibbsUnnormalized H β‖ :=
      norm_add_le _ _
    _ = ‖(Matrix.trace Mword)⁻¹‖ * ‖Mword - gibbsUnnormalized H β‖ +
          ‖(Matrix.trace Mword)⁻¹ - (gibbsPartition H β)⁻¹‖ * ‖gibbsUnnormalized H β‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ ‖(Matrix.trace Mword)⁻¹‖ * η +
          ‖(Matrix.trace Mword)⁻¹ - (gibbsPartition H β)⁻¹‖ * ‖gibbsUnnormalized H β‖ := by
      gcongr
    _ = ‖(Matrix.trace Mword)⁻¹‖ * η +
          (‖gibbsPartition H β - Matrix.trace Mword‖ /
            (‖Matrix.trace Mword‖ * ‖gibbsPartition H β‖)) * ‖gibbsUnnormalized H β‖ := by
      rw [hsplit]
    _ ≤ (‖gibbsPartition H β‖ - (D : ℝ) * η)⁻¹ * η +
          (((D : ℝ) * η) / (‖Matrix.trace Mword‖ * ‖gibbsPartition H β‖)) *
            ‖gibbsUnnormalized H β‖ := by
      have hnorm : ‖(Matrix.trace Mword)⁻¹‖ = ‖Matrix.trace Mword‖⁻¹ := norm_inv _
      have h1 : ‖(Matrix.trace Mword)⁻¹‖ ≤ (‖gibbsPartition H β‖ - (D : ℝ) * η)⁻¹ := by
        rw [hnorm]
        exact inv_anti₀ hden hs_ge
      have h2 : ‖gibbsPartition H β - Matrix.trace Mword‖ ≤ (D : ℝ) * η := by
        rw [norm_sub_rev]
        exact hsz
      refine add_le_add (mul_le_mul_of_nonneg_right h1 (by positivity)) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine div_le_div_of_nonneg_right h2 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ η / (‖gibbsPartition H β‖ - (D : ℝ) * η) +
          ‖gibbsUnnormalized H β‖ * (D : ℝ) * η /
            ((‖gibbsPartition H β‖ - (D : ℝ) * η) * ‖gibbsPartition H β‖) := by
      have hpos1 : 0 < ‖gibbsPartition H β‖ - (D : ℝ) * η := hden
      have hpos2 : 0 < ‖Matrix.trace Mword‖ := hspos
      have hpos3 : 0 < ‖gibbsPartition H β‖ := hZpos
      have hin : ‖gibbsPartition H β‖ - (D : ℝ) * η ≤ ‖Matrix.trace Mword‖ := hs_ge
      have ha : (‖gibbsPartition H β‖ - (D : ℝ) * η)⁻¹ * η =
          η / (‖gibbsPartition H β‖ - (D : ℝ) * η) := by
        rw [div_eq_mul_inv]
        ring
      have hmono : ((D : ℝ) * η) / (‖Matrix.trace Mword‖ * ‖gibbsPartition H β‖) ≤
          ((D : ℝ) * η) / ((‖gibbsPartition H β‖ - (D : ℝ) * η) * ‖gibbsPartition H β‖) := by
        refine div_le_div_of_nonneg_left (by positivity)
          (mul_pos hpos1 hpos3) ?_
        exact mul_le_mul_of_nonneg_right hin (norm_nonneg _)
      have hb : ((D : ℝ) * η / (‖Matrix.trace Mword‖ * ‖gibbsPartition H β‖)) *
          ‖gibbsUnnormalized H β‖ ≤
          ‖gibbsUnnormalized H β‖ * (D : ℝ) * η /
            ((‖gibbsPartition H β‖ - (D : ℝ) * η) * ‖gibbsPartition H β‖) := by
        calc
          ((D : ℝ) * η / (‖Matrix.trace Mword‖ * ‖gibbsPartition H β‖)) *
              ‖gibbsUnnormalized H β‖ ≤
              ((D : ℝ) * η / ((‖gibbsPartition H β‖ - (D : ℝ) * η) * ‖gibbsPartition H β‖)) *
                ‖gibbsUnnormalized H β‖ :=
            mul_le_mul_of_nonneg_right hmono (norm_nonneg _)
          _ = ‖gibbsUnnormalized H β‖ * (D : ℝ) * η /
                ((‖gibbsPartition H β‖ - (D : ℝ) * η) * ‖gibbsPartition H β‖) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
      rw [ha]
      exact add_le_add le_rfl hb

/-- The difference of observable traces is at most `‖O‖ * D * ‖ρ-g‖` in dimension `D`. -/
theorem gibbs_observable_bound {D : ℕ} (ρ g O : Operator D) :
    ‖Matrix.trace (O * ρ) - Matrix.trace (O * g)‖ ≤
      ‖O‖ * (D : ℝ) * ‖ρ - g‖ := by
  have h1 : Matrix.trace (O * ρ) - Matrix.trace (O * g) = Matrix.trace (O * (ρ - g)) := by
    rw [mul_sub, Matrix.trace_sub]
  rw [h1]
  calc
    ‖Matrix.trace (O * (ρ - g))‖ ≤ (D : ℝ) * ‖O * (ρ - g)‖ :=
      trace_abs_le_card_mul_opNorm _
    _ ≤ (D : ℝ) * (‖O‖ * ‖ρ - g‖) := by
      gcongr
      exact Matrix.l2_opNorm_mul O (ρ - g)
    _ = ‖O‖ * (D : ℝ) * ‖ρ - g‖ := by ring

/-- For success probability and failure tolerance in `(0,1)`, the selected repetition count
makes `(1-p)^r` at most `δ`. -/
theorem gibbsAmplificationRounds_pow_le (p δ : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - p) ^ gibbsAmplificationRounds p δ ≤ δ := by
  have h1p : 0 < 1 - p := by linarith
  have h1p1 : 1 - p < 1 := by linarith
  have hlogp : Real.log (1 - p) < 0 := Real.log_neg h1p h1p1
  have hlogδ : Real.log δ < 0 := Real.log_neg hδ hδ1
  have hLpos : 0 < Real.log δ / Real.log (1 - p) := div_pos_of_neg_of_neg hlogδ hlogp
  have hceil_ge : (Real.log δ / Real.log (1 - p)) ≤
      (Nat.ceil (Real.log δ / Real.log (1 - p)) : ℝ) := Nat.le_ceil _
  have hone : 1 ≤ Nat.ceil (Real.log δ / Real.log (1 - p)) := by
    have hpos : 0 < Nat.ceil (Real.log δ / Real.log (1 - p)) := Nat.ceil_pos.mpr hLpos
    omega
  rw [gibbsAmplificationRounds, max_eq_right hone]
  have hlogmul : (Nat.ceil (Real.log δ / Real.log (1 - p)) : ℝ) * Real.log (1 - p) ≤
      Real.log δ := by
    have hL : Real.log δ / Real.log (1 - p) * Real.log (1 - p) = Real.log δ :=
      div_mul_cancel₀ (Real.log δ) (ne_of_lt hlogp)
    have hmul : ((Nat.ceil (Real.log δ / Real.log (1 - p)) : ℝ) -
        Real.log δ / Real.log (1 - p)) * Real.log (1 - p) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hceil_ge) hlogp.le
    nlinarith [hmul, hL]
  have hpow : ((1 - p) ^ (Nat.ceil (Real.log δ / Real.log (1 - p)) : ℕ) : ℝ) =
      Real.exp ((Nat.ceil (Real.log δ / Real.log (1 - p)) : ℝ) * Real.log (1 - p)) := by
    have hcast : (1 - p) ^ (Nat.ceil (Real.log δ / Real.log (1 - p)) : ℕ) =
        (1 - p) ^ ((Nat.ceil (Real.log δ / Real.log (1 - p)) : ℕ) : ℝ) :=
      (Real.rpow_natCast (1 - p) (Nat.ceil (Real.log δ / Real.log (1 - p)))).symm
    rw [hcast, Real.rpow_def_of_pos h1p]
    congr 1
    ring
  rw [hpow]
  have hle : Real.exp ((Nat.ceil (Real.log δ / Real.log (1 - p)) : ℝ) * Real.log (1 - p)) ≤
      Real.exp (Real.log δ) := Real.exp_le_exp.mpr hlogmul
  rw [Real.exp_log hδ] at hle
  exact hle

/-- A positive semidefinite approximation to a Hermitian Gibbs exponential satisfying the
partition-gap bound yields a normalized density operator with the stated operator and
observable error bounds. The accompanying ledger records preparation calls, readout shots,
and amplification rounds whose repeated-failure bound is at most `δ`. -/
theorem clause57 : ∀ (D : ℕ) (H : Operator D) (β : ℝ) (p δ εro : ℝ),
    Hᴴ = H →
    0 ≤ β →
    0 < p →
    p < 1 →
    0 < δ →
    δ < 1 →
    0 < εro →
    0 < ‖gibbsPartition H β‖ →
    ∀ (Mword : Operator D) (η : ℝ),
      0 ≤ η →
      Mword.PosSemidef →
      ‖Mword - gibbsUnnormalized H β‖ ≤ η →
      (D : ℝ) * η < ‖gibbsPartition H β‖ →
      ∃ (ρ : Operator D) (ledger : GibbsOutputLedger),
        ρ = normalizedDensity Mword ∧
        IsDensityOperator ρ ∧
        ‖ρ - gibbsDensity H β‖ ≤
          η / (‖gibbsPartition H β‖ - (D : ℝ) * η) +
            ‖gibbsUnnormalized H β‖ * (D : ℝ) * η /
              ((‖gibbsPartition H β‖ - (D : ℝ) * η) * ‖gibbsPartition H β‖) ∧
        (∀ O : Operator D,
          ‖Matrix.trace (O * ρ) - Matrix.trace (O * gibbsDensity H β)‖ ≤
            ‖O‖ * (D : ℝ) * ‖ρ - gibbsDensity H β‖) ∧
        ledger.amplificationRounds = gibbsAmplificationRounds p δ ∧
        ledger.prepCalls = gibbsAmplificationRounds p δ ∧
        ledger.readoutShots = gibbsReadoutShots εro δ ∧
        (1 - p) ^ ledger.amplificationRounds ≤ δ := by
  intro D H β p δ εro _hHerm _hβ hp hp1 hδ hδ1 hεro _hZ Mword η _hη hpsd hclose hgap
  have hne : Matrix.trace Mword ≠ 0 := by
    have hZG : gibbsPartition H β = Matrix.trace (gibbsUnnormalized H β) := rfl
    have hTrDiff : ‖Matrix.trace (Mword - gibbsUnnormalized H β)‖ ≤ (D : ℝ) * η :=
      (trace_abs_le_card_mul_opNorm (Mword - gibbsUnnormalized H β)).trans (by gcongr)
    have hsz : ‖Matrix.trace Mword - gibbsPartition H β‖ ≤ (D : ℝ) * η := by
      have hsub : Matrix.trace (Mword - gibbsUnnormalized H β) =
          Matrix.trace Mword - gibbsPartition H β := by
        rw [Matrix.trace_sub, hZG]
      rw [← hsub]
      exact hTrDiff
    have htri : ‖gibbsPartition H β‖ ≤ ‖Matrix.trace Mword‖ +
        ‖Matrix.trace Mword - gibbsPartition H β‖ := by
      have hkey : gibbsPartition H β =
          Matrix.trace Mword + (gibbsPartition H β - Matrix.trace Mword) := by abel
      have h1 : ‖gibbsPartition H β‖ ≤ ‖Matrix.trace Mword‖ +
          ‖gibbsPartition H β - Matrix.trace Mword‖ := by
        nth_rw 1 [hkey]
        exact norm_add_le (Matrix.trace Mword) (gibbsPartition H β - Matrix.trace Mword)
      have h2 : ‖gibbsPartition H β - Matrix.trace Mword‖ =
          ‖Matrix.trace Mword - gibbsPartition H β‖ :=
        norm_sub_rev (gibbsPartition H β) (Matrix.trace Mword)
      rw [h2] at h1
      exact h1
    have hs_ge : ‖gibbsPartition H β‖ - (D : ℝ) * η ≤ ‖Matrix.trace Mword‖ := by
      nlinarith [hsz]
    have hspos : 0 < ‖Matrix.trace Mword‖ := by nlinarith [hgap]
    intro h
    simp [h] at hspos
  refine ⟨normalizedDensity Mword,
    ⟨gibbsAmplificationRounds p δ, gibbsAmplificationRounds p δ,
      gibbsReadoutShots εro δ⟩, rfl, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · exact normalizedDensity_isDensity Mword hpsd hne
  · exact gibbs_normalized_output_bound H β Mword η hclose hgap
  · intro O
    exact gibbs_observable_bound _ _ O
  · exact gibbsAmplificationRounds_pow_le p δ hp hp1 hδ hδ1
end Qatlib.Concepts.TrotterFormula.GeneralOrder
