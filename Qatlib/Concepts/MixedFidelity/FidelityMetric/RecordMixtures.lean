/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.RankOneTraceNormEquality
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.DiamondStabilization
import Qatlib.Concepts.HspRecovery.SieveLaw.MixedSelectivePerturbation
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.RecordMixtureTraceError
open Matrix
open scoped ComplexOrder

variable {R I : Type} [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

theorem density_distance (σ ρ : Matrix I I ℂ) (hσ : σ.PosSemidef) (hρ : ρ.PosSemidef)
    (hσt : Matrix.trace σ=1) (hρt : Matrix.trace ρ=1) : Matrix.traceNorm (σ-ρ)/2 ≤ 1 := by
  have h := Matrix.traceNorm_add_le σ (-ρ)
  rw [Matrix.traceNorm_neg,Qatlib.Concepts.HspRecovery.SieveLaw.posSemidef_traceNorm_eq_re hσ,Qatlib.Concepts.HspRecovery.SieveLaw.posSemidef_traceNorm_eq_re hρ,hσt,hρt] at h
  change Matrix.traceNorm (σ+-ρ) ≤ 1+1 at h
  rw [← sub_eq_add_neg] at h
  linarith

omit [DecidableEq R] in

theorem weighted_error (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (hs : ∑ r, w r=1)
    (σ : R → Matrix I I ℂ) (ρ : Matrix I I ℂ) :
    Matrix.traceNorm ((∑ r : R, ((w r : ℝ) : ℂ) • σ r)-ρ)/2 ≤
      ∑ r : R, w r*(Matrix.traceNorm (σ r-ρ)/2) := by
  have ht : (∑ r : R, ((w r : ℝ) : ℂ) • ρ)=ρ := by
    rw [← Finset.sum_smul,← Complex.ofReal_sum,hs,Complex.ofReal_one,one_smul]
  have hd : (∑ r : R, ((w r : ℝ) : ℂ) • σ r)-ρ=
      ∑ r : R, ((w r : ℝ) : ℂ) • (σ r-ρ) := by
    simp only [smul_sub,Finset.sum_sub_distrib,ht]
  rw [hd]
  have h :=
      Qatlib.Concepts.MixedFidelity.FidelityMetric.traceNorm_weighted_sum_le w hw
      (fun r => σ r-ρ)
  calc
    _ ≤ (∑ r : R, w r*Matrix.traceNorm (σ r-ρ))/2 := div_le_div_of_nonneg_right h (by norm_num)
    _=_ := by rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro r _; ring

theorem bad_record_budget (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (hs : ∑ r, w r=1)
    (σ : R → Matrix I I ℂ) (hσ : ∀ r, (σ r).PosSemidef ∧ Matrix.trace (σ r)=1)
    (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef ∧ Matrix.trace ρ=1)
    (good : Finset R) (η ζ : ℝ) (hη : 0 ≤ η)
    (hgood : ∀ r ∈ good, Matrix.traceNorm (σ r-ρ)/2 ≤ η)
    (hbad : (∑ r : R, if r ∈ good then 0 else w r) ≤ ζ) :
    Matrix.traceNorm ((∑ r : R, ((w r : ℝ) : ℂ) • σ r)-ρ)/2 ≤ η+ζ := by
  apply (Qatlib.Concepts.MixedFidelity.FidelityMetric.RecordMixtureTraceError.weighted_error w hw hs σ ρ).trans
  have hp (r : R) : w r*(Matrix.traceNorm (σ r-ρ)/2) ≤ w r*η+(if r ∈ good then 0 else w r) := by
    by_cases hr : r ∈ good
    · rw [if_pos hr,add_zero]
      exact mul_le_mul_of_nonneg_left (hgood r hr) (hw r)
    · rw [if_neg hr]
      have hd :=
          Qatlib.Concepts.MixedFidelity.FidelityMetric.RecordMixtureTraceError.density_distance
          (σ r) ρ (hσ r).1 hρ.1 (hσ r).2 hρ.2
      have he := mul_le_mul_of_nonneg_left hd (hw r)
      have hn := mul_nonneg (hw r) hη
      nlinarith
  have h := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hp r)
  rw [Finset.sum_add_distrib,← Finset.sum_mul,hs,one_mul] at h
  linarith

end Qatlib.Concepts.MixedFidelity.FidelityMetric.RecordMixtureTraceError
