/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Ln2SegmentationCorrectedStat
import Qatlib.Concepts.CoherentSim.ResetDiscard.ResetDiscardSegmentationCorrectedSimu
import Qatlib.Concepts.CoherentSim.ResetDiscard.Ln2Segmentation

/-!
# Amplified log-two segmentation

This module bounds the Taylor remainder and scale defect for segments of norm-duration at most
`log 2`. `ln2Segmentation` proves the corrected reset-and-discard simulation guarantee using
amplified steps and the prescribed tail budget, in the framework of [BerryEtAl2015Taylor].

## Main statements

* `truncatedSegment_ln2_error`: The exponential-tail bound for one Taylor segment.
* `oaa_cubic_small_error`: A small-error cubic amplification estimate.
* `ln2Segmentation`: The corrected total trace-norm guarantee.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.CoherentSim.FactorialTaylor

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace Qatlib.Concepts.CoherentSim.ResetDiscard
open Matrix
open scoped Classical ComplexOrder Matrix.Norms.L2Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The truncated exponential mass at `log 2` plus its remaining factorial tail equals two. -/
theorem ln2Scale_tail_identity (K : ℕ) :
    ln2Scale K+(∑' j : ℕ, Real.log 2^(K+1+j)/((K+1+j).factorial:ℝ))=2 := by
  have hs := (Real.summable_pow_div_factorial (Real.log 2)).sum_add_tsum_nat_add (K+1)
  have he : (∑' n : ℕ, Real.log 2^n/(n.factorial:ℝ)) = 2 := by
    have hh : (∑' n : ℕ, Real.log 2^n/(n.factorial:ℝ)) = Real.exp (Real.log 2) := by
      rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum ℝ]
      congr 1
      funext n
      simp [smul_eq_mul,div_eq_mul_inv,mul_comm]
    rwa [Real.exp_log (by norm_num)] at hh
  rw [he] at hs
  simpa only [ln2Scale,Nat.add_comm] using! hs

/-- For nonnegative duration with `τ * ‖H‖ ≤ log 2`, the Taylor-segment norm error is bounded by
the exponential tail at `log 2`. -/
theorem truncatedSegment_ln2_error (H : Matrix I I ℂ) (τ : ℝ) (K : ℕ)
    (hτ : 0 ≤ τ) (hsize : τ*‖H‖ ≤ Real.log 2) :
    ‖truncatedSegment H τ K-HamiltonianEvolution H τ‖ ≤
      ∑' j : ℕ, Real.log 2^(K+1+j)/((K+1+j).factorial:ℝ) := by
  let A := (-Complex.I*(τ:ℂ)) • H
  let f : ℕ → Matrix I I ℂ := fun n => (n.factorial:ℂ)⁻¹ • A^n
  have hA : ‖A‖ ≤ Real.log 2 := by
    dsimp [A]
    rw [norm_smul,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hτ]
    exact hsize
  have hf : Summable f := NormedSpace.expSeries_summable' A
  have hfn : Summable (fun n => ‖f n‖) := NormedSpace.norm_expSeries_summable' A
  have ht : ∑' n, f n = NormedSpace.exp A := (NormedSpace.exp_series_hasSum_exp' A).tsum_eq
  have hp : truncatedSegment H τ K = ∑ n ∈ Finset.range (K+1), f n := by
    unfold truncatedSegment
    apply Finset.sum_congr rfl
    intro n _
    dsimp [f,A]
    rw [smul_pow,smul_smul]
    congr 1
    ring
  have hre : NormedSpace.exp A-(∑ n ∈ Finset.range (K+1),f n) = ∑' n, f (n+(K+1)) := by
    have hs := hf.sum_add_tsum_nat_add (K+1)
    rw [ht] at hs
    exact (eq_sub_of_add_eq' hs).symm
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hg := (factorialTaylor_tail (Real.log 2) K hl (by linarith [Real.log_two_lt_d9])).1
  have hnf : Summable (fun n => ‖f (n+(K+1))‖) := (summable_nat_add_iff _).2 hfn
  rw [hp,norm_sub_rev]
  change ‖NormedSpace.exp A-∑ n ∈ Finset.range (K+1), f n‖ ≤ _
  rw [hre]
  apply (norm_tsum_le_tsum_norm hnf).trans
  have hg' : Summable (fun n : ℕ => Real.log 2^(n+(K+1))/((n+(K+1)).factorial:ℝ)) := by
    simpa only [Nat.add_comm] using! hg
  have hle : ∀ n : ℕ, ‖f (n+(K+1))‖ ≤ Real.log 2^(n+(K+1))/((n+(K+1)).factorial:ℝ) := by
    intro n
    dsimp [f]
    rw [norm_smul,norm_inv,Complex.norm_natCast]
    calc
      _ ≤ ((n+(K+1)).factorial:ℝ)⁻¹*‖A‖^(n+(K+1)) :=
        mul_le_mul_of_nonneg_left (norm_pow_le' A (by omega)) (by positivity)
      _ ≤ ((n+(K+1)).factorial:ℝ)⁻¹*Real.log 2^(n+(K+1)) := by gcongr
      _ = _ := by ring
  have hh := hnf.tsum_le_tsum hle hg'
  simpa only [Nat.add_comm] using! hh

/-- For `s ≥ 1` within `δ ≤ 1` of two, the scalar cubic amplification defect is at most `4 * δ`. -/
theorem oaa_scale_defect_four (s δ : ℝ) (hs : 1 ≤ s) (hd : |s-2| ≤ δ) (hδ : δ ≤ 1) :
    |3/s-4/s^3-1| ≤ 4*δ := by
  have hspos : 0 < s := by linarith
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hd
  have hs3 : s ≤ 3 := by have hh := (abs_le.mp hd).2; linarith
  have hpow : 1 ≤ s^3 := by simpa using! pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hs 3
  have he : 3/s-4/s^3-1 = -((s-2)^2*(s+1)/s^3) := by field_simp; ring
  rw [he,abs_neg,abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (pow_pos hspos 3)).mpr
  have hsq : (s-2)^2 ≤ |s-2| := by
    have hh : |s-2| ≤ 1 := hd.trans hδ
    nlinarith [sq_abs (s-2),abs_nonneg (s-2)]
  calc
    _ ≤ (s-2)^2*4 := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    _ ≤ |s-2| *4 := mul_le_mul_of_nonneg_right hsq (by norm_num)
    _ ≤ δ*4 := mul_le_mul_of_nonneg_right hd (by norm_num)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 4*δ)]

/-- If `X` is within `δ ≤ 1 / 8` of a unitary and `s ≥ 3 / 2` is within `δ` of two, the cubic
amplified operator has error at most `13 * δ`. -/
theorem oaa_cubic_small_error (X U : Matrix I I ℂ) (s δ : ℝ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hX : ‖X-U‖ ≤ δ)
    (hs : 3/2 ≤ s) (hd : |s-2| ≤ δ) (hδ : δ ≤ 1/8) :
    ‖((3/s:ℝ):ℂ) • X-((4/s^3:ℝ):ℂ) • (X*Xᴴ*X)-U‖ ≤ 13*δ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hX
  have hspos : 0 < s := by linarith
  have ha : ‖((3/s:ℝ):ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact (div_le_iff₀ hspos).mpr (by linarith)
  have hb : ‖((4/s^3:ℝ):ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ (pow_pos hspos 3)).mpr
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/2) hs 3
    norm_num at hh
    linarith only [hh]
  have hc : ‖((3/s:ℝ):ℂ)-((4/s^3:ℝ):ℂ)-1‖ ≤ 4*δ := by
    rw [← Complex.ofReal_sub,← Complex.ofReal_one,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs]
    exact oaa_scale_defect_four s δ (by linarith) hd (by linarith)
  have hcoef : ‖((3/s:ℝ):ℂ)‖+‖((4/s^3:ℝ):ℂ)‖*(3+3*δ+δ^2) ≤ 9 := by
    have hh := add_le_add ha (mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 3+3*δ+δ^2))
    have hsq : δ^2 ≤ (1/8:ℝ)^2 := pow_le_pow_left₀ hδ0 hδ 2
    norm_num at hsq
    nlinarith only [hh,hsq,hδ]
  have hh := l2_norm_scaled_cubic_sub_unitary_le hU hX ((3/s:ℝ):ℂ) ((4/s^3:ℝ):ℂ)
  have hm := mul_le_mul_of_nonneg_right hcoef hδ0
  exact hh.trans (by linarith only [hm,hc])

/-- The `n`th power of Hamiltonian evolution for duration `τ` equals evolution for duration `n *
τ`. -/
private theorem hamiltonianEvolution_power (H : Matrix I I ℂ) (τ : ℝ) (n : ℕ) :
    (HamiltonianEvolution H τ)^n = HamiltonianEvolution H ((n:ℝ)*τ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,ih,← hamiltonianEvolution_add]
    congr 1
    push_cast
    ring

/-- The corrected log-two segmentation property holds: repeated amplified reset-and-discard
Taylor steps meet the stated total trace-norm tolerance under its norm and tail assumptions.
See [BerryEtAl2015Taylor]. -/
theorem ln2Segmentation : Ln2SegmentationCorrected := by
  intro I _ _ H t ε Λ K J _ _ W j₀ hH ht hnorm hΛ hK hε hε1 henc htail ρ hρ htr
  let r := max 1 (Nat.ceil (Λ*t/Real.log 2))
  let τ := t/(r:ℝ)
  let δ := ∑' j : ℕ, Real.log 2^(K+1+j)/((K+1+j).factorial:ℝ)
  let X := truncatedSegment H τ K
  let U := HamiltonianEvolution H τ
  have hrNat : 1 ≤ r := le_max_left _ _
  have hr : (1:ℝ) ≤ r := by exact_mod_cast hrNat
  have hrpos : (0:ℝ) < r := by linarith only [hr]
  have hτ : 0 ≤ τ := div_nonneg ht hrpos.le
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : Λ*t/Real.log 2 ≤ (r:ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 (Nat.ceil (Λ*t/Real.log 2))))
  have hsize : τ*‖H‖ ≤ Real.log 2 := by
    have hh := (div_le_iff₀ hlog).mp hceil
    have hm := mul_le_mul_of_nonneg_left hnorm ht
    dsimp [τ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hrpos).mpr
    nlinarith only [hh,hm]
  have hδ0 : 0 ≤ δ := tsum_nonneg (fun _ => by positivity)
  have hδb : δ ≤ ε/(69*(r:ℝ)) := htail
  have hδ : δ ≤ 1/8 := by
    apply hδb.trans
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 69*(r:ℝ))).mpr
    nlinarith only [hε1,hr]
  have hs : 3/2 ≤ ln2Scale K := (ln2Scale_gt_three_halves K (by omega)).le
  have hsδ : |ln2Scale K-2| ≤ δ := by
    have hh := ln2Scale_tail_identity K
    change ln2Scale K+δ=2 at hh
    rw [show ln2Scale K-2 = -δ by linarith only [hh],abs_neg,abs_of_nonneg hδ0]
  have hU : U ∈ Matrix.unitaryGroup I ℂ := hamiltonianEvolution_unitary hH τ
  have hX : ‖X-U‖ ≤ δ := truncatedSegment_ln2_error H τ K hτ hsize
  have hc : ‖BlockCorner (ObliviousAmplitudeAmplification (FiberProjector j₀) W) j₀-U‖ ≤ 13*δ := by
    have hw : IsBlockEncoding W j₀ X (ln2Scale K) := henc
    rw [resetDiscardStepCorrected_corner W j₀ X (ln2Scale K) hw]
    exact oaa_cubic_small_error X U (ln2Scale K) δ hU hX hs hsδ hδ
  have hh := resetDiscardStepCorrected_iterate_error W j₀ U (13*δ) henc.1 hU hc ρ hρ htr r
  have hpow : U^r=HamiltonianEvolution H t := by
    rw [hamiltonianEvolution_power]
    dsimp [τ]
    rw [mul_div_cancel₀ t hrpos.ne']
  rw [← Matrix.conjTranspose_pow,hpow] at hh
  change Matrix.traceNorm ((ResetDiscardStepCorrected W j₀)^[r] ρ-
      HamiltonianEvolution H t*ρ*(HamiltonianEvolution H t)ᴴ) ≤ ε
  apply hh.trans
  have hb := (le_div_iff₀ (by positivity : (0:ℝ) < 69*(r:ℝ))).mp hδb
  have hn : 0 ≤ (r:ℝ)*δ := mul_nonneg hrpos.le hδ0
  nlinarith only [hb,hn]
end Qatlib.Concepts.CoherentSim.ResetDiscard
