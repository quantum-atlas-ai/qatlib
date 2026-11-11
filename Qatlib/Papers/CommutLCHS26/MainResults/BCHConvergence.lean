/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHFormal
import Qatlib.Papers.CommutLCHS26.MainResults.PerturbationDyson
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Convergence of matrix BCH logarithms

This module evaluates matrix power series and proves multiplication, exponential, and logarithm
identities under norm-summability hypotheses. For an exponential word `ws`, the condition `‖z‖ *
suzukiMass ws < log 2` ensures convergence and analyticity of its logarithm and recovers the
product by exponentiation, providing analytic foundations for [AftabAnTrivisa2026].

For palindromic words of skew-adjoint matrices, the logarithm at controlled real times is
skew-adjoint. The construction `strangPerturbation` expresses repeated Strang steps as one
perturbed exponential, with a finite Dyson expansion and a factorial remainder bound.

## Main statements

* `exp_word_log`: Under `‖z‖ * suzukiMass ws < log 2`, exponentiating the evaluated formal word
  logarithm recovers the ordered exponential product.
* `word_log_analyticAt`: The evaluated word logarithm is complex analytic at every `z`
  satisfying `‖z‖ * suzukiMass ws < log 2`.
* `strang_repetitions_eq_exp`: Under the stated strict mass bound, the `q` repeated Strang steps
  equal the exponential of `t • (X + Y) + strangPerturbation X Y q t`.
* `strang_perturbation_expansion`: For skew-adjoint generators under the stated mass bound and
  `p > 0`, repeated Strang steps have the displayed finite Dyson expansion with remainder norm
  at most `‖strangPerturbation X Y q t‖^p / p!`.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHConvergence

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator NNReal ENNReal
open BCHFormal SubdivisionPolynomial
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
set_option warningAsError false

variable {I : Type} [Fintype I] [DecidableEq I]
local instance : NormedAlgebra ℚ (Matrix I I ℂ) := .restrictScalars ℚ ℝ _

/-- The degree-`n` coefficient of the matrix power series `f`, multiplied by `z^n`. -/
def scaled (f : PowerSeries (Matrix I I ℂ)) (z : ℂ) (n : ℕ) : Matrix I I ℂ :=
  z ^ n • PowerSeries.coeff n f

/-- The matrix-valued sum of the scaled coefficients of `f` at `z`, defined using `tsum`. -/
def evaluate (f : PowerSeries (Matrix I I ℂ)) (z : ℂ) : Matrix I I ℂ :=
  ∑' n, scaled f z n

/-- The real sum of the norms of the scaled coefficients of `f` at `z`. -/
def normMass (f : PowerSeries (Matrix I I ℂ)) (z : ℂ) : ℝ :=
  ∑' n, ‖scaled f z n‖

/-- The scaled coefficient of a product is the finite Cauchy convolution of the scaled
coefficients of its factors. -/
theorem scaled_mul (f g : PowerSeries (Matrix I I ℂ)) (z : ℂ) (n : ℕ) :
    scaled (f * g) z n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, scaled f z p.1 * scaled g z p.2 := by
  simp only [scaled, PowerSeries.coeff_mul, Finset.smul_sum, smul_mul_smul_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← pow_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hp]

/-- Norm-summability of the scaled coefficients of two series implies norm-summability for their
product. -/
theorem norm_summable_mul (f g : PowerSeries (Matrix I I ℂ)) (z : ℂ)
    (hf : Summable fun n => ‖scaled f z n‖) (hg : Summable fun n => ‖scaled g z n‖) :
    Summable fun n => ‖scaled (f * g) z n‖ := by
  simpa only [scaled_mul] using! summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg

/-- Evaluation preserves multiplication when both series have norm-summable scaled coefficients
at `z`. -/
theorem evaluate_mul (f g : PowerSeries (Matrix I I ℂ)) (z : ℂ)
    (hf : Summable fun n => ‖scaled f z n‖) (hg : Summable fun n => ‖scaled g z n‖) :
    evaluate (f * g) z = evaluate f z * evaluate g z := by
  simpa only [evaluate, scaled_mul] using!
    (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg).symm

/-- Under norm-summability of both factors, the norm mass of their product is at most the
product of their norm masses. -/
theorem normMass_mul (f g : PowerSeries (Matrix I I ℂ)) (z : ℂ)
    (hf : Summable fun n => ‖scaled f z n‖) (hg : Summable fun n => ‖scaled g z n‖) :
    normMass (f * g) z ≤ normMass f z * normMass g z := by
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hf.norm hg.norm
  have he := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.norm hg.norm
  calc
    _ ≤ ∑' n, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ‖scaled f z p.1‖ * ‖scaled g z p.2‖ := by
      apply (norm_summable_mul f g z hf hg).tsum_le_tsum _ hs.of_norm
      intro n
      rw [scaled_mul]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => norm_mul_le _ _)
    _ = _ := he.symm

/-- The norm mass of the constant identity series equals the norm of the identity matrix. -/
theorem normMass_one (z : ℂ) : normMass (1 : PowerSeries (Matrix I I ℂ)) z = ‖(1 : Matrix I I ℂ)‖ := by
  simp [normMass, scaled, PowerSeries.coeff_one, apply_ite]

/-- The scaled coefficients of the constant identity series are norm-summable at every complex
argument. -/
theorem norm_summable_one (z : ℂ) :
    Summable fun n => ‖scaled (1 : PowerSeries (Matrix I I ℂ)) z n‖ := by
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [scaled, PowerSeries.coeff_one, hn]

/-- Evaluating the constant identity series gives the identity matrix. -/
theorem evaluate_one (z : ℂ) : evaluate (1 : PowerSeries (Matrix I I ℂ)) z = 1 := by
  simp [evaluate, scaled, PowerSeries.coeff_one]

/-- Every natural power of a series with norm-summable scaled coefficients also has
norm-summable scaled coefficients. -/
theorem norm_summable_pow (f : PowerSeries (Matrix I I ℂ)) (z : ℂ)
    (hf : Summable fun n => ‖scaled f z n‖) (r : ℕ) :
    Summable fun n => ‖scaled (f ^ r) z n‖ := by
  induction r with
  | zero => simpa only [pow_zero] using! norm_summable_one z
  | succ r ih => simpa only [pow_succ] using! norm_summable_mul (f ^ r) f z ih hf

/-- For a norm-summable series, the norm mass of its `r`th power is at most the `r`th power of
its norm mass. -/
theorem normMass_pow (f : PowerSeries (Matrix I I ℂ)) (z : ℂ)
    (hf : Summable fun n => ‖scaled f z n‖) (r : ℕ) :
    normMass (f ^ r) z ≤ normMass f z ^ r := by
  induction r with
  | zero =>
    simpa only [pow_zero, normMass_one] using!
      Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one
        (show (1 : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ from by simp)
  | succ r ih =>
    rw [pow_succ, pow_succ]
    exact (normMass_mul (f ^ r) f z (norm_summable_pow f z hf r) hf).trans
      (mul_le_mul_of_nonneg_right ih (tsum_nonneg fun _ => norm_nonneg _))

/-- Evaluation commutes with natural powers for a series with norm-summable scaled coefficients. -/
theorem evaluate_pow (f : PowerSeries (Matrix I I ℂ)) (z : ℂ)
    (hf : Summable fun n => ‖scaled f z n‖) (r : ℕ) :
    evaluate (f ^ r) z = evaluate f z ^ r := by
  induction r with
  | zero => simp [evaluate_one]
  | succ r ih => rw [pow_succ, evaluate_mul _ _ z (norm_summable_pow f z hf r) hf, ih, pow_succ]

/-- If the scaled coefficients of `f` are norm-summable, the factorial-weighted coefficients of
all powers of `f` are jointly norm-summable over power and coefficient indices. -/
theorem norm_summable_exp_coefficients (f : PowerSeries (Matrix I I ℂ)) (z : ℂ)
    (hf : Summable fun n => ‖scaled f z n‖) :
    Summable fun p : ℕ × ℕ => ‖(p.1.factorial : ℂ)⁻¹ • scaled (f ^ p.1) z p.2‖ := by
  have hs (r : ℕ) : Summable fun n => ‖(r.factorial : ℂ)⁻¹ • scaled (f ^ r) z n‖ := by
    simpa only [norm_smul] using!
      (norm_summable_pow f z hf r).mul_left ‖(r.factorial : ℂ)⁻¹‖
  have hmajor : Summable fun r => (normMass f z) ^ r / (r.factorial : ℝ) := by
    simpa only [smul_eq_mul, inv_mul_eq_div] using!
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (normMass f z)).summable
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨hs, hmajor.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) ?_⟩
  intro r
  simp only [norm_smul, norm_inv, Complex.norm_natCast, tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left (normMass_pow f z hf r) (by positivity)).trans_eq
    (by rw [div_eq_mul_inv, mul_comm])

/-- If a power series has zero constant coefficient, the degree-`n` coefficient of its `r`th
power vanishes whenever `n < r`. -/
private theorem high_power_coefficient_zero (f : PowerSeries (Matrix I I ℂ))
    (hf : f.constantCoeff = 0) (n r : ℕ) (hr : n < r) : PowerSeries.coeff n (f ^ r) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hr)
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero r hf)

/-- For a norm-summable series, the exponential of its evaluation equals the iterated sum of
factorial-weighted scaled coefficients of its powers. -/
theorem exp_evaluate_coefficients (f : PowerSeries (Matrix I I ℂ)) (z : ℂ)
    (hf : Summable fun n => ‖scaled f z n‖) :
    NormedSpace.exp (evaluate f z) =
      ∑' n, ∑' r, (r.factorial : ℂ)⁻¹ • scaled (f ^ r) z n := by
  have hd : Summable (fun p : ℕ × ℕ => (p.1.factorial : ℂ)⁻¹ • scaled (f ^ p.1) z p.2) :=
    (norm_summable_exp_coefficients f z hf).of_norm
  have hs (r : ℕ) : (evaluate f z) ^ r = ∑' n, scaled (f ^ r) z n :=
    (evaluate_pow f z hf r).symm
  calc
    _ = ∑' r, (r.factorial : ℂ)⁻¹ • (evaluate f z) ^ r :=
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) _).tsum_eq.symm
    _ = ∑' r, ∑' n, (r.factorial : ℂ)⁻¹ • scaled (f ^ r) z n := by
      apply tsum_congr
      intro r
      rw [hs r, tsum_const_smul'']
    _ = _ := hd.tsum_comm.symm

/-- For a series with constant coefficient one, the factorial-weighted sum of coefficients of
powers of its formal logarithm equals the corresponding scaled coefficient of the original
series. -/
theorem scaled_exp_log_coefficient (f : PowerSeries (Matrix I I ℂ))
    (hf : f.constantCoeff = 1) (z : ℂ) (n : ℕ) :
    (∑' r, (r.factorial : ℂ)⁻¹ • scaled (logSeries f ^ r) z n) = scaled f z n := by
  have hz : (logSeries f).constantCoeff = 0 := by
    simpa only [logSeries, PowerSeries.constantCoeff_mk] using! logCoefficient_zero f
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun r hr => by
    have hnr : n < r := by simp only [Finset.mem_range] at hr; omega
    simp only [scaled, high_power_coefficient_zero (logSeries f) hz n r hnr, smul_zero])]
  simp only [scaled, exp_log_coefficient f hf n, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact smul_comm _ _ _

/-- For a series with constant coefficient one and norm-summable logarithm coefficients at `z`,
exponentiating the evaluated logarithm recovers the evaluated series. -/
theorem exp_evaluate_log (f : PowerSeries (Matrix I I ℂ)) (hf : f.constantCoeff = 1)
    (z : ℂ) (hlog : Summable fun n => ‖scaled (logSeries f) z n‖) :
    NormedSpace.exp (evaluate (logSeries f) z) = evaluate f z := by
  rw [exp_evaluate_coefficients (logSeries f) z hlog]
  exact tsum_congr fun n => scaled_exp_log_coefficient f hf z n

/-- The logarithm-series weight `(-1)^r / (r + 1)` has norm at most one. -/
private theorem log_weight_norm_le (r : ℕ) : ‖(-1 : ℝ) ^ r / (r + 1)‖ ≤ 1 := by
  rw [norm_div, norm_pow, norm_neg, norm_one, one_pow]
  have hr : (1 : ℝ) ≤ ‖(r : ℝ) + 1‖ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) r]
  exact (div_le_one (lt_of_lt_of_le (by norm_num) hr)).mpr hr

/-- If `f - 1` has norm-summable scaled coefficients and norm mass less than one, its logarithm
expansion is jointly norm-summable over power and coefficient indices. -/
theorem norm_summable_log_coefficients (f : PowerSeries (Matrix I I ℂ)) (z : ℂ)
    (hg : Summable fun n => ‖scaled (f - 1) z n‖) (hsmall : normMass (f - 1) z < 1) :
    Summable fun p : ℕ × ℕ =>
      ‖((-1 : ℝ) ^ p.1 / (p.1 + 1)) • scaled ((f - 1) ^ (p.1 + 1)) z p.2‖ := by
  have hnonneg : 0 ≤ normMass (f - 1) z := tsum_nonneg fun _ => norm_nonneg _
  have hs (r : ℕ) : Summable fun n =>
      ‖((-1 : ℝ) ^ r / (r + 1)) • scaled ((f - 1) ^ (r + 1)) z n‖ := by
    simpa only [norm_smul] using!
      (norm_summable_pow (f - 1) z hg (r + 1)).mul_left ‖(-1 : ℝ) ^ r / (r + 1)‖
  have hmajor : Summable fun r => normMass (f - 1) z ^ (r + 1) := by
    simpa only [pow_succ] using!
      (summable_geometric_of_lt_one hnonneg hsmall).mul_right (normMass (f - 1) z)
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨hs, hmajor.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) ?_⟩
  intro r
  simp only [norm_smul, tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left (normMass_pow (f - 1) z hg (r + 1)) (norm_nonneg _)).trans
    (mul_le_of_le_one_left (pow_nonneg hnonneg _) (log_weight_norm_le r))

/-- For a series with constant coefficient one, each scaled logarithm coefficient equals the
weighted sum of the corresponding coefficients of positive powers of `f - 1`. -/
theorem scaled_log_coefficient (f : PowerSeries (Matrix I I ℂ)) (hf : f.constantCoeff = 1)
    (z : ℂ) (n : ℕ) :
    scaled (logSeries f) z n = ∑' r : ℕ,
      ((-1 : ℝ) ^ r / (r + 1)) • scaled ((f - 1) ^ (r + 1)) z n := by
  have hz : (f - 1).constantCoeff = 0 := by simp [hf]
  rw [tsum_eq_sum (s := Finset.range n) (fun r hr => by
    have hnr : n < r + 1 := by simp only [Finset.mem_range] at hr; omega
    simp only [scaled, high_power_coefficient_zero (f - 1) hz n (r + 1) hnr, smul_zero])]
  simp only [scaled, logSeries, PowerSeries.coeff_mk, logCoefficient_finite, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact smul_comm _ _ _

/-- A series with constant coefficient one has norm-summable logarithm coefficients at `z` if `f
- 1` is norm-summable there with norm mass less than one. -/
theorem norm_summable_log (f : PowerSeries (Matrix I I ℂ)) (hf : f.constantCoeff = 1)
    (z : ℂ) (hg : Summable fun n => ‖scaled (f - 1) z n‖)
    (hsmall : normMass (f - 1) z < 1) :
    Summable fun n => ‖scaled (logSeries f) z n‖ := by
  have hd := norm_summable_log_coefficients f z hg hsmall
  apply hd.prod_symm.prod.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  rw [scaled_log_coefficient f hf z n]
  exact norm_tsum_le_tsum_norm (hd.prod_symm.prod_factor n)

/-- Scaling every generator of an exponential word by `z` multiplies its degree-`n` series
coefficient by `z^n`. -/
theorem word_coefficient_complex_scale (ws : List (Matrix I I ℂ)) (z : ℂ) (n : ℕ) :
    suzukiSeries (ws.map (fun X => z • X)) n = z ^ n • suzukiSeries ws n := by
  induction ws generalizing n with
  | nil => cases n <;> simp [suzukiSeries]
  | cons X xs ih =>
    simp only [List.map_cons, suzukiSeries, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [smul_pow, ih, smul_comm ((p.1.factorial : ℝ)⁻¹) (z ^ p.1),
      smul_mul_smul_comm, ← pow_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hp]

/-- The ordered product of the matrix exponentials `exp (z • X)` over the generators in `ws`. -/
def complexWord (ws : List (Matrix I I ℂ)) (z : ℂ) : Matrix I I ℂ :=
  (ws.map (fun X => NormedSpace.exp (z • X))).prod

/-- The scaled coefficients of the exponential word series sum to `complexWord ws z`. -/
theorem complexWord_hasSum (ws : List (Matrix I I ℂ)) (z : ℂ) :
    HasSum (fun n => scaled (wordSeries ws) z n) (complexWord ws z) := by
  have h := suzukiSeries_hasSum (ws.map (fun X => z • X)) 1
  simpa only [word_coefficient_complex_scale, one_pow, one_smul, scaled, wordSeries,
    PowerSeries.coeff_mk, complexWord, suzukiExponentialWord, List.map_map,
    Function.comp_def] using! h

/-- The norm of the degree-`n` scaled word coefficient is at most `(‖z‖ * suzukiMass ws)^n /
n!`. -/
theorem norm_scaled_word_le (ws : List (Matrix I I ℂ)) (z : ℂ) (n : ℕ) :
    ‖scaled (wordSeries ws) z n‖ ≤ (‖z‖ * suzukiMass ws) ^ n / (n.factorial : ℝ) := by
  simp only [scaled, wordSeries, PowerSeries.coeff_mk, norm_smul, norm_pow]
  calc
    _ ≤ ‖z‖ ^ n * (suzukiMass ws ^ n / (n.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (suzukiSeries_norm_le ws n) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- The exponential word series minus one is norm-summable, with norm mass at most `exp (‖z‖ *
suzukiMass ws) - 1`. -/
theorem word_sub_one_bound (ws : List (Matrix I I ℂ)) (z : ℂ) :
    (Summable fun n => ‖scaled (wordSeries ws - 1) z n‖) ∧
    normMass (wordSeries ws - 1) z ≤ Real.exp (‖z‖ * suzukiMass ws) - 1 := by
  let a := ‖z‖ * suzukiMass ws
  have hexp : HasSum (fun n : ℕ => a ^ n / (n.factorial : ℝ)) (Real.exp a) := by
    simpa only [smul_eq_mul, inv_mul_eq_div, ← Real.exp_eq_exp_ℝ] using!
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a
  have hmajor := hexp.sub (hasSum_ite_eq (0 : ℕ) (1 : ℝ))
  have hbound (n : ℕ) : ‖scaled (wordSeries ws - 1) z n‖ ≤
      a ^ n / (n.factorial : ℝ) - (if n = 0 then 1 else 0) := by
    cases n with
    | zero => simp [scaled, wordSeries]
    | succ n =>
      simpa only [scaled, map_sub, PowerSeries.coeff_one, Nat.succ_ne_zero, if_false,
        sub_zero] using! norm_scaled_word_le ws z (n + 1)
  have hs := hmajor.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  exact ⟨hs, (hs.tsum_le_tsum hbound hmajor.summable).trans_eq hmajor.tsum_eq⟩

/-- The logarithm of an exponential word has norm-summable scaled coefficients whenever `‖z‖ *
suzukiMass ws < log 2`. -/
theorem word_log_norm_summable (ws : List (Matrix I I ℂ)) (z : ℂ)
    (hz : ‖z‖ * suzukiMass ws < Real.log 2) :
    Summable fun n => ‖scaled (logSeries (wordSeries ws)) z n‖ := by
  have hb := word_sub_one_bound ws z
  have he : Real.exp (‖z‖ * suzukiMass ws) < 2 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mp hz
  exact norm_summable_log (wordSeries ws) (by simp [wordSeries]) z hb.1
    (lt_of_le_of_lt hb.2 (by linarith))

/-- Under `‖z‖ * suzukiMass ws < log 2`, exponentiating the evaluated formal word logarithm
recovers the ordered exponential product. -/
theorem exp_word_log (ws : List (Matrix I I ℂ)) (z : ℂ)
    (hz : ‖z‖ * suzukiMass ws < Real.log 2) :
    NormedSpace.exp (evaluate (logSeries (wordSeries ws)) z) = complexWord ws z := by
  rw [exp_evaluate_log (wordSeries ws) (by simp [wordSeries]) z (word_log_norm_summable ws z hz)]
  exact (complexWord_hasSum ws z).tsum_eq

section Analytic

local instance (n : ℕ) : Norm (ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ) (Matrix I I ℂ)) :=
  ContinuousMultilinearMap.hasOpNorm'

/-- The formal multilinear series associated with the logarithm coefficients of the exponential
word. -/
def analyticSeries (ws : List (Matrix I I ℂ)) : FormalMultilinearSeries ℂ ℂ (Matrix I I ℂ) :=
  fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (logCoefficient (wordSeries ws) n)

/-- The sum function of `analyticSeries ws` equals evaluation of the formal word logarithm. -/
theorem analyticSeries_sum (ws : List (Matrix I I ℂ)) :
    (analyticSeries ws).sum = evaluate (logSeries (wordSeries ws)) := by
  funext z
  apply tsum_congr
  intro n
  simp only [analyticSeries, ContinuousMultilinearMap.mkPiRing_apply,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, scaled, logSeries,
    PowerSeries.coeff_mk]

/-- Summability of the radius-weighted logarithm coefficient norms gives that radius as a lower
bound for `analyticSeries ws`. -/
theorem analyticSeries_radius_of_summable (ws : List (Matrix I I ℂ)) (r : ℝ≥0)
    (hs : Summable fun n => (r : ℝ) ^ n * ‖logCoefficient (wordSeries ws) n‖) :
    (r : ℝ≥0∞) ≤ (analyticSeries ws).radius := by
  have hc (n : ℕ) : ‖analyticSeries ws n‖ = ‖logCoefficient (wordSeries ws) n‖ :=
    ContinuousMultilinearMap.norm_mkPiRing _
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  apply hs.congr
  intro n
  calc
    _ = (r : ℝ) ^ n * ‖analyticSeries ws n‖ :=
      congrArg (fun v : ℝ => (r : ℝ) ^ n * v) (hc n).symm
    _ = _ := mul_comm _ _

/-- If `r * suzukiMass ws < log 2`, the radius of the formal multilinear logarithm series is at
least `r`. -/
theorem analyticSeries_radius (ws : List (Matrix I I ℂ)) (r : ℝ≥0)
    (hr : (r : ℝ) * suzukiMass ws < Real.log 2) :
    (r : ℝ≥0∞) ≤ (analyticSeries ws).radius := by
  have hrz : ‖((r : ℝ) : ℂ)‖ = (r : ℝ) := by
    exact (Complex.norm_real (r : ℝ)).trans (Real.norm_of_nonneg r.2)
  have hs := word_log_norm_summable ws ((r : ℝ) : ℂ) (by rw [hrz]; exact hr)
  apply analyticSeries_radius_of_summable ws r
  simpa only [scaled, logSeries, PowerSeries.coeff_mk, norm_smul, norm_pow, hrz] using! hs

/-- The evaluated word logarithm is complex analytic at every `z` satisfying `‖z‖ * suzukiMass
ws < log 2`. -/
theorem word_log_analyticAt (ws : List (Matrix I I ℂ)) (z : ℂ)
    (hz : ‖z‖ * suzukiMass ws < Real.log 2) :
    AnalyticAt ℂ (evaluate (logSeries (wordSeries ws))) z := by
  let d := (Real.log 2 - ‖z‖ * suzukiMass ws) / (2 * (suzukiMass ws + 1))
  have hm : 0 ≤ suzukiMass ws := by
    apply List.sum_nonneg
    intro r hr
    rcases List.mem_map.mp hr with ⟨X, _, rfl⟩
    exact norm_nonneg _
  have hd : 0 < d := div_pos (sub_pos.mpr hz) (by positivity)
  have he : d * (2 * (suzukiMass ws + 1)) = Real.log 2 - ‖z‖ * suzukiMass ws := by
    dsimp only [d]
    exact div_mul_cancel₀ _ (by positivity)
  let r : ℝ≥0 := ⟨‖z‖ + d, by positivity⟩
  have hr : (r : ℝ) * suzukiMass ws < Real.log 2 := by
    change (‖z‖ + d) * suzukiMass ws < Real.log 2
    nlinarith
  have hmem : z ∈ Metric.eball (0 : ℂ) (analyticSeries ws).radius := by
    apply lt_of_lt_of_le _ (analyticSeries_radius ws r hr)
    rw [edist_dist, dist_zero_right, ENNReal.ofReal_lt_coe_iff (norm_nonneg z)]
    change ‖z‖ < ‖z‖ + d
    linarith
  have ha := (analyticSeries ws).analyticOnNhd z hmem
  exact (analyticSeries_sum ws) ▸ ha

end Analytic

/-- For a palindromic word of skew-adjoint generators and real `t` satisfying the strict `log 2`
mass bound, the logarithm series is norm-summable and its sum is skew-adjoint. -/
theorem real_word_log_skew (ws : List (Matrix I I ℂ)) (hws : ws.reverse = ws)
    (hskew : ∀ X ∈ ws, Xᴴ = -X) (t : ℝ)
    (ht : |t| * suzukiMass ws < Real.log 2) :
    (Summable fun n => ‖scaled (logSeries (wordSeries ws)) (t : ℂ) n‖) ∧
    (evaluate (logSeries (wordSeries ws)) (t : ℂ))ᴴ =
      -evaluate (logSeries (wordSeries ws)) (t : ℂ) := by
  refine ⟨word_log_norm_summable ws (t : ℂ) (by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using! ht), ?_⟩
  have hs (n : ℕ) : (scaled (logSeries (wordSeries ws)) (t : ℂ) n)ᴴ =
      -scaled (logSeries (wordSeries ws)) (t : ℂ) n := by
    simp only [scaled, logSeries, PowerSeries.coeff_mk, ← Complex.ofReal_pow,
      Complex.coe_smul, Matrix.conjTranspose_smul, star_trivial,
      symmetric_logCoefficient_skew ws hws hskew, smul_neg]
  simp only [evaluate, Matrix.conjTranspose_tsum, hs, tsum_neg]

/-- The difference between `q` times the Strang logarithm evaluated at `t / q` and the target
generator `t • (X + Y)`. -/
def strangPerturbation (X Y : Matrix I I ℂ) (q : ℕ) (t : ℝ) : Matrix I I ℂ :=
  (q : ℝ) • evaluate (logSeries (strangSeries X Y)) ((t / q : ℝ) : ℂ) - t • (X + Y)

/-- For skew-adjoint `X` and `Y`, the Strang perturbation is skew-adjoint under the stated
strict mass bound at `t / q`. -/
theorem strangPerturbation_skew (X Y : Matrix I I ℂ)
    (hX : Xᴴ = -X) (hY : Yᴴ = -Y) (q : ℕ) (t : ℝ)
    (ht : |t / q| * suzukiMass [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X] < Real.log 2) :
    (strangPerturbation X Y q t)ᴴ = -strangPerturbation X Y q t := by
  have hs := real_word_log_skew [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X] rfl (by
    intro A hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl <;> simp [Matrix.conjTranspose_smul, hX, hY]) (t / q) ht
  have hlog := hs.2
  change (evaluate (logSeries (strangSeries X Y)) ((t / q : ℝ) : ℂ))ᴴ =
    -evaluate (logSeries (strangSeries X Y)) ((t / q : ℝ) : ℂ) at hlog
  simp only [strangPerturbation, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    star_trivial, hlog, Matrix.conjTranspose_add, hX, hY, smul_neg, smul_add]
  abel

/-- Under the stated strict mass bound, the `q` repeated Strang steps equal the exponential of
`t • (X + Y) + strangPerturbation X Y q t`. -/
theorem strang_repetitions_eq_exp (X Y : Matrix I I ℂ) (q : ℕ) (t : ℝ)
    (ht : |t / q| * suzukiMass [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X] < Real.log 2) :
    suzukiExponentialWord [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X] (t / q) ^ q =
      NormedSpace.exp (t • (X + Y) + strangPerturbation X Y q t) := by
  have he := exp_word_log [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X]
    ((t / q : ℝ) : ℂ) (by simpa only [Complex.norm_real, Real.norm_eq_abs] using! ht)
  have hw : complexWord [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X] ((t / q : ℝ) : ℂ) =
      suzukiExponentialWord [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X] (t / q) := by
    simp only [complexWord, suzukiExponentialWord, Complex.coe_smul]
  rw [hw] at he
  calc
    _ = NormedSpace.exp (evaluate (logSeries (strangSeries X Y)) ((t / q : ℝ) : ℂ)) ^ q := by
      exact (congrArg (fun A : Matrix I I ℂ => A ^ q) he).symm
    _ = NormedSpace.exp (q • evaluate (logSeries (strangSeries X Y)) ((t / q : ℝ) : ℂ)) :=
      (NormedSpace.exp_nsmul q _).symm
    _ = _ := by
      congr 1
      rw [← Nat.cast_smul_eq_nsmul ℝ]
      simp only [strangPerturbation]
      abel

/-- For skew-adjoint generators under the stated mass bound and `p > 0`, repeated Strang steps
have the displayed finite Dyson expansion with remainder norm at most `‖strangPerturbation X
Y q t‖^p / p!`. -/
theorem strang_perturbation_expansion (X Y : Matrix I I ℂ)
    (hX : Xᴴ = -X) (hY : Yᴴ = -Y) (q : ℕ) (t : ℝ)
    (ht : |t / q| * suzukiMass [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X] < Real.log 2)
    (p : ℕ) (hp : 0 < p) :
    let A := t • (X + Y)
    let B := strangPerturbation X Y q t
    suzukiExponentialWord [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X] (t / q) ^ q =
      NormedSpace.exp A + (∑ j ∈ Finset.range (p - 1), PerturbationDyson.term A B (j + 1) 1) +
        PerturbationDyson.remainder A B p 1 ∧
      ‖PerturbationDyson.remainder A B p 1‖ ≤ ‖B‖ ^ p / (p.factorial : ℝ) := by
  have hA : (t • (X + Y))ᴴ = -(t • (X + Y)) := by
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add, hX, hY,
      smul_add, smul_neg]
    abel
  have h := PerturbationDyson.unit_interval_expansion (t • (X + Y))
    (strangPerturbation X Y q t) hA (strangPerturbation_skew X Y hX hY q t ht) p hp
  (try dsimp only)
  rw [← strang_repetitions_eq_exp X Y q t ht] at h
  exact h

end Qatlib.Papers.CommutLCHS26.MainResults.BCHConvergence
