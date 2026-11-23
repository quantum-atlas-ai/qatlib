/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MonteCarloMean.LayeredMean.LayeredQuantumMean
public import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Layered estimation for a general second moment

[Montanaro2015], Lemma 4 gives an error window of `ε * (‖v(A)‖₂ + 1)^2` for nonnegative payoffs.
The underlying layered estimator
(`Qatlib.Concepts.MonteCarloMean.LayeredMean.layered_quantum_mean_actual_guarantee`)
uses the normalized second-moment bound `E[v(A)^2] ≤ 1`.

The general second-moment bound rescales the payoff by `1 / (c + 1)`. A payoff with second moment
at most `c` has normalized second moment at most one, so the locked guarantee applies with accuracy
`(c + 1) * 2^(-k)`; once `2^(-k) ≤ ε` and `k ≥ 3`, the scaled estimator reaches additive accuracy
`ε * (c + 1)` with probability at least `4/5`.

## Main statements

* `layered_scaled_second_moment_guarantee`: the scaled layered estimator satisfies
  `|(c + 1) * layerEstimate - μ| ≤ ε * (c + 1)` with probability at least `4/5`.
* `layered_source_l2_scale_guarantee`: the source constant `(‖v(A)‖₂ + 1)²`, with
  `‖v(A)‖₂ = sqrt (∑ i, BornProb ... i * f i ^ 2)`, is reached with the same `4/5` success
  probability.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.MCMontanaro15.MonteCarlo

open Matrix
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open scoped BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

/-- A payoff whose second moment is at most `c` can be rescaled so that the dyadic layered
estimator of [Montanaro2015], Algorithm 2 reaches additive accuracy `ε * (c + 1)` with
probability at least `4/5`, provided `k ≥ 3` and `2^(-k) ≤ ε`. -/
theorem layered_scaled_second_moment_guarantee (k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i) (c ε : ℝ) (hc : 0 ≤ c)
    (hk : 3 ≤ k) (_hε0 : 0 < ε) (hε : (2 : ℝ) ^ (-((k : ℤ))) ≤ ε)
    (hE : (∑ i, BornProb (ApplyGate A (Ket j)) i * (f i) ^ 2) ≤ c) :
    let μ := ∑ i, BornProb (ApplyGate A (Ket j)) i * f i
    (∑ ω with |(c + 1) * layerEstimate k ω - μ| ≤ ε * (c + 1),
        (layerLaw k A j (fun i => f i / (c + 1)) hA
          (fun _ => div_nonneg (hf _) (by positivity))).prob ω)
      ≥ 4 / 5 := by
  classical
  intro μ
  set g : I → ℝ := fun i => f i / (c + 1) with hgdef
  have hc1 : (0 : ℝ) < c + 1 := by linarith
  have hg : ∀ i, 0 ≤ g i := fun i => div_nonneg (hf i) hc1.le
  have hsecond : (∑ i, BornProb (ApplyGate A (Ket j)) i * (g i) ^ 2) ≤ 1 := by
    have hpow : (0 : ℝ) < (c + 1) ^ 2 := by positivity
    have h1 : (∑ i, BornProb (ApplyGate A (Ket j)) i * (g i) ^ 2)
        = (∑ i, BornProb (ApplyGate A (Ket j)) i * (f i) ^ 2) / (c + 1) ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only [g]
      field_simp
    rw [h1]
    have hstep : (∑ i, BornProb (ApplyGate A (Ket j)) i * (f i) ^ 2) / (c + 1) ^ 2
        ≤ c / (c + 1) ^ 2 := by gcongr
    refine le_trans hstep ?_
    rw [div_le_one hpow]
    nlinarith [hc, sq_nonneg c]
  have hguar := layered_quantum_mean_actual_guarantee k (by omega) A j g hA hg hsecond
  simp only [] at hguar
  have hle_eighth : (2 : ℝ) ^ (-((k : ℤ))) ≤ 1 / 8 := by
    rw [neg_pow_half_eq k]
    calc ((1 : ℝ) / 2) ^ k ≤ ((1 : ℝ) / 2) ^ 3 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ = 1 / 8 := by norm_num
  have hscale : 4 / 5 ≤ 1 - (2 : ℝ) ^ (-((k : ℤ))) := by linarith
  have hμeq : μ = (c + 1) * (∑ i, BornProb (ApplyGate A (Ket j)) i * g i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [g]
    field_simp
  have hsub : SignedMean.mass (layerLaw k A j g hA hg)
        (fun ω => |layerEstimate k ω - ∑ i, BornProb (ApplyGate A (Ket j)) i * g i|
          ≤ (2 : ℝ) ^ (-((k : ℤ))))
      ≤ SignedMean.mass (layerLaw k A j g hA hg)
        (fun ω => |(c + 1) * layerEstimate k ω - μ| ≤ ε * (c + 1)) := by
    refine SignedMean.mass_mono _ (fun ω hle => ?_)
    have hstep : |(c + 1) * layerEstimate k ω - μ|
        = (c + 1) * |layerEstimate k ω - ∑ i, BornProb (ApplyGate A (Ket j)) i * g i| := by
      rw [hμeq, ← mul_sub, abs_mul, abs_of_pos hc1]
    rw [hstep]
    refine le_trans (mul_le_mul_of_nonneg_left hle hc1.le) ?_
    calc (c + 1) * (2 : ℝ) ^ (-((k : ℤ))) ≤ (c + 1) * ε :=
          mul_le_mul_of_nonneg_left hε hc1.le
      _ = ε * (c + 1) := by ring
  have htarget : (∑ ω with |(c + 1) * layerEstimate k ω - μ| ≤ ε * (c + 1),
        (layerLaw k A j g hA hg).prob ω)
      = SignedMean.mass (layerLaw k A j g hA hg)
        (fun ω => |(c + 1) * layerEstimate k ω - μ| ≤ ε * (c + 1)) := rfl
  rw [htarget]
  have hguar' : (∑ ω with |layerEstimate k ω - ∑ i, BornProb (ApplyGate A (Ket j)) i * g i|
        ≤ (2 : ℝ) ^ (-((k : ℤ))), (layerLaw k A j g hA hg).prob ω)
      ≥ 1 - (2 : ℝ) ^ (-((k : ℤ))) := hguar
  have hgood : (∑ ω with |layerEstimate k ω - ∑ i, BornProb (ApplyGate A (Ket j)) i * g i|
        ≤ (2 : ℝ) ^ (-((k : ℤ))), (layerLaw k A j g hA hg).prob ω)
      = SignedMean.mass (layerLaw k A j g hA hg)
        (fun ω => |layerEstimate k ω - ∑ i, BornProb (ApplyGate A (Ket j)) i * g i|
          ≤ (2 : ℝ) ^ (-((k : ℤ)))) := rfl
  rw [hgood] at hguar'
  linarith

/-- The payoff-weighted state vector, whose Euclidean norm is the Born-weighted payoff norm. -/
noncomputable def bornPayoffVector {J : Type} [Fintype J] (ψ : QState J) (f : J → ℝ) :
    EuclideanSpace ℂ J :=
  WithLp.toLp 2 (fun i => ψ i * (f i : ℂ))

/-- The Euclidean norm of the payoff-weighted state is the square root of the second moment. -/
theorem norm_bornPayoffVector {J : Type} [Fintype J] (ψ : QState J) (f : J → ℝ) :
    ‖bornPayoffVector ψ f‖ = Real.sqrt (∑ i, BornProb ψ i * (f i) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  change ‖ψ i * (f i : ℂ)‖ ^ 2 = BornProb ψ i * (f i) ^ 2
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, BornProb]

/-- Lemma 4 of [Montanaro2015] in the source normalization: with
`L = ‖v(A)‖₂ = sqrt (∑ i, BornProb ... i * f i ^ 2)`, scaling by `L + 1` makes the layered
payoff have second moment at most one, so the locked guarantee yields
`|(L + 1) * layerEstimate - μ| ≤ ε * (L + 1)²` with probability at least `4/5`. -/
theorem layered_source_l2_scale_guarantee {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i) (ε : ℝ)
    (hk : 3 ≤ k) (hε0 : 0 < ε) (hε : (2 : ℝ) ^ (-((k : ℤ))) ≤ ε) :
    let μ := ∑ i, BornProb (ApplyGate A (Ket j)) i * f i
    let L := ‖bornPayoffVector (ApplyGate A (Ket j)) f‖
    (∑ ω with |(L + 1) * layerEstimate k ω - μ| ≤ ε * (L + 1) ^ 2,
        (layerLaw k A j (fun i => f i / (L + 1)) hA
          (fun _ => div_nonneg (hf _) (by positivity))).prob ω)
      ≥ 4 / 5 := by
  classical
  intro μ
  dsimp only
  set L : ℝ := ‖bornPayoffVector (ApplyGate A (Ket j)) f‖ with hL
  set s : ℝ := L + 1 with hs
  have hLsq : L ^ 2 = ∑ i, BornProb (ApplyGate A (Ket j)) i * (f i) ^ 2 := by
    rw [hL, norm_bornPayoffVector]
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
      mul_nonneg (bornProb_nonneg _ _) (sq_nonneg _))
  have hL0 : 0 ≤ L := norm_nonneg _
  have hs1 : 1 ≤ s := by rw [hs]; linarith
  have hspos : 0 < s := by linarith
  set g : I → ℝ := fun i => f i / s with hg
  have hg0 : ∀ i, 0 ≤ g i := fun i => div_nonneg (hf i) hspos.le
  have hsecond : (∑ i, BornProb (ApplyGate A (Ket j)) i * (g i) ^ 2) ≤ 1 := by
    have h1 : (∑ i, BornProb (ApplyGate A (Ket j)) i * (g i) ^ 2)
        = (∑ i, BornProb (ApplyGate A (Ket j)) i * (f i) ^ 2) / s ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only [g]
      field_simp
    rw [h1, ← hLsq]
    rw [div_le_one (by positivity)]
    nlinarith [hL0, hs1]
  have hguar := layered_quantum_mean_actual_guarantee k (by omega) A j g hA hg0 hsecond
  rw [neg_pow_half_eq k] at hguar
  rw [neg_pow_half_eq k] at hε
  have hle_eighth : ((1 : ℝ) / 2) ^ k ≤ 1 / 8 :=
    calc ((1 : ℝ) / 2) ^ k ≤ ((1 : ℝ) / 2) ^ 3 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ = 1 / 8 := by norm_num
  have hμeq : μ = s * (∑ i, BornProb (ApplyGate A (Ket j)) i * g i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [g]
    field_simp
  have hsub : SignedMean.mass (layerLaw k A j g hA hg0)
        (fun ω => |layerEstimate k ω - ∑ i, BornProb (ApplyGate A (Ket j)) i * g i|
          ≤ (1 / 2 : ℝ) ^ k)
      ≤ SignedMean.mass (layerLaw k A j g hA hg0)
        (fun ω => |s * layerEstimate k ω - μ| ≤ ε * s ^ 2) := by
    refine SignedMean.mass_mono _ (fun ω hle => ?_)
    have hstep : |s * layerEstimate k ω - μ|
        = s * |layerEstimate k ω - ∑ i, BornProb (ApplyGate A (Ket j)) i * g i| := by
      rw [hμeq, ← mul_sub, abs_mul, abs_of_pos hspos]
    rw [hstep]
    calc s * |layerEstimate k ω - ∑ i, BornProb (ApplyGate A (Ket j)) i * g i|
        ≤ s * (1 / 2 : ℝ) ^ k := mul_le_mul_of_nonneg_left hle hspos.le
      _ ≤ s * (ε * s) := by
          refine mul_le_mul_of_nonneg_left ?_ hspos.le
          exact le_trans hε (le_mul_of_one_le_right hε0.le hs1)
      _ = ε * s ^ 2 := by ring
  have htarget : (∑ ω with |(L + 1) * layerEstimate k ω - μ| ≤ ε * (L + 1) ^ 2,
        (layerLaw k A j (fun i => f i / (L + 1)) hA
          (fun _ => div_nonneg (hf _) (by positivity))).prob ω)
      = SignedMean.mass (layerLaw k A j g hA hg0)
        (fun ω => |s * layerEstimate k ω - μ| ≤ ε * s ^ 2) := rfl
  rw [htarget]
  have hgood : (∑ ω with |layerEstimate k ω - ∑ i, BornProb (ApplyGate A (Ket j)) i * g i|
        ≤ (1 / 2 : ℝ) ^ k, (layerLaw k A j g hA hg0).prob ω)
      = SignedMean.mass (layerLaw k A j g hA hg0)
        (fun ω => |layerEstimate k ω - ∑ i, BornProb (ApplyGate A (Ket j)) i * g i|
          ≤ (1 / 2 : ℝ) ^ k) := rfl
  have hguar' : (∑ ω with
        |layerEstimate k ω - ∑ i, BornProb (ApplyGate A (Ket j)) i * g i| ≤ (1 / 2 : ℝ) ^ k,
        (layerLaw k A j g hA hg0).prob ω) ≥ 1 - (1 / 2 : ℝ) ^ k := hguar
  rw [hgood] at hguar'
  linarith

end Qatlib.Papers.MCMontanaro15.MonteCarlo
