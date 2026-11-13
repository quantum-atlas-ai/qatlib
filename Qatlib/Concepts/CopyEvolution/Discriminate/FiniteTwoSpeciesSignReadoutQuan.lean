/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteTwoSpeciesSignReadoutStat
import Qatlib.Concepts.CopyEvolution.Discriminate.TimedTwoSpeciesSpectralReadoutQuan

/-!
# Finite two-species sign readout

This module proves `FiniteTwoSpeciesSignReadout` for timed phase estimation of a
density-operator difference. Under the spectral magnitude and gap assumptions, positive-label
mass approximates the input's positive spectral weight within `twoSpeciesSignErrorBudget`,
supporting the discrimination construction of [LloydMohseniRebentrost2014].

The proof bounds the QPE kernel mass assigned to the wrong sign and combines this with
finite-copy implementation error. Positive and negative masses sum to one, and nonzero
eigenvectors have correct-sign probability at least one minus the budget, hence at least two
thirds when the budget is at most one third.

## Main statements

* `sign_kernel_positive_error`: the ideal kernel sign-error bound.
* `positive_mass_error`: the finite-copy positive spectral-weight bound.
* `timedTwoSpecies_sign_masses_sum`: normalization of the two sign masses.
* `finiteTwoSpeciesSignReadout`: the complete sign-readout specification.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HhlAlgorithms.UniformHHL

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyEvolution.Discriminate
open Matrix
open scoped Classical BigOperators ComplexOrder

/-- A phase label with the wrong sign is at circular phase distance greater than `γ / 8` from
`-x / 4` under the stated magnitude and gap bounds. -/
private theorem sign_bad_label_distance (M : ℕ) (γ x : ℝ) (z : Fin M)
    (hM : 0 < M) (_hγ : 0 < γ) (hγ1 : γ ≤ 1) (hx : |x| ≤ 1)
    (hgap : γ ≤ |x|) (hbad : if 0 < x then z ∉ twoSpeciesPositiveLabels M
      else z ∈ twoSpeciesPositiveLabels M) :
    γ/8 < phaseDistance (-x/4) ((z.val : ℝ)/(M : ℝ)) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hz0 : 0 ≤ (z.val : ℝ)/(M : ℝ) := div_nonneg (Nat.cast_nonneg _) hMr.le
  have hz1 : (z.val : ℝ)/(M : ℝ) < 1 := by
    rw [div_lt_one hMr]
    exact_mod_cast z.isLt
  have hrange := abs_le.mp hx
  unfold phaseDistance
  let c : ℤ := ⌊-x/4 - (z.val : ℝ)/(M : ℝ) + 1/2⌋
  change γ/8 < |-x/4 - (z.val : ℝ)/(M : ℝ) - (c : ℝ)|
  by_cases hp : 0 < x
  · rw [if_pos hp] at hbad
    have hz : (z.val : ℝ)/(M : ℝ) ≤ 1/2 := by
      have hb : (z.val : ℝ) ≤ (M : ℝ)/2 := by
        simpa only [twoSpeciesPositiveLabels, Finset.mem_filter, Finset.mem_univ,
          true_and, not_lt] using! hbad
      apply (div_le_iff₀ hMr).mpr
      linarith
    have hg : γ ≤ x := by simpa only [abs_of_pos hp] using! hgap
    by_cases hc : c ≤ -1
    · have hc' : (c : ℝ) ≤ -1 := by exact_mod_cast hc
      exact lt_of_lt_of_le (by linarith) (le_abs_self _)
    · have hc' : 0 ≤ (c : ℝ) := by exact_mod_cast (show 0 ≤ c by omega)
      exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
  · rw [if_neg hp] at hbad
    have hz : 1/2 < (z.val : ℝ)/(M : ℝ) := by
      have hb : (M : ℝ)/2 < (z.val : ℝ) := by
        simpa only [twoSpeciesPositiveLabels, Finset.mem_filter, Finset.mem_univ,
          true_and] using! hbad
      apply (lt_div_iff₀ hMr).mpr
      linarith
    have hg : γ ≤ -x := by simpa only [abs_of_nonpos (le_of_not_gt hp)] using! hgap
    by_cases hc : c ≤ -1
    · have hc' : (c : ℝ) ≤ -1 := by exact_mod_cast hc
      exact lt_of_lt_of_le (by linarith) (le_abs_self _)
    · have hc' : 0 ≤ (c : ℝ) := by exact_mod_cast (show 0 ≤ c by omega)
      exact lt_of_lt_of_le (by linarith) (neg_le_abs _)

/-- The total QPE kernel weight on positive labels differs from the indicator of `0 < x` by at
most `128 / (M * γ)` under the spectral gap assumptions. -/
private theorem sign_kernel_positive_error (M : ℕ) (γ x : ℝ) (hM : 0 < M)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hx : |x| ≤ 1)
    (hgap : x ≠ 0 → γ ≤ |x|) :
    |(∑ z ∈ twoSpeciesPositiveLabels M, ‖qpeKernel M (-x/4) z‖^2) -
      (if 0 < x then 1 else 0 : ℝ)| ≤ 128/((M : ℝ)*γ) := by
  let p := ∑ z ∈ twoSpeciesPositiveLabels M, ‖qpeKernel M (-x/4) z‖^2
  have hp0 : 0 ≤ p := Finset.sum_nonneg (fun z _ => sq_nonneg _)
  have hsplit : p + (∑ z ∈ (twoSpeciesPositiveLabels M)ᶜ,
      ‖qpeKernel M (-x/4) z‖^2) = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact uniform_qpeKernel_normalized M (-x/4) hM
  have hp1 : p ≤ 1 := by
    have hc0 : 0 ≤ ∑ z ∈ (twoSpeciesPositiveLabels M)ᶜ,
        ‖qpeKernel M (-x/4) z‖^2 := Finset.sum_nonneg (fun z _ => sq_nonneg _)
    linarith
  have ht := gradient_phase_kernel_tail M (-x/4) (γ/8) hM (by positivity)
  have hc : 16/((M : ℝ)*(γ/8)) = 128/((M : ℝ)*γ) := by ring
  rw [hc] at ht
  by_cases hzero : x = 0
  · subst x
    have hk (z : Fin M) : qpeKernel M 0 z = Qatlib.Foundations.PureStateMath.Ket (⟨0,hM⟩ : Fin M) z := by
      simpa only [Nat.cast_zero, zero_div] using!
        (offgrid_phase_geometric_and_periodic M 0 z hM).2.2 ⟨0,hM⟩
    have hp : p = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      have hne : (z : ℕ) ≠ 0 := by
        have hz' : (M : ℝ)/2 < (z.val : ℝ) := (Finset.mem_filter.mp hz).2
        intro he
        rw [he, Nat.cast_zero] at hz'
        have : 0 ≤ (M : ℝ)/2 := by positivity
        linarith
      simp [hk, Qatlib.Foundations.PureStateMath.Ket, Fin.ext_iff, hne]
    change |p - (if 0 < (0 : ℝ) then 1 else 0)| ≤ _
    rw [hp]
    simp only [lt_self_iff_false, if_false, sub_zero, abs_zero]
    positivity
  · let B := if 0 < x then (twoSpeciesPositiveLabels M)ᶜ else twoSpeciesPositiveLabels M
    have hsub : B ⊆ Finset.univ.filter (fun z : Fin M =>
        γ/8 < phaseDistance (-x/4) ((z.val : ℝ)/(M : ℝ))) := by
      intro z hz
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      apply sign_bad_label_distance M γ x z hM hγ hγ1 hx (hgap hzero)
      by_cases hp : 0 < x
      · simpa only [B, if_pos hp, Finset.mem_compl] using! hz
      · simpa only [B, if_neg hp] using! hz
    have hb : (∑ z ∈ B, ‖qpeKernel M (-x/4) z‖^2) ≤ 128/((M : ℝ)*γ) :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => sq_nonneg _)).trans ht
    change |p - (if 0 < x then 1 else 0)| ≤ _
    by_cases hp : 0 < x
    · simp only [B, if_pos hp] at hb ⊢
      rw [abs_of_nonpos (by linarith : p-1 ≤ 0)]
      linarith
    · simp only [B, if_neg hp] at hb ⊢
      rw [sub_zero, abs_of_nonneg hp0]
      exact hb

/-- For a gapped spectral decomposition of `ρ - σ`, the timed positive-label mass differs from
the positive spectral weight of any density input by at most `twoSpeciesSignErrorBudget M n
γ`. -/
private theorem positive_mass_error (d M n : ℕ) (γ : ℝ) (ρ σ V : Operator d)
    (x : Fin d → ℝ) (hM : 2 ≤ M) (hn : 0 < n) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hs : ρ-σ=V*Matrix.diagonal (fun j => (x j : ℂ))*Vᴴ)
    (hx : ∀ j, |x j| ≤ 1) (hgap : ∀ j, x j ≠ 0 → γ ≤ |x j|)
    (χ : Operator d) (hχ : IsDensityOperator χ) :
    |twoSpeciesTimedPositiveMass d M n ρ σ χ -
      (∑ j ∈ Finset.univ.filter (fun j => 0 < x j), ((Vᴴ*χ*V) j j).re)|
      ≤ twoSpeciesSignErrorBudget M n γ := by
  let a := fun j : Fin d => ((Vᴴ*χ*V) j j).re
  let p := fun j : Fin d => ∑ z ∈ twoSpeciesPositiveLabels M, ‖qpeKernel M (-x j/4) z‖^2
  let b := fun j : Fin d => if 0 < x j then (1 : ℝ) else 0
  have hd := timedTwoSpecies_basis_density d V χ hV hχ
  have ha (j : Fin d) : 0 ≤ a j := (timedTwoSpecies_density_diag d _ hd j).1
  have hasum : ∑ j, a j = 1 := by
    simpa only [a, Matrix.trace, Matrix.diag_apply, Complex.re_sum, Complex.one_re]
      using! congrArg Complex.re hd.2
  have href : (∑ j ∈ Finset.univ.filter (fun j => 0 < x j), a j) = ∑ j, a j*b j := by
    simp only [b, mul_ite, mul_one, mul_zero, Finset.sum_filter]
  have hideal : |(∑ j, a j*p j) - (∑ j, a j*b j)| ≤ 128/((M : ℝ)*γ) := by
    calc
      _ = |∑ j, a j*(p j-b j)| := by congr 1; rw [← Finset.sum_sub_distrib]; congr 1; funext j; ring
      _ ≤ ∑ j, |a j*(p j-b j)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, a j*|p j-b j| := by simp only [abs_mul, abs_of_nonneg (ha _)]
      _ ≤ ∑ j, a j*(128/((M : ℝ)*γ)) := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (sign_kernel_positive_error M γ (x j) (by omega)
          hγ hγ1 (hx j) (hgap j)) (ha j))
      _ = _ := by rw [← Finset.sum_mul, hasum, one_mul]
  have h := (timedTwoSpeciesSpectralReadout d M n (Real.pi/2) ρ σ V x χ hM hn hρ hσ hV hs hχ).2.2.2.2
    (twoSpeciesPositiveLabels M)
  have hphase (j : Fin d) : -(Real.pi/2)*x j/(2*Real.pi) = -x j/4 := by
    field_simp
    ring
  simp only [hphase] at h
  change |twoSpeciesTimedPositiveMass d M n ρ σ χ - ∑ j, a j*p j| ≤ _ at h
  rw [href]
  calc
    _ ≤ |twoSpeciesTimedPositiveMass d M n ρ σ χ - ∑ j, a j*p j| +
        |(∑ j, a j*p j) - ∑ j, a j*b j| := abs_sub_le _ _ _
    _ ≤ 32*(M-1 : ℕ)*(Real.pi/2)^2/(n : ℝ) + 128/((M : ℝ)*γ) := add_le_add h hideal
    _ = twoSpeciesSignErrorBudget M n γ := by unfold twoSpeciesSignErrorBudget; ring

/-- For positive `M` and density inputs, the timed positive and negative label masses sum to
one. -/
theorem timedTwoSpecies_sign_masses_sum (d M n : ℕ) (ρ σ χ : Operator d)
    (hM : 0 < M) (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ)
    (hχ : IsDensityOperator χ) :
    twoSpeciesTimedPositiveMass d M n ρ σ χ + twoSpeciesTimedNegativeMass d M n ρ σ χ = 1 := by
  unfold twoSpeciesTimedPositiveMass twoSpeciesTimedNegativeMass
  rw [Finset.sum_add_sum_compl, copyQPELabelMass_sum,
    (timedTwoSpeciesQPEOutput_density d M n (Real.pi/2) hM ρ σ χ hρ hσ hχ).2,
    Complex.one_re]

/-- The finite two-species sign-readout specification holds, with spectral-weight error and
nonzero-eigenvector sign success controlled by the stated budget. This formalizes the sign
readout used for discrimination in [LloydMohseniRebentrost2014]. -/
theorem finiteTwoSpeciesSignReadout : FiniteTwoSpeciesSignReadout := by
  intro d M n γ ρ σ V x hM hn hγ hγ1 hρ hσ hV hs hx hgap
  have hmain := positive_mass_error d M n γ ρ σ V x hM hn hγ hγ1 hρ hσ hV hs hx hgap
  have heigen (j : Fin d) (_hj : x j ≠ 0) :
      1-twoSpeciesSignErrorBudget M n γ ≤
        if 0 < x j then twoSpeciesTimedPositiveMass d M n ρ σ (outerProduct (fun a => V a j))
        else twoSpeciesTimedNegativeMass d M n ρ σ (outerProduct (fun a => V a j)) := by
    have hnorm : Normalized (fun a => V a j) := (normalized_iff_inner_self _).mpr (by
      simpa using! unitaryColumn_inner d V hV j j)
    have hχ := outerProduct_density hnorm
    have hw : (∑ k ∈ Finset.univ.filter (fun k => 0 < x k),
        ((Vᴴ*outerProduct (fun a => V a j)*V) k k).re) = if 0 < x j then 1 else 0 := by
      have hwk (k : Fin d) : ((Vᴴ*outerProduct (fun a => V a j)*V) k k).re =
          if k=j then 1 else 0 := by
        simp only [twoSpecies_outer_basis, unitaryColumn_inner d V hV]
        by_cases hk : k=j
        · simp [hk]
        · simp [hk]
      simp only [hwk, Finset.sum_filter]
      calc
        _ = ∑ k : Fin d, if k=j then (if 0 < x j then (1 : ℝ) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hk : k=j
          · simp [hk]
          · simp [hk]
        _ = _ := by simp
    have h := hmain _ hχ
    rw [hw] at h
    have hsum := timedTwoSpecies_sign_masses_sum d M n ρ σ _ (by omega) hρ hσ hχ
    by_cases hp : 0 < x j
    · simp only [if_pos hp] at h ⊢
      linarith [(abs_le.mp h).1]
    · simp only [if_neg hp, sub_zero] at h ⊢
      linarith [(abs_le.mp h).2]
  refine ⟨hmain, heigen, ?_⟩
  intro hbudget j hj
  have h := heigen j hj
  (try dsimp only)
  linarith

end Qatlib.Concepts.CopyEvolution.Discriminate
