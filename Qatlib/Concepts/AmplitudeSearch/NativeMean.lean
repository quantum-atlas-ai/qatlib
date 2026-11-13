/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.LayeredMean.NativeComposedMean

/-!
# Rational signed mean estimation

This module defines the rational signed estimator `nativeSignedOutput`, its median over repeated
trials, and the associated amplitude-estimation program lists and query budget. It transfers
error bounds from the real signed estimator to rational readouts and combines pilot-selected
scale and precision with median amplification, following the quantum mean-estimation setting of
[Montanaro2015].

## Main statements

* `native_signed_rational_trial_and_median`: a trial succeeds within 9σ·2⁻ᵏ with probability at
  least 13/24, with median failure at most (143/144)ʳ and an exact trial query count.
* `native_pilot_joint_rational_output`: a joint pilot-and-estimation failure bound at error
  threshold 2ε.
* `native_pilot_rational_worst_path_queries`: exact median query counts and a uniform upper
  bound over pilot outcomes.

## References

* [Montanaro, 2015, Theorem 5][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open Qatlib.Concepts.MonteCarloMean.PilotVariance
open Qatlib.Concepts.NativeNumerics.LayeredMean

namespace Qatlib.Concepts.AmplitudeSearch.NativeMean
open Matrix
open scoped BigOperators

/-- The rational signed mean estimate obtained by adding to the sampled payoff 4σ times the
difference of the positive and negative native layered outputs. -/
def nativeSignedOutput {I : Type} (f : I → ℚ) (σ : ℚ) (k : ℕ)
    (ω : I × (LayerRecord k × LayerRecord k)) : ℚ :=
  f ω.1+4*σ*(nativeLayerOutput k ω.2.1-nativeLayerOutput k ω.2.2)

/-- The rational median of the signed outputs from 2r + 1 trial records. -/
def nativeSignedOutputMedian {I : Type} (f : I → ℚ) (σ : ℚ) (k r : ℕ)
    (ω : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k)) : ℚ :=
  nativeRationalMedian r (fun z => nativeSignedOutput f σ k (ω z))

/-- The signed-trial query budget 2(k + 2)(2·`layerRepetitions` k + 1)(`layerGrid` k − 1). -/
def nativeSignedQueryBudget (k : ℕ) : ℕ :=
  2*(k+2)*(2*layerRepetitions k+1)*(layerGrid k-1)

noncomputable section
open scoped Classical
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean

/-- For nonnegative σ, every rational signed output differs from the corresponding real
`signedMeanEstimate` by at most σ·2⁻ᵏ. -/
private theorem native_signed_output_uniform_error {I : Type}
    (f : I → ℚ) (σ : ℚ) (k : ℕ) (hσ : 0 ≤ σ)
    (ω : I × (LayerRecord k × LayerRecord k)) :
    |(nativeSignedOutput f σ k ω : ℝ)-signedMeanEstimate k (fun i => (f i : ℝ)) (σ : ℝ) ω| ≤
      (σ : ℝ)*(1/2 : ℝ)^k := by
  have hs : (0 : ℝ) ≤ σ := by exact_mod_cast hσ
  have h1 := native_layered_readout_uniform_error k ω.2.1
  have h2 := native_layered_readout_uniform_error k ω.2.2
  change |(nativeLayerOutput k ω.2.1 : ℝ)-layerEstimate k ω.2.1| ≤ _ at h1
  change |(nativeLayerOutput k ω.2.2 : ℝ)-layerEstimate k ω.2.2| ≤ _ at h2
  have he : (nativeSignedOutput f σ k ω : ℝ)-signedMeanEstimate k (fun i => (f i : ℝ)) (σ : ℝ) ω =
      4*(σ : ℝ)*(((nativeLayerOutput k ω.2.1 : ℝ)-layerEstimate k ω.2.1)-
        ((nativeLayerOutput k ω.2.2 : ℝ)-layerEstimate k ω.2.2)) := by
    simp only [nativeSignedOutput, signedMeanEstimate]
    push_cast
    ring
  rw [he, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4*(σ : ℝ))]
  calc
    _ ≤ 4*(σ : ℝ)*(|(nativeLayerOutput k ω.2.1 : ℝ)-layerEstimate k ω.2.1|+
      |(nativeLayerOutput k ω.2.2 : ℝ)-layerEstimate k ω.2.2|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
    _ ≤ 8*(σ : ℝ)*(1/2 : ℝ)^(k+6) := by nlinarith
    _ ≤ _ := by
      rw [pow_add]
      norm_num
      have hh : (0 : ℝ) ≤ (σ : ℝ)*(1/2 : ℝ)^k := by positivity
      nlinarith

/-- For k ≥ 4, positive σ, and payoff variance at most σ² under the prepared Born law, the
rational signed trial has error at most 9σ·2⁻ᵏ with probability at least 13/24, and its
median over 2r + 1 trials exceeds that error with probability at most (143/144)ʳ. The
theorem also gives the exact query count for each trial program list, in the mean-estimation
setting of [Montanaro, Theorem 5][Montanaro2015]. -/
theorem native_signed_rational_trial_and_median :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
      (j : I) (f : I → ℚ) (σ : ℚ) (k r : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ),
      4 ≤ k → 0 < σ →
      let μ := ∑ i, BornProb (A *ᵥ Ket j) i*(f i : ℝ)
      (∑ i, BornProb (A *ᵥ Ket j) i*((f i : ℝ)-μ)^2) ≤ (σ : ℝ)^2 →
      let out := fun ω : LayerRecord k =>
        ∑ l : Fin (k+2), (2 : ℚ)^l.val *
          (((List.ofFn (fun z : Fin (2*layerRepetitions k+1) =>
            nativeAEDecode (layerGrid k) (2*k+8) (ω l z))).mergeSort (fun a b => a ≤ b)).getD (layerRepetitions k) 0)
      let hP := fun (x : I) (l : Fin (k+2)) => nativeLayerPrepare_unitary A
        (fun i => max 0 ((f i-f x)/(4*σ))) k l.val hA (fun _ => le_max_left _ _)
      let hN := fun (x : I) (l : Fin (k+2)) => nativeLayerPrepare_unitary A
        (fun i => max 0 ((f x-f i)/(4*σ))) k l.val hA (fun _ => le_max_left _ _)
      let law := nativeSignedLaw A j f σ k hA hP hN
      let trial := fun ω : I × (LayerRecord k × LayerRecord k) =>
        f ω.1+4*σ*(out ω.2.1-out ω.2.2)
      let med := fun ω : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k) =>
        (((List.ofFn (fun z => trial (ω z))).mergeSort (fun a b => a ≤ b)).getD r 0)
      (∑ ω ∈ Finset.univ.filter (fun ω : I × (LayerRecord k × LayerRecord k) =>
        |(trial ω : ℝ)-μ| ≤ 9*(σ : ℝ)*(1/2 : ℝ)^k), law.prob ω) ≥ 13/24 ∧
      law.probEvent (fun ω : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k) =>
        9*(σ : ℝ)*(1/2 : ℝ)^k < |(med ω : ℝ)-μ|) ≤ (143/144 : ℝ)^r ∧
      ∀ x : I, ((nativeSignedAEPrograms A j f σ k x).map QueryCount).sum =
        2*(k+2)*(2*layerRepetitions k+1)*(layerGrid k-1) := by
  intro I _ _ A j f σ k r hA hk hσ μ hvar out hP hN law trial med
  obtain ⟨hP', hN', oldlaw, hexact, hold⟩ :=
    native_signed_centered_same_program_consumer I A j f σ k hA hk hσ hvar
  have he : oldlaw = law := by
    cases oldlaw
    congr
    funext ω
    exact hexact ω
  rw [he] at hold
  have hs : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hgood : (∑ ω ∈ Finset.univ.filter (fun ω : I × (LayerRecord k × LayerRecord k) =>
      |(trial ω : ℝ)-μ| ≤ 9*(σ : ℝ)*(1/2 : ℝ)^k), law.prob ω) ≥ 13/24 := by
    refine hold.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ω _ _ => law.nonneg ω))
    intro ω hω
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hh := (Finset.mem_filter.mp hω).2
    have hd := native_signed_output_uniform_error f σ k hσ.le ω
    change |(trial ω : ℝ)-signedMeanEstimate k (fun i => (f i : ℝ)) (σ : ℝ) ω| ≤ _ at hd
    change |signedMeanEstimate k (fun i => (f i : ℝ)) (σ : ℝ) ω-μ| ≤ _ at hh
    exact (abs_sub_le _ (signedMeanEstimate k (fun i => (f i : ℝ)) (σ : ℝ) ω) _).trans (by linarith)
  refine ⟨hgood, ?_, fun x => (native_signed_actual_program_ledger I A j f σ k hA x).2.2.1⟩
  have hcomp := mass_complement law (fun ω => |(trial ω : ℝ)-μ| ≤ 9*(σ : ℝ)*(1/2 : ℝ)^k)
  simp only [not_le] at hcomp
  have hbad : mass law (fun ω => 9*(σ : ℝ)*(1/2 : ℝ)^k < |(trial ω : ℝ)-μ|) ≤ 11/24 := by
    change 13/24 ≤ mass law (fun ω => |(trial ω : ℝ)-μ| ≤ 9*(σ : ℝ)*(1/2 : ℝ)^k) at hgood
    linarith
  have hm := native_sorted_median_failure law (fun ω => (trial ω : ℝ)) r μ
    (9*(σ : ℝ)*(1/2 : ℝ)^k) (by positivity) hbad
  have hcast (ω : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k)) :
      (med ω : ℝ) = sortedBlockMedian r (fun z => (trial (ω z) : ℝ)) :=
    nativeRationalMedian_cast r (fun z => trial (ω z))
  simpa only [hcast] using! hm

/-- The probability of any event under n independent samples from a finite distribution is at
most one. -/
private theorem native_probEvent_le_one {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (n : ℕ) (E : (Fin n → X) → Prop) : p.probEvent E ≤ 1 := by
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  rw [← p.sum_probOf n]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun ω _ _ => Finset.prod_nonneg fun i _ => p.nonneg (ω i))

/-- For payoffs bounded in absolute value by one and the stated positive pilot parameters, the
joint probability that the pilot-selected rational median has error greater than 2ε is at
most 2/(Nν²) + (143/144)ʳ. This combines pilot scale selection with the mean-estimation
guarantee associated with [Montanaro2015]. -/
theorem native_pilot_joint_rational_output :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
      (j : I) (f : I → ℚ) (N h r : ℕ) (ν ε : ℚ) (hA : A ∈ Matrix.unitaryGroup I ℂ),
      0 < N → (∀ i, |f i| ≤ 1) → 0 < ν → ν ≤ 1/4 → 0 < ε →
      let μ := ∑ i, BornProb (A *ᵥ Ket j) i*(f i : ℝ)
      let bad := fun ω : Fin N → I =>
        let σ := pilotScale N h f ν ω
        let k := pilotPrecision N h f ν ε ω
        let out := fun ω : LayerRecord k =>
          ∑ l : Fin (k+2), (2 : ℚ)^l.val *
            (((List.ofFn (fun z : Fin (2*layerRepetitions k+1) =>
              nativeAEDecode (layerGrid k) (2*k+8) (ω l z))).mergeSort (fun a b => a ≤ b)).getD (layerRepetitions k) 0)
        let hP := fun (x : I) (l : Fin (k+2)) => nativeLayerPrepare_unitary A
          (fun i => max 0 ((f i-f x)/(4*σ))) k l.val hA (fun _ => le_max_left _ _)
        let hN := fun (x : I) (l : Fin (k+2)) => nativeLayerPrepare_unitary A
          (fun i => max 0 ((f x-f i)/(4*σ))) k l.val hA (fun _ => le_max_left _ _)
        let law := nativeSignedLaw A j f σ k hA hP hN
        let trial := fun ω : I × (LayerRecord k × LayerRecord k) =>
          f ω.1+4*σ*(out ω.2.1-out ω.2.2)
        let med := fun ω : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k) =>
          (((List.ofFn (fun z => trial (ω z))).mergeSort (fun a b => a ≤ b)).getD r 0)
        law.probEvent (fun ξ : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k) =>
          2*(ε : ℝ) < |(med ξ : ℝ)-μ|)
      (∑ ω : Fin N → I, (signedMeanSource A j hA).probOf ω * bad ω) ≤
        2/((N : ℝ)*(ν : ℝ)^2)+(143/144 : ℝ)^r := by
  intro I _ _ A j f N h r ν ε hA hN hf hν hν1 hε μ bad
  let p := signedMeanSource A j hA
  let B := fun ω : Fin N → I =>
    (pilotScale N h f ν ω : ℝ)^2 < p.variance (fun i => (f i : ℝ))
  have hρ : (0 : ℝ) ≤ (143/144 : ℝ)^r := by positivity
  have hpoint (ω : Fin N → I) : bad ω ≤ (if B ω then 1 else 0)+(143/144 : ℝ)^r := by
    by_cases hB : B ω
    · rw [if_pos hB]
      dsimp only [bad]
      exact (native_probEvent_le_one _ _ _).trans (by linarith)
    · rw [if_neg hB, zero_add]
      have hs :=
          (unknown_variance_pilot_native_moments_and_scale I N h f ν ω hN hf hν hν1).2.2.2.2.1
      have hp :=
          unknown_variance_pilot_computed_precision_and_worst_path I N h f ν ε ω hN hf hν hν1 hε
      have hv : (∑ i, BornProb (A *ᵥ Ket j) i*((f i : ℝ)-μ)^2) ≤ (pilotScale N h f ν ω : ℝ)^2 := by
        have hv := le_of_not_gt hB
        exact hv
      have hg := (native_signed_rational_trial_and_median I A j f
        (pilotScale N h f ν ω) (pilotPrecision N h f ν ε ω) r hA hp.1 hs hv).2.1
      have heps : (0 : ℝ) < ε := by exact_mod_cast hε
      have h9 : 9*(pilotScale N h f ν ω : ℝ)*(1/2 : ℝ)^(pilotPrecision N h f ν ε ω) ≤ 2*(ε : ℝ) := by
        nlinarith [hp.2.1]
      dsimp only [bad]
      unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
      refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans hg
      · intro ξ hξ
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact h9.trans_lt (Finset.mem_filter.mp hξ).2
      · intro ξ _ _
        exact Finset.prod_nonneg fun _ _ => (nativeSignedLaw A j f
          (pilotScale N h f ν ω) (pilotPrecision N h f ν ε ω) hA _ _).nonneg _
  have hcert := unknown_variance_pilot_actual_born_certificate_failure I A j N h f ν hA hN hf hν hν1
  change (∑ ω ∈ Finset.univ.filter B, p.probOf ω) ≤ 2/((N : ℝ)*(ν : ℝ)^2) at hcert
  calc
    _ ≤ ∑ ω : Fin N → I, p.probOf ω*((if B ω then 1 else 0)+(143/144 : ℝ)^r) := by
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left (hpoint ω) (Finset.prod_nonneg fun _ _ => p.nonneg _)
    _ = (∑ ω ∈ Finset.univ.filter B, p.probOf ω)+(143/144 : ℝ)^r := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, p.sum_probOf N, one_mul]
      congr 1
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_filter]
    _ ≤ _ := by linarith

/-- Concatenates the signed amplitude-estimation program lists associated with the sampled
centers of all 2r + 1 median trials. -/
noncomputable def nativeSignedMedianAEPrograms {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I → ℚ) (σ : ℚ) (k r : ℕ)
    (ξ : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k)) :=
  (List.ofFn (fun z => nativeSignedAEPrograms A j f σ k (ξ z).1)).flatten

/-- The signed-trial query budget is monotone in the precision parameter k. -/
private theorem nativeSignedQueryBudget_mono (k K : ℕ) (hk : k ≤ K) :
    nativeSignedQueryBudget k ≤ nativeSignedQueryBudget K := by
  unfold nativeSignedQueryBudget layerRepetitions layerGrid
  gcongr

/-- Under the pilot hypotheses, the selected precision k lies between 4 and the explicit ceiling
K, and every median record uses exactly (2r + 1)·`nativeSignedQueryBudget` k queries. This
count is at most (2r + 1)·`nativeSignedQueryBudget` K, uniformly over pilot outcomes. -/
theorem native_pilot_rational_worst_path_queries (I : Type) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I → ℚ) (N h r : ℕ) (ν ε : ℚ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1)
    (hν : 0 < ν) (hν1 : ν ≤ 1/4) (hε : 0 < ε) (ω : Fin N → I) :
    let σ := pilotScale N h f ν ω
    let k := pilotPrecision N h f ν ε ω
    let K := max 4 (Nat.clog 2 ((⌈16/ε⌉ : ℤ).toNat+1))
    4 ≤ k ∧ k ≤ K ∧
    ∀ ξ : Fin (2*r+1) → I × (LayerRecord k × LayerRecord k),
      ((nativeSignedMedianAEPrograms A j f σ k r ξ).map QueryCount).sum =
        (2*r+1)*nativeSignedQueryBudget k ∧
      ((nativeSignedMedianAEPrograms A j f σ k r ξ).map QueryCount).sum ≤
        (2*r+1)*nativeSignedQueryBudget K := by
  (try dsimp only)
  have hp := unknown_variance_pilot_computed_precision_and_worst_path I N h f ν ε ω hN hf hν hν1 hε
  refine ⟨hp.1, hp.2.2, fun ξ => ?_⟩
  have hc (z : Fin (2*r+1)) := (native_signed_actual_program_ledger I A j f
    (pilotScale N h f ν ω) (pilotPrecision N h f ν ε ω) hA (ξ z).1).2.2.1
  have he : ((nativeSignedMedianAEPrograms A j f (pilotScale N h f ν ω)
      (pilotPrecision N h f ν ε ω) r ξ).map QueryCount).sum =
        (2*r+1)*nativeSignedQueryBudget (pilotPrecision N h f ν ε ω) := by
    simp only [nativeSignedMedianAEPrograms, List.map_flatten, List.sum_flatten,
      List.map_ofFn, Function.comp_def, List.sum_ofFn, hc, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nativeSignedQueryBudget, Nat.cast_id]
  exact ⟨he, he.le.trans (Nat.mul_le_mul_left _ (nativeSignedQueryBudget_mono _ _ hp.2.2))⟩

end
end Qatlib.Concepts.AmplitudeSearch.NativeMean
