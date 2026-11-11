/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridDensityEvaluation
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MatrixOptimizationSemantics
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.DualMixtureMassApproximation

/-!
# Density evaluation of capped dual mixtures

This module relates density-matrix evaluation of a program family to its finite leaf laws,
including hybrid resource counts. Capped weighted sampling has output and count receipts, and
its successful-output L1 error is controlled by the rejection tail.

Rational grid masses then approximate normalized mixtures and dual vectors by actual
density-evaluated programs. The dual-mixture interpretation is motivated by quantum semidefinite
programming; see [BrandaoSvore2017].

## Main statements

* `cappedProgram_density_count_receipt`: count-sensitive density evaluation equals a capped-law
  expectation.
* `capped_success_error`: the rejection tail adds to successful-output L1 error.
* `grid_dual_error`: a grid-based capped program approximates the normalized dual vector with an
  explicit bound.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.Family

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib
open scoped Classical ENNReal ComplexOrder
namespace Family
variable {K D m : ℕ}

/-- The program family obtained by replacing its input state and density proof with a specified
density operator. -/
def withDensity (F : Family K D m) (ρ : Operator D) (hρ : IsDensityOperator ρ) : Family K D m :=
  { F with state := ρ, density := hρ }

/-- Replacing a family's input density operator leaves its capped program unchanged. -/
theorem cappedProgram_withDensity (F : Family K D m) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (w : Fin K → ℕ) (b fuel : ℕ) :
    (F.withDensity ρ hρ).cappedProgram w b fuel = F.cappedProgram w b fuel := rfl

/-- The real output mass at `i` equals density evaluation of the program with the trace-weighted
indicator of output `i`. -/
theorem output_density_eval (F : Family K D m) (u : Fin K) (i : Fin m) :
    (F.output u i).toReal = (F.program u).evalDensity F.oracle F.state
      (fun j σ => (Matrix.trace σ).re * if j = i then 1 else 0) := by
  classical
  unfold output
  rw [map_apply_event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype]
  rw [ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top
    ((F.leaves u).apply_ne_top j) (by split_ifs <;> simp))]
  simp only [ENNReal.toReal_mul, apply_ite ENNReal.toReal, ENNReal.toReal_one,
    ENNReal.toReal_zero, leaves, instrumentPMF_apply,
    ENNReal.toReal_ofReal (instrumentProb_nonneg _ F.density.1 _)]
  exact Qatlib.Concepts.AdversaryBounds.AdvDuality.evalDensity_instrument F.oracle F.oracle_unitary _ (F.legal u) F.state
    (fun j => if j = i then 1 else 0)

/-- For a nonnegative output payoff, density evaluation interpreted as an extended nonnegative
real equals its expectation over the program's leaf law. -/
theorem density_leaf_expectation (F : Family K D m) (u : Fin K)
    (f : Fin m → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ENNReal.ofReal ((F.program u).evalDensity F.oracle F.state
      (fun i σ => (Matrix.trace σ).re * f i)) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.leaves u)
        (fun i => ENNReal.ofReal (f ((F.program u).leaf F.oracle i).value)) := by
  rw [← Qatlib.Concepts.AdversaryBounds.AdvDuality.evalDensity_instrument F.oracle F.oracle_unitary _ (F.legal u)]
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype,
      ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.ofReal_mul (instrumentProb_nonneg _ F.density.1 _)]
    rfl
  · intro i _
    exact mul_nonneg (instrumentProb_nonneg _ F.density.1 _) (hf _)

/-- For a nonnegative payoff on optional outputs, capped-program density evaluation equals the
real value of its expectation under the capped record law. -/
theorem cappedProgram_density_expectation (F : Family K D m)
    (w : Fin K → ℕ) (b fuel : ℕ) (f : Option (Fin m) → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (F.cappedProgram w b fuel).evalDensity F.oracle F.state
      (fun i σ => (Matrix.trace σ).re * f i) =
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.capped w b fuel)
        (fun r => ENNReal.ofReal (f (F.cappedValue r)))).toReal := by
  classical
  let g : SelectorResult K → ℝ := fun z => (F.continuation z.1).evalDensity F.oracle F.state
      (fun i σ => (Matrix.trace σ).re * f i)
  have hg : ∀ z, 0 ≤ g z := by
    intro z
    apply Qatlib.Concepts.AdversaryBounds.AdvDuality.evalDensity_trace_nonneg _ F.oracle_unitary _ _ _ F.density.1 f hf
    dsimp [continuation]
    split
    · exact HybridProgram.bind_legal _ (F.legal _) _ (fun _ => trivial)
    · trivial
  have hn (z : SelectorResult K) : ENNReal.ofReal (g z) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.cappedNext z) (fun r => ENNReal.ofReal (f (F.cappedValue r))) := by
    cases h : selected z with
    | inl u =>
        have h' : rejectionOutcome z.1.1 = .inl u := h
        simp only [g, continuation, h', Qatlib.Concepts.AdversaryBounds.AdvDuality.evalDensity_bind,
          HybridProgram.evalDensity, cappedNext, h, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map, cappedValue]
        exact F.density_leaf_expectation u (fun i => f (some i)) (fun i => hf _)
    | inr v =>
        have h' : rejectionOutcome z.1.1 = .inr v := h
        simp [g, continuation, h', HybridProgram.evalDensity, cappedNext, h,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, cappedValue, F.density.2]
  change (HybridProgram.ofCoins (weightedSampler w b fuel) F.continuation).evalDensity
    F.oracle F.state _ = _
  rw [Qatlib.Concepts.AdversaryBounds.AdvDuality.evalDensity_ofCoins]
  change ((weightedSampler w b fuel).paths.map (fun z =>
    CoinCode.wordWeight z.2 * g (z.1,z.2.length))).sum = _
  rw [coin_paths_expectation _ g hg]
  congr 1
  rw [capped, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  exact congrArg
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (weightedSampler w b fuel).law) (funext hn)

/-- The density-evaluated mass of each optional output equals the corresponding real mass of the
capped law pushed forward by `cappedValue`. -/
theorem cappedProgram_density_receipt (F : Family K D m)
    (w : Fin K → ℕ) (b fuel : ℕ) (i : Option (Fin m)) :
    (F.cappedProgram w b fuel).evalDensity F.oracle F.state
      (fun j σ => (Matrix.trace σ).re * if j = i then 1 else 0) =
      (((F.capped w b fuel).map F.cappedValue) i).toReal := by
  rw [F.cappedProgram_density_expectation w b fuel _ (by intro j; split_ifs <;> norm_num)]
  congr 1
  simp only [apply_ite ENNReal.ofReal, ENNReal.ofReal_one, ENNReal.ofReal_zero]
  rw [map_apply_event]
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  apply congrArg (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation _)
  funext r
  split_ifs <;> rfl

/-- Count-sensitive evaluation of the capped program expands as a sum over weighted sampler
paths, adding each path's coin-word length to the initial counts. -/
theorem cappedProgram_density_counts (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (c : HybridCounts) (g : Option (Fin m) → Operator D → HybridCounts → ℝ) :
    (F.cappedProgram w b fuel).evalDensityCounts F.oracle F.state c g =
      ((weightedSampler w b fuel).paths.map (fun z => CoinCode.wordWeight z.2 *
        (F.continuation z.1).evalDensityCounts F.oracle F.state
          (c.plus ⟨0,0,0,z.2.length⟩) g)).sum :=
  Qatlib.Concepts.AdversaryBounds.AdvDuality.evalDensityCounts_ofCoins _ _ _ _ _ _

/-- Trace-weighted count-sensitive evaluation equals a sum over instrument leaves, using each
leaf's probability, output, and counts added to the initial counts. -/
theorem density_counts_sum (F : Family K D m) (u : Fin K) (c : HybridCounts)
    (f : Fin m → HybridCounts → ℝ) :
    (F.program u).evalDensityCounts F.oracle F.state c (fun a σ c' => (Matrix.trace σ).re*f a c') =
      ∑ i, instrumentProb ((F.program u).instrument F.oracle F.oracle_unitary (F.legal u)) F.state i *
        f ((F.program u).leaf F.oracle i).value (c.plus ((F.program u).leaf F.oracle i).counts) := by
  rw [Qatlib.Concepts.AdversaryBounds.AdvDuality.evalDensityCounts_leaves, ← (F.program u).leaf_ofFn F.oracle,
    List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  rw [(F.program u).probability_law]
  exact (mul_assoc _ _ _).symm

/-- For nonnegative payoffs of outputs and counts, density evaluation interpreted as a
nonnegative extended real equals expectation under the leaf law with accumulated counts. -/
theorem density_counts_expectation (F : Family K D m) (u : Fin K) (c : HybridCounts)
    (f : Fin m → HybridCounts → ℝ) (hf : ∀ a c', 0 ≤ f a c') :
    ENNReal.ofReal ((F.program u).evalDensityCounts F.oracle F.state c
      (fun a σ c' => (Matrix.trace σ).re*f a c')) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.leaves u) (fun i => ENNReal.ofReal
        (f ((F.program u).leaf F.oracle i).value (c.plus ((F.program u).leaf F.oracle i).counts))) := by
  rw [F.density_counts_sum, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation,
      tsum_fintype, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.ofReal_mul (instrumentProb_nonneg _ F.density.1 _)]
    rfl
  · intro i _
    exact mul_nonneg (instrumentProb_nonneg _ F.density.1 _) (hf _ _)

/-- Starting from zero counts, trace-weighted evaluation of a nonnegative output-and-count
payoff equals the real expectation of that payoff under the capped record law. -/
theorem cappedProgram_density_count_receipt (F : Family K D m)
    (w : Fin K → ℕ) (b fuel : ℕ) (f : Option (Fin m) → HybridCounts → ℝ)
    (hf : ∀ a c, 0 ≤ f a c) :
    (F.cappedProgram w b fuel).evalDensityCounts F.oracle F.state HybridCounts.zero
      (fun a σ c => (Matrix.trace σ).re*f a c) =
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.capped w b fuel)
        (fun r => ENNReal.ofReal (f (F.cappedValue r) (F.cappedCounts r)))).toReal := by
  classical
  let g : SelectorResult K → ℝ := fun z =>
    (F.continuation z.1).evalDensityCounts F.oracle F.state ⟨0,0,0,z.2⟩
      (fun a σ c => (Matrix.trace σ).re*f a c)
  have hg : ∀ z, 0 ≤ g z := by
    intro z
    cases h : selected z with
    | inl u =>
        have h' : rejectionOutcome z.1.1 = .inl u := h
        simp only [g, continuation, h', Qatlib.Concepts.AdversaryBounds.AdvDuality.evalDensityCounts_bind,
          HybridProgram.evalDensityCounts]
        rw [F.density_counts_sum]
        exact Finset.sum_nonneg fun i _ => mul_nonneg (instrumentProb_nonneg _ F.density.1 _) (hf _ _)
    | inr v =>
        have h' : rejectionOutcome z.1.1 = .inr v := h
        simpa only [g, continuation, h', HybridProgram.evalDensityCounts, F.density.2,
          Complex.one_re, one_mul] using hf none ⟨0,0,0,z.2⟩
  have hn (z : SelectorResult K) : ENNReal.ofReal (g z) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.cappedNext z)
        (fun r => ENNReal.ofReal (f (F.cappedValue r) (F.cappedCounts r))) := by
    cases h : selected z with
    | inl u =>
        have h' : rejectionOutcome z.1.1 = .inl u := h
        simp only [g, continuation, h', Qatlib.Concepts.AdversaryBounds.AdvDuality.evalDensityCounts_bind,
          HybridProgram.evalDensityCounts, cappedNext, h, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,
          cappedValue, cappedCounts]
        exact F.density_counts_expectation u _ (fun a c => f (some a) c) (fun a c => hf _ _)
    | inr v =>
        have h' : rejectionOutcome z.1.1 = .inr v := h
        simp [g, continuation, h', HybridProgram.evalDensityCounts, cappedNext, h,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, cappedValue, cappedCounts, F.density.2]
  rw [F.cappedProgram_density_counts]
  simp only [HybridCounts.zero_plus]
  change ((weightedSampler w b fuel).paths.map (fun z =>
    CoinCode.wordWeight z.2 * g (z.1,z.2.length))).sum = _
  rw [coin_paths_expectation _ g hg]
  congr 1
  rw [capped, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  exact congrArg
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (weightedSampler w b fuel).law) (funext hn)

/-- For positive weights fitting the sampling block, the L1 distance between capped
successful-output masses and the stopped output law equals the rejection mass raised to
`fuel`. -/
theorem capped_success_l1 (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b) :
    (∑ i, |(((F.capped w b fuel).map F.cappedValue) (some i)).toReal -
      (((F.stopped w b hW hb).map F.value) i).toReal|) =
      (rationalRejectMass w b ^ fuel).toReal := by
  have h := F.capped_l1 w b fuel hW hb
  dsimp only at h
  rw [Fintype.sum_option, F.capped_none w b fuel hb, map_some_none] at h
  simp only [ENNReal.toReal_zero, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg,
    map_some_apply] at h
  linarith

/-- If the stopped output law has L1 error at most `ε` from `q`, successful density outputs of
the capped program have error at most `ε` plus the rejection tail. -/
theorem capped_success_error (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b)
    (q : Fin m → ℝ) (ε : ℝ)
    (he : (∑ i, |(((F.stopped w b hW hb).map F.value) i).toReal-q i|) ≤ ε) :
    (∑ i, |(F.cappedProgram w b fuel).evalDensity F.oracle F.state
      (fun j σ => (Matrix.trace σ).re * if j = some i then 1 else 0)-q i|) ≤
      (rationalRejectMass w b ^ fuel).toReal+ε := by
  simp_rw [F.cappedProgram_density_receipt]
  exact (l1_triangle _ (fun i => (((F.stopped w b hW hb).map F.value) i).toReal) q).trans
    (by rw [F.capped_success_l1 w b fuel hW hb]; exact add_le_add (le_refl _) he)

/-- Extending `q` by zero at failure, the full optional-output L1 error of the capped density
program is at most `ε` plus twice the rejection tail. -/
theorem capped_joint_error (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b)
    (q : Fin m → ℝ) (ε : ℝ)
    (he : (∑ i, |(((F.stopped w b hW hb).map F.value) i).toReal-q i|) ≤ ε) :
    (∑ i : Option (Fin m), |(F.cappedProgram w b fuel).evalDensity F.oracle F.state
      (fun j σ => (Matrix.trace σ).re * if j = i then 1 else 0)-i.elim 0 q|) ≤
      2*(rationalRejectMass w b ^ fuel).toReal+ε := by
  rw [Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some]
  rw [F.cappedProgram_density_receipt, F.capped_none w b fuel hb]
  simp only [sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  have h := F.capped_success_error w b fuel hW hb q ε he
  linarith

end Family

/-- Positive total selector mass gives a positive dual scale and expresses the normalized dual
vector as the normalized selector-weighted linear combination of the offset family's real
outputs. -/
theorem dual_mixture_normalized {T D m : ℕ} (F : Family T D m) (j₀ : Fin m)
    (hT : 0 < T) (a : ℚ) (μ : Fin T → ℚ)
    (hS : 0 < ∑ u, (selectorMasses T a μ u : ℝ)) :
    0 < dualScale T (a : ℝ) (fun t => (μ t : ℝ)) ∧
    ∀ i, dualVector F j₀ (a : ℝ) (fun t => (μ t : ℝ)) i /
      dualScale T (a : ℝ) (fun t => (μ t : ℝ)) =
      ∑ u, ((selectorMasses T a μ u : ℝ) / ∑ v, (selectorMasses T a μ v : ℝ)) *
        (F.withOffset j₀).realOutput u i := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  rw [selectorMasses_sum] at hS
  have hscale : dualScale T (a : ℝ) (fun t => (μ t : ℝ)) =
      ((T : ℝ)*a+∑ t, (μ t : ℝ))/T := by unfold dualScale; field_simp
  refine ⟨by rw [hscale]; exact div_pos hS hTr, ?_⟩
  intro i
  rw [selectorMasses_sum, Fin.sum_univ_succ]
  simp only [selectorMasses, Fin.cons_zero, Fin.cons_succ, Rat.cast_mul, Rat.cast_natCast,
    Family.realOutput, Family.withOffset_zero, PMF.pure_apply, Family.withOffset_succ]
  simp only [apply_ite ENNReal.toReal, ENNReal.toReal_one, ENNReal.toReal_zero]
  simp only [dualVector, hscale, Family.realOutput]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  by_cases hi : i = j₀
  · simp only [hi, if_true, mul_one]
    field_simp [hTr.ne', hS.ne']
  · simp only [hi, if_false, mul_zero, zero_add]
    field_simp [hTr.ne', hS.ne']
    ring

/-- For nonnegative rational mixture masses of positive total, the capped grid program's
successful-output L1 error is at most the rejection tail plus twice K/((n + 1) times the
total mass). -/
theorem grid_capped_error {K D m : ℕ} (F : Family K D m) (v : Fin K → ℚ)
    (hv : ∀ u, 0 ≤ v u) (hS : 0 < ∑ u, (v u : ℝ)) (n fuel : ℕ) :
    let w := gridWeights v n
    let b := blockWidth w
    let q := fun i => ∑ u, ((v u : ℝ)/(∑ u, (v u : ℝ)))*F.realOutput u i
    let β := ((K : ℝ)/(n+1))/(∑ u, (v u : ℝ))
    (∑ i, |(F.cappedProgram w b fuel).evalDensity F.oracle F.state
      (fun j σ => (Matrix.trace σ).re * if j = some i then 1 else 0)-q i|) ≤
        (rationalRejectMass w b ^ fuel).toReal+2*β := by
  (try dsimp only)
  let E := gridEffective v hv hS
  have hW := (intWeights_normalization _ (E.nonneg n) (E.positive n)).1
  have he := effective_sampler_l1 F E n F.realOutput (fun _ => 0) (by intro t; simp)
  simp only [mul_zero, Finset.sum_const_zero, add_zero] at he
  have h := F.capped_success_error (gridWeights v n) (blockWidth (gridWeights v n)) fuel
    hW (blockWidth_capacity _) _ _ he
  simpa only [E, gridEffective, gridWeights, mul_div_assoc] using h

/-- For nonnegative rational dual parameters with positive selector total, the dual scale is
positive and the dual vector equals that scale times the stopped offset-family output
probabilities. -/
theorem dual_actual_output_nonnegative {T D m : ℕ} (F : Family T D m) (j₀ : Fin m)
    (hT : 0 < T) (a : ℚ) (μ : Fin T → ℚ) (ha : 0 ≤ a) (hμ : ∀ t, 0 ≤ μ t)
    (hS : 0 < ∑ u, (selectorMasses T a μ u : ℝ)) :
    let v := selectorMasses T a μ
    let w := intWeights v
    let hW := (intWeights_normalization v (selectorMasses_nonneg a μ ha hμ) hS).1
    let F' := F.withOffset j₀
    let L := dualScale T (a : ℝ) (fun t => (μ t : ℝ))
    let p := (F'.stopped w (blockWidth w) hW (blockWidth_capacity w)).map F'.value
    0 < L ∧ ∀ i, dualVector F j₀ (a : ℝ) (fun t => (μ t : ℝ)) i = L*(p i).toReal := by
  (try dsimp only)
  have hn := dual_mixture_normalized F j₀ hT a μ hS
  refine ⟨hn.1, fun i => ?_⟩
  have hi := hn.2 i
  rw [Family.stopped_real]
  simp_rw [(intWeights_normalization _ (selectorMasses_nonneg a μ ha hμ) hS).2]
  exact (div_eq_iff hn.1.ne').mp hi |>.trans (mul_comm _ _)

/-- Grid-based capped density evaluation agrees with the capped optional-output law and
approximates the normalized dual vector in L1 by the rejection tail plus twice (T + 1)/((n +
1) times total selector mass). -/
theorem grid_dual_error {T D m : ℕ} (F : Family T D m) (j₀ : Fin m)
    (hT : 0 < T) (a : ℚ) (μ : Fin T → ℚ) (ha : 0 ≤ a) (hμ : ∀ t, 0 ≤ μ t)
    (hS : 0 < ∑ u, (selectorMasses T a μ u : ℝ)) (n fuel : ℕ) :
    let v := selectorMasses T a μ
    let w := gridWeights v n
    let b := blockWidth w
    let F' := F.withOffset j₀
    let L := dualScale T (a : ℝ) (fun t => (μ t : ℝ))
    let β := (((T+1 : ℕ) : ℝ)/(n+1))/(∑ u, (v u : ℝ))
    0 < L ∧
    (∀ z : Option (Fin m), (F'.cappedProgram w b fuel).evalDensity F'.oracle F'.state
      (fun j σ => (Matrix.trace σ).re * if j = z then 1 else 0) =
        (((F'.capped w b fuel).map F'.cappedValue) z).toReal) ∧
    (∑ i, |(F'.cappedProgram w b fuel).evalDensity F'.oracle F'.state
      (fun j σ => (Matrix.trace σ).re * if j = some i then 1 else 0)-
        dualVector F j₀ (a : ℝ) (fun t => (μ t : ℝ)) i/L|) ≤
      (rationalRejectMass w b ^ fuel).toReal+2*β := by
  (try dsimp only)
  have hn := dual_mixture_normalized F j₀ hT a μ hS
  refine ⟨hn.1, (F.withOffset j₀).cappedProgram_density_receipt _ _ _, ?_⟩
  simp_rw [hn.2]
  exact grid_capped_error (F.withOffset j₀) _ (selectorMasses_nonneg a μ ha hμ) hS n fuel

end Qatlib.Concepts.MpsAdaptation.MpsTransfer

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer.DualMixtureDensityInput
open Qatlib
open Qatlib

/-- The grid-weighted capped offset program has exact density-output receipts and
successful-output L1 error from the normalized dual vector bounded by the rejection tail
plus the stated selector-grid error. -/
theorem frontier1 {T D m : ℕ} (F : Family T D m) (j₀ : Fin m)
    (hT : 0 < T) (a : ℚ) (μ : Fin T → ℚ) (ha : 0 ≤ a) (hμ : ∀ t, 0 ≤ μ t)
    (hS : 0 < ∑ u, (selectorMasses T a μ u : ℝ)) (n fuel : ℕ) :
    let v := selectorMasses T a μ
    let w := gridWeights v n
    let b := blockWidth w
    let F' := F.withOffset j₀
    let L := dualScale T (a : ℝ) (fun t => (μ t : ℝ))
    0 < L ∧
    (∀ z : Option (Fin m), (F'.cappedProgram w b fuel).evalDensity F'.oracle F'.state
      (fun j σ => (Matrix.trace σ).re * if j = z then 1 else 0) =
        (((F'.capped w b fuel).map F'.cappedValue) z).toReal) ∧
    (∑ i, |(F'.cappedProgram w b fuel).evalDensity F'.oracle F'.state
      (fun j σ => (Matrix.trace σ).re * if j = some i then 1 else 0)-
        dualVector F j₀ (a : ℝ) (fun t => (μ t : ℝ)) i/L|) ≤
      (rationalRejectMass w b ^ fuel).toReal+
        2*((((T+1 : ℕ) : ℝ)/(n+1))/(∑ u, (v u : ℝ))) :=
  grid_dual_error F j₀ hT a μ ha hμ hS n fuel
end Qatlib.Concepts.MpsAdaptation.MpsTransfer.DualMixtureDensityInput
