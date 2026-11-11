/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatentPQCTran26.MainResults.Definitions
import Qatlib.Papers.LatentPQCTran26.MainResults.FiniteCatalog
import Qatlib.Papers.LatentPQCTran26.MainResults.LatentUniversal

/-!
# A coupling bound for latent distribution approximation

`theorem1_diagonal_coupling` compares an atomic target distribution and a latent pushforward by
coupling two maps of the same latent variable. A uniform distance bound between a
target-realizing map and an approximating map bounds their `wasserstein1` cost on a compact
metric output space. See [TranEtAl2026] for the paper context.

## Main statements

* `theorem1_diagonal_coupling`: On a compact metric output space with measurable open sets,
  measurable maps of a common latent probability measure that are pointwise within nonnegative
  `δ` have `wasserstein1` cost at most `δ` when the first pushforward equals the specified
  atomic measure.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Qatlib.Papers.LatentPQCTran26.MainResults.Universality

open Qatlib.Papers.LatentPQCTran26.MainResults

/-- On a compact metric output space with measurable open sets, measurable maps of a common
latent probability measure that are pointwise within nonnegative `δ` have `wasserstein1`
cost at most `δ` when the first pushforward equals the specified atomic measure
[TranEtAl2026]. -/
theorem theorem1_diagonal_coupling
    {Z D : Type*} [MeasurableSpace Z] [MeasurableSpace D] [MetricSpace D]
    [OpensMeasurableSpace D] [CompactSpace D]
    (r : Measure Z) [IsProbabilityMeasure r]
    {N : ℕ} (q : Fin N → NNReal) (ρ : Fin N → D)
    (V : Z → D) (hV : Measurable V) (hpush : r.map V = atomicMeasure q ρ)
    (ρw : Z → D) (hρw : Measurable ρw)
    (δ : ℝ) (hδ : 0 ≤ δ) (happrox : ∀ z, dist (V z) (ρw z) ≤ δ) :
    wasserstein1 (atomicMeasure q ρ) (pushforward r ρw) ≤ δ := by
  set g : Z → D × D := fun z => (V z, ρw z) with hgdef
  have hmg : Measurable g := hV.prodMk hρw
  set γ : Measure (D × D) := r.map g with hγdef
  have hγ1 : γ.map Prod.fst = atomicMeasure q ρ := by
    have hcomp : Prod.fst ∘ g = V := funext fun _ => rfl
    rw [hγdef, Measure.map_map measurable_fst hmg, hcomp, hpush]
  have hγ2 : γ.map Prod.snd = pushforward r ρw := by
    have hcomp : Prod.snd ∘ g = ρw := funext fun _ => rfl
    rw [hγdef, Measure.map_map measurable_snd hmg, hcomp]
    rfl
  have hcost : (∫ p, dist p.1 p.2 ∂γ) ≤ δ := by
    have hFmeas : Measurable fun z : Z => dist (V z) (ρw z) :=
      ((Continuous.dist continuous_fst continuous_snd).measurable).comp hmg
    have hint : Integrable (fun z : Z => dist (V z) (ρw z)) r :=
      (integrable_const δ).mono hFmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          simp only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
          rw [abs_of_nonneg hδ]
          exact happrox z)
    have hmono : ∫ z : Z, dist (V z) (ρw z) ∂r ≤ ∫ _ : Z, δ ∂r :=
      integral_mono hint (integrable_const δ) (fun _ => happrox _)
    rw [integral_const, probReal_univ, one_smul] at hmono
    calc (∫ p, dist p.1 p.2 ∂γ)
        = ∫ z : Z, dist (g z).1 (g z).2 ∂r := by
          rw [hγdef]
          exact integral_map hmg.aemeasurable
            ((Continuous.dist continuous_fst continuous_snd).aestronglyMeasurable)
      _ = ∫ z : Z, dist (V z) (ρw z) ∂r := rfl
      _ ≤ δ := hmono
  have hbdd : BddBelow {c : ℝ | ∃ γ : Measure (D × D),
      γ ∈ coupling (atomicMeasure q ρ) (pushforward r ρw) ∧
      (∫ p, dist p.1 p.2 ∂γ) ≤ c} :=
    ⟨0, fun c ⟨γ, _, hle⟩ =>
      le_trans (integral_nonneg (fun _ => dist_nonneg)) hle⟩
  have hmem : δ ∈ {c : ℝ | ∃ γ : Measure (D × D),
      γ ∈ coupling (atomicMeasure q ρ) (pushforward r ρw) ∧
      (∫ p, dist p.1 p.2 ∂γ) ≤ c} := ⟨γ, ⟨hγ1, hγ2⟩, hcost⟩
  exact csInf_le hbdd hmem

end Qatlib.Papers.LatentPQCTran26.MainResults.Universality
