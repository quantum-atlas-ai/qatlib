/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.GaussCutoffError

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weak limits of oriented Gauss self-pairings

For each fixed positive cutoff the pairing is a bounded continuous
test of the oriented product measure. Uniform smallness of the
absolute interaction of spatial near pairs then permits the cutoff
to be removed. The mass factor permits normalized probability
measures to represent bundles with varying total tangent mass.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- The Gauss self-pairing of a probability measure after restoring a
total tangent mass (m). -/
noncomputable def orientedGaussSelf (δ m : ℝ) (μ : ProbabilityMeasure VorticityElement) : ℝ :=
  m ^ 2 * ∫ p, gaussSoftKernel δ p.1 p.2 ∂(μ.prod μ).toMeasure

/-- As an unbundled measure, a finite oriented measure equals its
probability normalization scaled by its total mass. -/
theorem finiteMeasure_eq_mass_smul_normalize (ν : FiniteMeasure VorticityElement) :
    ν.toMeasure = (ν.mass : ℝ≥0∞) • ν.normalize.toMeasure := by
  ext A hA
  rw [Measure.smul_apply, smul_eq_mul]
  have h := congrArg (fun μ : FiniteMeasure VorticityElement => μ.toMeasure A)
    ν.self_eq_mass_smul_normalize
  simpa only [FiniteMeasure.toMeasure_smul, ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    Measure.coe_nnreal_smul_apply] using h

/-- Restoring both factors of total mass makes normalized self-pairing
agree with the product integral of the original finite measure. -/
theorem orientedGaussSelf_mass_normalize (δ : ℝ) (ν : FiniteMeasure VorticityElement) :
    orientedGaussSelf δ (ν.mass : ℝ) ν.normalize =
      ∫ p, gaussSoftKernel δ p.1 p.2 ∂(ν.toMeasure.prod ν.toMeasure) := by
  rw [finiteMeasure_eq_mass_smul_normalize ν, Measure.prod_smul_left, Measure.prod_smul_right, integral_smul_measure,
    integral_smul_measure]
  simp only [orientedGaussSelf, ProbabilityMeasure.toMeasure_prod, ENNReal.coe_toReal,
    smul_eq_mul, pow_two, mul_assoc]

/-- If oriented measures converge weakly, their masses converge, and
the absolute full interaction of close pairs is uniformly small along
the filter, then the full Gauss self-pairings converge. -/
theorem tendsto_orientedGaussSelf {ι : Type*} {l : Filter ι}
    {F : ι → ProbabilityMeasure VorticityElement} {μ : ProbabilityMeasure VorticityElement}
    {m : ι → ℝ} {M : ℝ} (hF : Tendsto F l (𝓝 μ)) (hm : Tendsto m l (𝓝 M))
    (hfull : ∀ i, Integrable (fun p => gaussSoftKernel 0 p.1 p.2) ((F i).prod (F i)).toMeasure)
    (hμ : Integrable (fun p => gaussSoftKernel 0 p.1 p.2) (μ.prod μ).toMeasure)
    (hnear : ∀ ε > 0, ∀ b > 0, ∃ δ ∈ Ioo 0 b, ∀ᶠ i in l,
      m i ^ 2 * (∫ p in gaussNearPairs δ, |gaussSoftKernel 0 p.1 p.2|
        ∂((F i).prod (F i)).toMeasure) < ε) :
    Tendsto (fun i => orientedGaussSelf 0 (m i) (F i)) l (𝓝 (orientedGaussSelf 0 M μ)) := by
  have hs : Tendsto (fun δ => orientedGaussSelf δ M μ) (𝓝[>] (0 : ℝ))
      (𝓝 (orientedGaussSelf 0 M μ)) :=
    (tendsto_integral_gaussSoftKernel hμ).const_mul (M ^ 2)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε₃ : 0 < ε / 3 := by positivity
  have he := (Metric.tendsto_nhds.1 hs) (ε / 3) hε₃
  obtain ⟨b, hb, hbsub⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.1 he
  obtain ⟨δ, hδ, hδnear⟩ := hnear (ε / 3) hε₃ b hb
  have hcut : Tendsto (fun i => orientedGaussSelf δ (m i) (F i)) l
      (𝓝 (orientedGaussSelf δ M μ)) :=
    (hm.pow 2).mul (tendsto_gaussSoftPairing hδ.1 hF hF)
  have hto := (Metric.tendsto_nhds.1 hcut) (ε / 3) hε₃
  filter_upwards [hδnear, hto] with i hnear_i hto_i
  have h1 : dist (orientedGaussSelf 0 (m i) (F i)) (orientedGaussSelf δ (m i) (F i)) <
      ε / 3 := by
    rw [Real.dist_eq, orientedGaussSelf, orientedGaussSelf, ← mul_sub, abs_mul,
      abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (abs_integral_gaussSoftKernel_error hδ.1 (hfull i))
      (sq_nonneg _)).trans_lt hnear_i
  have h3 : dist (orientedGaussSelf δ M μ) (orientedGaussSelf 0 M μ) < ε / 3 := hbsub hδ
  calc
    _ ≤ dist (orientedGaussSelf 0 (m i) (F i)) (orientedGaussSelf δ (m i) (F i)) +
        dist (orientedGaussSelf δ (m i) (F i)) (orientedGaussSelf 0 M μ) := dist_triangle _ _ _
    _ ≤ dist (orientedGaussSelf 0 (m i) (F i)) (orientedGaussSelf δ (m i) (F i)) +
        (dist (orientedGaussSelf δ (m i) (F i)) (orientedGaussSelf δ M μ) +
          dist (orientedGaussSelf δ M μ) (orientedGaussSelf 0 M μ)) :=
      add_le_add_right (dist_triangle _ _ _) _
    _ < ε := by linarith

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
