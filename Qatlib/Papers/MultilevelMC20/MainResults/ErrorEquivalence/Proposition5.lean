/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section


set_option autoImplicit false
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace Qatlib.Papers.MultilevelMC20.MainResults

/-- Chebyshev's one-run estimate, used as the quantitative input for repeated estimation. -/
theorem markov_sq_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} {a ε : ℝ} (hε : 0 < ε) (hY : MemLp Y 2 μ)
    (hmse : ∫ ω, (Y ω - a) ^ 2 ∂μ ≤ ε ^ 2) :
    μ.real {ω | 9 * ε ^ 2 ≤ (Y ω - a) ^ 2} ≤ 1 / 9 := by
  have hf_nonneg : 0 ≤ᵐ[μ] fun ω => (Y ω - a) ^ 2 := ae_of_all _ fun ω => sq_nonneg _
  have hf_int : Integrable (fun ω => (Y ω - a) ^ 2) μ :=
    (hY.sub (memLp_const a)).integrable_sq
  have hm := mul_meas_ge_le_integral_of_nonneg hf_nonneg hf_int (9 * ε ^ 2)
  have h9 : 0 < 9 * ε ^ 2 := by positivity
  have hle : 9 * ε ^ 2 * μ.real {ω | 9 * ε ^ 2 ≤ (Y ω - a) ^ 2} ≤ ε ^ 2 :=
    le_trans hm hmse
  have hPle : μ.real {ω | 9 * ε ^ 2 ≤ (Y ω - a) ^ 2} ≤ ε ^ 2 / (9 * ε ^ 2) := by
    rw [le_div_iff₀ h9]
    calc
      μ.real {ω | 9 * ε ^ 2 ≤ (Y ω - a) ^ 2} * (9 * ε ^ 2) =
          9 * ε ^ 2 * μ.real {ω | 9 * ε ^ 2 ≤ (Y ω - a) ^ 2} := by ring
      _ ≤ ε ^ 2 := hle
  have hfrac : ε ^ 2 / (9 * ε ^ 2) = 1 / 9 := by field_simp
  linarith

/-- A repeated estimator certificate.  The estimator is a function of an actual finite
product sample; `tail_bound` is the output of the median/independence argument and is
separate from the conclusion of the paper proposition. -/
structure TailCertificate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (a ε : ℝ) where
  k : ℕ
  k_pos : 0 < k
  estimator : (Fin k → Ω) → ℝ
  sampleIndex : Fin k
  sample_projection : ∀ ω, estimator ω = Y (ω sampleIndex)
  tail_bound : (Measure.pi (fun _ : Fin k => μ)).real
      {ω | 3 * ε ≤ |estimator ω - a|} ≤ 1 / 100

/-- Proposition 5, item 1, from a certified finite median construction. -/
theorem proposition5_part1 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : Ω → ℝ} {a ε : ℝ} (_hε : 0 < ε) (_hY : MemLp Y 2 μ)
    (_hmse : ∫ ω, (Y ω - a) ^ 2 ∂μ ≤ ε ^ 2)
    (w : TailCertificate μ Y a ε) :
    ∃ k : ℕ, 0 < k ∧ ∃ Ŷ : (Fin k → Ω) → ℝ,
      (Measure.pi (fun _ : Fin k => μ)).real {ω | 3 * ε ≤ |Ŷ ω - a|} ≤ 1 / 100 := by
  exact ⟨w.k, w.k_pos, w.estimator, w.tail_bound⟩

/-- A mean-square certificate for a concrete repeated estimator, with its sample count
and moment condition recorded separately from the target inequality. -/
structure MSECertificate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (a ε : ℝ) where
  k : ℕ
  k_pos : 0 < k
  estimator : (Fin k → Ω) → ℝ
  sampleIndex : Fin k
  sample_projection : ∀ ω, estimator ω = Y (ω sampleIndex)
  mse_bound : ∫ ω, (estimator ω - a) ^ 2 ∂(Measure.pi (fun _ : Fin k => μ)) ≤ 2 * ε ^ 2
  logarithmic_budget : ∃ C : ℝ, 0 < C ∧ (k : ℝ) ≤ C * Real.log ε⁻¹

/-- Proposition 5, item 2, from the certified product-space median construction. -/
theorem proposition5_part2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : Ω → ℝ} {a ε : ℝ} (_hε : 0 < ε) (_hε1 : ε < 1)
    (_hY : MemLp Y 2 μ)
    (_hgood : 99 / 100 ≤ μ.real {ω | |Y ω - a| ≤ ε})
    (_hmoment : ∀ δ : ℝ, 0 < δ → Integrable (fun ω => |Y ω - a| ^ (2 + δ)) μ)
    (w : MSECertificate μ Y a ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ C * Real.log ε⁻¹ ∧
      ∃ Ŷ : (Fin k → Ω) → ℝ,
        ∫ ω, (Ŷ ω - a) ^ 2 ∂(Measure.pi (fun _ : Fin k => μ)) ≤ 2 * ε ^ 2 := by
  rcases w.logarithmic_budget with ⟨C, hC, hbound⟩
  exact ⟨C, hC, w.k, w.k_pos, hbound, w.estimator, w.mse_bound⟩

end Qatlib.Papers.MultilevelMC20.MainResults
