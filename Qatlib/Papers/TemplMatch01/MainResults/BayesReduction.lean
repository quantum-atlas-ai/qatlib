/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option warningAsError false

namespace Qatlib.Papers.TemplMatch01.MainResults.BayesReduction

open Qatlib.Foundations.PureStateMath
open Matrix MeasureTheory
open scoped ComplexOrder BigOperators MatrixOrder

set_option autoImplicit false

variable {d : ℕ} {J : Type*} [Fintype J] {X : Type*} [MeasurableSpace X]

noncomputable def scoreOperatorEntry (μ : Measure X) (ρ : X → Operator d) (P : X → ℝ)
    (S : J → X → ℝ) (j : J) (i i' : Fin d) : ℂ :=
  ∫ x, (((P x * S j x : ℝ)) : ℂ) * ρ x i i' ∂μ

noncomputable def scoreOperator (μ : Measure X) (ρ : X → Operator d) (P : X → ℝ)
    (S : J → X → ℝ) (j : J) : Operator d :=
  Matrix.of (fun i i' => scoreOperatorEntry μ ρ P S j i i')

noncomputable def averageScore (μ : Measure X) (ρ : X → Operator d) (P : X → ℝ)
    (S : J → X → ℝ) (pom : J → Operator d) : ℝ :=
  ∑ j, ∫ x, (P x * S j x) * (Matrix.trace (pom j * ρ x)).re ∂μ

theorem averageScore_eq_sum_trace
    (μ : Measure X) (ρ : X → Operator d) (P : X → ℝ) (S : J → X → ℝ) (pom : J → Operator d)
    (hInt : ∀ j (i i' : Fin d), Integrable (fun x => (((P x * S j x : ℝ)) : ℂ) * ρ x i i') μ) :
    averageScore μ ρ P S pom
      = ∑ j, (Matrix.trace (pom j * scoreOperator μ ρ P S j)).re := by
  classical
  rw [averageScore]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hint : ∀ (i k : Fin d), Integrable (fun x => pom j i k *
      ((((P x * S j x : ℝ)) : ℂ) * ρ x k i)) μ :=
    fun i k => (hInt j k i).const_mul (pom j i k)

  have hterm : ∀ i : Fin d, (pom j * scoreOperator μ ρ P S j) i i
      = ∫ x, (∑ k : Fin d, pom j i k * ((((P x * S j x : ℝ)) : ℂ) * ρ x k i)) ∂μ := by
    intro i
    rw [Matrix.mul_apply]
    have hk : ∀ k : Fin d, pom j i k * scoreOperator μ ρ P S j k i
        = ∫ x, pom j i k * ((((P x * S j x : ℝ)) : ℂ) * ρ x k i) ∂μ := by
      intro k
      rw [scoreOperator, Matrix.of_apply, scoreOperatorEntry, ← integral_const_mul]
    rw [Finset.sum_congr rfl (fun k _ => hk k)]
    exact (integral_finsetSum Finset.univ (fun k _ => hint i k)).symm
  have htrace : Matrix.trace (pom j * scoreOperator μ ρ P S j)
      = ∫ x, (∑ i : Fin d, ∑ k : Fin d,
          pom j i k * ((((P x * S j x : ℝ)) : ℂ) * ρ x k i)) ∂μ := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    exact (integral_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun k _ => hint i k))).symm
  have hintF : Integrable (fun x => ∑ i : Fin d, ∑ k : Fin d,
      pom j i k * ((((P x * S j x : ℝ)) : ℂ) * ρ x k i)) μ :=
    integrable_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun k _ => hint i k))
  rw [htrace]
  rw [show (∫ x, (∑ i : Fin d, ∑ k : Fin d, pom j i k *
        ((((P x * S j x : ℝ)) : ℂ) * ρ x k i)) ∂μ).re
      = ∫ x, (∑ i : Fin d, ∑ k : Fin d, pom j i k *
        ((((P x * S j x : ℝ)) : ℂ) * ρ x k i)).re ∂μ
    from (integral_re hintF).symm]
  apply integral_congr_ae
  filter_upwards with x
  have hre : (∑ i : Fin d, ∑ k : Fin d, pom j i k * ((((P x * S j x : ℝ)) : ℂ) * ρ x k i)).re
      = (P x * S j x) * (Matrix.trace (pom j * ρ x)).re := by
    have hinner : ∀ i : Fin d,
        (∑ k : Fin d, pom j i k * ((((P x * S j x : ℝ)) : ℂ) * ρ x k i)).re
          = (P x * S j x) * ((pom j * ρ x) i i).re := by
      intro i
      rw [Complex.re_sum]
      have hk : ∀ k : Fin d, (pom j i k * ((((P x * S j x : ℝ)) : ℂ) * ρ x k i)).re
          = (P x * S j x) * (pom j i k * ρ x k i).re := by
        intro k
        rw [show pom j i k * ((((P x * S j x : ℝ)) : ℂ) * ρ x k i)
            = (((P x * S j x : ℝ)) : ℂ) * (pom j i k * ρ x k i) by ring]
        exact Complex.re_ofReal_mul _ _
      rw [Finset.sum_congr rfl (fun k _ => hk k)]
      rw [Matrix.mul_apply, Complex.re_sum, Finset.mul_sum]
    rw [Complex.re_sum]
    rw [Finset.sum_congr rfl (fun i _ => hinner i)]
    rw [Matrix.trace, Complex.re_sum, Finset.mul_sum]
    simp only [Matrix.diag_apply]
  exact hre.symm

theorem bayesReduction (W pom : J → Operator d)
    (ht : ∀ j, (Matrix.trace (W j)).re ≠ 0)
    (hT : (∑ k, (Matrix.trace (W k)).re) ≠ 0) :
    (∑ j, (Matrix.trace (pom j * W j)).re)
      = (∑ j, (Matrix.trace (W j)).re) *
          ∑ j, ((Matrix.trace (W j)).re / (∑ k, (Matrix.trace (W k)).re)) *
            (Matrix.trace (pom j * ((Matrix.trace (W j)).re)⁻¹ • W j)).re := by
  classical
  have hterm : ∀ j, (Matrix.trace (pom j * ((Matrix.trace (W j)).re)⁻¹ • W j)).re
      = ((Matrix.trace (W j)).re)⁻¹ * (Matrix.trace (pom j * W j)).re := by
    intro j
    rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hterm j]
  field_simp
  rw [mul_div_cancel_right₀ _ (ht j)]

end Qatlib.Papers.TemplMatch01.MainResults.BayesReduction
