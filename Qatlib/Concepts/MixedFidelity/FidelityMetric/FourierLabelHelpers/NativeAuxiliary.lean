/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.RankOneTraceNormEquality
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.FourierLabelHelpers
open scoped BigOperators

theorem equation_one {I : Type*} [Fintype I] [DecidableEq I] (u v : I → ℂ) :
    (Matrix.vecMulVec u (star v)).traceNorm =
      Real.sqrt (∑ i, Complex.normSq (u i)) * Real.sqrt (∑ i, Complex.normSq (v i)) := by
  rw [Qatlib.Concepts.MixedFidelity.FidelityMetric.traceNorm_rankOne_eq, Real.sqrt_mul
    (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (u i)))]

theorem lemma_three_three {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Nonempty X] (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hone : ∑ x, p x = 1) (A : X → Matrix I I ℂ) :
    (∑ x, (p x : ℂ) • A x).traceNorm ≤ ∑ x, p x * (A x).traceNorm ∧
      (∑ x, p x * (A x).traceNorm) ≤
        Finset.univ.sup' Finset.univ_nonempty (fun x => (A x).traceNorm) := by
  classical
  refine ⟨Qatlib.Concepts.MixedFidelity.FidelityMetric.traceNorm_weighted_sum_le p hp A, ?_⟩
  let R := Finset.univ.sup' Finset.univ_nonempty (fun x => (A x).traceNorm)
  calc
    _ ≤ ∑ x, p x * R := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left
        (Finset.le_sup' (fun x => (A x).traceNorm) (Finset.mem_univ x)) (hp x)
    _ = R := by rw [← Finset.sum_mul, hone, one_mul]

theorem lemma_three_three_distance_bound {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hone : ∑ x, p x = 1)
    (ρ σ : X → Matrix I I ℂ) (R : ℝ)
    (hR : ∀ x, (ρ x - σ x).traceNorm / 2 ≤ R) :
    ((∑ x, (p x : ℂ) • ρ x) - (∑ x, (p x : ℂ) • σ x)).traceNorm / 2 ≤ R := by
  have h := Qatlib.Concepts.MixedFidelity.FidelityMetric.traceNorm_probability_sum_le p hp hone
    (fun x => ρ x - σ x) (2 * R) (fun x => by linarith [hR x])
  simp only [smul_sub, Finset.sum_sub_distrib] at h
  linarith

end Qatlib.Concepts.MixedFidelity.FidelityMetric.FourierLabelHelpers
