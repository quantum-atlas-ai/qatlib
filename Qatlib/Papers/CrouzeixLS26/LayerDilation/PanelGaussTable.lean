/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CrouzeixLS26.LayerDilation.ActualPolynomialPanelGauss

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc
open Qatlib.Papers.CrouzeixLS26.LayerDilation


/-! One common finite positive Gauss table for the actual panel integrals.
The witnesses are mathematical Gauss data, not a finite-precision producer. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Qatlib.Papers.CrouzeixLS26.LayerDilation.ContourGaussActualTable
open Matrix MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator
variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

omit [Fintype I] [DecidableEq I] [DecidableEq K] in
/-- One common real rule is chosen from the intervals and Q first, before
any matrix, index space, polynomial, complex direction or spectral input. -/
theorem uniform_actual_gauss_table (Q : ℕ) (a h : K → ℝ)
    (hQ : 1 ≤ Q) (hh : ∀ i, 0 < h i) :
    ∃ node weight : K → Fin Q → ℝ,
      (∀ i q, node i q ∈ Icc (a i) (a i+h i)) ∧
      (∀ i q, 0 < weight i q) ∧ (∀ i, ∑ q, weight i q = h i) ∧
      ∀ (T : Type) [Fintype T] [DecidableEq T] (A : Matrix T T ℂ) (p : Polynomial ℂ)
        (z₀ u c : K → ℂ) (r M : ℝ) (d m : ℕ),
        0 < r → (∀ i, h i ≤ r/4) → (∀ i, ‖u i‖ ≤ 1) → p.natDegree ≤ d → 0 ≤ M →
        d+m ≤ 2*Q-1 →
        (∀ i t, t ∈ Icc (a i) (a i+h i) → ∀ w ∈ matrixNumericalRange A,
          r ≤ ‖contourPanel (z₀ i) (u i) (a i) (h i) t-w‖) →
        (∀ i t, t ∈ Icc (a i) (a i+h i) →
          ‖p.eval (contourPanel (z₀ i) (u i) (a i) (h i) t)‖ ≤ M) →
        ‖(∑ i, ∑ q, ((c i*(weight i q : ℂ))*
            p.eval (contourPanel (z₀ i) (u i) (a i) (h i) (node i q))) •
              matrixResolvent A (contourPanel (z₀ i) (u i) (a i) (h i) (node i q))) -
          (∑ i, c i • (∫ t in (a i)..(a i+h i),
            p.eval (contourPanel (z₀ i) (u i) (a i) (h i) t) •
              matrixResolvent A (contourPanel (z₀ i) (u i) (a i) (h i) t)))‖ ≤
          ∑ i, ‖c i‖*(2*h i*(M*r⁻¹*(1/8 : ℝ)^(m+1))) := by
  have hex (i : K) := uniform_polynomial_panel_gauss Q (a i) (h i) hQ (hh i)
  choose node weight hnode hweight hsum hall using hex
  refine ⟨node, weight, hnode, hweight, hsum, ?_⟩
  intro T _ _ A p z₀ u c r M d m hr hsmall hu hp hM hdegree hsep hpbound
  have herror (i : K) :=
    (hall i T A p (z₀ i) (u i) r M d m hr (hsmall i) (hu i) hp hM hdegree (hsep i) (hpbound i)).2
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖(∑ q, ((c i * (weight i q : ℂ)) *
          p.eval (contourPanel (z₀ i) (u i) (a i) (h i) (node i q))) •
            matrixResolvent A (contourPanel (z₀ i) (u i) (a i) (h i) (node i q))) -
        c i • (∫ t in (a i)..(a i + h i),
          p.eval (contourPanel (z₀ i) (u i) (a i) (h i) t) •
            matrixResolvent A (contourPanel (z₀ i) (u i) (a i) (h i) t))‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have he := herror i
      rw [norm_sub_rev] at he
      have hsum' : (∑ q, ((c i * (weight i q : ℂ)) *
          p.eval (contourPanel (z₀ i) (u i) (a i) (h i) (node i q))) •
            matrixResolvent A (contourPanel (z₀ i) (u i) (a i) (h i) (node i q))) =
        c i • ∑ q, weight i q •
          (p.eval (contourPanel (z₀ i) (u i) (a i) (h i) (node i q)) •
            matrixResolvent A (contourPanel (z₀ i) (u i) (a i) (h i) (node i q))) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, smul_smul]
        rfl
      rw [hsum', ← smul_sub, norm_smul]
      exact mul_le_mul_of_nonneg_left he (norm_nonneg _)

omit [DecidableEq K] in
/-- Original table interface preserved; its witnesses now come from the
stronger rule chosen before the unknown matrix. -/
theorem actual_gauss_table (A : Matrix I I ℂ) (p : Polynomial ℂ)
    (z₀ u c : K → ℂ) (a h : K → ℝ) (r M : ℝ) (d m Q : ℕ)
    (hr : 0 < r) (hh : ∀ i, 0 < h i) (hsmall : ∀ i, h i ≤ r / 4)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hp : p.natDegree ≤ d) (hM : 0 ≤ M)
    (hQ : 1 ≤ Q) (hdegree : d + m ≤ 2 * Q - 1)
    (hsep : ∀ i t, t ∈ Icc (a i) (a i + h i) →
      ∀ w ∈ matrixNumericalRange A, r ≤ ‖contourPanel (z₀ i) (u i) (a i) (h i) t-w‖)
    (hpbound : ∀ i t, t ∈ Icc (a i) (a i + h i) →
      ‖p.eval (contourPanel (z₀ i) (u i) (a i) (h i) t)‖ ≤ M) :
    ∃ node weight : K → Fin Q → ℝ,
      (∀ i q, node i q ∈ Icc (a i) (a i + h i)) ∧
      (∀ i q, 0 < weight i q) ∧ (∀ i, ∑ q, weight i q = h i) ∧
      ‖(∑ i, ∑ q, ((c i * (weight i q : ℂ)) *
          p.eval (contourPanel (z₀ i) (u i) (a i) (h i) (node i q))) •
            matrixResolvent A (contourPanel (z₀ i) (u i) (a i) (h i) (node i q))) -
        (∑ i, c i • (∫ t in (a i)..(a i + h i),
          p.eval (contourPanel (z₀ i) (u i) (a i) (h i) t) •
            matrixResolvent A (contourPanel (z₀ i) (u i) (a i) (h i) t)))‖ ≤
      ∑ i, ‖c i‖ * (2 * h i * (M * r⁻¹ * (1 / 8 : ℝ) ^ (m + 1))) := by
  obtain ⟨node, weight, hn, hw, hs, hall⟩ := uniform_actual_gauss_table Q a h hQ hh
  exact ⟨node, weight, hn, hw, hs, hall I A p z₀ u c r M d m hr hsmall hu hp hM hdegree hsep hpbound⟩

end Qatlib.Papers.CrouzeixLS26.LayerDilation.ContourGaussActualTable
