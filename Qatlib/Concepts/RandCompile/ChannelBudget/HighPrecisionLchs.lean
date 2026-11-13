/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Quadrature.HighPrecisionLchsDefs

/-!
# High precision LCHS analytic and quadrature bounds

This module establishes regularity of the high precision LCHS kernel, the Duhamel source
decomposition, and composite Gauss quadrature bounds for nonunitary evolution. The simulation
setting is described in [AnChildsLin2026]; the statements here expose explicit coefficient,
precision, and evaluation-count estimates.

It also proves normalization and elementary success-probability bounds for finite Gibbs inputs,
together with a compact-cell supremum result used in remainder estimates.

## Main statements

* `clause30_source_integral_norm_le`: bound the propagated source integral in Euclidean norm.
* `clause31_composite_precision_budget`: certify the composite quadrature parameters and
  remainder budget.
* `clause32_gibbs_probabilities_sum_to_one`: normalize the finite Gibbs probabilities.

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
* [An, Liu, and Lin, 2023][AnLiuLin2023]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.LchsSimulation.Kernel
open Qatlib.Concepts.LchsSimulation.Quadrature
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.LchsSimulation.Quadrature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib MeasureTheory Set Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- Complex differentiability on the closed lower half-plane implies continuity on that set. -/
theorem clause30_closed_differentiable_gives_closed_continuity {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f lowerClosedHalfPlane) :
    ContinuousOn f lowerClosedHalfPlane :=
  hf.continuousOn

/-- The open lower half-plane is an open subset of the complex numbers. -/
theorem clause30_lower_open_half_plane_is_open : IsOpen lowerOpenHalfPlane := by
  have h : lowerOpenHalfPlane = Complex.im ⁻¹' Set.Iio 0 := by
    ext z
    simp [lowerOpenHalfPlane, Set.Iio]
  rw [h]
  exact Complex.continuous_im.isOpen_preimage (Set.Iio 0) isOpen_Iio

/-- Complex differentiability on the closed lower half-plane implies analyticity on the open
lower half-plane. -/
theorem clause30_closed_differentiable_gives_open_analyticity {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f lowerClosedHalfPlane) :
    AnalyticOn ℂ f lowerOpenHalfPlane :=
  DifferentiableOn.analyticOn (hf.mono fun z hz => by
    change z.im < 0 at hz
    change z.im ≤ 0
    exact le_of_lt hz) clause30_lower_open_half_plane_is_open

/-- The kernel `highKernelF β` is complex differentiable on the closed lower half-plane. -/
theorem clause30_actual_kernel_closed_differentiable (β : ℝ) :
    DifferentiableOn ℂ (highKernelF β) lowerClosedHalfPlane := by
  intro z hz
  exact (highKernelF_analyticAt β z hz).differentiableAt.differentiableWithinAt

/-- The kernel `highKernelF β` is continuous on the closed lower half-plane. -/
theorem clause30_actual_kernel_closed_continuous (β : ℝ) :
    ContinuousOn (highKernelF β) lowerClosedHalfPlane :=
  highKernelF_continuousOn β

/-- For `0 < β < 1`, the contour kernel is both complex differentiable and continuous on the
closed lower half-plane. -/
theorem clause30_contour_consumes_closed_differentiability (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    DifferentiableOn ℂ (highKernelF β) lowerClosedHalfPlane ∧
      ContinuousOn (highKernelF β) lowerClosedHalfPlane :=
  ⟨clause30_actual_kernel_closed_differentiable β, clause30_actual_kernel_closed_continuous β⟩

/-- The forced LCHS response is the homogeneous propagated vector plus `lchsSourceIntegral`. -/
theorem clause30_inhomogeneous_decomposition {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (s t : ℝ) (v : QState I) :
    lchsForcedResponse A b s v t =
      orderedEvolution A s t *ᵥ v + lchsSourceIntegral A b s t := by
  rfl

/-- The LCHS source term equals the interval integral of the propagated source vector. -/
theorem clause30_source_is_duhamel_integral {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (s t : ℝ) :
    lchsSourceIntegral A b s t = ∫ u in s..t, orderedEvolution A u t *ᵥ b u := rfl

/-- For a continuous source and generator with positive semidefinite Hermitian part, the source
integral's Euclidean norm is bounded by the integral of the source's Euclidean norm when `s
≤ t`. -/
theorem clause30_source_integral_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (s t : ℝ)
    (hA : Continuous A) (hb : Continuous b)
    (hPSD : ∀ u, (A u + (A u)ᴴ).PosSemidef) (hst : s ≤ t) :
    ‖toEuclidean_fromVec (lchsSourceIntegral A b s t)‖
      ≤ ∫ u in s..t, ‖toEuclidean_fromVec (b u)‖ := by
  have h := orderedForcedSolution_norm_le A b hA hb hPSD s t hst (0 : QState I)
  have hz : orderedForcedSolution A b s 0 t = lchsSourceIntegral A b s t := by
    simp [orderedForcedSolution, lchsSourceIntegral]
  rw [hz] at h
  have h0 : ‖toEuclidean_fromVec (0 : QState I)‖ = 0 := by
    simp [toEuclidean_fromVec]
  rw [h0, zero_add] at h
  exact h

/-- The loaded `Q`-node Gauss rule integrates every real polynomial of degree at most `2 * Q -
1` exactly on `[-1, 1]`. -/
theorem clause31_loaded_rule_exact (Q : ℕ) (hQ : 1 ≤ Q) :
    ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      ∫ x in (-1 : ℝ)..1, p.eval x =
        ∑ q, (loadedGaussRule Q hQ).weight q * p.eval ((loadedGaussRule Q hQ).node q) :=
  (loadedGaussRule Q hQ).exact

/-- Every weight of the loaded Gauss rule is strictly positive. -/
theorem clause31_loaded_rule_weight_pos (Q : ℕ) (hQ : 1 ≤ Q) (q : Fin Q) :
    0 < (loadedGaussRule Q hQ).weight q :=
  (loadedGaussRule Q hQ).weight_pos q

/-- Every node of the loaded Gauss rule lies strictly between minus one and one. -/
theorem clause31_loaded_rule_node_mem (Q : ℕ) (hQ : 1 ≤ Q) (q : Fin Q) :
    (loadedGaussRule Q hQ).node q ∈ Ioo (-1) 1 :=
  (loadedGaussRule Q hQ).node_mem q

/-- The weights of the loaded Gauss rule sum to two. -/
theorem clause31_loaded_rule_weight_sum (Q : ℕ) (hQ : 1 ≤ Q) :
    ∑ q, (loadedGaussRule Q hQ).weight q = 2 :=
  gauss_rule_weight_sum Q _ _ (loadedGaussRule Q hQ).exact

/-- For `0 < β < 1` and a positive cell count, the total composite coefficient mass is at most
`2 * K / highKernelC β`. -/
theorem clause31_composite_coefficient_mass {Q M : ℕ} (K : ℕ) (β : ℝ)
    (hβ : 0 < β) (hβ1 : β < 1) (hM : 0 < M) (rule : GaussRule Q) :
    ∑ m : Fin M, ∑ q : Fin Q,
        ‖compositeCoefficients K rule.node rule.weight (fun k => highKernelG β k) m q‖
      ≤ (2 * K : ℝ) / highKernelC β := by
  have hsum : ∑ q, rule.weight q = 2 := gauss_rule_weight_sum Q _ _ rule.exact
  have hpos : ∀ q : Fin Q, 0 ≤ rule.weight q := fun q => (rule.weight_pos q).le
  have hker : ∀ k : ℝ, ‖highKernelG β k‖ ≤ 1 / highKernelC β :=
    fun k => highKernelG_abs_le_invC β hβ hβ1 k
  have hcpos : 0 < highKernelC β := highKernelC_pos β
  have hcw : 0 ≤ compositeCellWidth K M / 2 := by
    unfold compositeCellWidth
    positivity
  have hcell : ∀ m : Fin M,
      ∑ q : Fin Q, ‖compositeCoefficients K rule.node rule.weight
          (fun k => highKernelG β k) m q‖
        ≤ (compositeCellWidth K M) / highKernelC β := by
    intro m
    have hq : ∀ q : Fin Q,
        ‖compositeCoefficients K rule.node rule.weight (fun k => highKernelG β k) m q‖
          ≤ (compositeCellWidth K M / 2) * rule.weight q / highKernelC β := by
      intro q
      have hg : ‖highKernelG β (compositeNodeAt K rule.node m q)‖
          ≤ 1 / highKernelC β := hker (compositeNodeAt K rule.node m q)
      have hn : ‖compositeCoefficients K rule.node rule.weight
            (fun k => highKernelG β k) m q‖
          = ‖((compositeCellWidth K M / 2 : ℝ) : ℂ)‖ * ‖((rule.weight q : ℝ) : ℂ)‖ *
            ‖highKernelG β (compositeNodeAt K rule.node m q)‖ := by
        rw [compositeCoefficients]
        simp only [norm_mul]
      rw [hn, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg hcw, abs_of_nonneg (hpos q)]
      calc (compositeCellWidth K M / 2) * rule.weight q *
            ‖highKernelG β (compositeNodeAt K rule.node m q)‖
          ≤ (compositeCellWidth K M / 2) * rule.weight q * (1 / highKernelC β) :=
            mul_le_mul_of_nonneg_left hg (mul_nonneg hcw (hpos q))
        _ = (compositeCellWidth K M / 2) * rule.weight q / highKernelC β := by ring
    calc ∑ q : Fin Q, ‖compositeCoefficients K rule.node rule.weight
            (fun k => highKernelG β k) m q‖
        ≤ ∑ q : Fin Q, (compositeCellWidth K M / 2) * rule.weight q / highKernelC β :=
          Finset.sum_le_sum fun q _ => hq q
      _ = (compositeCellWidth K M / 2) * (∑ q, rule.weight q) / highKernelC β := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
      _ = (compositeCellWidth K M) / highKernelC β := by
          rw [hsum]
          ring

  calc ∑ m : Fin M, ∑ q : Fin Q,
          ‖compositeCoefficients K rule.node rule.weight (fun k => highKernelG β k) m q‖
      ≤ ∑ m : Fin M, (compositeCellWidth K M) / highKernelC β :=
        Finset.sum_le_sum fun m _ => hcell m
    _ = ((Fintype.card (Fin M) : ℝ)) * (compositeCellWidth K M) / highKernelC β := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp only [nsmul_eq_mul]
        ring
    _ = (2 * K : ℝ) / highKernelC β := by
        rw [Fintype.card_fin]
        simp only [compositeCellWidth]
        have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
        field_simp [hM0, hcpos.ne']
        <;> ring

/-- For fixed `0 < β < 1` and positive `K`, the composite node count times `log 4` is bounded by
a constant plus `|log(1 / ε)|` for every positive `ε`. -/
theorem clause31_node_count_polylog_in_precision (β K : ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (hK : 0 < K) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε →
      (compositeNodeCount β K ε : ℝ) * Real.log 4 ≤
        c * Real.log 4 + |Real.log (1 / ε)| := by
  have hcpos : 0 < highKernelC β := highKernelC_pos β
  have hA : 0 < (8 / (3 * highKernelC β)) * K := by positivity
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨1 + |Real.log ((8 / (3 * highKernelC β)) * K)| / Real.log 4, by positivity, ?_⟩
  intro ε hε
  set x : ℝ := Real.log ((8 / (3 * highKernelC β)) * K / ε) / Real.log 4 with hx
  have habsx : 0 ≤ |x| := abs_nonneg x
  have hmax : ((max 1 (Nat.ceil x) : ℕ) : ℝ) ≤ 1 + |x| := by
    rw [Nat.cast_max]
    refine max_le ?_ ?_
    · simp only [Nat.cast_one]
      linarith [habsx]
    · rcases le_total 0 x with h | h
      · have hlt := Nat.ceil_lt_add_one h
        rw [abs_of_nonneg h]
        linarith
      · have hz : Nat.ceil x ≤ 0 := (Nat.ceil_le (α := ℝ) (n := 0)).mpr (by simpa using! h)
        have hz' : (Nat.ceil x : ℝ) ≤ 0 := by simpa using! hz
        linarith
  have hlogsplit : Real.log ((8 / (3 * highKernelC β)) * K / ε)
      = Real.log ((8 / (3 * highKernelC β)) * K) + Real.log (1 / ε) := by
    have h1 : Real.log ((8 / (3 * highKernelC β)) * K / ε)
        = Real.log ((8 / (3 * highKernelC β)) * K) - Real.log ε :=
      Real.log_div (by positivity) (by positivity)
    have h2 : Real.log (1 / ε) = -Real.log ε := by
      have hh := Real.log_div (x := 1) (y := ε) (by norm_num) (by positivity)
      simpa using! hh
    rw [h1, h2]
    ring
  have htri : |Real.log ((8 / (3 * highKernelC β)) * K / ε)|
      ≤ |Real.log ((8 / (3 * highKernelC β)) * K)| + |Real.log (1 / ε)| := by
    rw [hlogsplit]
    exact abs_add_le _ _
  have hnodeN : compositeNodeCount β K ε = max 1 (Nat.ceil x) := by
    unfold compositeNodeCount
    rfl
  have hxabs : |x| * Real.log 4 = |Real.log ((8 / (3 * highKernelC β)) * K / ε)| := by
    rw [hx, abs_div, abs_of_pos hlog4]
    field_simp
  calc (compositeNodeCount β K ε : ℝ) * Real.log 4
      = ((max 1 (Nat.ceil x) : ℕ) : ℝ) * Real.log 4 := by rw [hnodeN]
    _ ≤ (1 + |x|) * Real.log 4 := by
        have hm := mul_le_mul_of_nonneg_right hmax hlog4.le
        linarith
    _ ≤ Real.log 4 + |Real.log ((8 / (3 * highKernelC β)) * K)| + |Real.log (1 / ε)| := by
        nlinarith [hxabs, htri]
    _ = (1 + |Real.log ((8 / (3 * highKernelC β)) * K)| / Real.log 4) * Real.log 4
        + |Real.log (1 / ε)| := by
        field_simp [hlog4.ne']

/-- Under the positive parameter assumptions, the composite cell and node counts are positive,
the cell width meets the stated bound, and the explicit remainder expression is at most `ε`. -/
theorem clause31_composite_precision_budget (β T Λ ε : ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (hT : 0 < T) (hΛ : 0 < Λ) (hε : 0 < ε) (K : ℕ) (hK : 0 < K) :
    0 < (compositeCellCount T Λ K : ℝ) ∧ 0 < (compositeNodeCount β K ε : ℝ) ∧
      (2 * K : ℝ) / compositeCellCount T Λ K ≤ 1 / (Real.exp 1 * T * Λ) ∧
      (8 / (3 * highKernelC β)) * K *
          ((2 * K : ℝ) / compositeCellCount T Λ K) ^ ((2 : ℝ) * compositeNodeCount β K ε) *
          (Real.exp 1 * T * Λ / 2) ^ ((2 : ℝ) * compositeNodeCount β K ε) ≤ ε := by
  simpa [compositeCellCount, compositeNodeCount] using!
    (composite_gauss_precision_budget β T Λ ε hβ hβ1 hT hΛ hε K hK)

/-- The composite ledger's propagator evaluation count equals its cell count times its node
count. -/
theorem clause31_propagator_evaluation_count (β T Λ : ℝ) (K : ℕ) (ε : ℝ) :
    (compositeCostLedger β T Λ K ε).propagatorEvaluations =
      compositeCellCount T Λ K * compositeNodeCount β K ε := rfl

/-- A finite nonempty Gibbs input at positive temperature has strictly positive partition
function. -/
theorem clause32_partition_function_positive {X : Type} [Fintype X] [Nonempty X] (g : GibbsInput X)
    (hT : 0 < g.temperature) :
    0 < partitionFunction g := by
  refine Finset.sum_pos ?_ ?_
  · intro x hx
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-- The probabilities of a finite nonempty Gibbs input at positive temperature sum to one. -/
theorem clause32_gibbs_probabilities_sum_to_one {X : Type} [Fintype X] [Nonempty X] (g : GibbsInput X)
    (hT : 0 < g.temperature) :
    ∑ x, gibbsProbability g x = 1 := by
  have hZ : 0 < partitionFunction g := clause32_partition_function_positive g hT
  have hsum : (∑ x, Real.exp (-g.energy x / g.temperature)) = partitionFunction g := rfl
  unfold gibbsProbability
  rw [← Finset.sum_div]
  rw [hsum]
  exact div_self hZ.ne'

/-- Every Gibbs probability is nonnegative at positive temperature. -/
theorem clause32_gibbs_probability_nonneg {X : Type} [Fintype X] [Nonempty X]
    (g : GibbsInput X) (hT : 0 < g.temperature) (x : X) : 0 ≤ gibbsProbability g x := by
  have hZ := clause32_partition_function_positive g hT
  unfold gibbsProbability
  positivity

/-- The filter success probability is at most one at positive temperature. -/
theorem clause32_filter_success_probability_le_one {X : Type} [Fintype X] [Nonempty X] (g : GibbsInput X)
    (hT : 0 < g.temperature) :
    filterSuccessProbability g ≤ 1 := by
  have hone : ∑ x, gibbsProbability g x = 1 := clause32_gibbs_probabilities_sum_to_one g hT
  have hle : (∑ x : X, (if filterEvent g x then gibbsProbability g x else 0 : ℝ))
      ≤ ∑ x : X, gibbsProbability g x := by
    refine Finset.sum_le_sum ?_
    intro x hx
    by_cases h : filterEvent g x
    · simp [h]
    · simp [h, clause32_gibbs_probability_nonneg g hT x]
  unfold filterSuccessProbability
  calc (∑ x : X, (if filterEvent g x then gibbsProbability g x else 0 : ℝ))
      ≤ ∑ x : X, gibbsProbability g x := hle
    _ = 1 := hone

/-- The filter success probability is nonnegative at positive temperature. -/
theorem clause32_filter_success_probability_nonneg {X : Type} [Fintype X] [Nonempty X]
    (g : GibbsInput X) (hT : 0 < g.temperature) :
    0 ≤ filterSuccessProbability g := by
  unfold filterSuccessProbability
  refine Finset.sum_nonneg ?_
  intro x hx
  by_cases h : filterEvent g x
  · simp [h, clause32_gibbs_probability_nonneg g hT x]
  · simp [h]

/-- At positive temperature, the absolute Gibbs observable expectation is bounded by
`observableRange g`. -/
theorem clause32_gibbs_observable_expectation_bounded {X : Type} [Fintype X] [Nonempty X] (g : GibbsInput X)
    (hT : 0 < g.temperature) :
    |gibbsObservableExpectation g| ≤ observableRange g := by
  have hone : ∑ x, gibbsProbability g x = 1 := clause32_gibbs_probabilities_sum_to_one g hT
  have hnonneg : ∀ x : X, 0 ≤ gibbsProbability g x :=
    fun x => clause32_gibbs_probability_nonneg g hT x
  have hle : ∀ x : X, gibbsProbability g x ≤ 1 := by
    intro x
    have h := Finset.single_le_sum (s := (Finset.univ : Finset X))
      (f := gibbsProbability g) (fun y hy => hnonneg y) (Finset.mem_univ x)
    rw [hone] at h
    exact h
  unfold gibbsObservableExpectation
  calc |∑ x, gibbsProbability g x * g.observable x|
      ≤ ∑ x, |gibbsProbability g x * g.observable x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |g.observable x| := by
        refine Finset.sum_le_sum ?_
        intro x hx
        calc |gibbsProbability g x * g.observable x|
            = |gibbsProbability g x| * |g.observable x| := abs_mul _ _
          _ ≤ |g.observable x| := by
            rw [abs_of_nonneg (hnonneg x)]
            simpa using! mul_le_mul_of_nonneg_right (hle x) (abs_nonneg (g.observable x))
    _ ≤ observableRange g := by
      unfold observableRange
      linarith

/-- If the norm of the `2 * Q`th derivative is continuous, it attains its supremum on the closed
cell of positive width. -/
theorem clause30_correction_supremum_attained {I : Type} [Fintype I] [DecidableEq I] {Q : ℕ}
    (Φ : ℝ → Matrix I I ℂ) (a h : ℝ) (hpos : 0 < h)
    (hcont : Continuous fun k => ‖iteratedDeriv (2 * Q) Φ k‖) :
    ∃ k ∈ Icc a (a + h),
      ‖iteratedDeriv (2 * Q) Φ k‖ =
        sSup ((Icc a (a + h)).image (fun j => ‖iteratedDeriv (2 * Q) Φ j‖)) := by
  have hcont' : ContinuousOn (fun k => ‖iteratedDeriv (2 * Q) Φ k‖) (Icc a (a + h)) :=
    hcont.continuousOn
  obtain ⟨k, hk, hmax⟩ := (isCompact_Icc (a := a) (b := a + h)).exists_isMaxOn
    ⟨a, left_mem_Icc.2 (le_add_of_nonneg_right hpos.le)⟩ hcont'
  refine ⟨k, hk, ?_⟩
  have hne : ((Icc a (a + h)).image (fun j => ‖iteratedDeriv (2 * Q) Φ j‖)).Nonempty := by
    refine ⟨‖iteratedDeriv (2 * Q) Φ k‖, ?_⟩
    exact ⟨k, hk, rfl⟩
  have hbdd : BddAbove ((Icc a (a + h)).image (fun j => ‖iteratedDeriv (2 * Q) Φ j‖)) := by
    refine ⟨‖iteratedDeriv (2 * Q) Φ k‖, ?_⟩
    intro y hy
    obtain ⟨j, hj, rfl⟩ := hy
    exact hmax hj
  apply le_antisymm
  · exact le_csSup hbdd ⟨k, hk, rfl⟩
  · exact csSup_le hne fun y hy => by
      obtain ⟨j, hj, rfl⟩ := hy
      exact hmax hj

/-- A positive filter success probability at positive temperature has reciprocal at least one. -/
theorem clause32_filter_success_fee {X : Type} [Fintype X] [Nonempty X]
    (g : GibbsInput X) (hT : 0 < g.temperature)
    (hp : 0 < filterSuccessProbability g) :
    1 ≤ 1 / filterSuccessProbability g := by
  rw [le_div_iff₀ hp]
  linarith [clause32_filter_success_probability_le_one g hT]

end Qatlib.Concepts.RandCompile.ChannelBudget
