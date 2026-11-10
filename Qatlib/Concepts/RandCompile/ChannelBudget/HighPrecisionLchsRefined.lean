/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.HighPrecisionLchsDefs
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.OperatorNorm
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.Kernel
open Qatlib.Concepts.LchsSimulation.Quadrature
open Qatlib.Concepts.RandCompile.ChannelBudget

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace Qatlib.Concepts.RandCompile.ChannelBudget.HighPrecisionLchsRefined

open Matrix
open Qatlib
open MeasureTheory
open Filter
open Set
open Complex
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ComplexConjugate Topology
set_option warningAsError false

variable {I : Type} [Fintype I] [DecidableEq I]

theorem clause30_kernel_domain_gap_eq_frontier : kernelDomainGap = kernelFrontier := by
  ext z
  simp only [kernelDomainGap, Set.mem_diff, kernelFrontier, Set.mem_setOf_eq,
    lowerClosedHalfPlane, Set.mem_setOf_eq, lowerOpenHalfPlane, Set.mem_setOf_eq]
  constructor
  · intro h
    exact le_antisymm h.1 (by linarith [h.2])
  · intro h
    exact ⟨by linarith, by intro hlt; linarith⟩

theorem clause30_closed_is_closure_of_open : closure lowerOpenHalfPlane = lowerClosedHalfPlane := by
  have hcl : IsClosed lowerClosedHalfPlane := by
    have h : IsClosed {z : ℂ | z.im ≤ 0} :=
      isClosed_le Complex.continuous_im (g := fun _ => (0 : ℝ)) continuous_const
    simpa [lowerClosedHalfPlane] using! h
  have hsub : lowerOpenHalfPlane ⊆ lowerClosedHalfPlane := by
    intro z hz
    have hz' : z.im < 0 := hz
    show z.im ≤ 0
    exact le_of_lt hz'
  have hmono : closure lowerOpenHalfPlane ⊆ closure lowerClosedHalfPlane := closure_mono hsub
  rw [hcl.closure_eq] at hmono
  refine le_antisymm hmono ?_
  intro z hz
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_cases hlt : z.im < 0
  · refine ⟨z, hlt, ?_⟩
    simpa using! hε
  · have h0 : z.im = 0 := le_antisymm hz (le_of_not_gt hlt)
    have him : (Complex.I * (ε / 2 : ℝ) : ℂ).im = ε / 2 := by
      rw [Complex.mul_im]
      simp [Complex.I_im]
    have hz' : (z - Complex.I * (ε / 2 : ℝ) : ℂ).im = z.im - ε / 2 := by
      rw [Complex.sub_im, him]
    refine ⟨z - Complex.I * (ε / 2 : ℝ), ?_, ?_⟩
    · simp only [lowerOpenHalfPlane, Set.mem_setOf_eq]
      rw [hz', h0]
      have h2 : (0 : ℝ) - ε / 2 < 0 := by
        have : ε / 2 > 0 := by positivity
        linarith
      linarith
    · rw [dist_eq_norm]
      have hnorm : ‖z - (z - Complex.I * (ε / 2 : ℝ))‖ = ε / 2 := by
        have hz2 : z - (z - Complex.I * (ε / 2 : ℝ)) = Complex.I * (ε / 2 : ℝ) := by ring
        rw [hz2, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
        simp [Complex.norm_I, abs_of_pos (by positivity : 0 < ε / 2)]
      rw [hnorm]
      have : ε / 2 < ε := by linarith
      exact this

theorem clause30_frontier_indicator_analytic_open :
    AnalyticOn ℂ (frontierIndicator : ℂ → ℂ) lowerOpenHalfPlane := by
  have hconst : AnalyticOn ℂ (fun _ => (0 : ℂ)) lowerOpenHalfPlane := by
    intro x hx
    exact analyticAt_const.analyticWithinAt
  refine AnalyticOn.congr hconst ?_
  intro x hx
  have hx' : x.im < 0 := hx
  show frontierIndicator x = (0 : ℂ)
  simp only [frontierIndicator]
  rw [if_neg]
  intro hz
  rw [hz] at hx'
  exact (lt_irrefl _ hx')

theorem clause30_frontier_indicator_not_continuous_closed :
    ¬ ContinuousOn (frontierIndicator : ℂ → ℂ) lowerClosedHalfPlane := by
  intro h
  have hone := Metric.continuousOn_iff.1 h
  obtain ⟨δ, hδ0, hδ'⟩ :=
    hone (0 : ℂ) (by simp [lowerClosedHalfPlane]) (1 / 2 : ℝ) (by norm_num)
  have hmem : (-Complex.I * (δ / 2 : ℝ) : ℂ) ∈ lowerClosedHalfPlane := by
    simp only [lowerClosedHalfPlane, Set.mem_setOf_eq]
    have him : (-Complex.I * (δ / 2 : ℝ) : ℂ).im = -(δ / 2) := by
      simp [Complex.mul_im, Complex.I_im]
    rw [him]
    linarith [hδ0]
  have hdist : dist (-Complex.I * (δ / 2 : ℝ) : ℂ) 0 < δ := by
    rw [dist_eq_norm]
    have hnorm : ‖(-Complex.I * (δ / 2 : ℝ) : ℂ) - 0‖ = δ / 2 := by
      have hz2 : (-Complex.I * (δ / 2 : ℝ) : ℂ) - 0 = -Complex.I * (δ / 2 : ℝ) := by ring
      rw [hz2, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hhalf : 0 < δ / 2 := by linarith [hδ0]
      simp [Complex.norm_I, abs_of_pos hhalf]
    rw [hnorm]
    have hhalf : 0 < δ / 2 := by linarith [hδ0]
    linarith
  have hlt := hδ' (-Complex.I * (δ / 2 : ℝ)) hmem hdist
  have hne : (-Complex.I * (δ / 2 : ℝ) : ℂ).im ≠ 0 := by
    have him : (-Complex.I * (δ / 2 : ℝ) : ℂ).im = -(δ / 2) := by
      simp [Complex.mul_im, Complex.I_im]
    rw [him]
    have hhalf : 0 < δ / 2 := by linarith [hδ0]
    linarith
  have hlt' : dist (frontierIndicator (-Complex.I * (δ / 2 : ℝ) : ℂ))
      (frontierIndicator (0 : ℂ)) < 1 / 2 := hlt
  rw [frontierIndicator, frontierIndicator] at hlt'
  simp only [if_neg hne, Complex.zero_im, if_pos] at hlt'
  simp at hlt'
  linarith

theorem clause30_conj_continuous_closed :
    ContinuousOn (conj : ℂ → ℂ) lowerClosedHalfPlane :=
  Complex.continuous_conj.continuousOn

theorem clause30_conj_not_analytic_open :
    ¬ AnalyticOn ℂ (conj : ℂ → ℂ) lowerOpenHalfPlane := by
  intro h
  have hopen : IsOpen lowerOpenHalfPlane := clause30_lower_open_half_plane_is_open
  have hz0 : (-Complex.I : ℂ) ∈ lowerOpenHalfPlane := by
    change (-Complex.I : ℂ).im < 0
    simp [Complex.I_im]
  have h0 : AnalyticWithinAt ℂ (conj : ℂ → ℂ) lowerOpenHalfPlane (-Complex.I) := h (-Complex.I) hz0
  have hnh : insert (-Complex.I) lowerOpenHalfPlane ∈ 𝓝 (-Complex.I) := by
    have : insert (-Complex.I) lowerOpenHalfPlane = lowerOpenHalfPlane :=
      Set.insert_eq_self.mpr hz0
    rw [this]
    exact hopen.mem_nhds hz0
  have hd : DifferentiableAt ℂ (conj : ℂ → ℂ) (-Complex.I) :=
    AnalyticWithinAt.differentiableWithinAt h0 |>.differentiableAt hnh

  have hreal : fderiv ℝ (conj : ℂ → ℂ) (-Complex.I) = conjCLE := by
    have hfun : (conj : ℂ → ℂ) = (↑(conjCLE : ℂ →L[ℝ] ℂ) : ℂ → ℂ) := by
      funext z
      simp
    have h2 : fderiv ℝ (conj : ℂ → ℂ) (-Complex.I)
        = fderiv ℝ (↑(conjCLE : ℂ →L[ℝ] ℂ)) (-Complex.I) := by
      rw [hfun]
    rw [h2]
    exact conjCLE.fderiv (x := (-Complex.I : ℂ))

  have hlink : (fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)).restrictScalars ℝ = conjCLE :=
    (hd.fderiv_restrictScalars (𝕜 := ℝ)).symm.trans hreal
  have hlinkf : ⇑((fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)).restrictScalars ℝ)
      = ⇑(↑conjCLE : ℂ →L[ℝ] ℂ) :=
    congrArg (fun M : ℂ →L[ℝ] ℂ => ⇑M) hlink
  have hone : (fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)) 1 = 1 := by
    have h1 : (fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)) 1 = (↑conjCLE : ℂ →L[ℝ] ℂ) 1 := by
      calc (fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)) 1
          = ⇑((fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)).restrictScalars ℝ) 1 := by
            symm
            exact congrFun (ContinuousLinearMap.coe_restrictScalars'
              (f := fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)) (R := ℝ)) 1
        _ = ⇑(↑conjCLE : ℂ →L[ℝ] ℂ) 1 := congrFun hlinkf 1

    have h2 : (↑conjCLE : ℂ →L[ℝ] ℂ) 1 = 1 := by simp [conjCLE_apply]
    calc (fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)) 1 = (↑conjCLE : ℂ →L[ℝ] ℂ) 1 := h1
      _ = 1 := h2
  have hI : (fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)) Complex.I = -Complex.I := by
    have h1 : (fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)) Complex.I
        = (↑conjCLE : ℂ →L[ℝ] ℂ) Complex.I := by
      calc (fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)) Complex.I
          = ⇑((fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)).restrictScalars ℝ) Complex.I := by
            symm
            exact congrFun (ContinuousLinearMap.coe_restrictScalars'
              (f := fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)) (R := ℝ)) Complex.I
        _ = ⇑(↑conjCLE : ℂ →L[ℝ] ℂ) Complex.I := congrFun hlinkf Complex.I
    have h2 : (↑conjCLE : ℂ →L[ℝ] ℂ) Complex.I = -Complex.I := by
      simp [conjCLE_apply]
    calc (fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)) Complex.I
        = (↑conjCLE : ℂ →L[ℝ] ℂ) Complex.I := h1
      _ = -Complex.I := h2
  have hlin : (fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)) Complex.I
      = Complex.I * (fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)) 1 := by
    have hh := map_smul (fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)) Complex.I (1 : ℂ)
    simpa [mul_one] using! hh
  have hcontra : Complex.I = -Complex.I := by
    calc Complex.I = 1 * Complex.I := by simp
      _ = (fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)) 1 * Complex.I := by rw [hone]
      _ = (fderiv ℂ (conj : ℂ → ℂ) (-Complex.I)) Complex.I := by rw [hlin]; ring
      _ = -Complex.I := hI
  have hfalse : False := by
    have h := congrArg Complex.im hcontra
    simp at h
    linarith
  exact hfalse.elim

theorem clause30_open_closed_boundary_is_real :
    (closure lowerOpenHalfPlane = lowerClosedHalfPlane) ∧
    (kernelDomainGap = kernelFrontier) ∧
    (¬ (∀ f : ℂ → ℂ, AnalyticOn ℂ f lowerOpenHalfPlane → ContinuousOn f lowerClosedHalfPlane)) ∧
    (¬ (∀ f : ℂ → ℂ, ContinuousOn f lowerClosedHalfPlane → AnalyticOn ℂ f lowerOpenHalfPlane)) := by
  refine ⟨clause30_closed_is_closure_of_open, clause30_kernel_domain_gap_eq_frontier, ?_, ?_⟩
  · intro hall
    exact clause30_frontier_indicator_not_continuous_closed
      (hall (frontierIndicator : ℂ → ℂ) clause30_frontier_indicator_analytic_open)
  · intro hall
    exact clause30_conj_not_analytic_open
      (hall (conj : ℂ → ℂ) clause30_conj_continuous_closed)

theorem clause30_discrete_source_coefficient {Q M : ℕ} (K : ℕ) (node weight : Fin Q → ℝ)
    (κ : ℝ → ℂ) (m : Fin M) (q : Fin Q) :
    sourceCellCoefficient K node weight κ m q
      = (((compositeCellWidth K M / 2 : ℝ) : ℂ) * ((weight q : ℝ) : ℂ)) *
        κ (compositeNodeAt K node m q) := by
  rfl

theorem clause30_source_cell_mass_le {Q M : ℕ} (K : ℕ) (node weight : Fin Q → ℝ)
    (κ : ℝ → ℂ) (κbound : ℝ) (hκ : ∀ k, ‖κ k‖ ≤ κbound) (hκb : 0 ≤ κbound) :
    ∀ m : Fin M,
      ∑ q : Fin Q, ‖sourceCellCoefficient K node weight κ m q‖
        ≤ (compositeCellWidth K M) * (∑ q : Fin Q, |weight q|) * κbound := by
  intro m
  have hcw : 0 ≤ compositeCellWidth K M / 2 := by
    unfold compositeCellWidth
    positivity
  have hq : ∀ q : Fin Q,
      ‖sourceCellCoefficient K node weight κ m q‖
        ≤ (compositeCellWidth K M / 2) * |weight q| * κbound := by
    intro q
    have hn : ‖sourceCellCoefficient K node weight κ m q‖
        = ‖((compositeCellWidth K M / 2 : ℝ) : ℂ)‖ * ‖((weight q : ℝ) : ℂ)‖ *
          ‖κ (compositeNodeAt K node m q)‖ := by
      rw [sourceCellCoefficient]
      simp only [norm_mul]
    rw [hn, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg hcw]
    exact mul_le_mul_of_nonneg_left (hκ _) (mul_nonneg hcw (abs_nonneg (weight q)))
  calc (∑ q : Fin Q, ‖sourceCellCoefficient K node weight κ m q‖)
      ≤ ∑ q : Fin Q, (compositeCellWidth K M / 2) * |weight q| * κbound :=
        Finset.sum_le_sum fun q _ => hq q
    _ = (compositeCellWidth K M / 2) * (∑ q : Fin Q, |weight q|) * κbound := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ (compositeCellWidth K M) * (∑ q : Fin Q, |weight q|) * κbound := by
        have h1 : (compositeCellWidth K M / 2) * (∑ q : Fin Q, |weight q|)
            ≤ compositeCellWidth K M * (∑ q : Fin Q, |weight q|) := by
          have h2 : compositeCellWidth K M / 2 ≤ compositeCellWidth K M := by
            unfold compositeCellWidth
            have h3 : (0 : ℝ) ≤ (2 * K : ℝ) := by positivity
            have h4 : (0 : ℝ) ≤ (2 * K : ℝ) / M := by positivity
            linarith
          exact mul_le_mul_of_nonneg_right h2
            (Finset.sum_nonneg fun q _ => abs_nonneg (weight q))
        exact mul_le_mul_of_nonneg_right h1 hκb

theorem clause30_source_mass_independent_of_cells {Q M : ℕ} (K : ℕ) (node weight : Fin Q → ℝ)
    (κ : ℝ → ℂ) (κbound : ℝ) (hκ : ∀ k, ‖κ k‖ ≤ κbound) (hκb : 0 ≤ κbound)
    (hM : 0 < M) :
    sourceCoefficientMass M K node weight κ
      ≤ (2 * K : ℝ) * (∑ q : Fin Q, |weight q|) * κbound := by
  have hcell : ∀ m : Fin M,
      ∑ q : Fin Q, ‖sourceCellCoefficient K node weight κ m q‖
        ≤ (compositeCellWidth K M) * (∑ q : Fin Q, |weight q|) * κbound :=
    fun m => clause30_source_cell_mass_le K node weight κ κbound hκ hκb m
  have hmass : sourceCoefficientMass M K node weight κ
      ≤ ∑ m : Fin M, (compositeCellWidth K M) * (∑ q : Fin Q, |weight q|) * κbound := by
    unfold sourceCoefficientMass
    exact Finset.sum_le_sum fun m _ => hcell m
  have hsum : ∑ m : Fin M, (compositeCellWidth K M) * (∑ q : Fin Q, |weight q|) * κbound
      = ((Fintype.card (Fin M) : ℝ)) * (compositeCellWidth K M)
        * (∑ q : Fin Q, |weight q|) * κbound := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
    ring
  rw [hsum] at hmass
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hcard : (Fintype.card (Fin M) : ℝ) = (M : ℝ) := by
    rw [Fintype.card_fin]
  rw [hcard] at hmass
  have hcw : compositeCellWidth K M = (2 * K : ℝ) / M := by
    unfold compositeCellWidth
    rfl
  rw [hcw] at hmass
  have hdiv : (M : ℝ) * ((2 * K : ℝ) / M) = 2 * K := by
    rw [mul_div_cancel₀ _ hM0]
  rw [hdiv] at hmass
  nlinarith

theorem clause30_discrete_source_norm_le {Q M : ℕ} (K : ℕ) (node weight : Fin Q → ℝ)
    (κ : ℝ → ℂ) (σ : ℝ → QState I) (σbound : ℝ) (hσ : ∀ k, ‖σ k‖ ≤ σbound) :
    ‖discreteSourceTerm M K node weight κ σ‖
      ≤ sourceCoefficientMass M K node weight κ * σbound := by
  have hterm : ∀ (m : Fin M) (q : Fin Q),
      ‖(sourceCellCoefficient K node weight κ m q) •
        σ (compositeNodeAt K node m q)‖
        ≤ ‖sourceCellCoefficient K node weight κ m q‖ * σbound := by
    intro m q
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hσ _) (norm_nonneg _)
  have hsum : ‖discreteSourceTerm M K node weight κ σ‖
      ≤ ∑ m : Fin M, ∑ q : Fin Q,
        ‖sourceCellCoefficient K node weight κ m q‖ * σbound := by
    unfold discreteSourceTerm
    calc ‖∑ m : Fin M, ∑ q : Fin Q,
          (sourceCellCoefficient K node weight κ m q) •
            σ (compositeNodeAt K node m q)‖
        ≤ ∑ m : Fin M, ‖∑ q : Fin Q,
          (sourceCellCoefficient K node weight κ m q) •
            σ (compositeNodeAt K node m q)‖ := norm_sum_le _ _
      _ ≤ ∑ m : Fin M, ∑ q : Fin Q,
          ‖sourceCellCoefficient K node weight κ m q‖ * σbound := by
        apply Finset.sum_le_sum
        intro m hm
        calc ‖∑ q : Fin Q, (sourceCellCoefficient K node weight κ m q) •
              σ (compositeNodeAt K node m q)‖
            ≤ ∑ q : Fin Q, ‖(sourceCellCoefficient K node weight κ m q) •
              σ (compositeNodeAt K node m q)‖ := norm_sum_le _ _
          _ ≤ ∑ q : Fin Q, ‖sourceCellCoefficient K node weight κ m q‖ * σbound := by
            apply Finset.sum_le_sum
            intro q hq
            exact hterm m q
  calc ‖discreteSourceTerm M K node weight κ σ‖
      ≤ ∑ m : Fin M, ∑ q : Fin Q,
          ‖sourceCellCoefficient K node weight κ m q‖ * σbound := hsum
    _ = sourceCoefficientMass M K node weight κ * σbound := by
      unfold sourceCoefficientMass
      calc (∑ m : Fin M, ∑ q : Fin Q,
            ‖sourceCellCoefficient K node weight κ m q‖ * σbound)
          = ∑ m : Fin M, (∑ q : Fin Q,
            ‖sourceCellCoefficient K node weight κ m q‖) * σbound := by
              apply Finset.sum_congr rfl
              intro m hm
              exact (Finset.sum_mul _ _ _).symm
        _ = (∑ m : Fin M, ∑ q : Fin Q,
            ‖sourceCellCoefficient K node weight κ m q‖) * σbound :=
          (Finset.sum_mul _ _ _).symm

theorem clause30_discrete_source_zero_of_zero {Q M : ℕ} (K : ℕ) (node weight : Fin Q → ℝ)
    (κ : ℝ → ℂ) :
    discreteSourceTerm M K node weight κ (fun _ => (0 : QState I)) = 0 := by
  unfold discreteSourceTerm
  simp

theorem clause30_single_evaluation_point_bridge {Q : ℕ} (Φ : ℝ → Matrix I I ℂ)
    (a h : ℝ) (hpos : 0 < h) (hcont : Continuous fun k => ‖iteratedDeriv (2 * Q) Φ k‖) :
    ∃ k ∈ Icc a (a + h),
      ‖iteratedDeriv (2 * Q) Φ k‖ =
        sSup ((Icc a (a + h)).image (fun j => ‖iteratedDeriv (2 * Q) Φ j‖)) :=
  clause30_correction_supremum_attained Φ a h hpos hcont

theorem clause30_operator_norm_submultiplicative (A B : Matrix I I ℂ) :
    ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  l2_opNorm_mul A B

theorem clause30_all_ones_operator_norm (d : ℕ) (hd : 0 < d) :
    ‖allOnesMatrix d‖ = (d : ℝ) := by
  have hmul : (allOnesMatrix d)ᴴ * allOnesMatrix d = (d : ℝ) • allOnesMatrix d := by
    ext i j
    simp [allOnesMatrix, Matrix.mul_apply, Matrix.smul_apply]
  have hself := l2_opNorm_conjTranspose_mul_self (allOnesMatrix d)
  rw [hmul, norm_smul] at hself
  have hne0 : allOnesMatrix d ≠ 0 := by
    intro hz
    have hz' := congrFun (congrFun hz ⟨0, hd⟩) ⟨0, hd⟩
    simp [allOnesMatrix] at hz'
  have hne : ‖allOnesMatrix d‖ ≠ 0 := ne_of_gt (norm_pos_iff.2 hne0)
  have hposd : 0 ≤ (d : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hposd] at hself
  have hmul' : ‖allOnesMatrix d‖ * (‖allOnesMatrix d‖ - (d : ℝ)) = 0 := by nlinarith
  rcases mul_eq_zero.mp hmul' with h | h
  · exact absurd h hne
  · linarith

theorem clause30_entrywise_sup_does_not_bound_operator_norm (d : ℕ) (hd : 1 < d) :
    entrywiseSup (allOnesMatrix d) = 1 ∧ 1 < ‖allOnesMatrix d‖ := by
  constructor
  · have hd0 : 0 < d := by omega
    haveI : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
    rw [entrywiseSup]
    simp [allOnesMatrix, ciSup_const]
  · rw [clause30_all_ones_operator_norm d (by omega)]
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 2 ≤ d by omega)
    linarith

theorem clause30_dimension_factor_is_real (d : ℕ) (hd : 1 < d) :
    (1 : ℝ) < ‖allOnesMatrix d‖ ∧ entrywiseSup (allOnesMatrix d) = 1 :=
  ⟨(clause30_entrywise_sup_does_not_bound_operator_norm d hd).2,
   (clause30_entrywise_sup_does_not_bound_operator_norm d hd).1⟩

theorem clause30_discrete_source_uses_composite_rule {Q M : ℕ} (K : ℕ)
    (node weight : Fin Q → ℝ) (κ : ℝ → ℂ) (m : Fin M) (q : Fin Q) :
    sourceCellCoefficient K node weight κ m q = compositeCoefficients K node weight κ m q := rfl

theorem clause30_discrete_source_mass_is_composite_mass {Q M : ℕ} (K : ℕ)
    (node weight : Fin Q → ℝ) (κ : ℝ → ℂ) :
    sourceCoefficientMass M K node weight κ = compositeCoefficientMass M K node weight κ := by
  unfold sourceCoefficientMass compositeCoefficientMass
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro q _
  rw [clause30_discrete_source_uses_composite_rule]

theorem clause30_cell_remainder_zero (Q : ℕ) (c h : ℝ) :
    lchs30CellRemainder Q c 0 h = 0 := by
  simp [lchs30CellRemainder]

theorem clause30_cell_remainder_monotone (Q : ℕ) (c h : ℝ) {s s' : ℝ}
    (hcs : 0 ≤ c) (hh : 0 ≤ h) (hs : s ≤ s') :
    lchs30CellRemainder Q c s h ≤ lchs30CellRemainder Q c s' h := by
  simp only [lchs30CellRemainder]
  have hpow : 0 ≤ h ^ (2 * Q + 1) := by positivity
  have := mul_le_mul_of_nonneg_right hs (mul_nonneg hcs hpow)
  nlinarith [this]

theorem clause30_composite_remainder_power (Q M : ℕ) (c s h : ℝ) :
    lchs30CompositeRemainder Q M c s h = c * s * ((M : ℝ) * h) * h ^ (2 * Q) := by
  have hpow : h ^ (2 * Q + 1) = h ^ (2 * Q) * h := by
    rw [pow_add, pow_one]
  simp only [lchs30CompositeRemainder, lchs30CellRemainder]
  rw [hpow]
  ring

theorem clause31_near_optimal_ledger_cells (β T Λ : ℝ) (K : ℕ) (ε : ℝ) (rounds shots : ℕ) :
    (lchs31NearOptimalLedger β T Λ K ε rounds shots).cells =
        (compositeCostLedger β T Λ K ε).cells ∧
      (lchs31NearOptimalLedger β T Λ K ε rounds shots).nodesPerCell =
        (compositeCostLedger β T Λ K ε).nodesPerCell ∧
      (lchs31NearOptimalLedger β T Λ K ε rounds shots).loadedPairs =
        (compositeCostLedger β T Λ K ε).propagatorEvaluations := by
  simp [lchs31NearOptimalLedger, compositeCostLedger]

theorem clause31_near_optimal_ledger_reconciliation (β T Λ : ℝ) (K : ℕ) (ε : ℝ)
    (rounds shots : ℕ) :
    (lchs31NearOptimalLedger β T Λ K ε rounds shots).loadedPairs =
        (lchs31NearOptimalLedger β T Λ K ε rounds shots).cells *
          (lchs31NearOptimalLedger β T Λ K ε rounds shots).nodesPerCell ∧
      (lchs31NearOptimalLedger β T Λ K ε rounds shots).loadingBits = loadingBits ε ∧
      lchs31TotalCost (lchs31NearOptimalLedger β T Λ K ε rounds shots) =
        (lchs31NearOptimalLedger β T Λ K ε rounds shots).loadedPairs + rounds + shots := by
  simp [lchs31NearOptimalLedger, lchs31TotalCost, compositeCostLedger] <;> ring

theorem clause31_near_optimal_polylog_precision (β T Λ : ℝ) (K : ℕ) (ε : ℝ)
    (rounds shots : ℕ) :
    (lchs31NearOptimalLedger β T Λ K ε rounds shots).nodesPerCell =
        compositeNodeCount β K ε ∧
      (lchs31NearOptimalLedger β T Λ K ε rounds shots).loadingBits =
        Nat.ceil (Real.log (1 / ε) / Real.log 2) + 1 := by
  simp [lchs31NearOptimalLedger, compositeCostLedger, loadingBits]

theorem clause31_near_optimal_node_count_log (β K ε : ℝ) :
    compositeNodeCount β K ε ≤
      1 + Nat.ceil (Real.log ((8 / (3 * highKernelC β)) * K / ε) / Real.log 4) := by
  unfold compositeNodeCount
  omega

theorem clause31_loading_count (M Q : ℕ) : loadingCount M Q = M * Q := rfl

theorem clause31_loading_bits_logarithmic (ε : ℝ) :
    loadingBits ε = Nat.ceil (Real.log (1 / ε) / Real.log 2) + 1 := rfl

theorem clause31_amplification_rounds_pos {Q : ℕ} (M K : ℕ) (node weight : Fin Q → ℝ)
    (κ : ℝ → ℂ) :
    1 ≤ amplificationRounds M K node weight κ := by
  unfold amplificationRounds
  exact le_max_left _ _

theorem clause31_amplification_rounds_le_mass {Q : ℕ} (M K : ℕ) (node weight : Fin Q → ℝ)
    (κ : ℝ → ℂ) (hl2 : 0 < compositeCoefficientL2 M K node weight κ) :
    (amplificationRounds M K node weight κ : ℝ)
      ≤ compositeCoefficientMass M K node weight κ /
        compositeCoefficientL2 M K node weight κ + 1 := by
  have hceil : (Nat.ceil (compositeCoefficientMass M K node weight κ /
      compositeCoefficientL2 M K node weight κ) : ℝ)
      ≤ compositeCoefficientMass M K node weight κ /
        compositeCoefficientL2 M K node weight κ + 1 := by
    have hx0 : 0 ≤ compositeCoefficientMass M K node weight κ /
        compositeCoefficientL2 M K node weight κ := by
      have hnonneg : 0 ≤ compositeCoefficientMass M K node weight κ := by
        unfold compositeCoefficientMass
        positivity
      exact div_nonneg hnonneg (le_of_lt hl2)
    exact le_of_lt (Nat.ceil_lt_add_one hx0)
  have hmax : (max 1 (Nat.ceil (compositeCoefficientMass M K node weight κ /
      compositeCoefficientL2 M K node weight κ)) : ℝ)
      ≤ compositeCoefficientMass M K node weight κ /
        compositeCoefficientL2 M K node weight κ + 1 := by
    have hx0' : 0 ≤ compositeCoefficientMass M K node weight κ /
        compositeCoefficientL2 M K node weight κ := by
      have hnonneg : 0 ≤ compositeCoefficientMass M K node weight κ := by
        unfold compositeCoefficientMass
        positivity
      exact div_nonneg hnonneg (le_of_lt hl2)
    exact (max_le_iff).2 ⟨by linarith [hx0'], hceil⟩
  have hgoal : (amplificationRounds M K node weight κ : ℝ)
      = max 1 (Nat.ceil (compositeCoefficientMass M K node weight κ /
        compositeCoefficientL2 M K node weight κ) : ℝ) := by
    unfold amplificationRounds
    simp [Nat.cast_max, Nat.cast_one]
  rw [hgoal]
  exact hmax

theorem clause31_lcu_term_count (M Q : ℕ) : loadingCount M Q = M * Q :=
  clause31_loading_count M Q

theorem clause32_product_norm_le (δ : ℝ) (hδ : 0 ≤ δ) (A B : Matrix I I ℂ)
    (hA : ‖A‖ ≤ 1 + δ) (hB : ‖B‖ ≤ 1 + δ) :
    ‖A * B‖ ≤ (1 + δ) ^ 2 := by
  calc ‖A * B‖ ≤ ‖A‖ * ‖B‖ := l2_opNorm_mul A B
    _ ≤ (1 + δ) * (1 + δ) := mul_le_mul hA hB (by positivity) (by positivity)
    _ = (1 + δ) ^ 2 := by ring

theorem clause32_list_product_norm_le (δ : ℝ) (hδ : 0 ≤ δ) :
    ∀ (l : List (Matrix I I ℂ)), l ≠ [] → (∀ A ∈ l, ‖A‖ ≤ 1 + δ) →
      ‖l.prod‖ ≤ (1 + δ) ^ l.length := by
  intro l
  induction l with
  | nil =>
      intro h
      exact absurd rfl h
  | cons A l ih =>
      intro _ hA
      have hA' : ‖A‖ ≤ 1 + δ := hA A (by simp)
      have hl : ∀ B ∈ l, ‖B‖ ≤ 1 + δ := fun B hB => hA B (by simp [hB])
      by_cases hl_nil : l = []
      · subst hl_nil
        simp
        exact hA'
      · rw [List.prod_cons, List.length_cons]
        calc ‖A * l.prod‖ ≤ ‖A‖ * ‖l.prod‖ := l2_opNorm_mul _ _
          _ ≤ (1 + δ) * (1 + δ) ^ l.length := by
              refine mul_le_mul hA' ?_ (by positivity) (by positivity)
              exact ih hl_nil hl
          _ = (1 + δ) ^ (l.length + 1) := by ring

theorem clause32_one_le_pow (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) : 1 ≤ (1 + δ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      calc 1 = 1 * 1 := by ring
        _ ≤ (1 + δ) * (1 + δ) ^ n := by
            exact mul_le_mul (by linarith) ih (by positivity) (by positivity)
        _ = (1 + δ) ^ (n + 1) := by rw [pow_succ]; ring

theorem clause32_relative_error_le (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    (1 + δ) ^ n - 1 ≤ n * δ * (1 + δ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hbase : 0 ≤ 1 + δ := by linarith
      have hmul : (1 + δ) * (1 + δ) ^ n = (1 + δ) ^ (n + 1) := by
        rw [pow_succ]
        ring
      have hpow : 1 ≤ (1 + δ) ^ (n + 1) := clause32_one_le_pow δ hδ (n + 1)
      have hpow0 : 0 ≤ (1 + δ) ^ (n + 1) := by linarith
      have hle : δ ≤ δ * (1 + δ) ^ (n + 1) := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ δ) hpow0]
      calc (1 + δ) ^ (n + 1) - 1
          = (1 + δ) * ((1 + δ) ^ n - 1) + δ := by rw [← hmul]; ring
        _ ≤ (1 + δ) * (n * δ * (1 + δ) ^ n) + δ := by
            have h := mul_le_mul_of_nonneg_left ih hbase
            linarith
        _ = n * δ * (1 + δ) ^ (n + 1) + δ := by rw [← hmul]; ring
        _ ≤ n * δ * (1 + δ) ^ (n + 1) + δ * (1 + δ) ^ (n + 1) :=
          add_le_add_right hle _
        _ = ((n + 1 : ℕ) : ℝ) * δ * (1 + δ) ^ (n + 1) := by
            have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by exact_mod_cast rfl
            rw [hcast]
            ring

theorem clause32_filter_round_count {X : Type} [Fintype X] [Nonempty X]
    (g : GibbsInput X) : filterRoundCount g = 1 / filterSuccessProbability g := rfl

theorem clause32_filter_round_count_ge_one {X : Type} [Fintype X] [Nonempty X]
    (g : GibbsInput X) (hT : 0 < g.temperature) (hp : 0 < filterSuccessProbability g) :
    1 ≤ filterRoundCount g := by
  rw [filterRoundCount]
  exact clause32_filter_success_fee g hT hp

theorem clause32_observable_sample_count {X : Type} [Fintype X] [Nonempty X]
    (g : GibbsInput X) (ε δ : ℝ) :
    observableSampleCount g ε δ = gibbsSampleCount g ε δ := rfl

theorem clause32_source_preparation_term_count (M Q : ℕ) :
    loadingCount M Q = M * Q :=
  clause31_loading_count M Q

theorem lchs30_peano_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f f' f'' : ℝ → E) (a b : ℝ)
    (h₁ : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (h₂ : ∀ x ∈ Set.uIcc a b, HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f' (Set.uIcc a b))
    (hc' : ContinuousOn f'' (Set.uIcc a b)) :
    f b - f a - (b - a) • f' a = ∫ y in a..b, (b - y) • f'' y := by
  have hg : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => (b - y) • f' y)
        ((b - x) • f'' x + (-1 : ℝ) • f' x) x := by
    intro x hx
    have hs : HasDerivAt (fun y : ℝ => b - y) (-1 : ℝ) x := (hasDerivAt_id x).const_sub b
    simpa only [] using! (hs.smul (h₂ x hx))
  have hgc : ContinuousOn (fun y : ℝ => (b - y) • f' y) (Set.uIcc a b) :=
    (continuousOn_const.sub continuousOn_id).smul hc
  have hgd : ContinuousOn (fun x : ℝ => (b - x) • f'' x + (-1 : ℝ) • f' x)
      (Set.uIcc a b) := by
    refine ((continuousOn_const.sub continuousOn_id).smul hc').add ?_
    exact (continuousOn_const.smul hc)
  have hker : ContinuousOn (fun y : ℝ => (b - y) • f'' y) (Set.uIcc a b) :=
    (continuousOn_const.sub continuousOn_id).smul hc'
  have hftcg : ∫ y in a..b, ((b - y) • f'' y + (-1 : ℝ) • f' y)
      = (fun y : ℝ => (b - y) • f' y) b - (fun y : ℝ => (b - y) • f' y) a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hg hgd.intervalIntegrable
  have hftcf : ∫ y in a..b, f' y = f b - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt h₁ hc.intervalIntegrable
  have hconv : (∫ y in a..b, (b - y) • f'' y + (-1 : ℝ) • f' y)
      = ∫ y in a..b, ((b - y) • f'' y - f' y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    simp only [neg_smul, one_smul, sub_eq_add_neg]
  have hsub : ∫ y in a..b, ((b - y) • f'' y - f' y)
      = (∫ y in a..b, (b - y) • f'' y) - ∫ y in a..b, f' y := by
    rw [intervalIntegral.integral_sub hker.intervalIntegrable hc.intervalIntegrable]
  have hgb : (fun y : ℝ => (b - y) • f' y) b = 0 := by simp
  have hga : (fun y : ℝ => (b - y) • f' y) a = (b - a) • f' a := by simp
  have hgval : (fun y : ℝ => (b - y) • f' y) b - (fun y : ℝ => (b - y) • f' y) a
      = -(b - a) • f' a := by rw [hgb, hga, zero_sub, neg_smul]
  have hkey : ∫ y in a..b, (b - y) • f'' y = f b - f a - (b - a) • f' a := by
    have h1 : ∫ y in a..b, (b - y) • f'' y
        = (∫ y in a..b, ((b - y) • f'' y - f' y)) + ∫ y in a..b, f' y := by
      rw [hsub]
      abel
    rw [h1, ← hconv, hftcg, hgval, hftcf]
    simp only [neg_smul, sub_eq_add_neg]
    abel
  rw [hkey]

theorem lchs30_peano_remainder_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f f' f'' : ℝ → E) (a b : ℝ) (C : ℝ) (hab : a ≤ b)
    (h₁ : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (h₂ : ∀ x ∈ Set.uIcc a b, HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f' (Set.uIcc a b))
    (hc' : ContinuousOn f'' (Set.uIcc a b))
    (hC : ∀ x ∈ Set.uIcc a b, ‖f'' x‖ ≤ C) :
    ‖f b - f a - (b - a) • f' a‖ ≤ C * (b - a) ^ 2 / 2 := by
  have hstep12 : ‖∫ y in a..b, (b - y) • f'' y‖ ≤ ∫ y in a..b, (b - y) * C := by
    refine intervalIntegral.norm_integral_le_of_norm_le
      (f := fun y : ℝ => (b - y) • f'' y) hab ?_ ?_
    · filter_upwards with y hy
      have hyI : y ∈ Set.uIcc a b := by
        rw [Set.uIcc_of_le hab]
        exact ⟨le_of_lt hy.1, hy.2⟩
      have hy2 : y ≤ b := hy.2
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_left (hC y hyI) (by linarith)
    · exact
        ((continuousOn_const.sub continuousOn_id).smul continuousOn_const :
          ContinuousOn (fun y : ℝ => (b - y) * C) (Set.uIcc a b)).intervalIntegrable
  have hstep3 : ∫ y in a..b, (b - y) * C = ((b - a) ^ 2 / 2) * C := by
    rw [intervalIntegral.integral_mul_const]
    congr 1
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => b) (g := fun y : ℝ => y)
        (continuousOn_const.intervalIntegrable)
        (continuousOn_id.intervalIntegrable)]
    have h1 : ∫ y in a..b, b = (b - a) * b := by
      rw [intervalIntegral.integral_const]
      simp
    have h2 : ∫ y in a..b, y = (b ^ 2 - a ^ 2) / 2 := by simp
    rw [h1, h2]
    ring
  calc
    ‖f b - f a - (b - a) • f' a‖ = ‖∫ y in a..b, (b - y) • f'' y‖ := by
      rw [lchs30_peano_remainder f f' f'' a b h₁ h₂ hc hc']
    _ ≤ ∫ y in a..b, (b - y) * C := hstep12
    _ = ((b - a) ^ 2 / 2) * C := hstep3
    _ = C * (b - a) ^ 2 / 2 := by ring

theorem lchs30_peano_remainder_matrix (Φ Φ' Φ'' : ℝ → Matrix I I ℂ) (a b : ℝ)
    (h₁ : ∀ x ∈ Set.uIcc a b, HasDerivAt Φ (Φ' x) x)
    (h₂ : ∀ x ∈ Set.uIcc a b, HasDerivAt Φ' (Φ'' x) x)
    (hc : ContinuousOn Φ' (Set.uIcc a b))
    (hc' : ContinuousOn Φ'' (Set.uIcc a b)) :
    Φ b - Φ a - (b - a) • Φ' a = ∫ y in a..b, (b - y) • Φ'' y :=
  lchs30_peano_remainder Φ Φ' Φ'' a b h₁ h₂ hc hc'

theorem lchs30_peano_remainder_norm_matrix (Φ Φ' Φ'' : ℝ → Matrix I I ℂ) (a b : ℝ) (C : ℝ)
    (hab : a ≤ b)
    (h₁ : ∀ x ∈ Set.uIcc a b, HasDerivAt Φ (Φ' x) x)
    (h₂ : ∀ x ∈ Set.uIcc a b, HasDerivAt Φ' (Φ'' x) x)
    (hc : ContinuousOn Φ' (Set.uIcc a b))
    (hc' : ContinuousOn Φ'' (Set.uIcc a b))
    (hC : ∀ x ∈ Set.uIcc a b, ‖Φ'' x‖ ≤ C) :
    ‖Φ b - Φ a - (b - a) • Φ' a‖ ≤ C * (b - a) ^ 2 / 2 :=
  lchs30_peano_remainder_norm Φ Φ' Φ'' a b C hab h₁ h₂ hc hc' hC

theorem lchs30_peano_composite_scaling (M : ℕ) (s h : ℝ) :
    (M : ℝ) * (s * h ^ 2 / 2) = s * ((M : ℝ) * h) * h / 2 := by
  ring

theorem clause30_endpoint :
    (closure lowerOpenHalfPlane = lowerClosedHalfPlane) ∧
    (kernelDomainGap = kernelFrontier) ∧
    (¬ (∀ f : ℂ → ℂ, AnalyticOn ℂ f lowerOpenHalfPlane → ContinuousOn f lowerClosedHalfPlane)) ∧
    (¬ (∀ f : ℂ → ℂ, ContinuousOn f lowerClosedHalfPlane → AnalyticOn ℂ f lowerOpenHalfPlane)) ∧
    (∀ (Q M : ℕ) (K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ),
      ∀ m : Fin M, ∀ q : Fin Q,
        sourceCellCoefficient K node weight κ m q
          = (((compositeCellWidth K M / 2 : ℝ) : ℂ) * ((weight q : ℝ) : ℂ)) *
            κ (compositeNodeAt K node m q)) ∧
    (∀ (d : ℕ), 0 < d → ‖allOnesMatrix d‖ = (d : ℝ)) ∧
    (∀ (d : ℕ), 1 < d → entrywiseSup (allOnesMatrix d) = 1 ∧ 1 < ‖allOnesMatrix d‖) ∧
    (∀ (Q M : ℕ) (K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ),
      ∀ m : Fin M, ∀ q : Fin Q,
        sourceCellCoefficient K node weight κ m q = compositeCoefficients K node weight κ m q) ∧
    (∀ (Q M : ℕ) (K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ),
      sourceCoefficientMass M K node weight κ = compositeCoefficientMass M K node weight κ) ∧
    (∀ Q : ℕ, ∀ c h : ℝ, lchs30CellRemainder Q c 0 h = 0) ∧
    (∀ Q : ℕ, ∀ c h : ℝ, ∀ s s' : ℝ, 0 ≤ c → 0 ≤ h → s ≤ s' →
      lchs30CellRemainder Q c s h ≤ lchs30CellRemainder Q c s' h) ∧
    (∀ Q M : ℕ, ∀ c s h : ℝ,
      lchs30CompositeRemainder Q M c s h = c * s * ((M : ℝ) * h) * h ^ (2 * Q)) ∧
    (∀ (E : Type _) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (f f' f'' : ℝ → E) (a b : ℝ),
      (∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x) →
      (∀ x ∈ Set.uIcc a b, HasDerivAt f' (f'' x) x) →
      ContinuousOn f' (Set.uIcc a b) → ContinuousOn f'' (Set.uIcc a b) →
      f b - f a - (b - a) • f' a = ∫ y in a..b, (b - y) • f'' y) ∧
    (∀ (E : Type _) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (f f' f'' : ℝ → E) (a b : ℝ) (C : ℝ), a ≤ b →
      (∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x) →
      (∀ x ∈ Set.uIcc a b, HasDerivAt f' (f'' x) x) →
      ContinuousOn f' (Set.uIcc a b) → ContinuousOn f'' (Set.uIcc a b) →
      (∀ x ∈ Set.uIcc a b, ‖f'' x‖ ≤ C) →
      ‖f b - f a - (b - a) • f' a‖ ≤ C * (b - a) ^ 2 / 2) ∧
    (∀ (Φ Φ' Φ'' : ℝ → Matrix I I ℂ) (a b : ℝ),
      (∀ x ∈ Set.uIcc a b, HasDerivAt Φ (Φ' x) x) →
      (∀ x ∈ Set.uIcc a b, HasDerivAt Φ' (Φ'' x) x) →
      ContinuousOn Φ' (Set.uIcc a b) → ContinuousOn Φ'' (Set.uIcc a b) →
      Φ b - Φ a - (b - a) • Φ' a = ∫ y in a..b, (b - y) • Φ'' y) ∧
    (∀ (Φ Φ' Φ'' : ℝ → Matrix I I ℂ) (a b : ℝ) (C : ℝ), a ≤ b →
      (∀ x ∈ Set.uIcc a b, HasDerivAt Φ (Φ' x) x) →
      (∀ x ∈ Set.uIcc a b, HasDerivAt Φ' (Φ'' x) x) →
      ContinuousOn Φ' (Set.uIcc a b) → ContinuousOn Φ'' (Set.uIcc a b) →
      (∀ x ∈ Set.uIcc a b, ‖Φ'' x‖ ≤ C) →
      ‖Φ b - Φ a - (b - a) • Φ' a‖ ≤ C * (b - a) ^ 2 / 2) ∧
    (∀ M : ℕ, ∀ s h : ℝ, (M : ℝ) * (s * h ^ 2 / 2) = s * ((M : ℝ) * h) * h / 2) := by
  refine ⟨clause30_closed_is_closure_of_open, clause30_kernel_domain_gap_eq_frontier, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hall
    exact clause30_frontier_indicator_not_continuous_closed
      (hall (frontierIndicator : ℂ → ℂ) clause30_frontier_indicator_analytic_open)
  · intro hall
    exact clause30_conj_not_analytic_open
      (hall (conj : ℂ → ℂ) clause30_conj_continuous_closed)
  · intro Q M K node weight κ m q
    exact clause30_discrete_source_coefficient K node weight κ m q
  · intro d hd
    exact clause30_all_ones_operator_norm d hd
  · intro d hd
    exact clause30_entrywise_sup_does_not_bound_operator_norm d hd
  · intro Q M K node weight κ m q
    exact clause30_discrete_source_uses_composite_rule K node weight κ m q
  · intro Q M K node weight κ
    exact clause30_discrete_source_mass_is_composite_mass K node weight κ
  · intro Q c h
    exact clause30_cell_remainder_zero Q c h
  · intro Q c h s s' hc hh hs
    exact clause30_cell_remainder_monotone Q c h hc hh hs
  · intro Q M c s h
    exact clause30_composite_remainder_power Q M c s h
  · intro E inst inst' inst'' f f' f'' a b h1 h2 hc hc'
    exact lchs30_peano_remainder f f' f'' a b h1 h2 hc hc'
  · intro E inst inst' inst'' f f' f'' a b C hab h1 h2 hc hc' hC
    exact lchs30_peano_remainder_norm f f' f'' a b C hab h1 h2 hc hc' hC
  · intro Φ Φ' Φ'' a b h1 h2 hc hc'
    exact lchs30_peano_remainder_matrix Φ Φ' Φ'' a b h1 h2 hc hc'
  · intro Φ Φ' Φ'' a b C hab h1 h2 hc hc' hC
    exact lchs30_peano_remainder_norm_matrix Φ Φ' Φ'' a b C hab h1 h2 hc hc' hC
  · intro M s h
    exact lchs30_peano_composite_scaling M s h

theorem clause31_endpoint :
    (∀ M Q : ℕ, loadingCount M Q = M * Q) ∧
    (∀ ε : ℝ, loadingBits ε = Nat.ceil (Real.log (1 / ε) / Real.log 2) + 1) ∧
    (∀ (Q M : ℕ) (K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ),
      1 ≤ amplificationRounds M K node weight κ) ∧
    (∀ (Q M : ℕ) (K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ),
      0 < compositeCoefficientL2 M K node weight κ →
        (amplificationRounds M K node weight κ : ℝ)
          ≤ compositeCoefficientMass M K node weight κ /
            compositeCoefficientL2 M K node weight κ + 1) ∧
    (∀ (β T Λ : ℝ) (K : ℕ) (ε : ℝ) (rounds shots : ℕ),
      (lchs31NearOptimalLedger β T Λ K ε rounds shots).loadedPairs =
        (lchs31NearOptimalLedger β T Λ K ε rounds shots).cells *
          (lchs31NearOptimalLedger β T Λ K ε rounds shots).nodesPerCell ∧
      lchs31TotalCost (lchs31NearOptimalLedger β T Λ K ε rounds shots) =
        (lchs31NearOptimalLedger β T Λ K ε rounds shots).loadedPairs + rounds + shots) ∧
    (∀ (β T Λ : ℝ) (K : ℕ) (ε : ℝ) (rounds shots : ℕ),
      (lchs31NearOptimalLedger β T Λ K ε rounds shots).nodesPerCell =
          compositeNodeCount β K ε ∧
        (lchs31NearOptimalLedger β T Λ K ε rounds shots).loadingBits =
          Nat.ceil (Real.log (1 / ε) / Real.log 2) + 1) ∧
    (∀ β K ε : ℝ, compositeNodeCount β K ε ≤
      1 + Nat.ceil (Real.log ((8 / (3 * highKernelC β)) * K / ε) / Real.log 4)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M Q
    exact clause31_loading_count M Q
  · intro ε
    exact clause31_loading_bits_logarithmic ε
  · intro Q M K node weight κ
    exact clause31_amplification_rounds_pos M K node weight κ
  · intro Q M K node weight κ hl2
    exact clause31_amplification_rounds_le_mass M K node weight κ hl2
  · intro β T Λ K ε rounds shots
    exact ⟨(clause31_near_optimal_ledger_reconciliation β T Λ K ε rounds shots).1,
      (clause31_near_optimal_ledger_reconciliation β T Λ K ε rounds shots).2.2⟩
  · intro β T Λ K ε rounds shots
    exact clause31_near_optimal_polylog_precision β T Λ K ε rounds shots
  · intro β K ε
    exact clause31_near_optimal_node_count_log β K ε

theorem clause32_endpoint :
    (∀ (δ : ℝ) (A B : Matrix I I ℂ), 0 ≤ δ → ‖A‖ ≤ 1 + δ → ‖B‖ ≤ 1 + δ →
      ‖A * B‖ ≤ (1 + δ) ^ 2) ∧
    (∀ (δ : ℝ) (l : List (Matrix I I ℂ)), 0 ≤ δ → l ≠ [] →
      (∀ A ∈ l, ‖A‖ ≤ 1 + δ) → ‖l.prod‖ ≤ (1 + δ) ^ l.length) ∧
    (∀ (n : ℕ) (δ : ℝ), 0 ≤ δ → (1 + δ) ^ n - 1 ≤ n * δ * (1 + δ) ^ n) ∧
    (∀ M Q : ℕ, loadingCount M Q = M * Q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro δ A B hδ hA hB
    exact clause32_product_norm_le δ hδ A B hA hB
  · intro δ l hδ hl hA
    exact clause32_list_product_norm_le δ hδ l hl hA
  · intro n δ hδ
    exact clause32_relative_error_le n δ hδ
  · intro M Q
    exact clause32_source_preparation_term_count M Q

theorem clause32_fee_endpoint {X : Type} [Fintype X] [Nonempty X] (g : GibbsInput X) :
    filterRoundCount g = 1 / filterSuccessProbability g ∧
      ∀ ε δ : ℝ, observableSampleCount g ε δ = gibbsSampleCount g ε δ :=
  ⟨clause32_filter_round_count g, fun ε δ => clause32_observable_sample_count g ε δ⟩

end Qatlib.Concepts.RandCompile.ChannelBudget.HighPrecisionLchsRefined
