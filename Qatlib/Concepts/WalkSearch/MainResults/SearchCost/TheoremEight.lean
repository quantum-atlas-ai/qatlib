/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.SearchCost.TheoremSeven
import Qatlib.Concepts.WalkSearch.MnrsAmplify.Proposition3

/-!
# An MNRS search bound without the extra logarithm

`mnrs_search_theorem_eight` combines the abstract tolerant amplification guarantees with the
reflection ledger to obtain a cost proportional to `S + (U / sqrt δ + C) / sqrt ε`. Its
hypotheses explicitly require an invariant subspace, approximate reflections, and a minimal
amplification level; `mnrs_theoremEight_unique_singularValue` supplies the stated uniqueness
result for a finite Markov discriminant. For background on search via quantum walks, see
[MagniezNayakRolandSantha2011].

## Main statements

* `mnrsTheoremEightCostConstant`: The constant `6400 * π + 2` used in the MNRS Theorem 8 search
  cost bound.
* `mnrs_search_theorem_eight`: Under the invariant subspace, approximate reflection, schedule,
  and ledger hypotheses, tolerant success is zero at zero marked mass and at least `1 / 24`
  otherwise, with the stated cost bound proportional to `S + (U / sqrt δ + C) / sqrt ε`; see
  [Magniez et al., Theorem 8][MagniezNayakRolandSantha2011].

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Real BigOperators
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

namespace Qatlib.Concepts.WalkSearch.MainResults.SearchCost

/-- The constant `6400 * π + 2` used in the MNRS Theorem 8 search cost bound. -/
noncomputable def mnrsTheoremEightCostConstant : ℝ := 6400 * Real.pi + 2

/-- For an irreducible stochastic matrix with positive diagonal and a stationary probability
vector, the discriminant has exactly one singular value index with value one; see [Magniez
et al., Theorem 8][MagniezNayakRolandSantha2011]. -/
theorem mnrs_theoremEight_unique_singularValue {X : Type} [Fintype X] [DecidableEq X]
    [Nonempty X] (P : Matrix X X ℝ) (nu : X → ℝ) (hP : P.IsIrreducible)
    (hrow : ∀ x, ∑ y, P x y = 1) (hdiag : ∀ x, 0 < P x x) (hν0 : ∀ x, 0 ≤ nu x)
    (hν1 : ∑ x, nu x = 1) (hstat : ∀ y, ∑ x, nu x * P x y = nu y) :
    ∃! k : ℕ, (Matrix.toEuclideanLin (mnrsDiscriminant P nu)).singularValues k = 1 :=
  search_via_quantum_walk_proposition3 X P nu hP hrow hdiag hν0 hν1 hstat

/-- Under the stated amplification and reflection fee bounds, the recursive cost expression is
at most `3200 * π / sqrt ε * (U / sqrt δ + C)`. -/
theorem mnrs_eight_order_form {ε δ U C c₁ : ℝ} (tMax : ℕ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hU : 0 ≤ U) (hC : 0 ≤ C) (hc₁ : 0 ≤ c₁)
    (hc₁U : c₁ ≤ 80 * Real.pi * U / Real.sqrt δ)
    (hmax : 3 ^ tMax * Real.arcsin (Real.sqrt ε) ≤ 3 * Real.pi / 4) :
    2 * 3 ^ tMax * (c₁ * (Real.log 72 + 3) + C) ≤
      3200 * Real.pi * (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U + C) := by
  have hεroot : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hroot_le : Real.sqrt ε ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hε1
  have hsin : Real.sin (Real.arcsin (Real.sqrt ε)) = Real.sqrt ε :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg ε]) hroot_le
  have harc : Real.sqrt ε ≤ Real.arcsin (Real.sqrt ε) := by
    have h0 : 0 ≤ Real.arcsin (Real.sqrt ε) := (Real.arcsin_pos.mpr hεroot).le
    calc Real.sqrt ε = Real.sin (Real.arcsin (Real.sqrt ε)) := hsin.symm
      _ ≤ Real.arcsin (Real.sqrt ε) := by
        rcases eq_or_lt_of_le h0 with h | h
        · rw [← h, Real.sin_zero]
        · exact (Real.sin_lt h).le
  have hpos : 0 < Real.arcsin (Real.sqrt ε) := Real.arcsin_pos.mpr hεroot
  have h3 : (3 : ℝ) ^ tMax ≤ (3 * Real.pi / 4) / Real.arcsin (Real.sqrt ε) := by
    rw [le_div_iff₀ hpos]
    linarith
  have hstep : (3 * Real.pi / 4) / Real.arcsin (Real.sqrt ε) ≤
      (3 * Real.pi / 4) / Real.sqrt ε :=
    div_le_div_of_nonneg_left (by positivity) hεroot harc
  have hscale : 2 * 3 ^ tMax ≤ 5 * (1 / Real.sqrt ε) := by
    have hpi : 3 * Real.pi / 2 ≤ 5 := by
      have := Real.pi_lt_d2
      linarith
    have hinv : 0 ≤ (Real.sqrt ε)⁻¹ := (inv_pos.mpr hεroot).le
    have h1 := mul_le_mul_of_nonneg_right hpi hinv
    have hfin : 2 * ((3 * Real.pi / 4) / Real.sqrt ε) ≤ 5 * (1 / Real.sqrt ε) := by
      have heq : 2 * (3 * Real.pi * 4⁻¹ * (Real.sqrt ε)⁻¹) =
          3 * Real.pi / 2 * (Real.sqrt ε)⁻¹ := by ring
      rw [div_eq_mul_inv, div_eq_mul_inv, heq]
      simpa using h1
    nlinarith
  have hlog72 : Real.log 72 + 3 ≤ 8 := by
    have h72 : Real.log 72 ≤ 5 := by
      apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 72)).mpr
      have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5) 6
      norm_num [Finset.sum_range_succ] at hs
      linarith
    linarith
  have hmass : c₁ * (Real.log 72 + 3) + C ≤ 640 * Real.pi * U / Real.sqrt δ + C := by
    have h1 : c₁ * (Real.log 72 + 3) ≤ c₁ * 8 :=
      mul_le_mul_of_nonneg_left hlog72 hc₁
    have h2 : c₁ * 8 ≤ 640 * Real.pi * U / Real.sqrt δ := by
      have h := mul_le_mul_of_nonneg_left hc₁U (by norm_num : (0 : ℝ) ≤ 8)
      calc c₁ * 8 = 8 * c₁ := by ring
        _ ≤ 8 * (80 * Real.pi * U / Real.sqrt δ) := h
        _ = 640 * Real.pi * U / Real.sqrt δ := by ring
    linarith
  have hc0 : 0 ≤ c₁ * (Real.log 72 + 3) + C := by
    have hlog : 0 ≤ Real.log 72 := Real.log_nonneg (by norm_num)
    nlinarith
  have hprod : 2 * 3 ^ tMax * (c₁ * (Real.log 72 + 3) + C) ≤
      5 * (1 / Real.sqrt ε) * (640 * Real.pi * U / Real.sqrt δ + C) := by
    have hd0 : 0 ≤ 640 * Real.pi * U / Real.sqrt δ + C := by
      have hposδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
      have hnn : 0 ≤ 640 * Real.pi * U / Real.sqrt δ := by positivity
      linarith
    exact mul_le_mul hscale hmass hc0 (by positivity)
  have habsorb : 5 * (640 * Real.pi * U / Real.sqrt δ + C) ≤
      3200 * Real.pi * ((1 / Real.sqrt δ) * U + C) := by
    have hC5 : 5 * C ≤ 3200 * Real.pi * C := by
      have hpi : (5 : ℝ) ≤ 3200 * Real.pi := by
        have := Real.pi_gt_three
        nlinarith
      nlinarith
    calc 5 * (640 * Real.pi * U / Real.sqrt δ + C)
        = (3200 * Real.pi * U / Real.sqrt δ) + 5 * C := by ring
      _ ≤ 3200 * Real.pi * ((1 / Real.sqrt δ) * U) + 3200 * Real.pi * C := by
          have hEq : 3200 * Real.pi * U / Real.sqrt δ =
              3200 * Real.pi * ((1 / Real.sqrt δ) * U) := by ring
          linarith [hC5, hEq]
      _ = 3200 * Real.pi * ((1 / Real.sqrt δ) * U + C) := by ring
  calc 2 * 3 ^ tMax * (c₁ * (Real.log 72 + 3) + C)
      ≤ 5 * (1 / Real.sqrt ε) * (640 * Real.pi * U / Real.sqrt δ + C) := hprod
    _ = (1 / Real.sqrt ε) * (5 * (640 * Real.pi * U / Real.sqrt δ + C)) := by ring
    _ ≤ (1 / Real.sqrt ε) *
          (3200 * Real.pi * ((1 / Real.sqrt δ) * U + C)) :=
        mul_le_mul_of_nonneg_left habsorb (by positivity)
    _ = 3200 * Real.pi * (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U + C) := by ring

/-- Under the invariant subspace, approximate reflection, schedule, and ledger hypotheses,
tolerant success is zero at zero marked mass and at least `1 / 24` otherwise, with the
stated cost bound proportional to `S + (U / sqrt δ + C) / sqrt ε`; see [Magniez et al.,
Theorem 8][MagniezNayakRolandSantha2011]. -/
theorem mnrs_search_theorem_eight
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (Mr : Submodule ℂ W) (unmarkRefl : W ≃ₗᵢ[ℂ] W)
    (hneg : ∀ z ∈ Mr, unmarkRefl z = -z) (hpos : ∀ z ∈ Mrᗮ, unmarkRefl z = z)
    (x₀ : W) (hx₀ : ‖x₀‖ = 1)
    (ε δ U C S : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hU : 0 ≤ U) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hmass : markedMass Mr x₀ ≠ 0 → ε ≤ markedMass Mr x₀)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hrδ : r = 1 - δ)
    (tMax : ℕ) (R : ℕ → W ≃ₗᵢ[ℂ] W) (costR : ℕ → ℝ) (costMark : ℝ)
    (Rs : Submodule ℂ W) (hxRs : x₀ ∈ Rs)
    (hRsMark : ∀ z ∈ Rs, markProj Mr z ∈ Rs)
    (hRsR : ∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 → ∀ z ∈ Rs, R i z ∈ Rs)
    (hfix : ∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 →
      R i (raaState unmarkRefl R x₀ (i - 1)) = raaState unmarkRefl R x₀ (i - 1))
    (hclose : ∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 → ∀ ψ ∈ Rs,
      ψ ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ (i - 1)})ᗮ →
      ‖R i ψ + ψ - (2 : ℂ) • (lineProj (raaState unmarkRefl R x₀ (i - 1)) ψ)‖
        ≤ betaAt (1 / 72) i * ‖ψ‖)
    (hledger : ∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 →
      costR i ≤ mnrsReflectionLedger U (mnrsPhaseGap r) (betaAt (1 / 72) i))
    (hmarkC : costMark ≤ C)
    (hwin : 3 ^ tMax * Real.arcsin (Real.sqrt ε) ∈ Set.Icc (Real.pi / 4) (3 * Real.pi / 4))
    (hmin : ∀ j, j < tMax →
      3 ^ j * Real.arcsin (Real.sqrt ε) ∉ Set.Icc (Real.pi / 4) (3 * Real.pi / 4)) :
    (markedMass Mr x₀ = 0 →
      tolerantSuccess Mr (raaUnitary unmarkRefl R) x₀ (Nat.max tMax 1) = 0) ∧
    (markedMass Mr x₀ ≠ 0 →
      1 / 24 ≤ tolerantSuccess Mr (raaUnitary unmarkRefl R) x₀ (Nat.max tMax 1)) ∧
    (S + U + ∑ i ∈ Finset.Icc 1 (Nat.max tMax 1), raaCost costR costMark i ≤
      mnrsTheoremEightCostConstant *
        (S + (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U + C))) := by
  have hgap : 2 * Real.sqrt δ ≤ mnrsPhaseGap r :=
    mnrs_phaseGap_ge_two_sqrt_gap hr0 hr1 hrδ
  have hrootpos : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hΔpos : 0 < mnrsPhaseGap r := lt_of_lt_of_le (by linarith) hgap
  have hΔπ : mnrsPhaseGap r ≤ Real.pi := by
    rw [mnrsPhaseGap]
    have := Real.arccos_le_pi_div_two.mpr hr0
    linarith
  have hc₁ : 0 ≤ 80 * Real.pi * U / Real.sqrt δ := by positivity
  have hcostR : ∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 →
      costR i ≤ 80 * Real.pi * U / Real.sqrt δ * Real.log (1 / betaAt (1 / 72) i) := by
    intro i hi hit
    exact (hledger i hi hit).trans
      (mnrs_schedule_reflection_cost_le hU hδ hΔpos hΔπ hgap hi)
  have hassembly := mnrs_search_theorem_three_abstract W Mr unmarkRefl hneg hpos x₀ hx₀ ε hε
    hε1 hmass tMax R (80 * Real.pi * U / Real.sqrt δ) C hc₁ hC costR costMark Rs
    hxRs hRsMark hRsR hfix hclose hcostR hmarkC hwin hmin
  obtain ⟨hzero, hsucc, hcost, -⟩ := hassembly
  refine ⟨hzero, hsucc, ?_⟩
  have hord := mnrs_eight_order_form (ε := ε) (δ := δ) (U := U) (C := C)
    (c₁ := 80 * Real.pi * U / Real.sqrt δ) tMax hε hε1 hδ hU hC hc₁ le_rfl hwin.2
  set B : ℝ := (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U + C) with hBdef
  have hcost' : ∑ i ∈ Finset.Icc 1 (Nat.max tMax 1), raaCost costR costMark i ≤
      (3200 * Real.pi) * B := by
    rw [hBdef]
    have h := hcost.trans hord
    simpa only [mul_assoc] using h
  have hεroot : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hinvε : (1 : ℝ) ≤ 1 / Real.sqrt ε := by
    rw [le_div_iff₀ hεroot]
    nlinarith [Real.sqrt_le_one.mpr hε1]
  have hinvδ : (1 : ℝ) ≤ 1 / Real.sqrt δ := by
    rw [le_div_iff₀ hrootpos]
    nlinarith [Real.sqrt_le_one.mpr hδ1]
  have hitem : (1 : ℝ) ≤ (1 / Real.sqrt ε) * (1 / Real.sqrt δ) := by
    have h := mul_le_mul hinvε hinvδ (by norm_num) (by positivity :
      (0 : ℝ) ≤ 1 / Real.sqrt ε)
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (1 / Real.sqrt ε) * (1 / Real.sqrt δ) := h
  have hK : (1 : ℝ) ≤ mnrsTheoremEightCostConstant := by
    rw [mnrsTheoremEightCostConstant]
    have := Real.pi_pos
    linarith
  have hB0 : (0 : ℝ) ≤ B := by
    rw [hBdef]; positivity
  have hUle : U ≤ B := by
    rw [hBdef]
    have hm := mul_le_mul_of_nonneg_right hitem hU
    calc U = 1 * U := by ring
      _ ≤ ((1 / Real.sqrt ε) * (1 / Real.sqrt δ)) * U := hm
      _ ≤ (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U + C) := by
          have hCnn : (0 : ℝ) ≤ C := hC
          have hnn : (0 : ℝ) ≤ (1 / Real.sqrt ε) * (1 / Real.sqrt δ) * U := by positivity
          nlinarith
  have hSK : S ≤ mnrsTheoremEightCostConstant * S := by
    have := mul_le_mul_of_nonneg_right hK hS
    calc S = 1 * S := by ring
      _ ≤ mnrsTheoremEightCostConstant * S := this
  calc S + U + ∑ i ∈ Finset.Icc 1 (Nat.max tMax 1), raaCost costR costMark i
      = S + (U + ∑ i ∈ Finset.Icc 1 (Nat.max tMax 1), raaCost costR costMark i) := by ring
    _ ≤ mnrsTheoremEightCostConstant * S + mnrsTheoremEightCostConstant * B := by
        have hUsum : U + ∑ i ∈ Finset.Icc 1 (Nat.max tMax 1), raaCost costR costMark i ≤
            (1 + 3200 * Real.pi) * B := by nlinarith [hUle, hcost', hB0]
        have hbig : (1 + 3200 * Real.pi) * B ≤ mnrsTheoremEightCostConstant * B := by
          apply mul_le_mul_of_nonneg_right _ hB0
          rw [mnrsTheoremEightCostConstant]
          linarith [Real.pi_pos]
        linarith
    _ = mnrsTheoremEightCostConstant * (S + B) := by ring

end Qatlib.Concepts.WalkSearch.MainResults.SearchCost
