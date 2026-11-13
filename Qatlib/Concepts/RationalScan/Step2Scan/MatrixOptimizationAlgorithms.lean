/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RationalScan.Step2Scan.MatrixOptimizationAlgorithmsDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Matrix optimization width and sampling bounds

This module proves payoff interval bounds, certificate objective estimates, and sampling
identities for the SDP framework of [BrandaoSvore2017]. It states a corrected combined width
result with `2 ≤ α` and bounds on rounds below `T`, and derives the width and separation
estimates justified by the Step 2 acceptance test.

## Main statements

* `clause14_corrected_alpha2_bounded_rounds`: payoff and certificate bounds with explicit scale
  and round restrictions.
* `mixtureClause_fixed`: certificate sampling through the specified normalized mixture law.
* `step2Accepted_width` and `step2Accepted_separation_lower`: bounds for accepted candidates.
* `lemma2_rescale_objective_of_bridge`: an objective estimate transferred from a lifted problem.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.RationalScan.Step2Scan

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixWeights.WeightsCore

namespace Qatlib.Concepts.RationalScan.Step2Scan

set_option autoImplicit false

noncomputable section

open Matrix Qatlib.Concepts.RationalScan.Step2Scan

open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

/-- The sampled width equals the exact width plus the bridge slack. -/
theorem widthSampled_eq (α R ε : ℝ) :
    widthSampled α R ε = widthExact α + widthBridgeSlack α R ε := by
  simp only [widthSampled, widthExact, widthBridgeSlack]
  ring

/-- For nonnegative `α` and nonnegative sampling slack, the exact width is at most the sampled
width. -/
theorem widthExact_le_widthSampled (α R ε : ℝ) (hα : 0 ≤ α) (hslack : 0 ≤ 2 * R * ε) :
    widthExact α ≤ widthSampled α R ε := by
  have h := mul_le_mul_of_nonneg_left hslack hα
  simp only [widthSampled, widthExact] at *
  nlinarith

/-- A bound by the sampled width is equivalent to the same bound by the exact width plus bridge
slack. -/
theorem widthSampled_iff (α R ε : ℝ) (c : ℝ) :
    c ≤ widthSampled α R ε ↔ c ≤ widthExact α + widthBridgeSlack α R ε := by
  rw [widthSampled_eq]

/-- For Hermitian contraction data and positive `α`, a nonnegative round vector with mass at
most `2*α-1` gives a Hermitian payoff between zero and identity. -/
theorem payoffUnitInterval_of_mass (D m : ℕ) (A : Fin m → Operator D)
    (Cv : Operator D) (y : ℕ → Fin m → ℝ) (α : ℝ) (s : ℕ)
    (hD : 0 < D) (hα : 0 < α) (hA : ∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1)
    (hCv : Cv.IsHermitian ∧ ‖Cv‖ ≤ 1)
    (hy : ∀ i, 0 ≤ y s i) (hmass : (∑ i, y s i) ≤ 2 * α - 1) :
    payoffUnitInterval D (dualPayoff D m A Cv α y s) := by
  have hsum : (∑ i, y s i • A i).IsHermitian :=
    isSelfAdjoint_sum _ (fun i _ => (hA i).1.smul (by simp [IsSelfAdjoint]))
  let Z : Operator D := (∑ i, y s i • A i) - Cv
  have hZ : Z.IsHermitian := hsum.sub hCv.1
  have hn : ‖∑ i, y s i • A i‖ ≤ ∑ i, y s i := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hy i)]
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left (hA i).2 (hy i)
  have hnZ : ‖Z‖ ≤ 2 * α := by
    have htri := norm_sub_le (∑ i, y s i • A i) Cv
    change ‖Z‖ ≤ _ at htri
    linarith
  have hpad : ((2 * α - ‖Z‖) • (1 : Operator D)).PosSemidef :=
    (Matrix.PosSemidef.one : (1 : Operator D).PosSemidef).smul
      (by exact_mod_cast (sub_nonneg.mpr hnZ))
  have hupper : ((2 * α) • (1 : Operator D) - Z).PosSemidef := by
    convert! (mmw_shift_posSemidef D Z hZ hD).add hpad using 1
    module
  have hlower : (Z + (2 * α) • (1 : Operator D)).PosSemidef := by
    have h := (mmw_shift_posSemidef D (-Z) hZ.neg hD).add hpad
    rw [norm_neg] at h
    convert! h using 1
    module
  have hscale : 0 ≤ (4 * α)⁻¹ := by positivity
  have hunit : (4 * α)⁻¹ • ((4 * α) • (1 : Operator D)) = 1 := by
    rw [smul_smul, inv_mul_cancel₀ (by positivity : (4 * α : ℝ) ≠ 0), one_smul]
  have hdiff : (1 : Operator D) - dualPayoff D m A Cv α y s =
      (4 * α)⁻¹ • ((2 * α) • (1 : Operator D) - Z) := by
    change 1 - (4 * α)⁻¹ • (Z + (2 * α) • (1 : Operator D)) = _
    calc
      _ = (4 * α)⁻¹ • ((4 * α) • (1 : Operator D)) -
          (4 * α)⁻¹ • (Z + (2 * α) • (1 : Operator D)) := by rw [hunit]
      _ = _ := by module
  refine ⟨?_, ?_, ?_⟩
  · exact (hlower.smul (by exact_mod_cast hscale)).isHermitian
  · apply Matrix.le_iff.mpr
    simpa only [sub_zero] using! hlower.smul (by exact_mod_cast hscale)
  · apply Matrix.le_iff.mpr
    rw [hdiff]
    exact hupper.smul (by exact_mod_cast hscale)

/-- Under the stated contraction and positivity assumptions, an exact-width objective bound with
`α ≥ 1` places the round payoff between zero and identity. -/
theorem payoffUnitInterval_of_exact_width (D m : ℕ) (A : Fin m → Operator D)
    (Cv : Operator D) (b : Fin m → ℝ) (y : ℕ → Fin m → ℝ) (α : ℝ) (s : ℕ)
    (hD : 0 < D) (hα : 0 < α) (hα1 : 1 ≤ α) (hA : ∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1)
    (hCv : Cv.IsHermitian ∧ ‖Cv‖ ≤ 1) (hb : ∀ i, 1 ≤ b i)
    (hy : ∀ i, 0 ≤ y s i) (hw : certificateObjective m b (y s) ≤ widthExact α) :
    payoffUnitInterval D (dualPayoff D m A Cv α y s) := by
  have hsumle : (∑ i, y s i * 1) ≤ (∑ i, y s i * b i) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hb i) (hy i)
  have hwidth : (∑ i, y s i) ≤ α := by
    simpa only [mul_one] using! hsumle.trans hw
  exact payoffUnitInterval_of_mass D m A Cv y α s hD hα hA hCv hy (by linarith)

/-- Under the stated contraction and positivity assumptions, a sampled-width bound places the
payoff between zero and identity when `α ≥ 2` and `2*R*ε ≤ 1/2`. -/
theorem payoffUnitInterval_of_sampled_width (D m : ℕ) (A : Fin m → Operator D)
    (Cv : Operator D) (b : Fin m → ℝ) (y : ℕ → Fin m → ℝ) (α R ε : ℝ) (s : ℕ)
    (hD : 0 < D) (hα : 0 < α) (hα2 : 2 ≤ α) (hA : ∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1)
    (hCv : Cv.IsHermitian ∧ ‖Cv‖ ≤ 1) (hb : ∀ i, 1 ≤ b i)
    (hy : ∀ i, 0 ≤ y s i) (hslack : 2 * R * ε ≤ 1 / 2)
    (hw : certificateObjective m b (y s) ≤ widthSampled α R ε) :
    payoffUnitInterval D (dualPayoff D m A Cv α y s) := by
  have hsumle : (∑ i, y s i * 1) ≤ (∑ i, y s i * b i) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hb i) (hy i)
  have hwidth : (∑ i, y s i) ≤ α * (1 + 2 * R * ε) := by
    simpa only [mul_one, widthSampled] using! hsumle.trans hw
  have hmass : (∑ i, y s i) ≤ 2 * α - 1 := by
    nlinarith
  exact payoffUnitInterval_of_mass D m A Cv y α s hD hα hA hCv hy hmass

/-- When `b j₀ = R ≠ 0`, the dual certificate objective equals `δ*α/2` plus the average of the
round objectives. -/
theorem certificateObjective_dualCertificate (m : ℕ) (b : Fin m → ℝ) (δ α R : ℝ)
    (j₀ : Fin m) (y : ℕ → Fin m → ℝ) (T : ℕ) (_hT : 0 < T) (hR : R ≠ 0) (hbj : b j₀ = R) :
    certificateObjective m b (dualCertificate m δ α R j₀ y T) =
      δ * α / 2 + (∑ t ∈ Finset.range T, certificateObjective m b (y t)) / T := by
  have heval : certificateObjective m b (dualCertificate m δ α R j₀ y T) =
      δ * α / (2 * R) * b j₀ +
        (∑ t ∈ Finset.range T, ∑ i, y t i * b i) / T := by
    simp only [certificateObjective]
    simp only [dualCertificate, add_mul, div_mul_eq_mul_div, Finset.sum_add_distrib,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    simp only [Finset.sum_mul, ← Finset.sum_div]
    rw [Finset.sum_comm]
  rw [heval, hbj]
  have hcan : δ * α / (2 * R) * R = δ * α / 2 := by field_simp
  rw [hcan]
  congr 1

/-- If every round below positive `T` has objective at most the exact width, the dual
certificate objective is at most `α*(1+δ/2)`, assuming `b j₀ = R ≠ 0`. -/
theorem dualCertificate_obj_exact (m T : ℕ) (b : Fin m → ℝ) (j₀ : Fin m)
    (y : ℕ → Fin m → ℝ) (δ α R : ℝ) (hT : 0 < T) (hR : R ≠ 0) (hbj : b j₀ = R)
    (hy : ∀ t < T, certificateObjective m b (y t) ≤ widthExact α) :
    certificateObjective m b (dualCertificate m δ α R j₀ y T) ≤ α * (1 + δ / 2) := by
  have hT0 : 0 < (T : ℝ) := by exact_mod_cast hT
  rw [certificateObjective_dualCertificate m b δ α R j₀ y T hT hR hbj]
  have hsum : (∑ t ∈ Finset.range T, certificateObjective m b (y t)) ≤ T * α := by
    calc
      (∑ t ∈ Finset.range T, certificateObjective m b (y t)) ≤
          ∑ _t ∈ Finset.range T, α := by
        apply Finset.sum_le_sum
        intro t ht
        exact hy t (Finset.mem_range.mp ht)
      _ = T * α := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hav : (∑ t ∈ Finset.range T, certificateObjective m b (y t)) / T ≤ α := by
    apply (div_le_iff₀ hT0).mpr
    linarith
  linarith

/-- For nonnegative `α` and `δ`, exact-width round bounds give certificate objective at most
`(1+δ)*α`, assuming positive `T` and `b j₀ = R ≠ 0`. -/
theorem dualCertificate_obj_exact_le (m T : ℕ) (b : Fin m → ℝ) (j₀ : Fin m)
    (y : ℕ → Fin m → ℝ) (δ α R : ℝ) (hT : 0 < T) (hR : R ≠ 0) (hbj : b j₀ = R) (hα : 0 ≤ α)
    (hδ : 0 ≤ δ) (hy : ∀ t < T, certificateObjective m b (y t) ≤ widthExact α) :
    certificateObjective m b (dualCertificate m δ α R j₀ y T) ≤ (1 + δ) * α := by
  have h := dualCertificate_obj_exact m T b j₀ y δ α R hT hR hbj hy
  nlinarith

/-- Sampled-width bounds on rounds below positive `T` give certificate objective at most
`α*(1+δ/2+2*R*ε)`, assuming `b j₀ = R ≠ 0`. -/
theorem dualCertificate_obj_sampled (m T : ℕ) (b : Fin m → ℝ) (j₀ : Fin m)
    (y : ℕ → Fin m → ℝ) (δ α R ε : ℝ) (hT : 0 < T) (hR : R ≠ 0) (hbj : b j₀ = R)
    (hy : ∀ t < T, certificateObjective m b (y t) ≤ widthSampled α R ε) :
    certificateObjective m b (dualCertificate m δ α R j₀ y T) ≤
      α * (1 + δ / 2 + 2 * R * ε) := by
  have hT0 : 0 < (T : ℝ) := by exact_mod_cast hT
  rw [certificateObjective_dualCertificate m b δ α R j₀ y T hT hR hbj]
  have hsum : (∑ t ∈ Finset.range T, certificateObjective m b (y t)) ≤
      T * widthSampled α R ε := by
    calc
      (∑ t ∈ Finset.range T, certificateObjective m b (y t)) ≤
          ∑ _t ∈ Finset.range T, widthSampled α R ε := by
        apply Finset.sum_le_sum
        intro t ht
        exact hy t (Finset.mem_range.mp ht)
      _ = T * widthSampled α R ε := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hav : (∑ t ∈ Finset.range T, certificateObjective m b (y t)) / T ≤
      widthSampled α R ε := by
    apply (div_le_iff₀ hT0).mpr
    linarith
  simp only [widthSampled] at hav
  linarith

/-- For nonnegative `α` and `2*R*ε ≤ δ/2`, sampled-width round bounds give certificate objective
at most `(1+δ)*α`, assuming positive `T` and `b j₀ = R ≠ 0`. -/
theorem dualCertificate_obj_sampled_le (m T : ℕ) (b : Fin m → ℝ) (j₀ : Fin m)
    (y : ℕ → Fin m → ℝ) (δ α R ε : ℝ) (hT : 0 < T) (hR : R ≠ 0) (hbj : b j₀ = R) (hα : 0 ≤ α)
    (hslack : 2 * R * ε ≤ δ / 2)
    (hy : ∀ t < T, certificateObjective m b (y t) ≤ widthSampled α R ε) :
    certificateObjective m b (dualCertificate m δ α R j₀ y T) ≤ (1 + δ) * α := by
  have h := dualCertificate_obj_sampled m T b j₀ y δ α R ε hT hR hbj hy
  nlinarith

/-- With `α ≥ 2` and the stated instance, positivity, and slack hypotheses, exact and sampled
widths satisfy the bridge identities. The corresponding round bounds imply payoff interval
bounds for `s < T` and the stated dual certificate objective estimates. -/
theorem clause14_corrected_alpha2_bounded_rounds :
    ∀ (D m T : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
      (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R δ ε : ℝ),
    0 < D → 0 < m → 0 < T → 0 < α → 2 ≤ α → 0 < R → α ≤ R → 0 < δ → 0 < ε →
    2 * R * ε ≤ 1 / 2 → 2 * R * ε ≤ δ / 2 →
    SdpInstance D m A Cv b j₀ R →
    (∀ t < T, ∀ i, 0 ≤ y t i) →
    (∀ t < T, certificateObjective m b (y t) ≤ widthExact α →
      certificateObjective m b (y t) ≤ widthSampled α R ε) ∧
    (∀ t < T, certificateObjective m b (y t) ≤ widthSampled α R ε ↔
      certificateObjective m b (y t) ≤ widthExact α + widthBridgeSlack α R ε) ∧
    widthSampled α R ε = widthExact α + widthBridgeSlack α R ε ∧
    ((∀ t < T, certificateObjective m b (y t) ≤ widthExact α) →
      (∀ s < T, payoffUnitInterval D (dualPayoff D m A Cv α y s)) ∧
        certificateObjective m b (dualCertificate m δ α R j₀ y T) ≤ α * (1 + δ / 2) ∧
        certificateObjective m b (dualCertificate m δ α R j₀ y T) ≤ (1 + δ) * α) ∧
    ((∀ t < T, certificateObjective m b (y t) ≤ widthSampled α R ε) →
      (∀ s < T, payoffUnitInterval D (dualPayoff D m A Cv α y s)) ∧
        certificateObjective m b (dualCertificate m δ α R j₀ y T) ≤
          α * (1 + δ / 2 + 2 * R * ε) ∧
        certificateObjective m b (dualCertificate m δ α R j₀ y T) ≤ (1 + δ) * α) := by
  intro D m T A Cv b y j₀ α R δ ε hD hm hT hα hα2 hR hαR hδ hε hsmall hsmall2 hinst hy
  obtain ⟨_, _, hRpos, hA, hCvh, hCvnorm, hbnd, _, hb0⟩ := hinst
  have hb : ∀ i, 1 ≤ b i := fun i => (hbnd i).1
  have hRne : R ≠ 0 := ne_of_gt hRpos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht hc
    exact le_trans hc (widthExact_le_widthSampled α R ε hα.le (by positivity))
  · intro t ht
    exact widthSampled_iff α R ε (certificateObjective m b (y t))
  · exact widthSampled_eq α R ε
  · intro hexact
    refine ⟨?_, ?_, ?_⟩
    · intro s hs
      exact payoffUnitInterval_of_exact_width D m A Cv b y α s hD hα (by linarith)
        hA ⟨hCvh, hCvnorm⟩ hb (hy s hs) (hexact s hs)
    · exact dualCertificate_obj_exact m T b j₀ y δ α R hT hRne hb0 hexact
    · exact dualCertificate_obj_exact_le m T b j₀ y δ α R hT hRne hb0 hα.le
        hδ.le hexact
  · intro hsamp
    refine ⟨?_, ?_, ?_⟩
    · intro s hs
      exact payoffUnitInterval_of_sampled_width D m A Cv b y α R ε s hD hα hα2
        hA ⟨hCvh, hCvnorm⟩ hb (hy s hs) hsmall (hsamp s hs)
    · exact dualCertificate_obj_sampled m T b j₀ y δ α R ε hT hRne hb0 hsamp
    · exact dualCertificate_obj_sampled_le m T b j₀ y δ α R ε hT hRne hb0 hα.le
        hsmall2 hsamp

/-- Under the stated density, contraction, and positivity assumptions, there exist a finite
probability law, expectation estimates, and resource numbers satisfying
`ExpectationEstimationBudget`, with simultaneous estimation success probability at least
`1-p_e`. -/
theorem expectationClause_valid :
    ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (ρ : Operator D)
      (n s : ℕ) (h p_e : ℝ),
    0 < D → 0 < n → 0 < m → 0 < s → 0 < h → 0 < p_e → p_e < 1 →
    IsDensityOperator ρ →
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
    ∃ (Ω : ℕ) (w : Fin Ω → ℝ) (estA : Fin Ω → Fin m → ℝ) (estC : Fin Ω → ℝ)
      (copies meas copiesO oracle : ℝ),
      0 < Ω ∧ IsProbLaw w ∧
        ExpectationEstimationBudget n m s h p_e copies meas copiesO oracle ∧
        1 - p_e ≤ eventProb w (fun ω =>
          (∀ i, |estA ω i - (Matrix.trace (A i * ρ)).re| ≤ h) ∧
            |estC ω - (Matrix.trace (Cv * ρ)).re| ≤ h) := by
  intro D m A Cv ρ n s h p_e _hD _hn _hm _hs hh hp_e hpe1 _hρ _hA _hCv
  refine ⟨1, (fun _ => 1),
    (fun _ i => (Matrix.trace (A i * ρ)).re),
    (fun _ => (Matrix.trace (Cv * ρ)).re),
    8 * Real.log (1 / p_e) / h ^ 2,
    8 * (s : ℝ) / h ^ 2 * (Real.log (4 * (n : ℝ) * (s : ℝ) / (p_e * h))) ^ 4,
    8 * Real.log ((m : ℝ) / p_e) / h ^ 2,
    8 * (s : ℝ) / h ^ 2 * (Real.log (4 * (n : ℝ) * (m : ℝ) * (s : ℝ) / (p_e * h))) ^ 4,
    ?_, ?_, ?_, ?_⟩
  · norm_num
  · exact ⟨fun _ => by norm_num, by simp⟩
  · exact ⟨hh, hp_e, hpe1, le_refl _, le_refl _, le_refl _, le_refl _⟩
  · have hP : ∀ i : Fin m,
        |(Matrix.trace (A i * ρ)).re - (Matrix.trace (A i * ρ)).re| ≤ h := by
      intro i
      rw [sub_self, abs_zero]
      exact hh.le
    have hPc : |(Matrix.trace (Cv * ρ)).re - (Matrix.trace (Cv * ρ)).re| ≤ h := by
      rw [sub_self, abs_zero]
      exact hh.le
    have hval : eventProb (fun _ : Fin 1 => (1 : ℝ))
        (fun ω => (∀ i, |(Matrix.trace (A i * ρ)).re - (Matrix.trace (A i * ρ)).re| ≤ h) ∧
          |(Matrix.trace (Cv * ρ)).re - (Matrix.trace (Cv * ρ)).re| ≤ h) = 1 := by
      unfold eventProb
      rw [Fin.sum_univ_one]
      have hp0 : ((fun ω : Fin 1 =>
        (∀ i, |(Matrix.trace (A i * ρ)).re - (Matrix.trace (A i * ρ)).re| ≤ h) ∧
          |(Matrix.trace (Cv * ρ)).re - (Matrix.trace (Cv * ρ)).re| ≤ h) : Fin 1 → Prop) 0 :=
        ⟨hP, hPc⟩
      rw [if_pos hp0]
    rw [hval]
    linarith

/-- For nonnegative rounds of positive mass and positive `T`, the specified mixture equals the
normalized dual certificate distribution at every index. -/
theorem mixtureLaw_eq_dualSampleDist (m T : ℕ) (y : ℕ → Fin m → ℝ) (j₀ : Fin m)
    (δ α R : ℝ) (hT : 0 < T) (hy : ∀ t < T, ∀ i, 0 ≤ y t i)
    (hround : ∀ t < T, 0 < ∑ i, y t i)
    (_hscale : 0 < dualSampleScale m (dualCertificate m δ α R j₀ y T)) (i : Fin m) :
    mixtureLaw m T (mixtureWeights m δ α R j₀ y T) (mixtureComponents m j₀ y T) i =
      dualSampleDist m (dualCertificate m δ α R j₀ y T) i := by
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  have htotal : dualSampleScale m (dualCertificate m δ α R j₀ y T) =
      δ * α / (2 * R) + (∑ t ∈ Finset.range T, ∑ j, y t j) / (T : ℝ) := by
    simp only [dualSampleScale, dualCertificate]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_div, Finset.sum_comm]
  have hst (t : ℕ) (ht : t < T) : (0 : ℝ) < ∑ j, y t j := hround t ht
  have hmass (t : ℕ) (ht : t < T) (i' : Fin m) : 0 ≤ y t i' := hy t ht i'

  have hsplit : mixtureLaw m T (mixtureWeights m δ α R j₀ y T)
      (mixtureComponents m j₀ y T) i =
      (if i = j₀ then (δ * α / (2 * R)) / dualSampleScale m (dualCertificate m δ α R j₀ y T)
        else 0) +
      (∑ t ∈ Finset.range T, y t i) / (T : ℝ) /
        dualSampleScale m (dualCertificate m δ α R j₀ y T) := by
    show (∑ u : Fin (T + 1), mixtureWeights m δ α R j₀ y T u *
        mixtureComponents m j₀ y T u i) = _
    rw [Fin.sum_univ_succ]
    have h0 : mixtureWeights m δ α R j₀ y T 0 *
        mixtureComponents m j₀ y T 0 i =
        (if i = j₀ then (δ * α / (2 * R)) / dualSampleScale m (dualCertificate m δ α R j₀ y T)
          else 0) := by
      simp only [mixtureWeights, mixtureComponents, Fin.val_zero, if_true]
      split_ifs with hi
      · rw [mul_one]
      · rw [mul_zero]
    rw [h0]
    have hterm : ∀ t : Fin T, mixtureWeights m δ α R j₀ y T t.succ *
        mixtureComponents m j₀ y T t.succ i = y (t : ℕ) i / (T : ℝ) /
          dualSampleScale m (dualCertificate m δ α R j₀ y T) := by
      intro t
      have hval : (((t.succ : Fin (T + 1)).val) - 1 : ℕ) = (t : ℕ) := by simp
      have hnn : ¬ (((t.succ : Fin (T + 1)).val : ℕ) = 0) := by simp
      simp only [mixtureWeights, mixtureComponents, hval]
      rw [if_neg hnn, if_neg hnn]
      have hne : (∑ j, y (t : ℕ) j : ℝ) ≠ 0 := ne_of_gt (hst t.val t.isLt)
      have hprod : ((∑ j, y (t : ℕ) j) / (T : ℝ) /
          dualSampleScale m (dualCertificate m δ α R j₀ y T)) *
          (y (t : ℕ) i / (∑ j, y (t : ℕ) j)) =
          y (t : ℕ) i / (T : ℝ) / dualSampleScale m (dualCertificate m δ α R j₀ y T) := by
        simp only [div_div]
        rw [div_mul_div_comm, mul_comm (∑ j, y (t : ℕ) j) (y (t : ℕ) i),
          mul_div_mul_right _ _ hne]
      exact hprod
    have hrew : (∑ t : Fin T, mixtureWeights m δ α R j₀ y T t.succ *
        mixtureComponents m j₀ y T t.succ i) =
        ∑ t : Fin T, y (t : ℕ) i / (T : ℝ) /
          dualSampleScale m (dualCertificate m δ α R j₀ y T) :=
      Finset.sum_congr rfl (fun t _ => hterm t)
    rw [hrew]
    have hsum : (∑ t : Fin T, y (t : ℕ) i / (T : ℝ) /
        dualSampleScale m (dualCertificate m δ α R j₀ y T)) =
        (∑ t ∈ Finset.range T, y t i) / (T : ℝ) /
          dualSampleScale m (dualCertificate m δ α R j₀ y T) := by
      have hA : (∑ t : Fin T, y (t : ℕ) i / (T : ℝ) /
          dualSampleScale m (dualCertificate m δ α R j₀ y T)) =
          ∑ t : Fin T, y (t : ℕ) i /
            ((T : ℝ) * dualSampleScale m (dualCertificate m δ α R j₀ y T)) :=
        Finset.sum_congr rfl (fun t _ => by rw [div_div])
      have hB : (∑ t : Fin T, y (t : ℕ) i /
            ((T : ℝ) * dualSampleScale m (dualCertificate m δ α R j₀ y T))) =
          (∑ t : Fin T, y (t : ℕ) i) /
            ((T : ℝ) * dualSampleScale m (dualCertificate m δ α R j₀ y T)) :=
        (Finset.sum_div (Finset.univ : Finset (Fin T)) (fun t => y (t : ℕ) i)
          ((T : ℝ) * dualSampleScale m (dualCertificate m δ α R j₀ y T))).symm
      have hC : (∑ t : Fin T, y (t : ℕ) i) = ∑ t ∈ Finset.range T, y t i :=
        Fin.sum_univ_eq_sum_range (fun a => y a i) T
      have hD : ((∑ t ∈ Finset.range T, y t i) /
            ((T : ℝ) * dualSampleScale m (dualCertificate m δ α R j₀ y T))) =
          (∑ t ∈ Finset.range T, y t i) / (T : ℝ) /
            dualSampleScale m (dualCertificate m δ α R j₀ y T) := by
        rw [div_div]
      rw [hA, hB, hC, hD]
    rw [hsum]
  rw [hsplit]
  have hcert : dualSampleDist m (dualCertificate m δ α R j₀ y T) i =
      (if i = j₀ then (δ * α / (2 * R)) / dualSampleScale m (dualCertificate m δ α R j₀ y T)
        else 0) +
      (∑ t ∈ Finset.range T, y t i) / (T : ℝ) /
        dualSampleScale m (dualCertificate m δ α R j₀ y T) := by
    simp only [dualSampleDist, dualCertificate]
    rw [add_div]
    congr 1
    · split_ifs with hi
      · rfl
      · rw [zero_div]
  rw [hcert]

/-- For positive parameters and nonnegative rounds of positive mass, a positive certificate
scale gives a mixture sampling process for its own normalized distribution and a positive
sampling ledger. -/
theorem mixtureClause_fixed :
    ∀ (m T : ℕ) (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (δ α R : ℝ),
    0 < m → 0 < T → 0 < α → 0 < R → 0 < δ →
    (∀ t < T, ∀ i, 0 ≤ y t i) →
    (∀ t < T, 0 < ∑ i, y t i) →
    (0 < dualSampleScale m (dualCertificate m δ α R j₀ y T) →
      MixtureSamplingProcess m T (dualCertificate m δ α R j₀ y T)
          (dualSampleDist m (dualCertificate m δ α R j₀ y T))
          (mixtureWeights m δ α R j₀ y T) (mixtureComponents m j₀ y T) ∧
        ∃ draws selectorDraws componentDraws : ℕ,
          0 < draws ∧ MixtureSampleLedger draws selectorDraws componentDraws) := by
  intro m T y j₀ δ α R _hm hT hα hR hδ hy hround hscale
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  have hyBar : ∀ i, 0 ≤ dualCertificate m δ α R j₀ y T i := by
    intro i
    simp only [dualCertificate]
    apply add_nonneg
    · split_ifs
      · positivity
      · norm_num
    · exact div_nonneg (Finset.sum_nonneg fun t ht => hy t (Finset.mem_range.mp ht) i)
        (le_of_lt (by exact_mod_cast hT))
  have hw : ∀ u : Fin (T + 1), 0 ≤ mixtureWeights m δ α R j₀ y T u := by
    intro u
    simp only [mixtureWeights]
    by_cases hu : u.val = 0
    · rw [if_pos hu]
      exact div_nonneg (by positivity) (le_of_lt hscale)
    · rw [if_neg hu]
      have hlt : u.val - 1 < T := by
        have h1 : 0 < u.val := Nat.pos_of_ne_zero hu
        have h2 : u.val - 1 < u.val := Nat.sub_lt h1 (by norm_num)
        exact Nat.lt_of_lt_of_le h2 (Nat.le_of_lt_succ u.isLt)
      exact div_nonneg (div_nonneg (Finset.sum_nonneg fun i _ => hy (u.val - 1) hlt i)
        (le_of_lt (by exact_mod_cast hT))) (le_of_lt hscale)
  have hcomp : ∀ u : Fin (T + 1), IsSamplingLaw m (mixtureComponents m j₀ y T u) := by
    intro u
    refine ⟨fun i => ?_, ?_⟩
    · simp only [mixtureComponents]
      by_cases hu : u.val = 0
      · rw [if_pos hu]
        split_ifs <;> norm_num
      · rw [if_neg hu]
        have hlt : u.val - 1 < T := by
          have h1 : 0 < u.val := Nat.pos_of_ne_zero hu
          have h2 : u.val - 1 < u.val := Nat.sub_lt h1 (by norm_num)
          exact Nat.lt_of_lt_of_le h2 (Nat.le_of_lt_succ u.isLt)
        have hS : (0 : ℝ) < ∑ j, y (u.val - 1) j := hround (u.val - 1) hlt
        exact div_nonneg (hy (u.val - 1) hlt i) (le_of_lt hS)
    · simp only [mixtureComponents]
      by_cases hu : u.val = 0
      · simp only [if_pos hu]
        rw [Finset.sum_ite_eq']
        simp
      · simp only [if_neg hu]
        have hlt : u.val - 1 < T := by
          have h1 : 0 < u.val := Nat.pos_of_ne_zero hu
          have h2 : u.val - 1 < u.val := Nat.sub_lt h1 (by norm_num)
          exact Nat.lt_of_lt_of_le h2 (Nat.le_of_lt_succ u.isLt)
        have hS : (0 : ℝ) < ∑ j, y (u.val - 1) j := hround (u.val - 1) hlt
        rw [← Finset.sum_div]
        exact div_self (ne_of_gt hS)
  have hsumw : (∑ u : Fin (T + 1), mixtureWeights m δ α R j₀ y T u) = 1 := by
    have hw0 : mixtureWeights m δ α R j₀ y T 0 =
        (δ * α / (2 * R)) / dualSampleScale m (dualCertificate m δ α R j₀ y T) := by
      have hcond : ((((0 : Fin (T + 1)).val : ℕ)) = 0) := by simp
      have hdef : mixtureWeights m δ α R j₀ y T 0 =
          (if ((((0 : Fin (T + 1)).val : ℕ)) = 0)
            then (δ * α / (2 * R)) / dualSampleScale m (dualCertificate m δ α R j₀ y T)
            else ((∑ i, y ((((0 : Fin (T + 1)).val : ℕ)) - 1) i) / (T : ℝ) /
              dualSampleScale m (dualCertificate m δ α R j₀ y T))) := rfl
      rw [hdef, if_pos hcond]
    have htermw : ∀ t : Fin T, mixtureWeights m δ α R j₀ y T t.succ =
        (∑ i, y (t : ℕ) i) / (T : ℝ) / dualSampleScale m (dualCertificate m δ α R j₀ y T) := by
      intro t
      have hval : (((t.succ : Fin (T + 1)).val) - 1 : ℕ) = (t : ℕ) := by simp
      have hnn : ¬ (((t.succ : Fin (T + 1)).val : ℕ) = 0) := by simp
      simp only [mixtureWeights, hval]
      rw [if_neg hnn]
    rw [Fin.sum_univ_succ, hw0]
    have hrew : (∑ t : Fin T, mixtureWeights m δ α R j₀ y T t.succ) =
        ∑ t : Fin T, (∑ i, y (t : ℕ) i) / (T : ℝ) /
          dualSampleScale m (dualCertificate m δ α R j₀ y T) :=
      Finset.sum_congr rfl (fun t _ => htermw t)
    rw [hrew]
    have htotal : dualSampleScale m (dualCertificate m δ α R j₀ y T) =
        δ * α / (2 * R) + (∑ t ∈ Finset.range T, ∑ i, y t i) / (T : ℝ) := by
      simp only [dualSampleScale, dualCertificate]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← Finset.sum_div, Finset.sum_comm]
    have hrest : (∑ t : Fin T, (∑ i, y (t : ℕ) i) / (T : ℝ) /
        dualSampleScale m (dualCertificate m δ α R j₀ y T)) =
        (∑ t ∈ Finset.range T, ∑ i, y t i) / (T : ℝ) /
          dualSampleScale m (dualCertificate m δ α R j₀ y T) := by
      have h1 : ∀ t : Fin T, ((∑ i, y (t : ℕ) i) / (T : ℝ) /
          dualSampleScale m (dualCertificate m δ α R j₀ y T)) =
          (∑ i, y (t : ℕ) i) / ((T : ℝ) * dualSampleScale m (dualCertificate m δ α R j₀ y T)) := by
        intro t
        rw [div_div]
      have h2 : (∑ t : Fin T, (∑ i, y (t : ℕ) i) / (T : ℝ) /
          dualSampleScale m (dualCertificate m δ α R j₀ y T)) =
          ∑ t : Fin T, (∑ i, y (t : ℕ) i) /
            ((T : ℝ) * dualSampleScale m (dualCertificate m δ α R j₀ y T)) :=
        Finset.sum_congr rfl (fun t _ => h1 t)
      have h3 : (∑ t : Fin T, (∑ i, y (t : ℕ) i) /
            ((T : ℝ) * dualSampleScale m (dualCertificate m δ α R j₀ y T))) =
          (∑ t : Fin T, ∑ i, y (t : ℕ) i) /
            ((T : ℝ) * dualSampleScale m (dualCertificate m δ α R j₀ y T)) :=
        (Finset.sum_div (Finset.univ : Finset (Fin T)) (fun t => ∑ i, y (t : ℕ) i)
          ((T : ℝ) * dualSampleScale m (dualCertificate m δ α R j₀ y T))).symm
      have h4 : (∑ t : Fin T, ∑ i, y (t : ℕ) i) = ∑ t ∈ Finset.range T, ∑ i, y t i :=
        Fin.sum_univ_eq_sum_range (fun a => ∑ i, y a i) T
      rw [h2, h3, h4]
      rw [div_div]
    rw [hrest]
    have hsc : dualSampleScale m (dualCertificate m δ α R j₀ y T) ≠ 0 := ne_of_gt hscale
    rw [← add_div, ← htotal, div_self hsc]
  have hproc : MixtureSamplingProcess m T (dualCertificate m δ α R j₀ y T)
      (dualSampleDist m (dualCertificate m δ α R j₀ y T))
      (mixtureWeights m δ α R j₀ y T) (mixtureComponents m j₀ y T) :=
    ⟨hscale, hw, hsumw, fun u => Or.inl (hcomp u), rfl,
      funext fun i => mixtureLaw_eq_dualSampleDist m T y j₀ δ α R hT hy hround hscale i⟩
  refine ⟨hproc, ?_⟩
  exact ⟨1, 1, 1, by norm_num, ⟨rfl, rfl⟩⟩

/-- When the constraint index set is nonempty, the normalized exponential Step 2 law is a
sampling law. -/
theorem step2IdealLaw_isSamplingLaw (D m : ℕ) (A : Fin m → Operator D) (b : Fin m → ℝ)
    (ρ : Operator D) (κ R : ℝ) (γ k : ℕ) (hm : 0 < m) :
    IsSamplingLaw m (step2IdealLaw D m A b ρ κ R γ k) := by
  let e : Fin m → ℝ := fun i =>
    Real.exp (-(κ / (4 * R ^ 2)) *
      ((k : ℝ) * (Matrix.trace (A i * ρ)).re + ((γ - k : ℕ) : ℝ) * b i))
  have he : ∀ i, 0 < e i := fun i => Real.exp_pos _
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hS : 0 < ∑ j, e j := Finset.sum_pos (fun i _ => he i) Finset.univ_nonempty
  have hne : (∑ j, e j : ℝ) ≠ 0 := ne_of_gt hS
  refine ⟨fun i => ?_, ?_⟩
  · show 0 ≤ e i / (∑ j, e j)
    exact div_nonneg (he i).le (le_of_lt hS)
  · show (∑ i, e i / (∑ j, e j)) = 1
    rw [← Finset.sum_div]
    exact div_self hne

/-- The one-based row-major index of a candidate is at most the number of pairs in the full
grid. -/
theorem step2PairIndex_le {γ Nmax : ℕ} (k : Fin γ) (N : Fin Nmax) :
    step2PairIndex k N ≤ γ * Nmax := by
  have hk : k.val + 1 ≤ γ := Nat.succ_le_of_lt k.isLt
  have hN : N.val + 1 ≤ Nmax := Nat.succ_le_of_lt N.isLt
  have h1 : k.val * Nmax + N.val + 1 ≤ k.val * Nmax + Nmax := by
    have h : k.val * Nmax + (N.val + 1) ≤ k.val * Nmax + Nmax :=
      Nat.add_le_add_left hN _
    rw [← Nat.add_assoc] at h
    exact h
  have h2 : k.val * Nmax + Nmax = (k.val + 1) * Nmax := by
    rw [Nat.add_mul, Nat.one_mul]
  have h3 : (k.val + 1) * Nmax ≤ γ * Nmax := Nat.mul_le_mul_right Nmax hk
  unfold step2PairIndex
  calc
    k.val * Nmax + N.val + 1 ≤ k.val * Nmax + Nmax := h1
    _ = (k.val + 1) * Nmax := h2
    _ ≤ γ * Nmax := h3

/-- Each candidate has a sample ledger whose pair count is its one-based row-major index. -/
theorem step2SampleLedger_at (γ Nmax M L : ℕ) (k : Fin γ) (N : Fin Nmax) :
    ∃ pairs gibbsCopies qDraws stateCopies : ℕ,
      pairs = step2PairIndex k N ∧
        Step2SampleLedger γ Nmax M L pairs gibbsCopies qDraws stateCopies := by
  refine ⟨step2PairIndex k N, M * step2PairIndex k N, M * step2PairIndex k N,
    (M + 1) * L * step2PairIndex k N, rfl, ?_⟩
  exact ⟨step2PairIndex_le k N, rfl, rfl, rfl⟩

/-- The full candidate grid has a sample ledger with pair count `γ*Nmax`. -/
theorem step2SampleLedger_fullGrid (γ Nmax M L : ℕ) :
    ∃ pairs gibbsCopies qDraws stateCopies : ℕ,
      pairs = γ * Nmax ∧
        Step2SampleLedger γ Nmax M L pairs gibbsCopies qDraws stateCopies := by
  refine ⟨γ * Nmax, M * (γ * Nmax), M * (γ * Nmax), (M + 1) * L * (γ * Nmax), rfl, ?_⟩
  exact ⟨le_refl _, rfl, rfl, rfl⟩

/-- An accepted candidate with positive mass at most `α` satisfies the sampled-width objective
bound when the empirical objective error is at most `R*(κ+ν)` and the stated signs hold. -/
theorem step2Accepted_width (m M : ℕ) (b : Fin m → ℝ)
    (estA : Fin m → ℝ) (estC : ℝ) (draws : Fin M → Fin m) (q : Fin m → ℝ)
    (κ R ν α : ℝ) (mass : ℝ)
    (hR : 0 ≤ R) (htol : 0 ≤ κ + ν) (hmassPos : 0 < mass) (hmass : mass ≤ α)
    (hq : |(∑ i, q i * b i) - (∑ j, b (draws j)) / (M : ℝ)| ≤ R * (κ + ν))
    (haccept : step2Accepts m M b estA estC draws α R κ ν mass) :
    (∑ i, b i * step2RoundVector m mass q i) ≤ widthSampled α R (κ + ν) := by
  have hemp : (∑ i, q i * b i) ≤
      (∑ j, b (draws j)) / (M : ℝ) + R * (κ + ν) := by
    have h := le_of_abs_le hq
    linarith
  have hchain : (∑ i, q i * b i) ≤ α / mass + 2 * R * (κ + ν) := by
    have hacc := haccept.2
    linarith
  have hmass0 : (mass : ℝ) ≠ 0 := ne_of_gt hmassPos
  have hcan : mass * (α / mass) = α := mul_div_cancel₀ α hmass0
  have hscale := mul_le_mul_of_nonneg_left hchain (le_of_lt hmassPos)
  rw [mul_add, hcan] at hscale
  have hw : (∑ i, b i * step2RoundVector m mass q i) =
      mass * ∑ i, q i * b i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold step2RoundVector
    ring
  rw [hw]
  have hslack := mul_le_mul_of_nonneg_right hmass
    (by positivity : 0 ≤ 2 * R * (κ + ν))
  simp only [widthSampled]
  nlinarith

/-- With positive mass, a sampling law, legal estimates, and the empirical estimate bound,
acceptance gives separation at least `-(mass*(2*(κ+ν)+ν)+ν)`. -/
theorem step2Accepted_separation_lower (D m M : ℕ) (A : Fin m → Operator D)
    (Cv : Operator D) (b : Fin m → ℝ) (ρ : Operator D)
    (estA : Fin m → ℝ) (estC : ℝ) (draws : Fin M → Fin m) (q : Fin m → ℝ)
    (κ R ν α : ℝ) (mass : ℝ)
    (hmassPos : 0 < mass)
    (hlegal : (∀ i, |estA i - (Matrix.trace (A i * ρ)).re| ≤ ν) ∧
      |estC - (Matrix.trace (Cv * ρ)).re| ≤ ν)
    (hq : IsSamplingLaw m q)
    (hgood : |(∑ j, estA (draws j)) / (M : ℝ) - (∑ i, q i * estA i)| ≤ κ + ν)
    (haccept : step2Accepts m M b estA estC draws α R κ ν mass) :
    - (mass * (2 * (κ + ν) + ν) + ν) ≤
      (∑ i, step2RoundVector m mass q i * (Matrix.trace (A i * ρ)).re)
        - (Matrix.trace (Cv * ρ)).re := by
  have hmass0 : (mass : ℝ) ≠ 0 := ne_of_gt hmassPos
  have hnorm : (∑ i, q i) = 1 := hq.2
  have hq1 : (∑ i, q i * estA i) ≥
      (∑ j, estA (draws j)) / (M : ℝ) - (κ + ν) := by
    have h := le_of_abs_le hgood
    linarith
  have hacc1 : (∑ j, estA (draws j)) / (M : ℝ) ≥ estC / mass - (κ + ν) :=
    haccept.1
  have hq2 : (∑ i, q i * estA i) ≥ estC / mass - 2 * (κ + ν) := by
    linarith
  have hest : ∀ i, estA i - ν ≤ (Matrix.trace (A i * ρ)).re := by
    intro i
    have h := abs_le.mp (hlegal.1 i)
    linarith
  have hq3 : (∑ i, q i * (Matrix.trace (A i * ρ)).re) ≥
      (∑ i, q i * estA i) - ν := by
    have hsum : (∑ i, q i * (estA i - ν)) ≤
        (∑ i, q i * (Matrix.trace (A i * ρ)).re) :=
      Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => mul_le_mul_of_nonneg_left (hest i) (hq.1 i))
    have hform : (∑ i, q i * (estA i - ν)) =
        (∑ i, q i * estA i) - ν := by
      have hmul : ∀ i, q i * (estA i - ν) = q i * estA i - q i * ν := by
        intro i
        ring
      calc
        (∑ i, q i * (estA i - ν)) = ∑ i, (q i * estA i - q i * ν) :=
          Finset.sum_congr rfl (fun i _ => hmul i)
        _ = (∑ i, q i * estA i) - (∑ i, q i * ν) := by
          rw [← Finset.sum_sub_distrib]
        _ = (∑ i, q i * estA i) - ν := by
          rw [← Finset.sum_mul, hnorm, one_mul]
    rw [hform] at hsum
    linarith
  have hC : estC ≥ (Matrix.trace (Cv * ρ)).re - ν := by
    have h := abs_le.mp hlegal.2
    linarith
  have hq4 : mass * (∑ i, q i * (Matrix.trace (A i * ρ)).re) ≥
      (Matrix.trace (Cv * ρ)).re - ν - mass * (2 * (κ + ν) + ν) := by
    have h := mul_le_mul_of_nonneg_left hq3 (le_of_lt hmassPos)
    rw [mul_sub] at h
    have hcan : mass * (estC / mass) = estC := mul_div_cancel₀ estC hmass0
    have hmain : mass * (∑ i, q i * estA i) ≥ estC - mass * (2 * (κ + ν)) := by
      have h2 := mul_le_mul_of_nonneg_left hq2 (le_of_lt hmassPos)
      rw [mul_sub, hcan] at h2
      linarith
    linarith
  have hy : (∑ i, step2RoundVector m mass q i * (Matrix.trace (A i * ρ)).re) =
      mass * (∑ i, q i * (Matrix.trace (A i * ρ)).re) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold step2RoundVector
    ring
  rw [hy]
  linarith

/-- A positive rescaling factor `α` transfers the normalized objective bound to the bound
`(1+δ)*α`. -/
theorem alphaRescaleAccuracy_of_pos (m : ℕ) (b sol : Fin m → ℝ) (α δ : ℝ)
    (hα : 0 < α) : alphaRescaleAccuracy m b sol α δ := by
  intro hscaled
  have hrew : (∑ i, sol i * (b i / α)) = (∑ i, sol i * b i) / α := by
    have hterm : ∀ i, sol i * (b i / α) = (sol i * b i) / α := by
      intro i
      ring
    have hstep : (∑ i, sol i * (b i / α)) = ∑ i, (sol i * b i) / α :=
      Finset.sum_congr rfl (fun i _ => hterm i)
    rw [hstep]
    exact (Finset.sum_div (Finset.univ : Finset (Fin m)) (fun i => sol i * b i) α).symm
  rw [hrew] at hscaled
  exact (div_le_iff₀ hα).mp hscaled

/-- If the extra lifted coordinate and its objective coefficient are nonnegative, the lifted
objective bound and the stated bridge imply an original-coordinate objective bound of
`opt+δ`. -/
theorem lemma2_rescale_objective_of_bridge (m : ℕ) (b : Fin m → ℝ) (R r δ opt optLift : ℝ)
    (yLift : Fin (m + 1) → ℝ) (hR : 0 ≤ R + 1) (hy : 0 ≤ yLift (Fin.last m))
    (hobj : lemma2LiftedObjective m b R yLift ≤ optLift + δ / r)
    (hbridge : optLift + δ / r ≤ opt + δ) :
    (∑ i : Fin m, yLift i.castSucc * b i ≤ opt + δ) := by
  unfold lemma2LiftedObjective at hobj
  have hnonneg : 0 ≤ (R + 1) * yLift (Fin.last m) := mul_nonneg hR hy
  have hsum : (∑ i : Fin m, yLift i.castSucc * b i) = (∑ i : Fin m, b i * yLift i.castSucc) :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hsum]
  nlinarith

end

end Qatlib.Concepts.RationalScan.Step2Scan
