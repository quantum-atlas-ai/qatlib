/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationDefs
import Qatlib.Concepts.MatrixWeights.WeightsCore
import Mathlib.Tactic.FinCases

/-!
# Sampled SDP width bounds and their boundary

This module proves `clause29`, which turns nonnegative round vectors with `widthSampled`
objective bounds into matrix payoffs in the interval from zero to the identity. It also
establishes the sampled-to-exact width identities, rescaled objective bounds, and the objective
bound for `sdpDualCertificate`.

The width bookkeeping belongs to the quantum SDP framework of [BrandaoSvore2017]. The theorem
additionally supplies `widthWrongStrongBoundary`, an explicit example showing that a larger
width allowance can produce a payoff above the identity; its certificate conclusion bounds the
objective.

## Main statements

* `clause29`: Under the stated SDP, width, and parameter hypotheses, obtain unit-interval
  payoffs, rescaling identities, and certificate objective at most `(1 + δ) * α`, together with
  the wider-width boundary example.
* `fromBlocks_zero_zero_posSemidef`: A block diagonal matrix with positive semidefinite diagonal
  blocks is positive semidefinite.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixWeights.WeightsCore
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

open Qatlib.Concepts.SdpDuality.ConeSeparation  Matrix
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open Qatlib.Concepts.RationalScan.Step2Scan Qatlib.Concepts.SdpDuality.ConeSeparation

open Qatlib.Concepts.RationalScan.Step2Scan Qatlib.Concepts.SdpDuality.ConeSeparation
set_option warningAsError false
set_option maxHeartbeats 800000

/-- The two scalar identity constraint matrices used to witness failure under the wider width
allowance. -/
private noncomputable def WA : Fin 2 → Operator 1 := fun _ => (1 : Operator 1)
/-- The scalar negative identity objective matrix used in the wider-width boundary example. -/
private noncomputable def WCv : Operator 1 := -(1 : Operator 1)
/-- The constraint bounds one and two for the two-constraint wider-width boundary example. -/
private def Wb : Fin 2 → ℝ := fun i => if i = 0 then (1:ℝ) else (2:ℝ)
/-- The constant history assigning weight four to constraint zero and weight zero to constraint
one. -/
private noncomputable def Wy : ℕ → Fin 2 → ℝ := fun _ i => if i = 0 then (4:ℝ) else (0:ℝ)

/-- The first constraint bound in `Wb` is one. -/
private theorem hWb0 : Wb 0 = (1:ℝ) := if_pos rfl

/-- The second constraint bound in `Wb` is two. -/
private theorem hWb1 : Wb 1 = (2:ℝ) := if_neg (by decide)

/-- At every time, `Wy` assigns weight four to constraint zero. -/
private theorem hWy0 (t : ℕ) : Wy t 0 = (4:ℝ) := if_pos rfl

/-- At every time, `Wy` assigns weight zero to constraint one. -/
private theorem hWy1 (t : ℕ) : Wy t 1 = (0:ℝ) := if_neg (by decide)

/-- Every index in `Fin 2` is zero or one. -/
private theorem hfin2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
  intro i
  fin_cases i <;> simp

/-- Under the stated SDP, parameter, and sampled-width assumptions, the round payoffs lie
between zero and the identity, rescaling gives the exact width bound, and the averaged dual
certificate has objective at most `(1 + δ) * α`. The conclusion also includes an explicit
witness that the larger width allowance in `widthWrongStrongBoundary` can violate the
unit-interval payoff condition. -/
theorem clause29 : (
  ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
      (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (T : ℕ) (α R δ ε η : ℝ),
    SdpInstance D m A Cv b j₀ R →
    0 < T → 2 ≤ α → α ≤ R →
    0 < δ → δ ≤ 1 → 0 < ε → 2 * R * ε ≤ 1 / 2 → 2 * R * ε ≤ δ / 2 →
    0 < η → η ≤ 1 → η + ε ≤ δ / (8 * R) →
    T = sdpDualCertRounds D R δ η →
    (∀ t < T, (∀ i, 0 ≤ y t i) ∧ certificateObjective m b (y t) ≤ widthSampled α R ε) →

    (∀ s < T, payoffUnitInterval D (dualPayoff D m A Cv α y s)) ∧

    (widthSampled α R ε = widthExact α + widthBridgeSlack α R ε) ∧
    (∀ t < T,
      certificateObjective m b (y t) ≤ widthSampled α R ε ↔
        certificateObjective m b (y t) ≤ widthExact α + widthBridgeSlack α R ε) ∧
    (∀ t < T,
      certificateObjective m b (fun i => y t i / (1 + 2 * R * ε)) ≤ widthExact α) ∧
    (∀ t < T, ∀ ρ : Operator D, IsDensityOperator ρ →
      sourcePayoffTarget D Cv ρ α ε ≤ ∑ i, y t i * (Matrix.trace (A i * ρ)).re →
        sourcePayoffTarget D Cv ρ α ε ≤
          (1 + 2 * R * ε) *
            (∑ i, (y t i / (1 + 2 * R * ε)) * (Matrix.trace (A i * ρ)).re) +
            exactWidthSlack α R ε) ∧

    (certificateObjective m b (dualCertificate m δ α R j₀ y T) ≤ (1 + δ) * α) ∧
    (∑ i, sdpDualCertificate m δ α R j₀ y T i * b i ≤ (1 + δ) * α) ∧

    widthWrongStrongBoundary

  ) := by
  intro D m A Cv b y j₀ T α R δ ε η hSdp hT0 hα2 hαR hδ0 hδ1 hε0 hε1 hε2 hη0 hη1 hηε hTeq hy
  obtain ⟨hD0, hm0, hR0, hA, hCv, hCvn, hb, hAj0, hbj0⟩ := hSdp
  have hα0 : 0 < α := lt_of_lt_of_le (by norm_num) hα2
  have hyT : ∀ t < T, (∀ i, 0 ≤ y t i) ∧ certificateObjective m b (y t) ≤ widthSampled α R ε :=
    hy
  have hW : ∀ t < T, (∑ i, y t i * b i) ≤ α * (1 + 2 * R * ε) := by
    intro t ht
    have := (hyT t ht).2
    simpa [certificateObjective, widthSampled] using! this
  have hc : 0 < 1 + 2 * R * ε := by nlinarith [hR0, hε0, hα0, hα2]
  have hcross : 2 * α * R * ε ≤ α / 2 := by
    have h1 : α * (2 * R * ε) ≤ α * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hε1 hα0.le
    have h2 : α * (2 * R * ε) = 2 * α * R * ε := by ring
    have h3 : α * (1 / 2 : ℝ) = α / 2 := by ring
    rw [h2, h3] at h1
    exact h1
  have hsumLE : ∀ t < T, (∑ i, y t i) ≤ α + α / 2 := by
    intro t ht
    have hmass : (∑ i, y t i) ≤ ∑ i, y t i * b i := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [(hyT t ht).1 i, hb i]
    have hexpand : α * (1 + 2 * R * ε) = α + 2 * α * R * ε := by ring
    have hWt := hW t ht
    rw [hexpand] at hWt
    linarith

  have h1 : ∀ s < T, payoffUnitInterval D (dualPayoff D m A Cv α y s) := by
    intro s hs
    let Z : Operator D := (∑ i, y s i • A i) - Cv
    have hsum : (∑ i, y s i • A i).IsHermitian :=
      isSelfAdjoint_sum _ (fun i _ => (hA i).1.smul (by simp [IsSelfAdjoint]))
    have hZ : Z.IsHermitian := hsum.sub hCv
    have hn : ‖∑ i, y s i • A i‖ ≤ ∑ i, y s i := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((hyT s hs).1 i)]
      simpa only [mul_one] using! mul_le_mul_of_nonneg_left (hA i).2 ((hyT s hs).1 i)
    have hnZ : ‖Z‖ ≤ 2 * α := by
      have htri := norm_sub_le (∑ i, y s i • A i) Cv
      change ‖Z‖ ≤ _ at htri
      linarith [hCvn, hn, hsumLE s hs, hα2]
    have hpad : ((2 * α - ‖Z‖) • (1 : Operator D)).PosSemidef :=
      (Matrix.PosSemidef.one : (1 : Operator D).PosSemidef).smul
        (by exact_mod_cast (sub_nonneg.mpr hnZ))
    have hupper : ((2 * α) • (1 : Operator D) - Z).PosSemidef := by
      convert! (mmw_shift_posSemidef D Z hZ hD0).add hpad using 1
      module
    have hlower : (Z + (2 * α) • (1 : Operator D)).PosSemidef := by
      have h := (mmw_shift_posSemidef D (-Z) hZ.neg hD0).add hpad
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

  have h2a : widthSampled α R ε = widthExact α + widthBridgeSlack α R ε := by
    show α * (1 + 2 * R * ε) = α + 2 * R * ε * α
    ring
  have h2b : ∀ t < T, certificateObjective m b (y t) ≤ widthSampled α R ε ↔
      certificateObjective m b (y t) ≤ widthExact α + widthBridgeSlack α R ε := by
    intro t ht
    constructor <;> intro h
    · rw [← h2a]; exact h
    · rw [h2a]; exact h
  have h2c : ∀ t < T,
      certificateObjective m b (fun i => y t i / (1 + 2 * R * ε)) ≤ widthExact α := by
    intro t ht
    show (∑ i, (y t i / (1 + 2 * R * ε)) * b i) ≤ α
    have hkey : (∑ i, (y t i / (1 + 2 * R * ε)) * b i) = (∑ i, y t i * b i) / (1 + 2 * R * ε) := by
      have hterm : ∀ i, (y t i / (1 + 2 * R * ε)) * b i = (y t i * b i) / (1 + 2 * R * ε) := by
        intro i; field_simp
      simp only [hterm]
      rw [← Finset.sum_div]
    rw [hkey, div_le_iff₀ hc]
    exact hW t ht
  have h2d : ∀ t < T, ∀ ρ : Operator D, IsDensityOperator ρ →
      sourcePayoffTarget D Cv ρ α ε ≤ ∑ i, y t i * (Matrix.trace (A i * ρ)).re →
        sourcePayoffTarget D Cv ρ α ε ≤
          (1 + 2 * R * ε) *
            (∑ i, (y t i / (1 + 2 * R * ε)) * (Matrix.trace (A i * ρ)).re) +
            exactWidthSlack α R ε := by
    intro t ht ρ hρ hp
    have hId : (1 + 2 * R * ε) *
        (∑ i, (y t i / (1 + 2 * R * ε)) * (Matrix.trace (A i * ρ)).re) =
        ∑ i, y t i * (Matrix.trace (A i * ρ)).re := by
      have hterm : ∀ i, (1 + 2 * R * ε) *
          ((y t i / (1 + 2 * R * ε)) * (Matrix.trace (A i * ρ)).re) =
          y t i * (Matrix.trace (A i * ρ)).re := by
        intro i; field_simp
      calc
        _ = ∑ i, (1 + 2 * R * ε) *
              ((y t i / (1 + 2 * R * ε)) * (Matrix.trace (A i * ρ)).re) := by rw [Finset.mul_sum]
        _ = _ := by simp only [hterm]
    rw [hId]
    have hsl2 : 0 ≤ exactWidthSlack α R ε := by
      show 0 ≤ 2 * α * R * ε
      positivity
    linarith

  have hTpos : 0 < (T:ℝ) := by exact_mod_cast hT0
  have heq : dualCertificate m δ α R j₀ y T = sdpDualCertificate m δ α R j₀ y T := rfl
  have heval : (∑ i, sdpDualCertificate m δ α R j₀ y T i * b i) =
      δ * α / (2 * R) * b j₀ + (∑ t ∈ Finset.range T, ∑ i, y t i * b i) / T := by
    simp only [sdpDualCertificate, add_mul, div_mul_eq_mul_div, Finset.sum_add_distrib,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    simp only [Finset.sum_mul, ← Finset.sum_div]
    rw [Finset.sum_comm]
  have hwT : (∑ t ∈ Finset.range T, ∑ i, y t i * b i) ≤
      (T : ℝ) * (α * (1 + 2 * R * ε)) := by
    calc
      _ ≤ ∑ _t ∈ Finset.range T, α * (1 + 2 * R * ε) := by
        apply Finset.sum_le_sum
        intro t ht
        have hlt : t < T := Finset.mem_range.mp ht
        exact hW t hlt
      _ = _ := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hav : (∑ t ∈ Finset.range T, ∑ i, y t i * b i) / T ≤ α * (1 + 2 * R * ε) := by
    apply (div_le_iff₀ hTpos).mpr
    simpa only [mul_comm] using! hwT
  have h3main : (∑ i, sdpDualCertificate m δ α R j₀ y T i * b i) ≤ (1 + δ) * α := by
    rw [heval, hbj0]
    have hoff : δ * α / (2 * R) * R = δ * α / 2 := by field_simp
    rw [hoff]
    have hcross2 : 2 * α * R * ε ≤ α * δ / 2 := by
      have h1 : α * (2 * R * ε) ≤ α * (δ / 2 : ℝ) := mul_le_mul_of_nonneg_left hε2 hα0.le
      have h2 : α * (2 * R * ε) = 2 * α * R * ε := by ring
      have h3 : α * (δ / 2 : ℝ) = α * δ / 2 := by ring
      rw [h2, h3] at h1
      exact h1
    have hexpand : α * (1 + 2 * R * ε) = α + 2 * α * R * ε := by ring
    rw [hexpand] at hav
    nlinarith
  have h3 : certificateObjective m b (dualCertificate m δ α R j₀ y T) ≤ (1 + δ) * α := by
    rw [heq]
    show (∑ i, sdpDualCertificate m δ α R j₀ y T i * b i) ≤ (1 + δ) * α
    exact h3main
  have h3b : (∑ i, sdpDualCertificate m δ α R j₀ y T i * b i) ≤ (1 + δ) * α := h3main

  have h4 : widthWrongStrongBoundary := by
    refine ⟨1, 2, WA, WCv, Wb, Wy, 1, (2:ℝ), (2:ℝ), ((1:ℝ)/8), ?_⟩
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      show ((1 : Operator 1)).IsHermitian ∧ ‖(1 : Operator 1)‖ ≤ 1
      exact ⟨Matrix.isHermitian_one, le_of_eq norm_one⟩
    · show WCv.IsHermitian
      exact Matrix.isHermitian_one.neg
    · show ‖WCv‖ ≤ 1
      rw [show WCv = -(1 : Operator 1) from rfl, norm_neg]
      exact le_of_eq norm_one
    · intro i
      obtain hi | hi := hfin2 i
      · subst hi; simp [hWb0]
      · subst hi; simp [hWb1]
    · show WA 1 = 1
      rfl
    · show Wb 1 = (2:ℝ)
      exact hWb1
    · intro t
      refine ⟨?_, ?_⟩
      · intro i
        obtain hi | hi := hfin2 i
        · subst hi; simp [hWy0]
        · subst hi; simp [hWy1]
      · show (∑ i : Fin 2, Wb i * Wy t i) ≤ (2:ℝ) * (1 + 4 * 2 * ((1:ℝ)/8))
        rw [Fin.sum_univ_two, hWb0, hWb1, hWy0, hWy1]
        norm_num
    · show (2:ℝ) * (1 + 2 * 2 * ((1:ℝ)/8)) < ∑ i : Fin 2, Wb i * Wy 0 i
      rw [Fin.sum_univ_two, hWb0, hWb1, hWy0, hWy1]
      norm_num
    · intro hpu
      obtain ⟨_, _, hle⟩ := hpu
      have hpay : dualPayoff 1 2 WA WCv (2:ℝ) Wy 0 = ((9 / 8 : ℝ) • (1 : Operator 1)) := by
        show ((4 * 2 : ℝ))⁻¹ •
            ((∑ i : Fin 2, Wy 0 i • WA i) - WCv + ((2 * 2 : ℝ) • (1 : Operator 1))) = _
        have hsumw : (∑ i : Fin 2, Wy 0 i • WA i) = (4:ℝ) • (1 : Operator 1) := by
          rw [Fin.sum_univ_two, hWy0, hWy1]
          show (4:ℝ) • (1 : Operator 1) + (0:ℝ) • (1 : Operator 1) = (4:ℝ) • (1 : Operator 1)
          rw [zero_smul, add_zero]
        rw [hsumw]
        have hbr : (((4:ℝ) • (1 : Operator 1)) - WCv + ((2 * 2 : ℝ) • (1 : Operator 1)))
            = (((9:ℝ) • (1 : Operator 1))) := by
          show (((4:ℝ) • (1 : Operator 1)) - (-(1 : Operator 1)) + ((2 * 2 : ℝ) • (1 : Operator 1)))
              = (((9:ℝ) • (1 : Operator 1)))
          module
        rw [hbr, smul_smul]
        have hco : ((4 * 2 : ℝ))⁻¹ * 9 = (9 / 8 : ℝ) := by norm_num
        rw [hco]
      rw [hpay] at hle
      have hsub : (1 : Operator 1) - ((9 / 8 : ℝ) • (1 : Operator 1))
          = ((-1 / 8 : ℝ) • (1 : Operator 1)) := by module
      have hpsd : (((-1 / 8 : ℝ) • (1 : Operator 1)) : Operator 1).PosSemidef := by
        rw [← hsub]
        exact Matrix.le_iff.mp hle
      have hdiag := Matrix.PosSemidef.diag_nonneg hpsd (i := (0 : Fin 1))
      simp only [Matrix.smul_apply, Matrix.one_apply_eq] at hdiag
      norm_num at hdiag
      linarith
  exact ⟨h1, h2a, h2b, h2c, h2d, h3, h3b, h4⟩

/-- A block diagonal complex matrix with positive semidefinite diagonal blocks is positive
semidefinite, including when an index type is empty. -/
private theorem fromBlocks_zero_zero_posSemidef {m n : Type*} [Fintype m] [Fintype n]
    {P : Matrix m m ℂ} {Q : Matrix n n ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    (Matrix.fromBlocks P 0 0 Q).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.fromBlocks hP.1 (by simp) hQ.1, fun v => ?_⟩
  have hp' := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hP).2 (fun i => v (Sum.inl i))
  have hq' := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hQ).2 (fun i => v (Sum.inr i))
  simpa only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
    Pi.star_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
    using add_nonneg hp' hq'

end Qatlib.Concepts.SdpDuality.ConeSeparation
