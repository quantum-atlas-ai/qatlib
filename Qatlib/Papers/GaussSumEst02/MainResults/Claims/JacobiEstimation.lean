/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.MainResults.Source.Jacobi
import Qatlib.Papers.GaussSumEst02.MainResults.Source.Cost
import Qatlib.Papers.GaussSumEst02.MainResults.Source.PhaseSampling
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.MainResults.Claims

open Qatlib.Papers.GaussSumEst02.MainResults.Source

theorem corollary1_jacobiEstimation {K : Type*} [Field K] [Fintype K] (χ ψ : MultChar K)
    (e : AddChar K) (hχ : χ.IsNontrivial) (hψ : ψ.IsNontrivial)
    (hχψ : (multChar_mul χ ψ).IsNontrivial)
    (perSample : ℕ → ℕ) (hper : PolyLog perSample) (M : PhaseAccessModel) :
    ∃ (lam γχ γψ γχψ : ℝ),
      jacobiSum χ ψ
          = (Real.sqrt (Fintype.card K) : ℂ) * Complex.exp (lam * Complex.I) ∧
      gaussSum χ.toFun e 1
          = (Real.sqrt (Fintype.card K) : ℂ) * Complex.exp (γχ * Complex.I) ∧
      gaussSum ψ.toFun e 1
          = (Real.sqrt (Fintype.card K) : ℂ) * Complex.exp (γψ * Complex.I) ∧
      gaussSum (fun x => χ.toFun x * ψ.toFun x) e 1
          = (Real.sqrt (Fintype.card K) : ℂ) * Complex.exp (γχψ * Complex.I) ∧
      Complex.exp (lam * Complex.I)
          = Complex.exp ((γχ + γψ - γχψ) * Complex.I) ∧
      ‖jacobiSum χ ψ‖ = Real.sqrt (Fintype.card K) ∧
      (∀ ε : ℝ, 0 < ε → ∀ gχ gψ gχψ : ℝ,
        ‖Complex.exp (gχ * Complex.I) - Complex.exp (γχ * Complex.I)‖ < ε / 3 →
        ‖Complex.exp (gψ * Complex.I) - Complex.exp (γψ * Complex.I)‖ < ε / 3 →
        ‖Complex.exp (gχψ * Complex.I) - Complex.exp (γχψ * Complex.I)‖ < ε / 3 →
        ‖Complex.exp ((gχ + gψ - gχψ) * Complex.I) - Complex.exp (lam * Complex.I)‖
          < ε) ∧
      ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ ∀ ε : ℝ, 0 < ε →
        ∃ (Pχ Pψ Pχψ : SamplingProtocol) (tχ tψ tχψ : ℕ),
          0 < tχ ∧ 0 < tψ ∧ 0 < tχψ ∧
          expectedAngularError γχ Pχ tχ < ε / 3 ∧
          expectedAngularError γψ Pψ tψ < ε / 3 ∧
          expectedAngularError γχψ Pχψ tχψ < ε / 3 ∧
          (tχ + tψ + tχψ) * perSample (Fintype.card K)
            ≤ C * sampleCount ε * bitLength (Fintype.card K) ^ d := by
  obtain ⟨lam, hlam⟩ := jacobiSum_polar χ ψ e hχ hψ hχψ
  obtain ⟨γχ, hγχ⟩ := gaussSum_polar χ e hχ (β := (1 : K)) one_ne_zero
  obtain ⟨γψ, hγψ⟩ := gaussSum_polar ψ e hψ (β := (1 : K)) one_ne_zero
  obtain ⟨γχψ, hγχψ⟩ :=
    gaussSum_polar (multChar_mul χ ψ) e hχψ (β := (1 : K)) one_ne_zero
  have hphase : Complex.exp (lam * Complex.I)
      = Complex.exp ((γχ + γψ - γχψ) * Complex.I) :=
    jacobiSum_phase_exp χ ψ e hχ hψ hχψ hlam hγχ hγψ hγχψ
  have hnorm : ‖jacobiSum χ ψ‖ = Real.sqrt (Fintype.card K) :=
    jacobiSum_norm χ ψ e hχ hψ hχψ
  refine ⟨lam, γχ, γψ, γχψ, hlam, hγχ, hγψ, hγχψ, hphase, hnorm, ?_, ?_⟩
  · intro ε hε gχ gψ gχψ h1 h2 h3
    have hprodχ : Complex.exp (gχ * Complex.I) * Complex.exp (gψ * Complex.I)
          * (Complex.exp (gχψ * Complex.I))⁻¹
        = Complex.exp ((gχ + gψ - gχψ) * Complex.I) :=
      exp_angle_prod gχ gψ gχψ
    have hprodγ : Complex.exp (γχ * Complex.I) * Complex.exp (γψ * Complex.I)
          * (Complex.exp (γχψ * Complex.I))⁻¹
        = Complex.exp ((γχ + γψ - γχψ) * Complex.I) :=
      exp_angle_prod γχ γψ γχψ
    rw [← hprodχ, hphase, ← hprodγ]
    have hb1 : ‖Complex.exp (gχ * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have hb2 : ‖Complex.exp (gψ * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have hb3 : ‖Complex.exp (gχψ * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have hB1 : ‖Complex.exp (γχ * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have hB2 : ‖Complex.exp (γψ * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have hB3 : ‖Complex.exp (γχψ * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have hc3 : ‖(Complex.exp (gχψ * Complex.I))⁻¹‖ = 1 := by
      rw [norm_inv, hb3, inv_one]
    have hC3 : ‖(Complex.exp (γχψ * Complex.I))⁻¹‖ = 1 := by
      rw [norm_inv, hB3, inv_one]
    have hthird : ‖(Complex.exp (gχψ * Complex.I))⁻¹ - (Complex.exp (γχψ * Complex.I))⁻¹‖
        = ‖Complex.exp (gχψ * Complex.I) - Complex.exp (γχψ * Complex.I)‖ :=
      norm_inv_sub_inv hb3 hB3
    have hm := norm_mul3_sub_mul3_le hb1 hb2 hc3 hB1 hB2 hC3
    rw [hthird] at hm
    linarith
  · obtain ⟨C₀, hC₀, hbound⟩ := M.queries_bound
    obtain ⟨c, d, hc, hd, hperb⟩ := hper
    refine ⟨9 * C₀ * c, d, by positivity, hd, ?_⟩
    intro ε hε
    have h3ε : (0 : ℝ) < ε / 3 := by positivity
    refine ⟨M.protocol (ε / 3), M.protocol (ε / 3), M.protocol (ε / 3),
      M.queries (ε / 3), M.queries (ε / 3), M.queries (ε / 3),
      M.queries_pos _ h3ε, M.queries_pos _ h3ε, M.queries_pos _ h3ε,
      M.accuracy γχ (ε / 3) h3ε, M.accuracy γψ (ε / 3) h3ε,
      M.accuracy γχψ (ε / 3) h3ε, ?_⟩
    have hsum : M.queries (ε / 3) + M.queries (ε / 3) + M.queries (ε / 3)
        ≤ 3 * (C₀ * sampleCount (ε / 3)) := by
      have h := hbound (ε / 3) h3ε
      linarith
    calc (M.queries (ε / 3) + M.queries (ε / 3) + M.queries (ε / 3))
          * perSample (Fintype.card K)
        ≤ (3 * (C₀ * sampleCount (ε / 3))) * (c * bitLength (Fintype.card K) ^ d) :=
          Nat.mul_le_mul hsum (hperb (Fintype.card K))
      _ ≤ (3 * (C₀ * (3 * sampleCount ε))) * (c * bitLength (Fintype.card K) ^ d) := by
          gcongr
          exact sampleCount_third_le ε hε
      _ = (9 * C₀ * c) * sampleCount ε * bitLength (Fintype.card K) ^ d := by ring

end Qatlib.Papers.GaussSumEst02.MainResults.Claims
