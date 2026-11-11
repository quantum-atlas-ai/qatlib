/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.MainResults.Source.Dirichlet
import Qatlib.Papers.GaussSumEst02.MainResults.Source.Cost
import Qatlib.Papers.GaussSumEst02.MainResults.Source.PhaseSampling

/-!
# Conditional ring Gauss-sum phase estimation

The theorem `theorem2_ringGaussSumEstimation` gives a polar form and estimation bound for a ring
Gauss sum at a unit frequency. It assumes the square-root norm at frequency one,
`PhaseAccessModel`, and a polylogarithmic per-sample cost. See [VanDamSeroussi2002].

## Main statements

* `theorem2_ringGaussSumEstimation`: At a unit frequency, an assumed base Gauss-sum norm of `√n`
  yields the same norm and a polar representation at that frequency. Given `PhaseAccessModel`
  and polylogarithmic per-sample cost, protocols attain any positive expected absolute
  angular-error tolerance with the stated `sampleCount` times polylogarithmic cost bound.

## References

* [van Dam and Seroussi, 2002][VanDamSeroussi2002]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.MainResults.Claims

open Qatlib.Papers.GaussSumEst02.MainResults.Source

/-- At a unit frequency, an assumed base Gauss-sum norm of `√n` yields the same norm and a polar
representation at that frequency. Given `PhaseAccessModel` and polylogarithmic per-sample
cost, protocols attain any positive expected absolute angular-error tolerance with the
stated `sampleCount` times polylogarithmic cost bound [VanDamSeroussi2002]. -/
theorem theorem2_ringGaussSumEstimation (n : ℕ) [NeZero n] (χ : DirichletChar n)
    (e : AddChar (ZMod n)) {β : ZMod n} (hβ : IsUnit β)
    (hprim : ‖ringGaussSum χ e 1‖ = Real.sqrt (n : ℝ))
    (perSample : ℕ → ℕ) (hper : PolyLog perSample) (M : PhaseAccessModel) :
    ∃ γ : ℝ,
      ringGaussSum χ e β
          = (‖ringGaussSum χ e β‖ : ℂ) * Complex.exp (γ * Complex.I) ∧
      ‖ringGaussSum χ e β‖ = Real.sqrt (n : ℝ) ∧
      ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ ∀ ε : ℝ, 0 < ε →
        ∃ (P : SamplingProtocol) (t : ℕ), 0 < t ∧
          expectedAngularError γ P t < ε ∧
          t * perSample n ≤ C * sampleCount ε * bitLength n ^ d := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hnormβ : ‖ringGaussSum χ e β‖ = Real.sqrt (n : ℝ) :=
    ringGaussSum_norm χ e hβ hprim
  have hmpos : 0 < ‖ringGaussSum χ e β‖ := by
    rw [hnormβ]
    exact hsqrtpos
  have hmne : ((‖ringGaussSum χ e β‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact hmpos.ne'
  have hunit : ‖ringGaussSum χ e β / ((‖ringGaussSum χ e β‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmpos,
      div_self hmpos.ne']
  obtain ⟨γ, _, hγ⟩ := Complex.norm_eq_one_iff'.mp hunit
  refine ⟨γ, ?_, hnormβ, ?_⟩
  · rw [hγ]
    field_simp
  · obtain ⟨C₀, hC₀, hbound⟩ := M.queries_bound
    obtain ⟨c, d, hc, hd, hperb⟩ := hper
    refine ⟨C₀ * c, d, Nat.mul_pos hC₀ hc, hd, ?_⟩
    intro ε hε
    refine ⟨M.protocol ε, M.queries ε, M.queries_pos ε hε,
      M.accuracy γ ε hε, ?_⟩
    calc M.queries ε * perSample n
        ≤ (C₀ * sampleCount ε) * (c * bitLength n ^ d) :=
          Nat.mul_le_mul (hbound ε hε) (hperb n)
      _ = (C₀ * c) * sampleCount ε * bitLength n ^ d := by ring

end Qatlib.Papers.GaussSumEst02.MainResults.Claims
