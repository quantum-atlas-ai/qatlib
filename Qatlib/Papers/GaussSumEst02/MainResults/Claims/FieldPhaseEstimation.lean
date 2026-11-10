/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.MainResults.Source.GaussSumCore
import Qatlib.Papers.GaussSumEst02.MainResults.Source.Cost
import Qatlib.Papers.GaussSumEst02.MainResults.Source.PhaseSampling
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.MainResults.Claims

open Qatlib.Papers.GaussSumEst02.MainResults.Source

theorem theorem1_fieldGaussSumEstimation {K : Type*} [Field K] [Fintype K] (χ : MultChar K)
    (e : AddChar K) (hnt : χ.IsNontrivial) {β : K} (hβ : β ≠ 0)
    (perSample : ℕ → ℕ) (hper : PolyLog perSample) (M : PhaseAccessModel) :
    ∃ γ : ℝ,
      gaussSum χ.toFun e β
          = (Real.sqrt (Fintype.card K) : ℂ) * Complex.exp (γ * Complex.I) ∧
      (fun y : K => (χ.toFun y) ^ 2 * fourierChi χ e β y)
          = (Complex.exp (γ * Complex.I)) • chiState χ ∧
      ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ ∀ ε : ℝ, 0 < ε →
        ∃ (P : SamplingProtocol) (t : ℕ), 0 < t ∧
          expectedAngularError γ P t < ε ∧
          t * perSample (Fintype.card K)
            ≤ C * sampleCount ε * bitLength (Fintype.card K) ^ d := by
  obtain ⟨γ, hγ⟩ := gaussSum_polar χ e hnt hβ
  refine ⟨γ, hγ, ?_, ?_⟩
  · have hNpos : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
    have hsqrt_ne : ((Real.sqrt (Fintype.card K) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact (Real.sqrt_pos.mpr hNpos).ne'
    have hscalar : gaussSum χ.toFun e β / ((Real.sqrt (Fintype.card K) : ℝ) : ℂ)
        = Complex.exp (γ * Complex.I) := by
      rw [hγ]
      field_simp
    rw [algorithm1_phase_change χ e hnt hβ, hscalar]
  · obtain ⟨C₀, hC₀, hbound⟩ := M.queries_bound
    obtain ⟨c, d, hc, hd, hperb⟩ := hper
    refine ⟨C₀ * c, d, Nat.mul_pos hC₀ hc, hd, ?_⟩
    intro ε hε
    refine ⟨M.protocol ε, M.queries ε, M.queries_pos ε hε,
      M.accuracy γ ε hε, ?_⟩
    calc M.queries ε * perSample (Fintype.card K)
        ≤ (C₀ * sampleCount ε) * (c * bitLength (Fintype.card K) ^ d) :=
          Nat.mul_le_mul (hbound ε hε) (hperb (Fintype.card K))
      _ = (C₀ * c) * sampleCount ε * bitLength (Fintype.card K) ^ d := by ring

end Qatlib.Papers.GaussSumEst02.MainResults.Claims
