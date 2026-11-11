/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QIntegration00.MainResults.Defs

/-!
# Conditional query order for quantum integration

Assumed cost and error estimates yield an upper query bound for `complexityOf`; an assumed
lower-bound family yields the matching lower power. The theorem `theorem1_query_order` combines
these estimates into `IsThetaQuantumQuery` on a prescribed error interval. See [Novak2001] for
the paper context.

## Main statements

* `query_upper_bound`: The assumed inverse-parameter cost and power error estimates bound the
  complexity by `C * c^(1/(1+γ)) * ε^(-1/(1+γ))` for `0 < ε ≤ c`.
* `query_lower_bound`: The assumed lower bound at errors `t^(1+1/γ)` gives the lower query bound
  `c * ε^(-1/(1+γ))` for `0 < ε ≤ 1`.
* `theorem1_query_order`: The assumed upper estimates and lower-bound family imply
  `IsThetaQuantumQuery` with lower constant `c_lw` and upper constant `C * c^(1/(1+γ))` on the
  stated interval.

## References

* [Novak, 2001][Novak2001]
-/

set_option warningAsError false

noncomputable section

set_option autoImplicit false

namespace Qatlib.Papers.QIntegration00.MainResults.QueryTheorem

open Defs

/-- The assumed inverse-parameter cost and power error estimates bound the complexity by `C *
c^(1/(1+γ)) * ε^(-1/(1+γ))` for `0 < ε ≤ c`. -/
theorem query_upper_bound {γ C c : ℝ} (hγ : 0 < γ) (hC : 0 < C) (hc : 0 < c)
    {cost error : ℝ → ℝ} (hcost_nn : ∀ t, 0 ≤ cost t)
    (hcost : ∀ t ∈ Set.Ioc (0 : ℝ) 1, cost t ≤ C * t⁻¹)
    (herror : ∀ t ∈ Set.Ioc (0 : ℝ) 1, error t ≤ c * t ^ (1 + γ))
    {ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c) :
    complexityOf cost error ε ≤ C * c ^ (1 / (1 + γ)) * ε ^ (-1 / (1 + γ)) := by
  have hγ1 : (0 : ℝ) < 1 + γ := by linarith
  set t : ℝ := (ε / c) ^ (1 / (1 + γ)) with ht
  have hx : 0 < ε / c := div_pos hε hc
  have htpos : 0 < t := by
    rw [ht]
    exact Real.rpow_pos_of_pos hx _
  have hxle : ε / c ≤ 1 := by
    rw [div_le_one hc]
    exact hεc
  have htle : t ≤ 1 := by
    rw [ht]
    calc (ε / c) ^ (1 / (1 + γ)) ≤ 1 ^ (1 / (1 + γ)) :=
          Real.rpow_le_rpow (le_of_lt hx) hxle (by positivity)
      _ = 1 := Real.one_rpow _
  have htmem : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨htpos, htle⟩
  have hpow : t ^ (1 + γ) = ε / c := by
    rw [ht, ← Real.rpow_mul (le_of_lt hx)]
    have h1 : (1 / (1 + γ)) * (1 + γ) = 1 := by
      field_simp
    rw [h1, Real.rpow_one]
  have herrt : error t ≤ ε := by
    refine (herror t htmem).trans ?_
    rw [hpow]
    have : c * (ε / c) = ε := by
      field_simp
    exact le_of_eq this
  have htinv : t⁻¹ = c ^ (1 / (1 + γ)) * ε ^ (-1 / (1 + γ)) := by
    rw [ht, (Real.inv_rpow (le_of_lt hx) (1 / (1 + γ))).symm]
    have hxinv : (ε / c)⁻¹ = c / ε := by
      field_simp
    rw [hxinv, Real.div_rpow (le_of_lt hc) (le_of_lt hε)]
    have hepsneg : (ε ^ (1 / (1 + γ)))⁻¹ = ε ^ (-1 / (1 + γ)) := by
      rw [← Real.rpow_neg (le_of_lt hε)]
      congr 1
      ring
    rw [div_eq_mul_inv, hepsneg]
  calc complexityOf cost error ε ≤ cost t := complexityOf_le hcost_nn htpos herrt
    _ ≤ C * t⁻¹ := hcost t htmem
    _ = C * (c ^ (1 / (1 + γ)) * ε ^ (-1 / (1 + γ))) := by rw [htinv]
    _ = C * c ^ (1 / (1 + γ)) * ε ^ (-1 / (1 + γ)) := by ring

/-- The assumed lower bound at errors `t^(1+1/γ)` gives the lower query bound `c * ε^(-1/(1+γ))`
for `0 < ε ≤ 1`. -/
theorem query_lower_bound {γ c : ℝ} (hγ : 0 < γ) (hc : 0 < c)
    {cost error : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hnw : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      c * t ^ (-1 / γ) ≤ complexityOf cost error (t ^ (1 + 1 / γ))) :
    c * ε ^ (-1 / (1 + γ)) ≤ complexityOf cost error ε := by
  have hγne : γ ≠ 0 := ne_of_gt hγ
  have hγ1 : (0 : ℝ) < 1 + γ := by linarith
  set t : ℝ := ε ^ (γ / (1 + γ)) with ht
  have htpos : 0 < t := by
    rw [ht]
    exact Real.rpow_pos_of_pos hε _
  have htle : t ≤ 1 := by
    rw [ht]
    calc ε ^ (γ / (1 + γ)) ≤ 1 ^ (γ / (1 + γ)) :=
          Real.rpow_le_rpow (le_of_lt hε) hε1 (by positivity)
      _ = 1 := Real.one_rpow _
  have hte : t ^ (1 + 1 / γ) = ε := by
    rw [ht, ← Real.rpow_mul (le_of_lt hε)]
    have hexp : (γ / (1 + γ)) * (1 + 1 / γ) = 1 := by
      field_simp
      ring
    rw [hexp, Real.rpow_one]
  have htl : t ^ (-1 / γ) = ε ^ (-1 / (1 + γ)) := by
    rw [ht, ← Real.rpow_mul (le_of_lt hε)]
    congr 1
    field_simp
  have h := hnw t ⟨htpos, htle⟩
  rw [hte, htl] at h
  exact h

/-- The assumed upper estimates and lower-bound family imply `IsThetaQuantumQuery` with lower
constant `c_lw` and upper constant `C * c^(1/(1+γ))` on the stated interval. See
[Novak2001]. -/
theorem theorem1_query_order {γ c C c_lw : ℝ} (hγ : 0 < γ) (hC : 0 < C) (hc : 0 < c)
    (hclw : 0 < c_lw)
    {cost error : ℝ → ℝ} (hcost_nn : ∀ t, 0 ≤ cost t)
    (hcost : ∀ t ∈ Set.Ioc (0 : ℝ) 1, cost t ≤ C * t⁻¹)
    (herror : ∀ t ∈ Set.Ioc (0 : ℝ) 1, error t ≤ c * t ^ (1 + γ))
    (hnw : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      c_lw * t ^ (-1 / γ) ≤ complexityOf cost error (t ^ (1 + 1 / γ)))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀c : ε₀ ≤ c) (hε₀1 : ε₀ ≤ 1 / 2) :
    IsThetaQuantumQuery γ c_lw (C * c ^ (1 / (1 + γ))) ε₀ (complexityOf cost error) := by
  refine ⟨hclw, mul_pos hC (Real.rpow_pos_of_pos hc _), ?_⟩
  intro ε hε
  obtain ⟨hεpos, hεle⟩ := hε
  refine ⟨?_, ?_⟩
  · exact query_lower_bound hγ hclw hεpos
      (le_trans (le_trans hεle hε₀1) (by norm_num : (1 : ℝ) / 2 ≤ 1)) hnw
  · exact query_upper_bound hγ hC hc hcost_nn hcost herror hεpos (le_trans hεle hε₀c)

end Qatlib.Papers.QIntegration00.MainResults.QueryTheorem
