/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticPath02.MainResults.SymmetricDefs
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Basic

/-!
# Effective potential and its minimum value

Studies the straight and modified effective potentials `V0` and `V` associated with the
adiabatic paths in [FarhiGoldstoneGutmann2002a]. It proves endpoint minima, bounds at the
opposite pole, and minimization in the azimuthal variable for `V0`.

The minimum value `vMin` on the compact angular domain `Vdomain` exists for every interpolation
parameter and is continuous on `[0, 1]`, with zero values at both endpoints.

## Main statements

* `V_zero_global_min`: Identifies a zero global minimum at the initial endpoint.
* `V_one_global_min`: Identifies a zero global minimum at the final endpoint.
* `vMin_continuousOn`: Proves continuity of the minimum value on the interpolation interval.
* `source_effective_potential_conclusion`: Collects the potential identities, minima, and cost
  nonnegativity statements.

## References

* [Farhi et al., 2002][FarhiGoldstoneGutmann2002a]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticPath02.MainResults.EffectivePotential

open Qatlib.Papers.AdiabaticPath02.MainResults.PathDefs
open Qatlib.Papers.AdiabaticPath02.MainResults.SymmetricDefs
open scoped BigOperators

/-- Factors `13 + 3 * x - 9 * x ^ 2 - 7 * x ^ 3` as `(1 - x) * (7 * x ^ 2 + 16 * x + 13)`. -/
theorem cubic_factor (x : ℝ) :
    13 + 3 * x - 9 * x ^ 2 - 7 * x ^ 3 = (1 - x) * (7 * x ^ 2 + 16 * x + 13) := by
  ring

/-- The quadratic polynomial `7 * x ^ 2 + 16 * x + 13` is strictly positive for every real `x`. -/
theorem quad_pos (x : ℝ) : 0 < 7 * x ^ 2 + 16 * x + 13 := by
  have h : 0 < (7 * x + 8) ^ 2 + 27 := by positivity
  nlinarith

/-- Evaluates the straight-path potential at `s = 0` as `2 * (1 - Real.sin θ * Real.cos φ)`. -/
@[simp] theorem V0_zero (θ φ : ℝ) :
    V0 θ φ 0 = 2 * (1 - Real.sin θ * Real.cos φ) := by
  simp [V0]

/-- Evaluates the straight-path potential at `s = 1` as the cubic polynomial in `Real.cos θ`
divided by six. -/
@[simp] theorem V0_one (θ φ : ℝ) :
    V0 θ φ 1 =
      (1 / 6) * (13 + 3 * Real.cos θ - 9 * Real.cos θ ^ 2 - 7 * Real.cos θ ^ 3) := by
  simp [V0]

/-- The straight-path potential is nonnegative at `s = 0` for all angles. -/
theorem V0_zero_nonneg (θ φ : ℝ) : 0 ≤ V0 θ φ 0 := by
  rw [V0_zero]
  have hsin : |Real.sin θ| ≤ 1 :=
    abs_le.mpr ⟨by linarith [Real.neg_one_le_sin θ], Real.sin_le_one θ⟩
  have hcos : |Real.cos φ| ≤ 1 :=
    abs_le.mpr ⟨by linarith [Real.neg_one_le_cos φ], Real.cos_le_one φ⟩
  have habs : |Real.sin θ * Real.cos φ| ≤ 1 := by
    rw [abs_mul]
    have h := mul_le_mul hsin hcos (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using! h
  have hle : Real.sin θ * Real.cos φ ≤ 1 := le_trans (le_abs_self _) habs
  linarith

/-- The straight-path potential is nonnegative at `s = 1` for all angles. -/
theorem V0_one_nonneg (θ φ : ℝ) : 0 ≤ V0 θ φ 1 := by
  rw [V0_one]
  have hfac : 13 + 3 * Real.cos θ - 9 * Real.cos θ ^ 2 - 7 * Real.cos θ ^ 3 =
      (1 - Real.cos θ) * (7 * Real.cos θ ^ 2 + 16 * Real.cos θ + 13) :=
    cubic_factor (Real.cos θ)
  rw [hfac]
  have h1 : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
  have h2 : 0 ≤ 7 * Real.cos θ ^ 2 + 16 * Real.cos θ + 13 := (quad_pos _).le
  have hmul : 0 ≤ (1 - Real.cos θ) * (7 * Real.cos θ ^ 2 + 16 * Real.cos θ + 13) :=
    mul_nonneg h1 h2
  nlinarith

/-- The modified potential agrees with the straight-path potential at `s = 0`. -/
@[simp] theorem V_zero (θ φ : ℝ) : V θ φ 0 = V0 θ φ 0 := by
  simp [V, VE]

/-- The modified potential agrees with the straight-path potential at `s = 1`. -/
@[simp] theorem V_one (θ φ : ℝ) : V θ φ 1 = V0 θ φ 1 := by
  simp [V, VE]

/-- Expresses the modified potential as a term independent of `φ` minus an explicit coefficient
times `Real.cos φ`. See [FarhiGoldstoneGutmann2002a]. -/
theorem V_phi_linear (θ φ s : ℝ) :
    V θ φ s =
      2 * (1 - s) +
        (s / 6) * (13 + 3 * Real.cos θ - 9 * Real.cos θ ^ 2 - 7 * Real.cos θ ^ 3) -
        (2 * (1 - s) * Real.sin θ + 8 * s * (1 - s) * Real.cos θ * Real.sin θ) *
          Real.cos φ := by
  unfold V V0 VE
  ring

/-- At `s = 0`, the modified potential vanishes at `(θ, φ) = (π / 2, 0)` and is nonnegative at
every angular pair. -/
theorem V_zero_global_min :
    V (Real.pi / 2) 0 0 = 0 ∧ ∀ θ φ : ℝ, 0 ≤ V θ φ 0 := by
  constructor
  · rw [V_zero]
    norm_num [V0, Real.sin_pi_div_two, Real.cos_zero]
  · intro θ φ
    rw [V_zero]
    exact V0_zero_nonneg θ φ

/-- At `s = 1`, the modified potential vanishes at `(θ, φ) = (0, 0)` and is nonnegative at every
angular pair. -/
theorem V_one_global_min :
    V 0 0 1 = 0 ∧ ∀ θ φ : ℝ, 0 ≤ V θ φ 1 := by
  constructor
  · rw [V_one]
    norm_num [V0, Real.cos_zero]
  · intro θ φ
    rw [V_one]
    exact V0_one_nonneg θ φ

/-- For `θ ∈ [0, π]` and `s ∈ [0, 1]`, setting `φ = 0` minimizes the straight-path potential
over all real `φ`. See [FarhiGoldstoneGutmann2002a]. -/
theorem V0_phi_le (θ φ s : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (_hs0 : 0 ≤ s) (hs1 : s ≤ 1) : V0 θ 0 s ≤ V0 θ φ s := by
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ
  have hcos : Real.cos φ ≤ 1 := Real.cos_le_one φ
  have hcoef : 0 ≤ 2 * (1 - s) := by linarith
  have h1c : 0 ≤ 1 - Real.cos φ := by linarith
  have hdiff : V0 θ φ s - V0 θ 0 s =
      2 * (1 - s) * Real.sin θ * (1 - Real.cos φ) := by
    unfold V0
    rw [Real.cos_zero]
    ring
  have hnonneg : 0 ≤ 2 * (1 - s) * Real.sin θ * (1 - Real.cos φ) :=
    mul_nonneg (mul_nonneg hcoef hsin) h1c
  linarith

/-- The straight-path potential at `(θ, φ, s) = (π, 0, 1)` equals `4 / 3`. -/
theorem V0_one_pi : V0 Real.pi 0 1 = 4 / 3 := by
  rw [V0_one, Real.cos_pi]
  norm_num

/-- Factors the endpoint cubic potential minus `4 / 3` as `(x + 1) ^ 2 * (5 - 7 * x) / 6`. -/
theorem V0_one_sub_four_thirds (x : ℝ) :
    (1 / 6) * (13 + 3 * x - 9 * x ^ 2 - 7 * x ^ 3) - 4 / 3 =
      (1 / 6) * (x + 1) ^ 2 * (5 - 7 * x) := by
  ring

/-- For `θ ∈ [2 * π / 3, π]`, the final straight-path potential at `π` is no larger than its
value at `θ`. -/
theorem V0_one_pi_le_left (θ : ℝ) (hθ2 : 2 * Real.pi / 3 ≤ θ) (hθπ : θ ≤ Real.pi) :
    V0 Real.pi 0 1 ≤ V0 θ 0 1 := by
  have hcosle : Real.cos θ ≤ -(1 / 2 : ℝ) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := 2 * Real.pi / 3) (y := θ)
      (by positivity) hθπ hθ2
    have h2 : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
      have he : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
      rw [he, Real.cos_pi_sub, Real.cos_pi_div_three]
    rwa [h2] at h
  have hfac := V0_one_sub_four_thirds (Real.cos θ)
  have hsq : (0 : ℝ) ≤ (Real.cos θ + 1) ^ 2 := sq_nonneg _
  have hpos : (0 : ℝ) ≤ 5 - 7 * Real.cos θ := by linarith
  have hprod : (0 : ℝ) ≤ (1 / 6) * (Real.cos θ + 1) ^ 2 * (5 - 7 * Real.cos θ) := by
    positivity
  rw [V0_one_pi, V0_one]
  linarith

/-- Collects the final straight-path values at `θ = π` and `θ = 0`, minimality at `π` on `[2 * π
/ 3, π]`, and global nonnegativity. See [FarhiGoldstoneGutmann2002a]. -/
theorem straight_path_static_bounds :
    V0 Real.pi 0 1 = 4 / 3 ∧ V0 0 0 1 = 0 ∧
      (∀ θ : ℝ, 2 * Real.pi / 3 ≤ θ → θ ≤ Real.pi →
        V0 Real.pi 0 1 ≤ V0 θ 0 1) ∧
      (∀ θ φ : ℝ, 0 ≤ V0 θ φ 1) := by
  refine ⟨V0_one_pi, ?_, V0_one_pi_le_left, ?_⟩
  · rw [V0_one, Real.cos_zero]
    norm_num
  · intro θ φ
    exact V0_one_nonneg θ φ

/-- The problem energy is zero at weight zero and nonnegative at every integer weight from zero
through `n`. -/
theorem hp_ground_energy_zero (n : ℕ) :
    hpEnergy (n : ℝ) 0 = 0 ∧
      ∀ k : Fin (n + 1), 0 ≤ hpEnergy (n : ℝ) (k.val : ℝ) := by
  constructor
  · exact hpEnergy_zero (n : ℝ)
  · intro k
    exact hpEnergy_nonneg_nat (Nat.le_of_lt_succ k.isLt)

/-- The all-false bit string has zero cost, and every bit string has nonnegative cost. -/
theorem cost_ground_min (n : ℕ) :
    cost n (fun _ => false) = 0 ∧ ∀ z : Fin n → Bool, 0 ≤ cost n z :=
  cost_all_zero_is_global_min n

/-- The compact angular rectangle `[0, π] × [0, 2 * π]` used to minimize the effective
potential. -/
def Vdomain : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)

/-- The angular domain `Vdomain` is compact. -/
theorem Vdomain_compact : IsCompact Vdomain := isCompact_Icc.prod isCompact_Icc

/-- The angular domain `Vdomain` contains at least one point. -/
theorem Vdomain_nonempty : Vdomain.Nonempty :=
  ⟨⟨0, 0⟩, ⟨⟨le_refl 0, Real.pi_pos.le⟩, ⟨le_refl 0, by positivity⟩⟩⟩

/-- The modified effective potential is jointly continuous in both angles and the interpolation
parameter. -/
theorem V_continuous :
    Continuous (fun p : ℝ × ℝ × ℝ => V p.1 p.2.1 p.2.2) := by
  unfold V V0 VE
  fun_prop

/-- For each fixed interpolation parameter, the modified effective potential is continuous in
the angular pair. -/
theorem V_continuous_fixed (s : ℝ) : Continuous (fun p : ℝ × ℝ => V p.1 p.2 s) := by
  unfold V V0 VE
  fun_prop

/-- For every real `s`, the modified effective potential attains a minimum on `Vdomain`. -/
theorem V_exists_min (s : ℝ) :
    ∃ p ∈ Vdomain, ∀ q ∈ Vdomain, V p.1 p.2 s ≤ V q.1 q.2 s :=
  Vdomain_compact.exists_isMinOn Vdomain_nonempty (V_continuous_fixed s).continuousOn

/-- The minimum value of the modified effective potential on `Vdomain`, defined using a chosen
minimizer. -/
noncomputable def vMin (s : ℝ) : ℝ :=
  V (Classical.choose (V_exists_min s)).1 (Classical.choose (V_exists_min s)).2 s

/-- The minimum value `vMin s` is no larger than the potential at any point of `Vdomain`. -/
theorem vMin_le (s : ℝ) {q : ℝ × ℝ} (hq : q ∈ Vdomain) :
    vMin s ≤ V q.1 q.2 s :=
  (Classical.choose_spec (V_exists_min s)).2 q hq

/-- Unfolds `vMin` as the potential evaluated at the minimizer selected from `V_exists_min`. -/
theorem vMin_eq_chosen (s : ℝ) :
    vMin s = V (Classical.choose (V_exists_min s)).1
      (Classical.choose (V_exists_min s)).2 s := rfl

/-- The minimum value `vMin` is continuous on the interpolation interval `[0, 1]`. -/
theorem vMin_continuousOn : ContinuousOn vMin (Set.Icc (0 : ℝ) 1) := by
  rw [Metric.continuousOn_iff]
  intro s₀ hs₀ ε hε
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Vdomain) := isCompact_Icc.prod Vdomain_compact
  have hFcont : Continuous (fun p : ℝ × (ℝ × ℝ) => V p.2.1 p.2.2 p.1) := by
    unfold V V0 VE
    fun_prop
  have huc : UniformContinuousOn (fun p : ℝ × (ℝ × ℝ) => V p.2.1 p.2.2 p.1)
      (Set.Icc (0 : ℝ) 1 ×ˢ Vdomain) :=
    hK.uniformContinuousOn_of_continuous hFcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ0, hδ⟩ := huc ε hε
  refine ⟨δ, hδ0, fun s hs hdist => ?_⟩
  let p := Classical.choose (V_exists_min s)
  have hp : p ∈ Vdomain ∧ ∀ q ∈ Vdomain, V p.1 p.2 s ≤ V q.1 q.2 s :=
    Classical.choose_spec (V_exists_min s)
  let q := Classical.choose (V_exists_min s₀)
  have hq : q ∈ Vdomain ∧ ∀ r ∈ Vdomain, V q.1 q.2 s₀ ≤ V r.1 r.2 s₀ :=
    Classical.choose_spec (V_exists_min s₀)
  have hpS : (s, p) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Vdomain := ⟨hs, hp.1⟩
  have hpS₀ : (s₀, p) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Vdomain := ⟨hs₀, hp.1⟩
  have hqS : (s, q) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Vdomain := ⟨hs, hq.1⟩
  have hqS₀ : (s₀, q) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Vdomain := ⟨hs₀, hq.1⟩
  have hd1 : dist ((s, p) : ℝ × (ℝ × ℝ)) (s₀, p) = dist s s₀ := by
    rw [Prod.dist_eq]; simp
  have hd2 : dist ((s, q) : ℝ × (ℝ × ℝ)) (s₀, q) = dist s s₀ := by
    rw [Prod.dist_eq]; simp
  have hb1 : dist (V p.1 p.2 s) (V p.1 p.2 s₀) < ε := by
    refine hδ (s, p) hpS (s₀, p) hpS₀ ?_
    rw [hd1]; exact hdist
  have hb2 : dist (V q.1 q.2 s₀) (V q.1 q.2 s) < ε := by
    refine hδ (s₀, q) hqS₀ (s, q) hqS ?_
    rw [dist_comm, hd2]; exact hdist
  have hvs : vMin s = V p.1 p.2 s := rfl
  have hvs₀ : vMin s₀ = V q.1 q.2 s₀ := rfl
  have hA : vMin s - vMin s₀ < ε := by
    have hmin : V p.1 p.2 s ≤ V q.1 q.2 s := hp.2 q hq.1
    have hdiff : V q.1 q.2 s - V q.1 q.2 s₀ < ε := by
      have h := hb2
      rw [Real.dist_eq] at h
      have h2 := (abs_lt.mp h).1
      linarith
    rw [hvs, hvs₀]
    linarith
  have hB : vMin s₀ - vMin s < ε := by
    have hmin : V q.1 q.2 s₀ ≤ V p.1 p.2 s₀ := hq.2 p hp.1
    have hdiff : V p.1 p.2 s₀ - V p.1 p.2 s < ε := by
      have h := hb1
      rw [Real.dist_eq] at h
      have h2 := (abs_lt.mp h).1
      linarith
    rw [hvs, hvs₀]
    linarith
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, hA⟩

/-- The minimum value of the modified effective potential at `s = 0` is zero. -/
theorem vMin_zero : vMin 0 = 0 := by
  apply le_antisymm
  · have hmem : ((Real.pi / 2, (0 : ℝ)) : ℝ × ℝ) ∈ Vdomain := by
      exact ⟨⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
        ⟨le_refl 0, by linarith [Real.pi_pos]⟩⟩
    have h := vMin_le 0 hmem
    rwa [V_zero_global_min.1] at h
  · rw [vMin_eq_chosen]
    exact V_zero_global_min.2 _ _

/-- The minimum value of the modified effective potential at `s = 1` is zero. -/
theorem vMin_one : vMin 1 = 0 := by
  apply le_antisymm
  · have hmem : ((0, (0 : ℝ)) : ℝ × ℝ) ∈ Vdomain := by
      exact ⟨⟨le_refl 0, by linarith [Real.pi_pos]⟩,
        ⟨le_refl 0, by linarith [Real.pi_pos]⟩⟩
    have h := vMin_le 1 hmem
    rwa [V_one_global_min.1] at h
  · rw [vMin_eq_chosen]
    exact V_one_global_min.2 _ _

/-- Collects continuity of the minimum value on `[0, 1]`, its zero endpoint values, and
existence of an angular minimizer for every real parameter. See
[FarhiGoldstoneGutmann2002a]. -/
theorem source_effective_potential_branch :
    ContinuousOn vMin (Set.Icc (0 : ℝ) 1) ∧ vMin 0 = 0 ∧ vMin 1 = 0 ∧
      (∀ s : ℝ, ∃ p ∈ Vdomain, ∀ q ∈ Vdomain, V p.1 p.2 s ≤ V q.1 q.2 s) :=
  ⟨vMin_continuousOn, vMin_zero, vMin_one, V_exists_min⟩

/-- Collects the endpoint minima, azimuthal identity, continuity of the minimum value,
straight-path bounds, and nonnegativity of the discrete cost and problem energies. See
[FarhiGoldstoneGutmann2002a]. -/
theorem source_effective_potential_conclusion :
    (V (Real.pi / 2) 0 0 = 0 ∧ ∀ θ φ : ℝ, 0 ≤ V θ φ 0) ∧
      (V 0 0 1 = 0 ∧ ∀ θ φ : ℝ, 0 ≤ V θ φ 1) ∧
      (∀ θ φ s : ℝ,
        V θ φ s =
          2 * (1 - s) +
            (s / 6) * (13 + 3 * Real.cos θ - 9 * Real.cos θ ^ 2 - 7 * Real.cos θ ^ 3) -
            (2 * (1 - s) * Real.sin θ + 8 * s * (1 - s) * Real.cos θ * Real.sin θ) *
              Real.cos φ) ∧
      (ContinuousOn vMin (Set.Icc (0 : ℝ) 1) ∧ vMin 0 = 0 ∧ vMin 1 = 0 ∧
        ∀ s : ℝ, ∃ p ∈ Vdomain, ∀ q ∈ Vdomain, V p.1 p.2 s ≤ V q.1 q.2 s) ∧
      (∀ θ φ s : ℝ, 0 ≤ θ → θ ≤ Real.pi → 0 ≤ s → s ≤ 1 → V0 θ 0 s ≤ V0 θ φ s) ∧
      (V0 Real.pi 0 1 = 4 / 3 ∧ V0 0 0 1 = 0 ∧
        ∀ θ : ℝ, 2 * Real.pi / 3 ≤ θ → θ ≤ Real.pi → V0 Real.pi 0 1 ≤ V0 θ 0 1) ∧
      (∀ n : ℕ, cost n (fun _ => false) = 0 ∧ ∀ z : Fin n → Bool, 0 ≤ cost n z) ∧
      (∀ n : ℕ, hpEnergy (n : ℝ) 0 = 0 ∧
        ∀ k : Fin (n + 1), 0 ≤ hpEnergy (n : ℝ) (k.val : ℝ)) :=
  ⟨V_zero_global_min, V_one_global_min, V_phi_linear,
    source_effective_potential_branch, V0_phi_le,
    ⟨V0_one_pi, by rw [V0_one, Real.cos_zero]; norm_num, V0_one_pi_le_left⟩,
    cost_ground_min, hp_ground_energy_zero⟩

end Qatlib.Papers.AdiabaticPath02.MainResults.EffectivePotential
