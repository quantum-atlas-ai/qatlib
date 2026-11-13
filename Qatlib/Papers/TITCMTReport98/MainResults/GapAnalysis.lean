/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TITCMTReport98.MainResults.PhysicalEvolution
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

/-!
# Two-level gap and quasistatic deficiency

This module analyzes an explicit real two-level Hamiltonian and the gap-dependent weight
expressions used in [KadowakiNishimori1998]. It verifies a ground-energy equation, identifies
the corresponding overlap weight when the coupling is nonzero, and studies the small-coupling
deficiency.

The finite-sum expression `quasistaticDeficiency` records squared couplings divided by squared
energy differences. Its square-root schedule scales exactly as inverse time.

## Main statements

* `twoLevel_ground_eigen`: verifies the ground-energy equation for the explicit vector.
* `twoLevel_excited_equiv`: gives the quadratic small-coupling equivalent for positive diagonal
  gap.
* `twoLevel_schedule_deficiency_tendsto`: gives the rescaled large-time limit.
* `quasistaticDeficiency_schedule`: computes the deficiency along `c / √t`.

## References

* [Kadowaki and Nishimori, 1998][KadowakiNishimori1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TITCMTReport98.MainResults

open Filter Matrix
open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real symmetric two-level matrix with diagonal energies `E0`, `E1` and off-diagonal
entries `-g`. -/
def twoLevelHamiltonian (E0 E1 g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![E0, -g; -g, E1]

/-- The difference `E1 - E0` between the diagonal energies. -/
def twoLevelGap (E0 E1 : ℝ) : ℝ := E1 - E0

/-- The square-root discriminant `√((E1 - E0) ^ 2 + 4 * g ^ 2)`. -/
def twoLevelDisc (E0 E1 g : ℝ) : ℝ :=
  Real.sqrt ((E1 - E0) ^ 2 + 4 * g ^ 2)

/-- The lower eigenvalue expression `(E0 + E1 - twoLevelDisc E0 E1 g) / 2`. -/
def twoLevelGroundEnergy (E0 E1 g : ℝ) : ℝ :=
  (E0 + E1 - twoLevelDisc E0 E1 g) / 2

/-- The vector with coordinates `g` and `(twoLevelDisc E0 E1 g - (E1 - E0)) / 2` used in the
ground-energy equation. -/
def twoLevelGroundVec (E0 E1 g : ℝ) : Fin 2 → ℝ :=
  ![g, (twoLevelDisc E0 E1 g - (E1 - E0)) / 2]

/-- The ground-overlap weight expression `(D + (E1 - E0)) / (2D)`, where `D = twoLevelDisc E0 E1
g`. -/
def twoLevelGroundWeight (E0 E1 g : ℝ) : ℝ :=
  (twoLevelDisc E0 E1 g + (E1 - E0)) / (2 * twoLevelDisc E0 E1 g)

/-- The complementary weight expression `2 * g ^ 2 / (D * (D + (E1 - E0)))`, where `D =
twoLevelDisc E0 E1 g`. -/
def twoLevelExcitedWeight (E0 E1 g : ℝ) : ℝ :=
  2 * g ^ 2 / (twoLevelDisc E0 E1 g * (twoLevelDisc E0 E1 g + (E1 - E0)))

/-- A positive diagonal energy gap makes the discriminant strictly positive. -/
theorem twoLevelDisc_pos (E0 E1 g : ℝ) (hgap : 0 < E1 - E0) :
    0 < twoLevelDisc E0 E1 g := by
  unfold twoLevelDisc
  apply Real.sqrt_pos.mpr
  have : 0 < (E1 - E0) ^ 2 := by positivity
  nlinarith [sq_nonneg g]

/-- The squared discriminant equals `(E1 - E0) ^ 2 + 4 * g ^ 2`. -/
theorem twoLevelDisc_sq (E0 E1 g : ℝ) :
    twoLevelDisc E0 E1 g ^ 2 = (E1 - E0) ^ 2 + 4 * g ^ 2 := by
  unfold twoLevelDisc
  exact Real.sq_sqrt (by positivity)

/-- For a positive diagonal energy gap, the explicit ground vector satisfies the eigenvalue
equation with `twoLevelGroundEnergy` [KadowakiNishimori1998]. -/
theorem twoLevel_ground_eigen (E0 E1 g : ℝ) (_hgap : 0 < E1 - E0) :
    twoLevelHamiltonian E0 E1 g *ᵥ twoLevelGroundVec E0 E1 g
      = twoLevelGroundEnergy E0 E1 g • twoLevelGroundVec E0 E1 g := by
  have hs2 := twoLevelDisc_sq E0 E1 g
  ext i
  fin_cases i <;>
    simp [twoLevelHamiltonian, twoLevelGroundVec, twoLevelGroundEnergy,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · field_simp
    ring_nf
  · field_simp
    ring_nf
    nlinarith [hs2]

/-- For a positive diagonal gap and nonzero coupling, the ground weight equals the squared first
coordinate divided by the squared norm of the explicit real ground vector
[KadowakiNishimori1998]. -/
theorem twoLevelGroundWeight_eq_overlap (E0 E1 g : ℝ) (hgap : 0 < E1 - E0)
    (hg : g ≠ 0) :
    twoLevelGroundWeight E0 E1 g
      = g ^ 2 / (g ^ 2 + (twoLevelGroundVec E0 E1 g 1) ^ 2) := by
  have hs2 := twoLevelDisc_sq E0 E1 g
  have hs := twoLevelDisc_pos E0 E1 g hgap
  have hd : 0 < E1 - E0 := hgap
  have hgsq : 0 < g ^ 2 := sq_pos_of_ne_zero hg
  have hgt : (E1 - E0) ^ 2 < twoLevelDisc E0 E1 g ^ 2 := by
    rw [hs2]; nlinarith
  have hsd : 0 < twoLevelDisc E0 E1 g - (E1 - E0) := by
    have hlt : E1 - E0 < twoLevelDisc E0 E1 g := by nlinarith [hs, hgt, hd]
    linarith
  have hsne : twoLevelDisc E0 E1 g ≠ 0 := hs.ne'
  have hsdne : twoLevelDisc E0 E1 g - (E1 - E0) ≠ 0 := hsd.ne'
  unfold twoLevelGroundWeight twoLevelGroundVec
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hden : g ^ 2 + ((twoLevelDisc E0 E1 g - (E1 - E0)) / 2) ^ 2
      = twoLevelDisc E0 E1 g * (twoLevelDisc E0 E1 g - (E1 - E0)) / 2 := by
    field_simp
    nlinarith [hs2]
  rw [hden]
  field_simp
  nlinarith [hs2]

/-- For a positive diagonal energy gap, the ground and excited weight expressions sum to one
[KadowakiNishimori1998]. -/
theorem twoLevelGroundWeight_add_excited (E0 E1 g : ℝ) (hgap : 0 < E1 - E0) :
    twoLevelGroundWeight E0 E1 g + twoLevelExcitedWeight E0 E1 g = 1 := by
  have hs2 := twoLevelDisc_sq E0 E1 g
  have hs := (twoLevelDisc_pos E0 E1 g hgap).ne'
  have hd : 0 < E1 - E0 := hgap
  have hsd : twoLevelDisc E0 E1 g + (E1 - E0) ≠ 0 := by
    have hsp := twoLevelDisc_pos E0 E1 g hgap
    linarith
  unfold twoLevelGroundWeight twoLevelExcitedWeight
  field_simp
  ring_nf
  nlinarith [hs2]

/-- For a positive diagonal energy gap, the excited weight equals one minus the ground weight
[KadowakiNishimori1998]. -/
theorem twoLevel_excited_eq_one_sub (E0 E1 g : ℝ) (hgap : 0 < E1 - E0) :
    1 - twoLevelGroundWeight E0 E1 g = twoLevelExcitedWeight E0 E1 g := by
  have h := twoLevelGroundWeight_add_excited E0 E1 g hgap
  linarith

/-- For a positive diagonal gap, the excited weight is asymptotically equivalent to `g ^ 2 / (E1
- E0) ^ 2` as `g` tends to zero through nonzero values [KadowakiNishimori1998]. -/
theorem twoLevel_excited_equiv (E0 E1 : ℝ) (hgap : 0 < E1 - E0) :
    Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
      (fun g : ℝ => twoLevelExcitedWeight E0 E1 g)
      (fun g : ℝ => g ^ 2 / (E1 - E0) ^ 2) := by
  have hne : ∀ᶠ g : ℝ in 𝓝[≠] (0 : ℝ), g ^ 2 / (E1 - E0) ^ 2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with g hg
    have hd : (E1 - E0) ^ 2 ≠ 0 := by positivity
    exact div_ne_zero (pow_ne_zero 2 hg) hd
  rw [Asymptotics.isEquivalent_iff_tendsto_one hne]
  have hs : Tendsto (fun g : ℝ => twoLevelDisc E0 E1 g) (𝓝 0) (𝓝 (E1 - E0)) := by
    have hcont : Continuous (fun x : ℝ => Real.sqrt ((E1 - E0) ^ 2 + 4 * x ^ 2)) := by
      fun_prop
    have h0 := hcont.tendsto 0
    have hval : Real.sqrt ((E1 - E0) ^ 2 + 4 * (0 : ℝ) ^ 2) = E1 - E0 := by
      rw [show (E1 - E0) ^ 2 + 4 * (0 : ℝ) ^ 2 = (E1 - E0) ^ 2 by ring]
      exact Real.sqrt_sq hgap.le
    rw [hval] at h0
    simpa [twoLevelDisc] using! h0
  have hd : E1 - E0 ≠ 0 := hgap.ne'
  have hdisc0 : 0 < twoLevelDisc E0 E1 0 := twoLevelDisc_pos E0 E1 0 hgap

  have heq : (fun g : ℝ => twoLevelExcitedWeight E0 E1 g / (g ^ 2 / (E1 - E0) ^ 2))
      =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun g : ℝ => 2 * (E1 - E0) ^ 2
        / (twoLevelDisc E0 E1 g * (twoLevelDisc E0 E1 g + (E1 - E0)))) := by
    filter_upwards [self_mem_nhdsWithin] with g hg
    have hsne : twoLevelDisc E0 E1 g ≠ 0 :=
      (twoLevelDisc_pos E0 E1 g hgap).ne'
    have hsdne : twoLevelDisc E0 E1 g + (E1 - E0) ≠ 0 := by
      have hsp := twoLevelDisc_pos E0 E1 g hgap
      linarith
    have hdne : (E1 - E0) ^ 2 ≠ 0 := by positivity
    have hg0 : g ≠ 0 := by simpa using! hg
    unfold twoLevelExcitedWeight
    field_simp [hg0]
  have hlim0 : Tendsto
      (fun g : ℝ => 2 * (E1 - E0) ^ 2
        / (twoLevelDisc E0 E1 g * (twoLevelDisc E0 E1 g + (E1 - E0))))
      (𝓝 0) (𝓝 1) := by
    have hden : Tendsto
        (fun g : ℝ => twoLevelDisc E0 E1 g * (twoLevelDisc E0 E1 g + (E1 - E0)))
        (𝓝 0) (𝓝 ((E1 - E0) * ((E1 - E0) + (E1 - E0)))) :=
      hs.mul (hs.add tendsto_const_nhds)
    have hdenne : ((E1 - E0) * ((E1 - E0) + (E1 - E0))) ≠ 0 := by
      have : 0 < (E1 - E0) * ((E1 - E0) + (E1 - E0)) := by positivity
      exact this.ne'
    have h := (tendsto_const_nhds (x := 2 * (E1 - E0) ^ 2)).div hden hdenne
    have hv : 2 * (E1 - E0) ^ 2 / ((E1 - E0) * ((E1 - E0) + (E1 - E0))) = 1 := by
      field_simp
      ring
    rwa [hv] at h
  have hlim : Tendsto
      (fun g : ℝ => 2 * (E1 - E0) ^ 2
        / (twoLevelDisc E0 E1 g * (twoLevelDisc E0 E1 g + (E1 - E0))))
      (𝓝[≠] (0 : ℝ)) (𝓝 1) :=
    hlim0.mono_left nhdsWithin_le_nhds
  exact Tendsto.congr' heq.symm hlim

/-- For a positive diagonal gap, `t` times the excited weight at coupling `c / √t` tends to `c ^
2 / (E1 - E0) ^ 2` as `t` tends to infinity [KadowakiNishimori1998]. -/
theorem twoLevel_schedule_deficiency_tendsto (E0 E1 c : ℝ) (hgap : 0 < E1 - E0) :
    Tendsto (fun t : ℝ => t * twoLevelExcitedWeight E0 E1 (c / Real.sqrt t))
      atTop (𝓝 (c ^ 2 / (E1 - E0) ^ 2)) := by
  have hg : Tendsto (fun t : ℝ => c / Real.sqrt t) atTop (𝓝 0) := by
    simpa using! Tendsto.const_div_atTop Real.tendsto_sqrt_atTop c
  have hs : Tendsto (fun t : ℝ => twoLevelDisc E0 E1 (c / Real.sqrt t))
      atTop (𝓝 (E1 - E0)) := by
    have hcont : Continuous (fun x : ℝ => Real.sqrt ((E1 - E0) ^ 2 + 4 * x ^ 2)) := by
      fun_prop
    have h0 := hcont.tendsto 0
    have hval : Real.sqrt ((E1 - E0) ^ 2 + 4 * (0 : ℝ) ^ 2) = E1 - E0 := by
      rw [show (E1 - E0) ^ 2 + 4 * (0 : ℝ) ^ 2 = (E1 - E0) ^ 2 by ring]
      exact Real.sqrt_sq hgap.le
    rw [hval] at h0
    simpa [twoLevelDisc] using! h0.comp hg
  have hlim0 : Tendsto
      (fun t : ℝ => 2 * c ^ 2
        / (twoLevelDisc E0 E1 (c / Real.sqrt t)
            * (twoLevelDisc E0 E1 (c / Real.sqrt t) + (E1 - E0))))
      atTop (𝓝 (c ^ 2 / (E1 - E0) ^ 2)) := by
    have hden : Tendsto
        (fun t : ℝ => twoLevelDisc E0 E1 (c / Real.sqrt t)
            * (twoLevelDisc E0 E1 (c / Real.sqrt t) + (E1 - E0)))
        atTop (𝓝 ((E1 - E0) * ((E1 - E0) + (E1 - E0)))) :=
      hs.mul (hs.add tendsto_const_nhds)
    have hdenne : ((E1 - E0) * ((E1 - E0) + (E1 - E0))) ≠ 0 := by
      have : 0 < (E1 - E0) * ((E1 - E0) + (E1 - E0)) := by positivity
      exact this.ne'
    have h := (tendsto_const_nhds (x := 2 * c ^ 2)).div hden hdenne
    have hv : 2 * c ^ 2 / ((E1 - E0) * ((E1 - E0) + (E1 - E0)))
        = c ^ 2 / (E1 - E0) ^ 2 := by
      field_simp
      ring
    rwa [hv] at h
  have heq : (fun t : ℝ => t * twoLevelExcitedWeight E0 E1 (c / Real.sqrt t))
      =ᶠ[atTop]
      (fun t : ℝ => 2 * c ^ 2
        / (twoLevelDisc E0 E1 (c / Real.sqrt t)
            * (twoLevelDisc E0 E1 (c / Real.sqrt t) + (E1 - E0)))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hgsq : (c / Real.sqrt t) ^ 2 = c ^ 2 / t := by
      rw [div_pow, Real.sq_sqrt ht.le]
    have hsne : twoLevelDisc E0 E1 (c / Real.sqrt t) ≠ 0 :=
      (twoLevelDisc_pos E0 E1 _ hgap).ne'
    have hsdne : twoLevelDisc E0 E1 (c / Real.sqrt t) + (E1 - E0) ≠ 0 := by
      have hsp := twoLevelDisc_pos E0 E1 (c / Real.sqrt t) hgap
      linarith
    unfold twoLevelExcitedWeight
    rw [hgsq]
    field_simp
  exact Tendsto.congr' heq.symm hlim0

/-- The finite sum `Γ ^ 2 * ∑ i ≠ g, (V i) ^ 2 / (E g - E i) ^ 2` defining the quasistatic
deficiency expression. -/
def quasistaticDeficiency {κ : Type*} [Fintype κ] [DecidableEq κ]
    (E : κ → ℝ) (V : κ → ℝ) (g : κ) (Γ : ℝ) : ℝ :=
  Γ ^ 2 * ∑ i ∈ Finset.univ.erase g, (V i) ^ 2 / (E g - E i) ^ 2

/-- The quasistatic deficiency expression is nonnegative [KadowakiNishimori1998]. -/
theorem quasistaticDeficiency_nonneg {κ : Type*} [Fintype κ] [DecidableEq κ]
    (E : κ → ℝ) (V : κ → ℝ) (g : κ) (Γ : ℝ) :
    0 ≤ quasistaticDeficiency E V g Γ := by
  unfold quasistaticDeficiency
  have hterm : 0 ≤ ∑ i ∈ Finset.univ.erase g, (V i) ^ 2 / (E g - E i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
  exact mul_nonneg (sq_nonneg _) hterm

/-- At coupling `c / √t` with `t > 0`, the quasistatic deficiency equals `1 / t` times the sum
of squared ratios `c * V i / (E g - E i)` over `i ≠ g` [KadowakiNishimori1998]. -/
theorem quasistaticDeficiency_schedule {κ : Type*} [Fintype κ] [DecidableEq κ]
    (E : κ → ℝ) (V : κ → ℝ) (g : κ) (c t : ℝ) (ht : 0 < t) :
    quasistaticDeficiency E V g (c / Real.sqrt t)
      = (1 / t) * ∑ i ∈ Finset.univ.erase g, (c * V i / (E g - E i)) ^ 2 := by
  have hsqrt : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have htne : t ≠ 0 := ht.ne'
  unfold quasistaticDeficiency
  rw [div_pow, Real.sq_sqrt ht.le]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

/-- For two levels with energies zero and nonzero `d` and unit couplings, the quasistatic
deficiency at level zero equals `Γ ^ 2 / d ^ 2` [KadowakiNishimori1998]. -/
theorem twoLevelQuasistatic_eq (d Γ : ℝ) (hd : d ≠ 0) :
    quasistaticDeficiency (fun i : Fin 2 => (![0, d] : Fin 2 → ℝ) i)
      (fun _ : Fin 2 => 1) 0 Γ = Γ ^ 2 / d ^ 2 := by
  unfold quasistaticDeficiency
  have herase : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  rw [herase, Finset.sum_singleton]
  simp
  field_simp

end Qatlib.Papers.TITCMTReport98.MainResults
