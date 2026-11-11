/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WaterLevel.WaterPrecision.CoherentReweightingDefs
import Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel

/-!
# Endpoint fidelities for real water fills

This module proves a source-box overlap comparison and identifies real water-fill fidelities at
bracket endpoints under the stated positivity, normalization, and support assumptions. It also
handles zero mass and gives `gext1_endpoint_conjunct_refutable`, showing that the displayed
endpoint package does not follow from `ClosedBracket` alone, in the setting of
[OzolsRoettelerRoland2013].

## Main statements

* `realFidelity_bracket_low`: Identify the lower endpoint fidelity when its mass is positive.
* `realFidelity_bracket_high`: Identify the upper endpoint fidelity under the support condition.

## References

* [Ozols et al., 2013][OzolsRoettelerRoland2013]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Matrix
open Qatlib
open Qatlib.Concepts.Waterfill.ExactResampling
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WaterLevel.WaterPrecision
open scoped BigOperators ComplexOrder

open Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel

namespace Qatlib.Concepts.Waterfill.LevelFidelity
variable {m : ℕ} (π σ : Fin m → ℝ)
variable {m : ℕ} (π σ : Fin m → ℚ)

/-- A vector in `SourceBox π` whose squared norm is at most `realMass π σ γ` has target overlap
at most `realDot π σ γ`, for a positive level and nonnegative source and target. -/
theorem real_overlap_le {m : ℕ} (π σ : Fin m → ℝ) (_hπ : ∀ i, 0 ≤ π i) (_hσ : ∀ i, 0 ≤ σ i)
    {γ : ℝ} (hγ : 0 < γ) (v : Fin m → ℝ) (hv : SourceBox π v)
    (he : (∑ i, v i ^ 2) ≤ realMass π σ γ) :
    (∑ i, σ i * v i) ≤ realDot π σ γ := by
  have hi (j : Fin m) :
      2 * γ * (σ j * v j - σ j * realFill π σ γ j) ≤ v j ^ 2 - realFill π σ γ j ^ 2 := by
    by_cases hs : π j ≤ γ * σ j
    · rw [show realFill π σ γ j = π j from min_eq_left hs]
      nlinarith [mul_nonneg (sub_nonneg.mpr (hv j).2)
        (show (0 : ℝ) ≤ 2 * γ * σ j - π j - v j by nlinarith [(hv j).2, _hσ j])]
    · rw [show realFill π σ γ j = γ * σ j from min_eq_right (le_of_not_ge hs)]
      nlinarith [sq_nonneg (v j - γ * σ j)]
  have hh := Finset.sum_le_sum (s := Finset.univ) fun j _ => hi j
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hh
  have hmass : (∑ j, v j ^ 2) ≤ ∑ j, realFill π σ γ j ^ 2 := he
  unfold realDot
  nlinarith

/-- At a nonnegative lower bracket endpoint with positive mass, `realFidelity` equals `realPmax`
for nonnegative source and target. -/
theorem realFidelity_bracket_low {m : ℕ} (π σ : Fin m → ℝ) (hπ : ∀ i, 0 ≤ π i)
    (hσ : ∀ i, 0 ≤ σ i) {γlo : ℝ} (hγlo : 0 ≤ γlo) (hlow : BracketLow π σ γlo)
    (hmass : 0 < realMass π σ γlo) :
    realFidelity π σ γlo = realPmax π σ := by
  have hfill : ∀ i, realFill π σ γlo i = if 0 < π i then γlo * σ i else 0 := by
    intro i
    by_cases hpi : 0 < π i
    · rw [if_pos hpi]
      exact min_eq_right (hlow i hpi)
    · rw [if_neg hpi]
      have hπi : π i = 0 := le_antisymm (le_of_not_gt hpi) (hπ i)
      have : realFill π σ γlo i = min (π i) (γlo * σ i) := rfl
      rw [this, hπi, min_eq_left (mul_nonneg hγlo (hσ i))]
  have hdot : realDot π σ γlo = γlo * realPmax π σ := by
    unfold realDot realPmax
    have per : ∀ i, σ i * realFill π σ γlo i = γlo * (if 0 < π i then σ i ^ 2 else 0) := by
      intro i
      rw [hfill i]
      split_ifs with hpi
      · ring
      · ring
    rw [show (∑ i, σ i * realFill π σ γlo i)
        = ∑ i, γlo * (if 0 < π i then σ i ^ 2 else 0) from
      Finset.sum_congr rfl fun i _ => per i, Finset.mul_sum]
  have hmassE : realMass π σ γlo = γlo ^ 2 * realPmax π σ := by
    unfold realMass realPmax
    have per : ∀ i, realFill π σ γlo i ^ 2 = γlo ^ 2 * (if 0 < π i then σ i ^ 2 else 0) := by
      intro i
      rw [hfill i]
      split_ifs with hpi
      · ring
      · ring
    rw [show (∑ i, realFill π σ γlo i ^ 2)
        = ∑ i, γlo ^ 2 * (if 0 < π i then σ i ^ 2 else 0) from
      Finset.sum_congr rfl fun i _ => per i, Finset.mul_sum]
  have hpmax : 0 < realPmax π σ := by
    by_contra hn
    have hz : realPmax π σ = 0 := le_antisymm (le_of_not_gt hn) (by
      unfold realPmax
      exact Finset.sum_nonneg fun i _ => by split_ifs <;> [exact sq_nonneg _; exact le_rfl])
    rw [hz, mul_zero] at hmassE
    exact absurd hmassE (ne_of_gt hmass)
  have hγ : γlo ≠ 0 := by
    intro h
    have hz : realMass π σ γlo = 0 := by
      rw [hmassE, h, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul]
    exact absurd hz (ne_of_gt hmass)
  unfold realFidelity
  rw [if_neg (ne_of_gt hmass), hmassE, hdot]
  field_simp [ne_of_gt hpmax, hγ, ne_of_gt hmass]

/-- At an upper bracket endpoint, `realFidelity` equals `realPmin` when the source has squared
norm one and vanishes wherever the nonnegative target vanishes. -/
theorem realFidelity_bracket_high {m : ℕ} (π σ : Fin m → ℝ) (_hπ : ∀ i, 0 ≤ π i)
    (hσ : ∀ i, 0 ≤ σ i) (hπ1 : (∑ i, π i ^ 2) = 1)
    {γhi : ℝ} (hhigh : BracketHigh π σ γhi) (hsupp : ∀ i, σ i = 0 → π i = 0) :
    realFidelity π σ γhi = realPmin π σ := by
  have hfill : ∀ i, realFill π σ γhi i = π i := by
    intro i
    by_cases hs : 0 < σ i
    · exact min_eq_left (hhigh i hs)
    · have hz : σ i = 0 := le_antisymm (le_of_not_gt hs) (hσ i)
      have hπz : π i = 0 := hsupp i hz
      have : realFill π σ γhi i = min (π i) (γhi * σ i) := rfl
      rw [this, hz, mul_zero, hπz, min_eq_right le_rfl]
  have hmass : realMass π σ γhi = 1 := by
    unfold realMass
    rw [show (∑ i, realFill π σ γhi i ^ 2) = ∑ i, π i ^ 2 from
      Finset.sum_congr rfl fun i _ => by rw [hfill i]]
    exact hπ1
  have hdot : realDot π σ γhi = ∑ i, π i * σ i := by
    unfold realDot
    exact Finset.sum_congr rfl fun i _ => by rw [hfill i, mul_comm]
  unfold realFidelity realPmin
  rw [hmass, hdot]
  norm_num

/-- If the mass at the upper endpoint is zero, both mass and target overlap vanish at every
nonnegative level below that endpoint. -/
theorem realMass_zero_boundary {m : ℕ} (π σ : Fin m → ℝ) (hπ : ∀ i, 0 ≤ π i)
    (hσ : ∀ i, 0 ≤ σ i) {γlo γhi : ℝ} (_hbr : ClosedBracket π σ γlo γhi)
    (hmass : realMass π σ γhi = 0) :
    ∀ γ, 0 ≤ γ → γ ≤ γhi → realMass π σ γ = 0 ∧ realDot π σ γ = 0 := by
  intro γ hγ0 hγhi
  have hmono : realMass π σ γ ≤ realMass π σ γhi := realMass_mono π σ hπ hσ hγ0 hγhi
  have hz : realMass π σ γ = 0 :=
    le_antisymm (by linarith) (realMass_nonneg π σ γ)
  refine ⟨hz, ?_⟩
  have hper : ∀ j, realFill π σ γ j = 0 := by
    intro j
    have hle : realFill π σ γ j ^ 2 ≤ 0 := by
      have h1 := Finset.single_le_sum (f := fun i => realFill π σ γ i ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
      have h2 : (∑ i, realFill π σ γ i ^ 2) = 0 := by
        show realMass π σ γ = 0; exact hz
      linarith
    exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
  unfold realDot
  exact Finset.sum_eq_zero fun i _ => by rw [hper i, mul_zero]

/-- The two-coordinate source vector with entries zero and one used in the endpoint
counterexample. -/
private def gext1CounterPi : Fin 2 → ℝ := fun i => (i.val : ℝ)

/-- The two-coordinate target vector with entries one and zero used in the endpoint
counterexample. -/
private def gext1CounterSig : Fin 2 → ℝ := fun i => 1 - (i.val : ℝ)

/-- The two endpoint fidelity identities do not hold universally for normalized nonnegative
vectors under `ClosedBracket` alone. -/
theorem gext1_endpoint_conjunct_refutable :
    ¬ (∀ (m : ℕ) (π σ : Fin m → ℝ),
        (∀ i, 0 ≤ π i) → (∀ i, 0 ≤ σ i) →
        (∑ i, π i ^ 2) = 1 → (∑ i, σ i ^ 2) = 1 →
        ∀ γlo γhi, ClosedBracket π σ γlo γhi →
          (0 < realMass π σ γlo → realFidelity π σ γlo = realPmax π σ) ∧
            ((∀ i, σ i = 0 → π i = 0) → realFidelity π σ γhi = realPmin π σ)) := by
  intro h
  have hπ : ∀ i, 0 ≤ gext1CounterPi i := fun i => by
    unfold gext1CounterPi
    exact Nat.cast_nonneg _
  have hσ : ∀ i, 0 ≤ gext1CounterSig i := fun i => by
    unfold gext1CounterSig
    have hi : (i.val : ℝ) ≤ 1 := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
    linarith
  have hπ1 : (∑ i, gext1CounterPi i ^ 2) = 1 := by
    rw [Fin.sum_univ_two]
    norm_num [gext1CounterPi]
  have hσ1 : (∑ i, gext1CounterSig i ^ 2) = 1 := by
    rw [Fin.sum_univ_two]
    norm_num [gext1CounterSig]
  have hlow : BracketLow gext1CounterPi gext1CounterSig (-1) := by
    intro i _
    have hs : 0 ≤ gext1CounterSig i := hσ i
    have hp : 0 ≤ gext1CounterPi i := hπ i
    nlinarith
  have hhigh : BracketHigh gext1CounterPi gext1CounterSig 0 := by
    intro i hs
    have hne : gext1CounterPi i = 0 := by
      by_contra hn
      have hne2 : (i.val : ℝ) ≠ 0 := by simpa [gext1CounterPi] using! hn
      have hi1 : i.val = 1 := by
        have : i.val = 0 ∨ i.val = 1 := by omega
        rcases this with hh | hh
        · exact absurd (by exact_mod_cast hh : (i.val : ℝ) = 0) hne2
        · exact hh
      have hσz : gext1CounterSig i = 0 := by
        unfold gext1CounterSig
        rw [hi1]
        norm_num
      have : ¬ (0 < gext1CounterSig i) := by rw [hσz]; norm_num
      exact this hs
    show gext1CounterPi i ≤ (0 : ℝ) * gext1CounterSig i
    rw [hne, zero_mul]
  have hbr : ClosedBracket gext1CounterPi gext1CounterSig (-1) 0 :=
    ⟨by norm_num, hlow, hhigh⟩
  have hfill0 : realFill gext1CounterPi gext1CounterSig (-1) 0 = -1 := by
    norm_num [realFill, gext1CounterPi, gext1CounterSig]
  have hfill1 : realFill gext1CounterPi gext1CounterSig (-1) 1 = 0 := by
    norm_num [realFill, gext1CounterPi, gext1CounterSig]
  have hmass : 0 < realMass gext1CounterPi gext1CounterSig (-1) := by
    show 0 < (∑ i, realFill gext1CounterPi gext1CounterSig (-1) i ^ 2)
    rw [Fin.sum_univ_two, hfill0, hfill1]
    norm_num
  have hm : realMass gext1CounterPi gext1CounterSig (-1) = 1 := by
    show (∑ i, realFill gext1CounterPi gext1CounterSig (-1) i ^ 2) = 1
    rw [Fin.sum_univ_two, hfill0, hfill1]
    norm_num
  have hd : realDot gext1CounterPi gext1CounterSig (-1) = -1 := by
    show (∑ i, gext1CounterSig i * realFill gext1CounterPi gext1CounterSig (-1) i) = -1
    rw [Fin.sum_univ_two, hfill0, hfill1]
    norm_num [gext1CounterSig]
  have hfid : realFidelity gext1CounterPi gext1CounterSig (-1) = 1 := by
    unfold realFidelity
    rw [hm, if_neg (by norm_num : (1:ℝ) ≠ 0), hd]
    norm_num
  have hpmax : realPmax gext1CounterPi gext1CounterSig = 0 := by
    unfold realPmax
    rw [Fin.sum_univ_two]
    have h0 : ¬ (0 < gext1CounterPi 0) := by norm_num [gext1CounterPi]
    have h1 : (0:ℝ) < gext1CounterPi 1 := by norm_num [gext1CounterPi]
    rw [if_neg h0, if_pos h1]
    norm_num [gext1CounterSig]
  have hconj := h 2 gext1CounterPi gext1CounterSig hπ hσ hπ1 hσ1 (-1) 0 hbr
  exact absurd (hconj.1 hmass) (by
    rw [hfid, hpmax]; norm_num)
end Qatlib.Concepts.Waterfill.LevelFidelity
