/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic
import Qatlib.Papers.QWalkGraphs00.MainResults.Core

/-!
# Mixing, sampling, filling, and dispersion times

This module defines subset probabilities, total variation distance, and four time predicates for
a finite coined walk relative to a supplied reference distribution. Relative subset sampling
bounds imply the mixing, filling, and dispersion conclusions formalized in Theorem 3.12 of
[AharonovEtAl2001Walks].

## Main statements

* `avgSetProb_eq`: expresses averaged subset mass as a time average.
* `theorem_3_12`: derives all three time predicates from a positive sampling time.

## References

* [Aharonov et al., 2001][AharonovEtAl2001Walks]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkGraphs00.MainResults.Times

open scoped BigOperators Matrix Topology
open Filter
open Qatlib.Papers.QWalkGraphs00.MainResults.Core

variable {Coin V : Type*} [Fintype Coin] [Fintype V] [DecidableEq Coin] [DecidableEq V]

/-- The total vertex weight in a finite subset after `t` walk steps. -/
def setProb (U : Matrix (Coin × V) (Coin × V) ℂ) (ψ : (Coin × V) → ℂ)
    (t : ℕ) (X : Finset V) : ℝ :=
  ∑ x ∈ X, nodeProb U ψ t x

/-- The sum of the averaged vertex weights over a finite subset. -/
def avgSetProb (U : Matrix (Coin × V) (Coin × V) ℂ) (ψ : (Coin × V) → ℂ)
    (T : ℕ) (X : Finset V) : ℝ :=
  ∑ x ∈ X, avgNodeProb U ψ T x

/-- Half the ℓ¹ distance between two real functions on the vertex set. -/
def tvDistance (p q : V → ℝ) : ℝ :=
  (1 / 2) * ∑ v, |p v - q v|

/-- The condition that every averaging length at least `T` gives total variation error at most
`ε` for every input vector. -/
def IsMixingTime (U : Matrix (Coin × V) (Coin × V) ℂ)
    (π : ((Coin × V) → ℂ) → V → ℝ) (ε : ℝ) (T : ℕ) : Prop :=
  ∀ (t : ℕ), T ≤ t → ∀ ψ : (Coin × V) → ℂ,
    tvDistance (π ψ) (fun v => avgNodeProb U ψ t v) ≤ ε

/-- The condition that every averaging length at least `T` gives relative error at most `ε` on
every subset for every input vector. -/
def IsSamplingTime (U : Matrix (Coin × V) (Coin × V) ℂ)
    (π : ((Coin × V) → ℂ) → V → ℝ) (ε : ℝ) (T : ℕ) : Prop :=
  ∀ (t : ℕ), T ≤ t → ∀ (ψ : (Coin × V) → ℂ) (X : Finset V),
    |(∑ x ∈ X, π ψ x) - avgSetProb U ψ t X| ≤ ε * (∑ x ∈ X, π ψ x)

/-- The condition that every input vector and subset have some time at most `T` with subset
weight at least `(1 - ε)` times the reference mass. -/
def IsFillingTime (U : Matrix (Coin × V) (Coin × V) ℂ)
    (π : ((Coin × V) → ℂ) → V → ℝ) (ε : ℝ) (T : ℕ) : Prop :=
  ∀ (ψ : (Coin × V) → ℂ) (X : Finset V),
    ∃ t : ℕ, t ≤ T ∧ (1 - ε) * (∑ x ∈ X, π ψ x) ≤ setProb U ψ t X

/-- The condition that every input vector and subset have some time at most `T` with subset
weight at most `(1 + ε)` times the reference mass. -/
def IsDispersionTime (U : Matrix (Coin × V) (Coin × V) ℂ)
    (π : ((Coin × V) → ℂ) → V → ℝ) (ε : ℝ) (T : ℕ) : Prop :=
  ∀ (ψ : (Coin × V) → ℂ) (X : Finset V),
    ∃ t : ℕ, t ≤ T ∧ setProb U ψ t X ≤ (1 + ε) * (∑ x ∈ X, π ψ x)

/-- The averaged subset weight equals the normalized sum of instantaneous subset weights over
times less than `S`. -/
theorem avgSetProb_eq (U : Matrix (Coin × V) (Coin × V) ℂ) (ψ : (Coin × V) → ℂ)
    (S : ℕ) (X : Finset V) :
    avgSetProb U ψ S X = (S : ℝ)⁻¹ * ∑ t ∈ Finset.range S, setProb U ψ t X := by
  calc avgSetProb U ψ S X
      = ∑ x ∈ X, (S : ℝ)⁻¹ * ∑ t ∈ Finset.range S, nodeProb U ψ t x := rfl
    _ = ∑ x ∈ X, ∑ t ∈ Finset.range S, (S : ℝ)⁻¹ * nodeProb U ψ t x :=
        Finset.sum_congr rfl (fun x _ => Finset.mul_sum _ _ _)
    _ = ∑ t ∈ Finset.range S, ∑ x ∈ X, (S : ℝ)⁻¹ * nodeProb U ψ t x := Finset.sum_comm
    _ = ∑ t ∈ Finset.range S, (S : ℝ)⁻¹ * ∑ x ∈ X, nodeProb U ψ t x := by
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.mul_sum]
    _ = (S : ℝ)⁻¹ * ∑ t ∈ Finset.range S, ∑ x ∈ X, nodeProb U ψ t x := by
        rw [Finset.mul_sum]

/-- For nonnegative error and reference functions of total mass one, a sampling-time bound
implies a mixing-time bound at the same time. -/
theorem sampling_le_mixing
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (π : ((Coin × V) → ℂ) → V → ℝ) (ε : ℝ) (S : ℕ)
    (hε : 0 ≤ ε)
    (hπ_sum : ∀ ψ, ∑ v, π ψ v = 1)
    (hS : IsSamplingTime U π ε S) :
    IsMixingTime U π ε S := by
  intro t ht ψ
  have hpoint : ∀ v : V, |π ψ v - avgNodeProb U ψ t v| ≤ ε * π ψ v := by
    intro v
    have hs := hS t ht ψ {v}
    simpa [avgSetProb] using hs
  have hsum_le : ∑ v, |π ψ v - avgNodeProb U ψ t v| ≤ ε := by
    calc ∑ v, |π ψ v - avgNodeProb U ψ t v|
        ≤ ∑ v, ε * π ψ v := Finset.sum_le_sum (fun v _ => hpoint v)
      _ = ε * ∑ v, π ψ v := by rw [Finset.mul_sum]
      _ = ε := by rw [hπ_sum ψ, mul_one]
  unfold tvDistance
  have hhalf : (1 / 2 : ℝ) * ∑ v, |π ψ v - avgNodeProb U ψ t v| ≤ (1 / 2 : ℝ) * ε := by
    apply mul_le_mul_of_nonneg_left hsum_le
    norm_num
  nlinarith [hε]

/-- A positive sampling time is also a filling time with the same error parameter. -/
theorem sampling_le_filling
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (π : ((Coin × V) → ℂ) → V → ℝ) (ε : ℝ) (S : ℕ)
    (hSpos : 0 < S)
    (hS : IsSamplingTime U π ε S) :
    IsFillingTime U π ε S := by
  intro ψ X
  by_contra hcon
  push Not at hcon
  set c : ℝ := (1 - ε) * (∑ x ∈ X, π ψ x) with hc
  have havg_lt : avgSetProb U ψ S X < c := by
    rw [avgSetProb_eq]
    have hSposR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hSpos
    have hsum_lt : ∑ t ∈ Finset.range S, setProb U ψ t X <
        ∑ t ∈ Finset.range S, c := by
      refine Finset.sum_lt_sum (fun t ht => ?_) ⟨0, Finset.mem_range.mpr hSpos, ?_⟩
      · exact le_of_lt (hcon t (le_of_lt (Finset.mem_range.mp ht)))
      · exact hcon 0 (le_of_lt hSpos)
    have hmul : (S : ℝ)⁻¹ * ∑ t ∈ Finset.range S, setProb U ψ t X <
        (S : ℝ)⁻¹ * ∑ t ∈ Finset.range S, c :=
      mul_lt_mul_of_pos_left hsum_lt (inv_pos.mpr hSposR)
    have hcsum : ∑ t ∈ Finset.range S, c = (S : ℝ) * c := by
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hcsum] at hmul
    have hcancel : (S : ℝ)⁻¹ * ((S : ℝ) * c) = c := by
      field_simp
    rwa [hcancel] at hmul
  have hs := hS S le_rfl ψ X
  have hge : c ≤ avgSetProb U ψ S X := by
    have h2 : (∑ x ∈ X, π ψ x) - avgSetProb U ψ S X ≤ ε * (∑ x ∈ X, π ψ x) :=
      (abs_le.mp hs).2
    simp only [hc]
    nlinarith [h2]
  linarith

/-- A positive sampling time is also a dispersion time with the same error parameter. -/
theorem sampling_le_dispersion
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (π : ((Coin × V) → ℂ) → V → ℝ) (ε : ℝ) (S : ℕ)
    (hSpos : 0 < S)
    (hS : IsSamplingTime U π ε S) :
    IsDispersionTime U π ε S := by
  intro ψ X
  by_contra hcon
  push Not at hcon
  set c : ℝ := (1 + ε) * (∑ x ∈ X, π ψ x) with hc
  have havg_gt : c < avgSetProb U ψ S X := by
    rw [avgSetProb_eq]
    have hSposR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hSpos
    have hsum_lt : ∑ t ∈ Finset.range S, c <
        ∑ t ∈ Finset.range S, setProb U ψ t X := by
      refine Finset.sum_lt_sum (fun t ht => ?_) ⟨0, Finset.mem_range.mpr hSpos, ?_⟩
      · exact le_of_lt (hcon t (le_of_lt (Finset.mem_range.mp ht)))
      · exact hcon 0 (le_of_lt hSpos)
    have hmul : (S : ℝ)⁻¹ * ∑ t ∈ Finset.range S, c <
        (S : ℝ)⁻¹ * ∑ t ∈ Finset.range S, setProb U ψ t X :=
      mul_lt_mul_of_pos_left hsum_lt (inv_pos.mpr hSposR)
    have hcsum : ∑ t ∈ Finset.range S, c = (S : ℝ) * c := by
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hcsum] at hmul
    have hcancel : (S : ℝ)⁻¹ * ((S : ℝ) * c) = c := by
      field_simp
    rwa [hcancel] at hmul
  have hs := hS S le_rfl ψ X
  have hle : avgSetProb U ψ S X ≤ c := by
    have h1 : -(ε * (∑ x ∈ X, π ψ x)) ≤ (∑ x ∈ X, π ψ x) - avgSetProb U ψ S X :=
      (abs_le.mp hs).1
    simp only [hc]
    nlinarith [h1]
  linarith

/-- For nonnegative error, normalized reference functions, and positive `S`, a sampling-time
bound at `S` implies mixing, filling, and dispersion bounds at `S`. See [Aharonov et al.,
Theorem 3.12][AharonovEtAl2001Walks]. -/
theorem theorem_3_12
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (π : ((Coin × V) → ℂ) → V → ℝ) (ε : ℝ) (S : ℕ)
    (hε : 0 ≤ ε)
    (hπ_sum : ∀ ψ, ∑ v, π ψ v = 1)
    (hSpos : 0 < S)
    (hS : IsSamplingTime U π ε S) :
    IsMixingTime U π ε S ∧ IsFillingTime U π ε S ∧ IsDispersionTime U π ε S :=
  ⟨sampling_le_mixing U π ε S hε hπ_sum hS,
   sampling_le_filling U π ε S hSpos hS,
   sampling_le_dispersion U π ε S hSpos hS⟩

end Qatlib.Papers.QWalkGraphs00.MainResults.Times
