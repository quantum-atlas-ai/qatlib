/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic
public import Qatlib.Papers.QWalkGraphs00.MainResults.Core

@[expose] public section

/-!
# Mixing, sampling, filling, and dispersion times

This module defines subset probabilities, total variation distance, and four time predicates for
a finite coined walk relative to a supplied reference distribution. Relative subset sampling
bounds imply the mixing, filling, and dispersion conclusions formalized in Theorem 3.12 of
[AharonovEtAl2001Walks]. The four time predicates use computational basis inputs, as in
Definitions 3.8–3.11. Mixing uses the paper's full ℓ¹ distance.

## Main statements

* `avgSetProb_eq`: expresses averaged subset mass as a time average.
* `theorem_3_12`: derives all three time predicates from a positive sampling time.

## References

* [Aharonov et al., 2001][AharonovEtAl2001Walks]
-/

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

/-- The computational basis state at coin and vertex index `p`. -/
def walkBasisState (p : Coin × V) : (Coin × V) → ℂ :=
  Pi.single p 1

/-- The condition that every averaging length at least `T` gives total variation error at most
`ε / 2` for every computational basis input, equivalently an ℓ¹ error at most `ε`. -/
def IsMixingTime (U : Matrix (Coin × V) (Coin × V) ℂ)
    (π : ((Coin × V) → ℂ) → V → ℝ) (ε : ℝ) (T : ℕ) : Prop :=
  ∀ (t : ℕ), T ≤ t → ∀ p : Coin × V,
    2 * tvDistance (π (walkBasisState p)) (fun v => avgNodeProb U (walkBasisState p) t v) ≤ ε

/-- The condition that every averaging length at least `T` gives relative error at most `ε` on
every subset for every computational basis input. -/
def IsSamplingTime (U : Matrix (Coin × V) (Coin × V) ℂ)
    (π : ((Coin × V) → ℂ) → V → ℝ) (ε : ℝ) (T : ℕ) : Prop :=
  ∀ (t : ℕ), T ≤ t → ∀ (p : Coin × V) (X : Finset V),
    |(∑ x ∈ X, π (walkBasisState p) x) - avgSetProb U (walkBasisState p) t X| ≤
      ε * (∑ x ∈ X, π (walkBasisState p) x)

/-- For each computational basis input and subset, by time `T` the subset weight reaches
at least `(1 - ε)` times the reference mass. -/
def IsFillingTime (U : Matrix (Coin × V) (Coin × V) ℂ)
    (π : ((Coin × V) → ℂ) → V → ℝ) (ε : ℝ) (T : ℕ) : Prop :=
  ∀ (p : Coin × V) (X : Finset V),
    ∃ t : ℕ, t ≤ T ∧ (1 - ε) * (∑ x ∈ X, π (walkBasisState p) x) ≤
      setProb U (walkBasisState p) t X

/-- For each computational basis input and subset, by time `T` the subset weight reaches
at most `(1 + ε)` times the reference mass. -/
def IsDispersionTime (U : Matrix (Coin × V) (Coin × V) ℂ)
    (π : ((Coin × V) → ℂ) → V → ℝ) (ε : ℝ) (T : ℕ) : Prop :=
  ∀ (p : Coin × V) (X : Finset V),
    ∃ t : ℕ, t ≤ T ∧ setProb U (walkBasisState p) t X ≤
      (1 + ε) * (∑ x ∈ X, π (walkBasisState p) x)

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

/-- For reference functions of total mass one on basis inputs, a sampling-time bound
implies a mixing-time bound at the same time. -/
theorem sampling_le_mixing
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (π : ((Coin × V) → ℂ) → V → ℝ) (ε : ℝ) (S : ℕ)
    (hπ_sum : ∀ p, ∑ v, π (walkBasisState p) v = 1)
    (hS : IsSamplingTime U π ε S) :
    IsMixingTime U π ε S := by
  intro t ht p
  let ψ := walkBasisState p
  have hpoint : ∀ v : V, |π ψ v - avgNodeProb U ψ t v| ≤ ε * π ψ v := by
    intro v
    have hs := hS t ht p {v}
    simpa [avgSetProb] using hs
  have hsum_le : ∑ v, |π ψ v - avgNodeProb U ψ t v| ≤ ε := by
    calc ∑ v, |π ψ v - avgNodeProb U ψ t v|
        ≤ ∑ v, ε * π ψ v := Finset.sum_le_sum (fun v _ => hpoint v)
      _ = ε * ∑ v, π ψ v := by rw [Finset.mul_sum]
      _ = ε := by rw [hπ_sum p, mul_one]
  change 2 * tvDistance (π ψ) (fun v => avgNodeProb U ψ t v) ≤ ε
  unfold tvDistance
  linarith only [hsum_le]

/-- A positive sampling time is also a filling time with the same error parameter. -/
theorem sampling_le_filling
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (π : ((Coin × V) → ℂ) → V → ℝ) (ε : ℝ) (S : ℕ)
    (hSpos : 0 < S)
    (hS : IsSamplingTime U π ε S) :
    IsFillingTime U π ε S := by
  intro p X
  let ψ := walkBasisState p
  change ∃ t : ℕ, t ≤ S ∧ (1 - ε) * (∑ x ∈ X, π ψ x) ≤ setProb U ψ t X
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
  have hs := hS S le_rfl p X
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
  intro p X
  let ψ := walkBasisState p
  change ∃ t : ℕ, t ≤ S ∧ setProb U ψ t X ≤ (1 + ε) * (∑ x ∈ X, π ψ x)
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
  have hs := hS S le_rfl p X
  have hle : avgSetProb U ψ S X ≤ c := by
    have h1 : -(ε * (∑ x ∈ X, π ψ x)) ≤ (∑ x ∈ X, π ψ x) - avgSetProb U ψ S X :=
      (abs_le.mp hs).1
    simp only [hc]
    nlinarith [h1]
  linarith

/-- For reference functions normalized on basis inputs and positive `S`, a sampling-time
bound at `S` implies mixing, filling, and dispersion bounds at `S`. See [Aharonov et al.,
Theorem 3.12][AharonovEtAl2001Walks]. -/
theorem theorem_3_12
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (π : ((Coin × V) → ℂ) → V → ℝ) (ε : ℝ) (S : ℕ)
    (hπ_sum : ∀ p, ∑ v, π (walkBasisState p) v = 1)
    (hSpos : 0 < S)
    (hS : IsSamplingTime U π ε S) :
    IsMixingTime U π ε S ∧ IsFillingTime U π ε S ∧ IsDispersionTime U π ε S :=
  ⟨sampling_le_mixing U π ε S hπ_sum hS,
   sampling_le_filling U π ε S hSpos hS,
   sampling_le_dispersion U π ε S hSpos hS⟩

end Qatlib.Papers.QWalkGraphs00.MainResults.Times
