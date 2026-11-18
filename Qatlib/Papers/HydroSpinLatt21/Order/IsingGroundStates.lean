/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Exact order in finite signed spin networks

[Saenz2021HydroSpinLattices] observes geometry-dependent ferro- and
antiferromagnetic order. See
[the article](https://doi.org/10.1038/s41586-021-03682-1).

This module proves exact global energy bounds and equality classifications for
unit scalar spins on a finite graph. Positive weights represent ferromagnetic
coupling in one energy and antiferromagnetic coupling in the other. A bipartite
sign assignment attains the antiferromagnetic bound, and alternating spins close
on an even ring but cannot close on an odd ring. The graph model is an explicit
idealization. It does not identify a measured Bessel kernel with a particular
signed graph or prove that active droplet dynamics reaches an equilibrium.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HydroSpinLatt21.Order

/-- Unit scalar spins take the two orientations `1` and `-1`. -/
def UnitSpins {ι : Type*} (spin : ι → ℝ) : Prop := ∀ i, spin i ^ 2 = 1

/-- Ferromagnetic interaction energy, with each edge counted once. -/
def ferroEnergy {ι ε : Type*} [Fintype ε]
    (left right : ε → ι) (weight : ε → ℝ) (spin : ι → ℝ) : ℝ :=
  -∑ e, weight e * spin (left e) * spin (right e)

/-- Antiferromagnetic interaction energy, with each edge counted once. -/
def antiferroEnergy {ι ε : Type*} [Fintype ε]
    (left right : ε → ι) (weight : ε → ℝ) (spin : ι → ℝ) : ℝ :=
  ∑ e, weight e * spin (left e) * spin (right e)

/-- The ferromagnetic energy above its lower bound is a weighted sum of squared
spin differences. -/
theorem ferro_energy_defect {ι ε : Type*} [Fintype ε]
    (left right : ε → ι) (weight : ε → ℝ) (spin : ι → ℝ)
    (hspin : UnitSpins spin) :
    ferroEnergy left right weight spin + ∑ e, weight e =
      ∑ e, weight e / 2 * (spin (left e) - spin (right e)) ^ 2 := by
  classical
  unfold ferroEnergy
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  calc
    -(weight e * spin (left e) * spin (right e)) + weight e =
        weight e / 2 * (spin (left e) ^ 2 + spin (right e) ^ 2 -
          2 * spin (left e) * spin (right e)) := by
      rw [hspin (left e), hspin (right e)]
      ring
    _ = weight e / 2 * (spin (left e) - spin (right e)) ^ 2 := by ring

/-- The antiferromagnetic energy defect is a weighted sum of squared spin sums. -/
theorem antiferro_energy_defect {ι ε : Type*} [Fintype ε]
    (left right : ε → ι) (weight : ε → ℝ) (spin : ι → ℝ)
    (hspin : UnitSpins spin) :
    antiferroEnergy left right weight spin + ∑ e, weight e =
      ∑ e, weight e / 2 * (spin (left e) + spin (right e)) ^ 2 := by
  classical
  unfold antiferroEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  calc
    weight e * spin (left e) * spin (right e) + weight e =
        weight e / 2 * (spin (left e) ^ 2 + spin (right e) ^ 2 +
          2 * spin (left e) * spin (right e)) := by
      rw [hspin (left e), hspin (right e)]
      ring
    _ = weight e / 2 * (spin (left e) + spin (right e)) ^ 2 := by ring

/-- Nonnegative ferromagnetic weights give the sharp global lower bound. -/
theorem ferro_energy_lower_bound {ι ε : Type*} [Fintype ε]
    (left right : ε → ι) (weight : ε → ℝ) (spin : ι → ℝ)
    (hweight : ∀ e, 0 ≤ weight e) (hspin : UnitSpins spin) :
    -(∑ e, weight e) ≤ ferroEnergy left right weight spin := by
  have h := ferro_energy_defect left right weight spin hspin
  have hnonneg : 0 ≤ ∑ e, weight e / 2 * (spin (left e) - spin (right e)) ^ 2 :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (div_nonneg (hweight e) (by norm_num))
      (sq_nonneg _))
  linarith

/-- Strictly positive ferromagnetic weights saturate the lower bound exactly
when every interacting pair has the same orientation. -/
theorem ferro_energy_min_iff {ι ε : Type*} [Fintype ε]
    (left right : ε → ι) (weight : ε → ℝ) (spin : ι → ℝ)
    (hweight : ∀ e, 0 < weight e) (hspin : UnitSpins spin) :
    ferroEnergy left right weight spin = -(∑ e, weight e) ↔
      ∀ e, spin (left e) = spin (right e) := by
  classical
  have hdef := ferro_energy_defect left right weight spin hspin
  constructor
  · intro h e
    have hsum : (∑ e, weight e / 2 * (spin (left e) - spin (right e)) ^ 2) = 0 := by
      linarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ =>
      mul_nonneg (div_nonneg (hweight e).le (by norm_num)) (sq_nonneg _))).1 hsum e
      (Finset.mem_univ e)
    have hsq : (spin (left e) - spin (right e)) ^ 2 = 0 :=
      (mul_eq_zero.mp hz).resolve_left (ne_of_gt (div_pos (hweight e) (by norm_num)))
    nlinarith
  · intro h
    have hzero : (∑ e, weight e / 2 * (spin (left e) - spin (right e)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      rw [h e, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
    linarith

/-- Nonnegative antiferromagnetic weights have the same sharp numerical bound. -/
theorem antiferro_energy_lower_bound {ι ε : Type*} [Fintype ε]
    (left right : ε → ι) (weight : ε → ℝ) (spin : ι → ℝ)
    (hweight : ∀ e, 0 ≤ weight e) (hspin : UnitSpins spin) :
    -(∑ e, weight e) ≤ antiferroEnergy left right weight spin := by
  have h := antiferro_energy_defect left right weight spin hspin
  have hnonneg : 0 ≤ ∑ e, weight e / 2 * (spin (left e) + spin (right e)) ^ 2 :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (div_nonneg (hweight e) (by norm_num))
      (sq_nonneg _))
  linarith

/-- Strictly positive antiferromagnetic weights attain the lower bound exactly
when the spins at both ends of every edge are opposite. -/
theorem antiferro_energy_min_iff {ι ε : Type*} [Fintype ε]
    (left right : ε → ι) (weight : ε → ℝ) (spin : ι → ℝ)
    (hweight : ∀ e, 0 < weight e) (hspin : UnitSpins spin) :
    antiferroEnergy left right weight spin = -(∑ e, weight e) ↔
      ∀ e, spin (left e) = -spin (right e) := by
  classical
  have hdef := antiferro_energy_defect left right weight spin hspin
  constructor
  · intro h e
    have hsum : (∑ e, weight e / 2 * (spin (left e) + spin (right e)) ^ 2) = 0 := by
      linarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ =>
      mul_nonneg (div_nonneg (hweight e).le (by norm_num)) (sq_nonneg _))).1 hsum e
      (Finset.mem_univ e)
    have hsq : (spin (left e) + spin (right e)) ^ 2 = 0 :=
      (mul_eq_zero.mp hz).resolve_left (ne_of_gt (div_pos (hweight e) (by norm_num)))
    nlinarith
  · intro h
    have hzero : (∑ e, weight e / 2 * (spin (left e) + spin (right e)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      simp [h e]
    linarith

/-- A constant unit orientation is a global ferromagnetic minimizer. -/
theorem constant_ferro_global_min {ι ε : Type*} [Fintype ε]
    (left right : ε → ι) (weight : ε → ℝ) (hweight : ∀ e, 0 < weight e)
    (spin : ι → ℝ) (hspin : UnitSpins spin) :
    ferroEnergy left right weight (fun _ => 1) ≤ ferroEnergy left right weight spin := by
  rw [(ferro_energy_min_iff left right weight (fun _ => 1) hweight (by intro; norm_num)).2
    (by intro; rfl)]
  exact ferro_energy_lower_bound left right weight spin (fun e => (hweight e).le) hspin

/-- A bipartite sign assignment gives a global antiferromagnetic minimizer. -/
theorem bipartite_antiferro_global_min {ι ε : Type*} [Fintype ε]
    (left right : ε → ι) (weight : ε → ℝ) (hweight : ∀ e, 0 < weight e)
    (color : ι → ℝ) (hcolor : UnitSpins color)
    (hedge : ∀ e, color (left e) = -color (right e))
    (spin : ι → ℝ) (hspin : UnitSpins spin) :
    antiferroEnergy left right weight color ≤ antiferroEnergy left right weight spin := by
  rw [(antiferro_energy_min_iff left right weight color hweight hcolor).2 hedge]
  exact antiferro_energy_lower_bound left right weight spin (fun e => (hweight e).le) hspin

/-- A graph's Boolean bipartition assigns opposite unit orientations to its
two vertex classes. -/
def partitionSpin {ι : Type*} (color : ι → Bool) (i : ι) : ℝ :=
  if color i then 1 else -1

/-- The explicit bipartition construction has unit spins at every vertex. -/
theorem partition_spin_unit {ι : Type*} (color : ι → Bool) : UnitSpins (partitionSpin color) := by
  intro i
  unfold partitionSpin
  split <;> norm_num

/-- A Boolean bipartition crossing every edge constructively attains the
antiferromagnetic lower bound. -/
theorem partition_attains_antiferro_bound {ι ε : Type*} [Fintype ε]
    (left right : ε → ι) (weight : ε → ℝ) (hweight : ∀ e, 0 < weight e)
    (color : ι → Bool) (hcross : ∀ e, color (left e) ≠ color (right e)) :
    antiferroEnergy left right weight (partitionSpin color) = -(∑ e, weight e) := by
  apply (antiferro_energy_min_iff left right weight (partitionSpin color) hweight
    (partition_spin_unit color)).2
  intro e
  have he := hcross e
  cases hl : color (left e) <;> cases hr : color (right e) <;>
    simp_all [partitionSpin]

/-- Global ferromagnetic minimizers among all unit-spin configurations are
exactly the configurations aligned across every positive-weight edge. -/
theorem ferro_global_min_iff {ι ε : Type*} [Fintype ε]
    (left right : ε → ι) (weight : ε → ℝ) (hweight : ∀ e, 0 < weight e)
    (spin : ι → ℝ) (hspin : UnitSpins spin) :
    (∀ other : ι → ℝ, UnitSpins other →
      ferroEnergy left right weight spin ≤ ferroEnergy left right weight other) ↔
      ∀ e, spin (left e) = spin (right e) := by
  constructor
  · intro h
    apply (ferro_energy_min_iff left right weight spin hweight hspin).1
    apply le_antisymm
    · simpa [ferroEnergy] using h (fun _ => 1) (by intro; norm_num)
    · exact ferro_energy_lower_bound left right weight spin (fun e => (hweight e).le) hspin
  · intro hedge other hother
    rw [(ferro_energy_min_iff left right weight spin hweight hspin).2 hedge]
    exact ferro_energy_lower_bound left right weight other (fun e => (hweight e).le) hother

/-- On a bipartite graph, global antiferromagnetic minimizers are exactly the
configurations opposite across every positive-weight edge. -/
theorem bipartite_antiferro_global_min_iff {ι ε : Type*} [Fintype ε]
    (left right : ε → ι) (weight : ε → ℝ) (hweight : ∀ e, 0 < weight e)
    (color : ι → Bool) (hcross : ∀ e, color (left e) ≠ color (right e))
    (spin : ι → ℝ) (hspin : UnitSpins spin) :
    (∀ other : ι → ℝ, UnitSpins other →
      antiferroEnergy left right weight spin ≤ antiferroEnergy left right weight other) ↔
      ∀ e, spin (left e) = -spin (right e) := by
  constructor
  · intro h
    apply (antiferro_energy_min_iff left right weight spin hweight hspin).1
    apply le_antisymm
    · have hbound := h (partitionSpin color) (partition_spin_unit color)
      rw [partition_attains_antiferro_bound left right weight hweight color hcross] at hbound
      exact hbound
    · exact antiferro_energy_lower_bound left right weight spin
        (fun e => (hweight e).le) hspin
  · intro hedge other hother
    rw [(antiferro_energy_min_iff left right weight spin hweight hspin).2 hedge]
    exact antiferro_energy_lower_bound left right weight other
      (fun e => (hweight e).le) hother

/-- Alternating orientations along the integer-labelled vertices of a ring. -/
def alternatingSpin (i : ℕ) : ℝ := (-1) ^ i

/-- Every alternating spin has unit magnitude. -/
theorem alternating_spin_unit (i : ℕ) : alternatingSpin i ^ 2 = 1 := by
  unfold alternatingSpin
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

/-- Consecutive alternating spins are opposite. -/
theorem alternating_spin_succ (i : ℕ) : alternatingSpin (i + 1) = -alternatingSpin i := by
  simp [alternatingSpin, pow_succ]

/-- Alternating orientations close on every even ring. -/
theorem alternating_spin_even_closure {n : ℕ} (hn : Even n) :
    alternatingSpin n = alternatingSpin 0 := by
  simpa [alternatingSpin] using hn.neg_one_pow (α := ℝ)

/-- Opposite nearest neighbours on a finite chain determine the alternating
pattern from the initial orientation. -/
theorem opposite_chain_formula (spin : ℕ → ℝ) (n : ℕ)
    (hnext : ∀ i < n, spin (i + 1) = -spin i) :
    spin n = alternatingSpin n * spin 0 := by
  induction n with
  | zero => simp [alternatingSpin]
  | succ n ih =>
    rw [hnext n (Nat.lt_succ_self n), ih (fun i hi => hnext i (Nat.lt_trans hi
      (Nat.lt_succ_self n))), alternating_spin_succ]
    ring

/-- Odd rings cannot have nonzero unit spins and opposite orientations across
every edge, including the closing edge. This isolates geometric frustration
without making a statement about observed active dynamics. -/
theorem odd_ring_obstruction (spin : ℕ → ℝ) {n : ℕ} (hn : Odd n)
    (hzero : spin 0 ^ 2 = 1) (hclose : spin n = spin 0) :
    ¬(∀ i < n, spin (i + 1) = -spin i) := by
  intro hnext
  have h := opposite_chain_formula spin n hnext
  have hsign : alternatingSpin n = -1 := by
    simpa [alternatingSpin] using hn.neg_one_pow (α := ℝ)
  rw [hclose, hsign] at h
  nlinarith

end Qatlib.Papers.HydroSpinLatt21.Order
