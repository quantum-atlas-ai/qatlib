/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PairFlow
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# A quadratic gap bound from the actual pair-graph flow

Testing the explicit divergence against the squared vertex amplitudes and
applying Young's inequality yields a uniform Rayleigh lower bound. Every flow,
edge and loop in the proof is the actual coordinate construction of `PairFlow`;
no expansion, cut or spectral lower bound is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.KhovanovHom25.MainResults.PairFlow


/-- Squared mass of a real amplitude vector on the actual pair graph. -/
def mass {N : ℕ} (y : Pair N → ℝ) : ℝ := ∑ v, y v ^ 2

/-- The diagonal-loop part of the quadratic form. -/
def loopEnergy {N : ℕ} (y : Pair N → ℝ) : ℝ :=
  ∑ v, if IsLoop v then y v ^ 2 else 0

/-- Each undirected nearest-neighbor edge contributes its squared difference once. -/
def edgeEnergy {N : ℕ} (y : Pair N → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ v, ∑ u, if Adj v u then (y v - y u) ^ 2 else 0

/-- The actual loop-plus-gradient quadratic form. -/
def energy {N : ℕ} (y : Pair N → ℝ) : ℝ := loopEnergy y + edgeEnergy y

/-- The squared mass is nonnegative. -/
theorem mass_nonneg {N : ℕ} (y : Pair N → ℝ) : 0 ≤ mass y :=
  Finset.sum_nonneg fun _v _hv => sq_nonneg _

/-- Every diagonal-loop contribution is nonnegative. -/
theorem loopEnergy_nonneg {N : ℕ} (y : Pair N → ℝ) : 0 ≤ loopEnergy y := by
  apply Finset.sum_nonneg
  intro v _hv
  split_ifs <;> positivity

/-- The edge-gradient energy is nonnegative. -/
theorem edgeEnergy_nonneg {N : ℕ} (y : Pair N → ℝ) : 0 ≤ edgeEnergy y := by
  unfold edgeEnergy
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro v _hv
  apply Finset.sum_nonneg
  intro u _hu
  split_ifs <;> positivity

/-- The outgoing natural flow, viewed as a real weight. -/
def outWeight {N : ℕ} (v : Pair N) : ℝ := ∑ u, (flow v u : ℝ)

/-- The incoming natural flow, viewed as a real weight. -/
def inWeight {N : ℕ} (v : Pair N) : ℝ := ∑ u, (flow u v : ℝ)

/-- The total incident flow is at most `2N`, including all coordinate boundaries. -/
theorem incident_nat {N : ℕ} (v : Pair N) :
    (∑ u, flow v u) + (∑ u, flow u v) ≤ 2 * N := by
  rw [outgoing, incoming]
  have := coords v
  split_ifs <;> omega

/-- The same incident-flow bound in real scalars. -/
theorem incident_real {N : ℕ} (v : Pair N) :
    outWeight v + inWeight v ≤ 2 * (N : ℝ) := by
  unfold outWeight inWeight
  exact_mod_cast incident_nat v

/-- The exact pointwise divergence identity in real scalars. -/
theorem divergence_real {N : ℕ} (v : Pair N) :
    outWeight v + ((N : ℝ) + 1) * (if IsLoop v then 1 else 0) = inWeight v + 2 := by
  unfold outWeight inWeight
  exact_mod_cast divergence v

/-- Summing a weight depending only on the edge's source collapses its outgoing flow. -/
theorem weighted_rows {N : ℕ} (f : Pair N → ℝ) :
    (∑ v, ∑ u, (flow v u : ℝ) * f v) = ∑ v, outWeight v * f v := by
  simp only [outWeight, Finset.sum_mul]

/-- Summing a weight depending only on the edge's target collapses its incoming flow. -/
theorem weighted_cols {N : ℕ} (f : Pair N → ℝ) :
    (∑ v, ∑ u, (flow v u : ℝ) * f u) = ∑ v, inWeight v * f v := by
  rw [Finset.sum_comm]
  simp only [inWeight, Finset.sum_mul]

/-- Endpoint weights combine through the actual incident flow. -/
theorem weighted_endpoints {N : ℕ} (f : Pair N → ℝ) :
    (∑ v, ∑ u, (flow v u : ℝ) * (f v + f u)) =
      ∑ v, (outWeight v + inWeight v) * f v := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [weighted_rows, weighted_cols, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _hv
  ring

/-- The signed squared-amplitude flux across all directed flow edges. -/
def flux {N : ℕ} (y : Pair N → ℝ) : ℝ :=
  ∑ v, ∑ u, (flow v u : ℝ) * (y v ^ 2 - y u ^ 2)

/-- Testing the explicit flow divergence against the squared amplitudes. -/
theorem flux_eq {N : ℕ} (y : Pair N → ℝ) :
    flux y = 2 * mass y - ((N : ℝ) + 1) * loopEnergy y := by
  have hpoint (v : Pair N) :
      (outWeight v - inWeight v) * y v ^ 2 =
        2 * y v ^ 2 - ((N : ℝ) + 1) * (if IsLoop v then y v ^ 2 else 0) := by
    have hd := divergence_real v
    split_ifs with h
    · simp only [h, ite_true, mul_one] at hd
      nlinarith
    · simp only [h, ite_false, mul_zero, add_zero] at hd
      nlinarith
  calc
    _ = (∑ v, outWeight v * y v ^ 2) - ∑ v, inWeight v * y v ^ 2 := by
      unfold flux
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [weighted_rows, weighted_cols]
    _ = ∑ v, (outWeight v - inWeight v) * y v ^ 2 := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    _ = ∑ v, (2 * y v ^ 2 - ((N : ℝ) + 1) * (if IsLoop v then y v ^ 2 else 0)) :=
      Finset.sum_congr rfl fun v _hv => hpoint v
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; rfl

/-- Flow-weighted edge-gradient mass. -/
def gradFlow {N : ℕ} (y : Pair N → ℝ) : ℝ :=
  ∑ v, ∑ u, (flow v u : ℝ) * (y v - y u) ^ 2

/-- Flow-weighted endpoint-sum mass. -/
def plusFlow {N : ℕ} (y : Pair N → ℝ) : ℝ :=
  ∑ v, ∑ u, (flow v u : ℝ) * (y v + y u) ^ 2

/-- The true edge capacity bounds the gradient flow by the actual graph energy. -/
theorem gradFlow_bound {N : ℕ} (y : Pair N → ℝ) :
    gradFlow y ≤ 2 * (N : ℝ) * edgeEnergy y := by
  have hpoint (v u : Pair N) :
      (flow v u : ℝ) * (y v - y u) ^ 2 ≤
        (N : ℝ) * (if Adj v u then (y v - y u) ^ 2 else 0) := by
    have hf : (flow v u : ℝ) ≤ if Adj v u then (N : ℝ) else 0 := by
      exact_mod_cast flow_capacity v u
    split_ifs with h
    · simp only [h, ite_true] at hf
      exact mul_le_mul_of_nonneg_right hf (sq_nonneg _)
    · simp only [h, ite_false] at hf
      simpa only [mul_zero] using
        mul_nonpos_of_nonpos_of_nonneg hf (sq_nonneg (y v - y u))
  calc
    _ ≤ (N : ℝ) * ∑ v, ∑ u, if Adj v u then (y v - y u) ^ 2 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v _hv
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun u _hu => hpoint v u
    _ = _ := by unfold edgeEnergy; ring

/-- Incident flow bounds the endpoint-sum mass by the actual vector mass. -/
theorem plusFlow_bound {N : ℕ} (y : Pair N → ℝ) :
    plusFlow y ≤ 4 * (N : ℝ) * mass y := by
  calc
    _ ≤ 2 * ∑ v, ∑ u, (flow v u : ℝ) * (y v ^ 2 + y u ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v _hv
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro u _hu
      have hf : 0 ≤ (flow v u : ℝ) := Nat.cast_nonneg _
      have hs := mul_nonneg hf (sq_nonneg (y v - y u))
      nlinarith
    _ = 2 * ∑ v, (outWeight v + inWeight v) * y v ^ 2 := by rw [weighted_endpoints]
    _ ≤ 2 * ∑ v, (2 * (N : ℝ)) * y v ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun v _hv =>
        mul_le_mul_of_nonneg_right (incident_real v) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; unfold mass; ring

/-- Young's inequality for the actual directed flow, proved by a finite
sum of nonnegative weighted squares. -/
theorem flux_young {N : ℕ} (y : Pair N → ℝ) (T : ℝ) :
    4 * T * flux y ≤ 4 * T ^ 2 * gradFlow y + plusFlow y := by
  have hpoint (v u : Pair N) :
      4 * T * ((flow v u : ℝ) * (y v ^ 2 - y u ^ 2)) ≤
        4 * T ^ 2 * ((flow v u : ℝ) * (y v - y u) ^ 2) +
          (flow v u : ℝ) * (y v + y u) ^ 2 := by
    have hf : 0 ≤ (flow v u : ℝ) := Nat.cast_nonneg _
    have hs := mul_nonneg hf (sq_nonneg (2 * T * (y v - y u) - (y v + y u)))
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) fun v _hv =>
    Finset.sum_le_sum (s := Finset.univ) fun u _hu => hpoint v u
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, flux, gradFlow, plusFlow] using hs

/-- The actual quadratic form has a uniform positive Rayleigh lower bound,
independent of any assumed cut expansion or unproved spectral certificate. -/
theorem mass_le_energy {N : ℕ} (y : Pair N → ℝ) :
    mass y ≤ 2 * ((N : ℝ) + 1) ^ 2 * energy y := by
  have hD := mass_nonneg y
  have hL := loopEnergy_nonneg y
  have hE := edgeEnergy_nonneg y
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hy := flux_young y ((N : ℝ) + 1)
  have hg := gradFlow_bound y
  have hp := plusFlow_bound y
  have hflux := flux_eq y
  have hupper : 4 * ((N : ℝ) + 1) * flux y ≤
      8 * (N : ℝ) * ((N : ℝ) + 1) ^ 2 * edgeEnergy y + 4 * (N : ℝ) * mass y := by
    calc
      _ ≤ 4 * ((N : ℝ) + 1) ^ 2 * gradFlow y + plusFlow y := hy
      _ ≤ 4 * ((N : ℝ) + 1) ^ 2 * (2 * (N : ℝ) * edgeEnergy y) +
          4 * (N : ℝ) * mass y :=
        add_le_add (mul_le_mul_of_nonneg_left hg (by positivity)) hp
      _ = _ := by ring
  rw [hflux] at hupper
  have hbasic : mass y ≤ ((N : ℝ) + 1) * loopEnergy y +
      2 * (N : ℝ) * ((N : ℝ) + 1) * edgeEnergy y := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * ((N : ℝ) + 1) by positivity)).mp
    nlinarith
  have hcL : (N : ℝ) + 1 ≤ 2 * ((N : ℝ) + 1) ^ 2 := by nlinarith
  have hcE : 2 * (N : ℝ) * ((N : ℝ) + 1) ≤ 2 * ((N : ℝ) + 1) ^ 2 := by nlinarith
  calc
    _ ≤ ((N : ℝ) + 1) * loopEnergy y +
        2 * (N : ℝ) * ((N : ℝ) + 1) * edgeEnergy y := hbasic
    _ ≤ 2 * ((N : ℝ) + 1) ^ 2 * loopEnergy y +
        2 * ((N : ℝ) + 1) ^ 2 * edgeEnergy y :=
      add_le_add (mul_le_mul_of_nonneg_right hcL hL) (mul_le_mul_of_nonneg_right hcE hE)
    _ = _ := by unfold energy; ring

/-- The unnormalized energy controls the squared mass with the same uniform constant. -/
theorem energy_lower {N : ℕ} (y : Pair N → ℝ) :
    mass y / (2 * ((N : ℝ) + 1) ^ 2) ≤ energy y := by
  apply (div_le_iff₀ (show 0 < 2 * ((N : ℝ) + 1) ^ 2 by positivity)).2
  simpa only [mul_comm] using mass_le_energy y

/-- Every nonzero amplitude vector has a uniformly positive Rayleigh quotient. -/
theorem ratio_lower {N : ℕ} (y : Pair N → ℝ) (hy : 0 < mass y) :
    1 / (2 * ((N : ℝ) + 1) ^ 2) ≤ energy y / mass y := by
  apply (div_le_div_iff₀ (show 0 < 2 * ((N : ℝ) + 1) ^ 2 by positivity) hy).2
  simpa only [one_mul, mul_comm] using mass_le_energy y

end Qatlib.Papers.KhovanovHom25.MainResults.PairFlow
