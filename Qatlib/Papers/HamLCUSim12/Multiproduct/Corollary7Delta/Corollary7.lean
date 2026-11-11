/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductGammaThresholdHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductMassStructureHami

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 7 — gamma threshold guaranteeing subtracted failure `P_- <= delta`

Fixed source: arXiv:1202.5822v1, Corollary 7, p.8:
let `M_{k,chi}` be as in Definition 1, `kappa` as in Theorem 3, `delta <= 1`, `k > 0`,
and
`gamma >= 1 + log(eta)/2 + (1/(2k)) log((2k)^{5/2}/delta)`.
Then `P_- <= delta` and `k^2 e^{-2 gamma (k+1)} <= 1/2`.

The first conjunct is derived here from the frozen threshold statement
(`MultiproductGammaThreshold.multiproductGammaThreshold`), which gives
`4 Sigma_- <= delta Sigma_+`; combined with `P_- = 4 kappa/(kappa+1)^2`,
`kappa = Sigma_+/Sigma_- > 0`, this yields `P_- <= 4/kappa <= delta`.
`N > k` (needed for the mass structure) follows from the second conjunct.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HamLCUSim12.Multiproduct.Corollary7Delta

open Qatlib.Papers.HamLCUSim12.Multiproduct

/-- Positive sign mass `Sigma_+ := sum_{C_q > 0} C_q`. -/
def posMass (k : ℕ) (N : ℝ) : ℝ :=
  ∑ q ∈ Finset.univ.filter (fun q : Fin (k + 1) => 0 < mCoeff k N q), mCoeff k N q

/-- Negative sign mass `Sigma_- := sum_{C_q < 0} |C_q|`. -/
def negMass (k : ℕ) (N : ℝ) : ℝ :=
  ∑ q ∈ Finset.univ.filter (fun q : Fin (k + 1) => mCoeff k N q < 0), |mCoeff k N q|

/-- `kappa := Sigma_+ / Sigma_-`. -/
def kappa (k : ℕ) (N : ℝ) : ℝ := posMass k N / negMass k N

/-- The quantity `posMass` is positive under the stated assumptions. -/
theorem posMass_pos {k : ℕ} {N : ℝ} (hk : 1 ≤ k) (hN : (k : ℝ) < N) :
    0 < posMass k N := by
  have hm := (multiproductMassStructure k hk N hN).1
  have hmem : Fin.last k ∈ Finset.univ.filter (fun q : Fin (k + 1) => 0 < mCoeff k N q) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    linarith
  have hnonneg : ∀ i ∈ Finset.univ.filter (fun q : Fin (k + 1) => 0 < mCoeff k N q),
      (0 : ℝ) ≤ mCoeff k N i := by
    intro i hi
    have := (Finset.mem_filter.mp hi).2
    linarith
  have hle := Finset.single_le_sum hnonneg hmem
  unfold posMass
  linarith

/-- The quantity `negMass` is positive under the stated assumptions. -/
theorem negMass_pos {k : ℕ} {N : ℝ} (hk : 1 ≤ k) (hN : (k : ℝ) < N) :
    0 < negMass k N := by
  obtain ⟨q, hq⟩ := (multiproductMassStructure k hk N hN).2
  have hmem : q ∈ Finset.univ.filter (fun q : Fin (k + 1) => mCoeff k N q < 0) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hq
  have hnonneg : ∀ i ∈ Finset.univ.filter (fun q : Fin (k + 1) => mCoeff k N q < 0),
      (0 : ℝ) ≤ |mCoeff k N i| := fun i _ => abs_nonneg _
  have hle := Finset.single_le_sum hnonneg hmem
  unfold negMass
  have hqpos : 0 < |mCoeff k N q| := abs_pos.mpr (ne_of_lt hq)
  linarith

/-- The quantity `kappa` is positive under the stated assumptions. -/
theorem kappa_pos {k : ℕ} {N : ℝ} (hk : 1 ≤ k) (hN : (k : ℝ) < N) :
    0 < kappa k N := by
  unfold kappa
  exact div_pos (posMass_pos hk hN) (negMass_pos hk hN)

/-- The retry bound `k^2 e^{-2 gamma (k+1)} <= 1/2` of Corollary 7 forces the last
repetition node `N = e^{gamma(k+1)}` to exceed `k`. -/
theorem lt_node_of_retry_bound {k : ℕ} (γ : ℝ)
    (h : (k : ℝ) ^ 2 * Real.exp (-(2 * γ) * ((k + 1 : ℕ) : ℝ)) ≤ 1 / 2) :
    (k : ℝ) < Real.exp (γ * ((k + 1 : ℕ) : ℝ)) := by
  set N : ℝ := Real.exp (γ * ((k + 1 : ℕ) : ℝ)) with hNdef
  have hNpos : 0 < N := Real.exp_pos _
  have hsq : N ^ 2 = Real.exp (2 * γ * ((k + 1 : ℕ) : ℝ)) := by
    rw [hNdef, sq, ← Real.exp_add]
    congr 1
    ring
  have h' : (k : ℝ) ^ 2 ≤ (1 / 2) * N ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right h (le_of_lt (sq_pos_of_pos hNpos))
    have heq : ((k : ℝ) ^ 2 * Real.exp (-(2 * γ) * ((k + 1 : ℕ) : ℝ))) * N ^ 2
        = (k : ℝ) ^ 2 := by
      rw [hsq, mul_assoc, ← Real.exp_add]
      have hzero : -(2 * γ) * ((k + 1 : ℕ) : ℝ) + 2 * γ * ((k + 1 : ℕ) : ℝ) = 0 := by ring
      rw [hzero, Real.exp_zero, mul_one]
    calc (k : ℝ) ^ 2
        = ((k : ℝ) ^ 2 * Real.exp (-(2 * γ) * ((k + 1 : ℕ) : ℝ))) * N ^ 2 := heq.symm
      _ ≤ (1 / 2) * N ^ 2 := hm
  have hlt : (k : ℝ) ^ 2 < N ^ 2 := by nlinarith [sq_pos_of_pos hNpos]
  by_contra hcon
  push_neg at hcon
  have hle : N ^ 2 ≤ (k : ℝ) ^ 2 := by
    have hsqle := mul_self_le_mul_self hNpos.le hcon
    simpa [sq] using hsqle
  nlinarith

/-- Fixed arXiv:1202.5822v1, Corollary 7: under the stated gamma threshold,
`P_- = 4 kappa/(kappa+1)^2 <= delta` and `k^2 e^{-2 gamma (k+1)} <= 1/2`. -/
theorem corollary7_delta (k : ℕ) (hk : 1 ≤ k) (γ η δ : ℝ)
    (hγ : 0 < γ) (hη : 1 / 4 < η) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hEta : EtaMaxProperty η) (hFact : FactorialLowerBound)
    (hγlow : 1 + Real.log η / 2
        + (1 / (2 * (k : ℝ))) * Real.log ((2 * (k : ℝ)) ^ ((5 : ℝ) / 2) / δ) ≤ γ) :
    (4 * kappa k (Real.exp (γ * ((k + 1 : ℕ) : ℝ)))
        / (kappa k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) + 1) ^ 2 ≤ δ)
      ∧ (k : ℝ) ^ 2 * Real.exp (-(2 * γ) * ((k + 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
  set N : ℝ := Real.exp (γ * ((k + 1 : ℕ) : ℝ)) with hNdef
  obtain ⟨hmass, hsmall⟩ :=
    multiproductGammaThreshold k hk γ η δ hγ hη hδ0 hδ1 hEta hFact hγlow
  refine ⟨?_, hsmall⟩
  have hN : (k : ℝ) < N := lt_node_of_retry_bound γ hsmall
  have hpos := posMass_pos hk hN
  have hneg := negMass_pos hk hN
  have hκ : 0 < kappa k N := kappa_pos hk hN
  have hmass' : 4 * negMass k N ≤ δ * posMass k N := hmass
  have h4κ : 4 / kappa k N ≤ δ := by
    unfold kappa
    rw [div_div_eq_mul_div, div_le_iff₀ hpos]
    simpa only [mul_comm] using hmass'
  have hstep : 4 * kappa k N / (kappa k N + 1) ^ 2 ≤ 4 / kappa k N := by
    have hden : 0 < kappa k N * (kappa k N + 1) ^ 2 := by positivity
    have hnum : 4 * kappa k N * kappa k N - 4 * (kappa k N + 1) ^ 2 ≤ 0 := by nlinarith
    have hkey : 4 * kappa k N / (kappa k N + 1) ^ 2 - 4 / kappa k N
        = (4 * kappa k N * kappa k N - 4 * (kappa k N + 1) ^ 2)
            / (kappa k N * (kappa k N + 1) ^ 2) := by
      rw [div_sub_div]
      · ring_nf
      · positivity
      · exact ne_of_gt hκ
    have hzero : (4 * kappa k N * kappa k N - 4 * (kappa k N + 1) ^ 2)
        / (kappa k N * (kappa k N + 1) ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnum hden.le
    linarith
  linarith

end Qatlib.Papers.HamLCUSim12.Multiproduct.Corollary7Delta
