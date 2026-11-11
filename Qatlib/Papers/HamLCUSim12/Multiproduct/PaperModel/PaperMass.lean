/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductMassStructureHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductKappaBoundHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductGammaThresholdHami

set_option backward.isDefEq.respectTransparency false

/-!
# Paper-level sign masses of a multi-product formula (HamLCUSim12)

Fixed source: arXiv:1202.5822v1, Definition 1 p.5 Eq. (17) and Theorem 3 p.3.
The paper's `kappa := (sum of positive C_q)/(sum of |C_q| over negative C_q)` is the
ratio written here as `kappa k N = posMass k N / negMass k N`, where `N = e^{gamma(k+1)}`
is the last repetition node of Eq. (16).

Everything is stated on top of the frozen coefficient system
`QuantumAlgorithm.Papers.HamLCUSim12.Multiproduct.mCoeff`/`mNode`; no coefficient is
redefined here. This module only introduces the two partial sign masses used by
Lemma 6, Corollary 7 and Theorem 3, and proves their positivity from the frozen
mass-structure statement (`multiproductMassStructure`).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HamLCUSim12.Multiproduct.PaperModel

open Qatlib.Papers.HamLCUSim12.Multiproduct

/-- Positive sign mass `Sigma_+ := sum_{C_q > 0} C_q` of Theorem 3 / Lemma 6. -/
def posMass (k : ℕ) (N : ℝ) : ℝ :=
  ∑ q ∈ Finset.univ.filter (fun q : Fin (k + 1) => 0 < mCoeff k N q), mCoeff k N q

/-- Negative sign mass `Sigma_- := sum_{C_q < 0} |C_q|` of Theorem 3 / Lemma 6. -/
def negMass (k : ℕ) (N : ℝ) : ℝ :=
  ∑ q ∈ Finset.univ.filter (fun q : Fin (k + 1) => mCoeff k N q < 0), |mCoeff k N q|

/-- Theorem 3 / Lemma 6 ratio `kappa := Sigma_+ / Sigma_-`. -/
def kappa (k : ℕ) (N : ℝ) : ℝ := posMass k N / negMass k N

/-- Fixed arXiv:1202.5822v1, Lemma 6 p.7 (and the `C_{k+1} >= 1` observation before
Corollary 7): under the mass-structure regime `N > k`, the positive mass is strictly
positive.  The last node `ell_{k+1} = N` has coefficient at least `1`. -/
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

/-- Fixed arXiv:1202.5822v1, Lemma 6 p.7: under the mass-structure regime `N > k` some
coefficient is negative, hence the negative sign mass is strictly positive. -/
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

/-- `kappa > 0` whenever both sign masses are positive. -/
theorem kappa_pos {k : ℕ} {N : ℝ} (hk : 1 ≤ k) (hN : (k : ℝ) < N) :
    0 < kappa k N := by
  unfold kappa
  exact div_pos (posMass_pos hk hN) (negMass_pos hk hN)

/-- The retry bound `k^2 e^{-2 gamma (k+1)} <= 1/2` of Corollary 7 forces the last
repetition node `N = e^{gamma(k+1)}` to exceed `k`, i.e. the mass-structure regime
`N > k` used by Lemmas 6 and Corollary 7. -/
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
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlt : (k : ℝ) ^ 2 < N ^ 2 := by nlinarith [sq_pos_of_pos hNpos]
  by_contra hcon
  push_neg at hcon
  have hle : N ^ 2 ≤ (k : ℝ) ^ 2 := by
    have hsqle := mul_self_le_mul_self hNpos.le hcon
    simpa [sq] using hsqle
  nlinarith

end Qatlib.Papers.HamLCUSim12.Multiproduct.PaperModel
