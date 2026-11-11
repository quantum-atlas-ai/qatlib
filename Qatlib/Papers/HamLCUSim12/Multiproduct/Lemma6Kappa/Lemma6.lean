/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductKappaBoundHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductMassStructureHami

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 6 (Eq. (30)) — lower bound on the success-probability ratio kappa

Fixed source: arXiv:1202.5822v1, Lemma 6, p.7, Eq. (30):
if `2 k^2 <= e^{2 gamma (k+1)}` and `k > 0`, then
`kappa >= 2^{-1/2} e^{-2k(1 + log(eta)/2 - gamma) - log(k^{5/2})}`,
with `kappa = Sigma_+ / Sigma_-` as in Theorem 3 and `eta` as in Eq. (21).

Proof route (the paper's, Eqs. (31)-(35)): the negative mass is at most
`2^{-1/2} k^{-5/2} e^{-2k(1+log(eta)/2-gamma)}` times the positive mass
(frozen `MultiproductKappaBound.multiproductKappaBound`, itself built from Lemma 5
and the mass structure), and the mass structure guarantees both masses are strictly
positive when `N = e^{gamma(k+1)} > k`; `N > k` follows from `2k^2 <= N^2`.  Dividing
gives the claim.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma6Kappa

open Qatlib.Papers.HamLCUSim12.Multiproduct

/-- Negative sign mass `Sigma_- := sum_{C_q < 0} |C_q|` of Theorem 3 / Lemma 6. -/
def negMass (k : ℕ) (N : ℝ) : ℝ :=
  ∑ q ∈ Finset.univ.filter (fun q : Fin (k + 1) => mCoeff k N q < 0), |mCoeff k N q|

/-- Positive sign mass `Sigma_+ := sum_{C_q > 0} C_q` of Theorem 3 / Lemma 6. -/
def posMass (k : ℕ) (N : ℝ) : ℝ :=
  ∑ q ∈ Finset.univ.filter (fun q : Fin (k + 1) => 0 < mCoeff k N q), mCoeff k N q

/-- `kappa := Sigma_+ / Sigma_-`. -/
def kappa (k : ℕ) (N : ℝ) : ℝ := posMass k N / negMass k N

/-- Lemma 6 p.7: under the mass-structure regime `N > k` some coefficient is
negative, so `Sigma_- > 0`. -/
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

/-- Fixed arXiv:1202.5822v1, Lemma 6 Eq. (30) with the logarithmic factor split:
the bound `2^{-1/2} e^{-2k(1+log(eta)/2-gamma)} k^{-5/2}` (equal to the printed
`2^{-1/2} e^{-2k(1+log(eta)/2-gamma)-log(k^{5/2})}` for `k > 0`) is a lower bound for
`kappa = Sigma_+/Sigma_-`. -/
theorem lemma6_kappa_bound (k : ℕ) (hk : 1 ≤ k) (γ η : ℝ)
    (hγ : 0 < γ) (hη : 1 / 4 < η) (hEta : EtaMaxProperty η)
    (hFact : FactorialLowerBound)
    (hcond : 2 * (k : ℝ) ^ 2 ≤ Real.exp (2 * γ * ((k + 1 : ℕ) : ℝ))) :
    (2 : ℝ) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * (k : ℝ)) * (1 + Real.log η / 2 - γ))
        * (k : ℝ) ^ (-(5 : ℝ) / 2)
      ≤ kappa k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) := by
  set N : ℝ := Real.exp (γ * ((k + 1 : ℕ) : ℝ)) with hNdef
  have hNpos : 0 < N := Real.exp_pos _
  have hsq : N ^ 2 = Real.exp (2 * γ * ((k + 1 : ℕ) : ℝ)) := by
    rw [hNdef, sq, ← Real.exp_add]
    congr 1
    ring
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hlt : (k : ℝ) ^ 2 < N ^ 2 := by
    rw [hsq]
    nlinarith
  have hN : (k : ℝ) < N := by
    by_contra h
    push_neg at h
    have hle : N ^ 2 ≤ (k : ℝ) ^ 2 := by
      have hsqle := mul_self_le_mul_self hNpos.le h
      simpa [sq] using hsqle
    nlinarith
  have hneg := negMass_pos hk hN
  have hmb := multiproductKappaBound k hk γ η hγ hη hEta hFact hcond
  have hmb' : negMass k N *
      ((2 : ℝ) ^ (-(1 : ℝ) / 2) * (k : ℝ) ^ (-(5 : ℝ) / 2)
        * Real.exp (-(2 * (k : ℝ)) * (1 + Real.log η / 2 - γ))) ≤ posMass k N := hmb
  unfold kappa
  rw [le_div_iff₀ hneg]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hmb'

/-- Fixed arXiv:1202.5822v1, Lemma 6 Eq. (30) in the printed form (single exponential
`e^{-2k(1+log(eta)/2-gamma) - log(k^{5/2})}`). -/
theorem lemma6_kappa_bound_printed (k : ℕ) (hk : 1 ≤ k) (γ η : ℝ)
    (hγ : 0 < γ) (hη : 1 / 4 < η) (hEta : EtaMaxProperty η)
    (hFact : FactorialLowerBound)
    (hcond : 2 * (k : ℝ) ^ 2 ≤ Real.exp (2 * γ * ((k + 1 : ℕ) : ℝ))) :
    (2 : ℝ) ^ (-(1 : ℝ) / 2) *
        Real.exp (-(2 * (k : ℝ)) * (1 + Real.log η / 2 - γ) - Real.log ((k : ℝ) ^ ((5 : ℝ) / 2)))
      ≤ kappa k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkpow : (0 : ℝ) < (k : ℝ) ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hkpos _
  have hsplit : Real.exp (-(2 * (k : ℝ)) * (1 + Real.log η / 2 - γ)
        - Real.log ((k : ℝ) ^ ((5 : ℝ) / 2)))
      = Real.exp (-(2 * (k : ℝ)) * (1 + Real.log η / 2 - γ)) *
          (k : ℝ) ^ (-(5 : ℝ) / 2) := by
    rw [Real.exp_sub, Real.exp_log hkpow, div_eq_mul_inv, ← Real.rpow_neg hkpos.le, neg_div]
  rw [hsplit]
  simpa [mul_assoc] using lemma6_kappa_bound k hk γ η hγ hη hEta hFact hcond

end Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma6Kappa
