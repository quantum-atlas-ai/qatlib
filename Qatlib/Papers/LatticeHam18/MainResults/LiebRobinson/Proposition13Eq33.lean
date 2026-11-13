/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatticeHam18.MainResults.Model.LatticeModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lieb-Robinson Weighted Decay Estimate (Proposition 13, Eq. 33)

This module proves Eq. (33) of Proposition 13: under the local interaction decay
assumption `∑_{Z ∋ x} w(Z) |Z|^2 exp(μ diam(Z)) ≤ ζ`, the sum of weights `w(Q)` over
subsets `Q` intersecting both `P` and `S` is bounded by `ζ ∑_{p ∈ P} exp(-μ dist(p, S))`.

## Main statements

* `distTo_le_diam`: `dist(p, S) ≤ diam(Q)` whenever `p ∈ Q` and `Q ∩ S` is nonempty.
* `sum_through_site`: single-site Lieb-Robinson decay sum bound.
* `proposition13_eq33`: Proposition 13, Eq. (33) decay bound across `P` and `S`.

## References

* [Haah et al., 2018][HaahHastingsKothariLow2018], Proposition 13, Eq. (33), p. 24.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.LatticeHam18.MainResults.LiebRobinson

open Qatlib.Papers.LatticeHam18.MainResults.Model

variable {Site : Type} [DecidableEq Site]

/-- `dist(p, S) ≤ diam(Q)` when `p ∈ Q` and `Q` meets `S`. -/
lemma distTo_le_diam (d : SiteMetric (Site := Site)) {Q S : Finset Site} {p : Site}
    (hS : S.Nonempty) (hQS : (Q ∩ S).Nonempty) (hp : p ∈ Q) :
    distTo d p S ≤ diam d Q := by
  obtain ⟨s, hs⟩ := hQS
  rw [Finset.mem_inter] at hs
  obtain ⟨hsQ, hsS⟩ := hs
  have hQ : Q.Nonempty := ⟨p, hp⟩
  have h1 : distTo d p S ≤ d p s := by
    simp only [distTo, hS, ↓reduceDIte]
    exact Finset.inf'_le (f := fun y => d p y) hsS
  have h2 : d p s ≤ diam d Q := by
    simp only [diam, hQ, ↓reduceDIte]
    refine le_trans ?_ (Finset.le_sup' (f := fun x => Q.sup' hQ (fun y => d x y)) hp)
    exact Finset.le_sup' (f := fun y => d p y) hsQ
  exact le_trans h1 h2

variable [Fintype Site]

/-- Single-site version of Eq. (33): the sum over `Q` containing `p` and meeting `S`
is at most `ζ e^{-μ dist(p, S)}`. -/
lemma sum_through_site
    (d : SiteMetric (Site := Site)) (w : Finset Site → ℝ)
    (hw : ∀ X : Finset Site, 0 ≤ w X) (ζ μ : ℝ) (_hζ : 0 < ζ) (hμ : 0 < μ)
    (h15 : ∀ x : Site,
      ∑ Z ∈ Finset.univ.filter (fun Z : Finset Site => x ∈ Z),
          w Z * ((Z.card : ℝ) ^ 2) * Real.exp (μ * diam d Z) ≤ ζ)
    (S : Finset Site) (hS : S.Nonempty) (p : Site) :
    ∑ Q ∈ Finset.univ.filter (fun Q : Finset Site => p ∈ Q ∧ (Q ∩ S).Nonempty), w Q ≤
      ζ * Real.exp (-μ * distTo d p S) := by
  have hterm : ∀ Q ∈ Finset.univ.filter (fun Q : Finset Site => p ∈ Q ∧ (Q ∩ S).Nonempty),
      w Q ≤ (w Q * ((Q.card : ℝ) ^ 2) * Real.exp (μ * diam d Q)) *
        Real.exp (-μ * distTo d p S) := by
    intro Q hQ
    rw [Finset.mem_filter] at hQ
    obtain ⟨-, hpQ, hQS⟩ := hQ
    have hQne : Q.Nonempty := ⟨p, hpQ⟩
    have hcardNat : 1 ≤ Q.card := Nat.succ_le_of_lt (Finset.card_pos.mpr hQne)
    have h1 : (1 : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hcardNat
    have hcard1 : (1 : ℝ) ≤ ((Q.card : ℝ) ^ 2) := by nlinarith
    have hdd : distTo d p S ≤ diam d Q := distTo_le_diam d hS hQS hpQ
    have hexp : 1 ≤ Real.exp (μ * diam d Q) * Real.exp (-μ * distTo d p S) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have h : (0 : ℝ) ≤ μ * (diam d Q - distTo d p S) :=
        mul_nonneg hμ.le (sub_nonneg.mpr hdd)
      nlinarith
    have hexp_nonneg : (0 : ℝ) ≤ Real.exp (μ * diam d Q) * Real.exp (-μ * distTo d p S) :=
      le_of_lt (mul_pos (Real.exp_pos _) (Real.exp_pos _))
    have hcard_nonneg : (0 : ℝ) ≤ ((Q.card : ℝ) ^ 2) := by positivity
    have hk : 1 ≤ ((Q.card : ℝ) ^ 2) *
        (Real.exp (μ * diam d Q) * Real.exp (-μ * distTo d p S)) := by
      simpa using mul_le_mul hcard1 hexp zero_le_one hcard_nonneg
    have hwQ : (0 : ℝ) ≤ w Q := hw Q
    calc w Q = w Q * 1 := (mul_one _).symm
      _ ≤ w Q * (((Q.card : ℝ) ^ 2) *
            (Real.exp (μ * diam d Q) * Real.exp (-μ * distTo d p S))) :=
          mul_le_mul_of_nonneg_left hk hwQ
      _ = (w Q * ((Q.card : ℝ) ^ 2) * Real.exp (μ * diam d Q)) *
            Real.exp (-μ * distTo d p S) := by ring
  calc ∑ Q ∈ Finset.univ.filter (fun Q : Finset Site => p ∈ Q ∧ (Q ∩ S).Nonempty), w Q
      ≤ ∑ Q ∈ Finset.univ.filter (fun Q : Finset Site => p ∈ Q ∧ (Q ∩ S).Nonempty),
          (w Q * ((Q.card : ℝ) ^ 2) * Real.exp (μ * diam d Q)) *
            Real.exp (-μ * distTo d p S) := Finset.sum_le_sum hterm
    _ = (∑ Q ∈ Finset.univ.filter (fun Q : Finset Site => p ∈ Q ∧ (Q ∩ S).Nonempty),
          w Q * ((Q.card : ℝ) ^ 2) * Real.exp (μ * diam d Q)) *
          Real.exp (-μ * distTo d p S) := by rw [Finset.sum_mul]
    _ ≤ ζ * Real.exp (-μ * distTo d p S) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (h15 p)
        · intro Q hQ
          rw [Finset.mem_filter] at hQ ⊢
          exact ⟨Finset.mem_univ _, hQ.2.1⟩
        · intro Q _ _
          exact mul_nonneg (mul_nonneg (hw Q) (by positivity)) (Real.exp_pos _).le

/-- Proposition 13, Eq. (33):
`∑_{Q : P ∼ Q ∼ S} w Q ≤ ζ ∑_{p ∈ P} e^{-μ dist(p, S)}`. -/
theorem proposition13_eq33
    (d : SiteMetric (Site := Site)) (w : Finset Site → ℝ)
    (hw : ∀ X : Finset Site, 0 ≤ w X) (ζ μ : ℝ) (_hζ : 0 < ζ) (hμ : 0 < μ)
    (h15 : ∀ x : Site,
      ∑ Z ∈ Finset.univ.filter (fun Z : Finset Site => x ∈ Z),
          w Z * ((Z.card : ℝ) ^ 2) * Real.exp (μ * diam d Z) ≤ ζ)
    (P S : Finset Site) (hS : S.Nonempty) :
    ∑ Q ∈ Finset.univ.filter (fun Q : Finset Site =>
        (Q ∩ P).Nonempty ∧ (Q ∩ S).Nonempty), w Q ≤
      ζ * ∑ p ∈ P, Real.exp (-μ * distTo d p S) := by
  set F := Finset.univ.filter (fun Q : Finset Site =>
    (Q ∩ P).Nonempty ∧ (Q ∩ S).Nonempty) with hF
  have hstepA : ∑ Q ∈ F, w Q ≤ ∑ Q ∈ F, ∑ p ∈ P, (if p ∈ Q then w Q else 0) := by
    apply Finset.sum_le_sum
    intro Q hQ
    have hQF : Q ∈ F := hQ
    rw [hF, Finset.mem_filter] at hQF
    obtain ⟨-, hQP, _hQS⟩ := hQF
    obtain ⟨p, hp⟩ := hQP
    rw [Finset.mem_inter] at hp
    obtain ⟨hpQ, hpP⟩ := hp
    have h0 : ∀ p' ∈ P, 0 ≤ (if p' ∈ Q then w Q else 0) := by
      intro p' _
      split_ifs with h
      · exact hw Q
      · exact le_refl 0
    have := Finset.single_le_sum h0 hpP
    simpa [hpQ] using this
  calc ∑ Q ∈ F, w Q
      ≤ ∑ Q ∈ F, ∑ p ∈ P, (if p ∈ Q then w Q else 0) := hstepA
    _ = ∑ p ∈ P, ∑ Q ∈ F, (if p ∈ Q then w Q else 0) := by rw [Finset.sum_comm]
    _ = ∑ p ∈ P, ∑ Q ∈ F.filter (fun Q : Finset Site => p ∈ Q), w Q := by
        apply Finset.sum_congr rfl
        intro p _
        simpa using (Finset.sum_filter (s := F)
          (p := fun Q : Finset Site => p ∈ Q) (f := fun Q => w Q)).symm
    _ ≤ ∑ p ∈ P, ζ * Real.exp (-μ * distTo d p S) := by
        apply Finset.sum_le_sum
        intro p _
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
          (sum_through_site d w hw ζ μ _hζ hμ h15 S hS p)
        · intro Q hQ
          rw [Finset.mem_filter] at hQ
          obtain ⟨hQF, hpQ⟩ := hQ
          have hQF' : Q ∈ F := hQF
          rw [hF, Finset.mem_filter] at hQF'
          obtain ⟨-, _hQP, hQS⟩ := hQF'
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpQ, hQS⟩
        · intro Q _ _
          exact hw Q
    _ = ζ * ∑ p ∈ P, Real.exp (-μ * distTo d p S) := by rw [Finset.mul_sum]

end Qatlib.Papers.LatticeHam18.MainResults.LiebRobinson
