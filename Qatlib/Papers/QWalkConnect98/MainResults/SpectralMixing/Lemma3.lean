/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkConnect98.MainResults.SpectralMixing.MixingContraction
import Qatlib.Papers.QWalkConnect98.MainResults.SpectralMixing.SpectralGapProof

/-!
# Mixing of the projected connectivity walk

`lemma3State` measures the difference between a column of `walkQ ^ k` and the uniform vector on
the source component, embedded on diagonal pairs. The identity `lemma3State_eq_diagLift` reduces
this difference to the vertex-space walk `walkM`.

The mixing theorems bound its Euclidean norm by any positive `ε` after the explicit logarithmic
step threshold, first assuming `SpectralGap` and then deriving it from regularity. These results
support the connectivity analysis in [Watrous1998].

## Main statements

* `lemma3State_eq_diagLift`: identify the pair-space error with the lifted vertex-space error.
* `lemma3_mixing`: an explicit mixing bound under `SpectralGap`.
* `lemma3_mixing_uncond`: the mixing bound for regular graphs of degree at least two.

## References

* [Watrous, 1998][Watrous1998]
-/

set_option warningAsError false

namespace Qatlib.Papers.QWalkConnect98.MainResults.SpectralMixing

open Finset
open Qatlib.Papers.QWalkConnect98.MainResults.WalkOperator
open scoped BigOperators Matrix

set_option autoImplicit false
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The column of `walkQ G d ^ k` starting at `(u, u)`, minus the uniform vector on diagonal
pairs in the component of `u`. -/
def lemma3State (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (k : ℕ) (u : V) :
    V × V → ℝ := by
  classical
  exact fun p => (walkQ G d ^ k) p (u, u) -
    (if p.1 = p.2 ∧ G.Reachable u p.1 then 1 / (compSize G u : ℝ) else 0)

/-- The projected-walk error is the diagonal lift of the difference between the vertex-walk
distribution and `uniformOn G u`. -/
theorem lemma3State_eq_diagLift (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (k : ℕ) (u : V) :
    lemma3State G d k u =
      diagLift ((walkM G d ^ k) *ᵥ basisVec u - uniformOn G u) := by
  classical
  funext p
  rw [lemma3State, diagLift_apply]
  by_cases hp : p.1 = p.2
  · rw [if_pos hp]
    have hp' : p = (p.1, p.1) := by ext <;> simp [hp]
    rw [hp', walkQ_pow_apply_diag]
    by_cases hr : G.Reachable u p.1
    · simp [uniformOn, hr]
    · simp [uniformOn, hr]
  · rw [if_neg hp, walkQ_pow_apply_offdiag G d k u hp]
    simp [hp]

/-- For a regular graph of degree at least two with the assumed component spectral gap, the
stated step threshold makes the Euclidean norm of `lemma3State` strictly less than any
positive `ε`. -/
theorem lemma3_mixing (G : SimpleGraph V) [DecidableRel G.Adj] {d ε : ℝ}
    (hreg : RegularDegree G d) (hd : 2 ≤ d) (hε : 0 < ε) (u : V)
    (hgap : SpectralGap G d u) (k : ℕ)
    (hk : (d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2 / 8) * Real.log (1 / ε) ≤
      (k : ℝ)) :
    l2norm (lemma3State G d k u) < ε := by
  classical
  rw [lemma3State_eq_diagLift, l2norm_diagLift]

  have hdiff : (walkM G d ^ k) *ᵥ basisVec u - uniformOn G u =
      (walkM G d ^ k) *ᵥ (basisVec u - uniformOn G u) := by
    rw [Matrix.mulVec_sub, walkM_pow_mulVec_uniformOn G hreg]
  rw [hdiff]

  have hsupp : ∀ v, ¬ G.Reachable u v → (basisVec u - uniformOn G u) v = 0 := by
    intro v hv
    have hne : v ≠ u := fun h => hv (h ▸ SimpleGraph.Reachable.rfl)
    have hu : uniformOn G u v = 0 := by simp [uniformOn, hv]
    rw [Pi.sub_apply, hu, basisVec_apply_of_ne hne, sub_zero]
  have hsum0 : ∑ v, (basisVec u - uniformOn G u) v = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [sum_uniformOn]
    have hone : (∑ v, basisVec u v) = 1 := by
      simp [basisVec, Finset.sum_ite_eq']
    rw [hone]
    ring

  have hd0 : (0 : ℝ) < d := by linarith
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := by
    have hv : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
    exact_mod_cast hv
  have hd1 : (0 : ℝ) < d + 1 := by linarith
  have hn1 : (1 : ℝ) ≤ (compSize G u : ℝ) := by
    exact_mod_cast compSet_pos G u
  have hsqu : (0 : ℝ) < d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2 := by
    have h1 : (0 : ℝ) < (d + 1) ^ 2 := pow_pos hd1 2
    have h2 : (0 : ℝ) < (compSize G u : ℝ) ^ 2 := pow_pos (by linarith) 2
    exact mul_pos (mul_pos hd0 h1) h2
  have hsqn : (0 : ℝ) < d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2 := by
    have h1 : (0 : ℝ) < (d + 1) ^ 2 := pow_pos hd1 2
    have h2 : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 := pow_pos hcard 2
    exact mul_pos (mul_pos hd0 h1) h2
  set delta : ℝ := 8 / (d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2) with hdelta
  have hdelta_pos : (0 : ℝ) < delta := div_pos (by norm_num) hsqn

  have hlog : Real.log (1 / ε) ≤ delta * (k : ℝ) := by
    have hc : delta * (d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2 / 8) = 1 := by
      rw [hdelta, div_mul_div_comm,
        mul_comm 8 (d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2)]
      exact div_self (ne_of_gt (mul_pos hsqn (by norm_num)))
    have hmul := mul_le_mul_of_nonneg_left hk hdelta_pos.le
    calc Real.log (1 / ε) = 1 * Real.log (1 / ε) := (one_mul _).symm
      _ = (delta * (d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2 / 8)) *
            Real.log (1 / ε) := by rw [hc]
      _ = delta * ((d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2 / 8) *
            Real.log (1 / ε)) := by ring
      _ ≤ delta * (k : ℝ) := hmul

  have hexp_eq : Real.exp (-Real.log (1 / ε)) = ε := by
    rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr hε), one_div, inv_inv]

  have hkey : l2norm ((walkM G d ^ k) *ᵥ (basisVec u - uniformOn G u)) ≤
      (1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2)) ^ k := by
    have hcontr := l2norm_walkM_pow_le G hreg hd u hgap (basisVec u - uniformOn G u) hsupp hsum0 k
    have hinit : l2norm (basisVec u - uniformOn G u) ≤ 1 :=
      l2norm_basisVec_sub_uniformOn_le_one G u
    have hρ : (0 : ℝ) ≤ 1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2) :=
      (spectral_coeff_pos G hd u).le
    calc l2norm ((walkM G d ^ k) *ᵥ (basisVec u - uniformOn G u))
        ≤ (1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2)) ^ k *
            l2norm (basisVec u - uniformOn G u) := hcontr
      _ ≤ (1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2)) ^ k * 1 := by
        apply mul_le_mul_of_nonneg_left hinit (pow_nonneg hρ k)
      _ = (1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2)) ^ k := mul_one _

  have hcomp_le : (compSize G u : ℝ) ≤ (Fintype.card V : ℝ) := by
    have h : compSize G u ≤ Fintype.card V := Finset.card_le_univ _
    exact_mod_cast h
  have hfrac_le : 8 / (d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2) ≤
      8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ hsqn hsqu]
    have hsq_le : d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2 ≤
        d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (by linarith : (0 : ℝ) ≤ d) (by positivity : (0 : ℝ) ≤ (d + 1) ^ 2))
      exact pow_le_pow_left₀ (by positivity) hcomp_le 2
    nlinarith
  have hρle : 1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2) ≤ 1 - delta := by
    rw [hdelta]
    linarith
  have hρ_u_nonneg : (0 : ℝ) ≤ 1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2) :=
    (spectral_coeff_pos G hd u).le
  have hdelta_le_four : delta ≤ 4 / 9 := by
    rw [hdelta]
    rw [div_le_iff₀ hsqn]
    have h18 : (18 : ℝ) ≤ d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2 := by
      have h9 : (9 : ℝ) ≤ (d + 1) ^ 2 := by
        have h := mul_nonneg (by linarith : (0 : ℝ) ≤ d + 4) (by linarith : (0 : ℝ) ≤ d - 2)
        nlinarith [h]
      have h18a : (18 : ℝ) ≤ d * (d + 1) ^ 2 := by
        have := mul_le_mul hd h9 (by norm_num) hd0.le
        nlinarith [this]
      have hc1 : (1 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
        have h := mul_nonneg (by linarith : (0 : ℝ) ≤ (Fintype.card V : ℝ) - 1)
          (by linarith : (0 : ℝ) ≤ (Fintype.card V : ℝ) + 1)
        nlinarith [h]
      have := mul_le_mul h18a hc1 (by norm_num) (by linarith)
      nlinarith [this]
    nlinarith [h18]

  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hlog0 : Real.log (1 / ε) ≤ 0 := by simpa using hlog
    have hε1 : 1 / ε ≤ 1 := by
      by_contra hcon
      have : 0 < Real.log (1 / ε) := Real.log_pos (by linarith)
      linarith
    have hεge : 1 ≤ ε := by
      rw [div_le_one hε] at hε1
      exact hε1
    have hlt : l2norm ((walkM G d ^ 0) *ᵥ (basisVec u - uniformOn G u)) < 1 := by
      simpa using l2norm_basisVec_sub_uniformOn_lt_one G u
    linarith
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hkpos)
    have hne : delta ≠ 0 := ne_of_gt hdelta_pos
    have hstep : (1 : ℝ) - delta < Real.exp (-delta) := Real.one_sub_lt_exp_neg hne
    have hnonneg : (0 : ℝ) ≤ 1 - delta := by linarith
    have hpow : (1 - delta) ^ (m + 1) < (Real.exp (-delta)) ^ (m + 1) :=
      pow_lt_pow_left₀ hstep hnonneg (Nat.succ_ne_zero m)
    have hexp_pow : (Real.exp (-delta)) ^ (m + 1) =
        Real.exp (-(delta * (((m + 1 : ℕ)) : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    calc l2norm ((walkM G d ^ (m + 1)) *ᵥ (basisVec u - uniformOn G u))
        ≤ (1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2)) ^ (m + 1) := hkey
      _ ≤ (1 - delta) ^ (m + 1) := pow_le_pow_left₀ hρ_u_nonneg hρle (m + 1)
      _ < Real.exp (-(delta * ((m + 1 : ℕ) : ℝ))) := by
        rw [← hexp_pow]
        exact hpow
      _ ≤ Real.exp (-Real.log (1 / ε)) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = ε := hexp_eq

/-- For a regular graph of degree at least two, the stated step threshold makes the Euclidean
norm of `lemma3State` strictly less than any positive `ε`. See [Watrous1998]. -/
theorem lemma3_mixing_uncond (G : SimpleGraph V) [DecidableRel G.Adj] {d ε : ℝ}
    (hreg : RegularDegree G d) (hd : 2 ≤ d) (hε : 0 < ε) (u : V) (k : ℕ)
    (hk : (d * (d + 1) ^ 2 * (Fintype.card V : ℝ) ^ 2 / 8) * Real.log (1 / ε) ≤
      (k : ℝ)) :
    l2norm (lemma3State G d k u) < ε :=
  lemma3_mixing G hreg hd hε u (spectralGap_of_regular G hreg hd u) k hk

end

end Qatlib.Papers.QWalkConnect98.MainResults.SpectralMixing
