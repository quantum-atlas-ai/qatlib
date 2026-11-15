/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDistribution

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

/-- Finds a subset whose total weight lies between the target and the target plus the largest
allowed atom weight. -/
theorem finite_weight_subset_overshoot {α : Type} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (_hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    (q δ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hδ : 0 ≤ δ) (hatom : ∀ x, w x ≤ δ) :
    ∃ S : Finset α, q ≤ ∑ x ∈ S, w x ∧ (∑ x ∈ S, w x) ≤ q+δ := by
  rcases hq0.eq_or_lt with hq | hq
  · refine ⟨∅, ?_, ?_⟩ <;> simp [← hq, hδ]
  · have he : ∃ k : ℕ, ∃ S : Finset α, S.card=k ∧ q ≤ ∑ x ∈ S, w x :=
      ⟨Fintype.card α, Finset.univ, by simp, by simpa [hsum] using hq1⟩
    let k := Nat.find he
    obtain ⟨S,hSc,hSq⟩ := Nat.find_spec he
    have hS : S.Nonempty := by
      by_contra hh
      have hs : S=∅ := Finset.not_nonempty_iff_eq_empty.1 hh
      rw [hs, Finset.sum_empty] at hSq
      linarith
    obtain ⟨x,hx⟩ := hS
    have hc : (S.erase x).card < k := by
      change (S.erase x).card < Nat.find he
      rw [← hSc]
      exact Finset.card_erase_lt_of_mem hx
    have hl : (∑ y ∈ S.erase x, w y) < q := by
      by_contra hh
      exact Nat.find_min he hc ⟨S.erase x, rfl, le_of_not_gt hh⟩
    have hs := Finset.sum_erase_add S w hx
    refine ⟨S,hSq,?_⟩
    linarith [hatom x]

/-- Bounds each product-measure atom by the stated exponential decay in the dimension. -/
theorem muWeight_atom_bound {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ)
    (x : Fin m → Bool) : muWeight p m x ≤ (2 : ℝ)^(-(min p (1-p)*m)) := by
  let a := min p (1-p)
  have ha0 : 0 < a := lt_min hp0 (by linarith)
  have ha1 : a ≤ 1 := (min_le_left _ _).trans hp1.le
  have hfactor (i : Fin m) : (if x i then p else 1-p) ≤ 1-a := by
    split_ifs <;> dsimp [a] <;> linarith [min_le_left p (1-p),min_le_right p (1-p)]
  have hprod : muWeight p m x ≤ (1-a)^m := by
    have h := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun i : Fin m => if x i then p else 1-p) (g := fun _ => 1-a)
      (fun i _ => by change 0 ≤ (if x i then p else 1-p); split_ifs <;> linarith) (fun i _ => hfactor i)
    simpa only [muWeight, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  have he : 1-a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
  have hpow : (1-a)^m ≤ Real.exp (-a)^m := pow_le_pow_left₀ (by linarith) he m
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hneg : -(a*(m : ℝ)) ≤ 0 := by apply neg_nonpos.2; positivity
  have hcmp := mul_le_mul_of_nonpos_right hlog hneg
  rw [one_mul] at hcmp
  have hexp := Real.exp_le_exp.2 hcmp
  rw [← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at hexp
  apply hprod.trans (hpow.trans _)
  rw [← Real.exp_nat_mul]
  rw [show (m : ℝ)*(-a) = -(a*m) by ring]
  exact hexp

end Qatlib.Concepts.ProbabilityCore.DistributionAA
