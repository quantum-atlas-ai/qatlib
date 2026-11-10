/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterDefectAlgebra
set_option warningAsError false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix Set Filter
open scoped Classical BigOperators Matrix.Norms.L2Operator ContDiff Topology
variable {I : Type} [Fintype I] [DecidableEq I]

theorem pfTaylorBefore_sub (f g : ℝ→Matrix I I ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (p : ℕ) (t : ℝ) : pfTaylorBefore (fun u=>f u-g u) p t=pfTaylorBefore f p t-pfTaylorBefore g p t := by
  unfold pfTaylorBefore
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [iteratedDeriv_fun_sub (hf.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)))
    (hg.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))),smul_sub]

theorem pfTaylorBefore_sum {J : Type} [Fintype J] (f : J→ℝ→Matrix I I ℂ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (p : ℕ) (t : ℝ) :
    pfTaylorBefore (fun u=>∑ j : J,f j u) p t=∑ j : J,pfTaylorBefore (f j) p t := by
  unfold pfTaylorBefore
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [iteratedDeriv_fun_sum (fun j _=>(hf j).contDiffAt.of_le
    (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))),Finset.smul_sum]

theorem pfTaylorBefore_const (C : Matrix I I ℂ) (p : ℕ) (hp : 1≤p) (t : ℝ) :
    pfTaylorBefore (fun _ : ℝ=>C) p t=C := by
  unfold pfTaylorBefore
  simp_rw [iteratedDeriv_const]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro n _ hn
    simp [hn]
  · simp only [Finset.mem_range]
    omega

theorem pfLeftGenerator_defect_jets (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (p : ℕ)
    (hc : ∀ n≤p,suzukiSeries xs n=((n.factorial:ℝ)⁻¹) • H^n) :
    ∀ j<p,iteratedDeriv j (fun t=>pfLeftGenerator xs t-H) 0=0 := by
  have hfour := general_trotter_four_order_conditions I H (suzukiExponentialWord xs) p
    (general_trotter_word_contDiff xs) (by simp [suzukiExponentialWord])
  have horder := hfour.2.1.mp (hfour.1.mp (general_trotter_word_order xs H p hc))
  simp only [pf_actual_left_defect] at horder
  exact (trotter_matrix_order_jets _ p ((pfLeftGenerator_contDiff xs).sub contDiff_const)).mp horder

theorem pf_defect_prefix_polynomial_zero (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (p : ℕ)
    (hp : 1≤p) (hc : ∀ n≤p,suzukiSeries xs n=((n.factorial:ℝ)⁻¹) • H^n) (t : ℝ) :
    (∑ j : Fin xs.length,pfConjTrunc (xs.take j.val) (xs.getD j.val 0) p t)-H=0 := by
  have hz : pfTaylorBefore (fun u=>pfLeftGenerator xs u-H) p t=0 := by
    unfold pfTaylorBefore
    apply Finset.sum_eq_zero
    intro n hn
    rw [pfLeftGenerator_defect_jets xs H p hc n (Finset.mem_range.mp hn),smul_zero]
  have he : (fun u=>pfLeftGenerator xs u-H)=(fun u=>(∑ j : Fin xs.length,pfConjWord (xs.take j.val) (xs.getD j.val 0) u)-H) := by
    funext u
    rw [pfLeftGenerator_prefix_sum]
  rw [he,pfTaylorBefore_sub _ _ (ContDiff.sum (fun _ _=>pfConjWord_contDiff _ _)) contDiff_const,
    pfTaylorBefore_const H p hp t,pfTaylorBefore_sum _ (fun _=>pfConjWord_contDiff _ _)] at hz
  simpa only [pfConjWord_taylor_before] using! hz

theorem pf_mass_take_le (xs : List (Matrix I I ℂ)) (n : ℕ) : suzukiMass (xs.take n)≤ suzukiMass xs := by
  have he : suzukiMass xs=suzukiMass (xs.take n)+suzukiMass (xs.drop n) := by
    conv_lhs => rw [← List.take_append_drop n xs]
    simp only [suzukiMass,List.map_append,List.sum_append]
  linarith [general_trotter_mass_nonneg (xs.drop n)]

theorem pfWordInflation_take_le (skew : Bool) (xs : List (Matrix I I ℂ)) (n : ℕ) (t : ℝ) :
    pfWordInflation skew (xs.take n) t≤pfWordInflation skew xs t := by
  cases skew
  · rw [pfWordInflation_false,pfWordInflation_false]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (pf_mass_take_le xs n) (by positivity)
  · simp only [pfWordInflation_true,le_refl]

theorem pfLeftGenerator_defect_norm_mode (skew : Bool) (xs : List (Matrix I I ℂ))
    (H : Matrix I I ℂ) (p : ℕ) (t : ℝ) (hp : 1≤p)
    (hc : ∀ n≤p,suzukiSeries xs n=((n.factorial:ℝ)⁻¹) • H^n)
    (hxs : skew=true→∀ X∈xs,Xᴴ=-X) :
    ‖pfLeftGenerator xs t-H‖≤pfCommAlphaSelf xs (p+1)*|t| ^p*pfWordInflation skew xs t := by
  have hpoly := sub_eq_zero.mp (pf_defect_prefix_polynomial_zero xs H p hp hc t)
  rw [pfLeftGenerator_prefix_sum,← hpoly,← Finset.sum_sub_distrib]
  calc _≤∑ j : Fin xs.length,‖pfConjWord (xs.take j.val) (xs.getD j.val 0) t-
             pfConjTrunc (xs.take j.val) (xs.getD j.val 0) p t‖ := norm_sum_le _ _
       _≤∑ j : Fin xs.length,pfCommAlphaInner (xs.take j.val) (xs.getD j.val 0) p*|t| ^p*pfWordInflation skew xs t := by
         apply Finset.sum_le_sum
         intro j _
         have hs : skew=true→∀ X∈xs.take j.val,Xᴴ=-X :=
             fun h X hX=>hxs h X (List.mem_of_mem_take hX)
         apply (pfConjWord_remainder_norm_mode skew (xs.take j.val) (xs.getD j.val 0) p t hs).trans
         exact mul_le_mul_of_nonneg_left (pfWordInflation_take_le skew xs j.val t)
           (mul_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) (by positivity))
       _=(∑ j : Fin xs.length,pfCommAlphaInner (xs.take j.val) (xs.getD j.val 0) p)*|t| ^p*pfWordInflation skew xs t := by
         rw [← Finset.sum_mul,← Finset.sum_mul]
       _≤_ := mul_le_mul_of_nonneg_right
         (mul_le_mul_of_nonneg_right (pf_prefix_commutator_budget_le xs p) (by positivity))
         (pfWordInflation_nonneg skew xs t)

end Qatlib.Concepts.TrotterFormula.GeneralOrder
