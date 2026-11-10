/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHCloneBudget
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHCommBudget

open scoped BigOperators MonoidAlgebra Classical
open BCHDynkin BCHWordLie BCHWordLog BCHMultilinear BCHWordPowers
open BCHExpansion BCHCloneBudget

variable {B : Type} [NormedRing B] [NormedAlgebra ℝ B] [Algebra ℚ B]

def alphaComm {Γ : ℕ} (X : Fin Γ → B) (n : ℕ) : ℝ :=
  ∑ f : Fin n → Fin Γ, ‖rightBracket (List.ofFn (fun j => X (f j)))‖

omit [NormedAlgebra ℝ B] [Algebra ℚ B] in

theorem alphaComm_nonneg {Γ : ℕ} (X : Fin Γ → B) (n : ℕ) : 0 ≤ alphaComm X n :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_phi_list_le {σ : Type} (xs : List σ) (hx : xs.Nodup) (Y : σ → B)
    (hn : 0 < xs.length) :
    ‖BCHPhi.phi (fun j => Y (xs.get j))‖ ≤ (1 / (xs.length : ℝ) ^ 2) *
      ∑ w ∈ permutationWords xs, ‖rightBracket (w.map Y)‖ := by
  have h := BCHPhi.norm_phi_le (fun j => Y (xs.get j)) hn
  have he := sum_permutationWords_map xs.get hx.injective_get (List.finRange xs.length)
    (fun w => ‖rightBracket (w.map Y)‖)
  have hxs : (List.finRange xs.length).map xs.get = xs := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  rw [hxs] at he
  simp only [List.map_map, Function.comp_def] at he
  rw [he] at h
  exact h

theorem norm_factorial_phi_le {Γ n : ℕ} (X : Fin Γ → B) (m : Fin Γ → ℕ)
    (hm : m ∈ multidegrees Γ n) (hn : 0 < n) :
    ‖(factorialMass m)⁻¹ • BCHPhi.phi (fun j => X ((cloneWord m).get j).1)‖ ≤
      (1 / (n : ℝ) ^ 2) * ((factorialMass m : ℝ)⁻¹ *
        ∑ w ∈ permutationWords (cloneWord m), ‖rightBracket ((w.map Sigma.fst).map X)‖) := by
  have hlen : (cloneWord m).length = n :=
    (cloneWord_length m).trans ((mem_multidegrees m).mp hm)
  have hpos : 0 < (factorialMass m : ℝ) := by
    unfold factorialMass
    positivity
  have hphi := norm_phi_list_le (cloneWord m) (cloneWord_nodup m)
    (fun j => X j.1) (by omega)
  have hden : (1 / ((cloneWord m).length : ℝ) ^ 2) = 1 / (n : ℝ) ^ 2 := by rw [hlen]
  rw [hden] at hphi
  simp only [List.map_map, Function.comp_def] at hphi ⊢
  rw [← Rat.cast_smul_eq_qsmul ℝ, norm_smul, Real.norm_eq_abs, Rat.cast_inv,
    abs_of_pos (inv_pos.mpr hpos)]
  calc
    _ ≤ (factorialMass m : ℝ)⁻¹ * ((1 / (n : ℝ) ^ 2) *
      ∑ w ∈ permutationWords (cloneWord m), ‖rightBracket (w.map (fun j => X j.1))‖) :=
        mul_le_mul_of_nonneg_left hphi (le_of_lt (inv_pos.mpr hpos))
    _ = _ := by ring

theorem norm_word_log_le {Γ : ℕ} (X : Fin Γ → B) (n : ℕ) (hn : 0 < n) :
    ‖logCoefficient (wordSeries ((List.finRange Γ).map X)) n‖ ≤
      alphaComm X n / (n : ℝ) ^ 2 := by
  rw [word_log_phi_sum Γ n X]
  calc
    _ ≤ ∑ m ∈ multidegrees Γ n,
        ‖(factorialMass m)⁻¹ • BCHPhi.phi (fun j => X ((cloneWord m).get j).1)‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ m ∈ multidegrees Γ n, (1 / (n : ℝ) ^ 2) * ((factorialMass m : ℝ)⁻¹ *
        ∑ w ∈ permutationWords (cloneWord m), ‖rightBracket ((w.map Sigma.fst).map X)‖) :=
      Finset.sum_le_sum fun m hm => norm_factorial_phi_le X m hm hn
    _ = (1 / (n : ℝ) ^ 2) * alphaComm X n := by
      rw [← Finset.mul_sum,
        sum_normalized_clone_sum n (fun w : List (Fin Γ) => ‖rightBracket (w.map X)‖)]
      simp only [alphaComm, List.map_ofFn, Function.comp_def]
    _ = _ := by ring

end Qatlib.Papers.CommutLCHS26.MainResults.BCHCommBudget
