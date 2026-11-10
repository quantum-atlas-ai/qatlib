/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
set_option autoImplicit false
namespace Qatlib.Papers.CollisionProb97.MainResults.IntegerParameters

theorem cube_root_bounds (m : ℕ) (hm : 1 ≤ m) :
  1 ≤ Nat.nthRoot 3 m ∧ (Nat.nthRoot 3 m)^3 ≤ m ∧
    m < (Nat.nthRoot 3 m+1)^3 := by
  refine ⟨?_, Nat.pow_nthRoot_le (Or.inl (by decide)),
    Nat.lt_pow_nthRoot_add_one (by decide) m⟩
  apply (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).2
  simpa using hm

theorem cube_root_claw_admissible (m : ℕ) (hm : 2 ≤ m) : Nat.nthRoot 3 m ≤ m/2 := by
  let k := Nat.nthRoot 3 m
  obtain ⟨hk1,hpow,_⟩ := cube_root_bounds m (by omega)
  change 1 ≤ k at hk1
  change k^3 ≤ m at hpow
  change k ≤ m/2
  by_cases hk : k=1
  · omega
  · have hk2 : 2 ≤ k := by omega
    have h2 : 2*k ≤ k^3 := calc
      2*k ≤ k*k := Nat.mul_le_mul_right k hk2
      _ ≤ k^3 := by
        simpa [pow_succ, pow_two] using (Nat.mul_le_mul_left (k*k) hk1)
    omega

theorem cube_root_real_window (m : ℕ) :
  (Nat.nthRoot 3 m : ℝ) ≤ (m : ℝ)^(1/3 : ℝ) ∧
    (m : ℝ)^(1/3 : ℝ) < (Nat.nthRoot 3 m : ℝ)+1 := by
  have hl : (Nat.nthRoot 3 m)^3 ≤ m := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hu := Nat.lt_pow_nthRoot_add_one (n:=3) (by decide) m
  simp only [one_div]
  constructor
  · apply (Real.le_rpow_inv_iff_of_pos (x := (Nat.nthRoot 3 m:ℝ)) (y := (m:ℝ)) (by positivity) (by positivity) (by norm_num : (0:ℝ)<3)).2
    have h : (Nat.nthRoot 3 m : ℝ)^(3:ℕ) ≤ (m:ℝ) := by exact_mod_cast hl
    norm_num only [← Real.rpow_natCast] at h ⊢
    exact h
  · apply (Real.rpow_inv_lt_iff_of_pos (x := (m:ℝ)) (y := (Nat.nthRoot 3 m:ℝ)+1) (by positivity) (by positivity) (by norm_num : (0:ℝ)<3)).2
    have h : (m:ℝ) < ((Nat.nthRoot 3 m:ℝ)+1)^(3:ℕ) := by exact_mod_cast hu
    norm_num only [← Real.rpow_natCast] at h ⊢
    exact h

theorem sqrt_div_le_three_of_window {m k : ℕ} (hk : 1 ≤ k) (hu : m < (k+1)^3) :
  Real.sqrt ((m:ℝ)/(k:ℝ)) ≤ 3*(k:ℝ) := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have huR : (m:ℝ) < ((k:ℝ)+1)^3 := by exact_mod_cast hu
  have he : ((k:ℝ)+1)^3 ≤ (2*(k:ℝ))^3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hm : (m:ℝ) ≤ 9*(k:ℝ)^3 := by nlinarith [pow_nonneg hk0.le 3]
  have hd : (m:ℝ)/(k:ℝ) ≤ (3*(k:ℝ))^2 := by
    apply (div_le_iff₀ hk0).2
    nlinarith
  have hs := Real.sqrt_le_sqrt hd
  rw [Real.sqrt_sq (by positivity)] at hs
  exact hs

theorem cube_root_search_bound (m : ℕ) (hm : 1 ≤ m) :
  Real.sqrt ((m:ℝ)/(Nat.nthRoot 3 m:ℝ)) ≤ 3*(Nat.nthRoot 3 m:ℝ) := by
  obtain ⟨hk,_,hu⟩ := cube_root_bounds m hm
  exact sqrt_div_le_three_of_window hk hu

theorem cube_root_table_search_bound (m : ℕ) (hm : 1 ≤ m) :
  (Nat.nthRoot 3 m:ℝ)+Real.sqrt ((m:ℝ)/(Nat.nthRoot 3 m:ℝ)) ≤
    4*(m:ℝ)^(1/3:ℝ) := by
  have hs := cube_root_search_bound m hm
  have hl := (cube_root_real_window m).1
  linarith
end Qatlib.Papers.CollisionProb97.MainResults.IntegerParameters
