/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteCounts.SubsetIncidence
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Qatlib.Papers.NonlinearDE20.PolynomialStep.Model
open Qatlib.Foundations.FiniteCounts.SubsetIncidence

theorem polynomial_incidence (n m : ℕ) (a : Fin n) (hm : m+1≤n) :
    ((incidentSupports n (m+1) a).card:ℝ)/(Nat.choose n (m+1):ℝ)=((m:ℝ)+1)/n := by
  simpa only [Nat.cast_add,Nat.cast_one] using incidentSupports_fraction n (m+1) a (by omega) hm

theorem polynomial_overlap_fraction (n m : ℕ) (s : Finset (Fin n))
    (hm : 1 ≤ m) (hmn : m+1 ≤ n) (hs : s.card = m+1) :
    ((overlappingSupports n (m+1) s).card : ℝ) / (Nat.choose n (m+1) : ℝ) ≤
      4 * (m : ℝ)^2 / n := by
  have h := fixed_arity_overlap_fraction n (m+1) s (by omega) hmn hs
  simp only [Nat.cast_add, Nat.cast_one] at h
  refine h.trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n))
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 ≤ ((m : ℝ)-1) * (3*m+1) := mul_nonneg (by linarith) (by positivity)
  nlinarith

end Qatlib.Papers.NonlinearDE20.PolynomialStep.Model
