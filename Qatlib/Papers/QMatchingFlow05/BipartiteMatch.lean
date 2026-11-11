/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMatchingFlow05.SearchTools.Defs

/-!
# Bipartite matching resource inequalities

This module derives the bipartite matching resource estimates associated with Theorem 3 of
[AmbainisSpalek2006]. The scalar phase hypotheses imply an iteration bound of `2 * √n`.

Combining that bound with a supplied per-iteration budget yields total budgets proportional to
`n² * logFactor n` in the adjacency model and `n * √(m + n) * logFactor n` in the list model.

## Main statements

* `bipartite_iteration_bound`: the square-root bound on the supplied iteration count.
* `theorem3_adjacency`: total adjacency-model budget under the per-iteration hypothesis.
* `theorem3_list`: total list-model budget under the per-iteration hypothesis.

## References

* [Ambainis and Špalek, 2006][AmbainisSpalek2006]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QMatchingFlow05.BipartiteMatch

open Qatlib.Papers.QMatchingFlow05.SearchTools

/-- For natural `n`, the product `√n * n ^ (3 / 2)` equals `n ^ 2`. -/
theorem sqrt_mul_rpow_three_halves (n : ℕ) :
    Real.sqrt (n : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn (1 / 2) (3 / 2)]
    rw [show (1 / 2 + 3 / 2 : ℝ) = 2 by norm_num, Real.rpow_two]

/-- For natural `n` and `m`, one has `√n * √(n * (m + n)) = n * √(m + n)`. -/
theorem sqrt_mul_sqrt_mul_add (n m : ℕ) :
    Real.sqrt (n : ℝ) * Real.sqrt ((n : ℝ) * ((m : ℝ) + (n : ℝ))) =
      (n : ℝ) * Real.sqrt ((m : ℝ) + (n : ℝ)) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg (α := ℝ) n)]
  rw [show (n : ℝ) * ((n : ℝ) * ((m : ℝ) + (n : ℝ))) =
      (n : ℝ) ^ 2 * ((m : ℝ) + (n : ℝ)) by ring]
  rw [Real.sqrt_mul (sq_nonneg (n : ℝ)), Real.sqrt_sq (Nat.cast_nonneg (α := ℝ) n)]

/-- Under the stated threshold and phase-length hypotheses, the iteration count `T` is at most
`2 * √n`. See [AmbainisSpalek2006]. -/
theorem bipartite_iteration_bound (n j g T : ℕ) (hn : 0 < n)
    (hfirst : Real.sqrt (n : ℝ) < (g : ℝ) + 1)
    (hlen : ((g : ℝ) + 1) * ((j : ℝ) + 2) ≤ (n : ℝ))
    (hg : (g : ℝ) ≤ Real.sqrt (n : ℝ))
    (hT : T ≤ j + g) : (T : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  have hj2 : ((j : ℝ) + 2) ≤ Real.sqrt (n : ℝ) := by
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
      Real.mul_self_sqrt hn'.le
    have hmul : Real.sqrt (n : ℝ) * ((j : ℝ) + 2) ≤
        Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
      calc Real.sqrt (n : ℝ) * ((j : ℝ) + 2) ≤ ((g : ℝ) + 1) * ((j : ℝ) + 2) :=
              mul_le_mul_of_nonneg_right hfirst.le (by positivity)
        _ ≤ (n : ℝ) := hlen
        _ = Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := hsq.symm
    exact le_of_mul_le_mul_left hmul hs
  have hT' : (T : ℝ) ≤ (j : ℝ) + (g : ℝ) := by exact_mod_cast hT
  linarith

/-- For nonnegative `c`, the phase hypotheses and a per-iteration bound `c * n ^ (3 / 2) *
logFactor n` imply a total bound `C * n ^ 2 * logFactor n` for some positive `C`. See
[AmbainisSpalek2006]. -/
theorem theorem3_adjacency (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n j g T : ℕ) (perIter : ℝ), 2 ≤ n →
      Real.sqrt (n : ℝ) < (g : ℝ) + 1 →
      ((g : ℝ) + 1) * ((j : ℝ) + 2) ≤ (n : ℝ) →
      (g : ℝ) ≤ Real.sqrt (n : ℝ) → T ≤ j + g → 0 ≤ perIter →
      perIter ≤ c * (n : ℝ) ^ ((3 : ℝ) / 2) * logFactor n →
      (T : ℝ) * perIter ≤ C * (n : ℝ) ^ 2 * logFactor n := by
  refine ⟨2 * c + 1, by positivity, ?_⟩
  intro n j g T perIter hn2 hfirst hlen hg hT hper hbound
  have hTb : (T : ℝ) ≤ 2 * Real.sqrt (n : ℝ) :=
    bipartite_iteration_bound n j g T (by omega) hfirst hlen hg hT
  have hsqrt : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hL : (0 : ℝ) ≤ logFactor n := (logFactor_pos n).le
  have hstep1 : (T : ℝ) * perIter ≤ (2 * Real.sqrt (n : ℝ)) * perIter :=
    mul_le_mul_of_nonneg_right hTb hper
  have hstep2 : (2 * Real.sqrt (n : ℝ)) * perIter ≤
      2 * Real.sqrt (n : ℝ) * (c * (n : ℝ) ^ ((3 : ℝ) / 2) * logFactor n) :=
    mul_le_mul_of_nonneg_left hbound (by positivity)
  have hpow : Real.sqrt (n : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) ^ 2 :=
    sqrt_mul_rpow_three_halves n
  have hkey : 2 * Real.sqrt (n : ℝ) * (c * (n : ℝ) ^ ((3 : ℝ) / 2) * logFactor n) =
      2 * c * (n : ℝ) ^ 2 * logFactor n := by
    rw [← hpow]
    ring
  have hsq : (0 : ℝ) ≤ (n : ℝ) ^ 2 * logFactor n := by positivity
  calc (T : ℝ) * perIter
      ≤ 2 * Real.sqrt (n : ℝ) * (c * (n : ℝ) ^ ((3 : ℝ) / 2) * logFactor n) :=
        hstep1.trans hstep2
    _ = 2 * c * (n : ℝ) ^ 2 * logFactor n := hkey
    _ ≤ (2 * c + 1) * (n : ℝ) ^ 2 * logFactor n := by nlinarith [hsq, hc]

/-- For nonnegative `c`, the phase hypotheses and a per-iteration bound `c * √(n * (m + n)) *
logFactor n` imply a total bound `C * n * √(m + n) * logFactor n` for some positive `C`. See
[AmbainisSpalek2006]. -/
theorem theorem3_list (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m j g T : ℕ) (perIter : ℝ), 2 ≤ n → n ≤ m + 1 →
      Real.sqrt (n : ℝ) < (g : ℝ) + 1 →
      ((g : ℝ) + 1) * ((j : ℝ) + 2) ≤ (n : ℝ) →
      (g : ℝ) ≤ Real.sqrt (n : ℝ) → T ≤ j + g → 0 ≤ perIter →
      perIter ≤ c * Real.sqrt ((n : ℝ) * ((m : ℝ) + (n : ℝ))) * logFactor n →
      (T : ℝ) * perIter ≤ C * ((n : ℝ) * Real.sqrt ((m : ℝ) + (n : ℝ)) * logFactor n) := by
  refine ⟨2 * c + 1, by positivity, ?_⟩
  intro n m j g T perIter hn2 hnm hfirst hlen hg hT hper hbound
  have hTb : (T : ℝ) ≤ 2 * Real.sqrt (n : ℝ) :=
    bipartite_iteration_bound n j g T (by omega) hfirst hlen hg hT
  have hstep1 : (T : ℝ) * perIter ≤ (2 * Real.sqrt (n : ℝ)) * perIter :=
    mul_le_mul_of_nonneg_right hTb hper
  have hstep2 : (2 * Real.sqrt (n : ℝ)) * perIter ≤
      2 * Real.sqrt (n : ℝ) *
        (c * Real.sqrt ((n : ℝ) * ((m : ℝ) + (n : ℝ))) * logFactor n) :=
    mul_le_mul_of_nonneg_left hbound (by positivity)
  have hsqrtid : Real.sqrt (n : ℝ) * Real.sqrt ((n : ℝ) * ((m : ℝ) + (n : ℝ))) =
      (n : ℝ) * Real.sqrt ((m : ℝ) + (n : ℝ)) := sqrt_mul_sqrt_mul_add n m
  have hkey : 2 * Real.sqrt (n : ℝ) *
        (c * Real.sqrt ((n : ℝ) * ((m : ℝ) + (n : ℝ))) * logFactor n) =
      2 * c * ((n : ℝ) * Real.sqrt ((m : ℝ) + (n : ℝ))) * logFactor n := by
    rw [← hsqrtid]
    ring
  have hR : (0 : ℝ) ≤ (n : ℝ) * Real.sqrt ((m : ℝ) + (n : ℝ)) * logFactor n := by
    have : (0 : ℝ) ≤ Real.sqrt ((m : ℝ) + (n : ℝ)) := Real.sqrt_nonneg _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hl : (0 : ℝ) ≤ logFactor n := (logFactor_pos n).le
    positivity
  calc (T : ℝ) * perIter
      ≤ 2 * Real.sqrt (n : ℝ) *
          (c * Real.sqrt ((n : ℝ) * ((m : ℝ) + (n : ℝ))) * logFactor n) :=
        hstep1.trans hstep2
    _ = 2 * c * ((n : ℝ) * Real.sqrt ((m : ℝ) + (n : ℝ))) * logFactor n := hkey
    _ ≤ (2 * c + 1) * ((n : ℝ) * Real.sqrt ((m : ℝ) + (n : ℝ)) * logFactor n) := by
        have hX : (0 : ℝ) ≤ (n : ℝ) * Real.sqrt ((m : ℝ) + (n : ℝ)) * logFactor n := hR
        have hmono := mul_le_mul_of_nonneg_right (by linarith : 2 * c ≤ 2 * c + 1) hX
        calc 2 * c * ((n : ℝ) * Real.sqrt ((m : ℝ) + (n : ℝ))) * logFactor n
            = 2 * c * ((n : ℝ) * Real.sqrt ((m : ℝ) + (n : ℝ)) * logFactor n) := by ring
          _ ≤ (2 * c + 1) *
              ((n : ℝ) * Real.sqrt ((m : ℝ) + (n : ℝ)) * logFactor n) := hmono

end Qatlib.Papers.QMatchingFlow05.BipartiteMatch

end
