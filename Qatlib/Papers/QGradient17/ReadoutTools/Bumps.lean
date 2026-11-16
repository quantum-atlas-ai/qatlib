/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section


set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QGradient17.ReadoutTools

/-- The squared mass of the Gaussian bump family satisfies source Lemma 29. -/
theorem source_lemma_twentynine
    (d : ℕ) (ε c : ℝ) (_hε : 0 ≤ ε) (hc : 0 < c) (x : Fin d → ℝ) :
    ∑ j : Fin d,
        (2 * ε * (x j) * Real.exp (-(c ^ 2 * (∑ i : Fin d, (x i) ^ 2)) / 2)) ^ 2
      ≤ 4 * ε ^ 2 / (Real.exp 1 * c ^ 2) := by
  set S : ℝ := ∑ i : Fin d, (x i) ^ 2 with hSdef
  have hexp_sq : (Real.exp (-(c ^ 2 * S) / 2)) ^ 2 = Real.exp (-(c ^ 2 * S)) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hterm : ∀ j : Fin d,
      (2 * ε * (x j) * Real.exp (-(c ^ 2 * S) / 2)) ^ 2
        = (4 * ε ^ 2 * Real.exp (-(c ^ 2 * S))) * (x j) ^ 2 := by
    intro j
    calc (2 * ε * (x j) * Real.exp (-(c ^ 2 * S) / 2)) ^ 2
        = (2 * ε * (x j)) ^ 2 * (Real.exp (-(c ^ 2 * S) / 2)) ^ 2 := by ring
      _ = (2 * ε * (x j)) ^ 2 * Real.exp (-(c ^ 2 * S)) := by rw [hexp_sq]
      _ = (4 * ε ^ 2 * Real.exp (-(c ^ 2 * S))) * (x j) ^ 2 := by ring
  have hmulsum : 4 * ε ^ 2 * Real.exp (-(c ^ 2 * S)) * S
      = ∑ j : Fin d, 4 * ε ^ 2 * Real.exp (-(c ^ 2 * S)) * (x j) ^ 2 := by
    rw [hSdef, Finset.mul_sum]
  have hsum : ∑ j : Fin d,
      (2 * ε * (x j) * Real.exp (-(c ^ 2 * S) / 2)) ^ 2
        = 4 * ε ^ 2 * Real.exp (-(c ^ 2 * S)) * S := by
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    exact hmulsum.symm
  have hkey := Real.mul_exp_neg_le_exp_neg_one (c ^ 2 * S)
  have hcoef : 0 ≤ 4 * ε ^ 2 / c ^ 2 := by positivity
  have hrewrite : 4 * ε ^ 2 * Real.exp (-(c ^ 2 * S)) * S
      = (4 * ε ^ 2 / c ^ 2) * ((c ^ 2 * S) * Real.exp (-(c ^ 2 * S))) := by
    field_simp
  rw [hsum, hrewrite]
  calc (4 * ε ^ 2 / c ^ 2) * ((c ^ 2 * S) * Real.exp (-(c ^ 2 * S)))
      ≤ (4 * ε ^ 2 / c ^ 2) * Real.exp (-1) :=
        mul_le_mul_of_nonneg_left hkey hcoef
    _ = 4 * ε ^ 2 / (Real.exp 1 * c ^ 2) := by
        rw [Real.exp_neg]
        field_simp

end Qatlib.Papers.QGradient17.ReadoutTools
