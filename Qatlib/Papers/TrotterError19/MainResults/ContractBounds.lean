/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section


/-!
# Boundaries of the legacy Trotter contracts

The old application statements quantified over unrelated error and cost
functions. Nonnegativity cannot imply a bound by zero. Likewise the
creation/annihilation commutator rules need canonical relations.
-/

set_option autoImplicit false

namespace Qatlib.Papers.TrotterError19.MainResults

open Asymptotics Filter

/-- A nonzero constant is not bounded asymptotically by the zero function. -/
theorem one_not_bigO_zero :
    ¬ ((fun _ : ℕ => (1 : ℝ)) =O[atTop] fun _ => (0 : ℝ)) := by
  intro h
  obtain ⟨c, hc⟩ := isBigO_iff.mp h
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hc] with n hn
    norm_num at hn
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

/-- Nonnegative arbitrary errors violate the old local-Hamiltonian error bound. -/
theorem local_error_counterexample :
    (∀ n : ℕ, 0 ≤ (fun _ => (1 : ℝ)) n) ∧
    ¬ ((fun _ : ℕ => (1 : ℝ)) =O[atTop]
      fun _ => (0 : ℝ) ^ (1 : ℕ) * 0) := by
  constructor
  · intro n
    norm_num
  · simpa using one_not_bigO_zero

/-- The ring commutator used in the old second-quantized interface. -/
def brk {R : Type*} [Mul R] [Sub R] (x y : R) : R := x * y - y * x

/-- A commutator acts as a derivation on products in every ring. -/
theorem commutator_mul_nested {R : Type*} [Ring R] (w n m : R) :
    brk w (n * m) = brk w n * m + n * brk w m := by
  unfold brk
  noncomm_ring

/-- The third legacy commutation rule follows from the two supplied bracket identities. -/
theorem lemmaD3_rule3 {R : Type*} [Ring R] (w n m a b : R)
    (hn : brk w n = a) (hm : brk w m = b) :
    brk w (n * m) = a * m + n * b := by
  rw [commutator_mul_nested, hn, hm]

/-- Constant unit operators refute both old canonical commutator rules without CAR hypotheses. -/
theorem canonical_rule_counterexample :
    brk (1 : ℝ) 1 ≠
      (if (1 : Fin 2) = 1 then (1 : ℝ) else 0) * 1 -
        (if (0 : Fin 2) = 1 then (1 : ℝ) else 0) * 1 := by
  norm_num [brk]

/-- Zero geometric radius makes the old truncation bound false in dimension two. -/
theorem truncation_counterexample :
    ¬ ∃ c : ℝ, 0 < c ∧ (1 : ℝ) ≤
      c * (Real.rpow (0 + (0 : ℕ) * (1 : ℝ)) ((2 : ℝ) - 1) /
        Real.rpow 1 ((3 : ℝ) - 2 - 1)) := by
  norm_num

/-- Zero geometric radius also contradicts the old unrestricted nested-sum estimate. -/
theorem nested_sum_counterexample :
    ¬ ∃ c : ℝ, 0 < c ∧ (1 : ℝ) ≤
      c * (Real.rpow (0 + (0 : ℕ) * (1 : ℝ)) ((2 : ℝ) - 1) * 1) := by
  norm_num

end Qatlib.Papers.TrotterError19.MainResults
