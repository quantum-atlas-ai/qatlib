/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SparseMarkov16.MainResults.Model.SparseMarkovModel

@[expose] public section

/-!
# Single-jump Lindbladians and the public GKSL generator

Childs--Li, *Efficient simulation of sparse Markovian quantum dynamics*,
fixed arXiv:1611.05543v3 (9 Oct 2023), Eqs. (1)-(2) and Eq. (167).

The paper writes a Lindbladian either in the general GKSL jump-sum form
Eq. (1)-(2) or, when only one jump operator acts nontrivially, in the single
jump form Eq. (167):
`L(ρ) = M ρ M† - ½ (M† M ρ + ρ M† M)`.

The model layer records the single-jump form as `jumpLindbladApply M` and the
GKSL form as the public `lindbladMap`. This module proves that the GKSL
generator whose Hamiltonian vanishes and whose jump family is `M` on the first
slot and `0` on the remaining `D² - 1` slots (the model's `singleJumpGKSL`)
is exactly Eq. (167). The proof picks the single nonzero summand out of the
`D²`-term jump sum; for `D = 0` the jump index type is empty and both sides are
the zero operator.

The statement is an identity between generators, not between the semigroups or
their error terms; no resource or simulation claim is made here.
-/
set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Papers.SparseMarkov16.MainResults.SingleJumpBridge

open Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Qatlib.Papers.SparseMarkov16.MainResults.Model

/-- Eq. (167) is the GKSL generator with no Hamiltonian and one nonzero jump
operator: `lindbladMap (singleJumpGKSL M) ρ = jumpLindbladApply M ρ`. -/
theorem lindbladMap_singleJumpGKSL {D : ℕ} (M : Op D) (ρ : Op D) :
    lindbladMap (singleJumpGKSL M) ρ = jumpLindbladApply M ρ := by
  rcases D with _ | D
  · exact Subsingleton.elim _ _
  · have hjumps : ∀ j : Fin ((D + 1) * (D + 1)), j ≠ 0 → (singleJumpGKSL M).jumps j = 0 := by
      intro j hj
      show (if j.1 = 0 then M else 0) = 0
      by_cases h : j.1 = 0
      · exact absurd (Fin.ext h) hj
      · simp [h]
    have hjump0 : (singleJumpGKSL M).jumps 0 = M := by
      show (if (0 : Fin ((D + 1) * (D + 1))).1 = 0 then M else 0) = M
      rw [ite_eq_left (show (0 : Fin ((D + 1) * (D + 1))).1 = 0 from rfl)]
    have hham : (-Complex.I) •
        ((singleJumpGKSL M).ham * ρ - ρ * (singleJumpGKSL M).ham) = 0 := by
      show (-Complex.I) • ((0 : Op (D + 1)) * ρ - ρ * (0 : Op (D + 1))) = 0
      simp
    have hsum : (∑ j, ((singleJumpGKSL M).jumps j * ρ * ((singleJumpGKSL M).jumps j)ᴴ -
          (1 / 2 : ℂ) • (((singleJumpGKSL M).jumps j)ᴴ * (singleJumpGKSL M).jumps j * ρ +
            ρ * ((singleJumpGKSL M).jumps j)ᴴ * (singleJumpGKSL M).jumps j))) =
        ((singleJumpGKSL M).jumps 0 * ρ * ((singleJumpGKSL M).jumps 0)ᴴ -
          (1 / 2 : ℂ) • (((singleJumpGKSL M).jumps 0)ᴴ * (singleJumpGKSL M).jumps 0 * ρ +
            ρ * ((singleJumpGKSL M).jumps 0)ᴴ * (singleJumpGKSL M).jumps 0)) := by
      refine Finset.sum_eq_single 0 ?_ ?_
      · intro b _ hb
        rw [hjumps b hb]
        simp
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hmap : lindbladMap (singleJumpGKSL M) ρ =
        (-Complex.I) • ((singleJumpGKSL M).ham * ρ - ρ * (singleJumpGKSL M).ham) +
          ∑ j, ((singleJumpGKSL M).jumps j * ρ * ((singleJumpGKSL M).jumps j)ᴴ -
            (1 / 2 : ℂ) • (((singleJumpGKSL M).jumps j)ᴴ * (singleJumpGKSL M).jumps j * ρ +
              ρ * ((singleJumpGKSL M).jumps j)ᴴ * (singleJumpGKSL M).jumps j)) := rfl
    rw [hmap, hham, zero_add, hsum, hjump0]
    rfl

end Qatlib.Papers.SparseMarkov16.MainResults.SingleJumpBridge
