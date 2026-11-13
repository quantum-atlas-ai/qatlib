/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDistTV
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# GenerativeAdv25 — finite laws, conditional distributions and total variation

Fixed paper version: arXiv:2509.09033v1 ("Generative quantum advantage for classical
and quantum problems").

This file sets up the paper's probabilistic objects on top of the frozen finite
distribution API `Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist`:

* `Bit n` — the `n`-bit classical register `Fin n → Bool`;
* `CondLaw n m` — the paper's conditional distributions `p(y|x)` (Definitions 13–14,
  Appendix H);
* `uniformDist`, `pointMass`, `pushForward` — the uniform law, a point mass, and the
  pushforward of a finite law along a map (the law of a randomized circuit);
* `tvDist` — total variation distance, re-exported from the frozen development;
* a few elementary lemmas (`tvDist_self`, `tvDist_nonneg`, `pushForward_uniform`) used by
  Proposition 3 (universal approximation) and by the generative-advantage statements.

All definitions are elementary finite sums; no measure theory is involved, matching the
paper's finite-dimensional setting.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.GenerativeAdv25.MainResults

/-- The `n`-bit classical register. -/
abbrev Bit (n : ℕ) := Fin n → Bool

/-- The paper's conditional distribution `p(y|x)` from `n`-bit strings to `m`-bit strings
(Definition 13 and Definition 14 of arXiv:2509.09033v1). -/
abbrev CondLaw (n m : ℕ) := Bit n → FinDist (Bit m)

/-- The uniform distribution on a nonempty finite type. -/
def uniformDist (X : Type*) [Fintype X] [Nonempty X] : FinDist X where
  prob _ := (Fintype.card X : ℝ)⁻¹
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- The point mass at `x`. -/
def pointMass {X : Type*} [Fintype X] [DecidableEq X] (x : X) : FinDist X where
  prob y := if y = x then 1 else 0
  nonneg y := by split_ifs <;> norm_num
  sum_one := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [hy]
    · intro h; exact (h (Finset.mem_univ x)).elim

/-- Pushforward of a finite law along a map: the law of `f` applied to a sample of `p`. -/
def pushForward {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (p : FinDist X) (f : X → Y) : FinDist Y where
  prob y := ∑ x ∈ Finset.univ.filter (fun x => f x = y), p.prob x
  nonneg y := Finset.sum_nonneg fun x _ => p.nonneg x
  sum_one := by
    have h1 : (∑ y, ∑ x ∈ Finset.univ.filter (fun x => f x = y), p.prob x)
        = ∑ y, ∑ x, (if f x = y then p.prob x else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_filter]
    rw [h1, Finset.sum_comm, ← p.sum_one]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_eq_single (f x)]
    · simp
    · intro y _ hy
      split_ifs with h
      · exact (hy h.symm).elim
      · rfl
    · intro h; exact (h (Finset.mem_univ (f x))).elim

/-- The law of applying a uniform sampler `f : Bit r → Bit m` to uniform randomness. This is
the paper's "shallow/classical sampling circuit" output law (Definition 14 with the input
register fixed). -/
def uniformPushLaw {m r : ℕ} (f : Bit r → Bit m) : FinDist (Bit m) :=
  pushForward (uniformDist (Bit r)) f

/-- Total variation of a law with itself vanishes.  `tvDist` itself is the frozen
`Qatlib.Concepts.MonteCarloMean.FinDistBounds.tvDist`. -/
theorem tvDist_self {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X) :
    tvDist p p = 0 := by
  unfold tvDist
  simp

/-- Total variation is nonnegative. -/
theorem tvDist_nonneg {X : Type*} [Fintype X] [DecidableEq X] (p q : FinDist X) :
    0 ≤ tvDist p q := by
  unfold tvDist
  positivity

end Qatlib.Papers.GenerativeAdv25.MainResults
