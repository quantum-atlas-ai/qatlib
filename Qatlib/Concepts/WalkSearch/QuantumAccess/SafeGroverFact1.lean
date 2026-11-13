/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.TriangleContracts
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Safe Grover search interface guarantees

`fact1_answer` bundles the soundness, empty-input rejection, finite-seed failure-count, and
charge guarantees supplied by a `SafeGrover`. `fact1_failure_pow` gives a real-valued
inverse-power consequence when the floor parameter is zero.

These are interface-level forms of the search guarantees motivating [BoyerEtAl1998].

## Main statements

* `fact1_answer`: collect the four `SafeGrover` guarantees.
* `fact1_failure_pow`: the real-valued failure-count bound with zero floor.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.WalkSearch.QuantumAccess

open Qatlib.Concepts.WalkSearch.Primitives

/-- Collects soundness, rejection on unmarked inputs, the inverse-power failure-count bound, and
the logarithmic square-root charge bound of a supplied `SafeGrover` [BoyerEtAl1998]. -/
theorem fact1_answer (sgs : SafeGrover) {N : ℕ} (marked : Fin N → Bool) (check floor : ℕ) :
    (∀ (ρ : sgs.seed) {x : Fin N}, sgs.run marked check floor ρ = some x → marked x = true) ∧
    (∀ (ρ : sgs.seed), (∀ x, marked x = false) → sgs.run marked check floor ρ = none) ∧
    ((∃ x, marked x = true) →
      ((@Finset.univ sgs.seed sgs.seedFin).filter
          (fun ρ : sgs.seed => sgs.run marked check floor ρ = none)).card *
        (max N floor + 1) ^ sgs.cExp ≤ @Fintype.card sgs.seed sgs.seedFin) ∧
    (∀ (ρ : sgs.seed), sgs.cost marked check floor ρ ≤
      sgs.κ * (Nat.log 2 (max N floor + 1) + 2) * (check + 1) *
        (Nat.sqrt (max N floor + 1) + 1)) :=
  ⟨fun ρ _ h => sgs.sound marked check floor ρ h,
    fun ρ h => sgs.reject marked check floor ρ h,
    fun h => sgs.finds marked check floor h,
    fun ρ => sgs.charges marked check floor ρ⟩

/-- If a marked element exists, the real failure count at floor zero multiplied by `N ^
sgs.cExp` is at most the seed-space cardinality [BoyerEtAl1998]. -/
theorem fact1_failure_pow (sgs : SafeGrover) {N : ℕ} (marked : Fin N → Bool) (check : ℕ)
    (h : ∃ x, marked x = true) :
    (((@Finset.univ sgs.seed sgs.seedFin).filter
        (fun ρ : sgs.seed => sgs.run marked check 0 ρ = none)).card : ℝ) *
        (N : ℝ) ^ sgs.cExp ≤ (@Fintype.card sgs.seed sgs.seedFin : ℝ) := by
  have hf := sgs.finds marked check 0 h
  rw [show max N 0 = N from max_eq_left (Nat.zero_le N)] at hf
  have hfR : (((@Finset.univ sgs.seed sgs.seedFin).filter
        (fun ρ : sgs.seed => sgs.run marked check 0 ρ = none)).card : ℝ) *
        ((N : ℝ) + 1) ^ sgs.cExp ≤ (@Fintype.card sgs.seed sgs.seedFin : ℝ) := by
    have hcast : (((@Finset.univ sgs.seed sgs.seedFin).filter
        (fun ρ : sgs.seed => sgs.run marked check 0 ρ = none)).card : ℝ) *
        ((N + 1 : ℕ) : ℝ) ^ sgs.cExp ≤ (@Fintype.card sgs.seed sgs.seedFin : ℝ) := by
      exact_mod_cast hf
    simpa using hcast
  have hbase : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
  have hpow : (N : ℝ) ^ sgs.cExp ≤ ((N : ℝ) + 1) ^ sgs.cExp :=
    pow_le_pow_left₀ (by positivity) hbase sgs.cExp
  have hb : (((@Finset.univ sgs.seed sgs.seedFin).filter
        (fun ρ : sgs.seed => sgs.run marked check 0 ρ = none)).card : ℝ) * (N : ℝ) ^ sgs.cExp ≤
      (((@Finset.univ sgs.seed sgs.seedFin).filter
        (fun ρ : sgs.seed => sgs.run marked check 0 ρ = none)).card : ℝ) *
        ((N : ℝ) + 1) ^ sgs.cExp :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  exact hb.trans hfR

end Qatlib.Concepts.WalkSearch.QuantumAccess
