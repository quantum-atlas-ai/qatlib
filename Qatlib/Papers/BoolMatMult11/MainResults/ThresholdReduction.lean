/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Lower bound of Jeffery--Kothari--Magniez (arXiv:1112.5855v2, Section 4.2)

Theorem 4.2 reduces `ℓ`-Threshold on `n²` bits to Boolean matrix multiplication:
set `A` to the identity matrix and let `B` encode the threshold instance.  Then
`A B = B`, so the product exposes the number of marked elements, and any BMM
algorithm solves `ℓ`-Threshold with the same number of queries.

This module formalizes the reduction and the transfer of a query lower bound.
The `Ω(√(n² min{ℓ, n² - ℓ}))` lower bound for `ℓ`-Threshold itself is the cited
[BBC⁺01] polynomial-method result; it enters the transfer theorem as the
external hypothesis `hThr`, not re-derived here.
-/

namespace Qatlib.Papers.BoolMatMult11.MainResults.ThresholdReduction

open scoped BigOperators

set_option autoImplicit false

/-- Boolean matrix product entry over the Boolean semiring:
`(A B)[i, j] = ⋁_k A[i, k] ∧ B[k, j]`. -/
noncomputable def bmmEntry {n : ℕ} (A B : Fin n → Fin n → Bool) (i j : Fin n) : Bool :=
  decide (∃ k : Fin n, A i k = true ∧ B k j = true)

/-- The identity Boolean matrix, the `A` of the paper's reduction. -/
def identity (n : ℕ) : Fin n → Fin n → Bool :=
  fun i j => decide (i = j)

/-- `A = I` gives `I B = B` over the Boolean semiring. -/
theorem identity_bmmEntry {n : ℕ} (B : Fin n → Fin n → Bool) (i j : Fin n) :
    bmmEntry (identity n) B i j = B i j := by
  unfold bmmEntry identity
  cases hb : B i j
  · apply decide_eq_false
    rintro ⟨k, hik, hkj⟩
    have hik' : i = k := of_decide_eq_true hik
    subst hik'
    rw [hb] at hkj
    exact Bool.false_ne_true hkj
  · simp [hb]

/-- Number of `1`-entries of a Boolean matrix, the parameter `ℓ` of the paper. -/
noncomputable def onesCount {n : ℕ} (C : Fin n → Fin n → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter fun p : Fin n × Fin n => C p.1 p.2 = true).card

/-- The reduction preserves the number of ones. -/
theorem onesCount_identity_mul {n : ℕ} (B : Fin n → Fin n → Bool) :
    onesCount (fun i j => bmmEntry (identity n) B i j) = onesCount B := by
  unfold onesCount
  congr 1
  apply Finset.filter_congr
  intro p _
  simp only [identity_bmmEntry]

/-- The `ℓ`-Threshold answer on `n²` bits: whether at least `ℓ` entries are `1`. -/
noncomputable def thresholdAnswer {n : ℕ} (ℓ : ℕ) (f : Fin n → Fin n → Bool) : Bool :=
  decide (ℓ ≤ onesCount f)

/-- A query-counted solver for Boolean matrix products.  `queriesA` and
`queriesB` count the accesses to the two oracle matrices, as in the paper's
query model. -/
structure BMMSolver (n : ℕ) where
  solve : (Fin n → Fin n → Bool) → (Fin n → Fin n → Bool) → (Fin n → Fin n → Bool)
  queriesA : (Fin n → Fin n → Bool) → (Fin n → Fin n → Bool) → ℕ
  queriesB : (Fin n → Fin n → Bool) → (Fin n → Fin n → Bool) → ℕ

/-- Correctness of a BMM solver: every output entry is the Boolean product. -/
def BMMSolver.Correct {n : ℕ} (S : BMMSolver n) : Prop :=
  ∀ (A B : Fin n → Fin n → Bool) (i j : Fin n), S.solve A B i j = bmmEntry A B i j

/-- **The identity reduction of Theorem 4.2.**  Running a correct BMM solver on
`(I, f)` decides `ℓ`-Threshold for `f`; the identity factor is the known
constant matrix, so only the second-oracle queries are charged. -/
theorem threshold_solver_of_bmm_solver {n ℓ : ℕ} (S : BMMSolver n)
    (hS : S.Correct) :
    ∃ (thr : (Fin n → Fin n → Bool) → Bool) (q : (Fin n → Fin n → Bool) → ℕ),
      (∀ f, thr f = thresholdAnswer ℓ f) ∧
        (∀ f, q f = S.queriesB (identity n) f) := by
  refine ⟨fun f => thresholdAnswer ℓ (S.solve (identity n) f),
    fun f => S.queriesB (identity n) f, ?_, ?_⟩
  · intro f
    beta_reduce
    unfold thresholdAnswer
    have hm : S.solve (identity n) f = (fun i j => bmmEntry (identity n) f i j) := by
      funext i j
      exact hS (identity n) f i j
    rw [hm, onesCount_identity_mul]
  · intro f
    rfl

/-- **Theorem 4.2 lower-bound transfer.**  Any external query lower bound `L`
for `ℓ`-Threshold on `n²` bits transfers to Boolean matrix multiplication: a
correct BMM solver whose identity accesses are free uses at least `L` queries
on `(I, f)`.  The paper supplies `L = Ω(√(n² min{ℓ, n² - ℓ}))` from [BBC⁺01]. -/
theorem bmm_lower_bound_of_threshold_lower_bound {n ℓ L : ℕ}
    (hThr : ∀ (thr : (Fin n → Fin n → Bool) → Bool)
      (q : (Fin n → Fin n → Bool) → ℕ),
      (∀ f, thr f = thresholdAnswer ℓ f) → ∃ f, L ≤ q f)
    (S : BMMSolver n) (hS : S.Correct) (hfree : ∀ f, S.queriesA (identity n) f = 0) :
    ∃ A B : Fin n → Fin n → Bool, L ≤ S.queriesA A B + S.queriesB A B := by
  obtain ⟨thr, q, hthr, hq⟩ := threshold_solver_of_bmm_solver (ℓ := ℓ) S hS
  obtain ⟨f, hf⟩ := hThr thr q hthr
  refine ⟨identity n, f, ?_⟩
  rw [hq f] at hf
  simpa [hfree f] using hf

end Qatlib.Papers.BoolMatMult11.MainResults.ThresholdReduction
