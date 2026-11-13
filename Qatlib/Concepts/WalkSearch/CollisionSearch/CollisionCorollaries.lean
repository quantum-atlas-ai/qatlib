/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkContracts
import Qatlib.Concepts.WalkSearch.CollisionSearch.RealExponentTransportQuan
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Collision-search cost and amplification corollaries

The module extracts soundness, rejection, failure-count bounds, and real-exponent costs from a
supplied `KCollisionSolver`. It specializes the cost expression to two-collision search and
proves finite-product counting estimates for repeated trials.

`sourceWalkCost` records the real-valued setup, update, and checking expression, while the
solver bounds retain `Nat.sqrt r` and the logarithmic overhead. See [Ambainis2005] for the
mathematical background.

## Main statements

* `corollary1_answer`: guarantees for a supplied collision solver.
* `corollary2_answer`: the two-collision specialization.
* `amplification_reaches`: a product failure-count estimate.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

namespace Qatlib.Concepts.WalkSearch.CollisionSearch

/-- The real-valued walk cost `s + (n / r) ^ (k / 2) * (c + sqrt r * u)`. -/
def sourceWalkCost (s u c : ℝ) (n r k : ℝ) : ℝ :=
  s + (n / r) ^ (k / 2) * (c + Real.sqrt r * u)

/-- For the two-collision exponent, `(n / r) ^ (2 / 2)` simplifies to `n / r`. -/
theorem k2_exponent (n r : ℝ) :
    (n / r) ^ (((2 : ℕ) : ℝ) / 2) = n / r := by
  rw [show (((2 : ℕ) : ℝ) / 2) = 1 by norm_num, Real.rpow_one]

/-- If `F.card * q ≤ Fintype.card S`, then the number of length-`m` sequences entirely in `F`,
multiplied by `q ^ m`, is at most `Fintype.card S ^ m`. -/
theorem product_fail_ratio {S : Type*} [Fintype S] [DecidableEq S]
    (F : Finset S) {q : ℕ} (_hq : 0 < q) (hm : F.card * q ≤ Fintype.card S) (m : ℕ) :
    Fintype.card (Fin m → {x // x ∈ F}) * q ^ m ≤ Fintype.card S ^ m := by
  have hF : Fintype.card {x // x ∈ F} = F.card := by
    rw [Fintype.card_coe]
  rw [Fintype.card_fun, hF, Fintype.card_fin, ← mul_pow]
  exact Nat.pow_le_pow_left hm m

/-- If `F.card * q ≤ Fintype.card S` for `q ≥ 2`, then for every positive `D` some repetition
count makes the all-failure sequence count multiplied by `D` at most the total sequence
count. -/
theorem amplification_reaches {S : Type*} [Fintype S] [DecidableEq S]
    (F : Finset S) {q : ℕ} (hq : 2 ≤ q) (hm : F.card * q ≤ Fintype.card S)
    (D : ℕ) (_hD : 0 < D) :
    ∃ m : ℕ, Fintype.card (Fin m → {x // x ∈ F}) * D ≤ Fintype.card S ^ m := by

  obtain ⟨m, hmD⟩ : ∃ m : ℕ, D ≤ q ^ m := by
    refine ⟨D, ?_⟩
    have h1 : D ≤ 2 ^ D := le_of_lt (Nat.lt_two_pow_self (n := D))
    exact h1.trans (Nat.pow_le_pow_left hq D)
  exact ⟨m, by
    have hb := product_fail_ratio F (by omega : 0 < q) hm m
    have hleft : Fintype.card (Fin m → {x // x ∈ F}) * D ≤
        Fintype.card (Fin m → {x // x ∈ F}) * q ^ m :=
      Nat.mul_le_mul_left _ hmD
    exact hleft.trans hb⟩

/-- For a supplied `KCollisionSolver` with `κ ≥ 1` and `1 ≤ r ≤ n`, bounds every seed's cost by
the stated logarithmic overhead times the real-exponent collision-search expression. -/
theorem corollary1_cost (kcs : KCollisionSolver) (hκ : 1 ≤ kcs.κ)
    {n k : ℕ} (r : ℕ) (R : (Fin k → Fin n) → Bool) (s u c : ℕ) (ρ : kcs.seed)
    (hr : 1 ≤ r) (hrn : r ≤ n) :
    (kcs.cost r R s u c ρ : ℝ) ≤
      (kcs.κ : ℝ) * ((Nat.log 2 (n + 1) + 2 : ℕ) : ℝ) *
        (s + ((n : ℝ) / r) ^ ((k : ℝ) / 2) * (c + (Nat.sqrt r : ℝ) * u)) :=
  Qatlib.Concepts.WalkSearch.CollisionSearch.realExponentTransport_answer
    kcs hκ n k r s u c R ρ hr hrn

/-- For a supplied collision solver, combines soundness, rejection of empty relations, the
polynomial failure-count bound, and the real-exponent cost bound under `κ ≥ 1` and `1 ≤ r ≤
n`. See [Ambainis2005]. -/
theorem corollary1_answer (kcs : KCollisionSolver) (hκ : 1 ≤ kcs.κ)
    {n k : ℕ} (r : ℕ) (R : (Fin k → Fin n) → Bool) (s u c : ℕ)
    (hr : 1 ≤ r) (hrn : r ≤ n) :
    (∀ (ρ : kcs.seed) {t : Fin k → Fin n}, kcs.run r R s u c ρ = some t → R t = true) ∧
      (∀ (ρ : kcs.seed), (∀ t, R t = false) → kcs.run r R s u c ρ = none) ∧
      ((∃ t, R t = true) →
        ((@Finset.univ kcs.seed kcs.seedFin).filter
            (fun ρ : kcs.seed => kcs.run r R s u c ρ = none)).card *
          (n + 1) ^ kcs.cExp ≤ @Fintype.card kcs.seed kcs.seedFin) ∧
      (∀ ρ : kcs.seed, (kcs.cost r R s u c ρ : ℝ) ≤
        (kcs.κ : ℝ) * ((Nat.log 2 (n + 1) + 2 : ℕ) : ℝ) *
          (s + ((n : ℝ) / r) ^ ((k : ℝ) / 2) * (c + (Nat.sqrt r : ℝ) * u))) :=
  ⟨fun ρ _ h => kcs.sound r R s u c ρ h,
    fun ρ h => kcs.reject r R s u c ρ h,
    fun h => kcs.finds r R s u c h,
    fun ρ => corollary1_cost kcs hκ r R s u c ρ hr hrn⟩

/-- For a collision solver's seed space, the stated failure-count ratio with `q ≥ 2` yields a
repetition count meeting any prescribed positive integer amplification factor. -/
theorem corollary1_amplify (kcs : KCollisionSolver) (F : Finset kcs.seed) {q : ℕ}
    (hq : 2 ≤ q) (hm : F.card * q ≤ @Fintype.card kcs.seed kcs.seedFin) (D : ℕ)
    (hD : 0 < D) :
    ∃ m : ℕ, Fintype.card (Fin m → {x // x ∈ F}) * D ≤
      @Fintype.card kcs.seed kcs.seedFin ^ m :=
  @amplification_reaches kcs.seed kcs.seedFin (Classical.decEq kcs.seed) F q hq hm D hD

/-- For a supplied two-collision solver with `κ ≥ 1` and `1 ≤ r ≤ n`, bounds the cost using the
factor `n / r` in place of the general real power. -/
theorem corollary2_cost (kcs : KCollisionSolver) (hκ : 1 ≤ kcs.κ)
    {n : ℕ} (r : ℕ) (R : (Fin 2 → Fin n) → Bool) (s u c : ℕ) (ρ : kcs.seed)
    (hr : 1 ≤ r) (hrn : r ≤ n) :
    (kcs.cost r R s u c ρ : ℝ) ≤
      (kcs.κ : ℝ) * ((Nat.log 2 (n + 1) + 2 : ℕ) : ℝ) *
        (s + ((n : ℝ) / r) * (c + (Nat.sqrt r : ℝ) * u)) := by
  have h := corollary1_cost kcs hκ (k := 2) r R s u c ρ hr hrn
  simp only [k2_exponent] at h
  exact h

/-- Specializes the supplied solver's soundness, rejection, failure-count, and cost guarantees
to two-collision search. See [Ambainis2005]. -/
theorem corollary2_answer (kcs : KCollisionSolver) (hκ : 1 ≤ kcs.κ)
    {n : ℕ} (r : ℕ) (R : (Fin 2 → Fin n) → Bool) (s u c : ℕ)
    (hr : 1 ≤ r) (hrn : r ≤ n) :
    (∀ (ρ : kcs.seed) {t : Fin 2 → Fin n}, kcs.run r R s u c ρ = some t → R t = true) ∧
      (∀ (ρ : kcs.seed), (∀ t, R t = false) → kcs.run r R s u c ρ = none) ∧
      ((∃ t, R t = true) →
        ((@Finset.univ kcs.seed kcs.seedFin).filter
            (fun ρ : kcs.seed => kcs.run r R s u c ρ = none)).card *
          (n + 1) ^ kcs.cExp ≤ @Fintype.card kcs.seed kcs.seedFin) ∧
      (∀ ρ : kcs.seed, (kcs.cost r R s u c ρ : ℝ) ≤
        (kcs.κ : ℝ) * ((Nat.log 2 (n + 1) + 2 : ℕ) : ℝ) *
          (s + ((n : ℝ) / r) * (c + (Nat.sqrt r : ℝ) * u))) :=
  ⟨fun ρ _ h => kcs.sound r R s u c ρ h,
    fun ρ h => kcs.reject r R s u c ρ h,
    fun h => kcs.finds r R s u c h,
    fun ρ => corollary2_cost kcs hκ r R s u c ρ hr hrn⟩

end Qatlib.Concepts.WalkSearch.CollisionSearch
