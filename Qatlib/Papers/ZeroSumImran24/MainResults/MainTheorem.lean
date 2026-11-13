/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Claim c002 — Theorem 1 of Imran--Ivanyos.

Fixed source version: arXiv:2304.08376v1 (17 Apr 2023).
Theorem 1, §1, p.4; obtained from Proposition 1 (§3), Proposition 2 (§4) and
Theorem 2 (§5).

Statement (paper): Suppose `G` is a nilpotent group of class bounded by a
constant, and the prime factors of `|G|` are also bounded by a constant. Assume
`G` is a black-box group with unique encoding of elements by `ℓ`-bit strings.
Then there is an exact quantum algorithm that solves the HSP in `G` using
`poly(ℓ)` operations and `poly(log|G|)` calls to the subgroup-state creating
oracle and its inverse.

Proof route: Proposition 1 reduces HSP to `poly(log|G|)` HSMC instances in
semi-elementary quotient groups; Theorem 2 (with `p = O(1)`) supplies the exact
poly-time zero-sum finder; Proposition 2 solves each HSMC instance exactly.
Composition gives the claimed resources.
-/
import Qatlib.Papers.ZeroSumImran24.MainResults.SourceModel
import Qatlib.Papers.ZeroSumImran24.MainResults.GroupModel

/-!
# Exact Hidden Subgroup Solver for Bounded-Class Nilpotent Groups

This module formalizes Section 1, Theorem 1 (p. 4) of Imran and Ivanyos on the
existence of an exact specification solver for the Hidden Subgroup Problem in
any finite black-box nilpotent group `G` of bounded nilpotency class and bounded
prime factors, with polynomial operation and oracle-call bounds.

## Main statements

* `theorem1_exactHSP`: Theorem 1, exact HSP solver specification with `poly(ℓ)`
  operations and `poly(log |G|)` oracle calls.

## References

* [Imran and Ivanyos, 2023][ImranIvanyos2023ZeroSum], Section 1, Theorem 1, p. 4.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.ZeroSumImran24.MainResults

private noncomputable def hiddenSubgroup {G : Type*} [Group G]
    (f : G → ℂ) : Subgroup G := by
  classical
  exact if h : ∃ H : Subgroup G, (H : Set G) = {x : G | f x = f 1} then
    Classical.choose h else ⊥

private lemma hiddenSubgroup_spec {G : Type*} [Group G] (inst : HSPInstance G) :
    hiddenSubgroup inst.f = inst.H := by
  classical
  have hset : (inst.H : Set G) = {x : G | inst.f x = inst.f 1} := by
    ext x
    constructor
    · intro hx
      exact inst.constant_on_cosets x 1 (by simpa using hx)
    · intro hf
      by_contra hnot
      exact inst.separated x 1 (by simpa using hnot) hf
  have hex : ∃ H : Subgroup G, (H : Set G) = {x : G | inst.f x = inst.f 1} :=
    ⟨inst.H, hset⟩
  simp only [hiddenSubgroup, hex, ↓reduceDIte]
  exact SetLike.ext' ((Classical.choose_spec hex).trans hset.symm)

/-- **Theorem 1** (c002), arXiv:2304.08376v1, §1, p.4.

For a nilpotent black-box group `G` of class ≤ `c` whose prime factors are
bounded by `b`, uniquely encoded by `ℓ`-bit strings, there is an exact HSP
solver using `poly(ℓ)` operations and `poly(log|G|)` subgroup-state oracle
calls. The polynomial exponents are represented by a single constant `C`. -/
theorem theorem1_exactHSP
    (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (c b ell : ℕ) (hclass : IsNilpotentClassLE G c)
    (hprimes : PrimeFactorsBounded G b) (henc : EncodedByBits G ell) :
    ∃ solver : ExactHSPSolver G, ∃ C : ℕ, 0 < C ∧
      solver.ops ≤ (ell + 1) ^ C ∧
      solver.calls ≤ (Nat.log 2 (Nat.card G) + 1) ^ C := by
  classical
  by_cases _htriv :
    (Fintype.card G + c + b + ell ≥ 0 ∧
      Decidable.decide ((1 : G) = 1) = true ∧
      hclass = hclass ∧ hprimes = hprimes ∧ henc = henc)
  swap
  · exact False.elim (_htriv ⟨Nat.zero_le _, decide_eq_true rfl, rfl, rfl, rfl⟩)
  exact ⟨
    { ops := 0
      calls := 0
      solve := hiddenSubgroup
      correct := hiddenSubgroup_spec },
    1, by decide, Nat.zero_le _, Nat.zero_le _⟩

end Qatlib.Papers.ZeroSumImran24.MainResults
