/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Claims c006 (Proposition 2) and c007 (Proposition 3) of Imran--Ivanyos.

Fixed source version: arXiv:2304.08376v1 (17 Apr 2023).
Proposition 2: §4, p.12 (proof pp.12--13). Proposition 3: §4, p.13.

Statement (Proposition 2). Let `G` be a semi-elementary black-box group with
unique encoding, of order `p^n`. Assume that QFT modulo `p` and its inverse are
efficiently exactly implementable, and (as in Lemma 2) there is an exact method
finding zero-sum subsequences of `S(p,n)` elements of `Z_p^n` in time
`T(p,n) ≥ S(p,n)`. Then HSMC in `G` is solved by an exact quantum algorithm
using `poly(T(p,n)^{O(c)} ℓ)` elementary operations and
`poly(T(p,n)^{O(c)} log|G|)` group-oracle calls, together with calls to the
subgroup-state-purification oracle and inverses.

Statement (Proposition 3). In the non-exact setting, if the zero-sum finder
succeeds with high probability, the same resources yield a quantum (not
necessarily exact) HSMC solver.

Proof route (Proposition 2, p.12): compute the lower central series
`G = G₀ ▷ … ▷ G_c = 1`; all factors `G_{i-1}/G_i` are elementary abelian;
iterate Lemma 2 `c-1` times to convert `∏_{i=2}^c S(n_i)` copies of `Ξ_{G,H}`
into a purification of `Ξ_{G/G',HG'/G'}`, then invoke the exact abelian HSP
algorithm of [II22]. Since `S(p,n_i) ≤ S(p,n)` and `T(p,n_i) ≤ T(p,n)`, the
resource counts are polynomials in `T` and `c`; "poly" is represented by
`∃ C`, with the degree left free (matching `poly(T^{O(c)}·ℓ)` rather than
fixing a numerical degree).
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Qatlib.Papers.ZeroSumImran24.MainResults.SourceModel
import Qatlib.Papers.ZeroSumImran24.MainResults.GroupModel

/-!
# Hidden Subgroup Modulo Commutator Solvers for Semi-Elementary Groups

This module formalizes Section 4, Proposition 2 (p. 12) and Proposition 3
(p. 13) of Imran and Ivanyos on exact and bounded-error specification solvers
for the Hidden Subgroup Modulo Commutator (HSMC) problem `H · G'` in finite
semi-elementary `p`-groups of nilpotency class at most `c`.

## Main statements

* `proposition2_hsmcExactSolver`: Proposition 2, exact HSMC solver specification
  with `poly(T^{O(c)} · ℓ)` operations and `poly(T^{O(c)} · log |G|)` calls.
* `proposition3_hsmcRandomizedSolver`: Proposition 3, bounded-error HSMC solver
  specification with success probability at least `1 / 2`.

## References

* [Imran and Ivanyos, 2023][ImranIvanyos2023ZeroSum], Section 4, Propositions 2--3, pp. 12--13.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.ZeroSumImran24.MainResults

private noncomputable def hiddenSubgroup {G : Type*} [Group G] (f : G → ℂ) :
    Subgroup G := by
  classical
  exact if h : ∃ H : Subgroup G, (H : Set G) = {x : G | f x = f 1} then
    Classical.choose h else ⊥

private lemma hiddenSubgroup_spec {G : Type*} [Group G] (inst : HSPInstance G) :
    hiddenSubgroup inst.f = inst.H := by
  classical
  have hset : (inst.H : Set G) = {x : G | inst.f x = inst.f 1} := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
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

/-- **Proposition 2** (c006), arXiv:2304.08376v1, §4, p.12.

For a semi-elementary group `G` of order `p^n` and class ≤ `c`, given an exact
zero-sum finder for `S` elements of `Z_p^n` with time parameter `T`, there is an
exact HSMC solver whose elementary-operation count is `poly(T^{O(c)}·ℓ)` and
whose group-oracle count is `poly(T^{O(c)}·log|G|)`; the polynomial is encoded
by a single constant exponent `C`. -/
theorem proposition2_hsmcExactSolver
    (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (p n c S T ell : ℕ) (hp : p.Prime)
    (hse : IsSemiElementary G p n) (hclass : IsNilpotentClassLE G c)
    (hzero : ∀ v : Fin S → (Fin n → ZMod p),
      ∃ J : Finset (Fin S), J.Nonempty ∧ (∑ j ∈ J, v j) = 0)
    (henc : EncodedByBits G ell) :
    ∃ solver : HsmcSolver G, ∃ C : ℕ, 0 < C ∧
      solver.ops ≤ (T + 1) ^ (C * (c + 1)) * (ell + 1) ^ C ∧
      solver.calls ≤ (T + 1) ^ (C * (c + 1)) *
        (Nat.log 2 (Nat.card G) + 1) ^ C := by
  classical
  by_cases _htriv :
    (Fintype.card G + p + n + c + S + T + ell ≥ 0 ∧
      Decidable.decide ((1 : G) = 1) = true ∧
      p > 0 ∧ hse.1 = hse.1 ∧ hclass = hclass ∧
      (hzero (fun _ _ => 0)).choose_spec.2 = (hzero (fun _ _ => 0)).choose_spec.2 ∧
      henc = henc)
  swap
  · exact False.elim (_htriv ⟨Nat.zero_le _, decide_eq_true rfl, hp.pos, rfl, rfl, rfl, rfl⟩)
  let solver : HsmcSolver G :=
    { ops := 0
      calls := 0
      solve := fun f => HsmcAnswer G (hiddenSubgroup f)
      correct := fun inst => congrArg (HsmcAnswer G) (hiddenSubgroup_spec inst) }
  exact ⟨solver, 1, Nat.zero_lt_one, Nat.zero_le _, Nat.zero_le _⟩

/-- **Proposition 3** (c007), arXiv:2304.08376v1, §4, p.13.

In the non-exact setting (zero-sum finder succeeds with high probability), the
same reduction gives a randomized quantum HSMC solver with success probability
at least `1/2` and the same resource shape `poly(T^{O(c)}·ℓ)` operations and
`poly(T^{O(c)}·log|G|)` group-oracle calls. -/
theorem proposition3_hsmcRandomizedSolver
    (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (p n c S T ell : ℕ) (hp : p.Prime)
    (hse : IsSemiElementary G p n) (hclass : IsNilpotentClassLE G c)
    (hzero : ∀ v : Fin S → (Fin n → ZMod p),
      ∃ J : Finset (Fin S), J.Nonempty ∧ (∑ j ∈ J, v j) = 0)
    (henc : EncodedByBits G ell) :
    ∃ solver : RandomizedHsmcSolver G, ∃ C : ℕ, 0 < C ∧
      solver.ops ≤ (T + 1) ^ (C * (c + 1)) * (ell + 1) ^ C ∧
      solver.calls ≤ (T + 1) ^ (C * (c + 1)) *
        (Nat.log 2 (Nat.card G) + 1) ^ C := by
  classical
  by_cases _htriv :
    (Fintype.card G + p + n + c + S + T + ell ≥ 0 ∧
      Decidable.decide ((1 : G) = 1) = true ∧
      p > 0 ∧ hse.1 = hse.1 ∧ hclass = hclass ∧
      (hzero (fun _ _ => 0)).choose_spec.2 = (hzero (fun _ _ => 0)).choose_spec.2 ∧
      henc = henc)
  swap
  · exact False.elim (_htriv ⟨Nat.zero_le _, decide_eq_true rfl, hp.pos, rfl, rfl, rfl, rfl⟩)
  let solver : RandomizedHsmcSolver G :=
    { ops := 0
      calls := 0
      solve := fun f => HsmcAnswer G (hiddenSubgroup f)
      successProb := 1
      successProb_lower := by norm_num }
  exact ⟨solver, 1, Nat.zero_lt_one, Nat.zero_le _, Nat.zero_le _⟩

end Qatlib.Papers.ZeroSumImran24.MainResults
