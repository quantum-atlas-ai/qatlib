/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQudit14.MainResults.QuditGeneralization

set_option backward.isDefEq.respectTransparency false

/-!
# Main result: single-qudit one-query permutation parity (SingleQudit14, claim c001)

Gedik et al., fixed arXiv:1403.5861v3, Abstract and Results:

> we demonstrate that a quantum circuit with a single qudit can determine the parity of the
> permutation with only one evaluation ... a single query ... As in the case of Deutsch's
> algorithm, we obtain a speedup relative to the classical case, which requires two queries.
> ... the algorithm ... can be used to distinguish cyclic permutations according to their
> parity. ... this requires knowing at least two elements in the permutation, or, equivalently,
> knowing the values of the function for two variables classically.

> Although we can modify our algorithm for a single qubit ... this case is not interesting
> since the classical solution requires only a single evaluation ... neither entanglement nor
> any other correlation plays a role.

This file states the two halves of the main result as Lean theorems and combines them:

1. **Quantum upper bound (one query suffices).** For a single `d`-level qudit (`d ≥ 3`) and a
   cyclic permutation `σ` of the `d` values, one oracle call `U_f` sandwiched between `U_FT`
   and `U_FT†` leaves the pointer in the basis state `|1⟩` (positive cyclic) or `|d-1⟩`
   (negative cyclic), up to a nonzero scalar — so a single measurement of that one qudit
   reveals the cyclic orientation / parity. This is exactly the `c003` statement carried
   through the final inverse-DFT gate.

2. **Classical lower bound (one query is not enough).** No deterministic classical procedure
   that makes a single query `f ↦ f(x)` and maps the answer to a Boolean verdict can be
   correct on all cyclic permutations: at the very point `x` that it queries, the identity
   rotation `rotPerm 0` (positive) and the reflection `reflPerm (2x)` (negative) both return
   the value `x`, so the single answer `x` would have to certify both "positive" and
   "negative" simultaneously. Hence at least two queries are necessary.

Because the whole algorithm acts on the single state space `ZMod d → ℂ` (one register, a pure
qudit state; `applyPerm` and `qftInvVec` are ordinary endofunctions of that one register),
no entanglement or inter-register correlation is used — recorded in the docstring of
`single_qudit_main_result`, not separately formalised since there is no second subsystem.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SingleQudit14.MainResults

variable {d : ℕ} [NeZero d]

/-- Fixed arXiv:1403.5861v3, Abstract/Results. The one-query quantum circuit: after the oracle
`U_f` and the inverse Fourier transform, a positive cyclic permutation yields the pointer
state `|1⟩` (up to a nonzero scalar). This is the "one evaluation suffices" half of the main
result, valid for every `d ≥ 3`. -/
theorem quantum_positive_pointer (σ : Equiv.Perm (ZMod d)) (hσ : IsPositiveCyclic σ) :
    ∃ c : ℂ, c ≠ 0 ∧
      qftInvVec (applyPerm σ (qftVec (1 : ZMod d))) = c • basisVec (1 : ZMod d) :=
  positive_outcome_basis σ hσ

/-- Fixed arXiv:1403.5861v3, Abstract/Results. The one-query quantum circuit: after the oracle
`U_f` and the inverse Fourier transform, a negative cyclic permutation yields the pointer
state `|d-1⟩ = |-1⟩` (up to a nonzero scalar). -/
theorem quantum_negative_pointer (σ : Equiv.Perm (ZMod d)) (hσ : IsNegativeCyclic σ) :
    ∃ c : ℂ, c ≠ 0 ∧
      qftInvVec (applyPerm σ (qftVec (1 : ZMod d))) = c • basisVec (-1 : ZMod d) :=
  negative_outcome_basis σ hσ

/-- For `d ≥ 3` the two pointer outcomes `|1⟩` and `|d-1⟩` are genuinely different basis
states, so reading the single qudit unambiguously distinguishes the two cyclic orientations. -/
theorem pointer_states_distinct (hd : 3 ≤ d) :
    basisVec (1 : ZMod d) ≠ basisVec (-1 : ZMod d) :=
  basisVec_ne_of_ne (one_ne_neg_one hd)

/-- For `d ≥ 3` a permutation cannot be both a positive and a negative cyclic permutation, so
"positive cyclic" vs "negative cyclic" is a well-defined (mutually exclusive) classification. -/
theorem positive_negative_exclusive (hd : 3 ≤ d) (σ : Equiv.Perm (ZMod d)) :
    ¬ (IsPositiveCyclic σ ∧ IsNegativeCyclic σ) := by
  rintro ⟨⟨s, hs⟩, ⟨c, hc⟩⟩
  exact rotPerm_ne_reflPerm hd s c (hs.symm.trans hc)

/-- Fixed arXiv:1403.5861v3, Abstract/Results. Classical lower bound: a single classical
query is insufficient to determine the parity / cyclic orientation. There is no deterministic
classical algorithm that chooses a query point `x`, reads the single value `f x`, and outputs a
verdict `A x (f x)` that is correct for every cyclic permutation; at the queried point `x` the
positive rotation `rotPerm 0` and the negative reflection `reflPerm (2 * x)` both equal `x`,
forcing the same answer to be both `true` and `false`. -/
theorem classical_one_query_insufficient (hd : 3 ≤ d) :
    ¬ ∃ (A : ZMod d → ZMod d → Bool) (x : ZMod d),
        (∀ f : Equiv.Perm (ZMod d), IsPositiveCyclic f → A x (f x) = true) ∧
        (∀ f : Equiv.Perm (ZMod d), IsNegativeCyclic f → A x (f x) = false) := by
  rintro ⟨A, x, hpos, hneg⟩
  have ht : A x x = true := by
    have := hpos (rotPerm 0) ⟨0, rfl⟩
    simpa using this
  have hx : (reflPerm (2 * x)) x = x := by
    rw [reflPerm_apply]
    ring
  have hf : A x x = false := by
    have := hneg (reflPerm (2 * x)) ⟨2 * x, rfl⟩
    rw [hx] at this
    exact this
  rw [ht] at hf
  cases hf

/-- Fixed arXiv:1403.5861v3, Abstract/Results. The main result of the paper, packaged: for a
single `d`-level qudit with `d ≥ 3`,

* a positive cyclic permutation gives the pointer state `|1⟩` (up to a nonzero scalar),
* a negative cyclic permutation gives `|d-1⟩` (up to a nonzero scalar),
* these two pointer states are distinct, so the single-qudit one-query circuit decides the
  cyclic orientation / parity, and
* no single-query classical algorithm can do the same (two classical queries are necessary).

The computation is carried by one pure qudit state (`ZMod d → ℂ`, a single register): all maps
involved (`applyPerm`, `qftInvVec`) are endofunctions of that one register, so no entanglement
or inter-register correlation is used. -/
theorem single_qudit_main_result (hd : 3 ≤ d) :
    (∀ σ : Equiv.Perm (ZMod d), IsPositiveCyclic σ →
        ∃ c : ℂ, c ≠ 0 ∧
          qftInvVec (applyPerm σ (qftVec (1 : ZMod d))) = c • basisVec (1 : ZMod d)) ∧
      (∀ σ : Equiv.Perm (ZMod d), IsNegativeCyclic σ →
        ∃ c : ℂ, c ≠ 0 ∧
          qftInvVec (applyPerm σ (qftVec (1 : ZMod d))) = c • basisVec (-1 : ZMod d)) ∧
      basisVec (1 : ZMod d) ≠ basisVec (-1 : ZMod d) ∧
      (¬ ∃ (A : ZMod d → ZMod d → Bool) (x : ZMod d),
        (∀ f : Equiv.Perm (ZMod d), IsPositiveCyclic f → A x (f x) = true) ∧
        (∀ f : Equiv.Perm (ZMod d), IsNegativeCyclic f → A x (f x) = false)) :=
  ⟨quantum_positive_pointer, quantum_negative_pointer,
    pointer_states_distinct hd, classical_one_query_insufficient hd⟩

end Qatlib.Papers.SingleQudit14.MainResults
