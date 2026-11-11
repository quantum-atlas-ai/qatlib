/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQudit14.MainResults.QuditGeneralization

set_option backward.isDefEq.respectTransparency false

/-!
# Ququart algorithm and its NMR demonstration (SingleQudit14, claim c004)

Gedik et al., fixed arXiv:1403.5861v3, Eqs. (4)–(6) and the surrounding text:

> For a four level quantum system (ququart), we can use the initial state
> `|ψ_2⟩ = (|1⟩ + i|2⟩ - |3⟩ - i|4⟩)/2` ... the standard quantum Fourier transformation
> (Eq. (4)) ... so that `|ψ_2⟩ = U_FT |2⟩`. ... the positive cyclic permutations ... map
> `|ψ_2⟩` onto `|ψ_2⟩, -i|ψ_2⟩, -|ψ_2⟩, and i|ψ_2⟩`. On the other hand, the negative cyclic
> permutations result in `-i|ψ_4⟩, -|ψ_4⟩, i|ψ_4⟩, and |ψ_4⟩` (Eqs. (5), (6)) ... Final state
> `|2⟩` indicates that the permutation is even, while `|4⟩` means that the permutation is odd.

> We have experimentally demonstrated the proposed algorithm using a quadrupolar NMR setup,
> and showed that it deterministically decides whether a given permutation, from a set of
> eight possible functions, of four objects is positive or negative cyclic with a single
> query to the black-box.

Encoding. Positions `1,2,3,4` are indexed by `ZMod 4` via `position - 1 ∈ {0,1,2,3}`; the
standard DFT of Eq. (4) is then `(i,k) ↦ exp(2πi·i·k/4) = stdAddChar (i * k)`, and
`|ψ_2⟩ = U_FT |2⟩` is its `k = 1` column `qftVec 1` (position `2` is index `1`). The paper's
four positive cyclic permutations `U_1,…,U_4` are the rotations `j ↦ j + s` and its four
negative cyclic permutations `U_5,…,U_8` are the reflections `j ↦ c - j`; they are the eight
elements of the dihedral group `D_4` acting on the four positions.

The purely algebraic algorithm (favourable case: even ⇒ `|2⟩`, odd ⇒ `|4⟩`) is formalised
below. The *experimental* NMR realisation in the paper (the spin-3/2 sodium quadrupolar
sample, the pulse sequence, and the measured density matrices with <6% gate/readout error)
is physical-hardware work outside the scope of a Lean algebraic statement; it is recorded
here only as context, not as a theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SingleQudit14.MainResults

/-- Fixed arXiv:1403.5861v3, Eqs. (5) and following: "Final state `|2⟩` indicates that the
permutation is even". For every positive cyclic (even) ququart permutation, the final state
after the oracle and the inverse Fourier transform is `|2⟩ = basisVec (1 : ZMod 4)` (position
`2` is index `1`), up to a nonzero scalar. -/
theorem ququart_positive_outcome_is_two (σ : Equiv.Perm (ZMod 4)) (hσ : IsPositiveCyclic σ) :
    ∃ c : ℂ, c ≠ 0 ∧
      qftInvVec (applyPerm σ (qftVec (1 : ZMod 4))) = c • basisVec (1 : ZMod 4) := by
  haveI : NeZero 4 := ⟨by decide⟩
  exact positive_outcome_basis σ hσ

/-- Fixed arXiv:1403.5861v3, Eqs. (6) and following: "while `|4⟩` means that the permutation
is odd". For every negative cyclic (odd) ququart permutation, the final state after the oracle
and the inverse Fourier transform is `|4⟩ = basisVec (3 : ZMod 4)` (position `4` is index `3`),
up to a nonzero scalar. -/
theorem ququart_negative_outcome_is_four (σ : Equiv.Perm (ZMod 4)) (hσ : IsNegativeCyclic σ) :
    ∃ c : ℂ, c ≠ 0 ∧
      qftInvVec (applyPerm σ (qftVec (1 : ZMod 4))) = c • basisVec (-1 : ZMod 4) := by
  haveI : NeZero 4 := ⟨by decide⟩
  exact negative_outcome_basis σ hσ

/-- The abstract outcome label `-1` in `ZMod 4` is the position-4 index `3`, i.e.
`|4⟩ = basisVec (3 : ZMod 4)`; this ties the negative-cyclic outcome `basisVec (-1)` to the
paper's final state `|4⟩`. -/
theorem ququart_four_is_index_three :
    basisVec (-1 : ZMod 4) = basisVec (3 : ZMod 4) := by
  have h : (-1 : ZMod 4) = ((4 - 1 : ℕ) : ZMod 4) := neg_one_eq_last (by norm_num)
  rw [h]
  norm_num

/-- Fixed arXiv:1403.5861v3, Eqs. (5), (6) and the surrounding text: "a set of eight possible
functions, of four objects ... positive or negative cyclic". The four rotations
`U_1,…,U_4` and the four reflections `U_5,…,U_8` are pairwise distinct: `ZMod 4` has `4`
elements, the rotation and reflection families are each injective on it, and a rotation is
never equal to a reflection. Hence the ququart algorithm's target set has exactly `4 + 4 = 8`
cyclic permutations. -/
theorem ququart_eight_cyclic_permutations :
    Fintype.card (ZMod 4) = 4 ∧
      Function.Injective (rotPerm : ZMod 4 → Equiv.Perm (ZMod 4)) ∧
      Function.Injective (reflPerm : ZMod 4 → Equiv.Perm (ZMod 4)) ∧
      (∀ s c : ZMod 4, rotPerm s ≠ reflPerm c) := by
  haveI : NeZero 4 := ⟨by decide⟩
  refine ⟨ZMod.card 4, rotPerm_injective, reflPerm_injective, ?_⟩
  intro s c
  exact rotPerm_ne_reflPerm (by norm_num) s c

end Qatlib.Papers.SingleQudit14.MainResults
