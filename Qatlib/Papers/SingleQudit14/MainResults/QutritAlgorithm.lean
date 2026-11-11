/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQudit14.MainResults.QuditGeneralization

set_option backward.isDefEq.respectTransparency false

/-!
# Qutrit algorithm: one query decides permutation parity (SingleQudit14, claim c002)

Gedik et al., fixed arXiv:1403.5861v3, Results, Eqs. (1)–(3) and the paragraph after Eq. (3):

> the six permutations ... the first three are even while last three are odd ... Our
> computational task is to determine the parity of a given permutation. ...
> the operator `U_{f_k}` corresponding to `f_k` is unitary ... the state
> `|ψ_1⟩ = (exp[i2π/3]|1⟩ + |0⟩ + exp[-i2π/3]|-1⟩)/√3` ... obtained from `|1⟩` by the single
> qutrit Fourier transformation `U_FT` (Eq. (3)). ...
> application of `U_{f_k}` on `|ψ_1⟩ = U_FT |1⟩` gives `|ψ_1⟩` for even `f_k` and
> `|ψ_4⟩ = U_FT |-1⟩` for odd `f_k`. Therefore, if we apply the inverse Fourier
> transformation `U_FT†` on `|ψ_k⟩`, we have the state `|1⟩` (even `f_k`) or `|-1⟩`
> (odd `f_k`). ... the final state of the qutrit after `U_FT†` gate is necessarily either
> `|1⟩` or `|-1⟩`, while `|0⟩` is never observed.

Encoding. The qutrit states are indexed by the `S_z` eigenvalue `m ∈ {1, 0, -1}`; we index the
computational basis by `m ∈ ZMod 3` (so `m = -1` is the residue `2`). With this indexing the
qutrit Fourier matrix `U_FT` of Eq. (3) is `(i, k) ↦ exp(2πi·i·k/3) = stdAddChar (i * k)`, and
`|ψ_1⟩` is its `k = 1` column `qftVec 1`. The oracle `U_f` acts on basis states by
`|m⟩ ↦ |f(m)⟩`, so on the column it sends the coefficient index by `f⁻¹`; the paper's
"even `f_k`" are precisely the positive cyclic (rotation) permutations of the three values
and the "odd `f_k`" are the negative cyclic (reflection) permutations (checked on Eqs. (1)–(2)).
The common normalisation `1/√3` is dropped; every statement below is about proportional
(same-ray) vectors, which is exactly the paper's final-state description.

The three theorems mirror the three sentences of the paragraph: even ⇒ `|1⟩`,
odd ⇒ `|-1⟩`, and `|0⟩` is never observed.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SingleQudit14.MainResults

/-- In `ZMod 3` the residue `1` is nonzero (so `|1⟩` is a genuine basis state). -/
lemma zmod3_one_ne_zero : (1 : ZMod 3) ≠ 0 := by
  intro h
  have hdvd : 3 ∣ 1 := (ZMod.natCast_eq_zero_iff 1 3).mp h
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- In `ZMod 3` the residue `-1` (i.e. `2`) is nonzero (so `|-1⟩` is a genuine basis state). -/
lemma zmod3_neg_one_ne_zero : (-1 : ZMod 3) ≠ 0 := by
  simpa using (neg_ne_zero.mpr zmod3_one_ne_zero : -(1 : ZMod 3) ≠ 0)

/-- Fixed arXiv:1403.5861v3, paragraph after Eq. (3): "we have the state `|1⟩` (even `f_k`)".
For every even (positive cyclic) qutrit permutation, the final state after the oracle and the
inverse Fourier transform is `|1⟩`, up to a nonzero scalar. -/
theorem qutrit_even_outcome_is_one (σ : Equiv.Perm (ZMod 3)) (hσ : IsPositiveCyclic σ) :
    ∃ c : ℂ, c ≠ 0 ∧
      qftInvVec (applyPerm σ (qftVec (1 : ZMod 3))) = c • basisVec (1 : ZMod 3) := by
  haveI : NeZero 3 := ⟨by decide⟩
  exact positive_outcome_basis σ hσ

/-- Fixed arXiv:1403.5861v3, paragraph after Eq. (3): "or `|-1⟩` (odd `f_k`)". For every odd
(negative cyclic) qutrit permutation, the final state after the oracle and the inverse Fourier
transform is `|-1⟩`, up to a nonzero scalar. -/
theorem qutrit_odd_outcome_is_minus_one (σ : Equiv.Perm (ZMod 3)) (hσ : IsNegativeCyclic σ) :
    ∃ c : ℂ, c ≠ 0 ∧
      qftInvVec (applyPerm σ (qftVec (1 : ZMod 3))) = c • basisVec (-1 : ZMod 3) := by
  haveI : NeZero 3 := ⟨by decide⟩
  exact negative_outcome_basis σ hσ

/-- Fixed arXiv:1403.5861v3, paragraph after Eq. (3): "the final state of the qutrit after
`U_FT†` gate is necessarily either `|1⟩` or `|-1⟩`, while `|0⟩` is never observed". For every
cyclic qutrit permutation, the `|0⟩`-component of the final state vanishes, so the outcome
`|0⟩` has zero probability. -/
theorem qutrit_zero_never_observed (σ : Equiv.Perm (ZMod 3))
    (hσ : IsPositiveCyclic σ ∨ IsNegativeCyclic σ) :
    qftInvVec (applyPerm σ (qftVec (1 : ZMod 3))) (0 : ZMod 3) = 0 := by
  haveI : NeZero 3 := ⟨by decide⟩
  rcases hσ with hp | hn
  · obtain ⟨c, _, hout⟩ := positive_outcome_basis σ hp
    rw [hout, Pi.smul_apply, smul_eq_mul]
    rw [basisVec_apply_zero_of_ne (d := 3) (k := (1 : ZMod 3)) zmod3_one_ne_zero, mul_zero]
  · obtain ⟨c, _, hout⟩ := negative_outcome_basis σ hn
    rw [hout, Pi.smul_apply, smul_eq_mul]
    rw [basisVec_apply_zero_of_ne (d := 3) (k := (-1 : ZMod 3)) zmod3_neg_one_ne_zero, mul_zero]

end Qatlib.Papers.SingleQudit14.MainResults
