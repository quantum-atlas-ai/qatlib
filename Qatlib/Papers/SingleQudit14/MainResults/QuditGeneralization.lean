/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQudit14.MainResults.QuditFourier

set_option backward.isDefEq.respectTransparency false

/-!
# d-level qudit generalization (SingleQudit14, claim c003)

Gedik et al., fixed arXiv:1403.5861v3, Eq. (7) and the sentence immediately after it:

> Moving to a d-level quantum system (qudit), we can define
> `|ψ_k⟩ = (1/√d) ∑_{k'=1}^d exp[i 2π/d (k-1)(k'-1)] |k'⟩`.   (7)
> In this case, the positive cyclic permutations map `|ψ_2⟩` onto itself while the
> negative permutations give `|ψ_d⟩`.

We index the qudit computational basis by the residue `k ∈ ZMod d` of Eq. (7); with this
indexing the matrix `(i,k) ↦ exp(2πi·i·k/d)` is `qftVec k i = stdAddChar (i * k)`, and
`|ψ_1⟩` is the `k = 1` column (the paper's `|ψ_2⟩`, since `k` in Eq. (7) is one-based).
The normalisation `1/√d` is common to every column and is dropped; the statements below are
about proportional (same ray, up to a phase) vectors, exactly "onto itself" / "give |ψ_d⟩".

Faithful content:
* `positive_cyclic_maps_psi_two_to_itself` — a rotation `j ↦ j+s` scales `|ψ_2⟩` by the
  phase `stdAddChar s`, i.e. maps it onto itself.
* `negative_cyclic_maps_psi_two_to_psi_d` — a reflection `j ↦ c-j` sends `|ψ_2⟩` to
  `stdAddChar c` times `|ψ_d⟩ = qftVec (-1)` (and `-1 ≡ d-1`, the `d`-th column).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SingleQudit14.MainResults

variable {d : ℕ} [NeZero d]

/-- Fixed arXiv:1403.5861v3, Eq. (7) + following sentence. A positive cyclic permutation
(a rotation `j ↦ j + s`) maps `|ψ_2⟩` onto itself, up to the nonzero phase `stdAddChar s`. -/
theorem positive_cyclic_maps_psi_two_to_itself (σ : Equiv.Perm (ZMod d))
    (hσ : IsPositiveCyclic σ) :
    ∃ c : ℂ, c ≠ 0 ∧ applyPerm σ (qftVec (1 : ZMod d)) = c • qftVec (1 : ZMod d) := by
  obtain ⟨s, rfl⟩ := hσ
  refine ⟨ZMod.stdAddChar (N := d) (s * 1), stdAddChar_ne_zero _, ?_⟩
  exact applyPerm_rot s 1

/-- Fixed arXiv:1403.5861v3, Eq. (7) + following sentence. A negative cyclic permutation
(a reflection `j ↦ c - j`) sends `|ψ_2⟩` to the nonzero phase `stdAddChar c` times
`|ψ_d⟩ = qftVec (-1)` (the column `d-1 ≡ -1`). -/
theorem negative_cyclic_maps_psi_two_to_psi_d (σ : Equiv.Perm (ZMod d))
    (hσ : IsNegativeCyclic σ) :
    ∃ c : ℂ, c ≠ 0 ∧ applyPerm σ (qftVec (1 : ZMod d)) = c • qftVec (-1) := by
  obtain ⟨c, rfl⟩ := hσ
  exact ⟨ZMod.stdAddChar (N := d) (c * 1), stdAddChar_ne_zero _, applyPerm_refl c 1⟩

/-- Fixed arXiv:1403.5861v3, Eq. (7) + following sentence, packaged as one statement:
positive cyclic permutations preserve `|ψ_2⟩` (up to a phase) and negative cyclic
permutations send it to `|ψ_d⟩` (up to a phase). -/
theorem generalized_cyclic_orientation (σ : Equiv.Perm (ZMod d)) :
    (IsPositiveCyclic σ →
        ∃ c : ℂ, c ≠ 0 ∧ applyPerm σ (qftVec (1 : ZMod d)) = c • qftVec (1 : ZMod d)) ∧
      (IsNegativeCyclic σ →
        ∃ c : ℂ, c ≠ 0 ∧ applyPerm σ (qftVec (1 : ZMod d)) = c • qftVec (-1)) :=
  ⟨positive_cyclic_maps_psi_two_to_itself σ, negative_cyclic_maps_psi_two_to_psi_d σ⟩

/-- `-1` and `d - 1` agree in `ZMod d` (the reflection output is literally the paper's
`d`-th Fourier column `U_FT |d⟩ = |ψ_d⟩`). -/
lemma neg_one_eq_last (hd : 1 ≤ d) : (-1 : ZMod d) = ((d - 1 : ℕ) : ZMod d) := by
  rw [Nat.cast_sub hd, ZMod.natCast_self]
  ring

/-- The negative-cyclic output `qftVec (-1)` is the last Fourier column `qftVec (d-1)`,
i.e. exactly `|ψ_d⟩`. -/
theorem psi_d_eq_last_column (hd : 1 ≤ d) :
    qftVec (-1 : ZMod d) = qftVec (((d - 1 : ℕ)) : ZMod d) := by
  rw [neg_one_eq_last hd]

/-- Fixed arXiv:1403.5861v3, last gate of the circuit ("applying the inverse Fourier
transformation `U_FT†` ... we have the state `|1⟩` for even `f_k`"). A positive cyclic
permutation, after the oracle `U_f` and the inverse DFT `U_FT†`, leaves the unnormalised
basis state `|1⟩` up to a nonzero scalar: the pointer reads `|1⟩`, certifying an even /
positive-cyclic permutation. -/
theorem positive_outcome_basis (σ : Equiv.Perm (ZMod d)) (hσ : IsPositiveCyclic σ) :
    ∃ c : ℂ, c ≠ 0 ∧
      qftInvVec (applyPerm σ (qftVec (1 : ZMod d))) = c • basisVec (1 : ZMod d) := by
  obtain ⟨s, rfl⟩ := hσ
  refine ⟨ZMod.stdAddChar (N := d) (s * 1) * (d : ℂ),
    mul_ne_zero (stdAddChar_ne_zero _) (natCast_ne_zero_complex d), ?_⟩
  rw [applyPerm_rot, qftInvVec_smul, qftInvVec_qftVec, smul_smul]

/-- Fixed arXiv:1403.5861v3, last gate of the circuit ("`|−1⟩` (odd `f_k`)" and, for general
`d`, `|ψ_d⟩ = U_FT |d-1⟩`). A negative cyclic permutation, after the oracle and the inverse
DFT, leaves the unnormalised basis state `|d-1⟩ = |−1⟩` up to a nonzero scalar: the pointer
reads `|d-1⟩`, certifying an odd / negative-cyclic permutation. -/
theorem negative_outcome_basis (σ : Equiv.Perm (ZMod d)) (hσ : IsNegativeCyclic σ) :
    ∃ c : ℂ, c ≠ 0 ∧
      qftInvVec (applyPerm σ (qftVec (1 : ZMod d))) = c • basisVec (-1 : ZMod d) := by
  obtain ⟨c, rfl⟩ := hσ
  refine ⟨ZMod.stdAddChar (N := d) (c * 1) * (d : ℂ),
    mul_ne_zero (stdAddChar_ne_zero _) (natCast_ne_zero_complex d), ?_⟩
  rw [applyPerm_refl, qftInvVec_smul, qftInvVec_qftVec, smul_smul]

end Qatlib.Papers.SingleQudit14.MainResults
