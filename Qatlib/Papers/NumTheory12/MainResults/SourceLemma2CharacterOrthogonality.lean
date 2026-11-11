/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform

set_option backward.isDefEq.respectTransparency false

/-!
# NumTheory12.MainResults — Lemma 2 (character orthogonality)

Source: Wim van Dam and Yoshitaka Sasaki, *Quantum algorithms for problems in
number theory, algebraic geometry, and group theory*, fixed arXiv:1206.6126
(2012). Lemma 2, §5.1, page 8 (lines 354–364 of the pinned text).

The paper states, for a finite Abelian group `G` and a subgroup `H ≤ G`, that
for every character `Ψ` on `G`

```
 (1/|G|) ∑_{x ∈ G} Ψ(x) = 1  if Ψ is trivial,   0  if Ψ is nontrivial,
 (1/|H|) ∑_{x ∈ H} Ψ(x) = 1  if Ψ is trivial on H,  0  if Ψ is nontrivial on H.
```

Characters are written additively here (`AddChar G ℂ`), so "trivial on `G`"
is `Ψ = 0` (whose value is `1` everywhere, `AddChar.zero_apply`) and
"trivial on `H`" is `Ψ ∈ characterAnnihilator H`. The unnormalized pair of
identities and the annihilator criterion are the Frozen v2.0.2 theorems
`sum_character_subgroup`, `sum_character_mul_conj` and
`mem_characterAnnihilator`
(`QuantumAlgorithm.Concepts.QuditTeleport.TeleportCore`); the results below
only supply the paper's normalization and dichotomy.

No oracle, gate or cost model is involved: this is pure finite-abelian-group
arithmetic.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NumTheory12.MainResults

open scoped BigOperators Classical
open Qatlib.Concepts.QuditTeleport.TeleportCore

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- **Lemma 2, first identity** (arXiv:1206.6126, p. 8): the normalized sum of a
character over the whole finite Abelian group is `1` for the trivial character
and `0` for every nontrivial one.

Paper form: `(1/|G|) ∑_{x ∈ G} Ψ(x) = 1` if `Ψ` trivial, `0` otherwise.
"Trivial" is `Ψ = 0`; by `AddChar.eq_zero_iff` this is exactly `Ψ x = 1` for
all `x`. -/
theorem lemma2_average_over_group (χ : AddChar G ℂ) :
    (Fintype.card G : ℂ)⁻¹ * ∑ x : G, χ x = if χ = 0 then 1 else 0 := by
  classical
  rw [AddChar.sum_eq_ite χ]
  split_ifs with hχ
  · have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact inv_mul_cancel₀ hc
  · exact mul_zero _

/-- **Lemma 2, second identity** (arXiv:1206.6126, p. 8): the normalized sum of a
character over a subgroup `H` is `1` when the character is trivial on `H` and
`0` otherwise.

Paper form: `(1/|H|) ∑_{x ∈ H} Ψ(x) = 1` if `Ψ` trivial on `H`, `0` otherwise.
Triviality on `H` is membership in `characterAnnihilator H`, equivalent to
`∀ h : H, Ψ h = 1` by `mem_characterAnnihilator`. -/
theorem lemma2_average_over_subgroup (H : AddSubgroup G) (χ : AddChar G ℂ) :
    (Fintype.card H : ℂ)⁻¹ * ∑ h : H, χ h =
      if χ ∈ characterAnnihilator H then 1 else 0 := by
  classical
  rw [sum_character_subgroup H χ]
  split_ifs with hχ
  · have hc : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact inv_mul_cancel₀ hc
  · exact mul_zero _

/-- **Lemma 2** (arXiv:1206.6126, p. 8), both identities of the paper statement
in one conjunction. -/
theorem lemma2 (H : AddSubgroup G) (χ : AddChar G ℂ) :
    ((Fintype.card G : ℂ)⁻¹ * ∑ x : G, χ x = if χ = 0 then 1 else 0) ∧
      ((Fintype.card H : ℂ)⁻¹ * ∑ h : H, χ h =
        if χ ∈ characterAnnihilator H then 1 else 0) :=
  ⟨lemma2_average_over_group χ, lemma2_average_over_subgroup H χ⟩

/-- **Lemma 2 dictionary** (arXiv:1206.6126, p. 8): a character is the trivial
one exactly when it takes value `1` everywhere — the paper's "Ψ is trivial". -/
theorem lemma2_trivial_iff {G : Type*} [AddCommGroup G] (χ : AddChar G ℂ) :
    χ = 0 ↔ ∀ x : G, χ x = 1 :=
  AddChar.eq_zero_iff

/-- **Lemma 2 dictionary** (arXiv:1206.6126, p. 8): a character is trivial on the
subgroup `H` exactly when it restricts to the constant map `1` — the paper's
"Ψ is trivial on `H`". -/
theorem lemma2_trivial_on_subgroup_iff {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (χ : AddChar G ℂ) :
    χ ∈ characterAnnihilator H ↔ ∀ h : H, χ h = 1 :=
  mem_characterAnnihilator H χ

end Qatlib.Papers.NumTheory12.MainResults
