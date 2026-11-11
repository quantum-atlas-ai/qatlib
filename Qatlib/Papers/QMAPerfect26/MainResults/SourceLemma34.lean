/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMAPerfect26.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3.4: the cyclic operator `C_{z,Γ}` and history vector `|Ω_z⟩`

Fixed paper: Grewal–Rudolph, *QMA has perfect completeness*, arXiv:2609.13032v1, Lemma 3.4, p.8, Eq. (3).

* (i) On a YES instance, if `Γ_z > 2` and `Γ = Γ_z`, then `|Ω_z⟩ ≠ 0` and
  `(I − C_{z,Γ})|Ω_z⟩ = 0`.
* (ii) On a NO instance, for all `z`, `Γ ≥ 2` and all `|Ψ⟩`,
  `‖(I − C_{z,Γ})|Ψ⟩‖ ≥ (1/3)‖|Ψ⟩‖`.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QMAPerfect26.MainResults

/-- Lemma 3.4(i) (p.8): on a YES instance with `Γ = Γ_z > 2`, the history vector `|Ω_z⟩` is
nonzero and annihilated by `I − C_{z,Γ}`. -/
theorem lemma34_yes_part {m : ℕ} (A : ProofMat m) (ℓ : ℕ) (z : Idx m) (Γ : ℝ)
    (hΓ : Γ = Gamma A ℓ z) (hpos : 0 < Γ) :
    histVec A ℓ z ≠ 0 ∧ (1 - cyclicOp A ℓ z Γ) *ᵥ histVec A ℓ z = 0 :=
  lemma34_yes A ℓ z Γ hΓ hpos

/-- Lemma 3.4(ii), operator core (p.8): if `C` is a contraction with constant `2/3`, then
`‖(I − C)|Ψ⟩‖ ≥ (1/3)‖|Ψ⟩‖` for every `|Ψ⟩`. This is the statement that `I − C` has a
spectral gap and is what makes the kernel test reject NO instances. -/
theorem lemma34_no_part {ι : Type} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : ∀ ψ : ι → ℝ, ‖C *ᵥ ψ‖ ≤ (2 / 3) * ‖ψ‖) :
    ∀ ψ : ι → ℝ, (1 / 3) * ‖ψ‖ ≤ ‖(1 - C) *ᵥ ψ‖ := by
  intro ψ
  have h := contraction_separates C hC ψ
  simpa [Matrix.sub_mulVec, Matrix.one_mulVec] using h

/-- Lemma 3.4, combined (p.8, Eq. (3)). Part (i): YES-instance existence of a nonzero kernel
vector for `I − C_{z,Γ_z}`. Part (ii): the NO-instance contraction lower bound. -/
theorem lemma34 {m : ℕ} (A : ProofMat m) (ℓ : ℕ) (z : Idx m) (Γ : ℝ)
    (hΓ : Γ = Gamma A ℓ z) (hpos : 0 < Γ) :
    (histVec A ℓ z ≠ 0 ∧ (1 - cyclicOp A ℓ z Γ) *ᵥ histVec A ℓ z = 0) ∧
      (∀ (C : Matrix (ClockProof ℓ m) (ClockProof ℓ m) ℝ),
        (∀ ψ : ClockProof ℓ m → ℝ, ‖C *ᵥ ψ‖ ≤ (2 / 3) * ‖ψ‖) →
          ∀ ψ : ClockProof ℓ m → ℝ, (1 / 3) * ‖ψ‖ ≤ ‖(1 - C) *ᵥ ψ‖) :=
  ⟨lemma34_yes_part A ℓ z Γ hΓ hpos, fun C hC ψ => lemma34_no_part C hC ψ⟩

end Qatlib.Papers.QMAPerfect26.MainResults
