/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic
import Qatlib.Papers.KroneckerCoef23.MainResults.RowSumConjugation.ConjugationRowSum

set_option backward.isDefEq.respectTransparency false

/-!
# MultiplicityRowSum — Lemma 7 of Bravyi–Chowdhury–Gosset–Havlíček–Zhu

Fixed version: arXiv:2302.11454v3 (7 May 2024), Lemma 7, pp. 14–15 (supplementary).

Lemma 7 states that the multiplicity `m_λ` of the irreducible representation `ρ_λ` in the
conjugation representation `ρ_c` of `Sₙ` equals the row sum `R_λ` of Eq. (8).

The proof in the paper goes through Eq. (56):
`m_λ = (1/n!) Σ_g χ_λ(g) χ_c(g)`,
the character scalar product of `χ_λ` with `χ_c`; orthonormality of irreducible characters and
the identity `χ_c(g) = |Z(g)|` then identify this with the class sum `R_λ = Σ_{μ⊢n} χ_λ(μ)` of
Eq. (8) (the class sum is the Eq. (56) form of the row sum, see the last paragraph of the proof
of Lemma 7).  We formalise the multiplicity statement in exactly this form, with `rowSum χ` of
`RowSumConjugation` standing for `R_λ`.

The main theorem `lemma7_multiplicity_eq_rowSum` is stated for a finite group `G` (the paper's
case is `G = Equiv.Perm (Fin n)`) together with a family of irreducible `FDRep ℂ G` characters.
The hypothesis `hcharinv` records Eq. (54): the irreducible characters of `Sₙ` in the orthogonal
(Young) representation are real.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix CategoryTheory

namespace Qatlib.Papers.KroneckerCoef23.MainResults.MultiplicityConjugation

open Qatlib.Papers.KroneckerCoef23.MainResults.RowSumConjugation
open Qatlib.Papers.KroneckerCoef23.MainResults.KroneckerTrace

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The multiplicity of `ρ_λ` in `ρ_c` written as the character scalar product of Eq. (56):
`m_λ = (1/|G|) Σ_g χ_λ(g) χ_c(g)`. -/
def multiplicity (χ χc : G → ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, χ g * χc g

/-- The character-average expression of Eq. (56) for the conjugation character is the row sum
`R_χ` of Eq. (8). -/
theorem multiplicity_eq_rowSum (χ : G → ℂ) : multiplicity χ conjChar = rowSum χ := rfl

/-- The centralizer order is invariant under inversion, `|Z(g⁻¹)| = |Z(g)|`; equivalently the
conjugation character satisfies `χ_c(g⁻¹) = χ_c(g)` (used in the proof of Lemma 7). -/
theorem centralizerCard_inv (g : G) : centralizerCard g⁻¹ = centralizerCard g := by
  unfold centralizerCard
  refine Fintype.card_congr ?_
  refine
    { toFun := fun x : {x : G // x * g⁻¹ = g⁻¹ * x} => ⟨x.1⁻¹, ?_⟩
      invFun := fun x : {x : G // x * g = g * x} => ⟨x.1⁻¹, ?_⟩
      left_inv := fun x => Subtype.ext (inv_inv x.1)
      right_inv := fun x => Subtype.ext (inv_inv x.1) }
  · have h := congrArg (fun y : G => y⁻¹) x.2
    simpa [_root_.mul_inv_rev] using h.symm
  · have h := congrArg (fun y : G => y⁻¹) x.2
    simpa [_root_.mul_inv_rev] using h.symm

/-- The conjugation character is invariant under inversion: `χ_c(g⁻¹) = χ_c(g)`. -/
theorem conjChar_inv (g : G) : conjChar g⁻¹ = conjChar g := by
  simp [conjChar, centralizerCard_inv]

/-- **Lemma 7, Eq. (56) form** (fixed arXiv:2302.11454v3, p. 14):
if the character `χ_c` of the conjugation representation decomposes as
`χ_c = Σ_λ m_λ χ_λ` over a family of pairwise non-isomorphic irreducibles with real characters
(Eq. (54)), then the multiplicity of `χ_λ` is the character scalar product
`(1/|G|) Σ_g χ_λ(g) χ_c(g)`.

This is the computation `m_λ = (1/n!) Σ_g χ_λ(g) χ_c(g)` of Eq. (56), obtained from the
orthonormality of the irreducible characters (`FDRep.char_orthonormal`). -/
theorem lemma7_multiplicity_eq_character_average
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ι → FDRep ℂ G) (hS : ∀ i, Simple (ρ i))
    (m : ι → ℂ) (χc : G → ℂ)
    (hdecomp : ∀ g, χc g = ∑ i, m i * (ρ i).character g)
    (hinv : ∀ g, χc g⁻¹ = χc g)
    (hcharinv : ∀ i (g : G), (ρ i).character g⁻¹ = (ρ i).character g)
    (hdisj : ∀ i j, Nonempty (ρ i ≅ ρ j) → i = j)
    (i : ι) :
    m i = (Fintype.card G : ℂ)⁻¹ * ∑ g : G, (ρ i).character g * χc g := by
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  -- Orthonormality in the form `(1/|G|) Σ_g χ_i(g) χ_j(g) = δ_{ij}`.
  have horth : ∀ j : ι,
      (Fintype.card G : ℂ)⁻¹ * (∑ g : G, (ρ i).character g * (ρ j).character g)
        = if j = i then 1 else 0 := by
    intro j
    classical
    haveI hi : Simple (ρ i) := hS i
    haveI hj : Simple (ρ j) := hS j
    have h := FDRep.char_orthonormal (ρ i) (ρ j)
    have h' : (Fintype.card G : ℂ)⁻¹ * (∑ g : G, (ρ i).character g * (ρ j).character g)
        = if Nonempty (ρ i ≅ ρ j) then (1 : ℂ) else 0 := by
      rw [show (∑ g : G, (ρ i).character g * (ρ j).character g)
          = ∑ g : G, (ρ i).character g * (ρ j).character g⁻¹ from by
            refine Finset.sum_congr rfl fun g _ => ?_
            rw [hcharinv j g]]
      simpa [invOf_eq_inv, smul_eq_mul] using h
    rw [h']
    by_cases hji : j = i
    · subst hji; simp
    · have hn : ¬ Nonempty (ρ i ≅ ρ j) := fun hn => hji (hdisj i j hn).symm
      simp [hji, hn]
  -- Expand `χ_c` inside the scalar product and exchange the sums.
  have hexp : ∀ g : G, (ρ i).character g * χc g
      = ∑ j : ι, m j * ((ρ i).character g * (ρ j).character g) := by
    intro g
    rw [hdecomp g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hexp]
  rw [show (∑ g : G, ∑ j : ι, m j * ((ρ i).character g * (ρ j).character g))
      = ∑ j : ι, m j * (∑ g : G, (ρ i).character g * (ρ j).character g) from by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]]
  rw [show (Fintype.card G : ℂ)⁻¹ *
        (∑ j : ι, m j * (∑ g : G, (ρ i).character g * (ρ j).character g))
      = ∑ j : ι, m j *
          ((Fintype.card G : ℂ)⁻¹ * ∑ g : G, (ρ i).character g * (ρ j).character g) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring]
  simp_rw [horth]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Lemma 7** (fixed arXiv:2302.11454v3, pp. 14–15):
the multiplicity `m_λ` of the irreducible representation `ρ_λ` in the conjugation
representation `ρ_c` is the row sum `R_λ` of Eq. (8).

We model `ρ_c` by its character `χ_c = |Z(·)|` (`conjChar`) and the row sum `R_λ` by its
Eq. (56) character-sum form (`rowSum`), as in the last step of the paper's proof. -/
theorem lemma7_multiplicity_eq_rowSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ι → FDRep ℂ G) (hS : ∀ i, Simple (ρ i))
    (m : ι → ℂ)
    (hdecomp : ∀ g, conjChar g = ∑ j, m j * (ρ j).character g)
    (hcharinv : ∀ j (g : G), (ρ j).character g⁻¹ = (ρ j).character g)
    (hdisj : ∀ j j', Nonempty (ρ j ≅ ρ j') → j = j')
    (i : ι) :
    m i = rowSum (ρ i).character := by
  rw [← multiplicity_eq_rowSum]
  exact lemma7_multiplicity_eq_character_average ρ hS m conjChar hdecomp conjChar_inv
    hcharinv hdisj i

end Qatlib.Papers.KroneckerCoef23.MainResults.MultiplicityConjugation
