/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BeyondCircuit08.MainResults.Model.WordAlgebra

@[expose] public section

/-!
# Base cases of the density statements (Proposition 3 and Corollary 1)

Paper: Stephen P. Jordan, *Quantum Computation Beyond the Circuit Model*,
arXiv:0809.2307v1 (2008), §3.9, pp. 80–81.

The proof of Proposition 3 proceeds by induction on `n` with base cases
`n = 3` (the trivial group `SU(1)`, p. 80) and `n = 4` (Proposition 2).
This file proves the `n = 3` base case in full, together with the
one-dimensional base cases of Corollary 1 at `n = 1`: on a one-element
basis every special unitary is the identity, and the empty braid word
already attains it exactly, so density modulo phase holds with error `0`.

## Main statements

* `phaseDenseOn_of_card_eq_one`: on an index type of cardinality `1`,
  any set containing the identity matrix is dense modulo phase.
* `card_starStarBasis_three`: the `∗…∗` basis at `n = 3` has one element.
* `proposition3_base_case`: Proposition 3 at `n = 3`.
* `corollary1_starP_base_case`, `corollary1_pStar_base_case`: Corollary 1
  at `n = 1` for the `∗…p` and `p…∗` blocks.
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.BeyondCircuit08.MainResults.Density

open Qatlib.Papers.BeyondCircuit08.MainResults.Model

/-- On a one-element index type, every special unitary matrix equals the
identity (its single entry is its determinant), so any set `G` containing
the identity is dense modulo phase, with the phase `θ = 0` and error `0`. -/
theorem phaseDenseOn_of_card_eq_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : Set (Matrix ι ι ℂ)} (hcard : Fintype.card ι = 1)
    (h1 : (1 : Matrix ι ι ℂ) ∈ G) : PhaseDenseOn ι G := by
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hcard
  intro U hU ε hε
  have hdet : U.det = 1 := hU.2
  have hU1 : U = 1 := by
    apply Matrix.ext
    intro i j
    rw [ha i, ha j]
    have hdd : U a a = 1 := (Matrix.det_eq_elem_of_card_eq_one hcard a).symm.trans hdet
    rw [hdd]
    exact (Matrix.one_apply_eq a).symm
  refine ⟨1, h1, 0, ?_⟩
  rw [hU1]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul,
    sub_self, norm_zero]
  exact hε.le

/-- The `∗…∗` basis at `n = 3` has exactly one element, the string
`∗pp∗`: strings have length `4`, both endpoints are stars, and no two
stars are adjacent.  This is the dimension `f₂ = 1` of the `n = 3` base
case of Proposition 3 of [Jordan2008]. -/
theorem card_starStarBasis_three : Fintype.card (StarStarBasis 3) = 1 := by
  decide

/-- The `∗…p` basis at `n = 1` has exactly one element, the string `∗p`,
of dimension `f₁ = 1`. -/
theorem card_starPBasis_one : Fintype.card (StarPBasis 1) = 1 := by
  decide

/-- The `p…∗` basis at `n = 1` has exactly one element, the string `p∗`,
of dimension `f₁ = 1`. -/
theorem card_pStarBasis_one : Fintype.card (PStarBasis 1) = 1 := by
  decide

/-- **Proposition 3, base case `n = 3`** (arXiv:0809.2307v1, §3.9, p. 80).
`ρ_∗∗⁽³⁾(B₃)` modulo phase is dense in `SU(f₂) = SU(1)`: the block is
one-dimensional, every special unitary on it is the identity, and the
empty braid word attains the identity exactly. -/
theorem proposition3_base_case :
    PhaseDenseOn (StarStarBasis 3) (Set.range (evalWord (starStarGen 3))) :=
  phaseDenseOn_of_card_eq_one card_starStarBasis_three ⟨[], evalWord_nil _⟩

/-- **Corollary 1, base case `n = 1`, `∗…p` block** (arXiv:0809.2307v1,
§3.9, p. 80).  `ρ_∗p⁽¹⁾(B₁)` modulo phase is dense in `SU(f₁) = SU(1)`:
the block is one-dimensional and the empty word attains the identity. -/
theorem corollary1_starP_base_case :
    PhaseDenseOn (StarPBasis 1) (Set.range (evalWord (starPGen 1))) :=
  phaseDenseOn_of_card_eq_one card_starPBasis_one ⟨[], evalWord_nil _⟩

/-- **Corollary 1, base case `n = 1`, `p…∗` block** (arXiv:0809.2307v1,
§3.9, p. 80).  `ρ_p∗⁽¹⁾(B₁)` modulo phase is dense in `SU(f₁) = SU(1)`:
the block is one-dimensional and the empty word attains the identity. -/
theorem corollary1_pStar_base_case :
    PhaseDenseOn (PStarBasis 1) (Set.range (evalWord (pStarGen 1))) :=
  phaseDenseOn_of_card_eq_one card_pStarBasis_one ⟨[], evalWord_nil _⟩

end Qatlib.Papers.BeyondCircuit08.MainResults.Density
