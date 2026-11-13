/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphIsom13.GiCost
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic

/-!
# A diagonal graph-isomorphism Hamiltonian

This module places the integer-string cost from [GaitanClark2014] on the diagonal of
`problemHamiltonian`. Computational basis vectors have their corresponding costs as eigenvalues,
and `minimumCost` vanishes exactly when the two graphs are isomorphic.

## Main statements

* `problemHamiltonian_mulVec_cbsKet`: the action on each computational basis vector.
* `minimumCost_zero_iff_iso`: the zero minimum-cost criterion.

## References

* [Gaitan and Clark, 2014][GaitanClark2014]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.GraphIsom13.DiagonalModel

open Qatlib.Papers.GraphIsom13.GiCost

/-- The computational basis vector supported at the integer string `s`. -/
def cbsKet {N : ℕ} (s : IntStr N) : IntStr N → ℂ :=
  Pi.single s 1

/-- The diagonal complex matrix whose entry at string `s` is the graph-isomorphism cost of `s`. -/
def problemHamiltonian {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    Matrix (IntStr N) (IntStr N) ℂ :=
  Matrix.diagonal (fun s => (cost G G' s : ℂ))

/-- Each computational basis vector is scaled by its string's graph-isomorphism cost under the
problem Hamiltonian. -/
theorem problemHamiltonian_mulVec_cbsKet {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (s : IntStr N) :
    problemHamiltonian G G' *ᵥ cbsKet s = (cost G G' s : ℂ) • cbsKet s := by
  unfold problemHamiltonian cbsKet
  rw [Matrix.diagonal_mulVec_single, mul_one]
  ext t
  by_cases h : t = s
  · subst h
    simp
  · simp [h]

/-- The finite set of graph-isomorphism costs attained by integer strings. -/
def energies {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] : Finset ℕ :=
  Finset.univ.image (cost G G')

/-- The set of attained graph-isomorphism costs is nonempty. -/
theorem energies_nonempty {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] : (energies G G').Nonempty := by
  unfold energies
  rw [Finset.image_nonempty]
  exact ⟨fun _ => ⟨0, Nat.pow_pos (by norm_num)⟩, Finset.mem_univ _⟩

/-- The least graph-isomorphism cost attained by an integer string. -/
def minimumCost {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] : ℕ :=
  (energies G G').min' (energies_nonempty G G')

/-- The minimum cost is zero if and only if some integer string has zero cost. -/
theorem minimumCost_eq_zero_iff {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    minimumCost G G' = 0 ↔ ∃ s : IntStr N, cost G G' s = 0 := by
  unfold minimumCost
  constructor
  · intro h
    have hmem : 0 ∈ energies G G' := by
      rw [← h]
      exact (energies G G').min'_mem (energies_nonempty G G')
    rw [energies, Finset.mem_image] at hmem
    obtain ⟨s, -, hs⟩ := hmem
    exact ⟨s, hs⟩
  · rintro ⟨s, hs⟩
    have hle : (energies G G').min' (energies_nonempty G G') ≤ cost G G' s :=
      (energies G G').min'_le (cost G G' s)
        (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩)
    have hge : 0 ≤ (energies G G').min' (energies_nonempty G G') := Nat.zero_le _
    omega

/-- The minimum cost is zero if and only if the two graphs are isomorphic. -/
theorem minimumCost_zero_iff_iso {N : ℕ}
    (G G' : SimpleGraph (Fin N)) [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    minimumCost G G' = 0 ↔ Nonempty (G ≃g G') :=
  (minimumCost_eq_zero_iff G G').trans (gi_cop_zero_iff G G')

end Qatlib.Papers.GraphIsom13.DiagonalModel
