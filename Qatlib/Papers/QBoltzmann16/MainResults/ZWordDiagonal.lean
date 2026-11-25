/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.PauliClifford.PauliBasis

@[expose] public section

/-!
# Diagonal register Pauli words

The tensor-product Pauli words of `Qatlib.Concepts.PauliClifford.PauliBasis.pauliWord` are indexed
by a four-valued letter at each site, with label `3` reserved for `Z`. Taking the same letter at
every site therefore yields the computational-basis diagonal operator `σz_a` of [AminEtAl2018]:
the entry at `(s, t)` vanishes off the diagonal, and the diagonal entries are the products of the
single-site eigenvalues `±1`.

This identifies the operator slot used by the diagonal Ising energy of Eq (9)-(11), and the unit
diagonal values supply the normalization used when such a word is inserted into a Gibbs average.
The statement is purely about the register Pauli basis; it does not construct the transverse-field
Hamiltonian or its Gibbs state.

## Main statements

* `pauliBool_three_apply`: the `Z` letter has entries `1, -1` on the diagonal and `0` off it.
* `pauliWord_z_offdiag`: an all-`Z` word vanishes at unequal register configurations.
* `pauliWord_z_diagonal`: an all-`Z` word is the diagonal operator of its own diagonal values.
* `pauliWord_z_diag_norm`: an all-`Z` word has unit norm on the diagonal.

## References

* [Amin et al., 2018][AminEtAl2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.QBoltzmann16.MainResults

open Qatlib.Foundations.PureStateMath Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.PauliClifford.PauliBasis

/-- The Boolean-indexed `Z` letter of the Pauli family has entry `-1` at equal `true` indices,
`1` at equal `false` indices, and `0` at unequal indices. -/
theorem pauliBool_three_apply (x y : Bool) :
    pauliBool 3 x y = if x = y then (if x then (-1 : ℂ) else 1) else 0 := by
  cases x <;> cases y <;> simp [pauliBool, PauliZ, Matrix.diagonal]

/-- An all-`Z` Pauli word vanishes at every pair of unequal register configurations, because the
single site where the two configurations differ contributes a zero matrix entry
[AminEtAl2018]. -/
theorem pauliWord_z_offdiag {N : ℕ} {s t : Reg N} (h : s ≠ t) :
    pauliWord (fun _ => (3 : Fin 4)) s t = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  rw [pauliBool_three_apply]
  simp [hj]

/-- The diagonal entries of an all-`Z` Pauli word are the products of the single-site eigenvalues
`-1` for `true` and `1` for `false` [AminEtAl2018]. -/
theorem pauliWord_z_diag_entry {N : ℕ} (s : Reg N) :
    pauliWord (fun _ => (3 : Fin 4)) s s = ∏ j, if s j then (-1 : ℂ) else 1 := by
  simp only [pauliWord, pauliBool_three_apply, ite_true]

/-- An all-`Z` Pauli word is the diagonal operator built from its own diagonal values, so its
off-diagonal matrix entries all vanish [AminEtAl2018]. -/
theorem pauliWord_z_diagonal {N : ℕ} :
    pauliWord (fun _ => (3 : Fin 4)) =
      Matrix.diagonal (fun s : Reg N => ∏ j, if s j then (-1 : ℂ) else 1) := by
  ext s t
  rw [Matrix.diagonal_apply]
  by_cases h : s = t
  · subst h
    simp [pauliWord_z_diag_entry]
  · rw [pauliWord_z_offdiag h]
    simp [h]

/-- An all-`Z` Pauli word has diagonal entries of modulus one, hence unit norm at every diagonal
position [AminEtAl2018]. -/
theorem pauliWord_z_diag_norm {N : ℕ} (s : Reg N) :
    ‖pauliWord (fun _ => (3 : Fin 4)) s s‖ = 1 := by
  rw [pauliWord_z_diag_entry, norm_prod]
  refine Finset.prod_eq_one (fun j _ => ?_)
  split_ifs <;> norm_num

end Qatlib.Papers.QBoltzmann16.MainResults
