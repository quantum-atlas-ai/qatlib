/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QBoltzmann16.MainResults.VisibleSector

@[expose] public section

/-!
# Visible-sector projectors are orthogonal projections

The visible sector `v` of [AminEtAl2018] carries the projector `Λ_v = E_v E_v†` built from the
basis inclusion `Qatlib.Papers.QBoltzmann16.MainResults.visibleInclusion`. Its matrix entries are
`1` exactly at the diagonal positions whose visible coordinate is `v` and `0` elsewhere, so the
projector is Hermitian and idempotent. These are the two algebraic properties used when the Born
probability `Tr(Λ_v exp(-H))` is read as a measurement outcome weight.

The statements are index-register identities for the product register `Fin (M * H)`. They do not
prove the tensor product form `∏ ν (1 + v_ν σz_ν)/2` of the projector, and they do not construct
the transverse-field Hamiltonian.

## Main statements

* `visible_projector_isHermitian`: `Λ_v` is Hermitian.
* `visible_projector_idempotent`: `Λ_v` is idempotent.

## References

* [Amin et al., 2018][AminEtAl2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Matrix Matrix.Norms.L2Operator

namespace Qatlib.Papers.QBoltzmann16.MainResults

open Qatlib.Papers.QBoltzmann16.MainResults

/-- The visible-sector projector of `Qatlib.Papers.QBoltzmann16.MainResults.visibleInclusion` is
Hermitian, because it is the matrix product `A * Aᴴ` of a rectangular matrix with its adjoint
[AminEtAl2018]. -/
theorem visible_projector_isHermitian {M H : ℕ} (v : Fin M) :
    (visibleInclusion (H := H) v*(visibleInclusion (H := H) v)ᴴ).IsHermitian :=
  Matrix.isHermitian_mul_conjTranspose_self (visibleInclusion (H := H) v)

/-- The visible-sector projector of `Qatlib.Papers.QBoltzmann16.MainResults.visibleInclusion` is
idempotent: the product entry at `(r, s)` sums over the intermediate index `k`, and only `k = r`
survives, reproducing the single-entry projector [AminEtAl2018]. -/
theorem visible_projector_idempotent {M H : ℕ} (v : Fin M) :
    (visibleInclusion (H := H) v*(visibleInclusion (H := H) v)ᴴ)*
        (visibleInclusion (H := H) v*(visibleInclusion (H := H) v)ᴴ) =
      visibleInclusion (H := H) v*(visibleInclusion (H := H) v)ᴴ := by
  classical
  ext r s
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · by_cases hrs : r = s
    · subst hrs
      simp [visible_projector_entry]
    · simp [visible_projector_entry, hrs]
  · intro k _ hk
    rw [visible_projector_entry]
    simp [show r ≠ k from fun h => hk h.symm]
  · intro hr
    exact absurd (Finset.mem_univ r) hr

end Qatlib.Papers.QBoltzmann16.MainResults
