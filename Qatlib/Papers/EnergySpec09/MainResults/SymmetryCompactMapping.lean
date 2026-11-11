/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.InstrumentCore.Measurement.Basic

/-!
# Compact registers for supported sectors

This module provides finite-dimensional support and reindexing facts for the symmetry-restricted
compact mapping discussed in [WangEtAl2008]. A finite sector `S` can be enumerated by `Fin
S.card`; `sectorRestrict` and `sectorMatrix` use such an enumeration to form its state vector
and matrix block.

The support-preservation theorems assume a block or entrywise condition excluding leakage from
the sector. The equality `sector_dynamics_on_register` identifies the restricted output with
multiplication by the sector matrix whenever the input is supported on `S`. These statements
take the sector and its matrix conditions as input.

## Main statements

* `collapse_preserved_of_block` and `leak_free_preserves_support`: the stated matrix conditions
  preserve sector support.
* `cross_block_entry_zero`: a zero projected block forces its entries to vanish.
* `irrep_subspace_register_equiv` and `compact_mapping_qubits_le`: sector enumeration and the
  base-two ceiling-logarithm bound.
* `sector_dynamics_on_register`: the restricted matrix exactly computes the sector coordinates
  of the output.

## References

* [Wang et al., 2008][WangEtAl2008]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

open scoped BigOperators Classical

namespace Qatlib.Papers.EnergySpec09.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- If `Projector S * U * Projector S = U * Projector S`, applying `U` preserves states fixed by
projection onto `S`. This is the support-preservation condition used for compact sectors in
[WangEtAl2008]. -/
theorem collapse_preserved_of_block {U : Matrix I I ℂ} {S : Finset I}
    (hblock : Projector S * U * Projector S = U * Projector S)
    {ψ : QState I} (hψ : Collapse ψ S = ψ) :
    Collapse (ApplyGate U ψ) S = ApplyGate U ψ := by
  unfold Collapse ApplyGate at *
  rw [← hψ]
  calc Projector S *ᵥ (U *ᵥ (Projector S *ᵥ ψ))
      = ((Projector S * U) * Projector S) *ᵥ ψ := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = (U * Projector S) *ᵥ ψ := by rw [hblock]
    _ = U *ᵥ (Projector S *ᵥ ψ) := by rw [← Matrix.mulVec_mulVec]

/-- A vanishing projected block from `T` to `S` forces every corresponding matrix entry to
vanish. This is the entrywise consequence of a block condition in the compact-mapping
setting of [WangEtAl2008]. -/
theorem cross_block_entry_zero {U : Matrix I I ℂ} {S T : Finset I}
    (hblock : Projector S * U * Projector T = 0) {i j : I} (hi : i ∈ S) (hj : j ∈ T) :
    U i j = 0 := by
  have hentry : (Projector S * U * Projector T) i j = U i j := by
    unfold Projector
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, if_pos hi, if_pos hj]
    ring
  rw [hblock] at hentry
  simpa using hentry.symm

omit [Fintype I] [DecidableEq I] in

/-- Every finite sector has an enumeration by `Fin S.card`. This gives the finite basis
relabeling used for the compact-sector discussion of [WangEtAl2008]. -/
theorem irrep_subspace_register_equiv (S : Finset I) :
    Nonempty (↥S ≃ Fin S.card) := by
  have hcard : Fintype.card ↥S = S.card := Fintype.card_coe S
  exact ⟨(Fintype.equivFin ↥S).trans (Equiv.cast (congrArg Fin hcard))⟩

omit [DecidableEq I] in

/-- The base-two ceiling-logarithm register bound for a finite sector is at most that of the
full finite basis. This supplies the dimension comparison for compact mapping in
[WangEtAl2008]. -/
theorem compact_mapping_qubits_le (S : Finset I) :
    Nat.clog 2 S.card ≤ Nat.clog 2 (Fintype.card I) :=
  Nat.clog_mono_right 2 (Finset.card_le_univ S)

/-- The coordinates of a state on `S`, relabeled by the specified equivalence from `S` to `Fin
S.card`. -/
noncomputable def sectorRestrict {S : Finset I} (e : ↥S ≃ Fin S.card) (ψ : QState I) :
    QState (Fin S.card) :=
  fun x => ψ (e.symm x : I)

/-- The matrix block with both indices in `S`, relabeled by the specified equivalence to `Fin
S.card`. -/
noncomputable def sectorMatrix {S : Finset I} (e : ↥S ≃ Fin S.card) (U : Matrix I I ℂ) :
    Matrix (Fin S.card) (Fin S.card) ℂ :=
  fun x y => U (e.symm x : I) (e.symm y : I)

/-- A matrix with no entries carrying amplitude from `S` to its complement sends a state
supported on `S` to another state supported on `S`. This is the entrywise support criterion
for the compact-sector setting of [WangEtAl2008]. -/
theorem leak_free_preserves_support {U : Matrix I I ℂ} {S : Finset I}
    (hU : ∀ i, i ∉ S → ∀ j ∈ S, U i j = 0) {ψ : QState I}
    (hψ : ∀ i, i ∉ S → ψ i = 0) {i : I} (hi : i ∉ S) :
    ApplyGate U ψ i = 0 := by
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_zero]
  intro j _
  by_cases hj : j ∈ S
  · rw [hU i hi j hj, zero_mul]
  · rw [hψ j hj, mul_zero]

omit [DecidableEq I] in

/-- For an input supported on `S`, restricting the full matrix action equals applying the
relabeled sector matrix to the restricted state. This is the exact coordinate identity used
for compact-sector dynamics in [WangEtAl2008]. -/
theorem sector_dynamics_on_register {U : Matrix I I ℂ} {S : Finset I}
    (e : ↥S ≃ Fin S.card) {ψ : QState I} (hψ : ∀ i, i ∉ S → ψ i = 0) :
    sectorRestrict e (ApplyGate U ψ) = ApplyGate (sectorMatrix e U) (sectorRestrict e ψ) := by
  funext x
  simp only [sectorRestrict, sectorMatrix, ApplyGate, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by rw [hψ j hj, mul_zero])]
  rw [← Finset.sum_attach]
  rw [Finset.attach_eq_univ]
  refine Fintype.sum_equiv e (fun a : ↥S => U (e.symm x : I) (a : I) * ψ (a : I))
    (fun y : Fin S.card => U (e.symm x : I) (e.symm y : I) * ψ (e.symm y : I)) (fun a => ?_)
  simp

end Qatlib.Papers.EnergySpec09.MainResults
