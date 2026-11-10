/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.InstrumentCore.Measurement.Basic

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

open scoped BigOperators Classical

namespace Qatlib.Papers.EnergySpec09.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

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

theorem irrep_subspace_register_equiv (S : Finset I) :
    Nonempty (↥S ≃ Fin S.card) := by
  have hcard : Fintype.card ↥S = S.card := Fintype.card_coe S
  exact ⟨(Fintype.equivFin ↥S).trans (Equiv.cast (congrArg Fin hcard))⟩

omit [DecidableEq I] in

theorem compact_mapping_qubits_le (S : Finset I) :
    Nat.clog 2 S.card ≤ Nat.clog 2 (Fintype.card I) :=
  Nat.clog_mono_right 2 (Finset.card_le_univ S)

noncomputable def sectorRestrict {S : Finset I} (e : ↥S ≃ Fin S.card) (ψ : QState I) :
    QState (Fin S.card) :=
  fun x => ψ (e.symm x : I)

noncomputable def sectorMatrix {S : Finset I} (e : ↥S ≃ Fin S.card) (U : Matrix I I ℂ) :
    Matrix (Fin S.card) (Fin S.card) ℂ :=
  fun x y => U (e.symm x : I) (e.symm y : I)

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
