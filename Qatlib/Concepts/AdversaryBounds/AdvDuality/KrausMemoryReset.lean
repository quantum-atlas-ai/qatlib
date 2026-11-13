/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.InstrumentCore.Measurement.Basic
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Mathlib.Tactic.Ext

/-!
# Resetting the auxiliary register of a Kraus dilation

`krausMemoryReset` swaps a measured auxiliary label with a designated initial label while acting
identically on the system. This unitary permutation permits repeated use of an auxiliary
register in the dilation representation of quantum operations described in [Kraus1971].

The branch identities show that selecting outcome `a` of a dilation and applying the reset
yields the branch `K a`, tensored with the initialized auxiliary state. Both state-vector and
operator versions are proved; the operator identity holds for arbitrary input operators.

## Main statements

* `kraus_memory_reset_unitary`: the reset permutation is unitary.
* `kraus_memory_reset_branch`: measurement followed by reset realizes a pure Kraus branch.
* `kraus_memory_reset_mixed_branch`: the corresponding operator identity.

## References

* [Kraus, 1971][Kraus1971]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

set_option autoImplicit false

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix

/-- The joint permutation gate that swaps auxiliary labels `a` and `zero` and acts identically
on the system. -/
noncomputable def krausMemoryReset {d s : ℕ} (zero a : Fin s) :
    Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ :=
  TensorGate (1 : Operator d) (permMatrix (Equiv.swap a zero))

/-- The auxiliary reset permutation is unitary. -/
theorem kraus_memory_reset_unitary {d s : ℕ} (zero a : Fin s) :
    krausMemoryReset (d := d) zero a ∈ Matrix.unitaryGroup (Fin d × Fin s) ℂ := by
  exact tensorGate_unitary (Submonoid.one_mem _)
    (permMatrix_unitary (fun b => Equiv.swap_apply_self a zero b))

/-- Selecting auxiliary outcome `a` of a dilation satisfying `hW` and resetting that label to
`zero` produces `K a` applied to the system, tensored with `Ket zero`. -/
theorem kraus_memory_reset_branch {d s : ℕ}
    (K : Fin s → Operator d) (zero a : Fin s)
    (W : Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ)
    (hW : ∀ psi : QState (Fin d),
      ApplyGate W (TensorState psi (Ket zero)) =
        fun x => ApplyGate (K x.2) psi x.1)
    (psi : QState (Fin d)) :
    ApplyGate (krausMemoryReset zero a)
        (Collapse (ApplyGate W (TensorState psi (Ket zero)))
          (Finset.univ.filter (fun x : Fin d × Fin s => x.2 = a))) =
      TensorState (ApplyGate (K a) psi) (Ket zero) := by
  have hcollapse :
      Collapse (ApplyGate W (TensorState psi (Ket zero)))
          (Finset.univ.filter (fun x : Fin d × Fin s => x.2 = a)) =
        TensorState (ApplyGate (K a) psi) (Ket a) := by
    rw [hW]
    funext ⟨i, b⟩
    by_cases hb : b = a
    · subst b
      simp [collapse_apply, tensorState_apply, ket_apply]
    · simp [collapse_apply, tensorState_apply, ket_apply, hb]
  rw [hcollapse, krausMemoryReset, applyGate_tensorGate, applyGate_one,
    applyGate_permMatrix_ket (fun b => Equiv.swap_apply_self a zero b),
    Equiv.swap_apply_left]

/-- Applying a matrix to the basis state `Ket j` extracts its column indexed by `j`. -/
private theorem krausMemoryReset_apply_ket {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (j i : I) : ApplyGate M (Ket j) i = M i j := by
  simp [ApplyGate, Matrix.mulVec, dotProduct, ket_apply, mul_ite]

/-- If the auxiliary-`zero` columns of `M` are given by `L`, the auxiliary block indexed by `b,
c` of the conjugated initialized operator is `L b * rho * (L c).conjTranspose`. -/
private theorem krausMemoryReset_joint_block {d s : ℕ}
    (L : Fin s → Operator d) (zero : Fin s)
    (M : Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ)
    (hcol : ∀ (i j : Fin d) (b : Fin s), M (i, b) (j, zero) = L b i j)
    (rho : Operator d) (i j : Fin d) (b c : Fin s) :
    (M * TensorGate rho (outerProduct (Ket zero)) * M.conjTranspose) (i, b) (j, c) =
      (L b * rho * (L c).conjTranspose) i j := by
  have hleft (k : Fin d) (e : Fin s) :
      (M * TensorGate rho (outerProduct (Ket zero))) (i, b) (k, e) =
        if e = zero then (L b * rho) i k else 0 := by
    by_cases he : e = zero
    · subst e
      simp [Matrix.mul_apply, tensorGate_apply, outerProduct_apply, ket_apply,
        Fintype.sum_prod_type, mul_ite, hcol]
    · simp [Matrix.mul_apply, tensorGate_apply, outerProduct_apply, ket_apply,
        Fintype.sum_prod_type, he]
  change (∑ y : Fin d × Fin s,
      (M * TensorGate rho (outerProduct (Ket zero))) (i, b) y *
        star (M (j, c) y)) =
    ∑ k : Fin d, (L b * rho) i k * star (L c j k)
  simp only [Fintype.sum_prod_type, hleft, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, hcol]

/-- Dilation followed by auxiliary outcome projection and reset maps an initialized joint
operator to `K a * rho * (K a).conjTranspose` tensored with the projector onto `Ket zero`. -/
theorem kraus_memory_reset_mixed_branch {d s : ℕ}
    (K : Fin s → Operator d) (zero a : Fin s)
    (W : Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ)
    (hW : ∀ psi : QState (Fin d),
      ApplyGate W (TensorState psi (Ket zero)) =
        fun x => ApplyGate (K x.2) psi x.1)
    (rho : Operator d) :
    let M := krausMemoryReset zero a *
      Projector (Finset.univ.filter (fun x : Fin d × Fin s => x.2 = a)) * W
    M * TensorGate rho (outerProduct (Ket zero)) * M.conjTranspose =
      TensorGate (K a * rho * (K a).conjTranspose) (outerProduct (Ket zero)) := by
  let M := krausMemoryReset zero a *
    Projector (Finset.univ.filter (fun x : Fin d × Fin s => x.2 = a)) * W
  let L : Fin s → Operator d := fun b => if b = zero then K a else 0
  have hact (psi : QState (Fin d)) :
      ApplyGate M (TensorState psi (Ket zero)) =
        TensorState (ApplyGate (K a) psi) (Ket zero) := by
    dsimp only [M]
    rw [applyGate_mul, applyGate_mul]
    exact kraus_memory_reset_branch K zero a W hW psi
  have hcol (i j : Fin d) (b : Fin s) : M (i, b) (j, zero) = L b i j := by
    have h := congrFun (hact (Ket j)) (i, b)
    rw [tensorState_ket_ket] at h
    by_cases hb : b = zero <;>
      simpa [L, tensorState_apply, krausMemoryReset_apply_ket, ket_apply, hb] using h
  change M * TensorGate rho (outerProduct (Ket zero)) * M.conjTranspose = _
  ext ⟨i, b⟩ ⟨j, c⟩
  rw [krausMemoryReset_joint_block L zero M hcol rho i j b c]
  by_cases hb : b = zero <;> by_cases hc : c = zero <;>
    simp [L, hb, hc, tensorGate_apply, outerProduct_apply, ket_apply]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
