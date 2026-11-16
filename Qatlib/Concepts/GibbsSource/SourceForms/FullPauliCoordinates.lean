/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullPauliSparse

@[expose] public section


/-! # Exact computational coordinates of the full local Pauli family

The fixed register enumeration is used throughout. These formulas retain
the complex phase of `Y = i X Z`; no spectral change of basis is made.
-/

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.GibbsSource.FormAlgebra

namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators

/-- The bit at a physical site in the fixed computational enumeration. -/
noncomputable def fullPauliBit (n : ℕ) (i : Fin n)
    (x : Fin (fullPauliDim n)) : ZMod 2 :=
  (regIndexEquiv (Fin n)).symm x i

/-- Flip one physical bit, without changing the register enumeration. -/
noncomputable def fullPauliFlip (n : ℕ) (i : Fin n)
    (x : Fin (fullPauliDim n)) : Fin (fullPauliDim n) :=
  regIndexEquiv (Fin n) ((regIndexEquiv (Fin n)).symm x + Pi.single i 1)

/-- Flipping the same physical bit twice restores the original register index. -/
@[simp] theorem fullPauliFlip_flip (n : ℕ) (i : Fin n)
    (x : Fin (fullPauliDim n)) :
    fullPauliFlip n i (fullPauliFlip n i x) = x := by
  simp only [fullPauliFlip, Equiv.symm_apply_apply, add_assoc,
    binary_add_self, add_zero]
  simpa only using! (regIndexEquiv (Fin n)).apply_symm_apply x

/-- The actual site flip is an involutive permutation. -/
noncomputable def fullPauliFlipEquiv (n : ℕ) (i : Fin n) :
    Equiv.Perm (Fin (fullPauliDim n)) where
  toFun := fullPauliFlip n i
  invFun := fullPauliFlip n i
  left_inv := fullPauliFlip_flip n i
  right_inv := fullPauliFlip_flip n i

/-- The finite flip permutation acts by the same physical bit-flip map. -/
@[simp] theorem fullPauliFlipEquiv_apply (n : ℕ) (i : Fin n)
    (x : Fin (fullPauliDim n)) :
    fullPauliFlipEquiv n i x = fullPauliFlip n i x := rfl

/-- A physical bit flip adds one at the selected site. -/
@[simp] theorem fullPauliBit_flip_self (n : ℕ) (i : Fin n)
    (x : Fin (fullPauliDim n)) :
    fullPauliBit n i (fullPauliFlip n i x) = fullPauliBit n i x + 1 := by
  simp [fullPauliBit, fullPauliFlip]

/-- Full Pauli Bit flip of ne for the stated finite source data. -/
theorem fullPauliBit_flip_of_ne (n : ℕ) (i j : Fin n) (h : j ≠ i)
    (x : Fin (fullPauliDim n)) :
    fullPauliBit n j (fullPauliFlip n i x) = fullPauliBit n j x := by
  simp [fullPauliBit, fullPauliFlip, h]

/-- Full Pauli Flip ne for the stated finite source data. -/
theorem fullPauliFlip_ne (n : ℕ) (i : Fin n)
    (x : Fin (fullPauliDim n)) : fullPauliFlip n i x ≠ x := by
  intro h
  have hb := congrArg (fullPauliBit n i) h
  rw [fullPauliBit_flip_self] at hb
  have h10 : (1 : ZMod 2) = 0 :=
    add_left_cancel (hb.trans (add_zero _).symm)
  exact one_ne_zero h10

/-- Full Pauli Flip eq iff for the stated finite source data. -/
theorem fullPauliFlip_eq_iff (n : ℕ) (i : Fin n)
    (x y : Fin (fullPauliDim n)) :
    x = fullPauliFlip n i y ↔ y = fullPauliFlip n i x := by
  constructor <;> intro h <;> subst h <;> simp

/-- Every actual X entry is the indicator of a single site flip. -/
theorem fullPauliX_apply (n : ℕ) (i : Fin n)
    (a b : Fin (fullPauliDim n)) :
    fullPauliX n i a b = if a = fullPauliFlip n i b then 1 else 0 := by
  classical
  unfold fullPauliX
  rw [Matrix.coe_reindexAlgEquiv]
  change (if (regIndexEquiv (Fin n)).symm a =
    (regIndexEquiv (Fin n)).symm b + Pi.single i 1 then (1 : ℂ) else 0) = _
  have he : (regIndexEquiv (Fin n)).symm a =
      (regIndexEquiv (Fin n)).symm b + Pi.single i 1 ↔
      a = fullPauliFlip n i b := by
    constructor
    · intro h
      simpa only [fullPauliFlip] using!
        ((regIndexEquiv (Fin n)).apply_symm_apply a).symm.trans
          (congrArg (regIndexEquiv (Fin n)) h)
    · intro h
      simpa only [fullPauliFlip, Equiv.symm_apply_apply] using
        congrArg (regIndexEquiv (Fin n)).symm h
  simp only [he]

/-- The phase proposal is diagonal with its exact binary phase. -/
theorem fullPauliZ_apply (n : ℕ) (i : Fin n)
    (a b : Fin (fullPauliDim n)) :
    fullPauliZ n i a b = if a = b then phaseOfBit (fullPauliBit n i a) else 0 := by
  classical
  unfold fullPauliZ
  rw [Matrix.coe_reindexAlgEquiv]
  change cssPauliZ (Pi.single i 1) ((regIndexEquiv (Fin n)).symm a)
    ((regIndexEquiv (Fin n)).symm b) = _
  have he : (regIndexEquiv (Fin n)).symm a = (regIndexEquiv (Fin n)).symm b ↔
      a = b := by
    constructor
    · intro hab
      simpa only using! (regIndexEquiv (Fin n)).symm.injective hab
    · rintro rfl
      rfl
  simp [cssPauliZ, Matrix.diagonal_apply, fullPauliBit, bitDot_single_left, he]

/-- The actual Y entry retains the complex phase of its source bit. -/
theorem fullPauliY_apply (n : ℕ) (i : Fin n)
    (a b : Fin (fullPauliDim n)) :
    fullPauliY n i a b =
      if a = fullPauliFlip n i b then Complex.I * phaseOfBit (fullPauliBit n i b)
      else 0 := by
  classical
  simp [fullPauliY, Matrix.smul_apply, Matrix.mul_apply, fullPauliZ_apply,
    fullPauliX_apply, mul_ite, ite_mul]

/-- Full Pauli Phase norm Sq for the stated finite source data. -/
theorem fullPauliPhase_normSq (b : ZMod 2) :
    Complex.normSq (phaseOfBit b) = 1 := by
  unfold phaseOfBit
  split <;> norm_num

/-- Full Pauli X norm Sq for the stated finite source data. -/
theorem fullPauliX_normSq (n : ℕ) (i : Fin n)
    (a b : Fin (fullPauliDim n)) :
    Complex.normSq (fullPauliX n i a b) =
      if a = fullPauliFlip n i b then 1 else 0 := by
  rw [fullPauliX_apply]
  split <;> norm_num

/-- Full Pauli Y norm Sq for the stated finite source data. -/
theorem fullPauliY_normSq (n : ℕ) (i : Fin n)
    (a b : Fin (fullPauliDim n)) :
    Complex.normSq (fullPauliY n i a b) =
      if a = fullPauliFlip n i b then 1 else 0 := by
  rw [fullPauliY_apply]
  split <;> simp [Complex.normSq_mul, fullPauliPhase_normSq]

/-- Full Pauli Z norm Sq for the stated finite source data. -/
theorem fullPauliZ_normSq (n : ℕ) (i : Fin n)
    (a b : Fin (fullPauliDim n)) :
    Complex.normSq (fullPauliZ n i a b) = if a = b then 1 else 0 := by
  rw [fullPauliZ_apply]
  split <;> simp [fullPauliPhase_normSq]

end Qatlib.Concepts.GibbsSource.SourceForms
