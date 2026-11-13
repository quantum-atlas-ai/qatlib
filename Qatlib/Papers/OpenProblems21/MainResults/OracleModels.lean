/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BitColumnAccess.ColumnAssemble.BitColumnValueAccess

set_option backward.isDefEq.respectTransparency false

/-!
# OpenProblems21.MainResults — the two query models of §9 (Problem 11)

Source: Scott Aaronson, *Open Problems Related to Quantum Query Complexity*,
arXiv:2109.06917v1 (fixed version), §9 "Comparing Query Models", p. 6, Problem 11.

The paper compares two oracle models for a function `f`:

* the **standard** (value / XOR) oracle `|x, a⟩ ↦ |x, a ⊕ f(x)⟩`; and
* for injective `f`, the **erasing** oracle `|x⟩ ↦ |f(x)⟩`, which erases the
  previous contents of the `|x⟩` register.

This module gives both models as concrete matrices over the computational
basis of `Qatlib.Concepts.MbqcFlow.FlowDecision` and proves the
structural facts that the paper takes for granted:

* the standard oracle is the value oracle
  `Qatlib.Foundations.BitColumnAccess.ColumnAssemble.valueMatrix`,
  and its action on basis states is the XOR update;
* the erasing oracle for `f : X → Y` is the matrix with columns `e_{f x}`;
  it maps `|x⟩` to `|f x⟩`, and it is an isometry exactly when `f` is
  injective (`Aᴴ * A = 1 ↔ Injective f`);
* when `f` is not injective the erasing oracle has a nontrivial kernel — this
  is the precise sense in which the paper's erasing oracle is "not inherently
  reversible";
* when `X = Y` and `f` is injective, the erasing oracle is a permutation
  matrix and hence unitary.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OpenProblems21.MainResults

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-! ## §1. The standard (value / XOR) oracle -/

/-- The paper's standard oracle `|x,a⟩ ↦ |x, a ⊕ f(x)⟩` (arXiv:2109.06917v1,
§9, p. 6) is exactly the value-oracle update
`Qatlib.Foundations.BitColumnAccess.ColumnAssemble.valueUpdate`. -/
theorem standardOracle_eq_valueUpdate {N b : ℕ} (f : Fin N → Reg b) :
    Qatlib.Concepts.BitColumnAccess.ColumnAssemble.valueUpdate f =
      fun s : Fin N × Reg b => (s.1, fun j => s.2 j ^^ f s.1 j) := rfl

/-- The standard oracle matrix is the value-oracle matrix
`Qatlib.Foundations.BitColumnAccess.ColumnAssemble.valueMatrix`. (arXiv:2109.06917v1, §9, p. 6). -/
theorem standardOracleMatrix_eq_valueMatrix {N b : ℕ} (f : Fin N → Reg b) :
    Qatlib.Concepts.BitColumnAccess.ColumnAssemble.valueMatrix f =
      permMatrix (fun s : Fin N × Reg b => (s.1, fun j => s.2 j ^^ f s.1 j)) := by
  rw [Qatlib.Concepts.BitColumnAccess.ColumnAssemble.valueMatrix,
    standardOracle_eq_valueUpdate]

/-- The standard oracle maps the basis state `|x,a⟩` to `|x, a ⊕ f(x)⟩`. (arXiv:2109.06917v1, §9, p. 6). -/
theorem standardOracle_ket {N b : ℕ} (f : Fin N → Reg b) (x : Fin N) (a : Reg b) :
    ApplyGate (Qatlib.Concepts.BitColumnAccess.ColumnAssemble.valueMatrix f)
        (Ket (x, a)) =
      Ket (x, fun j => a j ^^ f x j) := by
  rw [Qatlib.Concepts.BitColumnAccess.ColumnAssemble.valueMatrix]
  rw [applyGate_permMatrix_ket
    (Qatlib.Concepts.BitColumnAccess.ColumnAssemble.valueUpdate_involutive f)]
  rfl

/-- Two standard queries cancel: the XOR update is an involution, matching the
paper's "second oracle invocation to uncompute garbage" (§9, p. 6). -/
theorem standardOracle_involutive {N b : ℕ} (f : Fin N → Reg b) :
    Function.Involutive
      (fun s : Fin N × Reg b => (s.1, fun j => s.2 j ^^ f s.1 j)) := by
  intro s
  apply Prod.ext
  · rfl
  · funext j
    simp

/-- The standard oracle is unitary: it is a permutation gate. (arXiv:2109.06917v1, §9, p. 6). -/
theorem standardOracle_unitary {N b : ℕ} (f : Fin N → Reg b) :
    Qatlib.Concepts.BitColumnAccess.ColumnAssemble.valueMatrix f ∈
      Matrix.unitaryGroup (Fin N × Reg b) ℂ := by
  rw [Qatlib.Concepts.BitColumnAccess.ColumnAssemble.valueMatrix]
  exact permMatrix_unitary
    (Qatlib.Concepts.BitColumnAccess.ColumnAssemble.valueUpdate_involutive f)

/-! ## §2. The erasing oracle -/

/-- The **erasing oracle** for `f : X → Y` (arXiv:2109.06917v1, §9, p. 6):
the matrix whose column `x` is the basis vector `e_{f x}`, i.e.
`|x⟩ ↦ |f(x)⟩`, erasing the previous contents of the input register. -/
def erasingMatrix {X Y : Type*} [DecidableEq Y] (f : X → Y) : Matrix Y X ℂ :=
  Matrix.of fun y x => if f x = y then 1 else 0

/-- The erasing oracle sends the basis state `|x⟩` to `|f(x)⟩`. -/
theorem erasingMatrix_mulVec_ket {X Y : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq Y] (f : X → Y) (x : X) :
    erasingMatrix f *ᵥ Ket x = Ket (f x) := by
  funext y
  simp only [erasingMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, Ket]
  rw [Finset.sum_eq_single x]
  · simp [eq_comm]
  · intro z _ hz
    simp [hz]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- The Gram matrix of the erasing oracle: entry `(x, x')` is `1` exactly when
`f x = f x'`. Equivalently, the columns of the erasing oracle are orthonormal
exactly when `f` is injective. (arXiv:2109.06917v1, §9, p. 6). -/
theorem erasingMatrix_conjTranspose_mul_self {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] :
    ∀ (f : X → Y), (erasingMatrix f)ᴴ * erasingMatrix f =
      Matrix.of fun x x' => if f x = f x' then 1 else 0 := by
  intro f
  ext x x'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, erasingMatrix,
    Matrix.of_apply, RCLike.star_def]
  rw [Finset.sum_eq_single (f x')]
  · simp
  · intro y _ hy
    rw [if_neg (fun h : f x' = y => hy h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (f x')) h

/-- The erasing oracle is an isometry (`Aᴴ A = 1`) exactly when `f` is
injective. This is the matrix form of the paper's remark that the erasing
oracle "has the disadvantage of not being inherently reversible" (§9, p. 6):
reversibility requires injectivity. -/
theorem erasingMatrix_isometry_iff_injective {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y) :
    (erasingMatrix f)ᴴ * erasingMatrix f = 1 ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    have hentry := congrFun (congrFun h x) y
    rw [erasingMatrix_conjTranspose_mul_self, Matrix.one_apply] at hentry
    simp only [Matrix.of_apply] at hentry
    by_contra hne
    rw [if_pos hxy, if_neg hne] at hentry
    exact one_ne_zero hentry
  · intro hf
    rw [erasingMatrix_conjTranspose_mul_self]
    ext x y
    rw [Matrix.of_apply, Matrix.one_apply]
    by_cases h : x = y
    · subst h
      simp
    · have h' : f x ≠ f y := fun hfxy => h (hf hfxy)
      rw [if_neg h, if_neg h']

/-- If `f` is not injective, the erasing oracle annihilates a nonzero state:
the paper's "erasing" oracle cannot be inverted once two inputs collide. (arXiv:2109.06917v1, §9, p. 6). -/
theorem erasingMatrix_kernel_of_not_injective {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y) (hf : ¬ Function.Injective f) :
    ∃ ψ : QState X, ψ ≠ 0 ∧ erasingMatrix f *ᵥ ψ = 0 := by
  classical
  rw [Function.Injective] at hf
  push Not at hf
  obtain ⟨x, y, hxy, hne⟩ := hf
  refine ⟨Ket x - Ket y, ?_, ?_⟩
  · intro hzero
    have hx := congrFun hzero x
    simp [Ket, hne] at hx
  · rw [Matrix.mulVec_sub, erasingMatrix_mulVec_ket, erasingMatrix_mulVec_ket,
      hxy, sub_self]

/-- For an injective function on a common register the erasing oracle is a
permutation and hence a unitary oracle. (arXiv:2109.06917v1, §9, p. 6). -/
theorem erasingMatrix_mem_unitaryGroup_of_injective {X : Type*} [Fintype X]
    [DecidableEq X] (f : X → X) (hf : Function.Injective f) :
    erasingMatrix f ∈ Matrix.unitaryGroup X ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact (erasingMatrix_isometry_iff_injective f).mpr hf

/-- After an erasing query the input label is gone: the output has no
amplitude on labels outside the range of `f`, so the register holds `f(x)`
only (the paper's "erasing the previous contents of the `|x⟩` register"). (arXiv:2109.06917v1, §9, p. 6). -/
theorem erasingMatrix_mulVec_ket_eq_zero_of_not_mem_range {X Y : Type*}
    [Fintype X] [DecidableEq X] [DecidableEq Y] (f : X → Y) (x : X) (y : Y)
    (hy : ∀ x', f x' ≠ y) :
    (erasingMatrix f *ᵥ Ket x) y = 0 := by
  rw [erasingMatrix_mulVec_ket]
  simp only [Ket]
  rw [if_neg (fun h : y = f x => hy x h.symm)]

end Qatlib.Papers.OpenProblems21.MainResults
