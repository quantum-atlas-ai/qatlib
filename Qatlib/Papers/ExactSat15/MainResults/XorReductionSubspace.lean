/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card

set_option backward.isDefEq.respectTransparency false

/-!
# XOR-Reduction: the reduced candidate space

Paper: arXiv:1512.00859v2 (29 Aug 2016), *Faster than Classical Quantum Algorithm
for dense Formulas of Exact Satisfiability and Occupation Problems*, Sec. II,
Eqs. (4)–(6), p. 7–9.

This module formalises the combinatorial heart of the XOR-Reduction:

* the XORSAT instance associated with an Occupation instance is the linear system
  `A x ≡ b (mod 2)` (source Eq. (4)), where `A` is the `M × n` incidence matrix of
  the clauses and `b` records the negations together with the occupation number;
* if the system is consistent, its solution set has exactly `2^(n - M')` elements,
  with `M' ≤ min {n, M}` the number of linearly independent clauses (source
  Eq. (5)–(6) and the paragraph after Eq. (6));
* `M'` is the row rank of `A` and the kernel dimension is `k = n - M'`.

The candidate register of the quantum algorithm is exactly this solution set
(source: "This search actually takes place in the smaller register of `k` qubits").
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ExactSat15.MainResults.XorReductionSubspace

-- `ZMod 2` is a field; the `Fact (Nat.Prime 2)` instance is needed explicitly.
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

open Matrix

/-- The set of valid assignments of the XORSAT instance `A x ≡ b (mod 2)`
(source Eq. (4), p. 7): the assignments `x : (Fin n → ZMod 2)` satisfying all the
linear parity constraints. -/
def xorSolutionSet {n M : ℕ} (A : Matrix (Fin M) (Fin n) (ZMod 2))
    (b : Fin M → ZMod 2) : Type :=
  {x : Fin n → ZMod 2 // A.mulVec x = b}

/-- The solutions of a finite binary linear system form a finite type. -/
instance {n M : ℕ} (A : Matrix (Fin M) (Fin n) (ZMod 2)) (b : Fin M → ZMod 2) :
    Fintype (xorSolutionSet A b) := by
  classical exact Subtype.fintype _

/-- If `x₀` is one solution of `A x = b`, then `x ↦ x₀ + v` is a bijection between
the kernel of `A` and the whole affine solution set (source Eq. (6), p. 8:
`x(v₁,…,v_k) = v₁ξ₁ ⊕ … ⊕ v_kξ_k ⊕ ξ̄`). -/
def kernelEquivSolutionSet {n M : ℕ} (A : Matrix (Fin M) (Fin n) (ZMod 2))
    (b : Fin M → ZMod 2) (x₀ : Fin n → ZMod 2) (hx₀ : A.mulVec x₀ = b) :
    LinearMap.ker A.mulVecLin ≃ xorSolutionSet A b where
  toFun v :=
    ⟨x₀ + v.1, by
      rw [Matrix.mulVec_add, hx₀]
      have hv : A.mulVec v.1 = 0 := by
        simpa only [Matrix.mulVecLin_apply] using (LinearMap.mem_ker.mp v.2)
      rw [hv, add_zero]⟩
  invFun y :=
    ⟨y.1 - x₀, by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, hx₀, y.2, sub_self]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    simp
  right_inv y := by
    apply Subtype.ext
    funext i
    simp

/-- The kernel dimension of the XORSAT matrix is `k = n - M'`, where `M'` is the
row rank of `A` (source Eq. (5) and the line `M' = n - k`, p. 8). -/
theorem finrank_kernel_eq (n M : ℕ) (A : Matrix (Fin M) (Fin n) (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin) = n - Matrix.rank A := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hsrc : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [← Matrix.rank, hsrc] at h
  omega

/-- **Candidate-space cardinality** (source Eq. (6), p. 8): when the XORSAT system
is consistent, the number of assignments that are valid for the XORSAT relaxation
is exactly `2^(n - M')`, where `M' = rank A` is the number of linearly independent
clauses. -/
theorem card_xorSolutionSet_of_nonempty {n M : ℕ} (A : Matrix (Fin M) (Fin n) (ZMod 2))
    (b : Fin M → ZMod 2) (h : Nonempty (xorSolutionSet A b)) :
    Fintype.card (xorSolutionSet A b) = 2 ^ (n - Matrix.rank A) := by
  classical
  obtain ⟨x₀, hx₀⟩ := h
  have hcard : Fintype.card (xorSolutionSet A b) =
      Fintype.card (LinearMap.ker A.mulVecLin) :=
    (Fintype.card_congr (kernelEquivSolutionSet A b x₀ hx₀)).symm
  rw [hcard]
  calc Fintype.card ↥(LinearMap.ker A.mulVecLin)
      = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin) :=
        Module.card_eq_pow_finrank
    _ = 2 ^ (n - Matrix.rank A) := by
        rw [ZMod.card, finrank_kernel_eq n M A]

/-- The number `M'` of linearly independent clauses never exceeds `min {n, M}`
(source Eq. (5), p. 8: `M' = (n - k) ≤ min {n, M}`). -/
theorem rank_le_min {n M : ℕ} (A : Matrix (Fin M) (Fin n) (ZMod 2)) :
    Matrix.rank A ≤ min n M := by
  have h1 : Matrix.rank A ≤ n := by
    simpa using (Matrix.rank_le_card_width (A := A))
  have h2 : Matrix.rank A ≤ M := by
    simpa using (Matrix.rank_le_card_height (A := A))
  exact le_min h1 h2

/-- Consequence used by the complexity analysis: the reduced candidate space is
never larger than the full assignment space `2^n`, i.e. `2^(n - M') ≤ 2^n`. -/
theorem card_le_full_space {n M : ℕ} (A : Matrix (Fin M) (Fin n) (ZMod 2))
    (b : Fin M → ZMod 2) (h : Nonempty (xorSolutionSet A b)) :
    Fintype.card (xorSolutionSet A b) ≤ 2 ^ n := by
  rw [card_xorSolutionSet_of_nonempty A b h]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n (Matrix.rank A))

end Qatlib.Papers.ExactSat15.MainResults.XorReductionSubspace
