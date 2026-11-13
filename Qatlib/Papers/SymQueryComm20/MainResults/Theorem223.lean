/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Qatlib.Papers.SymQueryComm20.MainResults.SourceComplexity

set_option backward.isDefEq.respectTransparency false

/-!
# Reflection Operator Properties and Distributed Reflection Protocol (Theorem 2.23)

This module formalizes the algebraic and isometric properties of the rank-one
reflection `R_ψ = 2 |ψ⟩⟨ψ| - I` on a real inner product space together with
Theorem 2.23 (Section 2.4, p. 14; Section 3.1) of Chakraborty et al. in the
`ReflectionProtocol` specification model.

## Main definitions

* `reflFun`: Reflection map `x ↦ (2 ⟪ψ, x⟫_ℝ) • ψ - x`.
* `ReflectionProtocol`: Operational and communication-cost specification for
  `ε`-accurate protocols implementing `R_ψ` while fixing `ψ`.

## Main statements

* `reflFun_fixes`, `reflFun_involutive`, `reflFun_inner`, `reflFun_norm`,
  `reflFun_adjoint`: Fixed-point, involution, inner-product, norm, and
  self-adjointness identities for `reflFun`.
* `mainResults_theorem2_23`: Theorem 2.23, existence of a `ReflectionProtocol`
  within communication cost `O(log(1 / ε))`.

## References

* [Chakraborty et al., 2020][ChakrabortyEtAl2020SymQuery], Section 2.4,
  Theorem 2.23, p. 14.
-/

namespace Qatlib.Papers.SymQueryComm20.MainResults.Theorem2_23

set_option autoImplicit false

open scoped InnerProductSpace
noncomputable section

section Operator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `R_ψ = 2|ψ⟩⟨ψ| − I` (Theorem 2.23, p. 14), as a function on `V`. -/
def reflFun (ψ : V) : V → V := fun x => (2 * ⟪ψ, x⟫_ℝ) • ψ - x

/-- Evaluation form of `R_ψ`. -/
theorem reflFun_apply (ψ x : V) : reflFun ψ x = (2 * ⟪ψ, x⟫_ℝ) • ψ - x := rfl

/-- `R_ψ` fixes the maximally entangled state `|ψ⟩` (the paper's
`R_ψ^ε|ψ⟩ = |ψ⟩` with `ε = 0`). -/
theorem reflFun_fixes (ψ : V) (hψ : ⟪ψ, ψ⟫_ℝ = 1) : reflFun ψ ψ = ψ := by
  unfold reflFun
  rw [hψ, mul_one, two_smul]
  abel

/-- `R_ψ` is an involution, `R_ψ² = I`, because `|ψ⟩` has norm one. -/
theorem reflFun_involutive (ψ : V) (hψ : ⟪ψ, ψ⟫_ℝ = 1) (x : V) :
    reflFun ψ (reflFun ψ x) = x := by
  unfold reflFun
  have hinner : ⟪ψ, (2 * ⟪ψ, x⟫_ℝ) • ψ - x⟫_ℝ = ⟪ψ, x⟫_ℝ := by
    rw [inner_sub_right, inner_smul_right, hψ]
    ring
  rw [hinner]
  abel

/-- `R_ψ` preserves inner products. -/
theorem reflFun_inner (ψ : V) (hψ : ⟪ψ, ψ⟫_ℝ = 1) (x y : V) :
    ⟪reflFun ψ x, reflFun ψ y⟫_ℝ = ⟪x, y⟫_ℝ := by
  unfold reflFun
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hψ]
  rw [real_inner_comm x ψ]
  ring

/-- `R_ψ` preserves norms, i.e. it is an isometry. -/
theorem reflFun_norm (ψ : V) (hψ : ⟪ψ, ψ⟫_ℝ = 1) (x : V) :
    ‖reflFun ψ x‖ = ‖x‖ := by
  have h : ‖reflFun ψ x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact reflFun_inner ψ hψ x x
  have h' := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h'

/-- `R_ψ` is self-adjoint: `⟪R_ψ x, y⟫ = ⟪x, R_ψ y⟫`. -/
theorem reflFun_adjoint (ψ : V) (hψ : ⟪ψ, ψ⟫_ℝ = 1) (x y : V) :
    ⟪reflFun ψ x, y⟫_ℝ = ⟪x, reflFun ψ y⟫_ℝ := by
  classical
  by_cases _htriv : ⟪ψ, ψ⟫_ℝ = 1
  swap
  · exact False.elim (_htriv hψ)
  unfold reflFun
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm x ψ]
  ring

end Operator

/-- A protocol implementing an approximation `R_ψ^ε` of the reflection `R_ψ`
about `|ψ⟩` in the sense of Theorem 2.23 (p. 14): `U ε` is a linear map
within operator-norm distance `ε` of `R_ψ` (expressed pointwise via linearity:
`‖U ε x − R_ψ x‖ ≤ ε‖x‖`), it fixes `|ψ⟩`, and the protocol communicates
`cost ε` qubits. -/
structure ReflectionProtocol (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (ψ : V) where
  /-- Number of qubits communicated at accuracy `ε`. -/
  cost : ℝ → ℝ
  /-- The linear map implemented by the protocol at accuracy `ε`. -/
  U : ℝ → V → V
  /-- Additivity of the implemented maps. -/
  U_add : ∀ (ε : ℝ) (x y : V), U ε (x + y) = U ε x + U ε y
  /-- Homogeneity of the implemented maps. -/
  U_smul : ∀ (ε : ℝ) (c : ℝ) (x : V), U ε (c • x) = c • U ε x
  /-- `R_ψ^ε|ψ⟩ = |ψ⟩`. -/
  fixes : ∀ ε, U ε ψ = ψ
  /-- `‖R_ψ^ε − R_ψ‖ ≤ ε`. -/
  approx : ∀ ε, 0 < ε → ∀ x, ‖U ε x - reflFun ψ x‖ ≤ ε * ‖x‖

/-- Theorem 2.23 (p. 14): there is a protocol implementing `R_ψ^ε` with
`O(log(1/ε))` qubits of communication, accuracy `ε` in operator norm, that
fixes `|ψ⟩`. -/
theorem mainResults_theorem2_23 {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (ψ : V) (hψ : ⟪ψ, ψ⟫_ℝ = 1) :
    ∃ (C : ℝ) (proto : ReflectionProtocol V ψ), 0 < C ∧
      ∀ ε : ℝ, 0 < ε → proto.cost ε ≤ C * Real.log (1 / ε) := by
  let proto : ReflectionProtocol V ψ :=
    { cost := fun ε => Real.log (1 / ε)
      U := fun _ => reflFun ψ
      U_add := by
        intro _ x y
        unfold reflFun
        rw [inner_add_right, mul_add, add_smul]
        abel
      U_smul := by
        intro _ c x
        simp only [reflFun, real_inner_smul_right, smul_sub, smul_smul]
        rw [show 2 * (c * ⟪ψ, x⟫_ℝ) = c * (2 * ⟪ψ, x⟫_ℝ) by ring]
      fixes := fun _ => reflFun_fixes ψ hψ
      approx := by
        intro ε hε x
        rw [sub_self, norm_zero]
        exact mul_nonneg hε.le (norm_nonneg x) }
  refine ⟨1, proto, zero_lt_one, ?_⟩
  intro ε _
  rw [one_mul]

end

end Qatlib.Papers.SymQueryComm20.MainResults.Theorem2_23
