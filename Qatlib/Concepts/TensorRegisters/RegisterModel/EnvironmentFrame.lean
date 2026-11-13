/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-!
# Environment frames and matrix compression

The map `environmentFrame q` attaches a fixed environment vector to a system vector. Its adjoint
contracts against that environment vector, and `compression F q` expresses the resulting system
matrix after applying a joint matrix `F`. For background, see [Watrous2018].

## Main statements

* `environmentFrame_isometry`: a unit environment vector defines an isometric frame.
* `compression_entries`: explicit double-sum formula for compressed entries.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace Qatlib.Concepts.TensorRegisters.RegisterModel.EnvironmentFrame

/-- The product vector `(i, a) ↦ x i * q a` obtained by attaching environment amplitudes `q`. -/
def inflate {I E : Type} (q : E→ℂ) (x : I→ℂ) : I×E→ℂ :=fun p=>x p.1*q p.2

/-- The contraction of a joint vector against `q`, with entries `∑ a, star (q a) * v (i, a)`. -/
def capture {I E : Type} [Fintype E] (q : E→ℂ) (v : I×E→ℂ) : I→ℂ :=
  fun i=>∑ a : E,star (q a)*v (i,a)

/-- The matrix embedding a system vector by attaching the environment vector `q`. -/
def environmentFrame {I E : Type} [DecidableEq I] (q : E→ℂ) : Matrix (I×E) I ℂ :=
  fun p j=>if p.1=j then q p.2 else 0

/-- The system matrix `environmentFrame q` adjoint times `F` times `environmentFrame q`. -/
def compression {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (F : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) : Matrix I I ℂ :=
  (environmentFrame (I:=I) q)ᴴ*F*environmentFrame (I:=I) q

/-- Multiplication by the environment frame is the vector map `inflate q`. -/
theorem environmentFrame_action {I E : Type} [Fintype I] [DecidableEq I] (q : E→ℂ) (x : I→ℂ) :
    environmentFrame q*ᵥ x=inflate q x := by
  funext p
  simp [environmentFrame,Matrix.mulVec,dotProduct,inflate,eq_comm,mul_comm]

/-- Multiplication by the adjoint environment frame is the contraction `capture q`. -/
theorem environmentFrame_adjoint_action {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (q : E→ℂ) (v : I×E→ℂ) : (environmentFrame q)ᴴ*ᵥ v=capture q v := by
  funext i
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,environmentFrame,Matrix.conjTranspose_apply,
    capture,apply_ite,ite_mul]

/-- A compressed matrix acts by inflating the input, applying `F`, and capturing against `q`. -/
theorem compression_action {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (F : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) (x : I→ℂ) :
    compression F q*ᵥ x=capture q (F*ᵥ inflate q x) := by
  rw [compression,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
    environmentFrame_action,environmentFrame_adjoint_action]

/-- If the sum of squared environment amplitudes is one, the frame satisfies `Vᴴ * V = 1`. -/
theorem environmentFrame_isometry {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (q : E→ℂ) (hq : (∑ a : E,Complex.normSq (q a))=1) :
    (environmentFrame (I:=I) q)ᴴ*environmentFrame (I:=I) q=1 := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [Matrix.mul_apply,Fintype.sum_prod_type,environmentFrame,Matrix.conjTranspose_apply,
      apply_ite,ite_mul,Complex.conj_mul']
    have hh : (∑ a : E,‖q a‖^2)=1 := by simpa only [Complex.normSq_eq_norm_sq] using hq
    exact_mod_cast hh
  · simp [Matrix.mul_apply,Fintype.sum_prod_type,environmentFrame,Matrix.conjTranspose_apply,
      apply_ite,ite_mul,hij,Ne.symm hij]

/-- Each compressed entry is the sum of `star (q a) * F (i, a) (j, b) * q b` over environment
indices. -/
theorem compression_entries {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (F : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) (i j : I) :
    compression F q i j=∑ a : E,∑ b : E,star (q a)*F (i,a) (j,b)*q b := by
  simp [compression,Matrix.mul_apply,Fintype.sum_prod_type,environmentFrame,Matrix.conjTranspose_apply,
    apply_ite,ite_mul,Finset.sum_mul]
  rw [Finset.sum_comm]

end Qatlib.Concepts.TensorRegisters.RegisterModel.EnvironmentFrame
