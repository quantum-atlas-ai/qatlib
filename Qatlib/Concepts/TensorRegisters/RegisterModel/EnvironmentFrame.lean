/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace Qatlib.Concepts.TensorRegisters.RegisterModel.EnvironmentFrame

def inflate {I E : Type} (q : E→ℂ) (x : I→ℂ) : I×E→ℂ :=fun p=>x p.1*q p.2

def capture {I E : Type} [Fintype E] (q : E→ℂ) (v : I×E→ℂ) : I→ℂ :=
  fun i=>∑ a : E,star (q a)*v (i,a)

def environmentFrame {I E : Type} [DecidableEq I] (q : E→ℂ) : Matrix (I×E) I ℂ :=
  fun p j=>if p.1=j then q p.2 else 0

def compression {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (F : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) : Matrix I I ℂ :=
  (environmentFrame (I:=I) q)ᴴ*F*environmentFrame (I:=I) q

theorem environmentFrame_action {I E : Type} [Fintype I] [DecidableEq I] (q : E→ℂ) (x : I→ℂ) :
    environmentFrame q*ᵥ x=inflate q x := by
  funext p
  simp [environmentFrame,Matrix.mulVec,dotProduct,inflate,eq_comm,mul_comm]

theorem environmentFrame_adjoint_action {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (q : E→ℂ) (v : I×E→ℂ) : (environmentFrame q)ᴴ*ᵥ v=capture q v := by
  funext i
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,environmentFrame,Matrix.conjTranspose_apply,
    capture,apply_ite,ite_mul]

theorem compression_action {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (F : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) (x : I→ℂ) :
    compression F q*ᵥ x=capture q (F*ᵥ inflate q x) := by
  rw [compression,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
    environmentFrame_action,environmentFrame_adjoint_action]

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

theorem compression_entries {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (F : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) (i j : I) :
    compression F q i j=∑ a : E,∑ b : E,star (q a)*F (i,a) (j,b)*q b := by
  simp [compression,Matrix.mul_apply,Fintype.sum_prod_type,environmentFrame,Matrix.conjTranspose_apply,
    apply_ite,ite_mul,Finset.sum_mul]
  rw [Finset.sum_comm]

end Qatlib.Concepts.TensorRegisters.RegisterModel.EnvironmentFrame
