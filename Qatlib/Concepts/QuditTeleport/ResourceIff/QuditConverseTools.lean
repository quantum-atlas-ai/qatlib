/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceConverseAux
import Qatlib.Concepts.FiniteLocc.LOCCProgram.PositiveBranchDecomposition
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1500000
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.FiniteLocc.LOCCProgram

namespace Qatlib.Concepts.QuditTeleport.ResourceIff
variable {n : ℕ}
open Matrix
open scoped Classical BigOperators ComplexOrder

theorem quditBobFirst_local_gate (A : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    relabelGate (quditBobFirstEquiv n) (TensorGate A (1 : Operator n)) =
      TensorGate (1 : Operator n) (relabelGate finProdFinEquiv A) := by
  ext x y
  change A (finProdFinEquiv.symm x.2) (finProdFinEquiv.symm y.2) *
      (1 : Operator n) x.1 y.1 =
    (1 : Operator n) x.1 y.1 * A (finProdFinEquiv.symm x.2) (finProdFinEquiv.symm y.2)
  exact mul_comm _ _

theorem quditBobBranchMarginal_positive
    (K : Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hω : ω.PosSemidef)
    (s : Fin n × Fin n) (ρ : Operator n) (hρ : ρ.PosSemidef) :
    (quditBobBranchMarginal n K ω s ρ).PosSemidef := by
  apply partialTrace_posSemidef
  apply converse_relabel_positive
  have hj := converse_relabel_positive (Equiv.prodAssoc (Fin n) (Fin n) (Fin n)).symm _
    (Qatlib.Foundations.PureStateMath.BornBridge.posSemidef_tensorGate hρ hω)
  simpa only [Matrix.conjTranspose_conjTranspose] using
    hj.conjTranspose_mul_mul_same (TensorGate (K s) (1 : Operator n))ᴴ

theorem quditBobBranchMarginal_add
    (K : Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (s : Fin n × Fin n) (A B : Operator n) :
    quditBobBranchMarginal n K ω s (A + B) = quditBobBranchMarginal n K ω s A + quditBobBranchMarginal n K ω s B := by
  simp only [quditBobBranchMarginal, TensorGate, Matrix.add_kronecker, relabelGate,
    Matrix.reindex_apply, Matrix.submatrix_add, Pi.add_apply,
    Matrix.mul_add, Matrix.add_mul, partialTrace_add]

theorem quditBobBranchMarginal_smul
    (K : Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (s : Fin n × Fin n) (c : ℂ) (A : Operator n) :
    quditBobBranchMarginal n K ω s (c • A) = c • quditBobBranchMarginal n K ω s A := by
  simp only [quditBobBranchMarginal, TensorGate, Matrix.smul_kronecker, relabelGate,
    Matrix.reindex_apply, Matrix.submatrix_smul, Pi.smul_apply,
    Matrix.mul_smul, Matrix.smul_mul, partialTrace_smul]

theorem quditBobBranchMarginal_bobFirst
    (K : Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (s : Fin n × Fin n) (ρ : Operator n) :
    quditBobBranchMarginal n K ω s ρ =
      PartialTrace (TensorGate (1 : Operator n) (relabelGate finProdFinEquiv (K s)) *
        relabelGate (quditBobFirstEquiv n)
          (relabelGate (Equiv.prodAssoc (Fin n) (Fin n) (Fin n)).symm (TensorGate ρ ω)) *
        (TensorGate (1 : Operator n) (relabelGate finProdFinEquiv (K s)))ᴴ) := by
  unfold quditBobBranchMarginal
  rw [converse_relabel_mul, converse_relabel_mul, converse_relabel_adjoint,
    quditBobFirst_local_gate]

theorem quditBobBranchMarginal_no_signalling
    (K : Fin n × Fin n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hK : ∑ s : Fin n × Fin n, (TensorGate (K s) (1 : Operator n))ᴴ *
      TensorGate (K s) (1 : Operator n) = 1) (ρ : Operator n) :
    ∑ s, quditBobBranchMarginal n K ω s ρ =
      (Matrix.trace ρ) • PartialTrace (relabelGate (Equiv.prodComm (Fin n) (Fin n)) ω) := by
  let V := fun s : Fin n × Fin n => TensorGate (1 : Operator n) (relabelGate finProdFinEquiv (K s))
  let X := relabelGate (quditBobFirstEquiv n)
    (relabelGate (Equiv.prodAssoc (Fin n) (Fin n) (Fin n)).symm (TensorGate ρ ω))
  have hc : ∑ s, (V s)ᴴ * V s = 1 := by
    have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ (quditBobFirstEquiv n)) hK
    simp only [map_sum, map_one, Matrix.reindexAlgEquiv_apply] at h
    change (∑ s, relabelGate (quditBobFirstEquiv n)
      ((TensorGate (K s) (1 : Operator n))ᴴ * TensorGate (K s) (1 : Operator n))) = 1 at h
    simp only [converse_relabel_mul, converse_relabel_adjoint, quditBobFirst_local_gate] at h
    exact h
  calc
    _ = ∑ s, PartialTrace (V s * X * (V s)ᴴ) := by simp only [quditBobBranchMarginal_bobFirst]; rfl
    _ = ∑ s, PartialTrace (X * ((V s)ᴴ * V s)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [partialTrace_discard_sandwich]
      simp only [V, tensorGate_conjTranspose, Matrix.conjTranspose_one, tensorGate_mul,
          Matrix.one_mul]
    _ = PartialTrace (X * (∑ s, (V s)ᴴ * V s)) := by rw [Matrix.mul_sum, partialTrace_sum]
    _ = PartialTrace X := by rw [hc, Matrix.mul_one]
    _ = _ := by
      ext i j
      change (∑ a : Fin (n * n), ρ ((finProdFinEquiv (m := n) (n := n)).symm a).1 ((finProdFinEquiv (m := n) (n := n)).symm a).1 *
        ω (((finProdFinEquiv (m := n) (n := n)).symm a).2, i) (((finProdFinEquiv (m := n) (n := n)).symm a).2, j)) =
        (Matrix.trace ρ) * ∑ b : Fin n, ω (b, i) (b, j)
      rw [← (finProdFinEquiv (m := n) (n := n)).sum_comp]
      simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.trace,
        Matrix.diag_apply, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm

end Qatlib.Concepts.QuditTeleport.ResourceIff
