/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9Aux
import Qatlib.Concepts.FiniteLocc.LOCCProgram.PositiveBranchDecomposition

/-!
# Qubit branch marginals and no-signalling

The results express `bobBranchMarginal` in Bob-first register order and prove input linearity
and positivity for positive semidefinite resources. Summing a complete four-outcome Alice-side
instrument yields the receiver resource marginal scaled by the input trace. The resource setting
is the qubit teleportation protocol of [BennettEtAl1993Teleportation].

## Main statements

* `bobBranchMarginal_positive`: For positive semidefinite resource and input operators, each Bob
  branch marginal is positive semidefinite.
* `bobBranchMarginal_bobFirst`: The Bob branch marginal equals the partial trace of the joint
  branch operator written in Bob-first register order.
* `bobBranchMarginal_no_signalling`: For a complete four-outcome Alice-side Kraus family, the
  sum of Bob's branch marginals is `trace ρ` times the resource's receiver marginal.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1500000
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.FiniteLocc.LOCCProgram

namespace Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped Classical BigOperators ComplexOrder

/-- Moving Bob's register first identifies Alice's local operator with the second tensor factor,
using `finProdFinEquiv` on Alice's indices. -/
theorem bobFirst_local_gate (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    relabelGate bobFirstEquiv (TensorGate A (1 : Operator 2)) =
      TensorGate (1 : Operator 2) (relabelGate finProdFinEquiv A) := by
  ext x y
  change A (finProdFinEquiv.symm x.2) (finProdFinEquiv.symm y.2) *
      (1 : Operator 2) x.1 y.1 =
    (1 : Operator 2) x.1 y.1 * A (finProdFinEquiv.symm x.2) (finProdFinEquiv.symm y.2)
  exact mul_comm _ _

/-- For positive semidefinite resource and input operators, each Bob branch marginal is positive
semidefinite. -/
theorem bobBranchMarginal_positive
    (K : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (ω : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hω : ω.PosSemidef)
    (s : Fin 4) (ρ : Operator 2) (hρ : ρ.PosSemidef) :
    (bobBranchMarginal K ω s ρ).PosSemidef := by
  apply partialTrace_posSemidef
  apply converse_relabel_positive
  have hj := converse_relabel_positive (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2)).symm _
    (Qatlib.Foundations.PureStateMath.BornBridge.posSemidef_tensorGate hρ hω)
  simpa only [Matrix.conjTranspose_conjTranspose] using
    hj.conjTranspose_mul_mul_same (TensorGate (K s) (1 : Operator 2))ᴴ

/-- Each Bob branch marginal is additive in the input operator. -/
theorem bobBranchMarginal_add
    (K : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (ω : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (s : Fin 4) (A B : Operator 2) :
    bobBranchMarginal K ω s (A + B) = bobBranchMarginal K ω s A + bobBranchMarginal K ω s B := by
  simp only [bobBranchMarginal, TensorGate, Matrix.add_kronecker, relabelGate,
    Matrix.reindex_apply, Matrix.submatrix_add, Pi.add_apply,
    Matrix.mul_add, Matrix.add_mul, partialTrace_add]

/-- Each Bob branch marginal commutes with complex scalar multiplication of the input operator. -/
theorem bobBranchMarginal_smul
    (K : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (ω : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (s : Fin 4) (c : ℂ) (A : Operator 2) :
    bobBranchMarginal K ω s (c • A) = c • bobBranchMarginal K ω s A := by
  simp only [bobBranchMarginal, TensorGate, Matrix.smul_kronecker, relabelGate,
    Matrix.reindex_apply, Matrix.submatrix_smul, Pi.smul_apply,
    Matrix.mul_smul, Matrix.smul_mul, partialTrace_smul]

/-- The Bob branch marginal equals the partial trace of the joint branch operator written in
Bob-first register order. -/
theorem bobBranchMarginal_bobFirst
    (K : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (ω : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (s : Fin 4) (ρ : Operator 2) :
    bobBranchMarginal K ω s ρ =
      PartialTrace (TensorGate (1 : Operator 2) (relabelGate finProdFinEquiv (K s)) *
        relabelGate bobFirstEquiv
          (relabelGate (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2)).symm (TensorGate ρ ω)) *
        (TensorGate (1 : Operator 2) (relabelGate finProdFinEquiv (K s)))ᴴ) := by
  unfold bobBranchMarginal
  rw [converse_relabel_mul, converse_relabel_mul, converse_relabel_adjoint,
    bobFirst_local_gate]

/-- For a complete four-outcome Alice-side Kraus family, the sum of Bob's branch marginals is
`trace ρ` times the resource's receiver marginal. -/
theorem bobBranchMarginal_no_signalling
    (K : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (ω : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hK : ∑ s : Fin 4, (TensorGate (K s) (1 : Operator 2))ᴴ *
      TensorGate (K s) (1 : Operator 2) = 1) (ρ : Operator 2) :
    ∑ s, bobBranchMarginal K ω s ρ =
      (Matrix.trace ρ) • PartialTrace (relabelGate (Equiv.prodComm (Fin 2) (Fin 2)) ω) := by
  let V := fun s : Fin 4 => TensorGate (1 : Operator 2) (relabelGate finProdFinEquiv (K s))
  let X := relabelGate bobFirstEquiv
    (relabelGate (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2)).symm (TensorGate ρ ω))
  have hc : ∑ s, (V s)ᴴ * V s = 1 := by
    have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ bobFirstEquiv) hK
    simp only [map_sum, map_one, Matrix.reindexAlgEquiv_apply] at h
    change (∑ s, relabelGate bobFirstEquiv
      ((TensorGate (K s) (1 : Operator 2))ᴴ * TensorGate (K s) (1 : Operator 2))) = 1 at h
    simp only [converse_relabel_mul, converse_relabel_adjoint, bobFirst_local_gate] at h
    exact h
  calc
    _ = ∑ s, PartialTrace (V s * X * (V s)ᴴ) := by simp only [bobBranchMarginal_bobFirst]; rfl
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
      change (∑ a : Fin 4, ρ ((finProdFinEquiv (m := 2) (n := 2)).symm a).1 ((finProdFinEquiv (m := 2) (n := 2)).symm a).1 *
        ω (((finProdFinEquiv (m := 2) (n := 2)).symm a).2, i) (((finProdFinEquiv (m := 2) (n := 2)).symm a).2, j)) =
        (Matrix.trace ρ) * ∑ b : Fin 2, ω (b, i) (b, j)
      rw [← (finProdFinEquiv (m := 2) (n := 2)).sum_comp]
      simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.trace,
        Matrix.diag_apply, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm

end Qatlib.Concepts.QuditTeleport.ResourceIff
