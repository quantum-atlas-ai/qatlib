/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCore
import Qatlib.Concepts.MbqcFlow.FlowDecision.IsingClusterResource

/-!
# Local Pauli rewrites across the graph entangler

The neighborhood `nbhd` and phase `depZVal` isolate the Z corrections on the neighbors of a flow
successor. The module proves the local X and Z actions, the controlled-Z rewrite, invariance of
the all-plus vector, and the outcome conjugation identity for XY-plane projectors used in
[DanosKashefi2006].

## Main statements

* `localZ_mul_cz_mul_localX`: For adjacent distinct vertices in a canonical graph, local Z times
  the entangler equals local X times the dependent Z matrix, the entangler, and local X.
* `localX_mulVec_allPlus`: Applying any local X operator leaves every amplitude of the all-plus
  vector unchanged.
* `mbqcPlaneBasis_conj_pauliZ`: The true-outcome XY-plane basis projector is the Pauli Z
  conjugate of the false-outcome projector.

## References

* [Danos and Kashefi, 2006][DanosKashefi2006]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open scoped Classical BigOperators ComplexOrder

namespace Qatlib.Papers.OneWayDanos05.MainResults

variable {n : ℕ}

/-- The finite set of vertices adjacent to `w` in the MBQC graph. -/
def nbhd (G : MbqcGraph n) (w : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun k => mbqcAdj G k w = true)

/-- Membership in `nbhd G w` is equivalent to Boolean adjacency to `w`. -/
@[simp] theorem mem_nbhd (G : MbqcGraph n) (w k : Fin n) :
    k ∈ nbhd G w ↔ mbqcAdj G k w = true := by
  simp [nbhd]

/-- In a canonical MBQC graph, a vertex is not in its own neighborhood. -/
theorem not_mem_nbhd_self (G : MbqcGraph n) (hcanon : mbqcCanonical G) (w : Fin n) :
    w ∉ nbhd G w := by
  rw [mem_nbhd]
  unfold mbqcAdj
  intro h
  rw [decide_eq_true_eq] at h
  rcases h with h | h <;> exact (lt_irrefl (w : ℕ)) (hcanon (w, w) h)

/-- The neighborhood consists of vertices joined to `w` by an edge in either orientation. -/
theorem nbhd_eq_filter (G : MbqcGraph n) (w : Fin n) :
    nbhd G w = Finset.univ.filter (fun k => (w, k) ∈ G.edges ∨ (k, w) ∈ G.edges) := by
  ext k
  simp [nbhd, mbqcAdj, or_comm]

/-- The neighbor phase is the product of the bit phases over the neighborhood. -/
theorem neighborPhase_eq_prod_nbhd (G : MbqcGraph n) (w : Fin n) (x : Reg n) :
    neighborPhase G.edges w x = ∏ k ∈ nbhd G w, bitPhase (x k) := by
  classical
  unfold neighborPhase
  rw [nbhd_eq_filter, ← Finset.prod_filter]

/-- A local Z operator multiplies each amplitude by minus one exactly when its selected bit is
true. -/
theorem localZ_mulVec (v : Fin n) (ψ : Reg n → ℂ) (x : Reg n) :
    (localZ v *ᵥ ψ) x = (if x v then (-1 : ℂ) else 1) * ψ x := by
  rw [localZ, Matrix.mulVec_diagonal]

/-- A local X operator evaluates the input amplitude at the register with its selected bit
flipped. -/
theorem localX_mulVec (v : Fin n) (ψ : Reg n → ℂ) (x : Reg n) :
    (localX v *ᵥ ψ) x = ψ (flipBit v x) := by
  have h : localX v = permMatrix (flipBit v) := rfl
  rw [h]
  exact applyGate_permMatrix (flipBit_involutive v) ψ x

/-- The controlled-Z graph entangler is the diagonal matrix of its graph phase function. -/
theorem czMatrix_eq_diagonal (G : MbqcGraph n) :
    czMatrix G.edges = Matrix.diagonal (czPhase G.edges) := by
  unfold czMatrix czPhase
  rfl

/-- The graph entangler multiplies each amplitude by its controlled-Z graph phase. -/
theorem czMatrix_mulVec (G : MbqcGraph n) (ψ : Reg n → ℂ) (x : Reg n) :
    (czMatrix G.edges *ᵥ ψ) x = czPhase G.edges x * ψ x := by
  rw [czMatrix_eq_diagonal, Matrix.mulVec_diagonal]

/-- The product of Z phases on the neighbors of `w` other than `v`. -/
def depZVal (G : MbqcGraph n) (w v : Fin n) (x : Reg n) : ℂ :=
  ∏ k ∈ (nbhd G w).erase v, (if x k then (-1 : ℂ) else 1)

/-- The diagonal correction matrix given by `depZVal`. -/
noncomputable def depZMatrix (G : MbqcGraph n) (w v : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (depZVal G w v)

/-- The dependent Z phase multiplied by itself is one. -/
theorem depZVal_sq (G : MbqcGraph n) (w v : Fin n) (x : Reg n) :
    depZVal G w v x * depZVal G w v x = 1 := by
  unfold depZVal
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro k _
  split_ifs <;> norm_num

/-- For a canonical graph, flipping the bit at `w` does not change its dependent Z phase. -/
theorem depZVal_flip (G : MbqcGraph n) (hcanon : mbqcCanonical G) (w v : Fin n) (x : Reg n) :
    depZVal G w v (flipBit w x) = depZVal G w v x := by
  unfold depZVal
  apply Finset.prod_congr rfl
  intro k hk
  have hk' : k ∈ nbhd G w := Finset.mem_of_mem_erase hk
  have hkw : k ≠ w := fun h => not_mem_nbhd_self G hcanon w (h ▸ hk')
  simp [flipBit, hkw]

/-- If `v` is a neighbor of `w`, its local Z phase factors out of the full neighbor phase,
leaving `depZVal`. -/
theorem neighborPhase_eq_depZ_mul (G : MbqcGraph n) (w v : Fin n) (hv : v ∈ nbhd G w)
    (x : Reg n) :
    neighborPhase G.edges w x = depZVal G w v x * (if x v then (-1 : ℂ) else 1) := by
  rw [neighborPhase_eq_prod_nbhd]
  unfold depZVal
  rw [← Finset.prod_erase_mul (nbhd G w) (fun k => bitPhase (x k)) hv]
  simp only [bitPhase]

/-- For adjacent distinct vertices in a canonical graph, local Z times the entangler equals
local X times the dependent Z matrix, the entangler, and local X [DanosKashefi2006]. -/
theorem localZ_mul_cz_mul_localX (G : MbqcGraph n) (hcanon : mbqcCanonical G)
    {v w : Fin n} (hvw : mbqcAdj G v w = true) (_hne : v ≠ w) :
    localZ v * czMatrix G.edges
      = localX w * depZMatrix G w v * czMatrix G.edges * localX w := by
  rw [Matrix.ext_iff_mulVec]
  intro ψ
  funext x
  have hvmem : v ∈ nbhd G w := by rw [mem_nbhd]; exact hvw

  have hL : ((localZ v * czMatrix G.edges) *ᵥ ψ) x
      = (if x v then (-1 : ℂ) else 1) * (czPhase G.edges x * ψ x) := by
    rw [← Matrix.mulVec_mulVec, localZ_mulVec, czMatrix_mulVec]

  have hR : ((localX w * depZMatrix G w v * czMatrix G.edges * localX w) *ᵥ ψ) x
      = depZVal G w v (flipBit w x) * (czPhase G.edges (flipBit w x)
          * ψ (flipBit w (flipBit w x))) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [localX_mulVec, depZMatrix, Matrix.mulVec_diagonal, czMatrix_mulVec, localX_mulVec]
  rw [hL, hR, depZVal_flip G hcanon w v x, czPhase_flip G.edges hcanon w x,
    neighborPhase_eq_depZ_mul G w v hvmem x, flipBit_involutive w]

  have hsq := depZVal_sq G w v x
  linear_combination (-(czPhase G.edges x * ψ x * (if x v then (-1 : ℂ) else 1))) * hsq

/-- The constant register amplitude of the normalized all-plus product vector on `n` qubits. -/
def allPlus (n : ℕ) : Reg n → ℂ := fun _ => ((Real.sqrt 2 : ℂ))⁻¹ ^ n

/-- Applying any local X operator leaves every amplitude of the all-plus vector unchanged
[DanosKashefi2006]. -/
theorem localX_mulVec_allPlus (v : Fin n) (x : Reg n) :
    (localX v *ᵥ allPlus n) x = allPlus n x := by
  rw [localX_mulVec]
  rfl

/-- The true-outcome XY-plane basis projector is the Pauli Z conjugate of the false-outcome
projector [DanosKashefi2006]. -/
theorem mbqcPlaneBasis_conj_pauliZ (a : ℝ) :
    MbqcPlaneBasis MbqcPlane.XY a true
      = pauliZ * MbqcPlaneBasis MbqcPlane.XY a false * pauliZ := by
  unfold MbqcPlaneBasis mbqcPlaneAxisA mbqcPlaneAxisB
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliZ, pauliX, pauliY, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Fin.isValue] <;>
    norm_num <;> ring

end Qatlib.Papers.OneWayDanos05.MainResults
