/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.DepolarizingLaw.SingletConventionBridgeStat

/-!
# The singlet convention bridge

`singletConventionBridge` identifies singlet-prepared teleportation branches with signed
standard branches at complemented outcomes. The associated corrections recover one quarter of
each input operator on every branch. The singlet convention follows the qubit protocol of
[BennettEtAl1993Teleportation].

## Main statements

* `singlet_branch_bridge`: The singlet branch at `o` is `singletSign o` times the standard
  branch at `singletSwap o`.
* `singletConventionBridge`: Singlet preparation satisfies the signed outcome bridge and each
  corrected branch recovers one quarter of the input. See [Bennett et al., 1993, Eqs.
  (1)–(6)][BennettEtAl1993Teleportation].

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.DepolarizingLaw
open Matrix

/-- An entry of a singlet branch Kraus operator is the signed sum of the two singlet amplitudes
selected by the input basis index. -/
private theorem singlet_branch_entry (o : Bool × Bool) (c i : Fin 2) :
    singletBranchKraus o c i = (Real.sqrt 2 : ℂ)⁻¹ *
      ((if false = boolEquivFin2.symm i then singletResource (o.2,boolEquivFin2.symm c) else 0) +
       (if o.1 then (-1 : ℂ) else 1) *
        (if true = boolEquivFin2.symm i then singletResource (!o.2,boolEquivFin2.symm c) else 0)) := by
  let ψ : QState ((Bool × Bool) × Bool) := fun x =>
    if x.1.1 = boolEquivFin2.symm i then singletResource (x.1.2,x.2) else 0
  have hc : (fun r => singletPreparedFrame r i) = relabelState teleportRegisterEquiv ψ := rfl
  have hd : teleportDecodeGate = relabelGate teleportRegisterEquiv
      (teleportHaB * teleportCnotAbB) := by
    unfold teleportDecodeGate teleportHaGate teleportCnotAbGate
    rw [teleportRelabelGate_mul]
  change (teleportDecodeGate * singletPreparedFrame)
    (teleportRegisterEquiv ((o.1,o.2),boolEquivFin2.symm c)) i = _
  rw [matrix_mul_column, hc, hd, applyGate_relabelGate, applyGate_mul,
    teleportHaB_apply, teleportCnotAbB_apply]
  cases o with
  | mk a b => cases a <;> cases b <;> simp [relabelState, ψ]

/-- The singlet branch at `o` is `singletSign o` times the standard branch at `singletSwap o`. -/
private theorem singlet_branch_bridge (o : Bool × Bool) :
    singletBranchKraus o = singletSign o • teleportBranchKraus (singletSwap o) := by
  ext c i
  rw [singlet_branch_entry]
  simp only [Matrix.smul_apply, smul_eq_mul, teleportBranchKraus, Matrix.of_apply]
  rw [teleportDecode_mul_prepared_apply, Equiv.symm_apply_apply]
  rcases o with ⟨a,b⟩
  cases a <;> cases b <;> fin_cases c <;> fin_cases i <;>
    simp [singletResource, singletSign, singletSwap, boolEquivFin2, sqrt2_inv_sq]

/-- Singlet preparation satisfies the signed outcome bridge and each corrected branch recovers
one quarter of the input. See [Bennett et al., 1993, Eqs.
(1)–(6)][BennettEtAl1993Teleportation]. -/
theorem singletConventionBridge : SingletConventionBridge := by
  refine ⟨singlet_branch_bridge, ?_⟩
  intro ρ o
  have hc : singletCorrection o * singletBranchKraus o = (1/2 : ℂ) • (1 : Operator 2) := by
    rw [singletCorrection, singlet_branch_bridge, smul_mul_assoc, mul_smul_comm,
      smul_smul, (bell_pauli_corrections (singletSwap o)).2]
    rcases o with ⟨a,b⟩
    cases b <;> simp [singletSign]
  rw [hc]
  simp [Matrix.conjTranspose_smul, smul_smul]
  norm_num

end Qatlib.Concepts.QuditTeleport.DepolarizingLaw
