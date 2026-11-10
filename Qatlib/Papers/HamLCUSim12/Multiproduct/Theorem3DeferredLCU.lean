/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.DeferredLCUContracts
import Qatlib.Papers.HamLCUSim12.Multiproduct.NearbyLCUDiagnostics
import Qatlib.Foundations.PureStateMath.Qubit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.HamLCUSim12.LCUDeferred

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

open Matrix

def deferredCounterexampleCoefficients (q : Fin 2) : ℝ := if q = 0 then 1 else -1

def deferredCounterexampleGates (q : Fin 2) : Matrix Unit Unit ℂ :=
  if q = 0 then 1 else -1

private theorem rot_unit_diagonal (k : ℕ) (i : Fin k) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    rotGate (I := Unit) k i V =
      Matrix.diagonal (fun p => V (if p.1 i then 1 else 0) (if p.1 i then 1 else 0)) := by
  ext ⟨z, n⟩ ⟨w, n'⟩
  cases n
  cases n'
  by_cases h : z = w <;> simp [rotGate, h]

private theorem lift_unit_one (k : ℕ) :
    liftSys k (1 : Matrix Unit Unit ℂ) = 1 := by
  ext ⟨z, n⟩ ⟨w, n'⟩
  cases n
  cases n'
  simp [liftSys, Matrix.one_apply]

private theorem ctrl_unit_one (k : ℕ) (i : Fin k) :
    ctrlGate (I := Unit) k i 1 1 = 1 := by
  ext ⟨z, n⟩ ⟨w, n'⟩
  cases n
  cases n'
  by_cases h : z = w <;> simp [ctrlGate, Matrix.one_apply, h]

private theorem lift_unit_neg_one (k : ℕ) :
    -liftSys k (-1 : Matrix Unit Unit ℂ) = 1 := by
  ext ⟨z, n⟩ ⟨w, n'⟩
  cases n
  cases n'
  by_cases h : z = w <;> simp [liftSys, Matrix.one_apply, h]

private theorem counterexample_protocol :
    cwProtocol 1 deferredCounterexampleCoefficients deferredCounterexampleGates =
      lcuLevelGate 2 1 (vKappa 1) (1 : Matrix ((Fin 2 → Bool) × Unit) _ ℂ) 1 := by
  have hpos : (Finset.univ.filter fun q : Fin 2 => 0 < deferredCounterexampleCoefficients q) = {0} := by
    ext q
    fin_cases q <;> norm_num [deferredCounterexampleCoefficients]
  have hneg : (Finset.univ.filter fun q : Fin 2 => deferredCounterexampleCoefficients q < 0) = {1} := by
    ext q
    fin_cases q <;> norm_num [deferredCounterexampleCoefficients]
  unfold cwProtocol
  simp only [hpos, hneg]
  norm_num [cwChainList, chainCircuit, chainFold, deferredCounterexampleCoefficients,
    deferredCounterexampleGates, Fin.sum_univ_succ, lift_unit_one, lift_unit_neg_one]

theorem deferredCounterexample_output :
    cwOutput 1 deferredCounterexampleCoefficients deferredCounterexampleGates
      (fun _ => 1) (cwZero 1, ()) = (1 / 2 : ℂ) := by
  unfold cwOutput ApplyGate
  rw [counterexample_protocol]
  unfold lcuLevelGate
  rw [ctrl_unit_one, Matrix.one_mul, rot_unit_diagonal, rot_unit_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.mulVec_diagonal]
  simp [cwZero, TensorState, Ket, Matrix.conjTranspose_apply, vKappa]
  have hs : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  norm_num only [Nat.cast_add, Nat.cast_one]
  simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat] using
    congrArg Complex.ofReal hs

theorem not_theorem3LCUFiber : ¬ Theorem3LCUFiber := by
  intro h
  have hU : ∀ q, deferredCounterexampleGates q ∈ Matrix.unitaryGroup Unit ℂ := by
    intro q
    fin_cases q <;> simp [deferredCounterexampleGates, Matrix.mem_unitaryGroup_iff]
  have hc : ∀ q, deferredCounterexampleCoefficients q ≠ 0 := by
    intro q
    fin_cases q <;> norm_num [deferredCounterexampleCoefficients]
  have he := h 1 Unit (by norm_num) deferredCounterexampleGates hU
    deferredCounterexampleCoefficients hc ⟨0, by norm_num [deferredCounterexampleCoefficients]⟩
    ⟨1, by norm_num [deferredCounterexampleCoefficients]⟩ (fun _ => 1) ()
  rw [deferredCounterexample_output] at he
  norm_num [deferredCounterexampleCoefficients, deferredCounterexampleGates,
    Fin.sum_univ_succ, Matrix.mulVec, dotProduct] at he

end Qatlib.Papers.HamLCUSim12.Multiproduct
