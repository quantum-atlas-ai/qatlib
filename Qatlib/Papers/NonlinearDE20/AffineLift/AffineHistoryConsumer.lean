/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.HistorySystem.FiniteHistoryEuler
import Qatlib.Papers.NonlinearDE20.AffineLift.AffinePostselect
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical
open Matrix

namespace Qatlib.Papers.NonlinearDE20.AffineLift.Model
open Qatlib.Papers.NonlinearDE20.HistorySystem.History

def affineStep {I : Type} [Fintype I] (A : Matrix I I ℂ) (b x : I→ℂ) (dt : ℂ) : I→ℂ :=
  x+dt • (A*ᵥ x+b)

def affineProductStep {I : Type} [DecidableEq I] (n : ℕ) (A : Matrix I I ℂ) (b : I→ℂ) (dt : ℂ) :
    Matrix (Fin n→Option I) (Fin n→Option I) ℂ :=
  tensorMatrix n (fun _=>1+dt • affineMatrix A b)

theorem affineProductStep_action {I : Type} [Fintype I] [DecidableEq I]
    (n : ℕ) (A : Matrix I I ℂ) (b x : I→ℂ) (dt : ℂ) :
    affineProductStep n A b dt*ᵥ tensorPower n (homogenize x)=
      tensorPower n (homogenize (affineStep A b x dt)) := by
  funext u
  rw [affineProductStep,tensorMatrix_action]
  simp_rw [affine_euler]
  rfl

def affineSequence {I : Type} [Fintype I] (A : Matrix I I ℂ) (b x0 : I→ℂ) (dt : ℂ) : ℕ→I→ℂ
  | 0=>x0
  | k+1=>affineStep A b (affineSequence A b x0 dt k) dt

def homogeneousRhs {I : Type} (n : ℕ) (x0 : I→ℂ) (k : ℕ) : (Fin n→Option I)→ℂ :=
  if k=0 then tensorPower n (homogenize x0) else 0

theorem homogeneous_sequence_exact {I : Type} [Fintype I] [DecidableEq I]
    (n : ℕ) (A : Matrix I I ℂ) (b x0 : I→ℂ) (dt : ℂ) (k : ℕ) :
    eulerSequence (affineProductStep n A b dt) (homogeneousRhs n x0) k=
      tensorPower n (homogenize (affineSequence A b x0 dt k)) := by
  induction k with
  | zero => simp [eulerSequence,homogeneousRhs,affineSequence]
  | succ k ih =>
    rw [eulerSequence,ih,affineProductStep_action]
    simp [homogeneousRhs,affineSequence]

theorem affine_history_slice {I : Type} [Fintype I] [DecidableEq I]
    (T n : ℕ) (A : Matrix I I ℂ) (b x0 : I→ℂ) (dt : ℂ) (k : Fin (T+1)) (u : Fin n→Option I) :
    (historyInverse (T+1) (affineProductStep n A b dt)*ᵥ
      (fun p : Fin (T+1)×(Fin n→Option I)=>homogeneousRhs n x0 p.1.val p.2)) (k,u)=
      tensorPower n (homogenize (affineSequence A b x0 dt k.val)) u := by
  rw [← eulerHistory_eq_inverse T (affineProductStep n A b dt) (homogeneousRhs n x0)]
  exact congrFun (homogeneous_sequence_exact n A b x0 dt k.val) u

theorem affine_history_postselect {I : Type} [Fintype I] [DecidableEq I]
    (T n : ℕ) (A : Matrix I I ℂ) (b x0 : I→ℂ) (dt : ℂ) (k : Fin (T+1)) :
    branchSelector n*ᵥ (fun u=>(historyInverse (T+1) (affineProductStep n A b dt)*ᵥ
      (fun p : Fin (T+1)×(Fin n→Option I)=>homogeneousRhs n x0 p.1.val p.2)) (k,u))=
      tensorPower n (affineSequence A b x0 dt k.val) := by
  funext v
  rw [branchSelector_action,affine_history_slice]
  rfl

theorem affine_history_conditional_density {I : Type} [Fintype I] [DecidableEq I]
    (T n : ℕ) (A : Matrix I I ℂ) (b x0 : I→ℂ) (dt : ℂ) (k : Fin (T+1)) :
    normalizedOuter (branchSelector n*ᵥ (fun u=>(historyInverse (T+1) (affineProductStep n A b dt)*ᵥ
      (fun p : Fin (T+1)×(Fin n→Option I)=>homogeneousRhs n x0 p.1.val p.2)) (k,u)))=
      normalizedOuter (tensorPower n (affineSequence A b x0 dt k.val)) := by
  rw [affine_history_postselect]

end Qatlib.Papers.NonlinearDE20.AffineLift.Model
