/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.HistorySystem.FiniteHistoryEuler
import Qatlib.Papers.NonlinearDE20.AffineLift.AffinePostselect

/-!
# Exact affine histories in homogeneous coordinates

Encodes affine Euler steps in homogeneous coordinates and takes tensor powers of their step
matrices. The resulting linear history system has exact tensor-product time slices; selecting
the original-coordinate branch recovers tensor powers of the affine Euler iterates and their
normalized outer products. See [LloydEtAl2020].

## Main statements

* `homogeneous_sequence_exact`: the homogeneous recurrence is the tensor power of the affine
  recurrence.
* `affine_history_slice`: the history inverse has the expected homogeneous time slices.
* `affine_history_postselect`: branch selection recovers the original affine iterates.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical
open Matrix

namespace Qatlib.Papers.NonlinearDE20.AffineLift.Model
open Qatlib.Papers.NonlinearDE20.HistorySystem.History

/-- The affine forward-Euler update `x + dt • (A *ᵥ x + b)`. -/
def affineStep {I : Type} [Fintype I] (A : Matrix I I ℂ) (b x : I→ℂ) (dt : ℂ) : I→ℂ :=
  x+dt • (A*ᵥ x+b)

/-- The tensor product of `n` copies of the homogeneous affine Euler step matrix. -/
def affineProductStep {I : Type} [DecidableEq I] (n : ℕ) (A : Matrix I I ℂ) (b : I→ℂ) (dt : ℂ) :
    Matrix (Fin n→Option I) (Fin n→Option I) ℂ :=
  tensorMatrix n (fun _=>1+dt • affineMatrix A b)

/-- The product step maps the tensor power of a homogenized vector to the tensor power of its
homogenized affine Euler update. -/
theorem affineProductStep_action {I : Type} [Fintype I] [DecidableEq I]
    (n : ℕ) (A : Matrix I I ℂ) (b x : I→ℂ) (dt : ℂ) :
    affineProductStep n A b dt*ᵥ tensorPower n (homogenize x)=
      tensorPower n (homogenize (affineStep A b x dt)) := by
  funext u
  rw [affineProductStep,tensorMatrix_action]
  simp_rw [affine_euler]
  rfl

/-- The sequence starting at `x0` and repeatedly applying the affine Euler update with fixed
`A`, `b`, and `dt`. -/
def affineSequence {I : Type} [Fintype I] (A : Matrix I I ℂ) (b x0 : I→ℂ) (dt : ℂ) : ℕ→I→ℂ
  | 0=>x0
  | k+1=>affineStep A b (affineSequence A b x0 dt k) dt

/-- The history right-hand side equal to the tensor power of `homogenize x0` at time zero and
zero at later times. -/
def homogeneousRhs {I : Type} (n : ℕ) (x0 : I→ℂ) (k : ℕ) : (Fin n→Option I)→ℂ :=
  if k=0 then tensorPower n (homogenize x0) else 0

/-- The homogeneous tensor recurrence at each time equals the tensor power of the homogenized
affine Euler iterate. -/
theorem homogeneous_sequence_exact {I : Type} [Fintype I] [DecidableEq I]
    (n : ℕ) (A : Matrix I I ℂ) (b x0 : I→ℂ) (dt : ℂ) (k : ℕ) :
    eulerSequence (affineProductStep n A b dt) (homogeneousRhs n x0) k=
      tensorPower n (homogenize (affineSequence A b x0 dt k)) := by
  induction k with
  | zero => simp [eulerSequence,homogeneousRhs,affineSequence]
  | succ k ih =>
    rw [eulerSequence,ih,affineProductStep_action]
    simp [homogeneousRhs,affineSequence]

/-- Every slice of the linear history inverse applied to the initial-only right-hand side equals
the tensor power of the corresponding homogenized affine Euler iterate. See [LloydEtAl2020]. -/
theorem affine_history_slice {I : Type} [Fintype I] [DecidableEq I]
    (T n : ℕ) (A : Matrix I I ℂ) (b x0 : I→ℂ) (dt : ℂ) (k : Fin (T+1)) (u : Fin n→Option I) :
    (historyInverse (T+1) (affineProductStep n A b dt)*ᵥ
      (fun p : Fin (T+1)×(Fin n→Option I)=>homogeneousRhs n x0 p.1.val p.2)) (k,u)=
      tensorPower n (homogenize (affineSequence A b x0 dt k.val)) u := by
  rw [← eulerHistory_eq_inverse T (affineProductStep n A b dt) (homogeneousRhs n x0)]
  exact congrFun (homogeneous_sequence_exact n A b x0 dt k.val) u

/-- Selecting the original-coordinate branch of a homogeneous affine history slice gives exactly
the tensor power of the affine Euler iterate. See [LloydEtAl2020]. -/
theorem affine_history_postselect {I : Type} [Fintype I] [DecidableEq I]
    (T n : ℕ) (A : Matrix I I ℂ) (b x0 : I→ℂ) (dt : ℂ) (k : Fin (T+1)) :
    branchSelector n*ᵥ (fun u=>(historyInverse (T+1) (affineProductStep n A b dt)*ᵥ
      (fun p : Fin (T+1)×(Fin n→Option I)=>homogeneousRhs n x0 p.1.val p.2)) (k,u))=
      tensorPower n (affineSequence A b x0 dt k.val) := by
  funext v
  rw [branchSelector_action,affine_history_slice]
  rfl

/-- The normalized outer product of a branch-selected affine history slice equals that of the
tensor power of the affine Euler iterate. See [LloydEtAl2020]. -/
theorem affine_history_conditional_density {I : Type} [Fintype I] [DecidableEq I]
    (T n : ℕ) (A : Matrix I I ℂ) (b x0 : I→ℂ) (dt : ℂ) (k : Fin (T+1)) :
    normalizedOuter (branchSelector n*ᵥ (fun u=>(historyInverse (T+1) (affineProductStep n A b dt)*ᵥ
      (fun p : Fin (T+1)×(Fin n→Option I)=>homogeneousRhs n x0 p.1.val p.2)) (k,u)))=
      normalizedOuter (tensorPower n (affineSequence A b x0 dt k.val)) := by
  rw [affine_history_postselect]

end Qatlib.Papers.NonlinearDE20.AffineLift.Model
