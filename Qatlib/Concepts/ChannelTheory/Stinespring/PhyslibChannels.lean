/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel
import QuantumInfo.Channels.CPTP
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ChannelTheory.Stinespring

open scoped ComplexOrder

variable {D E F : ℕ}

theorem kron_id_apply
    (T : Operator D →ₗ[ℂ] Operator E) (r : ℕ)
    (A : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (i j : Fin E) (a b : Fin r) :
    (MatrixMap.kron T (LinearMap.id : MatrixMap (Fin r) (Fin r) ℂ)) A
        (i, a) (j, b) =
      T (fun x y => A (x, a) (y, b)) i j := by
  classical
  calc
    _ = ∑ x : Fin D, ∑ y : Fin D,
        T (Matrix.single x y 1) i j * A (x, a) (y, b) := by
      rw [MatrixMap.kron_def]
      simp [Matrix.single, ite_and, mul_ite, ite_mul]
    _ = _ := by
      have h := congrArg
        (fun S : MatrixMap (Fin D) (Fin E) ℂ =>
          S (fun x y => A (x, a) (y, b)) i j)
        (MatrixMap.choi_map_inv T)
      simpa [MatrixMap.of_choi_matrix, MatrixMap.choi_matrix, mul_comm] using h

theorem kron_id_eq_swapped_amplification
    (T : Operator D →ₗ[ℂ] Operator E) (r : ℕ)
    (A : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    (MatrixMap.kron T (LinearMap.id : MatrixMap (Fin r) (Fin r) ℂ)) A =
      (ChannelAmplification T r (A.submatrix Prod.swap Prod.swap)).submatrix
        Prod.swap Prod.swap := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [kron_id_apply]
  rfl

theorem amplification_eq_swapped_kron_id
    (T : Operator D →ₗ[ℂ] Operator E) (r : ℕ)
    (A : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ) :
    ChannelAmplification T r A =
      ((MatrixMap.kron T (LinearMap.id : MatrixMap (Fin r) (Fin r) ℂ))
        (A.submatrix Prod.swap Prod.swap)).submatrix Prod.swap Prod.swap := by
  ext ⟨a, i⟩ ⟨b, j⟩
  change T (fun x y => A (a, x) (b, y)) i j =
    (MatrixMap.kron T (LinearMap.id : MatrixMap (Fin r) (Fin r) ℂ))
      (A.submatrix Prod.swap Prod.swap) (i, a) (j, b)
  rw [kron_id_apply]
  rfl

theorem completelyPositive_iff_physlib
    (T : Operator D →ₗ[ℂ] Operator E) :
    CompletelyPositive T ↔ MatrixMap.IsCompletelyPositive T := by
  constructor
  · intro h r A hA
    rw [kron_id_eq_swapped_amplification]
    exact (h r _ (hA.submatrix Prod.swap)).submatrix Prod.swap
  · intro h r A hA
    rw [amplification_eq_swapped_kron_id]
    exact (h r (hA.submatrix Prod.swap)).submatrix Prod.swap

theorem tracePreserving_iff_physlib
    (T : Operator D →ₗ[ℂ] Operator E) :
    TracePreserving T ↔ MatrixMap.IsTracePreserving T := Iff.rfl

noncomputable def toPhyslib (T : QuantumChannel D E) : CPTPMap (Fin D) (Fin E) where
  toLinearMap := T.map
  cp := (completelyPositive_iff_physlib T.map).mp T.completelyPositive
  TP := (tracePreserving_iff_physlib T.map).mp T.tracePreserving

noncomputable def ofPhyslib (T : CPTPMap (Fin D) (Fin E)) : QuantumChannel D E where
  map := T.map
  completelyPositive := (completelyPositive_iff_physlib T.map).mpr T.cp
  tracePreserving := (tracePreserving_iff_physlib T.map).mpr T.TP

@[simp] theorem toPhyslib_map (T : QuantumChannel D E) :
    (toPhyslib T).map = T.map := rfl

@[simp] theorem ofPhyslib_map (T : CPTPMap (Fin D) (Fin E)) :
    (ofPhyslib T).map = T.map := rfl

@[simp] theorem ofPhyslib_toPhyslib (T : QuantumChannel D E) :
    ofPhyslib (toPhyslib T) = T := by
  cases T
  rfl

@[simp] theorem toPhyslib_ofPhyslib (T : CPTPMap (Fin D) (Fin E)) :
    toPhyslib (ofPhyslib T) = T := by
  apply CPTPMap.ext
  rfl

noncomputable def channelEquivPhyslib (D E : ℕ) :
    QuantumChannel D E ≃ CPTPMap (Fin D) (Fin E) where
  toFun := toPhyslib
  invFun := ofPhyslib
  left_inv := ofPhyslib_toPhyslib
  right_inv := toPhyslib_ofPhyslib

@[simp] theorem toPhyslib_id (D : ℕ) :
    toPhyslib (QuantumChannel.id D) = CPTPMap.id (dIn := Fin D) := by
  apply CPTPMap.ext
  rfl

@[simp] theorem toPhyslib_comp (S : QuantumChannel E F) (T : QuantumChannel D E) :
    toPhyslib (S.comp T) = CPTPMap.compose (toPhyslib S) (toPhyslib T) := by
  apply CPTPMap.ext
  rfl

@[simp] theorem ofPhyslib_id (D : ℕ) :
    ofPhyslib (CPTPMap.id (dIn := Fin D)) = QuantumChannel.id D := by
  rfl

@[simp] theorem ofPhyslib_comp
    (S : CPTPMap (Fin E) (Fin F)) (T : CPTPMap (Fin D) (Fin E)) :
    ofPhyslib (CPTPMap.compose S T) = (ofPhyslib S).comp (ofPhyslib T) := by
  rfl

end Qatlib.Concepts.ChannelTheory.Stinespring
