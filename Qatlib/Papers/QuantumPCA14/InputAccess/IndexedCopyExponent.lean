/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.CopyExponentialPrecision
import Qatlib.Papers.QuantumPCA14.InputAccess.IndexedColumnLoad
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumPCA14.InputAccess

open Matrix
open scoped BigOperators ComplexOrder

open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

theorem marginal_eq_paperMatrix_of_real {m d : ℕ} (O : ColumnOracle m d)
    (hR : RealColumns O) : marginal O = paperMatrix O := by
  rw [marginal_eq_paperMatrix_transpose]
  exact (paperMatrix_real_eq O hR).symm

theorem indexedLoad_copyExponentiation {m d : ℕ} (O : ColumnOracle m d)
    (T k s : ℕ) (t : ℝ) (ht : |t| ≤ (T : ℝ))
    (Y : Matrix (Fin m × Fin s) (Fin m × Fin s) ℂ) (Ypos : Y.PosSemidef) :
    let n := copyPrecisionBudget T k
    Matrix.traceNorm
        (freshCopyReferenceRun (marginal O) (List.replicate n (t / (n : ℝ))) s Y -
          TensorGate (HamiltonianEvolution (marginal O) t) (1 : Operator s) * Y *
            (TensorGate (HamiltonianEvolution (marginal O) t) (1 : Operator s))ᴴ) ≤
        ((2 : ℝ)⁻¹) ^ k * Matrix.traceNorm Y ∧
      freshCopyResourceCounts m (List.replicate n (t / (n : ℝ))) = (n, n, n, 0) :=
  copy_precision_same_protocol_and_four_resource_counts m s T k (marginal O) t Y
    (marginal_isDensity O) Ypos ht

theorem realColumns_copyExponentiates_paperMatrix {m d : ℕ} (O : ColumnOracle m d)
    (hR : RealColumns O) (T k s : ℕ) (t : ℝ) (ht : |t| ≤ (T : ℝ))
    (Y : Matrix (Fin m × Fin s) (Fin m × Fin s) ℂ) (Ypos : Y.PosSemidef) :
    let n := copyPrecisionBudget T k
    Matrix.traceNorm
        (freshCopyReferenceRun (paperMatrix O) (List.replicate n (t / (n : ℝ))) s Y -
          TensorGate (HamiltonianEvolution (paperMatrix O) t) (1 : Operator s) * Y *
            (TensorGate (HamiltonianEvolution (paperMatrix O) t) (1 : Operator s))ᴴ) ≤
        ((2 : ℝ)⁻¹) ^ k * Matrix.traceNorm Y ∧
      freshCopyResourceCounts m (List.replicate n (t / (n : ℝ))) = (n, n, n, 0) := by
  rw [← marginal_eq_paperMatrix_of_real O hR]
  exact indexedLoad_copyExponentiation O T k s t ht Y Ypos

theorem conjugateAccess_copyExponentiates_paperMatrix {m d : ℕ} (O : ColumnOracle m d)
    (T k s : ℕ) (t : ℝ) (ht : |t| ≤ (T : ℝ))
    (Y : Matrix (Fin m × Fin s) (Fin m × Fin s) ℂ) (Ypos : Y.PosSemidef) :
    let n := copyPrecisionBudget T k
    Matrix.traceNorm
        (freshCopyReferenceRun (paperMatrix O) (List.replicate n (t / (n : ℝ))) s Y -
          TensorGate (HamiltonianEvolution (paperMatrix O) t) (1 : Operator s) * Y *
            (TensorGate (HamiltonianEvolution (paperMatrix O) t) (1 : Operator s))ᴴ) ≤
        ((2 : ℝ)⁻¹) ^ k * Matrix.traceNorm Y ∧
      freshCopyResourceCounts m (List.replicate n (t / (n : ℝ))) = (n, n, n, 0) := by
  rw [← conjugateAccess_marginal O]
  exact indexedLoad_copyExponentiation (conjugateOracle O) T k s t ht Y Ypos

end Qatlib.Papers.QuantumPCA14.InputAccess
