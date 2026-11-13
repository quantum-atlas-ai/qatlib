/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliShadowStatistics

/-!
# Tensor product states and Pauli readout

The operator `newWord` expresses a tensor Pauli word after relabeling the qubit register.
Relabeled tensor products of one-qubit density operators remain physical, and their tensor Pauli
measurement expectation equals the real trace pairing with `newWord`. See
[CrostaSaubanereHuber2026].

## Main statements

* `newProduct_physical`: proves physicality of the relabeled tensor product.
* `newProduct_actual_readout`: identifies the Pauli readout expectation with its operator trace.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.ShadowModels.ShadowChannel
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.Rounding.TensorReadout
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct

/-- The tensor product of the specified Pauli or identity factors, relabeled by `bitVecEquiv` as
an operator on a register of dimension `2^n`. -/
noncomputable def newWord {n : ℕ} (w : Fin n → Option (Fin 3)) : Operator (2^n) :=
  relabelGate (bitVecEquiv n) (qubitTensor (fun i => tensorPauliWordFactor (w i)))

/-- The relabeled tensor Pauli word `newWord` equals `tensorPauliWord`. -/
theorem newWord_measured {n : ℕ} (w : Fin n → Option (Fin 3)) :
    newWord w=tensorPauliWord n w := rfl

/-- Relabeling a tensor product of one-qubit density operators yields a density operator on the
full register. -/
theorem newProduct_physical {n : ℕ} (A : Fin n → Operator 2) (hA : ∀ i,IsDensityOperator (A i)) :
    IsDensityOperator (relabelGate (bitVecEquiv n) (qubitTensor A)) := by
  have h := qubitTensor_density A hA
  constructor
  · exact (Matrix.posSemidef_submatrix_equiv _).mpr h.1
  · change (∑ x,qubitTensor A ((bitVecEquiv n).symm x) ((bitVecEquiv n).symm x))=1
    exact (Equiv.sum_comp (bitVecEquiv n).symm (fun x => qubitTensor A x x)).trans h.2

/-- The expectation of a tensor Pauli word under the measurement law of the relabeled product
density equals the real part of its trace pairing with `newWord`. -/
theorem newProduct_actual_readout {n : ℕ} (A : Fin n → Operator 2)
    (hA : ∀ i,IsDensityOperator (A i)) (w : Fin n → Option (Fin 3)) :
    (tensorPauliLaw n (relabelGate (bitVecEquiv n) (qubitTensor A)) (newProduct_physical A hA)).expect
      (tensorPauliValue w)=
      (newWord w*relabelGate (bitVecEquiv n) (qubitTensor A)).trace.re := by
  rw [tensorPauliValue_mean,newWord_measured]
end Qatlib.Papers.RydbergMaxCut26.Rounding.TensorReadout
