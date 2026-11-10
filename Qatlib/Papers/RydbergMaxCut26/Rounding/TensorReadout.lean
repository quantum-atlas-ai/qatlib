/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliShadowStatistics
set_option warningAsError false
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

noncomputable def newWord {n : ℕ} (w : Fin n → Option (Fin 3)) : Operator (2^n) :=
  relabelGate (bitVecEquiv n) (qubitTensor (fun i => tensorPauliWordFactor (w i)))

theorem newWord_measured {n : ℕ} (w : Fin n → Option (Fin 3)) :
    newWord w=tensorPauliWord n w := rfl

theorem newProduct_physical {n : ℕ} (A : Fin n → Operator 2) (hA : ∀ i,IsDensityOperator (A i)) :
    IsDensityOperator (relabelGate (bitVecEquiv n) (qubitTensor A)) := by
  have h := qubitTensor_density A hA
  constructor
  · exact (Matrix.posSemidef_submatrix_equiv _).mpr h.1
  · change (∑ x,qubitTensor A ((bitVecEquiv n).symm x) ((bitVecEquiv n).symm x))=1
    exact (Equiv.sum_comp (bitVecEquiv n).symm (fun x => qubitTensor A x x)).trans h.2

theorem newProduct_actual_readout {n : ℕ} (A : Fin n → Operator 2)
    (hA : ∀ i,IsDensityOperator (A i)) (w : Fin n → Option (Fin 3)) :
    (tensorPauliLaw n (relabelGate (bitVecEquiv n) (qubitTensor A)) (newProduct_physical A hA)).expect
      (tensorPauliValue w)=
      (newWord w*relabelGate (bitVecEquiv n) (qubitTensor A)).trace.re := by
  rw [tensorPauliValue_mean,newWord_measured]
end Qatlib.Papers.RydbergMaxCut26.Rounding.TensorReadout
