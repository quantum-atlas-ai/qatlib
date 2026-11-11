/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Ext
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification

/-!
# Unitary dilation of a finite Kraus family

A finite family satisfying the Kraus completeness relation defines an isometry into the system
together with an outcome register. `kraus_unitary_dilation` extends this isometry to a unitary
whose action on a fixed initialized register records each Kraus output coherently, as in
[NielsenChuang2010].

## Main statements

* `krausDilationMatrix_gram`: completeness gives an identity Gram matrix.
* `kraus_unitary_dilation`: a unitary realizes the Kraus isometry on the initialized ancilla
  subspace.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false

namespace Qatlib.Concepts.Execution.KnownKraus

open Matrix
open scoped BigOperators

/-- The rectangular matrix that stacks the Kraus operators in a joint system and outcome
register. -/
private def krausDilationMatrix {d s : ℕ} (K : Fin s → Operator d) :
    Matrix (Fin d × Fin s) (Fin d) ℂ :=
  fun x j => K x.2 x.1 j

/-- The stacked Kraus matrix has identity Gram matrix when the Kraus family satisfies
completeness. -/
private theorem krausDilationMatrix_gram {d s : ℕ} (K : Fin s → Operator d)
    (hK : ∑ a, (K a).conjTranspose * K a = 1) :
    (krausDilationMatrix K).conjTranspose * krausDilationMatrix K = 1 := by
  ext i j
  calc
    ((krausDilationMatrix K).conjTranspose * krausDilationMatrix K) i j =
        ∑ a : Fin s, ((K a).conjTranspose * K a) i j := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
        krausDilationMatrix, Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ = (∑ a : Fin s, (K a).conjTranspose * K a) i j := by
      simp only [Matrix.sum_apply]
    _ = (1 : Operator d) i j := congrFun (congrFun hK i) j

/-- The complex linear isometry induced by the stacked matrix of a complete Kraus family. -/
private noncomputable def krausDilationIsometry {d s : ℕ} (K : Fin s → Operator d)
    (hK : ∑ a, (K a).conjTranspose * K a = 1) :
    EuclideanSpace ℂ (Fin d) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d × Fin s) :=
  (krausDilationMatrix K).toEuclideanLin.isometryOfInner (by
    intro v w
    change inner ℂ (toEuclidean_fromVec (krausDilationMatrix K *ᵥ v.ofLp))
      (toEuclidean_fromVec (krausDilationMatrix K *ᵥ w.ofLp)) =
        inner ℂ (toEuclidean_fromVec v.ofLp) (toEuclidean_fromVec w.ofLp)
    rw [inner_euclidean_fromVec, inner_euclidean_fromVec]
    simp only [Qatlib.Foundations.PureStateMath.Inner, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, krausDilationMatrix_gram K hK, Matrix.vecMul_one])

/-- A complete finite square Kraus family can be realized coherently by a unitary on the system
and an initialized outcome register [NielsenChuang2010]. -/
theorem kraus_unitary_dilation {d s : ℕ} (K : Fin s → Operator d)
    (hK : ∑ a, (K a).conjTranspose * K a = 1) (zero : Fin s) :
    ∃ W : Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ,
      W ∈ Matrix.unitaryGroup (Fin d × Fin s) ℂ ∧
        ∀ psi : QState (Fin d),
          ApplyGate W (TensorState psi (Qatlib.Foundations.PureStateMath.Ket zero)) =
            fun x => ApplyGate (K x.2) psi x.1 := by
  let e : Fin d ↪ Fin d × Fin s :=
    ⟨fun i => (i, zero), fun _ _ h => congrArg Prod.fst h⟩
  obtain ⟨W, hW, hact⟩ := adaptiveHistoryIsometries_transport
    (adaptiveCoordinateIsometry e) (krausDilationIsometry K hK)
  refine ⟨W, hW, ?_⟩
  intro psi
  have hm : ApplyGate W (adaptiveCoordinateMatrix e *ᵥ psi) =
      krausDilationMatrix K *ᵥ psi :=
    congrArg WithLp.ofLp (hact (toEuclidean_fromVec psi))
  have hseed : adaptiveCoordinateMatrix e *ᵥ psi = TensorState psi (Qatlib.Foundations.PureStateMath.Ket zero) := by
    funext x
    rcases x with ⟨i, a⟩
    by_cases ha : a = zero
    · subst a
      simpa [TensorState, Qatlib.Foundations.PureStateMath.Ket, e] using
        adaptiveCoordinateMatrix_apply_image e psi i
    · have hout : ∀ k, e k ≠ (i, a) := by
        intro k hk
        exact ha (congrArg Prod.snd hk).symm
      simpa [TensorState, Qatlib.Foundations.PureStateMath.Ket, ha] using
        adaptiveCoordinateMatrix_apply_outside e psi (i, a) hout
  change ApplyGate W
      (TensorState psi (Qatlib.Foundations.PureStateMath.Ket zero)) = krausDilationMatrix K *ᵥ psi
  rw [← hseed]
  exact hm

end Qatlib.Concepts.Execution.KnownKraus
