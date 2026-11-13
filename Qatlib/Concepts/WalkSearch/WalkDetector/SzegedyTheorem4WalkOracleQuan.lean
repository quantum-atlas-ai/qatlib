/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkDetector.SzegedyTheorem4WalkOracleStat
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.WalkSearch.TwoLevelLower

/-!
# Unitary extension of the Szegedy isometry

`szegedyTheorem4WalkOracle` proves that a finite transition matrix has a unitary
state-preparation extension on two registers with a fixed basis state in the second register.
The proof extends the orthonormal columns of `SzegedyIsometry` to a full orthonormal basis,
supplying the walk-oracle construction used in [Szegedy2004].

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.WalkDetector
open Matrix
open scoped BigOperators

set_option maxHeartbeats 800000 in

/-- Every finite transition matrix has a unitary extension of `SzegedyIsometry` on inputs with
the second register fixed to a chosen basis state; see [Szegedy2004]. -/
theorem szegedyTheorem4WalkOracle : SzegedyTheorem4WalkOracle := by
  classical
  intro I _ _ P j hP
  let e : I ↪ I × I := ⟨fun i => (i, j), fun _ _ h => congrArg Prod.fst h⟩
  let v : I × I → EuclideanSpace ℂ (I × I) := fun p =>
    WithLp.toLp 2 (fun x => SzegedyIsometry P x p.1)
  have hv : Orthonormal ℂ ((Set.range e).restrict v) := by
    rw [orthonormal_iff_ite]
    intro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    dsimp only [Set.restrict]; rw [EuclideanSpace.inner_eq_star_dotProduct]
    have hab := congrArg (fun M : Matrix I I ℂ => M a b)
      (szegedyIsometry_conjTranspose_mul P hP)
    simpa [e, v, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      dotProduct, Subtype.ext_iff, mul_comm, WithLp.ofLp_toLp] using hab
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (ι := I × I) finrank_euclideanSpace
  let U : Matrix (I × I) (I × I) ℂ := fun x y => b y x
  refine ⟨U, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext x y
    have hxy := orthonormal_iff_ite.mp b.orthonormal x y
    simpa [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using hxy
  · intro i
    rw [tensorState_ket_ket]
    funext x
    have hi := congrArg (fun w : EuclideanSpace ℂ (I × I) => w x)
      (hb (e i) ⟨i, rfl⟩)
    simpa [U, v, e, Matrix.mulVec, dotProduct, Ket, mul_ite] using hi

end Qatlib.Concepts.WalkSearch.WalkDetector
