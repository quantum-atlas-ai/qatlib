/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis

/-!
# Padding finite quantum systems into binary registers

`finiteBasisPadding` encodes a finite basis into a binary register, and `finiteBasisPadState`
applies the encoding to states. For injective encodings, the padding matrix is an isometry and
preserves normalization, as in the finite-dimensional circuit framework of [NielsenChuang2010].

`finiteBasisPadUnitary` extends the encoded action of a matrix by the identity on the orthogonal
complement of the encoded subspace. The module proves unitarity and intertwining for injective
encodings and provides the canonical encoding `finiteBasisCode` when the register has enough
basis states.

## Main statements

* `finiteBasisPadding_isometry`: the encoding matrix has orthonormal columns.
* `finiteBasisPadUnitary_unitary`: unitary operators extend to unitary binary-register
  operators.
* `finiteBasisPadUnitary_apply`: extension commutes with applying the original operator.
* `finiteBasisCode_injective`: the canonical binary encoding is injective.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkFind.SearchAlgorithm
open Matrix
open scoped Classical

/-- The matrix sending the basis vector indexed by `i` to the binary basis vector indexed by `e
i`. -/
def finiteBasisPadding {I : Type} [Fintype I] [DecidableEq I]
    {b : ℕ} (e : I → Reg b) : Matrix (Reg b) I ℂ :=
  fun x i => if x = e i then 1 else 0

/-- The binary-register state obtained by multiplying `ψ` by the basis-padding matrix for `e`. -/
def finiteBasisPadState {I : Type} [Fintype I] [DecidableEq I]
    {b : ℕ} (e : I → Reg b) (ψ : QState I) : QState (Reg b) :=
  finiteBasisPadding e *ᵥ ψ

/-- The matrix `E * U * Eᴴ + (1 - E * Eᴴ)`, where `E` is `finiteBasisPadding e`, extending the
encoded action by the complementary term. -/
def finiteBasisPadUnitary {I : Type} [Fintype I] [DecidableEq I]
    {b : ℕ} (e : I → Reg b) (U : Matrix I I ℂ) : Matrix (Reg b) (Reg b) ℂ :=
  finiteBasisPadding e*U*(finiteBasisPadding e)ᴴ +
    (1-finiteBasisPadding e*(finiteBasisPadding e)ᴴ)

/-- A binary encoding of a finite type into `b` bits, obtained by enumerating its elements and
using `Fintype.card I ≤ 2^b`. -/
def finiteBasisCode (I : Type) [Fintype I] (b : ℕ) (hb : Fintype.card I ≤ 2^b) : I → Reg b :=
  fun i => (bitVecEquiv b).symm (Fin.castLE hb ((Fintype.equivFin I) i))

end Qatlib.Concepts.WalkFind.SearchAlgorithm

namespace Qatlib.Concepts.WalkFind.SearchAlgorithm
open Matrix
open scoped Classical BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] {b : ℕ}

omit [DecidableEq I] in

/-- The canonical finite-basis binary encoding is injective. -/
theorem finiteBasisCode_injective (hb : Fintype.card I ≤ 2^b) :
    Function.Injective (finiteBasisCode I b hb) := by
  intro i j hij
  apply (Fintype.equivFin I).injective
  apply Fin.ext
  have h := congrArg (fun x => (bitVecEquiv b) x) hij
  simpa [finiteBasisCode] using! congrArg Fin.val h

/-- The padding matrix for an injective encoding satisfies `Eᴴ * E = 1`. -/
theorem finiteBasisPadding_isometry (e : I → Reg b) (he : Function.Injective e) :
    (finiteBasisPadding e)ᴴ * finiteBasisPadding e = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, finiteBasisPadding]
  rw [Finset.sum_eq_single (e i)]
  · simp [Matrix.one_apply, he.eq_iff]
  · intro x _ hx
    simp [hx]
  · simp

/-- Padding along an injective encoding preserves normalization of quantum states. -/
theorem finiteBasisPadState_normalized (e : I → Reg b) (he : Function.Injective e)
    {ψ : QState I} (hψ : Normalized ψ) : Normalized (finiteBasisPadState e ψ) := by
  have hE := finiteBasisPadding_isometry e he
  have hi : Qatlib.Foundations.PureStateMath.Inner (finiteBasisPadding e *ᵥ ψ) (finiteBasisPadding e *ᵥ ψ) = Qatlib.Foundations.PureStateMath.Inner ψ ψ := by
    simp only [Qatlib.Foundations.PureStateMath.Inner, Matrix.star_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    rw [hE, Matrix.vecMul_one]
  rw [normalized_iff_inner_self]
  exact hi.trans ((normalized_iff_inner_self ψ).mp hψ)

/-- For an injective encoding, the padded matrix intertwines `U` with its encoded action:
`finiteBasisPadUnitary e U * E = E * U`. -/
theorem finiteBasisPadUnitary_intertwining (e : I → Reg b) (he : Function.Injective e)
    (U : Matrix I I ℂ) : finiteBasisPadUnitary e U * finiteBasisPadding e =
      finiteBasisPadding e * U := by
  have hE := finiteBasisPadding_isometry e he
  unfold finiteBasisPadUnitary
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [hE, Matrix.mul_one, Matrix.mul_one]
  simp

/-- Padding a unitary matrix along an injective encoding produces a unitary matrix on the binary
register. -/
theorem finiteBasisPadUnitary_unitary (e : I → Reg b) (he : Function.Injective e)
    (U : Matrix I I ℂ) (hU : U ∈ unitaryGroup I ℂ) :
    finiteBasisPadUnitary e U ∈ unitaryGroup (Reg b) ℂ := by
  let E := finiteBasisPadding e
  have hE : Eᴴ * E = 1 := finiteBasisPadding_isometry e he
  have hu : Uᴴ * U = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using! hU
  let P := E * Eᴴ
  let A := E * U * Eᴴ
  have hpE : P * E = E := by simp [P, Matrix.mul_assoc, hE]
  have hEp : Eᴴ * P = Eᴴ := by simp [P, ← Matrix.mul_assoc, hE]
  have hPP : P * P = P := by
    calc
      P * P = (P * E) * Eᴴ := by simp only [P, Matrix.mul_assoc]
      _ = P := by rw [hpE]
  have hpA : P * A = A := by simp only [A, ← Matrix.mul_assoc, hpE]
  have hstar : Aᴴ = E * Uᴴ * Eᴴ := by simp [A, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hAA : Aᴴ * A = P := by
    rw [hstar]
    simp only [A, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Eᴴ E, hE, Matrix.one_mul,
      ← Matrix.mul_assoc Uᴴ U, hu, Matrix.one_mul]
  have hpstar : Pᴴ = P := by simp [P, Matrix.conjTranspose_mul]
  have hAQ : Aᴴ * (1-P) = 0 := by
    have h := congrArg Matrix.conjTranspose hpA
    simp only [Matrix.conjTranspose_mul, hpstar] at h
    rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]
  have hQA : (1-P) * A = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hpA, sub_self]
  have hQQ : (1-P)*(1-P) = 1-P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      hPP, sub_self, sub_zero]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  change (A+(1-P))ᴴ * (A+(1-P)) = 1
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hpstar]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hAA, hAQ, hQA, hQQ]
  abel

/-- Applying the padded matrix to a padded state agrees with padding the result of applying the
original matrix. -/
theorem finiteBasisPadUnitary_apply (e : I → Reg b) (he : Function.Injective e)
    (U : Matrix I I ℂ) (ψ : QState I) :
    ApplyGate (finiteBasisPadUnitary e U) (finiteBasisPadState e ψ) =
      finiteBasisPadState e (ApplyGate U ψ) := by
  unfold ApplyGate finiteBasisPadState
  rw [Matrix.mulVec_mulVec, finiteBasisPadUnitary_intertwining e he, ← Matrix.mulVec_mulVec]

end Qatlib.Concepts.WalkFind.SearchAlgorithm

namespace Qatlib.Concepts.WalkFind.SearchAlgorithm
open Matrix
open scoped Classical BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] {b : ℕ}

/-- Padding a computational basis state `Ket i` yields `Ket (e i)`. -/
theorem finiteBasisPadState_ket (e : I → Reg b) (i : I) :
    finiteBasisPadState e (Qatlib.Foundations.PureStateMath.Ket i) = Qatlib.Foundations.PureStateMath.Ket (e i) := by
  funext x
  simp [finiteBasisPadState, finiteBasisPadding, Matrix.mulVec, dotProduct,
      Qatlib.Foundations.PureStateMath.Ket]

/-- Basis padding commutes with finite sums of states. -/
theorem finiteBasisPadState_sum {J : Type} [Fintype J] (e : I → Reg b)
    (ψ : J → QState I) : finiteBasisPadState e (∑ j, ψ j) =
      ∑ j, finiteBasisPadState e (ψ j) := by
  unfold finiteBasisPadState
  rw [Matrix.mulVec_sum]

/-- Basis padding commutes with complex scalar multiplication. -/
theorem finiteBasisPadState_smul (e : I → Reg b) (z : ℂ) (ψ : QState I) :
    finiteBasisPadState e (z • ψ) = z • finiteBasisPadState e ψ := Matrix.mulVec_smul _ _ _

/-- For an injective encoding, the padded state's amplitude at `e i` is the original amplitude
at `i`. -/
theorem finiteBasisPadState_apply_image (e : I → Reg b) (he : Function.Injective e)
    (ψ : QState I) (i : I) : finiteBasisPadState e ψ (e i) = ψ i := by
  simp [finiteBasisPadState, finiteBasisPadding, Matrix.mulVec, dotProduct, he.eq_iff]

end Qatlib.Concepts.WalkFind.SearchAlgorithm
