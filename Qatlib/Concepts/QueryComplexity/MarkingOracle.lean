/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Boolean marking oracles

Constructs a reversible Boolean marking oracle on an index register with an auxiliary flag,
together with matrix lifts and circuits applying `Tᴴ * U * T` before marking. The amplitude and
squared-mass identities require no normalization assumptions on the input state.

The conjugated diagonal-entry formulas specialize constant and weighted columns to arithmetic
means. This finite-register setting is standard in quantum algorithms; see [NielsenChuang2010].

## Main statements

* `markMatrix_unitary`: the marking permutation matrix is unitary.
* `markingCircuit_good_mass`: the true-flag sector carries the transformed marked-index squared
  mass.
* `conjugated_phase_mean`: weighted uniform columns extract a conjugate-weighted mean.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace Qatlib.Concepts.QueryComplexity.MarkingOracle
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Flips the Boolean flag exactly at indices marked by `z`. -/
def markBasis (z : I → Bool) (x : I×Bool) : I×Bool :=
  (x.1,if z x.1 then !x.2 else x.2)

omit [Fintype I] [DecidableEq I] in

/-- Applying `markBasis z` twice returns the original index and flag. -/
theorem markBasis_involutive (z : I → Bool) : Function.Involutive (markBasis z) := by
  intro x
  rcases x with ⟨i,b⟩
  cases hz : z i <;> simp [markBasis,hz]

/-- The permutation of index-flag pairs induced by the marking involution. -/
def markPerm (z : I → Bool) : Equiv.Perm (I×Bool) :=
  Function.Involutive.toPerm (markBasis z) (markBasis_involutive z)

/-- The permutation matrix implementing the Boolean marking oracle. -/
def markMatrix (z : I → Bool) : Matrix (I×Bool) (I×Bool) ℂ :=
  (markPerm z).permMatrix ℂ

/-- The Boolean marking matrix is unitary. -/
theorem markMatrix_unitary (z : I → Bool) : markMatrix z ∈ Matrix.unitaryGroup (I×Bool) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change (markPerm z).permMatrix ℂ*((markPerm z).permMatrix ℂ)ᴴ=1
  rw [Matrix.conjTranspose_permMatrix,← Matrix.permMatrix_mul]
  simp

/-- The marking matrix acts by evaluating the input state at the conditionally flipped flag. -/
theorem markMatrix_mulVec (z : I → Bool) (psi : I×Bool → ℂ) (i : I) (b : Bool) :
    (markMatrix z*ᵥ psi) (i,b)=psi (i,if z i then !b else b) := by
  rw [markMatrix,Matrix.permMatrix_mulVec]
  rfl

/-- Embeds a state into the sector whose Boolean flag is false. -/
def zeroFlag (psi : I→ℂ) : I×Bool→ℂ := fun x=>if x.2 then 0 else psi x.1

/-- After marking a false-flag state, the true-flag amplitude equals the original amplitude on
marked indices and vanishes elsewhere. -/
theorem marking_good_amplitude (z : I→Bool) (psi : I→ℂ) (i : I) :
    (markMatrix z*ᵥ zeroFlag psi) (i,true)=if z i then psi i else 0 := by
  rw [markMatrix_mulVec]
  cases hz : z i <;> simp [zeroFlag]

/-- The squared norm in the true-flag sector after marking is the total squared amplitude on
marked indices. -/
theorem marking_good_mass (z : I→Bool) (psi : I→ℂ) :
    (∑i,‖(markMatrix z*ᵥ zeroFlag psi) (i,true)‖^2)=
      ∑i,if z i then ‖psi i‖^2 else 0 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [marking_good_amplitude]
  cases hz : z i <;> simp

/-- Extends a matrix to the index-flag register by tensoring with the identity on the flag. -/
def liftFlag (A : Matrix I I ℂ) : Matrix (I×Bool) (I×Bool) ℂ :=
  A ⊗ₖ (1 : Matrix Bool Bool ℂ)

/-- Tensoring a unitary matrix with the identity on the flag preserves unitarity. -/
theorem liftFlag_unitary (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    liftFlag A ∈ Matrix.unitaryGroup (I×Bool) ℂ :=
  Matrix.kronecker_mem_unitary hA (one_mem _)

omit [DecidableEq I] in

/-- Applying the lifted matrix to a false-flag state applies the original matrix to its index
register. -/
theorem liftFlag_zeroFlag (A : Matrix I I ℂ) (psi : I→ℂ) :
    liftFlag A*ᵥ zeroFlag psi=zeroFlag (A*ᵥ psi) := by
  funext x
  rcases x with ⟨i,b⟩
  cases b <;> simp [liftFlag,zeroFlag,Matrix.mulVec,dotProduct,
    Fintype.sum_prod_type,Matrix.one_apply]

/-- Applies `Tᴴ * U * T` to the index register and then marks the Boolean flag. -/
def markingCircuit (z : I→Bool) (T U : Matrix I I ℂ) : Matrix (I×Bool) (I×Bool) ℂ :=
  markMatrix z*liftFlag (Tᴴ*U*T)

/-- The marking circuit is unitary when both `T` and `U` are unitary. -/
theorem markingCircuit_unitary (z : I→Bool) (T U : Matrix I I ℂ)
    (hT : T ∈ Matrix.unitaryGroup I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    markingCircuit z T U ∈ Matrix.unitaryGroup (I×Bool) ℂ :=
  mul_mem (markMatrix_unitary z)
    (liftFlag_unitary _ (mul_mem (mul_mem (Unitary.star_mem hT) hU) hT))

/-- The true-flag amplitude is the amplitude of `Tᴴ * U * T` on marked indices and zero
elsewhere. -/
theorem markingCircuit_good_amplitude (z : I→Bool) (T U : Matrix I I ℂ) (psi : I→ℂ) (i : I) :
    (markingCircuit z T U*ᵥ zeroFlag psi) (i,true)=
      if z i then ((Tᴴ*U*T)*ᵥ psi) i else 0 := by
  rw [markingCircuit,← Matrix.mulVec_mulVec,liftFlag_zeroFlag,marking_good_amplitude]

/-- The true-flag squared mass is the marked-index squared mass of the state transformed by `Tᴴ
* U * T`. -/
theorem markingCircuit_good_mass (z : I→Bool) (T U : Matrix I I ℂ) (psi : I→ℂ) :
    (∑i,‖(markingCircuit z T U*ᵥ zeroFlag psi) (i,true)‖^2)=
      ∑i,if z i then ‖((Tᴴ*U*T)*ᵥ psi) i‖^2 else 0 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [markingCircuit_good_amplitude]
  cases hz : z i <;> simp

/-- For a basis input, the true-flag amplitude is the corresponding entry of `Tᴴ * U * T` on
marked indices. -/
theorem markingCircuit_basis_good (z : I→Bool) (T U : Matrix I I ℂ) (i0 i : I) :
    (markingCircuit z T U*ᵥ zeroFlag (Pi.single i0 1)) (i,true)=
      if z i then (Tᴴ*U*T) i i0 else 0 := by
  rw [markingCircuit_good_amplitude]
  simp [Matrix.mulVec,dotProduct,Pi.single_apply]

/-- Expands an entry of `Tᴴ * Matrix.diagonal u * T` as a sum over products of matrix entries. -/
theorem conjugated_diagonal_entry (T : Matrix I I ℂ) (u : I→ℂ) (i j : I) :
    (Tᴴ*Matrix.diagonal u*T) i j=∑k,star (T k i)*u k*T k j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply]

/-- A constant column of `T` makes the corresponding conjugated diagonal entry equal to `star c
* c` times the sum of the diagonal values. -/
theorem conjugated_uniform_entry (T : Matrix I I ℂ) (u : I→ℂ) (i0 : I) (c : ℂ)
    (hT : ∀k,T k i0=c) :
    (Tᴴ*Matrix.diagonal u*T) i0 i0=(star c*c)*(∑k,u k) := by
  rw [conjugated_diagonal_entry]
  simp_rw [hT]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A constant column and a column weighted by `phase` yield a conjugated entry given by the
conjugate-weighted sum of `u`. -/
theorem conjugated_phase_entry (T : Matrix I I ℂ) (u phase : I→ℂ) (i0 i1 : I) (c : ℂ)
    (h0 : ∀k,T k i0=c) (h1 : ∀k,T k i1=c*phase k) :
    (Tᴴ*Matrix.diagonal u*T) i1 i0=(star c*c)*(∑k,star (phase k)*u k) := by
  rw [conjugated_diagonal_entry]
  simp_rw [h0,h1,star_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Flips the output flag of `markingCircuit` so that marked amplitudes occupy the false-flag
sector. -/
def zeroGoodCircuit (z : I→Bool) (T U : Matrix I I ℂ) : Matrix (I×Bool) (I×Bool) ℂ :=
  markMatrix (fun _=>true)*markingCircuit z T U

/-- The circuit with the final flag flip is unitary when `T` and `U` are unitary. -/
theorem zeroGoodCircuit_unitary (z : I→Bool) (T U : Matrix I I ℂ)
    (hT : T ∈ Matrix.unitaryGroup I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    zeroGoodCircuit z T U ∈ Matrix.unitaryGroup (I×Bool) ℂ :=
  mul_mem (markMatrix_unitary _) (markingCircuit_unitary z T U hT hU)

/-- The false-flag amplitude of `zeroGoodCircuit` equals the transformed amplitude on marked
indices and vanishes elsewhere. -/
theorem zeroGoodCircuit_amplitude (z : I→Bool) (T U : Matrix I I ℂ) (psi : I→ℂ) (i : I) :
    (zeroGoodCircuit z T U*ᵥ zeroFlag psi) (i,false)=
      if z i then ((Tᴴ*U*T)*ᵥ psi) i else 0 := by
  rw [zeroGoodCircuit,← Matrix.mulVec_mulVec,markMatrix_mulVec]
  exact markingCircuit_good_amplitude z T U psi i

/-- The reciprocal square root of the cardinality of the finite index type. -/
def uniformCoefficient (I : Type*) [Fintype I] : ℝ := (Real.sqrt (Fintype.card I))⁻¹

omit [DecidableEq I] in

/-- The squared modulus of the uniform coefficient equals the reciprocal cardinality. -/
theorem uniformCoefficient_star_mul :
    star (uniformCoefficient I : ℂ)*(uniformCoefficient I : ℂ)=(Fintype.card I : ℂ)⁻¹ := by
  have hr : (uniformCoefficient I)^2=(Fintype.card I : ℝ)⁻¹ := by
    unfold uniformCoefficient
    rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul]
  rw [show uniformCoefficient I*uniformCoefficient I=(uniformCoefficient I)^2 by ring,hr]
  simp only [Complex.ofReal_inv,Complex.ofReal_natCast]

/-- A uniformly normalized constant column makes the corresponding conjugated diagonal entry the
arithmetic mean of `u`. -/
theorem conjugated_uniform_mean (T : Matrix I I ℂ) (u : I→ℂ) (i0 : I)
    (hT : ∀k,T k i0=(uniformCoefficient I : ℂ)) :
    (Tᴴ*Matrix.diagonal u*T) i0 i0=(Fintype.card I : ℂ)⁻¹*(∑k,u k) := by
  rw [conjugated_uniform_entry T u i0 _ hT,uniformCoefficient_star_mul]

/-- Uniformly normalized constant and weighted columns give the arithmetic mean of `star (phase
k) * u k` as the conjugated entry. -/
theorem conjugated_phase_mean (T : Matrix I I ℂ) (u phase : I→ℂ) (i0 i1 : I)
    (h0 : ∀k,T k i0=(uniformCoefficient I : ℂ))
    (h1 : ∀k,T k i1=(uniformCoefficient I : ℂ)*phase k) :
    (Tᴴ*Matrix.diagonal u*T) i1 i0=(Fintype.card I : ℂ)⁻¹*(∑k,star (phase k)*u k) := by
  rw [conjugated_phase_entry T u phase i0 i1 _ h0 h1,uniformCoefficient_star_mul]

end Qatlib.Concepts.QueryComplexity.MarkingOracle
