/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-!
# Koopman actions, scalar shifts, and compression

This module defines the pullback action `koopman`, its restriction to invariant observable
subspaces, and scalar shifts making a matrix dissipative. It also gives a finite two-point
example showing that compression by a projection can destroy the semigroup law. These
constructions provide algebraic background for Koopman simulation [ZhangEtAl2026].

## Main statements

* `scalar_shift_exponential`: exponential recovery after subtracting a scalar identity.
* `invariantKoopman_semigroup`: the semigroup law on an invariant subspace.
* `finite_projection_not_semigroup`: a counterexample for projected evolution.

## References

* [Zhang et al., 2026][ZhangEtAl2026]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Concepts.KoopmanFlow.FlowAction

noncomputable local instance matrixCStar {d : ℕ} : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) where
noncomputable local instance matrixRatAlgebra {d : ℕ} : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _
noncomputable local instance matrixRealAlgebra {d : ℕ} : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  NormedAlgebra.restrictScalars ℝ ℂ _

/-- The Hermitian part `(A + Aᴴ) / 2` of a complex square matrix. -/
def hermitianPart {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (1/2:ℝ) • (A+A.conjTranspose)

/-- The Euclidean operator norm of the Hermitian part of `A`, used as a scalar shift. -/
def shiftSize {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ‖(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℂ)) (hermitianPart A)‖

/-- The matrix obtained from `A` by subtracting `shiftSize A` times the identity. -/
def shifted {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  A-shiftSize A • 1

/-- The Hermitian part of a complex square matrix is self-adjoint. -/
theorem hermitianPart_selfAdjoint {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    IsSelfAdjoint (hermitianPart A) := by
  change (hermitianPart A).conjTranspose=hermitianPart A
  simp only [hermitianPart,Matrix.conjTranspose_smul,star_trivial,
    Matrix.conjTranspose_add,Matrix.conjTranspose_conjTranspose]
  rw [add_comm A.conjTranspose A]

/-- Taking the Hermitian part commutes with subtracting a real scalar multiple of the identity. -/
theorem hermitianPart_sub_real_one {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (a : ℝ) :
    hermitianPart (A-a • 1)=hermitianPart A-a • 1 := by
  simp only [hermitianPart,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,star_trivial,
    Matrix.conjTranspose_one]
  module

/-- Bounds the Hermitian part of `A` above by `shiftSize A` times the identity in the matrix
order. -/
theorem hermitianPart_le_shift {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    hermitianPart A ≤ shiftSize A • (1:Matrix (Fin d) (Fin d) ℂ) := by
  have h := (hermitianPart_selfAdjoint A).le_algebraMap_norm_self
  simpa only [Algebra.algebraMap_eq_smul_one,Matrix.cstar_norm_def,shiftSize] using h

/-- The Hermitian part of `shifted A` is nonpositive in the matrix order. -/
theorem shifted_dissipative {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    hermitianPart (shifted A) ≤ 0 := by
  rw [shifted,hermitianPart_sub_real_one]
  exact sub_nonpos.mpr (hermitianPart_le_shift A)

/-- The negative of the Hermitian part of `shifted A` is positive semidefinite. -/
theorem shifted_negative_part_psd {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    (-(hermitianPart (shifted A))).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (neg_nonneg.mpr (shifted_dissipative A))

set_option backward.isDefEq.respectTransparency false in

/-- Expresses the exponential of `t • A` as the exponential of `t • shifted A` multiplied by the
real scalar `exp (t * shiftSize A)`. -/
theorem scalar_shift_exponential {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) :
    NormedSpace.exp (t • A)=Real.exp (t*shiftSize A) • NormedSpace.exp (t • shifted A) := by
  have he : t • A = algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) (t*shiftSize A)+t • shifted A := by
    rw [Algebra.algebraMap_eq_smul_one,shifted,smul_sub,smul_smul]
    module
  have hc : Commute (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) (t*shiftSize A)) (t • shifted A) :=
    Algebra.commute_algebraMap_left _ _
  rw [he,NormedSpace.exp_add_of_commute hc,
    ← NormedSpace.algebraMap_exp_comm (𝕂:=ℝ),← Real.exp_eq_exp_ℝ,
    Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]

/-- The complex-linear pullback operator sending an observable `g` to `g ∘ Φ`. -/
def koopman {X : Type*} (Φ : X → X) : (X → ℂ) →ₗ[ℂ] (X → ℂ) where
  toFun g x := g (Φ x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Pullback by the identity map is the identity linear map on observables. -/
theorem koopman_id {X : Type*} : koopman (id:X → X)=LinearMap.id := rfl

/-- If `Φ 0` fixes every point, its Koopman operator is the identity. -/
theorem koopman_zero {X T : Type*} [Zero T] (Φ : T → X → X)
    (hzero : ∀ x,Φ 0 x=x) : koopman (Φ 0)=LinearMap.id := by
  ext g x
  change g (Φ 0 x)=g x
  rw [hzero]

/-- Pullback reverses the order of composition of the underlying maps. -/
theorem koopman_comp {X : Type*} (Φ Ψ : X → X) :
    koopman (Φ ∘ Ψ)=(koopman Ψ).comp (koopman Φ) := rfl

/-- An additive flow over a commutative time monoid induces the corresponding semigroup law for
its Koopman operators. -/
theorem koopman_semigroup {X T : Type*} [AddCommMonoid T] (Φ : T → X → X)
    (hflow : ∀ s t x,Φ (s+t) x=Φ s (Φ t x)) (s t : T) :
    koopman (Φ (s+t))=(koopman (Φ s)).comp (koopman (Φ t)) := by
  ext g x
  change g (Φ (s+t) x)=g (Φ t (Φ s x))
  rw [add_comm s t,hflow]

/-- The restriction of `koopman (Φ t)` to an observable submodule preserved by every map in the
family. -/
def invariantKoopman {X T : Type*} (Φ : T → X → X) (S : Submodule ℂ (X → ℂ))
    (hInv : ∀ t g,g ∈ S → koopman (Φ t) g ∈ S) (t : T) : S →ₗ[ℂ] S where
  toFun g := ⟨koopman (Φ t) g,hInv t g g.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The Koopman operators restricted to an invariant submodule satisfy the additive semigroup
law of the underlying flow. -/
theorem invariantKoopman_semigroup {X T : Type*} [AddCommMonoid T] (Φ : T → X → X)
    (hflow : ∀ s t x,Φ (s+t) x=Φ s (Φ t x)) (S : Submodule ℂ (X → ℂ))
    (hInv : ∀ t g,g ∈ S → koopman (Φ t) g ∈ S) (s t : T) :
    invariantKoopman Φ S hInv (s+t)=
      (invariantKoopman Φ S hInv s).comp (invariantKoopman Φ S hInv t) := by
  ext g x
  change (g : X → ℂ) (Φ (s+t) x)=(g : X → ℂ) (Φ t (Φ s x))
  rw [add_comm s t,hflow]

/-- A linear map fixing an invariant submodule can be applied before and after Koopman evolution
without changing the evolution of any observable in that submodule. -/
theorem projection_exact_on_invariant {X T : Type*} (Φ : T → X → X)
    (S : Submodule ℂ (X → ℂ)) (hInv : ∀ t g,g ∈ S → koopman (Φ t) g ∈ S)
    (P : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (hP : ∀ g,g ∈ S → P g=g)
    (t : T) (g : X → ℂ) (hg : g ∈ S) :
    P (koopman (Φ t) (P g))=koopman (Φ t) g := by
  rw [hP g hg,hP _ (hInv t g hg)]

/-- Translation by `t` on the two-element additive group `ZMod 2`. -/
def flipFlow (t : ZMod 2) (x : ZMod 2) : ZMod 2 := x+t

/-- Translations in `flipFlow` compose according to addition of their time parameters. -/
theorem flipFlow_add (s t x : ZMod 2) : flipFlow (s+t) x=flipFlow s (flipFlow t x) := by
  simp only [flipFlow]
  ring

/-- The linear projection retaining the value of an observable at zero and setting its other
value to zero. -/
def firstProjection : (ZMod 2 → ℂ) →ₗ[ℂ] (ZMod 2 → ℂ) where
  toFun g x := if x=0 then g 0 else 0
  map_add' g h := by ext x;by_cases hx:x=0 <;> simp [hx]
  map_smul' c g := by ext x;by_cases hx:x=0 <;> simp [hx]

/-- Composing `firstProjection` with itself leaves it unchanged. -/
theorem firstProjection_idempotent : firstProjection.comp firstProjection=firstProjection := by
  ext g x
  by_cases hx:x=0 <;> simp [firstProjection,hx]

/-- The Koopman operator for `flipFlow t` compressed on both sides by `firstProjection`. -/
def compressedFlip (t : ZMod 2) : (ZMod 2 → ℂ) →ₗ[ℂ] (ZMod 2 → ℂ) :=
  firstProjection.comp ((koopman (flipFlow t)).comp firstProjection)

/-- The compressed one-step flip is the zero linear map. -/
theorem compressedFlip_one : compressedFlip 1=0 := by
  ext g x
  have h10 : (1:ZMod 2) ≠ 0 := by decide
  by_cases hx:x=0 <;> simp [compressedFlip,firstProjection,koopman,flipFlow,hx,h10]

/-- The compressed two-step flip equals `firstProjection`. -/
theorem compressedFlip_two : compressedFlip (1+1)=firstProjection := by
  have h11 : (1:ZMod 2)+1=0 := by decide
  rw [h11]
  ext g x
  simp [compressedFlip,firstProjection,koopman,flipFlow]

/-- The compressed two-point flip fails the semigroup identity at the sum `1 + 1`. -/
theorem finite_projection_not_semigroup :
    compressedFlip (1+1) ≠ (compressedFlip 1).comp (compressedFlip 1) := by
  rw [compressedFlip_two,compressedFlip_one]
  intro h
  let g : ZMod 2 → ℂ := fun x => if x=0 then 1 else 0
  have he := congrFun (congrArg (fun P : (ZMod 2 → ℂ) →ₗ[ℂ] (ZMod 2 → ℂ) => P g) h) 0
  norm_num [firstProjection,g] at he

end Qatlib.Concepts.KoopmanFlow.FlowAction
