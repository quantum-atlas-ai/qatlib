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
set_option warningAsError false

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

def hermitianPart {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (1/2:ℝ) • (A+A.conjTranspose)

def shiftSize {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ‖(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℂ)) (hermitianPart A)‖

def shifted {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  A-shiftSize A • 1

theorem hermitianPart_selfAdjoint {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    IsSelfAdjoint (hermitianPart A) := by
  change (hermitianPart A).conjTranspose=hermitianPart A
  simp only [hermitianPart,Matrix.conjTranspose_smul,star_trivial,
    Matrix.conjTranspose_add,Matrix.conjTranspose_conjTranspose]
  rw [add_comm A.conjTranspose A]

theorem hermitianPart_sub_real_one {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (a : ℝ) :
    hermitianPart (A-a • 1)=hermitianPart A-a • 1 := by
  simp only [hermitianPart,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,star_trivial,
    Matrix.conjTranspose_one]
  module

theorem hermitianPart_le_shift {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    hermitianPart A ≤ shiftSize A • (1:Matrix (Fin d) (Fin d) ℂ) := by
  have h := (hermitianPart_selfAdjoint A).le_algebraMap_norm_self
  simpa only [Algebra.algebraMap_eq_smul_one,Matrix.cstar_norm_def,shiftSize] using h

theorem shifted_dissipative {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    hermitianPart (shifted A) ≤ 0 := by
  rw [shifted,hermitianPart_sub_real_one]
  exact sub_nonpos.mpr (hermitianPart_le_shift A)

theorem shifted_negative_part_psd {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    (-(hermitianPart (shifted A))).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (neg_nonneg.mpr (shifted_dissipative A))

set_option backward.isDefEq.respectTransparency false in

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

def koopman {X : Type*} (Φ : X → X) : (X → ℂ) →ₗ[ℂ] (X → ℂ) where
  toFun g x := g (Φ x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem koopman_id {X : Type*} : koopman (id:X → X)=LinearMap.id := rfl

theorem koopman_zero {X T : Type*} [Zero T] (Φ : T → X → X)
    (hzero : ∀ x,Φ 0 x=x) : koopman (Φ 0)=LinearMap.id := by
  ext g x
  change g (Φ 0 x)=g x
  rw [hzero]

theorem koopman_comp {X : Type*} (Φ Ψ : X → X) :
    koopman (Φ ∘ Ψ)=(koopman Ψ).comp (koopman Φ) := rfl

theorem koopman_semigroup {X T : Type*} [AddCommMonoid T] (Φ : T → X → X)
    (hflow : ∀ s t x,Φ (s+t) x=Φ s (Φ t x)) (s t : T) :
    koopman (Φ (s+t))=(koopman (Φ s)).comp (koopman (Φ t)) := by
  ext g x
  change g (Φ (s+t) x)=g (Φ t (Φ s x))
  rw [add_comm s t,hflow]

def invariantKoopman {X T : Type*} (Φ : T → X → X) (S : Submodule ℂ (X → ℂ))
    (hInv : ∀ t g,g ∈ S → koopman (Φ t) g ∈ S) (t : T) : S →ₗ[ℂ] S where
  toFun g := ⟨koopman (Φ t) g,hInv t g g.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem invariantKoopman_semigroup {X T : Type*} [AddCommMonoid T] (Φ : T → X → X)
    (hflow : ∀ s t x,Φ (s+t) x=Φ s (Φ t x)) (S : Submodule ℂ (X → ℂ))
    (hInv : ∀ t g,g ∈ S → koopman (Φ t) g ∈ S) (s t : T) :
    invariantKoopman Φ S hInv (s+t)=
      (invariantKoopman Φ S hInv s).comp (invariantKoopman Φ S hInv t) := by
  ext g x
  change (g : X → ℂ) (Φ (s+t) x)=(g : X → ℂ) (Φ t (Φ s x))
  rw [add_comm s t,hflow]

theorem projection_exact_on_invariant {X T : Type*} (Φ : T → X → X)
    (S : Submodule ℂ (X → ℂ)) (hInv : ∀ t g,g ∈ S → koopman (Φ t) g ∈ S)
    (P : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (hP : ∀ g,g ∈ S → P g=g)
    (t : T) (g : X → ℂ) (hg : g ∈ S) :
    P (koopman (Φ t) (P g))=koopman (Φ t) g := by
  rw [hP g hg,hP _ (hInv t g hg)]

def flipFlow (t : ZMod 2) (x : ZMod 2) : ZMod 2 := x+t

theorem flipFlow_add (s t x : ZMod 2) : flipFlow (s+t) x=flipFlow s (flipFlow t x) := by
  simp only [flipFlow]
  ring

def firstProjection : (ZMod 2 → ℂ) →ₗ[ℂ] (ZMod 2 → ℂ) where
  toFun g x := if x=0 then g 0 else 0
  map_add' g h := by ext x;by_cases hx:x=0 <;> simp [hx]
  map_smul' c g := by ext x;by_cases hx:x=0 <;> simp [hx]

theorem firstProjection_idempotent : firstProjection.comp firstProjection=firstProjection := by
  ext g x
  by_cases hx:x=0 <;> simp [firstProjection,hx]

def compressedFlip (t : ZMod 2) : (ZMod 2 → ℂ) →ₗ[ℂ] (ZMod 2 → ℂ) :=
  firstProjection.comp ((koopman (flipFlow t)).comp firstProjection)

theorem compressedFlip_one : compressedFlip 1=0 := by
  ext g x
  have h10 : (1:ZMod 2) ≠ 0 := by decide
  by_cases hx:x=0 <;> simp [compressedFlip,firstProjection,koopman,flipFlow,hx,h10]

theorem compressedFlip_two : compressedFlip (1+1)=firstProjection := by
  have h11 : (1:ZMod 2)+1=0 := by decide
  rw [h11]
  ext g x
  simp [compressedFlip,firstProjection,koopman,flipFlow]

theorem finite_projection_not_semigroup :
    compressedFlip (1+1) ≠ (compressedFlip 1).comp (compressedFlip 1) := by
  rw [compressedFlip_two,compressedFlip_one]
  intro h
  let g : ZMod 2 → ℂ := fun x => if x=0 then 1 else 0
  have he := congrFun (congrArg (fun P : (ZMod 2 → ℂ) →ₗ[ℂ] (ZMod 2 → ℂ) => P g) h) 0
  norm_num [firstProjection,g] at he

end Qatlib.Concepts.KoopmanFlow.FlowAction
