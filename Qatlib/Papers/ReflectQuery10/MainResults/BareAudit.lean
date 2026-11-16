/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ReflectQuery10.MainResults.BarePowerTest
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # A constant-zero boundary of the unrestricted historical bare-power interface

Fixed source1005.1601v1 Proposition3.6. Its proof of the false clause explicitly
uses a true input in Eq3.23, or a separate constant-function branch. The old
upper-budget SourceDualFeasible interface alone admits a constant-zero instance
with zero witness space. Its genuine two-dimensional reflection is minus the
identity and every bare-power root measurement accepts with probability one.
This diagnoses an omitted interface/preprocessing condition, not the source's
nonconstant-function argument.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace Qatlib.Papers.ReflectQuery10.MainResults.BareAudit
open Qatlib.Concepts.QueryComplexity.Reflections
open Qatlib.Papers.ReflectQuery10.MainResults
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

/-- The actual one-coordinate input is zero. -/
def input (_ : Unit) (_ : Fin 1) : Bool := false

/-- The constant-zero output family. -/
def output (_ : Unit) : Bool := false

/-- The actual witness family in the zero-dimensional witness space. -/
def witness (_ : Unit) (_ : Fin 1) : Fin 0 → ℂ := 0

/-- The actual graph has one row vertex and one root, with no witness vertices. -/
abbrev Space := Vertex Unit output 1 0

/-- The distinguished root is an actual nonempty graph vertex. -/
def root : Space := Sum.inr (Sum.inl ())

/-- This constant family really satisfies every old upper-budget dual constraint. -/
theorem feasible : SourceDualFeasible input output witness 1 := by
  constructor
  · intro x
    norm_num [witness]
  · intro x y _ hy
    simp [output] at hy

/-- The zero matrix is an actual orthogonal projector. -/
theorem zeroProjector : IsOrthogonalProjector (0 : Matrix Space Space ℂ) := by
  exact IsStarProjection.zero (Matrix Space Space ℂ)

/-- A state annihilated by this actual graph adjacency is zero. -/
theorem kernelZero (v : QState Space)
    (hv : adjacency input output witness 1 *ᵥ v=0) : v=0 := by
  let : Unique (Fin0 Unit output) :=
    ⟨⟨(),rfl⟩,fun a => Subtype.ext (Subsingleton.elim _ _)⟩
  have hrow:=congrFun hv (Sum.inl ⟨(),rfl⟩)
  have hroot:=congrFun hv root
  have hzroot : v root=0 := by
    simpa [adjacency,blockAdjacency,biadj,tvec,root,Matrix.mulVec,dotProduct,
      Fintype.sum_sum_type,Fintype.sum_prod_type] using hrow
  ext z
  rcases z with a|z
  · have ha : a=⟨(),rfl⟩ := Subtype.ext (Subsingleton.elim _ _)
    subst a
    simpa [adjacency,blockAdjacency,biadj,tvec,root,Matrix.mulVec,dotProduct,
      Fintype.sum_sum_type,Fintype.sum_prod_type] using hroot
  · rcases z with u|z
    · cases u
      exact hzroot
    · exact Fin.elim0 z.2.2

/-- The supplied projector is precisely the actual adjacency-kernel projector. -/
theorem kernelProjector (v : QState Space) :
    adjacency input output witness 1 *ᵥ v=0 ↔ (0 : Matrix Space Space ℂ)*ᵥ v=v := by
  constructor
  · intro h
    rw [kernelZero v h]
    simp
  · intro h
    have hz : v=0 := by simpa using h.symm
    simp [hz]

/-- With no witness labels, the actual input projection is the identity. -/
theorem inputIdentity : pixProj input output ()=(1 : Matrix Space Space ℂ) := by
  ext a b
  rcases a with a|a
  · simp [pixProj,Matrix.diagonal_apply,Matrix.one_apply]
  · rcases a with a|a
    · simp [pixProj,complementMark,Matrix.diagonal_apply,Matrix.one_apply]
    · exact Fin.elim0 a.2.2

/-- The actual two-reflection unitary is minus the identity. -/
theorem minusIdentity :
    twoReflectionUnitary input output () (0 : Matrix Space Space ℂ)=-1 := by
  rw [twoReflectionUnitary,inputIdentity]
  ext a b
  by_cases h : a=b <;> norm_num [Matrix.mul_apply,Matrix.one_apply,h]

/-- Every actual bare power of minus identity has unit root Born probability. -/
theorem powerBorn {J : Type} [Fintype J] [DecidableEq J] (z : J) (k : ℕ) :
    ‖(((-1 : Matrix J J ℂ)^k)*ᵥ Ket z) z‖^2=1 := by
  have he : (-1 : Matrix J J ℂ)=(-1 : ℂ) • 1 := by simp
  rw [he,smul_pow,one_pow,Matrix.smul_mulVec,Matrix.one_mulVec]
  simp [Ket,norm_pow]

/-- The entire nonempty-horizon average equals one in the concrete old interface. -/
theorem scoreOne (τ : ℕ) (hτ : 0<τ) :
    barePowerScore (twoReflectionUnitary input output () (0 : Matrix Space Space ℂ)) root τ=1 := by
  rw [minusIdentity,barePowerScore]
  simp only [barePowerState,powerBorn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast ne_of_gt hτ)

/-- All interface premises hold, but the old false-input bound fails at its actual source horizon. -/
theorem falseBoundFails : ¬ (barePowerScore
    (twoReflectionUnitary input output () (0 : Matrix Space Space ℂ)) root
    (Nat.ceil (100000*(1 : ℝ)))≤(61/100 : ℝ)) := by
  rw [scoreOne _ (by norm_num)]
  norm_num

/-- The concrete boundary uses a normalized root in a genuine two-dimensional graph. -/
theorem rootNormalized : Normalized (Ket root) := normalized_ket root

/-- The unrestricted false-input extension of the current vocabulary is false without a constant-case condition. -/
theorem univFalseBound : ¬ (∀ (X : Type) [Fintype X] [DecidableEq X] (n m : ℕ)
    (inp : X → Fin n → Bool) (f : X → Bool) (v : X → Fin n → Fin m → ℂ) (W : ℝ),
    SourceDualFeasible inp f v W → 1≤W →
    ∀ Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ,
      IsOrthogonalProjector Δ →
      (∀ z, adjacency inp f v W *ᵥ z=0 ↔ Δ *ᵥ z=z) →
      ∀ x, f x=false →
        barePowerScore (twoReflectionUnitary inp f x Δ)
          (Sum.inr (Sum.inl ())) (Nat.ceil (100000*W))≤(61/100 : ℝ)) := by
  intro h
  exact falseBoundFails (h Unit 1 0 input output witness 1 feasible (by norm_num)
    0 zeroProjector kernelProjector () rfl)

end Qatlib.Papers.ReflectQuery10.MainResults.BareAudit
