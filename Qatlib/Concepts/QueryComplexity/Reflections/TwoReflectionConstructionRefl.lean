/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.TwoReflectionConstructionStat
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Concepts.BlockEncoding.Basic

/-!
# Construction of the two reflection projectors

Proves that the span-program graph adjacency is Hermitian and its input-dependent diagonal
matrix is an orthogonal projector. The corresponding reflection is identified with the phase
oracle marking complement input labels.

`twoReflectionConstruction` also supplies an orthogonal projector onto the adjacency kernel,
completing the matrix construction associated with [Reichardt2011].

## Main statements

* `pixProj_reflection`: the input-projector reflection equals the complement-marking phase
  oracle.
* `twoReflectionConstruction`: packages the graph, input-projection, and kernel-projection
  properties.

## References

* [Reichardt, Eqs. (2.2)-(2.6)][Reichardt2011]
-/

set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.CoherentSim.CoherentOAA

namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open scoped BigOperators

/-- The block adjacency matrix of any complex biadjacency equals its conjugate transpose. -/
private theorem blockAdjacency_hermitian {R C : Type} [DecidableEq R] [DecidableEq C]
    (B : Matrix R C ℂ) : (blockAdjacency B)ᴴ = blockAdjacency B := by
  ext p q
  cases p <;> cases q <;> simp [blockAdjacency, Matrix.conjTranspose_apply]

/-- The input-dependent diagonal matrix `pixProj` is an orthogonal projector. -/
private theorem pixProj_orthogonal {X : Type} [Fintype X] [DecidableEq X] (n m : ℕ)
    (input : X → Fin n → Bool) (f : X → Bool) (x : X) :
    IsOrthogonalProjector (pixProj (m := m) input f x) := by
  classical
  constructor
  · change pixProj input f x * pixProj input f x = pixProj input f x
    simp only [pixProj, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext l
    cases l with
    | inl r => simp
    | inr c => cases complementMark input f x c <;> simp
  · change (pixProj input f x)ᴴ = pixProj input f x
    simp only [pixProj, Matrix.diagonal_conjTranspose]
    apply congrArg Matrix.diagonal
    funext l
    cases l with
    | inl r => simp
    | inr c => cases complementMark input f x c <;> simp

/-- Reflection about the input projector equals the phase oracle marking complement input
labels. -/
private theorem pixProj_reflection {X : Type} [Fintype X] [DecidableEq X] (n m : ℕ)
    (input : X → Fin n → Bool) (f : X → Bool) (x : X) :
    (2 : ℂ) • pixProj (m := m) input f x - 1 =
      PhaseOracle (fun l => match l with
        | Sum.inl _ => false
        | Sum.inr c => complementMark input f x c) := by
  classical
  ext p q
  by_cases hpq : p=q
  · subst q
    cases p with
    | inl r => norm_num [pixProj, PhaseOracle, Matrix.smul_apply]
    | inr c =>
      cases hc : complementMark input f x c <;>
        norm_num [pixProj, PhaseOracle, Matrix.smul_apply, hc]
  · simp [pixProj, PhaseOracle, Matrix.smul_apply, hpq]

/-- The graph adjacency is Hermitian, input projections are orthogonal with the prescribed
phase-oracle reflections, and an orthogonal projector onto the adjacency kernel exists. See
[Reichardt, Eqs. (2.2)-(2.6)][Reichardt2011]. -/
theorem twoReflectionConstruction : TwoReflectionConstruction := by
  classical
  intro X _ _ n m input f v W
  refine ⟨blockAdjacency_hermitian _, pixProj_orthogonal n m input f,
    pixProj_reflection n m input f, ?_⟩
  let A := adjacency input f v W
  let R := matrixPseudoinverse A*A
  refine ⟨1-R, (matrixPseudoinverse_projectors A).2.one_sub, ?_⟩
  intro z
  constructor
  · intro hz
    change (1-matrixPseudoinverse A*A)*ᵥ z = z
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hz]
    simp
  · intro hz
    have hRz : R*ᵥ z = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hz
      exact sub_eq_self.mp hz
    have hAR : A*R = A := by
      simpa only [R, ← Matrix.mul_assoc] using mul_matrixPseudoinverse_mul A
    change A*ᵥ z = 0
    calc
      _ = (A*R)*ᵥ z := by rw [hAR]
      _ = A*ᵥ(R*ᵥ z) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hRz, Matrix.mulVec_zero]

end Qatlib.Concepts.QueryComplexity.Reflections
