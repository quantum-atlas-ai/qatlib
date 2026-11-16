/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AncilFreeClfT14.MainResults.LegacyAlgebra

@[expose] public section

/-! # Preserved closed legacy mathematics
This module uses the archived coefficient model at the fixed public pin.
It does not identify free operation counts with Clifford+T circuit costs.
-/
set_option autoImplicit false
noncomputable section
open scoped Real
open Complex
namespace Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy
open Qatlib.Papers.AncilFreeClfT14.MainResults

/-- An enumeration of the solutions of a predicate `P`, with an operation-cost
function on the outputs.  `sound` says every output solves `P`, `complete` says
every solution is eventually output. -/
structure Enumeration {α : Type} (P : α → Prop) where
  next : ℕ → Option α
  sound : ∀ n a, next n = some a → P a
  complete : ∀ a, P a → ∃ n, next n = some a
  cost : ℕ → ℕ

/-- An axis-parallel closed rectangle `[x₀,x₁] × [y₀,y₁]` in the plane. -/
def IsUprightRect (A : Set ℂ) : Prop :=
  ∃ x0 x1 y0 y1 : ℝ, x0 ≤ x1 ∧ y0 ≤ y1 ∧
    A = {z | z.re ∈ Set.Icc x0 x1 ∧ z.im ∈ Set.Icc y0 y1}

/-- Convexity of a planar set, written on `ℂ` (the paper's `R²`). -/
def Convex2 (A : Set ℂ) : Prop :=
  ∀ u ∈ A, ∀ v ∈ A, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    ((t : ℂ) * u + ((1 - t : ℝ) : ℂ) * v) ∈ A

/-- `A` is the point set of an ellipse in the sense of Definition 5.15. -/
def IsEllipseSet (A : Set ℂ) : Prop := ∃ E : Ellipse, A = E.points

/-! ## A grid operator together with its 2-conjugate

Theorem 5.16 and Proposition 5.13 use both `G` and the entrywise 2-conjugate
`G•` (Remark 5.12).  We carry the two matrices as data; the relation between
them is the conjugation `√2 ↦ -√2` of Remark 5.12. -/

/-- A special grid operator `G` (Definition 5.10) together with its entrywise
2-conjugate `G•`. -/
structure SpecialGridOperator where
  mat : Mat2
  bulletMat : Mat2
  mapsZomega : ∀ u : Zomega, ∃ v : Zomega, v.toComplex = mat.apply u.toComplex
  special : mat.det = 1 ∨ mat.det = -1

namespace SpecialGridOperator

/-- `G(A) = {G u | u ∈ A}`. -/
def image (G : SpecialGridOperator) (A : Set ℂ) : Set ℂ := matImage G.mat A

/-- `G•(B) = {G• u | u ∈ B}`. -/
def bulletImage (G : SpecialGridOperator) (B : Set ℂ) : Set ℂ := matImage G.bulletMat B

end SpecialGridOperator

end Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy
