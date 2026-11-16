/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.Basic.ENNReal.Real

@[expose] public section


/-! # Adversary feasible sets under output coarsening

This is the actual finite-matrix monotonicity argument of Reichardt,
arXiv:0904.2759v1, Lemma10.3. The alphabet and coordinate type are arbitrary.
It does not construct a query algorithm or identify an SDP optimum.
-/

set_option autoImplicit false

noncomputable section
open Matrix
open scoped Classical ENNReal Matrix.Norms.L2Operator

namespace Qatlib.Concepts.AdversaryBounds.AdversarySets

variable {X J C E F : Type*} [Fintype X] [DecidableEq X] [DecidableEq C]

/-- A real symmetric adversary matrix has zero equal-output blocks and bounded filters. -/
def Feasible (input : X → J → C) (f : X → E) (s : J → ℝ)
    (Γ : Matrix X X ℝ) : Prop :=
  Γᵀ = Γ ∧ (∀ x y, f x = f y → Γ x y = 0) ∧
    ∀ j, ‖Γ ⊙ (fun x y => if input x j = input y j then 0 else 1)‖ ≤ s j

/-- The general signed adversary bound is the supremum over actual feasible matrices. -/
def signed (input : X → J → C) (f : X → E) (s : J → ℝ) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℝ // Feasible input f s Γ}, ENNReal.ofReal ‖Γ.1‖

/-- The nonnegative adversary bound restricts the same feasible set entry by entry. -/
def nonnegative (input : X → J → C) (f : X → E) (s : J → ℝ) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℝ // Feasible input f s Γ ∧ ∀ x y, 0 ≤ Γ x y},
    ENNReal.ofReal ‖Γ.1‖

/-- Coarsening outputs restricts the feasible set without changing filters or norms. -/
theorem feasibleCoarsen (input : X → J → C) (f : X → E) (g : E → F)
    (s : J → ℝ) (Γ : Matrix X X ℝ) (h : Feasible input (fun x => g (f x)) s Γ) :
    Feasible input f s Γ := by
  exact ⟨h.1, fun x y hxy => h.2.1 x y (congrArg g hxy), h.2.2⟩

/-- Both optimized adversary bounds can only decrease when outputs are coarsened. -/
theorem boundsCoarsen (input : X → J → C) (f : X → E) (g : E → F) (s : J → ℝ) :
    nonnegative input (fun x => g (f x)) s ≤ nonnegative input f s ∧
      signed input (fun x => g (f x)) s ≤ signed input f s := by
  constructor
  · unfold nonnegative
    apply iSup_le
    rintro ⟨Γ, hfeas, hpos⟩
    exact le_iSup (fun G : {G : Matrix X X ℝ // Feasible input f s G ∧
      ∀ x y, 0 ≤ G x y} => ENNReal.ofReal ‖G.1‖)
      ⟨Γ, feasibleCoarsen input f g s Γ hfeas, hpos⟩
  · unfold signed
    apply iSup_le
    rintro ⟨Γ, hfeas⟩
    exact le_iSup (fun G : {G : Matrix X X ℝ // Feasible input f s G} =>
      ENNReal.ofReal ‖G.1‖) ⟨Γ, feasibleCoarsen input f g s Γ hfeas⟩

/-- A constant output forces every feasible matrix to zero, hence the signed value is zero. -/
theorem signedConstant (input : X → J → C) (e : E) (s : J → ℝ) :
    signed input (fun _ => e) s = 0 := by
  apply le_antisymm
  · unfold signed
    apply iSup_le
    rintro ⟨Γ,hΓ⟩
    have hz : Γ = 0 := by
      ext x y
      exact hΓ.2.1 x y rfl
    simp [hz]
  · exact bot_le

/-- Constant outputs also have zero nonnegative adversary value, including empty domains. -/
theorem nonnegConstant (input : X → J → C) (e : E) (s : J → ℝ) :
    nonnegative input (fun _ => e) s = 0 := by
  apply le_antisymm
  · unfold nonnegative
    apply iSup_le
    rintro ⟨Γ,hΓ,_⟩
    have hz : Γ = 0 := by
      ext x y
      exact hΓ.2.1 x y rfl
    simp [hz]
  · exact bot_le

end Qatlib.Concepts.AdversaryBounds.AdversarySets
