/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MinorClosed10.MainResults.PathCover

@[expose] public section


/-! # Explicit covers of subdivided stars

Demand: Childs--Kothari, fixed arXiv1011.1443v2 Proposition 4.1.
The constructor is definitionally the paper's three-branch claw when
the length vector has three entries. Covers and disjoint-edge lower
bounds refer to the actual graph edges.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.MinorClosed10.MainResults.ClawCover
open PathCover

/-- A subdivided star with finitely many branches of the prescribed lengths. -/
def starG {I : Type} (d : I → ℕ) : SimpleGraph (Unit ⊕ (Σ i, Fin (d i))) :=
  SimpleGraph.fromRel (fun a b => match a, b with
    | .inl _, .inr ⟨_, j⟩ => j.val = 0
    | .inr ⟨i,j⟩, .inr ⟨i',j'⟩ => i = i' ∧ j.val+1=j'.val
    | _, _ => False)

/-- The cover containing the centre and every odd-indexed branch vertex. -/
def withCentre {I : Type} (d : I → ℕ) : Set (Unit ⊕ (Σ i, Fin (d i))) :=
  {v | match v with | .inl _ => True | .inr ⟨_,j⟩ => j.val%2=1}

/-- The cover excluding the centre and containing every even-indexed branch vertex. -/
def noCentre {I : Type} (d : I → ℕ) : Set (Unit ⊕ (Σ i, Fin (d i))) :=
  {v | match v with | .inl _ => False | .inr ⟨_,j⟩ => j.val%2=0}

/-- The centre together with odd branch vertices meets every genuine star edge. -/
theorem withCover {I : Type} (d : I → ℕ) : (starG d).IsVertexCover (withCentre d) := by
  rintro (a | ⟨i,a⟩) (b | ⟨j,b⟩) h
  · simp [starG, SimpleGraph.fromRel] at h
  · exact Or.inl trivial
  · exact Or.inr trivial
  · change _ ∧ ((i=j ∧ a.val+1=b.val) ∨ (j=i ∧ b.val+1=a.val)) at h
    change a.val%2=1 ∨ b.val%2=1
    rcases h.2 with h | h <;> omega

/-- The even branch vertices meet every genuine star edge without the centre. -/
theorem noCover {I : Type} (d : I → ℕ) : (starG d).IsVertexCover (noCentre d) := by
  rintro (a | ⟨i,a⟩) (b | ⟨j,b⟩) h
  · simp [starG, SimpleGraph.fromRel] at h
  · change _ ∧ (b.val=0 ∨ False) at h
    have hb : b.val=0 := h.2.resolve_right id
    exact Or.inr (by change b.val%2=0; rw [hb])
  · change _ ∧ (False ∨ a.val=0) at h
    have ha : a.val=0 := h.2.resolve_left id
    exact Or.inl (by change a.val%2=0; rw [ha])
  · change _ ∧ ((i=j ∧ a.val+1=b.val) ∨ (j=i ∧ b.val+1=a.val)) at h
    change a.val%2=0 ∨ b.val%2=0
    rcases h.2 with h | h <;> omega

/-- Enumerate exactly the centre and the actual odd branch vertices. -/
def withEquiv {I : Type} (d : I → ℕ) :
    (Unit ⊕ (Σ i, Fin (d i/2))) ≃ withCentre d where
  toFun v := match v with
    | .inl u => ⟨.inl u, trivial⟩
    | .inr ⟨i,j⟩ => ⟨.inr ⟨i,⟨2*j.val+1, by have := j.isLt; omega⟩⟩,
        by change (2*j.val+1)%2=1; omega⟩
  invFun v := match v with
    | ⟨.inl u,_⟩ => .inl u
    | ⟨.inr ⟨i,j⟩,h⟩ => .inr ⟨i,⟨j.val/2,
        by have := j.isLt; change j.val%2=1 at h; omega⟩⟩
  left_inv v := by
    rcases v with u | ⟨i,j⟩
    · rfl
    · dsimp only
      apply congrArg Sum.inr
      apply congrArg (Sigma.mk i)
      apply Fin.ext
      dsimp
      omega
  right_inv v := by
    rcases v with ⟨u | ⟨i,j⟩,h⟩
    · rfl
    · apply Subtype.ext
      dsimp only
      apply congrArg Sum.inr
      apply congrArg (Sigma.mk i)
      apply Fin.ext
      change j.val%2=1 at h
      dsimp
      omega

/-- Enumerate exactly the actual even branch vertices. -/
def noEquiv {I : Type} (d : I → ℕ) :
    (Σ i, Fin ((d i+1)/2)) ≃ noCentre d where
  toFun v := ⟨.inr ⟨v.1,⟨2*v.2.val, by have := v.2.isLt; omega⟩⟩,
    by change (2*v.2.val)%2=0; omega⟩
  invFun v := match v with
    | ⟨.inl _,h⟩ => False.elim h
    | ⟨.inr ⟨i,j⟩,h⟩ => ⟨i,⟨j.val/2,
        by have := j.isLt; change j.val%2=0 at h; omega⟩⟩
  left_inv v := by
    rcases v with ⟨i,j⟩
    dsimp only
    apply congrArg (Sigma.mk i)
    apply Fin.ext
    dsimp
    omega
  right_inv v := by
    rcases v with ⟨u | ⟨i,j⟩,h⟩
    · exact False.elim h
    · apply Subtype.ext
      dsimp only
      apply congrArg Sum.inr
      apply congrArg (Sigma.mk i)
      apply Fin.ext
      change j.val%2=0 at h
      dsimp
      omega

/-- The actual centre cover has one vertex plus half of each branch rounded down. -/
theorem withCard {I : Type} [Fintype I] (d : I → ℕ) :
    (withCentre d).encard = ((1 + ∑ i, d i/2 : ℕ) : ℕ∞) := by
  have h := Fintype.card_congr (withEquiv d)
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_sigma,
    Fintype.card_fin] at h
  simpa [Set.encard, ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card] using
    congrArg (fun n : ℕ => (n : ℕ∞)) h.symm

/-- The actual cover excluding the centre contains half of each branch rounded up. -/
theorem noCard {I : Type} [Fintype I] (d : I → ℕ) :
    (noCentre d).encard = ((∑ i, (d i+1)/2 : ℕ) : ℕ∞) := by
  have h := Fintype.card_congr (noEquiv d)
  simp only [Fintype.card_sigma, Fintype.card_fin] at h
  simpa [Set.encard, ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card] using
    congrArg (fun n : ℕ => (n : ℕ∞)) h.symm

end Qatlib.Papers.MinorClosed10.MainResults.ClawCover
