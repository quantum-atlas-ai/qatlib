/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SymmetryAdv10.MainResults.SourceModel

@[expose] public section


/-! # Actual finite-group averaging for the historical Lemma22 core

Fixed source1012.2112v1. This proves Hermiticity, the fixed uniform vector,
and conjugacy invariance of the actual average. The source's junk transport
and adversary objective comparison are separate obligations.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.SymmetryAdv10.MainResults.GroupAverage

/-- The actual finite-group conjugation average. -/
def average {G n : Type} [Fintype G] [Fintype n]
    (U : G → Matrix n n ℂ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (Fintype.card G : ℝ)⁻¹ • ∑ g : G, U g*A*Matrix.conjTranspose (U g)

/-- Every actual summand is Hermitian, hence so is its real-scaled average. -/
theorem hermitian {G n : Type} [Fintype G] [Fintype n]
    (U : G → Matrix n n ℂ) (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (average U A).IsHermitian := by
  classical
  unfold average Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul,Matrix.conjTranspose_sum]
  simp only [star_trivial]
  congr 1
  exact Finset.sum_congr rfl fun g _ => Matrix.isHermitian_mul_mul_conjTranspose (U g) hA

/-- A unitary fixing a vector has its adjoint fix that vector too. -/
theorem adjointFix {n : Type} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (v : n → ℂ)
    (hU : Matrix.conjTranspose U*U=1) (hv : U.mulVec v=v) :
    (Matrix.conjTranspose U).mulVec v=v := by
  calc _=(Matrix.conjTranspose U).mulVec (U.mulVec v) := by rw [hv]
       _=v := by rw [Matrix.mulVec_mulVec,hU,Matrix.one_mulVec]

/-- Actual matrix sums act as sums on every vector. -/
theorem sumAction {G n : Type} [Fintype G] [Fintype n]
    (A : G → Matrix n n ℂ) (v : n → ℂ) :
    (∑ g, A g).mulVec v=∑ g, (A g).mulVec v := by
  classical
  ext i
  simp only [Matrix.mulVec,dotProduct,Finset.sum_apply,Matrix.sum_apply,Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The normalized average fixes the original vector, for every actual group size. -/
theorem fixes {G n : Type} [Fintype G] [Nonempty G] [Fintype n] [DecidableEq n]
    (U : G → Matrix n n ℂ) (A : Matrix n n ℂ) (v : n → ℂ)
    (hU : ∀ g, Matrix.conjTranspose (U g)*U g=1)
    (hUfix : ∀ g, (U g).mulVec v=v) (hA : A.mulVec v=v) :
    (average U A).mulVec v=v := by
  classical
  have hs : ∀ g, (U g*A*Matrix.conjTranspose (U g)).mulVec v=v := by
    intro g
    rw [← Matrix.mulVec_mulVec,adjointFix (U g) v (hU g) (hUfix g),
      ← Matrix.mulVec_mulVec,hA,hUfix g]
  rw [average,Matrix.smul_mulVec,sumAction]
  simp only [hs,Finset.sum_const,Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀]
  · exact one_smul ℝ v
  · exact_mod_cast Fintype.card_ne_zero

/-- The group law and a genuine bijective group reindexing prove invariance. -/
theorem invariant {G n : Type} [Fintype G] [Group G] [Fintype n]
    (U : G → Matrix n n ℂ) (A : Matrix n n ℂ)
    (hgroup : ∀ g h, U g*U h=U (g*h)) (h : G) :
    U h*average U A*Matrix.conjTranspose (U h)=average U A := by
  classical
  simp only [average,mul_smul_comm,Matrix.smul_mul,Finset.mul_sum,Finset.sum_mul]
  congr 1
  calc
    (∑ g : G, U h*(U g*A*Matrix.conjTranspose (U g))*Matrix.conjTranspose (U h))=
        ∑ g : G, U (h*g)*A*Matrix.conjTranspose (U (h*g)) := by
      apply Finset.sum_congr rfl
      intro g _
      simp only [← hgroup,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _=∑ g : G, U g*A*Matrix.conjTranspose (U g) :=
      Function.Bijective.sum_comp (Group.mulLeft_bijective h)
        (fun g : G => U g*A*Matrix.conjTranspose (U g))

/-- The complete historical adversary-and-invariance conjunction, with redundant assumptions removed. -/
theorem wholeOriginal (P : Qatlib.Papers.SymmetryAdv10.MainResults.Problem)
    {G : Type} [Fintype G] [Group G]
    (U : G → Matrix P.F P.F ℂ) (Γ : Matrix P.F P.F ℂ)
    (hU : ∀ g, Matrix.conjTranspose (U g)*U g=1)
    (hgroup : ∀ g h, U g*U h=U (g*h))
    (hdelta : ∀ g, (U g).mulVec P.deltaVec=P.deltaVec)
    (hΓ : P.IsAdversaryMatrix Γ) :
    P.IsAdversaryMatrix (average U Γ) ∧
      ∀ h : G, U h*average U Γ*Matrix.conjTranspose (U h)=average U Γ :=
  ⟨⟨hermitian U Γ hΓ.1,fixes U Γ P.deltaVec hU hdelta hΓ.2⟩,invariant U Γ hgroup⟩

end Qatlib.Papers.SymmetryAdv10.MainResults.GroupAverage
