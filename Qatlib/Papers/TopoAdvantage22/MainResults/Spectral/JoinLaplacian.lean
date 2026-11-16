/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Tactic.Module
public import Mathlib.Basic.Real.Basic

@[expose] public section


/-!
# Join Laplacian on a tensor summand

Lemma 8 and the eigenchain identity of arXiv:2209.13581v3, Appendix F,
hold for arbitrary real linear maps. The spectral converse additionally
assumes an eigenbasis for the second factor. This is sufficient without
finite dimensionality or an eigenbasis for the first factor, and is supplied
by the spectral theorem for the finite symmetric Laplacians in the paper.
The geometric identification with chains of the join is not asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TopoAdvantage22.MainResults.Spectral

open scoped TensorProduct

variable {Vx Vy : Type*}
  [AddCommGroup Vx] [Module ℝ Vx] [AddCommGroup Vy] [Module ℝ Vy]

/-- The sum of the two factor Laplacians acting on a tensor summand. -/
def joinLap (Δx : Vx →ₗ[ℝ] Vx) (Δy : Vy →ₗ[ℝ] Vy) : Vx ⊗[ℝ] Vy →ₗ[ℝ] Vx ⊗[ℝ] Vy :=
  Δx.rTensor Vy + Δy.lTensor Vx

/-- Lemma 8: the join operator acts separately on each factor of a pure tensor. -/
theorem lemma8_join_laplacian (Δx : Vx →ₗ[ℝ] Vx) (Δy : Vy →ₗ[ℝ] Vy)
    (σ : Vx) (τ : Vy) :
    joinLap Δx Δy (σ ⊗ₜ[ℝ] τ) = (Δx σ) ⊗ₜ[ℝ] τ + σ ⊗ₜ[ℝ] (Δy τ) := by
  simp [joinLap]

/-- Corollary 1: tensor products of eigenchains satisfy the sum eigenvalue equation. -/
theorem corollary1_eigenchain (Δx : Vx →ₗ[ℝ] Vx) (Δy : Vy →ₗ[ℝ] Vy)
    (σ : Vx) (τ : Vy) (lam mu : ℝ)
    (hσ : Δx σ = lam • σ) (hτ : Δy τ = mu • τ) :
    joinLap Δx Δy (σ ⊗ₜ[ℝ] τ) = (lam + mu) • (σ ⊗ₜ[ℝ] τ) := by
  rw [lemma8_join_laplacian, hσ, hτ]
  rw [← TensorProduct.smul_tmul, ← TensorProduct.add_tmul, ← add_smul]
  rfl

/-- An eigenvalue has a nonzero eigenvector. -/
def HasEigen (A : Vx →ₗ[ℝ] Vx) (lam : ℝ) : Prop :=
  ∃ v : Vx, v ≠ 0 ∧ A v = lam • v

/-- Corollary 1 with the missing eigenbasis premise on the second factor. -/
theorem corollary1_join_spectrum (Δx : Vx →ₗ[ℝ] Vx) (Δy : Vy →ₗ[ℝ] Vy)
    {ι : Type*} (b : Module.Basis ι ℝ Vy) (mu : ι → ℝ)
    (hy : ∀ i, Δy (b i) = mu i • b i) :
    ∀ lam : ℝ, HasEigen (joinLap Δx Δy) lam ↔
      ∃ lamx lamy : ℝ, HasEigen Δx lamx ∧ HasEigen Δy lamy ∧ lam = lamx + lamy := by
  classical
  let e := TensorProduct.equivFinsuppOfBasisRight (M := Vx) b
  have hd (i : ι) : (b.coord i).comp Δy = mu i • b.coord i := by
    apply b.ext
    intro j
    by_cases h : j = i
    · subst j
      simp [hy, Module.Basis.coord_apply]
    · simp [hy, Module.Basis.coord_apply, Ne.symm h]
  have hc (z : Vx ⊗[ℝ] Vy) (i : ι) :
      e (joinLap Δx Δy z) i = Δx (e z i) + mu i • e z i := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      have hi := LinearMap.congr_fun (hd i) y
      simp only [LinearMap.comp_apply, LinearMap.smul_apply,
        Module.Basis.coord_apply] at hi
      simp [e, lemma8_join_laplacian, hi, smul_smul]
    | add z w hz hw => simp [map_add, hz, hw, smul_add]; module
  intro lam
  constructor
  · rintro ⟨z, hz, he⟩
    have hn : e z ≠ 0 := fun h => hz (e.injective (by simpa using h))
    obtain ⟨i, hi⟩ : ∃ i, e z i ≠ 0 := by
      by_contra h
      apply hn
      ext i
      exact Classical.not_not.mp (fun hi => h ⟨i, hi⟩)
    have hv := hc z i
    rw [he, map_smul] at hv
    refine ⟨lam - mu i, mu i, ⟨e z i, hi, ?_⟩,
      ⟨b i, b.ne_zero i, hy i⟩, (sub_add_cancel _ _).symm⟩
    change lam • e z i = Δx (e z i) + mu i • e z i at hv
    rw [sub_smul]
    exact eq_sub_iff_add_eq.mpr hv.symm
  · rintro ⟨lamx, lamy, ⟨x, hx, hxe⟩, ⟨y, hy0, hye⟩, rfl⟩
    refine ⟨x ⊗ₜ y, ?_, corollary1_eigenchain Δx Δy x y lamx lamy hxe hye⟩
    intro h
    have hn : b.repr y ≠ 0 := fun h => hy0 (b.repr.injective (by simpa using h))
    obtain ⟨i, hi⟩ : ∃ i, b.repr y i ≠ 0 := by
      by_contra h
      apply hn
      ext i
      exact Classical.not_not.mp (fun hi => h ⟨i, hi⟩)
    have hi0 := congrArg (fun z => e z i) h
    simp only [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
      map_zero, Finsupp.zero_apply] at hi0
    exact (smul_ne_zero hi hx) hi0

end Qatlib.Papers.TopoAdvantage22.MainResults.Spectral
