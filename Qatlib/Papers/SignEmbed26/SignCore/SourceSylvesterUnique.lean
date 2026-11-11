/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

set_option backward.isDefEq.respectTransparency false

/-!
# Uniqueness of the Sylvester solution under spectral separation

Source: Y. Wang and J.-P. Liu, *Sign Embedding Quantum Algorithms for Matrix Equations and
Matrix Functions*, arXiv:2604.25333v2, proof of Theorem 3.3 (Section 3.2).

The source closes the proof of Theorem 3.3 by observing that the Sylvester solution `X` of
`A X + X B = C` is unique: "Uniqueness follows from the half-plane separation, which implies
`spec(A) ∩ (-spec(B)) = ∅`".

This module formalizes that step.  A solution of the homogeneous equation `A Z + Z B = 0`
intertwines the endomorphism `-B` with `A`, hence carries each generalized eigenspace of `-B`
into the generalized eigenspace of `A` for the same scalar.  If `A` and `-B` share no
eigenvalue, the relevant generalized eigenspaces are trivial, so `Z` vanishes on the span of
the generalized eigenspaces of `-B` — which, over an algebraically closed field, is the whole
space.  Hence `Z = 0` and the solution is unique.

The half-plane version used by the source (spectrum of `A` in `Re > 0`, spectrum of `-B` in
`Re < 0`, over `ℂ`) is recorded as a corollary.
-/

namespace Qatlib.Papers.SignEmbed26.SignCore

open Matrix Module

set_option autoImplicit false

variable {K : Type*} [Field K] [IsAlgClosed K] {n : Type*} [Fintype n] [DecidableEq n]

omit [IsAlgClosed K] in
/-- A solution of the homogeneous Sylvester equation `A Z + Z B = 0` intertwines the linear map
`-B` with the linear map `A` on vectors: `A (Z v) = Z (-B v)`. -/
theorem sylvester_intertwine {A B Z : Matrix n n K} (hZ : A * Z + Z * B = 0) (v : n → K) :
    Matrix.toLin' A (Matrix.toLin' Z v) = Matrix.toLin' Z (Matrix.toLin' (-B) v) := by
  have h : A * Z = -(Z * B) := eq_neg_of_add_eq_zero_left hZ
  simp only [Matrix.toLin'_apply, Matrix.neg_mulVec]
  calc
    A *ᵥ (Z *ᵥ v) = (A * Z) *ᵥ v := (Matrix.mulVec_mulVec v A Z)
    _ = (-(Z * B)) *ᵥ v := by rw [h]
    _ = -((Z * B) *ᵥ v) := by rw [Matrix.neg_mulVec]
    _ = -(Z *ᵥ (B *ᵥ v)) := by rw [Matrix.mulVec_mulVec]
    _ = Z *ᵥ (-(B *ᵥ v)) := by rw [Matrix.mulVec_neg]

omit [IsAlgClosed K] [Fintype n] [DecidableEq n] in
/-- The intertwining relation survives subtracting the same scalar from both sides: if
`f (x v) = x (g v)` for all `v`, then `(f - μI) (x v) = x ((g - μI) v)`. -/
theorem intertwine_sub_smul {f g x : Module.End K (n → K)} (h : ∀ v, f (x v) = x (g v)) (mu : K) :
    ∀ v, (f - mu • 1) (x v) = x ((g - mu • 1) v) := by
  intro v
  calc (f - mu • 1) (x v) = f (x v) - mu • x v := by simp
    _ = x (g v) - x (mu • v) := by rw [h v, ← map_smul]
    _ = x (g v - mu • v) := by rw [map_sub]
    _ = x ((g - mu • 1) v) := by simp

omit [IsAlgClosed K] [Fintype n] [DecidableEq n] in
/-- Iterated form of `intertwine_sub_smul`. -/
theorem intertwine_pow {f g x : Module.End K (n → K)} (h : ∀ v, f (x v) = x (g v)) (mu : K)
    (k : ℕ) (v : n → K) :
    ((f - mu • 1) ^ k) (x v) = x (((g - mu • 1) ^ k) v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply,
        intertwine_sub_smul h mu v, ih]

omit [IsAlgClosed K] [Fintype n] [DecidableEq n] in
/-- An endomorphism carrying every generalized eigenspace of `g` for `μ` into the corresponding
generalized eigenspace of `f` — the consequence of the intertwining relation used in the source
uniqueness argument. -/
theorem map_maxGenEigenspace_le {f g x : Module.End K (n → K)}
    (h : ∀ v, f (x v) = x (g v)) (mu : K) :
    (g.maxGenEigenspace mu).map x ≤ f.maxGenEigenspace mu := by
  intro y hy
  rw [Submodule.mem_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [Module.End.mem_maxGenEigenspace] at hz ⊢
  obtain ⟨k, hk⟩ := hz
  exact ⟨k, by rw [intertwine_pow h mu k z, hk, map_zero]⟩

omit [IsAlgClosed K] [Fintype n] [DecidableEq n] in
/-- If `f` has no eigenvalue `μ`, then its generalized `μ`-eigenspace is trivial: the powers
`(f - μI)^k` are all injective because `f - μI` already is. -/
theorem maxGenEigenspace_eq_bot_of_not_hasEigenvalue {f : Module.End K (n → K)} {mu : K}
    (h : ¬ f.HasEigenvalue mu) : f.maxGenEigenspace mu = ⊥ := by
  have hbot : f.eigenspace mu = ⊥ := by
    by_contra hc
    exact h (Module.End.hasEigenvalue_iff.mpr hc)
  have hker : LinearMap.ker (f - mu • 1) = ⊥ := by
    simpa [Module.End.eigenspace_def] using hbot
  have hinj : Function.Injective (f - (mu • 1 : Module.End K (n → K))) :=
    LinearMap.ker_eq_bot.mp hker
  rw [Submodule.eq_bot_iff]
  intro z hz
  rw [Module.End.mem_maxGenEigenspace] at hz
  obtain ⟨k, hk⟩ := hz
  have hiter : ∀ (k : ℕ) (y : n → K), ((f - (mu • 1 : Module.End K (n → K))) ^ k) y = 0 →
      y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
        intro y hy
        rw [pow_succ', Module.End.mul_apply] at hy
        exact ih _ ((hinj.eq_iff).mp (by simpa using hy))
  exact hiter k z hk

/-- **The Sylvester kernel is trivial under spectral separation.**  If `A` and `-B` share no
eigenvalue, then `A Z + Z B = 0` forces `Z = 0`. -/
theorem sylvester_eq_zero {A B Z : Matrix n n K} (hsep : ∀ mu : K,
    ¬ (Module.End.HasEigenvalue (Matrix.toLin' A) mu ∧
        Module.End.HasEigenvalue (Matrix.toLin' (-B)) mu))
    (hZ : A * Z + Z * B = 0) : Z = 0 := by
  have hinter : ∀ v, Matrix.toLin' A (Matrix.toLin' Z v) =
      Matrix.toLin' Z (Matrix.toLin' (-B) v) := fun v => sylvester_intertwine hZ v
  have hle : ∀ mu : K,
      Module.End.maxGenEigenspace (Matrix.toLin' (-B)) mu ≤ LinearMap.ker (Matrix.toLin' Z) := by
    intro mu
    by_cases hg : Module.End.HasEigenvalue (Matrix.toLin' (-B)) mu
    · have hf := maxGenEigenspace_eq_bot_of_not_hasEigenvalue (f := Matrix.toLin' A)
        (fun hfm => hsep mu ⟨hfm, hg⟩)
      intro z hz
      rw [LinearMap.mem_ker]
      have hmap := map_maxGenEigenspace_le (f := Matrix.toLin' A) (g := Matrix.toLin' (-B))
        (x := Matrix.toLin' Z) hinter mu (Submodule.mem_map_of_mem hz)
      rw [hf] at hmap
      simpa using hmap
    · rw [maxGenEigenspace_eq_bot_of_not_hasEigenvalue (f := Matrix.toLin' (-B)) hg]
      exact bot_le
  have htop : LinearMap.ker (Matrix.toLin' Z) = ⊤ := by
    rw [eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top (Matrix.toLin' (-B))]
    exact iSup_le hle
  have hx0 : Matrix.toLin' Z = 0 := by
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ LinearMap.ker (Matrix.toLin' Z) := by
      rw [htop]
      exact Submodule.mem_top
    simpa using hv
  have h := congrArg LinearMap.toMatrix' hx0
  simpa using h

/-- **Uniqueness of the Sylvester solution** (last line of the proof of Theorem 3.3).  Under
spectral separation of `A` and `-B`, the equation `A X + X B = C` has at most one solution. -/
theorem sylvester_unique {A B C X Y : Matrix n n K} (hsep : ∀ mu : K,
    ¬ (Module.End.HasEigenvalue (Matrix.toLin' A) mu ∧
        Module.End.HasEigenvalue (Matrix.toLin' (-B)) mu))
    (hX : A * X + X * B = C) (hY : A * Y + Y * B = C) : X = Y := by
  have hzero : A * (X - Y) + (X - Y) * B = 0 := by
    rw [Matrix.mul_sub, Matrix.sub_mul,
      show A * X - A * Y + (X * B - Y * B) = (A * X + X * B) - (A * Y + Y * B) from by abel,
      hX, hY, sub_self]
  have hXY := sylvester_eq_zero hsep hzero
  rwa [sub_eq_zero] at hXY

/-- **Half-plane separation implies no common eigenvalue.**  Over `ℂ`, if every eigenvalue of
`A` has positive real part and every eigenvalue of `-B` has negative real part, then `A` and
`-B` share no eigenvalue.  These are exactly the hypotheses of Theorem 3.3. -/
theorem no_common_eigenvalue_of_halfPlane {A B : Matrix n n ℂ}
    (hA : ∀ mu : ℂ, Module.End.HasEigenvalue (Matrix.toLin' A) mu → 0 < mu.re)
    (hB : ∀ mu : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (-B)) mu → mu.re < 0) :
    ∀ mu : ℂ, ¬ (Module.End.HasEigenvalue (Matrix.toLin' A) mu ∧
        Module.End.HasEigenvalue (Matrix.toLin' (-B)) mu) := by
  intro mu h
  have h1 := hA mu h.1
  have h2 := hB mu h.2
  linarith

/-- **Theorem 3.3, uniqueness under the half-plane separation.**  Under the source hypotheses
`spec A ⊂ {Re > 0}` and `spec (-B) ⊂ {Re < 0}`, the solution `X` of `A X + X B = C` is unique. -/
theorem sylvester_unique_of_halfPlane {A B C X Y : Matrix n n ℂ}
    (hA : ∀ mu : ℂ, Module.End.HasEigenvalue (Matrix.toLin' A) mu → 0 < mu.re)
    (hB : ∀ mu : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (-B)) mu → mu.re < 0)
    (hX : A * X + X * B = C) (hY : A * Y + Y * B = C) : X = Y :=
  sylvester_unique (no_common_eigenvalue_of_halfPlane hA hB) hX hY

end Qatlib.Papers.SignEmbed26.SignCore
