/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SeqEntangle05.MainResults.ExampleStates
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace

namespace Qatlib.Papers.SeqEntangle05.MainResults.StandardMap

open Qatlib.Papers.SeqEntangle05.MainResults.MPSDefs
open Qatlib.Papers.SeqEntangle05.MainResults.SequentialGeneration

def swapTB (D : ℕ) (x : Fin D × Fin 2 × Fin 2) : Fin D × Fin 2 × Fin 2 :=
  (x.1, x.2.2, x.2.1)

theorem swapTB_invol (D : ℕ) (x : Fin D × Fin 2 × Fin 2) :
    swapTB D (swapTB D x) = x := by
  rcases x with ⟨α, t, b⟩
  rfl

def stdMap (D : ℕ) : Matrix (Fin D × Fin 2 × Fin 2) (Fin D × Fin 2 × Fin 2) ℂ :=
  fun x z => if x = swapTB D z then 1 else 0

theorem stdMap_mul_self (D : ℕ) : stdMap D * stdMap D = 1 := by
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single (swapTB D y)]
  · simp only [stdMap, swapTB_invol, Matrix.one_apply]
    by_cases h : x = y <;> simp [h]
  · intro z _ hz
    simp only [stdMap]
    have : z ≠ swapTB D y := hz
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem stdMap_conjTranspose_eq (D : ℕ) :
    Matrix.conjTranspose (stdMap D) = stdMap D := by
  ext x z
  simp only [Matrix.conjTranspose_apply, stdMap]
  by_cases h : x = swapTB D z
  · have h' : z = swapTB D x := by rw [h, swapTB_invol]
    rw [if_pos h', if_pos h]
    simp
  · have h' : z ≠ swapTB D x := by
      intro hz
      exact h (by rw [hz, swapTB_invol])
    rw [if_neg h', if_neg h]
    simp

theorem stdMap_unitary (D : ℕ) : Matrix.conjTranspose (stdMap D) * stdMap D = 1 := by
  rw [stdMap_conjTranspose_eq, stdMap_mul_self]

theorem stdMap_unitary' (D : ℕ) : stdMap D * Matrix.conjTranspose (stdMap D) = 1 := by
  rw [stdMap_conjTranspose_eq, stdMap_mul_self]

def IsUnitary {D : ℕ} (U : Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ) : Prop :=
  Matrix.conjTranspose U * U = 1 ∧ U * Matrix.conjTranspose U = 1

def atomIsometry {D : ℕ} (U : Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ) :
    IsometryMatrix D :=
  fun a β => U a (β, 0)

theorem atomIsometry_isometry {D : ℕ} (U : Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ)
    (hU : Matrix.conjTranspose U * U = 1) : IsIsometry (atomIsometry U) := by
  unfold IsIsometry
  ext β β'
  have h := congrFun (congrFun hU (β, 0)) (β', 0)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, atomIsometry]
  have hsum : (∑ x : Fin D × Fin 2,
      star (U x (β, (0 : Fin 2))) * U x (β', (0 : Fin 2))) =
      (if (β, (0 : Fin 2)) = (β', (0 : Fin 2)) then (1 : ℂ) else 0) := h
  rw [hsum, Matrix.one_apply]
  by_cases hb : β = β'
  · subst hb; simp
  · have hne : (β, (0 : Fin 2)) ≠ (β', 0) := by simp [hb]
    simp [hb, hne]

def AtomGenerable (D n : ℕ) (ψ : (Fin n → Fin 2) → ℂ) : Prop :=
  ∃ (U : Fin n → Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ) (φI φF : Fin D → ℂ),
    (∀ k, IsUnitary (U k)) ∧
    ∀ bits, ψ bits =
      mpsAmplitude (fun k => isoBlockFamily (atomIsometry (U k))) φI φF bits

theorem atomGenerable_seqGenerable {D n : ℕ} {ψ : (Fin n → Fin 2) → ℂ}
    (h : AtomGenerable D n ψ) : SeqGenerable D n ψ := by
  obtain ⟨U, φI, φF, hU, hpsi⟩ := h
  exact ⟨fun k => atomIsometry (U k), φI, φF,
    fun k => atomIsometry_isometry (U k) (hU k).1, hpsi⟩

def IsometryRealizability (D : ℕ) : Prop :=
  ∀ (V : IsometryMatrix D), IsIsometry V →
    ∃ U : Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ,
      IsUnitary U ∧ V = atomIsometry U

theorem isometryRealizability (D : ℕ) : IsometryRealizability D := by
  classical
  intro V hV
  let E := EuclideanSpace ℂ (Fin D × Fin 2)
  let u : Fin D → E := fun β => WithLp.toLp 2 (fun p => V p β)
  have hu : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro β β'
    have hVentry := congrFun (congrFun hV β) β'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hVentry
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [u, dotProduct, Pi.star_apply]
    rw [show (∑ i : Fin D × Fin 2, V i β' * star (V i β))
        = ∑ i, star (V i β) * V i β' from Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
    exact hVentry
  let s : Set (Fin D × Fin 2) := {p | p.2 = 0}
  let v : (Fin D × Fin 2) → E := fun p => u p.1
  have hv : Orthonormal ℂ (s.restrict v) := by
    let e : s → Fin D := fun p => p.val.1
    have he : Function.Injective e := by
      intro a b h
      exact Subtype.ext (Prod.ext h (by rw [a.prop, b.prop]))
    have hcomp : Orthonormal ℂ (fun p : s => u (e p)) := hu.comp e he
    have hfun : (s.restrict v) = (fun p : s => u (e p)) := by
      funext p
      simp [Set.restrict, v, e]
    rw [hfun]
    exact hcomp
  obtain ⟨b', hb'⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℂ) (E := E) (ι := Fin D × Fin 2) (v := v) (s := s)
    (by
      show Module.finrank ℂ (EuclideanSpace ℂ (Fin D × Fin 2)) = Fintype.card (Fin D × Fin 2)
      exact finrank_euclideanSpace) hv
  let U : Matrix (Fin D × Fin 2) (Fin D × Fin 2) ℂ := fun p q => WithLp.ofLp (b' q) p
  have hUU : Matrix.conjTranspose U * U = 1 := by
    ext q q'
    rw [Matrix.mul_apply]
    have hinner : ⟪b' q, b' q'⟫_ℂ
        = ∑ p, WithLp.ofLp (b' q') p * star (WithLp.ofLp (b' q) p) :=
      EuclideanSpace.inner_eq_star_dotProduct _ _
    simp only [Matrix.conjTranspose_apply, Matrix.one_apply, U]
    rw [show (∑ p : Fin D × Fin 2,
          star (WithLp.ofLp (b' q) p) * WithLp.ofLp (b' q') p)
        = ∑ p, WithLp.ofLp (b' q') p * star (WithLp.ofLp (b' q) p) from
      Finset.sum_congr rfl (fun p _ => mul_comm _ _)]
    rw [← hinner, orthonormal_iff_ite.mp b'.orthonormal q q']
  refine ⟨U, ⟨hUU, mul_eq_one_comm.mp hUU⟩, ?_⟩
  ext p β
  have hmem : (β, (0 : Fin 2)) ∈ s := rfl
  have hb : b' (β, 0) = u β := by
    rw [hb' (β, 0) hmem]
  simp only [atomIsometry, U, hb, u, WithLp.ofLp_toLp]

theorem seqGenerable_atomGenerable {D n : ℕ} (hreal : IsometryRealizability D)
    {ψ : (Fin n → Fin 2) → ℂ} (h : SeqGenerable D n ψ) : AtomGenerable D n ψ := by
  obtain ⟨V, φI, φF, hV, hpsi⟩ := h
  choose U hU hVeq using fun k => hreal (V k) (hV k)
  refine ⟨U, φI, φF, hU, ?_⟩
  intro bits
  rw [hpsi bits]
  simp only [hVeq]

theorem three_sets_equivalent {D n : ℕ} (hfactor : BlockFactorization D)
    (hreal : IsometryRealizability D) {ψ : (Fin n → Fin 2) → ℂ} :
    IsMPS D n ψ ↔ AtomGenerable D n ψ :=
  ⟨fun h => seqGenerable_atomGenerable hreal (isMPS_seqGenerable hfactor h),
   fun h => seqGenerable_isMPS (atomGenerable_seqGenerable h)⟩

theorem seqGenerable_iff_atomGenerable {D n : ℕ} (hreal : IsometryRealizability D)
    {ψ : (Fin n → Fin 2) → ℂ} : SeqGenerable D n ψ ↔ AtomGenerable D n ψ :=
  ⟨seqGenerable_atomGenerable hreal, atomGenerable_seqGenerable⟩

theorem seqGenerable_atomGenerable_uncond {D n : ℕ} {ψ : (Fin n → Fin 2) → ℂ}
    (h : SeqGenerable D n ψ) : AtomGenerable D n ψ :=
  seqGenerable_atomGenerable (isometryRealizability D) h

theorem three_sets_equivalent_uncond {D n : ℕ} {ψ : (Fin n → Fin 2) → ℂ} :
    IsMPS D n ψ ↔ AtomGenerable D n ψ :=
  three_sets_equivalent (blockFactorization D) (isometryRealizability D)

theorem seqGenerable_iff_atomGenerable_uncond {D n : ℕ} {ψ : (Fin n → Fin 2) → ℂ} :
    SeqGenerable D n ψ ↔ AtomGenerable D n ψ :=
  seqGenerable_iff_atomGenerable (isometryRealizability D)

end Qatlib.Papers.SeqEntangle05.MainResults.StandardMap
