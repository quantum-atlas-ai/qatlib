/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.ApproxProducts
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Bridge generators and finite-word approximation

This module defines subspace special unitaries extended by the identity, a bridge mixing
condition, and approximation by finite words in continuous linear maps. It proves basic closure
and norm properties of this approximation relation and a dimension argument producing a
preserved vector in the larger complementary subspace. See [AharonovArad2011].

## Main statements

* `ApproximableBy.comp`: composition preserves approximability under nonexpansion bounds.
* `exists_preserved_vector`: a larger complementary subspace contains a nonzero vector whose
  image remains there.
* `specialUnitary_norm`: extended subspace special unitaries preserve norms.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults.Model

open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The continuous linear maps acting as a determinant-one linear isometry on `A` and as the
identity on its orthogonal complement. -/
def SpecialUnitary (A : Submodule ℂ E) : Set (E →L[ℂ] E) :=
  { T | ∃ U : A ≃ₗᵢ[ℂ] A, LinearMap.det (U : A →ₗ[ℂ] A) = 1 ∧
      ∀ x, T x = ((U (A.orthogonalProjection x) : A) : E) + (x - A.starProjection x) }

/-- The continuous linear maps induced by determinant-one linear isometric equivalences of the
ambient space. -/
def SpecialUnitaryTop : Set (E →L[ℂ] E) :=
  { T | ∃ U : E ≃ₗᵢ[ℂ] E, LinearMap.det (U : E →ₗ[ℂ] E) = 1 ∧ ∀ x, T x = U x }

/-- Some unit vector in `A` has image under `W` with nonzero inner product against a vector in
`B`. -/
def IsBridge (A B : Submodule ℂ E) (W : E ≃ₗᵢ[ℂ] E) : Prop :=
  ∃ u ∈ A, ‖u‖ = 1 ∧ ∃ b ∈ B, inner ℂ (W u : E) b ≠ 0

/-- The map `T` can be approximated to every positive uniform relative tolerance by finite words
of maps from `S`. -/
def ApproximableBy (S : Set (E →L[ℂ] E)) (T : E →L[ℂ] E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ L : List (E →L[ℂ] E), (∀ Q ∈ L, Q ∈ S) ∧
    FunDistLE (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L) (T : E → E) ε

/-- The union of the special unitary maps on `A`, those on `B`, and the single bridge map `W`. -/
def bridgeGenerators (A B : Submodule ℂ E) (W : E ≃ₗᵢ[ℂ] E) : Set (E →L[ℂ] E) :=
  SpecialUnitary A ∪ SpecialUnitary B ∪ {(W : E →L[ℂ] E)}

/-- Evaluating concatenated words is composition of their evaluations, with the first word
acting after the second. -/
theorem evalWord_append {ι : Type*} (ρ : ι → E → E) (w₁ w₂ : List ι) (x : E) :
    evalWord ρ (w₁ ++ w₂) x = evalWord ρ w₁ (evalWord ρ w₂ x) := by
  induction w₁ with
  | nil => rfl
  | cons i w ih => simp only [List.cons_append, evalWord_cons, ih]

/-- A word of maps that do not increase norms also does not increase norms. -/
theorem evalWord_norm_le {ι : Type*} (ρ : ι → E → E) (w : List ι)
    (h : ∀ i ∈ w, ∀ x, ‖ρ i x‖ ≤ ‖x‖) (x : E) :
    ‖evalWord ρ w x‖ ≤ ‖x‖ := by
  induction w with
  | nil => simp
  | cons i w ih =>
      simp only [evalWord_cons]
      have hi : ∀ x, ‖ρ i x‖ ≤ ‖x‖ := h i (by simp)
      have hw : ∀ j ∈ w, ∀ x, ‖ρ j x‖ ≤ ‖x‖ := fun j hj => h j (by simp [hj])
      exact (hi _).trans (ih hw)

/-- The identity map is approximable by words from any generator set. -/
theorem ApproximableBy.id (S : Set (E →L[ℂ] E)) :
    ApproximableBy S (1 : E →L[ℂ] E) := by
  intro ε hε
  refine ⟨[], by simp, ?_⟩
  intro x
  have hone : (1 : E →L[ℂ] E) x = x := by simp
  have hnil : evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) ([] : List (E →L[ℂ] E)) x = x := by
    simp [evalWord]
  rw [hnil, hone, sub_self, norm_zero]
  exact mul_nonneg (le_of_lt hε) (norm_nonneg x)

/-- Every member of a generator set is approximable by words from that set. -/
theorem ApproximableBy.of_mem {S : Set (E →L[ℂ] E)} {T : E →L[ℂ] E} (hT : T ∈ S) :
    ApproximableBy S T := by
  intro ε hε
  refine ⟨([T] : List (E →L[ℂ] E)), by simpa using hT, ?_⟩
  intro x
  have hval : evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) ([T] : List (E →L[ℂ] E)) x = T x := by
    simp [evalWord]
  rw [hval, sub_self, norm_zero]
  exact mul_nonneg (le_of_lt hε) (norm_nonneg x)

/-- Approximable maps remain approximable under composition when all generators and the left
target map do not increase norms. -/
theorem ApproximableBy.comp {S : Set (E →L[ℂ] E)} {T U : E →L[ℂ] E}
    (hS : ∀ Q ∈ S, ∀ x : E, ‖Q x‖ ≤ ‖x‖)
    (hTnorm : ∀ x : E, ‖T x‖ ≤ ‖x‖)
    (hT : ApproximableBy S T) (hU : ApproximableBy S U) :
    ApproximableBy S (T.comp U) := by
  intro ε hε
  obtain ⟨L₁, hL₁, hd₁⟩ := hT (ε / 2) (half_pos hε)
  obtain ⟨L₂, hL₂, hd₂⟩ := hU (ε / 2) (half_pos hε)
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · intro Q hQ
    rcases List.mem_append.mp hQ with h | h
    exacts [hL₁ Q h, hL₂ Q h]
  · intro x
    have hw₂ : ‖evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x‖ ≤ ‖x‖ :=
      evalWord_norm_le _ L₂ (fun Q hQ => hS Q (hL₂ Q hQ)) x
    have happ₁ := hd₁ (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x)
    have happ₂ := hd₂ x
    have hsplit :
        evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) (L₁ ++ L₂) x - (T.comp U) x =
          (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₁
              (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x) -
            T (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x)) +
          (T (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x) - T (U x)) := by
      rw [evalWord_append, ContinuousLinearMap.comp_apply]
      abel
    rw [hsplit]
    have hb₁ :
        ‖evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₁
            (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x) -
          T (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x)‖ ≤
          ε / 2 * ‖evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x‖ := happ₁
    have hb₂ :
        ‖T (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x) - T (U x)‖ ≤ ε / 2 * ‖x‖ := by
      have hlin : T (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x) - T (U x) =
          T (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x - U x) := by
        rw [map_sub]
      rw [hlin]
      exact (hTnorm _).trans happ₂
    calc
      ‖(evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₁
              (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x) -
            T (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x)) +
          (T (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x) - T (U x))‖
          ≤ ‖evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₁
                (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x) -
              T (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x)‖ +
            ‖T (evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x) - T (U x)‖ := norm_add_le _ _
      _ ≤ ε / 2 * ‖evalWord (fun Q : E →L[ℂ] E => (Q : E → E)) L₂ x‖ + ε / 2 * ‖x‖ :=
          add_le_add hb₁ hb₂
      _ ≤ ε / 2 * ‖x‖ + ε / 2 * ‖x‖ := by
          have hε2 : (0 : ℝ) ≤ ε / 2 := le_of_lt (half_pos hε)
          exact add_le_add (mul_le_mul_of_nonneg_left hw₂ hε2) le_rfl
      _ = ε * ‖x‖ := by ring

/-- If `B` is the orthogonal complement of `A` and has larger dimension, every linear isometric
equivalence maps some nonzero vector of `B` into `B`. See [Aharonov and Arad, Lemma
6.1][AharonovArad2011]. -/
theorem exists_preserved_vector {A B : Submodule ℂ E} (hBA : Aᗮ = B)
    (hAB : Module.finrank ℂ A < Module.finrank ℂ B) (W : E ≃ₗᵢ[ℂ] E) :
    ∃ v ∈ B, v ≠ 0 ∧ (W v : E) ∈ B := by

  let f : B →L[ℂ] A :=
    A.orthogonalProjection.comp ((W : E →L[ℂ] E).comp B.subtypeL)
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    have hle : Module.finrank ℂ B ≤ Module.finrank ℂ A :=
      LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) hinj
    omega
  obtain ⟨x, y, hfxy, hne⟩ : ∃ x y : B, f x = f y ∧ x ≠ y := by
    by_contra h
    apply hnotinj
    intro x y hxy
    by_contra hne
    exact h ⟨x, y, hxy, hne⟩
  refine ⟨((x - y : B) : E), (x - y).2, ?_, ?_⟩
  · intro hzero
    apply hne
    have hsub : x - y = 0 := Subtype.ext (by simpa using hzero)
    exact sub_eq_zero.1 hsub
  · have hf0 : f (x - y) = 0 := by
      rw [map_sub, hfxy, sub_self]
    have hproj : A.starProjection (W (((x - y : B) : E))) = 0 := by
      rw [Submodule.starProjection_apply]
      have hval : (A.orthogonalProjection (W (((x - y : B) : E))) : A) = 0 := hf0
      simpa using congrArg (fun z : A => (z : E)) hval
    have hmem : W (((x - y : B) : E)) ∈ Aᗮ := by
      have horth : W (((x - y : B) : E)) -
          A.starProjection (W (((x - y : B) : E))) ∈ Aᗮ :=
        A.sub_starProjection_mem_orthogonal _
      rwa [hproj, sub_zero] at horth
    exact hBA ▸ hmem

/-- Every map in `SpecialUnitary A` preserves the norm of every ambient vector. See [Aharonov
and Arad, Lemma 4.1][AharonovArad2011]. -/
theorem specialUnitary_norm {A : Submodule ℂ E} {T : E →L[ℂ] E}
    (hT : T ∈ SpecialUnitary A) (x : E) : ‖T x‖ = ‖x‖ := by
  obtain ⟨U, _hdet, hTx⟩ := hT
  rw [hTx]
  set p : E := A.starProjection x with hpdef
  have hpA : p ∈ A := by
    rw [hpdef, Submodule.starProjection_apply]; exact Subtype.coe_prop _
  have hborth : x - p ∈ Aᗮ := by
    rw [hpdef]; exact A.sub_starProjection_mem_orthogonal x
  have hxdec : p + (x - p) = x := by abel
  have horth1 : inner ℂ p (x - p) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K := A) hpA hborth
  have hsplit : ((U (A.orthogonalProjection x) : A) : E) = ((U ⟨p, hpA⟩ : A) : E) := by
    congr 2
  have hnorm_first : ‖((U (A.orthogonalProjection x) : A) : E)‖ = ‖p‖ := by
    rw [hsplit, Submodule.norm_coe, U.norm_map, ← Submodule.norm_coe]
  have hfirstA : ((U (A.orthogonalProjection x) : A) : E) ∈ A := Subtype.coe_prop _
  have horth2 : inner ℂ (((U (A.orthogonalProjection x) : A) : E)) (x - p) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K := A) hfirstA hborth
  have hpythT := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (((U (A.orthogonalProjection x) : A) : E)) (x - p) horth2
  have hpythX := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p (x - p) horth1
  rw [hxdec] at hpythX
  rw [hnorm_first] at hpythT
  have h2prod : ‖((U (A.orthogonalProjection x) : A) : E) + (x - p)‖ *
      ‖((U (A.orthogonalProjection x) : A) : E) + (x - p)‖ = ‖x‖ * ‖x‖ := by
    rw [hpythX]; exact hpythT
  have h2 : ‖((U (A.orthogonalProjection x) : A) : E) + (x - p)‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [pow_two, pow_two]; exact h2prod
  have hres := congrArg Real.sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hres

end Qatlib.Papers.BQPJonesPoly06.MainResults.Model
