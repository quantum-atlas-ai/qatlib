/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ApproxSpan15.MainResults.TimeComplexity

@[expose] public section

/-!
# Reflection spectra and the adjoint form of `U′`

Ito--Jeffery, *Approximate Span Programs*, arXiv:1507.00432v1, Appendix B, Lemma B.2
(p. 28), and Section 3 (p. 13).

Lemma B.2 identifies the `±1`-eigenspaces of the product
`W = (2Π_Z - I)(2Π_Y - I)` of two reflections: a vector `v ∈ Y` is fixed by `W` exactly
when `v ∈ Y ∩ Z`, and is sent to `-v` exactly when `v ∈ Y ∩ Zᗮ`.  The two statements below
record this on `Y`, where the first reflection already acts as the identity.

Section 3 (p. 13) writes the second walk unitary as
`U′(P,x) = U(P,x)† (I - 2|w₀⟩⟨w₀|)` under the source's standing assumption that `w₀` is a
unit vector in `(ker A)ᗮ`, so that `T = ker A ⊕ span{w₀}`.  The operator identity is proved
here for the model's `Qatlib.Papers.ApproxSpan15.MainResults.SpanProgram.Uprime`, with
`Π_{span{w₀}}` in place of the Dirac projector `|w₀⟩⟨w₀|`; for a unit `w₀` the two agree,
since then `Π_{span{w₀}} v = ⟪w₀, v⟫ • w₀`.  The proof uses only that `ker A` and
`span{w₀}` are orthogonal, plus the orthogonality of `U` as a product of two reflections.

The identity is an operator-level statement: no query, register or gate semantics is
asserted, matching the paper-layer boundary for Lemma 3.1.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ApproxSpan15.MainResults

open scoped RealInnerProductSpace InnerProduct

open Qatlib.Papers.ApproxSpan15.MainResults

variable {q n : ℕ} {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Lemma B.2 (p. 28), eigenvalues of a product of two reflections on `Y`.**  For
subspaces `Y, Z` and any `v ∈ Y`, the reflected vector
`reflectionAbout Z (reflectionAbout Y v)` equals `v` exactly when `v ∈ Z`, and equals
`-v` exactly when `v ∈ Zᗮ`.  Since `reflectionAbout Y` fixes `Y` pointwise, this is the
Lemma B.2 statement for `W = (2Π_Z - I)(2Π_Y - I)` restricted to `Y`.  The paper's
identification of the image sets with `M_Y(ker A)` and `M_Y((ker A)ᗮ)` is not part of this
lemma. -/
theorem reflectionProduct_eigenspaces (Y Z : Submodule ℝ H) :
    (∀ v : H, v ∈ Y → (SpanProgram.reflectionAbout Z (SpanProgram.reflectionAbout Y v) = v ↔
        v ∈ Z)) ∧
      ∀ v : H, v ∈ Y → (SpanProgram.reflectionAbout Z (SpanProgram.reflectionAbout Y v) = -v ↔
        v ∈ Zᗮ) := by
  have hfix : ∀ v : H, v ∈ Y → SpanProgram.reflectionAbout Y v = v := fun v hv =>
    (Qatlib.Papers.ApproxSpan15.MainResults.TimeComplexity.source_lemma_B_2 Y Y).1 v hv |>.mpr hv
  constructor
  · intro v hv
    rw [hfix v hv]
    exact (Qatlib.Papers.ApproxSpan15.MainResults.TimeComplexity.source_lemma_B_2 Y Z).1 v hv
  · intro v hv
    rw [hfix v hv]
    exact (Qatlib.Papers.ApproxSpan15.MainResults.TimeComplexity.source_lemma_B_2 Y Z).2 v hv

/-- The orthogonal projector onto the supremum of two orthogonal subspaces is the sum of
the two projectors. -/
theorem starProjection_sup_of_isOrtho {K W : Submodule ℝ H} (h : K ⟂ W) (v : H) :
    (K ⊔ W).starProjection v = K.starProjection v + W.starProjection v := by
  have h1 : v - K.starProjection v ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have h2 : v - W.starProjection v ∈ Wᗮ := Submodule.sub_starProjection_mem_orthogonal v
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · exact Submodule.add_mem_sup (Submodule.coe_mem _) (Submodule.coe_mem _)
  · rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    have e1 : ⟪a, v - K.starProjection v⟫ = 0 :=
      (Submodule.mem_orthogonal K _).mp h1 a ha
    have e2 : ⟪a, W.starProjection v⟫ = 0 := h.inner_eq ha (Submodule.coe_mem _)
    have e3 : ⟪b, v - W.starProjection v⟫ = 0 :=
      (Submodule.mem_orthogonal W _).mp h2 b hb
    have e4 : ⟪b, K.starProjection v⟫ = 0 := h.symm.inner_eq hb (Submodule.coe_mem _)
    have hreg1 : v - (K.starProjection v + W.starProjection v) =
        (v - K.starProjection v) - W.starProjection v := by abel
    have hreg2 : v - (K.starProjection v + W.starProjection v) =
        (v - W.starProjection v) - K.starProjection v := by abel
    have t1 : ⟪a, v - (K.starProjection v + W.starProjection v)⟫ = 0 := by
      rw [hreg1, inner_sub_right, e1, e2, sub_zero]
    have t2 : ⟪b, v - (K.starProjection v + W.starProjection v)⟫ = 0 := by
      rw [hreg2, inner_sub_right, e3, e4, sub_zero]
    rw [inner_add_left, t1, t2, add_zero]

/-- The reflection `2Π_K - I` is self-adjoint. -/
theorem reflectionAbout_adjoint (K : Submodule ℝ H) :
    (SpanProgram.reflectionAbout K)† = SpanProgram.reflectionAbout K := by
  have h : IsSelfAdjoint (SpanProgram.reflectionAbout K) := by
    unfold SpanProgram.reflectionAbout
    have h2 : IsSelfAdjoint (2 : ℝ) := IsSelfAdjoint.all 2
    exact (h2.smul (isSelfAdjoint_starProjection K)).sub (IsSelfAdjoint.one (H →L[ℝ] H))
  exact ContinuousLinearMap.isSelfAdjoint_iff'.mp h

/-- **Section 3 (p. 13).**  For orthogonal `K ⟂ W` the reflection about `K ⊔ W` factors as
the reflection about `K` followed by `I - 2Π_W`; this is the operator content of
`2Π_{K ⊕ W} - I = (2Π_K - I)(I - 2Π_W)` used for `T = ker A ⊕ span{w₀}`. -/
theorem reflectionAbout_sup_of_isOrtho {K W : Submodule ℝ H} (h : K ⟂ W) :
    SpanProgram.reflectionAbout (K ⊔ W) =
      (SpanProgram.reflectionAbout K).comp (1 - 2 • W.starProjection : H →L[ℝ] H) := by
  have hzero : K.starProjection.comp W.starProjection = 0 :=
    Submodule.IsOrtho.starProjection_comp_starProjection h
  refine ContinuousLinearMap.ext fun v => ?_
  have hK0 : K.starProjection (W.starProjection v) = 0 := by
    simpa using congrArg (fun f : H →L[ℝ] H => f v) hzero
  have hsup : (K ⊔ W).starProjection v = K.starProjection v + W.starProjection v :=
    starProjection_sup_of_isOrtho h v
  simp [SpanProgram.reflectionAbout, hsup, hK0, two_smul ℝ]
  abel

/-- **Section 3 (p. 13).**  The adjoint of the walk unitary
`U = (2Π_{ker A} - I)(2Π_{H(x)} - I)` is the same product in the opposite order, both
factors being self-adjoint. -/
theorem U_adjoint {q n : ℕ} {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : SpanProgram q n H V) (x : Fin n → Fin q) :
    (P.U x)† = SpanProgram.reflectionAbout (P.Hx x) ∘L
      SpanProgram.reflectionAbout (LinearMap.ker (P.A : H →ₗ[ℝ] V)) := by
  simp only [SpanProgram.U, ContinuousLinearMap.adjoint_comp, reflectionAbout_adjoint]

/-- **Section 3 (p. 13).**  Under the source's assumption `w₀ ∈ (ker A)ᗮ`, so that
`ker A` and `span{w₀}` are orthogonal and `T = ker A ⊕ span{w₀}`, the second walk unitary
satisfies `U′(P,x) = U(P,x)† (I - 2|w₀⟩⟨w₀|)`.  The projector `|w₀⟩⟨w₀|` is represented by
`(Submodule.span ℝ {w0}).starProjection`, which is the Dirac projector for a unit vector
`w0`.  The unit hypothesis of the source's normalisation is kept in the statement but is
not needed for the operator identity itself; it is written `_hunit` for that reason. -/
theorem Uprime_eq_adjoint_comp {q n : ℕ} {H V : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (P : SpanProgram q n H V) (x : Fin n → Fin q) (w0 : H)
    (hker : w0 ∈ (LinearMap.ker (P.A : H →ₗ[ℝ] V))ᗮ) (_hunit : ‖w0‖ = 1) :
    P.Uprime x w0 =
      (P.U x)†.comp (1 - 2 • (Submodule.span ℝ {w0}).starProjection : H →L[ℝ] H) := by
  have horth : LinearMap.ker (P.A : H →ₗ[ℝ] V) ⟂ Submodule.span ℝ {w0} :=
    (Submodule.le_orthogonal_orthogonal _).trans
      (Submodule.orthogonal_le (Submodule.span_le.mpr (by simpa using hker)))
  simp only [SpanProgram.Uprime, reflectionAbout_sup_of_isOrtho horth, U_adjoint,
    ContinuousLinearMap.comp_assoc]

end Qatlib.Papers.ApproxSpan15.MainResults
