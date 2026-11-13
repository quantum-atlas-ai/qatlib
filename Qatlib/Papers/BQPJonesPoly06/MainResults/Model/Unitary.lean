/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Bridge
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Unitary maps between unit vectors

The constructions `lineToUnit` and `exists_unitary_apply_eq` extend an isometry between complex
lines to a unitary map on a finite-dimensional inner product space. Scaling a subspace by a unit
complex number preserves norms and permits a determinant correction on a one-dimensional
subspace.

The resulting `specialUnitary_sphere_transitive` supplies the unit-vector transport used in the
bridge-lemma development of [AharonovArad2011].

## Main statements

* `scaleLine_det`: the determinant of a phase change on a line is that phase.
* `specialUnitary_sphere_transitive`: special unitary transformations of a subspace of dimension
  at least two act transitively on its unit sphere.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults.Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The complex-linear map from the span of `u` to `E` sending `s` to `⟪u, s⟫ • v`. -/
noncomputable def lineMap (u v : E) : (ℂ ∙ u) →ₗ[ℂ] E where
  toFun s := (inner ℂ u (s : E)) • v
  map_add' x y := by rw [Submodule.coe_add, inner_add_right, add_smul]
  map_smul' c x := by rw [SetLike.val_smul, inner_smul_right, RingHom.id_apply, smul_smul]

/-- The linear isometry from the span of a unit vector `u` sending `u` to the unit vector `v`. -/
noncomputable def lineToUnit (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (ℂ ∙ u) →ₗᵢ[ℂ] E where
  toLinearMap := lineMap u v
  norm_map' := by
    intro s
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp s.2
    have hinner : inner ℂ u (s : E) = c := by
      rw [← hc, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
      simp
    have hnorm : ‖(s : E)‖ = ‖c‖ := by rw [← hc, norm_smul, hu, mul_one]
    change ‖inner ℂ u (s : E) • v‖ = ‖s‖
    rw [hinner, norm_smul, hv, mul_one, ← Submodule.norm_coe]
    exact hnorm.symm

/-- Any two unit vectors in a finite-dimensional complex inner product space are related by a
linear isometry equivalence. -/
theorem exists_unitary_apply_eq (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ e : E ≃ₗᵢ[ℂ] E, e u = v := by
  refine ⟨(lineToUnit u v hu hv).extend.toLinearIsometryEquiv rfl, ?_⟩
  rw [LinearIsometry.toLinearIsometryEquiv_apply]
  have hval : (lineToUnit u v hu hv)
      (⟨u, Submodule.mem_span_singleton_self u⟩ : ℂ ∙ u) = v := by
    change (inner ℂ u u) • v = v
    rw [inner_self_eq_norm_sq_to_K, hu]
    simp
  calc (lineToUnit u v hu hv).extend u
      = (lineToUnit u v hu hv).extend
          ((⟨u, Submodule.mem_span_singleton_self u⟩ : ℂ ∙ u) : E) := rfl
    _ = (lineToUnit u v hu hv) ⟨u, Submodule.mem_span_singleton_self u⟩ :=
        LinearIsometry.extend_apply _ _
    _ = v := hval

/-- The linear map multiplying the orthogonal projection onto `M` by `lam` and fixing the
orthogonal component. -/
noncomputable def scaleLine (M : Submodule ℂ E) (lam : ℂ) : E →ₗ[ℂ] E :=
  LinearMap.id + (lam - 1) • (M.starProjection : E →ₗ[ℂ] E)

/-- Expresses `scaleLine` as the sum of the scaled projection onto `M` and the unchanged
orthogonal component. -/
theorem scaleLine_apply (M : Submodule ℂ E) (lam : ℂ) (x : E) :
    scaleLine M lam x = lam • M.starProjection x + (x - M.starProjection x) := by
  have h : scaleLine M lam x = x + (lam - 1) • M.starProjection x := rfl
  rw [h, sub_smul, one_smul]
  abel

/-- The map `scaleLine M lam` fixes every vector orthogonal to `M`. -/
theorem scaleLine_eq_self_of_mem_orthogonal (M : Submodule ℂ E) (lam : ℂ) {x : E}
    (hx : x ∈ Mᗮ) : scaleLine M lam x = x := by
  have h0 : M.orthogonalProjection x = 0 :=
    (Submodule.orthogonalProjection_eq_zero_iff (K := M)).2 hx
  have h0' : M.starProjection x = 0 := by
    rw [Submodule.starProjection_apply, h0]
    simp
  rw [scaleLine_apply, h0']
  simp

/-- Scaling the component in `M` by a complex number of norm one preserves the norm. -/
theorem scaleLine_norm (M : Submodule ℂ E) {lam : ℂ} (hlam : ‖lam‖ = 1) (x : E) :
    ‖scaleLine M lam x‖ = ‖x‖ := by
  rw [scaleLine_apply]
  set p : E := M.starProjection x with hpdef
  have hpA : p ∈ M := by rw [hpdef]; exact M.starProjection_apply_mem x
  have hborth : x - p ∈ Mᗮ := by rw [hpdef]; exact M.sub_starProjection_mem_orthogonal x
  have hxdec : p + (x - p) = x := by abel
  have horth1 : inner ℂ p (x - p) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K := M) hpA hborth
  have hlpA : lam • p ∈ M := M.smul_mem lam hpA
  have horth2 : inner ℂ (lam • p) (x - p) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K := M) hlpA hborth
  have hpyth1 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (lam • p) (x - p) horth2
  have hpyth2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p (x - p) horth1
  rw [hxdec] at hpyth2
  have hnormlam : ‖lam • p‖ = ‖p‖ := by rw [norm_smul, hlam, one_mul]
  rw [hnormlam] at hpyth1
  have h2 : ‖lam • p + (x - p)‖ * ‖lam • p + (x - p)‖ = ‖x‖ * ‖x‖ := by
    rw [hpyth1, ← hpyth2]
  have h2' : ‖lam • p + (x - p)‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [pow_two, pow_two]
    exact h2
  have hres := congrArg Real.sqrt h2'
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hres

/-- The linear isometry obtained by scaling `M` by a complex number of norm one and fixing its
orthogonal complement. -/
noncomputable def scaleLineIsometry (M : Submodule ℂ E) {lam : ℂ} (hlam : ‖lam‖ = 1) :
    E →ₗᵢ[ℂ] E where
  toLinearMap := scaleLine M lam
  norm_map' := scaleLine_norm M hlam

/-- The linear isometry equivalence obtained from `scaleLineIsometry` in finite dimension. -/
noncomputable def scaleLineEquiv (M : Submodule ℂ E) {lam : ℂ} (hlam : ‖lam‖ = 1) :
    E ≃ₗᵢ[ℂ] E :=
  (scaleLineIsometry M hlam).toLinearIsometryEquiv rfl

/-- Evaluation of `scaleLineEquiv` agrees with the underlying map `scaleLine`. -/
theorem scaleLineEquiv_apply (M : Submodule ℂ E) {lam : ℂ} (hlam : ‖lam‖ = 1) (x : E) :
    scaleLineEquiv M hlam x = scaleLine M lam x := rfl

/-- Scaling a one-dimensional subspace by `lam` of norm one, while fixing its orthogonal
complement, has determinant `lam`. -/
theorem scaleLine_det (M : Submodule ℂ E) (hM : Module.finrank ℂ M = 1) {lam : ℂ}
    (hlam : ‖lam‖ = 1) :
    LinearMap.det ((scaleLineEquiv M hlam : E ≃ₗᵢ[ℂ] E) : E →ₗ[ℂ] E) = lam := by
  have hMorth : IsCompl M Mᗮ :=
    Submodule.isCompl_orthogonal_of_hasOrthogonalProjection (K := M)
  let ψ : (M × Mᗮ) ≃ₗ[ℂ] E := Submodule.prodEquivOfIsCompl M Mᗮ hMorth
  have hψ : (ψ : (M × Mᗮ) →ₗ[ℂ] E) = M.subtype.coprod Mᗮ.subtype :=
    Submodule.coe_prodEquivOfIsCompl (p := M) (q := Mᗮ) hMorth
  have hD : ((scaleLineEquiv M hlam : E ≃ₗᵢ[ℂ] E) : E →ₗ[ℂ] E)
      = (ψ : (M × Mᗮ) →ₗ[ℂ] E) ∘ₗ
        (LinearMap.prodMap (lam • LinearMap.id) (LinearMap.id : Mᗮ →ₗ[ℂ] Mᗮ)) ∘ₗ
        (ψ.symm : E →ₗ[ℂ] (M × Mᗮ)) := by
    ext x
    set y : M × Mᗮ := ψ.symm x with hy
    have hyx : (ψ : (M × Mᗮ) →ₗ[ℂ] E) y = x := by
      rw [hy]
      exact ψ.apply_symm_apply x
    have hsum : ((y.1 : M) : E) + ((y.2 : Mᗮ) : E) = x := by
      rw [← hyx, hψ]
      rfl
    have hy1 : ((y.1 : M) : E) = M.starProjection x := by
      refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := M)
        (u := x) y.1.2 ?_).symm
      intro w hw
      have hxsub : x - ((y.1 : M) : E) = ((y.2 : Mᗮ) : E) := by
        rw [← hsum]; abel
      rw [hxsub]
      exact (Submodule.mem_orthogonal' (K := M) ((y.2 : Mᗮ) : E)).1 y.2.2 w hw
    change scaleLine M lam x = (ψ : (M × Mᗮ) →ₗ[ℂ] E)
      (LinearMap.prodMap (lam • LinearMap.id) (LinearMap.id : Mᗮ →ₗ[ℂ] Mᗮ) y)
    rw [LinearMap.prodMap_apply, LinearMap.smul_apply, LinearMap.id_apply, hψ,
      LinearMap.coprod_apply]
    change scaleLine M lam x = lam • ((y.1 : M) : E) + ((y.2 : Mᗮ) : E)
    rw [scaleLine_apply, ← hy1]
    have hxsub : x - ((y.1 : M) : E) = ((y.2 : Mᗮ) : E) := by
      rw [← hsum]; abel
    rw [hxsub]
  calc LinearMap.det ((scaleLineEquiv M hlam : E ≃ₗᵢ[ℂ] E) : E →ₗ[ℂ] E)
      = LinearMap.det ((ψ : (M × Mᗮ) →ₗ[ℂ] E) ∘ₗ
          (LinearMap.prodMap (lam • LinearMap.id) (LinearMap.id : Mᗮ →ₗ[ℂ] Mᗮ)) ∘ₗ
          (ψ.symm : E →ₗ[ℂ] (M × Mᗮ))) := by rw [hD]
    _ = LinearMap.det (LinearMap.prodMap (lam • LinearMap.id)
          (LinearMap.id : Mᗮ →ₗ[ℂ] Mᗮ)) := by
          rw [LinearMap.det_conj]
    _ = lam := by
          rw [LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id, hM, pow_one]
          simp

/-- The equivalence `scaleLineEquiv M hlam` fixes every vector in the orthogonal complement of
`M`. -/
theorem scaleLineEquiv_apply_of_mem_orthogonal (M : Submodule ℂ E) {lam : ℂ}
    (hlam : ‖lam‖ = 1) {v : E} (hv : v ∈ Mᗮ) : scaleLineEquiv M hlam v = v := by
  rw [scaleLineEquiv_apply]
  exact scaleLine_eq_self_of_mem_orthogonal M lam hv

/-- The determinant of a complex linear isometry equivalence in finite dimension has norm one. -/
theorem norm_det_eq_one (f : E ≃ₗᵢ[ℂ] E) :
    ‖LinearMap.det (f : E →ₗ[ℂ] E)‖ = 1 := by
  let b := stdOrthonormalBasis ℂ E
  have hunit : (f.toMatrix b.toBasis b.toBasis) ∈
      Matrix.unitaryGroup (Fin (Module.finrank ℂ E)) ℂ :=
    LinearIsometryEquiv.toMatrix_mem_unitaryGroup f b b
  have hdet : (f.toMatrix b.toBasis b.toBasis).det ∈ unitary ℂ :=
    Matrix.det_of_mem_unitary hunit
  have h1 : star (f.toMatrix b.toBasis b.toBasis).det *
      (f.toMatrix b.toBasis b.toBasis).det = 1 := hdet.1
  have hmat : Matrix.det (f.toMatrix b.toBasis b.toBasis) =
      LinearMap.det (f : E →ₗ[ℂ] E) :=
    LinearMap.det_toMatrix b.toBasis (f : E →ₗ[ℂ] E)
  rw [← hmat]
  have h2 : (Complex.normSq (f.toMatrix b.toBasis b.toBasis).det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    simpa using h1
  have h3 : Complex.normSq (f.toMatrix b.toBasis b.toBasis).det = 1 := by
    exact_mod_cast h2
  have h4 : ‖(f.toMatrix b.toBasis b.toBasis).det‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact h3
  nlinarith [norm_nonneg (f.toMatrix b.toBasis b.toBasis).det]

set_option maxHeartbeats 800000 in

/-- In a complex subspace of dimension at least two, every unit vector has an orthogonal unit
vector [AharonovArad2011]. -/
theorem exists_unit_orthogonal {A : Submodule ℂ E} (hA : 2 ≤ Module.finrank ℂ A)
    {v : A} (hv : ‖v‖ = 1) : ∃ w : A, ‖w‖ = 1 ∧ inner ℂ w v = 0 := by
  have hvne : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    linarith
  have hline : Module.finrank ℂ (ℂ ∙ v) = 1 := finrank_span_singleton hvne
  have hsum := Submodule.finrank_add_finrank_orthogonal (K := ℂ ∙ v)
  have hKpos : 0 < Module.finrank ℂ (ℂ ∙ v)ᗮ := by omega
  obtain ⟨w, hwne⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := (ℂ ∙ v)ᗮ)).1 hKpos
  have hwne' : (w : A) ≠ 0 := by
    intro h
    exact hwne (Subtype.ext h)
  refine ⟨(‖(w : A)‖)⁻¹ • w, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hwne')]
  · have hmem : ((‖(w : A)‖)⁻¹ • w : A) ∈ (ℂ ∙ v)ᗮ := (ℂ ∙ v)ᗮ.smul_mem _ w.2
    exact (Submodule.mem_orthogonal' (K := ℂ ∙ v) ((‖(w : A)‖)⁻¹ • w)).1 hmem v
      (Submodule.mem_span_singleton_self v)

/-- Any two unit vectors in a complex subspace of dimension at least two are related by an
element of `SpecialUnitary A`, as used in [AharonovArad2011, Lemma 6.1][AharonovArad2011]. -/
theorem specialUnitary_sphere_transitive (A : Submodule ℂ E)
    (hA : 2 ≤ Module.finrank ℂ A) {u v : A} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ T ∈ SpecialUnitary A, T (u : E) = (v : E) := by
  obtain ⟨e, he⟩ := exists_unitary_apply_eq (E := A) u v hu hv
  obtain ⟨w, hw1, hw2⟩ := exists_unit_orthogonal (A := A) hA hv
  have hwne : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw1
    linarith
  let M : Submodule ℂ A := ℂ ∙ w
  have hM : Module.finrank ℂ M = 1 := finrank_span_singleton hwne
  have hvM : v ∈ Mᗮ := by
    rw [show Mᗮ = (ℂ ∙ w)ᗮ from rfl, Submodule.mem_orthogonal]
    intro a ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    rw [inner_smul_left]
    simp [hw2]
  have hdetnorm : ‖LinearMap.det (e : A →ₗ[ℂ] A)‖ = 1 := norm_det_eq_one e
  have hdetne : LinearMap.det (e : A →ₗ[ℂ] A) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdetnorm
    norm_num at hdetnorm
  set lam : ℂ := (LinearMap.det (e : A →ₗ[ℂ] A))⁻¹ with hlamdef
  have hlam : ‖lam‖ = 1 := by
    rw [hlamdef, norm_inv, hdetnorm, inv_one]
  let S : A ≃ₗᵢ[ℂ] A := scaleLineEquiv M hlam
  have hSdet : LinearMap.det (S : A →ₗ[ℂ] A) = lam := scaleLine_det M hM hlam
  have hSv : S v = v := scaleLineEquiv_apply_of_mem_orthogonal M hlam hvM
  let U : A ≃ₗᵢ[ℂ] A := e.trans S
  have hcomp : (U : A →ₗ[ℂ] A) = (S : A →ₗ[ℂ] A) ∘ₗ (e : A →ₗ[ℂ] A) := rfl
  have hUdet : LinearMap.det (U : A →ₗ[ℂ] A) = 1 := by
    rw [hcomp, LinearMap.det_comp, hSdet, hlamdef]
    exact inv_mul_cancel₀ hdetne
  have hUu : U u = v := by
    change S (e u) = v
    rw [he, hSv]
  let T : E →L[ℂ] E :=
    (Submodule.subtypeL A).comp ((U.toContinuousLinearMap).comp A.orthogonalProjection) +
      (1 - A.starProjection)
  refine ⟨T, ?_, ?_⟩
  · refine ⟨U, hUdet, fun x => ?_⟩
    simp [T, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
  · simp only [T, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      Submodule.coe_subtypeL]
    rw [show A.orthogonalProjection (u : E) = u from
        Submodule.orthogonalProjection_mem_subspace_eq_self u,
      show A.starProjection (u : E) = (u : E) from
        Submodule.starProjection_mem_subspace_eq_self u]
    simp only [sub_self, add_zero]
    change ((U u : A) : E) = (v : E)
    rw [hUu]

end Qatlib.Papers.BQPJonesPoly06.MainResults.Model
