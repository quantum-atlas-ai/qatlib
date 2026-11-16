/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.LowSpectralBandLeakage

@[expose] public section


/-! Sharp trace leakage of an entire positive low spectral subspace.
The trace is computed from the actual source matrix and its complete basis. -/

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Qatlib.Concepts.GibbsSource.SourceForms
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.SpectralGeom
variable {D : ℕ}

/-- Source hs Inner as real for the stated finite source data. -/
private theorem source_hsInner_as_real (X : Operator D) :
    hsInner X X = ((hsInner X X).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using hsInner_self_re X

/-- Source projection pair for the stated finite source data. -/
theorem source_projection_pair
    (Q : Operator D →ₗ[ℂ] Operator D) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X)=Q X) (X Y : Operator D) :
    hsInner (Q X) (Q Y)=hsInner (Q X) Y := by
  simpa only [hQQ] using (hQ (Q X) Y).symm

/-- Source projection pythagoras for the stated finite source data. -/
theorem source_projection_pythagoras
    (Q : Operator D →ₗ[ℂ] Operator D) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X)=Q X) (X : Operator D) :
    (hsInner (X-Q X) (X-Q X)).re =
      (hsInner X X).re-(hsInner (Q X) (Q X)).re := by
  have h1 := (source_projection_pair Q hQ hQQ X X).symm
  have h2 := (hQ X X).symm.trans h1
  rw [hsInner_sub_left, hsInner_sub_right, hsInner_sub_right, h1, h2]
  simp only [Complex.sub_re]
  ring

/-- Source projection norm le for the stated finite source data. -/
theorem source_projection_norm_le
    (Q : Operator D →ₗ[ℂ] Operator D) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X)=Q X) (X : Operator D) :
    (hsInner (Q X) (Q X)).re≤(hsInner X X).re := by
  have h := hsInner_self_nonneg (X-Q X)
  rw [source_projection_pythagoras Q hQ hQQ] at h
  linarith

/-- Real trace on the complete source supermatrix. -/
noncomputable def sourceTrace (T : Operator D →ₗ[ℂ] Operator D) : ℝ :=
  (Matrix.trace (sourceSuperMatrix T)).re

/-- Source Eigenoperator expansion for the stated finite source data. -/
theorem sourceEigenoperator_expansion
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (X : Operator D) :
    X = ∑ i, hsInner (sourceEigenoperator L hL i) X • sourceEigenoperator L hL i := by
  ext a b
  have h := source_hsInner_eq_sum_eigenoperators L hL (matUnit a b 1) X
  simpa only [hsInner_matUnit_left, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, mul_comm] using h

/-- Source Trace eq sum eigenoperators for the stated finite source data. -/
theorem sourceTrace_eq_sum_eigenoperators
    (L T : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) :
    sourceTrace T = ∑ i, (hsInner (sourceEigenoperator L hL i)
      (T (sourceEigenoperator L hL i))).re := by
  classical
  have he : Matrix.trace (sourceSuperMatrix T) =
      ∑ i, hsInner (sourceEigenoperator L hL i) (T (sourceEigenoperator L hL i)) := by
    change (∑ a : Fin D × Fin D, T (matUnit a.1 a.2 1) a.1 a.2) = _
    conv_lhs =>
      arg 2
      ext a
      rw [sourceEigenoperator_expansion L hL (matUnit a.1 a.2 1)]
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [hsInner_matUnit_right]
    exact (sourceVector_hsInner (sourceEigenoperator L hL i)
      (T (sourceEigenoperator L hL i)))
  unfold sourceTrace
  rw [he]
  exact map_sum complexReAddMonoidHom _ _

/-- Source Trace sub for the stated finite source data. -/
theorem sourceTrace_sub (A B : Operator D →ₗ[ℂ] Operator D) :
    sourceTrace (A-B)=sourceTrace A-sourceTrace B := by
  simp [sourceTrace, sourceSuperMatrix, Matrix.trace, Finset.sum_sub_distrib]

/-- Source Trace real smul for the stated finite source data. -/
theorem sourceTrace_real_smul (c : ℝ) (A : Operator D →ₗ[ℂ] Operator D) :
    sourceTrace ((c:ℂ) • A)=c*sourceTrace A := by
  change (∑ a : Fin D × Fin D, (c:ℂ) * A (matUnit a.1 a.2 1) a.1 a.2).re =
    c * (∑ a : Fin D × Fin D, A (matUnit a.1 a.2 1) a.1 a.2).re
  rw [← Finset.mul_sum, ofReal_mul_re]

/-- Source Trace nonneg for the stated finite source data. -/
theorem sourceTrace_nonneg
    (A : Operator D →ₗ[ℂ] Operator D)
    (hA : ∀ X, 0≤(hsInner X (A X)).re) : 0≤sourceTrace A := by
  change 0 ≤ (∑ a : Fin D × Fin D, A (matUnit a.1 a.2 1) a.1 a.2).re
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro i hi
  simpa only [hsInner_matUnit_left] using hA (matUnit i.1 i.2 1)

/-- Source Trace positive cap for the stated finite source data. -/
theorem sourceTrace_positive_cap
    (A : Operator D →ₗ[ℂ] Operator D) (hA : SourceSelfAdjoint A)
    (hpos : ∀ X, 0≤(hsInner X (A X)).re) (X : Operator D) :
    (hsInner X (A X)).re≤sourceTrace A*(hsInner X X).re := by
  classical
  have ht : sourceTrace A=∑ i, sourceEigenvalues A hA i := by
    rw [sourceTrace_eq_sum_eigenoperators A A hA]
    apply Finset.sum_congr rfl
    intro i hi
    rw [sourceEigenoperator_apply, hsInner_smul_right, ofReal_mul_re,
      sourceEigenoperator_normSq, mul_one]
  have hb (i : Fin D × Fin D) : sourceEigenvalues A hA i≤sourceTrace A := by
    rw [ht]
    exact Finset.single_le_sum (fun j hj => sourceEigenvalues_nonneg A hA hpos j)
      (Finset.mem_univ i)
  rw [source_energy_eq_sum_eigenvalues A hA, source_hsNormSq_eq_sum_coefficients A hA,
    Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hb i)
    (Complex.normSq_nonneg _))


/-- Unnormalised rank-one operator in the source Hilbert space. -/
noncomputable def sourceRankOne (W : Operator D) : Operator D →ₗ[ℂ] Operator D where
  toFun X := hsInner W X • W
  map_add' X Y := by simp only [hsInner, Matrix.mul_add, Matrix.trace_add, add_smul]
  map_smul' c X := by simp only [hsInner_smul_right, smul_smul]; rfl

/-- Source Rank One self Adjoint for the stated finite source data. -/
theorem sourceRankOne_selfAdjoint (W : Operator D) :
    SourceSelfAdjoint (sourceRankOne W) := by
  intro X Y
  change hsInner (hsInner W X • W) Y = hsInner X (hsInner W Y • W)
  rw [hsInner_smul_left, hsInner_smul_right, ← hsInner_conj_swap X W]
  ring

/-- Source Trace rank One for the stated finite source data. -/
theorem sourceTrace_rankOne (W : Operator D) :
    sourceTrace (sourceRankOne W)=(hsInner W W).re := by
  change (∑ a : Fin D × Fin D, (hsInner W (matUnit a.1 a.2 1) • W) a.1 a.2).re = _
  simp only [hsInner_matUnit_right, Matrix.smul_apply, smul_eq_mul]
  exact congrArg Complex.re (sourceVector_hsInner W W)

/-- Projection onto the band after removing its actual compressed Gibbs root. -/
noncomputable def sourceCenteredProjection
    (Q : Operator D →ₗ[ℂ] Operator D) (G : Operator D) : Operator D →ₗ[ℂ] Operator D :=
  Q - ((((hsInner (Q G) (Q G)).re)⁻¹ : ℝ) : ℂ) • sourceRankOne (Q G)

/-- Source Centered Projection apply for the stated finite source data. -/
theorem sourceCenteredProjection_apply
    (Q : Operator D →ₗ[ℂ] Operator D) (G X : Operator D) :
    sourceCenteredProjection Q G X =
      Q X-(hsInner (Q G) X / ((hsInner (Q G) (Q G)).re : ℂ)) • Q G := by
  change Q X - ((((hsInner (Q G) (Q G)).re)⁻¹ : ℝ) : ℂ) •
    (hsInner (Q G) X • Q G) = _
  simp only [div_eq_mul_inv, smul_smul, Complex.ofReal_inv, mul_comm]

/-- Source Centered Projection self Adjoint for the stated finite source data. -/
theorem sourceCenteredProjection_selfAdjoint
    (Q : Operator D →ₗ[ℂ] Operator D) (hQ : SourceSelfAdjoint Q) (G : Operator D) :
    SourceSelfAdjoint (sourceCenteredProjection Q G) := by
  intro X Y
  simp only [sourceCenteredProjection, LinearMap.sub_apply, LinearMap.smul_apply,
    hsInner_sub_left, hsInner_sub_right, hsInner_smul_left, hsInner_smul_right,
    star_ofReal]
  rw [hQ X Y, sourceRankOne_selfAdjoint (Q G) X Y]

/-- Source Centered Projection properties for the stated finite source data. -/
theorem sourceCenteredProjection_properties
    (Q : Operator D →ₗ[ℂ] Operator D) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X)=Q X) (G : Operator D)
    (hp : 0<(hsInner (Q G) (Q G)).re) (X : Operator D) :
    Q (sourceCenteredProjection Q G X)=sourceCenteredProjection Q G X ∧
    hsInner G (sourceCenteredProjection Q G X)=0 ∧
    hsInner X (sourceCenteredProjection Q G X)=
      hsInner (sourceCenteredProjection Q G X) (sourceCenteredProjection Q G X) := by
  let Y := sourceCenteredProjection Q G X
  have hp0 : ((hsInner (Q G) (Q G)).re : ℂ)≠0 := by exact_mod_cast hp.ne'
  have hf : Q Y=Y := by
    dsimp only [Y]
    rw [sourceCenteredProjection_apply]
    simp only [map_sub, map_smul, hQQ]
  have hw : hsInner (Q G) Y=0 := by
    dsimp only [Y]
    rw [sourceCenteredProjection_apply, hsInner_sub_right, hsInner_smul_right,
      source_projection_pair Q hQ hQQ, source_hsInner_as_real (Q G), Complex.ofReal_re,
      div_mul_cancel₀ _ hp0, sub_self]
  have hg : hsInner G Y=0 := by rw [← hf, ← hQ, hw]
  have hyw : hsInner Y (Q G)=0 := by rw [hsInner_conj_swap, hw, star_zero]
  have hyx : hsInner Y X=hsInner Y Y := by
    calc
      hsInner Y X=hsInner Y (Q X) := by rw [← hQ, hf]
      _=hsInner Y Y := by
        conv_rhs => arg 2; rw [show Y=sourceCenteredProjection Q G X from rfl,
          sourceCenteredProjection_apply]
        rw [hsInner_sub_right, hsInner_smul_right, hyw, mul_zero, sub_zero]
  refine ⟨hf, hg, ?_⟩
  rw [hsInner_conj_swap X Y, hyx, source_hsInner_as_real]
  simp

/-- Source Centered Projection idempotent for the stated finite source data. -/
theorem sourceCenteredProjection_idempotent
    (Q : Operator D →ₗ[ℂ] Operator D) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X)=Q X) (G : Operator D)
    (hp : 0<(hsInner (Q G) (Q G)).re) (X : Operator D) :
    sourceCenteredProjection Q G (sourceCenteredProjection Q G X)=
      sourceCenteredProjection Q G X := by
  obtain ⟨hf, hg, hxy⟩ := sourceCenteredProjection_properties Q hQ hQQ G hp X
  rw [sourceCenteredProjection_apply, hf, hQ, hf, hg, zero_div, zero_smul, sub_zero]

/-- Source Trace centered for the stated finite source data. -/
theorem sourceTrace_centered
    (Q : Operator D →ₗ[ℂ] Operator D) (G : Operator D)
    (hp : 0<(hsInner (Q G) (Q G)).re) :
    sourceTrace (sourceCenteredProjection Q G)=sourceTrace Q-1 := by
  rw [sourceCenteredProjection, sourceTrace_sub, sourceTrace_real_smul,
    sourceTrace_rankOne, inv_mul_cancel₀ hp.ne']

/-- Source Centered Projection norm Sq for the stated finite source data. -/
theorem sourceCenteredProjection_normSq
    (Q : Operator D →ₗ[ℂ] Operator D) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X)=Q X) (G : Operator D)
    (hp : 0<(hsInner (Q G) (Q G)).re) (X : Operator D) :
    (hsInner (sourceCenteredProjection Q G X) (sourceCenteredProjection Q G X)).re =
      (hsInner (Q X) (Q X)).re -
        Complex.normSq (hsInner (Q G) X)/(hsInner (Q G) (Q G)).re := by
  let p := (hsInner (Q G) (Q G)).re
  have he := fullVariance_eq_projected_normSq (sourceVector (Q G)) (sourceVector (Q X))
    (by
      intro hz
      have hz' : Q G=0 := by
        have h := congrArg sourceUnvector hz
        simpa using! h
      have : p=0 := by simp [p, hz', hsInner]
      exact hp.ne' this)
  have hv : fullGibbsComplement (sourceVector (Q G)) *ᵥ sourceVector (Q X)=
      sourceVector (sourceCenteredProjection Q G X) := by
    rw [fullGibbsComplement_mulVec, sourceVector_hsInner]
    simp only [fullNormSq, sourceVector_hsInner]
    rw [source_projection_pair Q hQ hQQ, sourceCenteredProjection_apply]
    rfl
  rw [hv] at he
  simpa only [fullVariance, fullNormSq, sourceVector_hsInner,
    source_projection_pair Q hQ hQQ] using he.symm

/-- The mass-sensitive angle inequality holds homogeneously on the kernel complement. -/
theorem sourceCenteredProjection_mass_angle
    (Q : Operator D →ₗ[ℂ] Operator D) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X)=Q X) (G X : Operator D)
    (hG : (hsInner G G).re=1) (horth : hsInner G X=0)
    (hp : 0<(hsInner (Q G) (Q G)).re) :
    (hsInner (Q G) (Q G)).re *
      ((hsInner X X).re-
        (hsInner (sourceCenteredProjection Q G X) (sourceCenteredProjection Q G X)).re) ≤
      (hsInner (X-Q X) (X-Q X)).re := by
  have ha : hsInner (G-Q G) (X-Q X) = -hsInner (Q G) X := by
    rw [hsInner_sub_left, hsInner_sub_right, hsInner_sub_right,
      horth, ← hQ, source_projection_pair Q hQ hQQ]
    ring
  have hc := source_hsInner_cauchy_sq (G-Q G) (X-Q X)
  rw [ha, Complex.normSq_neg, source_projection_pythagoras Q hQ hQQ G, hG] at hc
  rw [sourceCenteredProjection_normSq Q hQ hQQ G hp]
  have hd := mul_div_cancel₀ (Complex.normSq (hsInner (Q G) X)) hp.ne'
  have hpy := source_projection_pythagoras Q hQ hQQ X
  nlinarith


/-- Source Super Matrix comp for the stated finite source data. -/
theorem sourceSuperMatrix_comp
    (A B : Operator D →ₗ[ℂ] Operator D) :
    sourceSuperMatrix (A.comp B)=sourceSuperMatrix A*sourceSuperMatrix B := by
  ext a b
  exact (congrFun (sourceSuperMatrix_mulVec A (B (matUnit b.1 b.2 1))) a).symm

/-- Source Trace comp comm for the stated finite source data. -/
theorem sourceTrace_comp_comm (A B : Operator D →ₗ[ℂ] Operator D) :
    sourceTrace (A.comp B)=sourceTrace (B.comp A) := by
  unfold sourceTrace
  rw [sourceSuperMatrix_comp, sourceSuperMatrix_comp, Matrix.trace_mul_comm]

/-- Source Trace le for the stated finite source data. -/
theorem sourceTrace_le (A B : Operator D →ₗ[ℂ] Operator D)
    (h : ∀ X, (hsInner X (A X)).re≤(hsInner X (B X)).re) :
    sourceTrace A≤sourceTrace B := by
  change (∑ a : Fin D × Fin D, A (matUnit a.1 a.2 1) a.1 a.2).re ≤
    (∑ a : Fin D × Fin D, B (matUnit a.1 a.2 1) a.1 a.2).re
  rw [Complex.re_sum, Complex.re_sum]
  exact Finset.sum_le_sum (fun i hi => by
    simpa only [hsInner_matUnit_left] using h (matUnit i.1 i.2 1))

/-- Source projection compression energy for the stated finite source data. -/
theorem source_projection_compression_energy
    (R V : Operator D →ₗ[ℂ] Operator D) (hR : SourceSelfAdjoint R)
    (hV : SourceSelfAdjoint V) (hVV : ∀ X, V (V X)=V X)
    (X : Operator D) :
    (hsInner X ((R.comp (V.comp R)) X)).re =
      (hsInner (V (R X)) (V (R X))).re := by
  change (hsInner X (R (V (R X)))).re=_
  rw [← hR, hV (R X) (V (R X)), hVV]

/-- Source projection compression self Adjoint for the stated finite source data. -/
theorem source_projection_compression_selfAdjoint
    (R V : Operator D →ₗ[ℂ] Operator D) (hR : SourceSelfAdjoint R)
    (hV : SourceSelfAdjoint V) :
    SourceSelfAdjoint (R.comp (V.comp R)) := by
  intro X Y
  change hsInner (R (V (R X))) Y=hsInner X (R (V (R Y)))
  rw [hR, hV, hR]

/-- Source Trace projection compression for the stated finite source data. -/
theorem sourceTrace_projection_compression
    (R V : Operator D →ₗ[ℂ] Operator D)
    (hRR : ∀ X, R (R X)=R X) :
    sourceTrace (R.comp (V.comp R))=sourceTrace (R.comp V) := by
  rw [sourceTrace_comp_comm]
  have he : (V.comp R).comp R=V.comp R := by ext X; simp only [LinearMap.comp_apply, hRR]
  rw [he, sourceTrace_comp_comm]

/-- Source Trace comp rank One for the stated finite source data. -/
theorem sourceTrace_comp_rankOne
    (R : Operator D →ₗ[ℂ] Operator D) (W : Operator D) :
    sourceTrace (R.comp (sourceRankOne W))=(hsInner W (R W)).re := by
  change (∑ a : Fin D × Fin D, R (hsInner W (matUnit a.1 a.2 1) • W) a.1 a.2).re=_
  simp only [map_smul, hsInner_matUnit_right, Matrix.smul_apply, smul_eq_mul]
  exact congrArg Complex.re (sourceVector_hsInner W (R W))

/-- Source Trace comp centered for the stated finite source data. -/
theorem sourceTrace_comp_centered
    (R Q : Operator D →ₗ[ℂ] Operator D) (hR : SourceSelfAdjoint R)
    (hRR : ∀ X, R (R X)=R X) (G : Operator D) :
    sourceTrace (R.comp (sourceCenteredProjection Q G)) =
      sourceTrace (R.comp Q) -
        (hsInner (R (Q G)) (R (Q G))).re/(hsInner (Q G) (Q G)).re := by
  rw [sourceCenteredProjection, LinearMap.comp_sub, LinearMap.comp_smul,
    sourceTrace_sub, sourceTrace_real_smul, sourceTrace_comp_rankOne,
    ← hR, ← source_projection_pair R hR hRR]
  ring

/-- Adjoint duality of the two projection angles, including the zero-vector case. -/
theorem source_projection_angle_dual
    (R V : Operator D →ₗ[ℂ] Operator D)
    (hR : SourceSelfAdjoint R) (hV : SourceSelfAdjoint V)
    (hRR : ∀ X, R (R X)=R X) (hVV : ∀ X, V (V X)=V X) {c : ℝ}
    (hc : 0≤c) (hangle : ∀ X, (hsInner (V (R X)) (V (R X))).re ≤
      c*(hsInner (R X) (R X)).re) (X : Operator D) :
    (hsInner (R (V X)) (R (V X))).re ≤ c*(hsInner (V X) (V X)).re := by
  let t := (hsInner (R (V X)) (R (V X))).re
  let u := (hsInner (V X) (V X)).re
  have ht : 0≤t := hsInner_self_nonneg _
  have hu : 0≤u := hsInner_self_nonneg _
  have hi : hsInner (V X) (V (R (V X)))=(t:ℂ) := by
    rw [← hV, hVV, ← hR, ← source_projection_pair R hR hRR,
      source_hsInner_as_real]
  have hcs := source_hsInner_cauchy_sq (V X) (V (R (V X)))
  rw [hi, Complex.normSq_ofReal] at hcs
  have hm := mul_le_mul_of_nonneg_left (hangle (V X)) hu
  by_cases ht0 : t=0
  · change t≤c*u
    rw [ht0]
    exact mul_nonneg hc hu
  have htp : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  change t≤c*u
  apply (mul_le_mul_iff_left₀ htp).mp
  nlinarith


/-- Source projection angle trace le for the stated finite source data. -/
theorem source_projection_angle_trace_le
    (R V : Operator D →ₗ[ℂ] Operator D)
    (hR : SourceSelfAdjoint R) (hV : SourceSelfAdjoint V)
    (hRR : ∀ X, R (R X)=R X) (hVV : ∀ X, V (V X)=V X) {c : ℝ}
    (hangle : ∀ X, (hsInner (R (V X)) (R (V X))).re ≤
      c*(hsInner (V X) (V X)).re) :
    sourceTrace (R.comp V)≤c*sourceTrace V := by
  have h := sourceTrace_le (V.comp (R.comp V)) ((c:ℂ) • V) (fun X => by
    rw [source_projection_compression_energy V R hV hR hRR]
    change _≤(hsInner X ((c:ℂ) • V X)).re
    rw [hsInner_smul_right, ofReal_mul_re, ← hV X X,
      ← source_projection_pair V hV hVV X X]
    exact hangle X)
  rw [sourceTrace_projection_compression V R hVV, sourceTrace_comp_comm V R,
    sourceTrace_real_smul] at h
  exact h

/-- Source projection kernel mass for the stated finite source data. -/
theorem source_projection_kernel_mass
    (R Q : Operator D →ₗ[ℂ] Operator D)
    (hR : SourceSelfAdjoint R) (hQ : SourceSelfAdjoint Q)
    (hRR : ∀ X, R (R X)=R X) (hQQ : ∀ X, Q (Q X)=Q X)
    (G : Operator D) (hG : (hsInner G G).re=1) (hRG : R G=0) :
    (hsInner (R (Q G)) (R (Q G))).re ≤
      (hsInner (Q G) (Q G)).re*(1-(hsInner (Q G) (Q G)).re) := by
  let p := (hsInner (Q G) (Q G)).re
  have hgw : hsInner G (Q G)=(p:ℂ) := by
    rw [← hQ, ← source_projection_pair Q hQ hQQ, source_hsInner_as_real]
  have hg : hsInner G G=(1:ℂ) := by rw [source_hsInner_as_real, hG]; rfl
  have hn : (hsInner (Q G-(p:ℂ) • G) (Q G-(p:ℂ) • G)).re=p*(1-p) := by
    rw [hsInner_sub_smul_self, hgw, hg]
    simp only [star_ofReal, mul_one, ← Complex.ofReal_mul, Complex.sub_re,
      Complex.add_re, Complex.ofReal_re]
    change p-p*p-p*p+p*p=p*(1-p)
    ring
  have he : R (Q G-(p:ℂ) • G)=R (Q G) := by
    rw [map_sub, map_smul, hRG, smul_zero, sub_zero]
  have hc := source_projection_norm_le R hR hRR (Q G-(p:ℂ) • G)
  rw [he, hn] at hc
  exact hc

/-- The two sharp trace constraints follow from an angle between actual
orthogonal projections. The same interface accepts certified residual angles. -/
theorem source_projection_sharp_trace_leakage
    (R Q : Operator D →ₗ[ℂ] Operator D)
    (hR : SourceSelfAdjoint R) (hQ : SourceSelfAdjoint Q)
    (hRR : ∀ X, R (R X)=R X) (hQQ : ∀ X, Q (Q X)=Q X)
    (G : Operator D) (hG : (hsInner G G).re=1) (hRG : R G=0)
    {c : ℝ} (hc : 0≤c) (hc1 : c≤1)
    (hp : 0<(hsInner (Q G) (Q G)).re)
    (hangle : ∀ X,
      (hsInner (R (sourceCenteredProjection Q G X))
        (R (sourceCenteredProjection Q G X))).re ≤
      c*(hsInner (sourceCenteredProjection Q G X)
        (sourceCenteredProjection Q G X)).re) :
    max ((sourceTrace R-1+(hsInner (Q G) (Q G)).re)*(1-c))
      (sourceTrace R-(sourceTrace Q-1)-1+(hsInner (Q G) (Q G)).re+
        (sourceTrace Q-1)*(1-c)) ≤
      sourceTrace R-sourceTrace (R.comp Q) := by
  let V := sourceCenteredProjection Q G
  let p := (hsInner (Q G) (Q G)).re
  let v := R (Q G)
  let q := (hsInner v v).re
  have hV : SourceSelfAdjoint V := sourceCenteredProjection_selfAdjoint Q hQ G
  have hVV : ∀ X, V (V X)=V X := sourceCenteredProjection_idempotent Q hQ hQQ G hp
  have hdual := source_projection_angle_dual V R hV hR hVV hRR hc hangle
  have htrace := source_projection_angle_trace_le R V hR hV hRR hVV hangle
  have hcenter := sourceTrace_comp_centered R Q hR hRR G
  have hdim := sourceTrace_centered Q G hp
  have hmass := source_projection_kernel_mass R Q hR hQ hRR hQQ G hG hRG
  have hp1 : p≤1 := by
    have h := source_projection_norm_le Q hQ hQQ G
    rw [hG] at h
    exact h
  have hq : 0≤q := hsInner_self_nonneg v
  have hqmass : q/p≤1-p := (div_le_iff₀ hp).mpr (by simpa [q, v, p, mul_comm] using hmass)
  have hsecond : sourceTrace R-(sourceTrace Q-1)-1+p+
      (sourceTrace Q-1)*(1-c) ≤ sourceTrace R-sourceTrace (R.comp Q) := by
    change sourceTrace (R.comp V)=sourceTrace (R.comp Q)-q/p at hcenter
    change sourceTrace V=sourceTrace Q-1 at hdim
    rw [hdim] at htrace
    nlinarith
  -- The positive angle deficit controls the single direction R(QG).
  let A := (c:ℂ) • R-R.comp (V.comp R)
  have hA : SourceSelfAdjoint A := by
    intro X Y
    simp only [A, LinearMap.sub_apply, LinearMap.smul_apply,
      hsInner_sub_left, hsInner_sub_right, hsInner_smul_left, hsInner_smul_right,
      star_ofReal]
    rw [hR X Y, source_projection_compression_selfAdjoint R V hR hV X Y]
  have henergy (X : Operator D) : (hsInner X (A X)).re =
      c*(hsInner (R X) (R X)).re-(hsInner (V (R X)) (V (R X))).re := by
    change (hsInner X ((c:ℂ) • R X-(R.comp (V.comp R)) X)).re=_
    rw [hsInner_sub_right, hsInner_smul_right, Complex.sub_re, ofReal_mul_re,
      source_projection_compression_energy R V hR hV hVV,
      ← hR X X, ← source_projection_pair R hR hRR X X]
  have hpos : ∀ X, 0≤(hsInner X (A X)).re := by
    intro X
    rw [henergy]
    exact sub_nonneg.mpr (hdual X)
  have hAtr : sourceTrace A=c*sourceTrace R-sourceTrace (R.comp V) := by
    dsimp only [A]
    rw [sourceTrace_sub, sourceTrace_real_smul,
      sourceTrace_projection_compression R V hRR]
  have hfirst : (sourceTrace R-1+p)*(1-c)≤sourceTrace R-sourceTrace (R.comp Q) := by
    have htrpos := sourceTrace_nonneg A hpos
    have hRv : R v=v := hRR (Q G)
    have hgv : hsInner G v=0 := by
      dsimp only [v]
      rw [← hR, hRG]
      simp [hsInner]
    have hvcoeff : hsInner (Q G) v=(q:ℂ) := by
      dsimp only [v]
      rw [← hR, ← source_projection_pair R hR hRR, source_hsInner_as_real]
    have hqv := sourceCenteredProjection_normSq Q hQ hQQ G hp v
    rw [hvcoeff, Complex.normSq_ofReal] at hqv
    have hangleV := hdual v
    rw [hRv] at hangleV
    have hgeom := sourceCenteredProjection_mass_angle Q hQ hQQ G v hG hgv hp
    rw [source_projection_pythagoras Q hQ hQQ v] at hgeom
    have hAcap := sourceTrace_positive_cap A hA hpos v
    rw [henergy, hRv] at hAcap
    change c*q-(hsInner (V v) (V v)).re≤sourceTrace A*q at hAcap
    by_cases hq0 : q=0
    · change sourceTrace (R.comp V)=sourceTrace (R.comp Q)-q/p at hcenter
      rw [hq0, zero_div, sub_zero] at hcenter
      rw [hcenter] at hAtr
      have hd : 0≤(1-p)*(1-c) := mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hc1)
      nlinarith
    have hqpos : 0<q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hdeficit : q/p-(1-p)*(1-c)≤sourceTrace A := by
      apply (mul_le_mul_iff_right₀ hqpos).mp
      have hm := mul_le_mul_of_nonneg_left hangleV hp.le
      change p*(q-(hsInner (V v) (V v)).re)≤
        q-(hsInner (Q v) (Q v)).re at hgeom
      change (hsInner (V v) (V v)).re=
        (hsInner (Q v) (Q v)).re-q*q/p at hqv
      change p*(hsInner (V v) (V v)).re≤p*(c*q) at hm
      have hd : q*q/p=(q/p)*q := by ring
      rw [hd] at hqv
      nlinarith only [hm, hgeom, hqv, hAcap]
    change sourceTrace (R.comp V)=sourceTrace (R.comp Q)-q/p at hcenter
    nlinarith
  exact max_le hfirst hsecond



/-- Source Spectral Cut eigenoperator for the stated finite source data. -/
theorem sourceSpectralCut_eigenoperator
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) (i : Fin D × Fin D) :
    sourceSpectralCut L hL S (sourceEigenoperator L hL i) =
      if i∈S then sourceEigenoperator L hL i else 0 := by
  classical
  change (∑ j ∈ S, hsInner (sourceEigenoperator L hL j)
    (sourceEigenoperator L hL i) • sourceEigenoperator L hL j) = _
  simp [sourceEigenoperator_inner, ite_smul]

/-- Source Trace spectral Cut for the stated finite source data. -/
theorem sourceTrace_spectralCut
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) :
    sourceTrace (sourceSpectralCut L hL S)=(S.card:ℝ) := by
  classical
  rw [sourceTrace_eq_sum_eigenoperators L _ hL]
  have hz (X : Operator D) : hsInner X 0=0 := by simp [hsInner]
  simp [sourceSpectralCut_eigenoperator, apply_ite, sourceEigenoperator_inner, hz]

/-- Source Spectral Cut leakage sum for the stated finite source data. -/
theorem sourceSpectralCut_leakage_sum
    (L Q : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hQ : SourceSelfAdjoint Q) (hQQ : ∀ X, Q (Q X)=Q X)
    (S : Finset (Fin D × Fin D)) :
    sourceTrace (sourceSpectralCut L hL S) -
      sourceTrace ((sourceSpectralCut L hL S).comp Q) =
      ∑ i ∈ S,
        (hsInner (sourceEigenoperator L hL i-Q (sourceEigenoperator L hL i))
          (sourceEigenoperator L hL i-Q (sourceEigenoperator L hL i))).re := by
  classical
  have hp (X : Operator D) : hsInner X (Q X)=hsInner (Q X) (Q X) := by
    rw [← hQ, source_projection_pair Q hQ hQQ]
  have hz (X : Operator D) : hsInner X 0=0 := by simp [hsInner]
  have hi (i : Fin D × Fin D) :
      (hsInner (sourceEigenoperator L hL i)
        ((Q.comp (sourceSpectralCut L hL S)) (sourceEigenoperator L hL i))).re =
      if i∈S then
        (hsInner (Q (sourceEigenoperator L hL i)) (Q (sourceEigenoperator L hL i))).re
      else 0 := by
    by_cases hmem : i∈S
    · simp [sourceSpectralCut_eigenoperator, hmem, hp]
    · simp [sourceSpectralCut_eigenoperator, hmem, hz]
  rw [sourceTrace_spectralCut, sourceTrace_comp_comm,
    sourceTrace_eq_sum_eigenoperators L _ hL]
  simp_rw [hi]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp_rw [source_projection_pythagoras Q hQ hQQ, sourceEigenoperator_normSq]
  rw [Finset.sum_sub_distrib]
  simp

/-- Source Positive Low Projection kernel for the stated finite source data. -/
theorem sourcePositiveLowProjection_kernel
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (G : Operator D) (hG : L G=0) (lam : ℝ) :
    sourcePositiveLowProjection L hL lam G=0 := by
  classical
  change (∑ i ∈ sourcePositiveLowModes L hL lam,
    hsInner (sourceEigenoperator L hL i) G • sourceEigenoperator L hL i)=0
  apply Finset.sum_eq_zero
  intro i hi
  have hp : 0<sourceEigenvalues L hL i := (Finset.mem_filter.mp hi).2.1
  rw [hsInner_conj_swap,
    hsInner_kernel_eigenvector_eq_zero L hL G _ hG
      (Complex.ofReal_ne_zero.mpr hp.ne') (sourceEigenoperator_apply L hL i),
    star_zero, zero_smul]

/-- The exact positive low projector supplies the centered band angle. -/
theorem sourcePositiveLowProjection_centered_angle
    (L Q : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hQ : SourceSelfAdjoint Q) (hQQ : ∀ X, Q (Q X)=Q X)
    (G : Operator D) {B α lam : ℝ}
    (hp : 0<(hsInner (Q G) (Q G)).re) (hαB : α≤B) (hgap : lam<α)
    (hcap : ∀ Z, (hsInner Z (L Z)).re≤B*(hsInner Z Z).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      α*(hsInner Y Y).re≤(hsInner Y (L Y)).re) (X : Operator D) :
    (hsInner (sourcePositiveLowProjection L hL lam (sourceCenteredProjection Q G X))
      (sourcePositiveLowProjection L hL lam (sourceCenteredProjection Q G X))).re ≤
      ((B-α)/(B-lam)) *
        (hsInner (sourceCenteredProjection Q G X) (sourceCenteredProjection Q G X)).re := by
  let Y := sourceCenteredProjection Q G X
  obtain ⟨hf, ho, hxy⟩ := sourceCenteredProjection_properties Q hQ hQQ G hp X
  have hb := hband Y hf ho
  have hs := sourcePositiveLowProjection_split_cap L hL (lam := lam) hcap Y
  have hB : 0<B-lam := by linarith
  have he : ((B-α)/(B-lam))*(hsInner Y Y).re =
      ((B-α)*(hsInner Y Y).re)/(B-lam) := by ring
  change _≤((B-α)/(B-lam))*(hsInner Y Y).re
  rw [he]
  apply (le_div_iff₀ hB).mpr
  nlinarith

/-- Both sharp budgets for the actual complete positive low spectral space.
The right side is the leakage summed over its actual orthonormal modes. -/
theorem source_positiveLowProjection_sharp_trace_leakage
    (L Q : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hQ : SourceSelfAdjoint Q) (hQQ : ∀ X, Q (Q X)=Q X)
    (G : Operator D) {B α lam : ℝ}
    (hG : (hsInner G G).re=1) (hLG : L G=0)
    (hp : 0<(hsInner (Q G) (Q G)).re) (hαB : α≤B) (hgap : lam<α)
    (hcap : ∀ Z, (hsInner Z (L Z)).re≤B*(hsInner Z Z).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      α*(hsInner Y Y).re≤(hsInner Y (L Y)).re) :
    max ((((sourcePositiveLowModes L hL lam).card:ℝ)-1+(hsInner (Q G) (Q G)).re)*
        ((α-lam)/(B-lam)))
      (((sourcePositiveLowModes L hL lam).card:ℝ)-(sourceTrace Q-1)-1+
        (hsInner (Q G) (Q G)).re+(sourceTrace Q-1)*((α-lam)/(B-lam))) ≤
      ∑ i ∈ sourcePositiveLowModes L hL lam,
        (hsInner (sourceEigenoperator L hL i-Q (sourceEigenoperator L hL i))
          (sourceEigenoperator L hL i-Q (sourceEigenoperator L hL i))).re := by
  have hB : 0<B-lam := by linarith
  have hc : 0≤(B-α)/(B-lam) := div_nonneg (sub_nonneg.mpr hαB) hB.le
  have hc1 : (B-α)/(B-lam)≤1 := (div_le_iff₀ hB).mpr (by linarith)
  have hd : 1-(B-α)/(B-lam)=(α-lam)/(B-lam) := by field_simp; ring
  have h := source_projection_sharp_trace_leakage
    (sourcePositiveLowProjection L hL lam) Q
    (sourceSpectralCut_selfAdjoint L hL _) hQ
    (sourceSpectralCut_idempotent L hL _) hQQ G hG
    (sourcePositiveLowProjection_kernel L hL G hLG lam) hc hc1 hp
    (sourcePositiveLowProjection_centered_angle L Q hL hQ hQQ G hp hαB hgap hcap hband)
  unfold sourcePositiveLowProjection at h
  rw [sourceSpectralCut_leakage_sum L Q hL hQ hQQ,
    sourceTrace_spectralCut, hd] at h
  exact h

/-- Source Trace compression for the stated finite source data. -/
theorem sourceTrace_compression (P : Operator D) :
    sourceTrace (sourceCompression P)=(Matrix.trace P*Matrix.trace P).re := by
  have he (a b : Fin D) : (P*matUnit a b 1*P) a b=P a a*P b b := by
    simp [Matrix.mul_apply, matUnit_apply, ite_and]
  change (∑ a : Fin D × Fin D, (P*matUnit a.1 a.2 1*P) a.1 a.2).re=_
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Herm Energy Band trace for the stated finite source data. -/
theorem hermEnergyBand_trace (H : Operator D) (hH : H.IsHermitian)
    (S : Finset (Fin D)) :
    Matrix.trace (hermEnergyBand H hH S)=(S.card:ℂ) := by
  classical
  unfold hermEnergyBand hermPhysicalCoordinates
  rw [Matrix.trace_mul_cycle, hermUnitary_star_mul, Matrix.one_mul]
  simp [Matrix.trace]

/-- Source Trace energy Band for the stated finite source data. -/
theorem sourceTrace_energyBand (H : Operator D) (hH : H.IsHermitian)
    (S : Finset (Fin D)) :
    sourceTrace (sourceCompression (hermEnergyBand H hH S))=(S.card:ℝ)^2 := by
  rw [sourceTrace_compression, hermEnergyBand_trace]
  simp [Complex.mul_re, pow_two]



/-- Source Trace sum for the stated finite source data. -/
theorem sourceTrace_sum {ι : Type*} [Fintype ι]
    (T : ι → (Operator D →ₗ[ℂ] Operator D)) :
    sourceTrace (∑ i, T i)=∑ i, sourceTrace (T i) := by
  change (∑ a : Fin D × Fin D, (∑ i, T i) (matUnit a.1 a.2 1) a.1 a.2).re =
    ∑ i, (∑ a : Fin D × Fin D, T i (matUnit a.1 a.2 1) a.1 a.2).re
  simp only [LinearMap.sum_apply, Matrix.sum_apply, Complex.re_sum]
  rw [Finset.sum_comm]

/-- Projection generated by a supplied orthonormal source family. -/
noncomputable def sourceFamilyProjection {r : ℕ} (X : Fin r → Operator D) :
    Operator D →ₗ[ℂ] Operator D := ∑ i, sourceRankOne (X i)

/-- Source Family Projection apply for the stated finite source data. -/
theorem sourceFamilyProjection_apply {r : ℕ} (X : Fin r → Operator D) (Y : Operator D) :
    sourceFamilyProjection X Y=∑ i, hsInner (X i) Y • X i := by
  simp only [sourceFamilyProjection, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- Source Family Projection self Adjoint for the stated finite source data. -/
theorem sourceFamilyProjection_selfAdjoint {r : ℕ} (X : Fin r → Operator D) :
    SourceSelfAdjoint (sourceFamilyProjection X) := by
  intro Y Z
  simp only [sourceFamilyProjection_apply, hsInner_sum_left, hsInner_sum_right,
    hsInner_smul_left, hsInner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hsInner_conj_swap]
  ring

/-- Source Family Projection family for the stated finite source data. -/
theorem sourceFamilyProjection_family {r : ℕ} (X : Fin r → Operator D)
    (horth : ∀ i j, hsInner (X i) (X j)=if i=j then 1 else 0) (i : Fin r) :
    sourceFamilyProjection X (X i)=X i := by
  simp [sourceFamilyProjection_apply, horth, ite_smul]

/-- Source Family Projection idempotent for the stated finite source data. -/
theorem sourceFamilyProjection_idempotent {r : ℕ} (X : Fin r → Operator D)
    (horth : ∀ i j, hsInner (X i) (X j)=if i=j then 1 else 0) (Y : Operator D) :
    sourceFamilyProjection X (sourceFamilyProjection X Y)=sourceFamilyProjection X Y := by
  conv_lhs => arg 2; rw [sourceFamilyProjection_apply]
  rw [map_sum, sourceFamilyProjection_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, sourceFamilyProjection_family X horth]

/-- Source Trace family Projection for the stated finite source data. -/
theorem sourceTrace_familyProjection {r : ℕ} (X : Fin r → Operator D)
    (horth : ∀ i j, hsInner (X i) (X j)=if i=j then 1 else 0) :
    sourceTrace (sourceFamilyProjection X)=(r:ℝ) := by
  rw [sourceFamilyProjection, sourceTrace_sum]
  simp [sourceTrace_rankOne, horth]

/-- Source Family Projection leakage sum for the stated finite source data. -/
theorem sourceFamilyProjection_leakage_sum {r : ℕ} (X : Fin r → Operator D)
    (horth : ∀ i j, hsInner (X i) (X j)=if i=j then 1 else 0)
    (Q : Operator D →ₗ[ℂ] Operator D) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ Y, Q (Q Y)=Q Y) :
    sourceTrace (sourceFamilyProjection X)-sourceTrace ((sourceFamilyProjection X).comp Q) =
      ∑ i, (hsInner (X i-Q (X i)) (X i-Q (X i))).re := by
  have hp (Y : Operator D) : hsInner Y (Q Y)=hsInner (Q Y) (Q Y) := by
    rw [← hQ, source_projection_pair Q hQ hQQ]
  have ht : sourceTrace ((sourceFamilyProjection X).comp Q) =
      ∑ i, (hsInner (Q (X i)) (Q (X i))).re := by
    rw [sourceTrace_comp_comm]
    have he : Q.comp (sourceFamilyProjection X)=∑ i, Q.comp (sourceRankOne (X i)) := by
      ext Y a b
      simp only [sourceFamilyProjection, LinearMap.comp_apply, LinearMap.sum_apply,
        map_sum, Matrix.sum_apply]
    rw [he, sourceTrace_sum]
    simp only [sourceTrace_comp_rankOne, hp]
  rw [sourceTrace_familyProjection X horth, ht]
  have hn (i : Fin r) : (hsInner (X i) (X i)).re=1 := by simp [horth]
  simp_rw [source_projection_pythagoras Q hQ hQQ, hn]
  rw [Finset.sum_sub_distrib]
  simp

/-- Every orthonormal family in the actual positive low space obeys the sharp
budget, even after arbitrary unitary mixing of its low modes. -/
theorem source_positiveLowFamily_sharp_trace_leakage {r : ℕ}
    (L Q : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hQ : SourceSelfAdjoint Q) (hQQ : ∀ Y, Q (Q Y)=Q Y)
    (G : Operator D) (X : Fin r → Operator D) {B α lam : ℝ}
    (hG : (hsInner G G).re=1) (hLG : L G=0)
    (horth : ∀ i j, hsInner (X i) (X j)=if i=j then 1 else 0)
    (hlow : ∀ i, sourcePositiveLowProjection L hL lam (X i)=X i)
    (hp : 0<(hsInner (Q G) (Q G)).re) (hαB : α≤B) (hgap : lam<α)
    (hcap : ∀ Z, (hsInner Z (L Z)).re≤B*(hsInner Z Z).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      α*(hsInner Y Y).re≤(hsInner Y (L Y)).re) :
    max (((r:ℝ)-1+(hsInner (Q G) (Q G)).re)*((α-lam)/(B-lam)))
      ((r:ℝ)-(sourceTrace Q-1)-1+(hsInner (Q G) (Q G)).re+
        (sourceTrace Q-1)*((α-lam)/(B-lam))) ≤
      ∑ i, (hsInner (X i-Q (X i)) (X i-Q (X i))).re := by
  let F := sourceFamilyProjection X
  let R := sourcePositiveLowProjection L hL lam
  have hF : SourceSelfAdjoint F := sourceFamilyProjection_selfAdjoint X
  have hFF : ∀ Y, F (F Y)=F Y := sourceFamilyProjection_idempotent X horth
  have hR : SourceSelfAdjoint R := sourceSpectralCut_selfAdjoint L hL _
  have hFR (Y : Operator D) : F (R Y)=F Y := by
    simp only [F, sourceFamilyProjection_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hR, hlow]
  have hFG : F G=0 := by
    rw [← hFR G, sourcePositiveLowProjection_kernel L hL G hLG lam, map_zero]
  have hB : 0<B-lam := by linarith
  have hc : 0≤(B-α)/(B-lam) := div_nonneg (sub_nonneg.mpr hαB) hB.le
  have hc1 : (B-α)/(B-lam)≤1 := (div_le_iff₀ hB).mpr (by linarith)
  have hd : 1-(B-α)/(B-lam)=(α-lam)/(B-lam) := by field_simp; ring
  have hangle (Y : Operator D) :
      (hsInner (F (sourceCenteredProjection Q G Y)) (F (sourceCenteredProjection Q G Y))).re ≤
      ((B-α)/(B-lam)) *
        (hsInner (sourceCenteredProjection Q G Y) (sourceCenteredProjection Q G Y)).re := by
    rw [← hFR (sourceCenteredProjection Q G Y)]
    exact (source_projection_norm_le F hF hFF _).trans
      (sourcePositiveLowProjection_centered_angle L Q hL hQ hQQ G hp hαB hgap hcap hband Y)
  have h := source_projection_sharp_trace_leakage F Q hF hQ hFF hQQ G hG hFG hc hc1 hp hangle
  change max _ _≤sourceTrace (sourceFamilyProjection X)-
    sourceTrace ((sourceFamilyProjection X).comp Q) at h
  rw [sourceFamilyProjection_leakage_sum X horth Q hQ hQQ] at h
  change max (((sourceTrace (sourceFamilyProjection X))-1+(hsInner (Q G) (Q G)).re)*
    (1-(B-α)/(B-lam))) _≤_ at h
  rw [sourceTrace_familyProjection X horth, hd] at h
  exact h

/-- The rational six-mode budget used by the two-qubit interval certificate.
Its matrix cap, centered floor, thermal mass and actual mode count remain explicit. -/
theorem source_positiveLow_sixMode_budget
    (L Q : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hQ : SourceSelfAdjoint Q) (hQQ : ∀ X, Q (Q X)=Q X)
    (G : Operator D) {s : ℝ} (hs : 0<s)
    (hG : (hsInner G G).re=1) (hLG : L G=0)
    (hmass : (119:ℝ)/1000<(hsInner (Q G) (Q G)).re)
    (hdim : sourceTrace Q=4)
    (hcount : (sourcePositiveLowModes L hL (4*s)).card=6)
    (hcap : ∀ Z, (hsInner Z (L Z)).re≤(7*s)*(hsInner Z Z).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      (6*s)*(hsInner Y Y).re≤(hsInner Y (L Y)).re) :
    (4119:ℝ)/1000 <
      ∑ i ∈ sourcePositiveLowModes L hL (4*s),
        (hsInner (sourceEigenoperator L hL i-Q (sourceEigenoperator L hL i))
          (sourceEigenoperator L hL i-Q (sourceEigenoperator L hL i))).re := by
  have hp : 0<(hsInner (Q G) (Q G)).re := by linarith
  have h := source_positiveLowProjection_sharp_trace_leakage L Q hL hQ hQQ G hG hLG hp
    (show 6*s≤7*s by linarith) (show 4*s<6*s by linarith) hcap hband
  have hd : (6*s-4*s)/(7*s-4*s)=(2:ℝ)/3 := by
    field_simp
    ring
  rw [hcount, hdim, hd] at h
  have hsecond := (le_max_right _ _).trans h
  norm_num at hsecond
  linarith


end Qatlib.Concepts.GibbsSource.SpectralGeom
