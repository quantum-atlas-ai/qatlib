/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.PhysicalCkgSpectralGap
public import Qatlib.Concepts.GibbsSource.SourceForms.PhysicalCoordinates
public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceGapProjection

@[expose] public section


/-! A true parent eigenvector cannot concentrate in a band whose centered
Rayleigh floor exceeds its eigenvalue. All norms are Hilbert--Schmidt norms. -/

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open scoped BigOperators MatrixOrder ComplexOrder
open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Concepts.GibbsSource.SpectralGeom
variable {D : ℕ}

/-- Hs Inner self as real for the stated finite source data. -/
private theorem hsInner_self_as_real (X : Operator D) :
    hsInner X X = ((hsInner X X).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using hsInner_self_re X

/-- Hs Inner cauchy sq for the stated finite source data. -/
private theorem hsInner_cauchy_sq (X Y : Operator D) :
    Complex.normSq (hsInner X Y) ≤ (hsInner X X).re * (hsInner Y Y).re := by
  let x : EuclideanSpace ℂ (Fin D × Fin D) := WithLp.toLp 2 (sourceVector X)
  let y : EuclideanSpace ℂ (Fin D × Fin D) := WithLp.toLp 2 (sourceVector Y)
  have hi : inner ℂ x y = hsInner X Y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    exact sourceVector_hsInner X Y
  have hx : ‖x‖^2 = (hsInner X X).re := by
    rw [PiLp.norm_sq_eq_of_L2,hsInner_self_re_sum]
    simp [x,sourceVector,Fintype.sum_prod_type,Complex.normSq_eq_norm_sq]
  have hy : ‖y‖^2 = (hsInner Y Y).re := by
    rw [PiLp.norm_sq_eq_of_L2,hsInner_self_re_sum]
    simp [y,sourceVector,Fintype.sum_prod_type,Complex.normSq_eq_norm_sq]
  have h := sq_le_sq₀ (norm_nonneg (inner ℂ x y)) (mul_nonneg (norm_nonneg x) (norm_nonneg y))
  rw [← hi, Complex.normSq_eq_norm_sq]
  calc
    _ ≤ (‖x‖*‖y‖)^2 := h.mpr (norm_inner_le_norm x y)
    _ = _ := by rw [mul_pow,hx,hy]

/-- Source Projection pair for the stated finite source data. -/
private theorem sourceProjection_pair
    (Q : Operator D →ₗ[ℂ] Operator D) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X) = Q X) (X Y : Operator D) :
    hsInner (Q X) (Q Y) = hsInner (Q X) Y := by
  simpa only [hQQ] using (hQ (Q X) Y).symm

/-- Source Projection pythagoras for the stated finite source data. -/
private theorem sourceProjection_pythagoras
    (Q : Operator D →ₗ[ℂ] Operator D) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X) = Q X) (X : Operator D) :
    (hsInner (X-Q X) (X-Q X)).re =
      (hsInner X X).re - (hsInner (Q X) (Q X)).re := by
  have h1 : hsInner (Q X) X = hsInner (Q X) (Q X) := (sourceProjection_pair Q hQ hQQ X X).symm
  have h2 : hsInner X (Q X) = hsInner (Q X) (Q X) := (hQ X X).symm.trans h1
  rw [hsInner_sub_left,hsInner_sub_right,hsInner_sub_right,h1,h2]
  simp only [Complex.sub_re]
  ring

/-- Centering a compressed input against the compressed Gibbs root is an
orthogonal projection onto the centered compressed space. The last inequality
pays exactly the retained Gibbs mass, even for a complex input. -/
theorem source_centered_projection
    (Q : Operator D →ₗ[ℂ] Operator D) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X) = Q X) (G X : Operator D)
    (hG : (hsInner G G).re=1) (hX : (hsInner X X).re=1)
    (horth : hsInner G X=0) (hp : 0 < (hsInner (Q G) (Q G)).re) :
    let p := (hsInner (Q G) (Q G)).re
    let Y := Q X - (hsInner (Q G) (Q X) / (p : ℂ)) • Q G
    Q Y=Y ∧ hsInner G Y=0 ∧ hsInner X Y=hsInner Y Y ∧
      p * (1-(hsInner Y Y).re) ≤ (hsInner (X-Q X) (X-Q X)).re := by
  dsimp only
  let p := (hsInner (Q G) (Q G)).re
  let a := hsInner (Q G) (Q X)
  let c := a/(p:ℂ)
  let Y := Q X-c • Q G
  have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hfix : Q Y=Y := by simp only [Y,map_sub,map_smul,hQQ]
  have hrg : hsInner (Q G) (Q G)=(p:ℂ) := hsInner_self_as_real _
  have hrY : hsInner (Q G) Y=0 := by
    dsimp [Y,c]
    rw [hsInner_sub_right,hsInner_smul_right,hrg]
    change a-(a/(p:ℂ))*(p:ℂ)=0
    rw [div_mul_cancel₀ _ hp0,sub_self]
  have hGY : hsInner G Y=0 := by
    rw [← hfix,←hQ G Y,hrY]
  have hYr : hsInner Y (Q G)=0 := by
    rw [hsInner_conj_swap,hrY,star_zero]
  have hYX : hsInner Y X=hsInner Y Y := by
    calc
      hsInner Y X = hsInner Y (Q X) := by rw [←hQ Y X,hfix]
      _ = hsInner Y Y := by
        dsimp only [Y]
        rw [hsInner_sub_right,hsInner_smul_right,hYr,mul_zero,sub_zero]
  have hXY : hsInner X Y=hsInner Y Y := by
    rw [hsInner_conj_swap,hYX,hsInner_self_as_real]
    simp
  have hnY : (hsInner Y Y).re = (hsInner (Q X) (Q X)).re-Complex.normSq a/p := by
    have he := fullVariance_eq_projected_normSq (sourceVector (Q G)) (sourceVector (Q X))
      (by
        intro hz
        have hz' : Q G=0 := by
          have h := congrArg sourceUnvector hz
          simpa using! h
        have : p=0 := by simp [p,hz',hsInner]
        exact hp.ne' this)
    have hv : fullGibbsComplement (sourceVector (Q G)) *ᵥ sourceVector (Q X)=sourceVector Y := by
      rw [fullGibbsComplement_mulVec,sourceVector_hsInner]
      simp only [fullNormSq,sourceVector_hsInner]
      rfl
    rw [hv] at he
    simpa only [fullVariance,fullNormSq,sourceVector_hsInner,p,a] using he.symm
  have hae : hsInner (G-Q G) (X-Q X) = -a := by
    have h1 : hsInner (Q G) X=a := (sourceProjection_pair Q hQ hQQ G X).symm
    have h2 : hsInner G (Q X)=a := (hQ G X).symm.trans h1
    rw [hsInner_sub_left,hsInner_sub_right,hsInner_sub_right,horth,h1,h2]
    change 0-a-(a-a)= -a
    ring
  have hcs := hsInner_cauchy_sq (G-Q G) (X-Q X)
  rw [hae,Complex.normSq_neg,sourceProjection_pythagoras Q hQ hQQ G,hG] at hcs
  have hpy := sourceProjection_pythagoras Q hQ hQQ X
  rw [hX] at hpy
  refine ⟨hfix,hGY,hXY,?_⟩
  change p*(1-(hsInner Y Y).re) ≤ _
  rw [hnY]
  have hd : p*(Complex.normSq a/p)=Complex.normSq a := mul_div_cancel₀ _ hp.ne'
  nlinarith

/-- A unit eigenvector's squared distance from any orthogonal projection
with Rayleigh floor α is at least (α-lam)/(B-lam), under the absolute cap B.
This uses the eigenvector equation and is sharper than the general
energy-seminorm triangle estimate. -/
theorem source_eigenvector_projection_le
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (X Y : Operator D) {B α lam : ℝ}
    (hX : (hsInner X X).re=1) (heig : L X=(lam:ℂ) • X)
    (hXY : hsInner X Y=hsInner Y Y) (hαB : α≤B) (hlamα : lam<α)
    (hcap : ∀ Z, (hsInner Z (L Z)).re ≤ B*(hsInner Z Z).re)
    (hband : α*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re) :
    (α-lam)/(B-lam) ≤ 1-(hsInner Y Y).re := by
  let t := (hsInner Y Y).re
  have ht : 0≤t := hsInner_self_nonneg Y
  have hB : 0<B-lam := by linarith
  by_cases ht0 : t=0
  · change _ ≤ 1-t
    rw [ht0,sub_zero]
    apply (div_le_iff₀ hB).mpr
    linarith
  have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hXX : hsInner X X=(1:ℂ) := by rw [hsInner_self_as_real,hX]; rfl
  have hYY : hsInner Y Y=(t:ℂ) := hsInner_self_as_real Y
  have hXY' : hsInner X Y=(t:ℂ) := hXY.trans hYY
  have hYX' : hsInner Y X=(t:ℂ) := by rw [hsInner_conj_swap,hXY']; simp
  have hXL : hsInner X (L Y)=((lam*t:ℝ):ℂ) := by
    rw [←hL,heig,hsInner_smul_left,hXY']
    simp
  have hn : (hsInner (Y-(t:ℂ) • X) (Y-(t:ℂ) • X)).re=t-t^2 := by
    rw [hsInner_sub_smul_self,hXX,hXY',hYY]
    simp only [star_ofReal,mul_one,←Complex.ofReal_mul,Complex.sub_re,Complex.add_re,Complex.ofReal_re]
    ring
  have he : (hsInner (Y-(t:ℂ) • X) (L (Y-(t:ℂ) • X))).re =
      (hsInner Y (L Y)).re-lam*t^2 := by
    simp only [map_sub,map_smul,hsInner_sub_left,hsInner_sub_right,
      hsInner_smul_left,hsInner_smul_right,hXL,heig,hXX,hYX',star_ofReal,
      mul_one,←Complex.ofReal_mul,Complex.sub_re,Complex.ofReal_re]
    ring_nf
    simp
  have hc := hcap (Y-(t:ℂ) • X)
  rw [hn,he] at hc
  have hb : (B-lam)*t ≤ B-α := by
    apply (mul_le_mul_iff_left₀ htpos).mp
    change α*t ≤ _ at hband
    nlinarith
  apply (div_le_iff₀ hB).mpr
  change α-lam ≤ (1-t)*(B-lam)
  nlinarith

/-- Leakage for an actual unit eigenvector and an actual source-space
orthogonal projection, with the band Gibbs mass derived from that projection. -/
theorem source_eigenvector_centered_leakage
    (L Q : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X)=Q X) (G X : Operator D) {B α lam : ℝ}
    (hG : (hsInner G G).re=1) (hX : (hsInner X X).re=1)
    (horth : hsInner G X=0) (hp : 0<(hsInner (Q G) (Q G)).re)
    (heig : L X=(lam:ℂ) • X) (hαB : α≤B) (hlamα : lam<α)
    (hcap : ∀ Z, (hsInner Z (L Z)).re ≤ B*(hsInner Z Z).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      α*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re) :
    (hsInner (Q G) (Q G)).re*((α-lam)/(B-lam)) ≤
      (hsInner (X-Q X) (X-Q X)).re := by
  obtain ⟨hf,ho,hxy,hpdist⟩ := source_centered_projection Q hQ hQQ G X hG hX horth hp
  have he := source_eigenvector_projection_le L hL X _ hX heig hxy hαB hlamα hcap (hband _ hf ho)
  exact (mul_le_mul_of_nonneg_left he hp.le).trans hpdist


/-- Two-leg compression by the specified physical projector. -/
noncomputable def sourceCompression (P : Operator D) : Operator D →ₗ[ℂ] Operator D where
  toFun X := P*X*P
  map_add' X Y := by simp only [Matrix.mul_add,Matrix.add_mul]
  map_smul' c X := by simp only [Matrix.mul_smul,Matrix.smul_mul]; rfl

/-- Source Compression self Adjoint for the stated finite source data. -/
theorem sourceCompression_selfAdjoint (P : Operator D) (hP : P.IsHermitian) :
    SourceSelfAdjoint (sourceCompression P) := by
  intro X Y
  change hsInner (P*X*P) Y=hsInner X (P*Y*P)
  rw [hsInner_mulRight,hsInner_mulLeft,hP.eq,Matrix.mul_assoc]

/-- Source Compression idempotent for the stated finite source data. -/
theorem sourceCompression_idempotent (P : Operator D) (hP : P*P=P) (X : Operator D) :
    sourceCompression P (sourceCompression P X)=sourceCompression P X := by
  change P*(P*X*P)*P=P*X*P
  calc
    _ = (P*P)*X*(P*P) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hP]

/-- A spectral band's projected Gibbs-root norm is its thermal probability.
Only commutation with the square root is needed for this exact identity. -/
theorem sourceCompression_gibbsMass (ρ P : Operator D) (hρ : 0≤ρ)
    (hP : P.IsHermitian) (hPP : P*P=P)
    (hcomm : P*CFC.sqrt ρ=CFC.sqrt ρ*P) :
    (hsInner (sourceCompression P (CFC.sqrt ρ))
      (sourceCompression P (CFC.sqrt ρ))).re=(Matrix.trace (ρ*P)).re := by
  have hg : (CFC.sqrt ρ)ᴴ=CFC.sqrt ρ :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
  have hcut : sourceCompression P (CFC.sqrt ρ)=CFC.sqrt ρ*P := by
    change P*CFC.sqrt ρ*P=CFC.sqrt ρ*P
    rw [hcomm,Matrix.mul_assoc,hPP]
  rw [hcut,hsInner,Matrix.conjTranspose_mul,hP.eq,hg]
  have hm : (P*CFC.sqrt ρ)*(CFC.sqrt ρ*P)=P*ρ*P := by
    rw [Matrix.mul_assoc,←Matrix.mul_assoc (CFC.sqrt ρ),CFC.sqrt_mul_sqrt_self ρ hρ]
    exact (Matrix.mul_assoc ..).symm
  rw [hm,Matrix.trace_mul_cycle,hPP,Matrix.trace_mul_comm]

/-- Herm Gibbs Root norm Sq for the stated finite source data. -/
private theorem hermGibbsRoot_normSq [NeZero D]
    (H : Operator D) (hH : H.IsHermitian) (β : ℝ) :
    (hsInner (CFC.sqrt (hermGibbs H hH β)) (CFC.sqrt (hermGibbs H hH β))).re=1 := by
  have hg : (CFC.sqrt (hermGibbs H hH β))ᴴ=CFC.sqrt (hermGibbs H hH β) :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
  have htr : Matrix.trace (hermGibbs H hH β)=1 := (hermGibbs_isDensityOperator H hH β).2
  rw [hsInner,hg,CFC.sqrt_mul_sqrt_self _ (hermGibbs_posDef H hH β).posSemidef.nonneg,htr]
  rfl

/-- The orthogonal projector onto a selected set of actual energy eigenvectors.
Choosing all indices in an energy interval gives the two-leg band used above. -/
noncomputable def hermEnergyBand (H : Operator D) (hH : H.IsHermitian)
    (S : Finset (Fin D)) : Operator D :=
  hermPhysicalCoordinates H hH (Matrix.diagonal fun i => if i∈S then 1 else 0)

/-- Compression retains exactly the matrix entries with both energy indices in S. -/
theorem hermEnergyBand_compression_entry (H : Operator D) (hH : H.IsHermitian)
    (S : Finset (Fin D)) (X : Operator D) (i j : Fin D) :
    hermEnergyCoordinates H hH (hermEnergyBand H hH S*X*hermEnergyBand H hH S) i j =
      if i∈S ∧ j∈S then hermEnergyCoordinates H hH X i j else 0 := by
  simp only [hermEnergyCoordinates_mul,hermEnergyBand,hermEnergy_physical_inverse,
    Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases hi : i∈S <;> by_cases hj : j∈S <;> simp [hi,hj]

/-- Herm Energy Band is Hermitian for the stated finite source data. -/
theorem hermEnergyBand_isHermitian (H : Operator D) (hH : H.IsHermitian)
    (S : Finset (Fin D)) : (hermEnergyBand H hH S).IsHermitian := by
  unfold hermEnergyBand hermPhysicalCoordinates
  rw [Matrix.IsHermitian]
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.diagonal_conjTranspose]
  simp [Pi.star_def,Matrix.mul_assoc]

/-- Herm Energy Band idempotent for the stated finite source data. -/
theorem hermEnergyBand_idempotent (H : Operator D) (hH : H.IsHermitian)
    (S : Finset (Fin D)) : hermEnergyBand H hH S*hermEnergyBand H hH S=hermEnergyBand H hH S := by
  unfold hermEnergyBand hermPhysicalCoordinates
  rw [conj_mul_conj,hermUnitary_star_mul,Matrix.mul_one,Matrix.diagonal_mul_diagonal]
  congr 2
  ext i j
  by_cases hij : i=j
  · subst j; by_cases hi : i∈S <;> simp [hi]
  · simp [hij]

/-- Herm Energy Band commute gibbs Root for the stated finite source data. -/
theorem hermEnergyBand_commute_gibbsRoot (H : Operator D) (hH : H.IsHermitian)
    (β : ℝ) (S : Finset (Fin D)) :
    hermEnergyBand H hH S*CFC.sqrt (hermGibbs H hH β)=
      CFC.sqrt (hermGibbs H hH β)*hermEnergyBand H hH S := by
  have hr : CFC.sqrt (hermGibbs H hH β)=hermPhysicalCoordinates H hH (CFC.sqrt (gibbsDiag hH.eigenvalues β)) :=
    CFC_sqrt_conj _ _ (hermUnitary_star_mul H hH) (gibbsDiag_nonneg _ _)
  rw [hr]
  unfold hermEnergyBand hermPhysicalCoordinates
  rw [conj_mul_conj,conj_mul_conj,hermUnitary_star_mul,Matrix.mul_one,Matrix.mul_one]
  have hg : CFC.sqrt (gibbsDiag hH.eigenvalues β) =
      Matrix.diagonal (fun i => (Real.sqrt (Real.exp (-(β*hH.eigenvalues i)) /
        ∑ j,Real.exp (-(β*hH.eigenvalues j))) : ℂ)) := by
    apply CFC_sqrt_diagonal
    intro i
    positivity
  rw [hg,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  congr 2
  ext i j
  simp [Matrix.diagonal_apply,mul_comm]

/-- Herm Energy Band gibbs Mass for the stated finite source data. -/
theorem hermEnergyBand_gibbsMass (H : Operator D) (hH : H.IsHermitian)
    (β : ℝ) (S : Finset (Fin D)) :
    (Matrix.trace (hermGibbs H hH β*hermEnergyBand H hH S)).re =
      ∑ i ∈ S, Real.exp (-(β*hH.eigenvalues i)) /
        ∑ j,Real.exp (-(β*hH.eigenvalues j)) := by
  unfold hermGibbs hermEnergyBand hermPhysicalCoordinates
  rw [conj_mul_conj,hermUnitary_star_mul,Matrix.mul_one,
    Matrix.trace_mul_cycle,hermUnitary_star_mul,Matrix.one_mul,
    gibbsDiag,Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal,Complex.re_sum]
  simp only [mul_one,mul_zero,apply_ite,Complex.ofReal_re,Complex.zero_re]
  simp

/-- Herm Energy Band gibbs Mass pos for the stated finite source data. -/
theorem hermEnergyBand_gibbsMass_pos [NeZero D]
    (H : Operator D) (hH : H.IsHermitian) (β : ℝ)
    (S : Finset (Fin D)) (hS : S.Nonempty) :
    0<(Matrix.trace (hermGibbs H hH β*hermEnergyBand H hH S)).re := by
  rw [hermEnergyBand_gibbsMass]
  have hz : 0<∑ j,Real.exp (-(β*hH.eigenvalues j)) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  exact Finset.sum_pos (fun _ _ => div_pos (Real.exp_pos _) hz) hS



end Qatlib.Concepts.GibbsSource.SpectralGeom
