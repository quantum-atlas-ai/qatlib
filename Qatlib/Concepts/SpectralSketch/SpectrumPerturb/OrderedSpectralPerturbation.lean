/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Algebra.Order.Rearrangement

/-!
# Ordered eigenvalue and singular value perturbation

This module develops Frobenius identities, eigenbasis transport, and rearrangement estimates for
finite complex matrices. These tools yield ordered Hermitian Weyl and Hoffman–Wielandt bounds
and rectangular singular value Weyl and Mirsky bounds, as studied in [Bhatia1997].

## Main statements

* `ordered_hermitian_weyl_and_hoffman_wielandt`: bounds ordered Hermitian eigenvalue errors in
  operator and Frobenius norms.
* `rectangular_singular_weyl_and_mirsky`: gives the corresponding singular value estimates.
* `spectralFrobenius_cross_difference`: expresses a spectral function difference through
  eigenbasis overlaps.

## References

* [Bhatia, 1997][Bhatia1997]
-/

open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix Module
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The Frobenius norm of a finite complex matrix, defined as the square root of the sum of
squared entry norms. -/
noncomputable def spectralFrobenius {O I : Type} [Fintype O] [Fintype I]
    (A : Matrix O I ℂ) : ℝ := Real.sqrt (∑ i,∑ j,Complex.normSq (A i j))
/-- The real eigenvalues of a Hermitian matrix in decreasing order, indexed by its dimension. -/
noncomputable def orderedHermitianValues {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} (hA : A.IsHermitian) : Fin (Fintype.card I)→ℝ := hA.eigenvalues₀
/-- The orthonormal eigenbasis associated with the ordered eigenvalues of a Hermitian matrix. -/
noncomputable def orderedHermitianBasis {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    OrthonormalBasis (Fin (Fintype.card I)) ℂ (EuclideanSpace ℂ I) :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace

/-- For decreasing real sequences, transport by a nonnegative matrix with unit row and column
sums gives an inner product at most the aligned inner product. -/
theorem ordered_transport_rearrangement : ∀ (n : ℕ) (a b : Fin n→ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ),
    Antitone a → Antitone b → (∀ i j,0 ≤  W i j) →
    (∀ i,∑ j,W i j=1) → (∀ j,∑ i,W i j=1) →
    (∑ i,∑ j,W i j*a i*b j) ≤ ∑ i,a i*b i := by
  intro n a b W ha hb hnonneg hrow hcol
  have hW : W ∈ doublyStochastic ℝ (Fin n) :=
    mem_doublyStochastic_iff_sum.mpr ⟨hnonneg,hrow,hcol⟩
  obtain ⟨w,hw,hw1,hwm⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hW
  have hentry (i j : Fin n) : W i j=∑ σ : Equiv.Perm (Fin n),
      w σ*(σ.permMatrix ℝ i j) := by
    simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] using!
      (congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hwm).symm
  have hperm (σ : Equiv.Perm (Fin n)) :
      (∑ i,∑ j,σ.permMatrix ℝ i j*a i*b j) ≤ ∑ i,a i*b i := by
    have he : (∑ i,∑ j,σ.permMatrix ℝ i j*a i*b j)=∑ i,a i*b (σ i) := by
      simp only [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
        Option.mem_def,Option.some.injEq,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,
        Finset.mem_univ,if_true]
    rw [he]
    exact (ha.monovary hb).sum_mul_comp_perm_le_sum_mul
  calc
    (∑ i,∑ j,W i j*a i*b j)=∑ σ : Equiv.Perm (Fin n),
        w σ*(∑ i,∑ j,σ.permMatrix ℝ i j*a i*b j) := by
      simp_rw [hentry,Finset.sum_mul]
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum,mul_assoc]
    _ ≤ ∑ σ : Equiv.Perm (Fin n),w σ*(∑ i,a i*b i) :=
      Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (hperm σ) (hw σ))
    _=∑ i,a i*b i := by rw [← Finset.sum_mul,hw1,one_mul]

/-- For nonnegative decreasing sequences, a nonnegative matrix with row and column sums at most
one gives a weighted inner product at most the aligned inner product. -/
theorem ordered_subtransport_rearrangement (n : ℕ) (a b : Fin n → ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (ha : Antitone a) (hb : Antitone b)
    (ha0 : ∀ i,0 ≤ a i) (hb0 : ∀ i,0 ≤ b i) (hW : ∀ i j,0 ≤ W i j)
    (hr : ∀ i,∑ j,W i j ≤ 1) (hc : ∀ j,∑ i,W i j ≤ 1) :
    (∑ i,∑ j,W i j*a i*b j) ≤ ∑ i,a i*b i := by
  let r : Fin n → ℝ := fun i => 1-∑ j,W i j
  let c : Fin n → ℝ := fun j => 1-∑ i,W i j
  have hr0 (i : Fin n) : 0 ≤ r i := sub_nonneg.mpr (hr i)
  have hc0 (j : Fin n) : 0 ≤ c j := sub_nonneg.mpr (hc j)
  let t := ∑ i,r i
  have ht0 : 0 ≤ t := Finset.sum_nonneg (fun i _ => hr0 i)
  have hct : (∑ j,c j)=t := by
    dsimp [c,t,r]
    simp only [Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  by_cases ht : t=0
  · have hrr (i : Fin n) : r i=0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hr0 i)).mp ht i (Finset.mem_univ _)
    have hcc (j : Fin n) : c j=0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hc0 j)).mp (hct.trans ht) j (Finset.mem_univ _)
    exact ordered_transport_rearrangement n a b W ha hb hW
      (fun i => by have h := hrr i; dsimp [r] at h; linarith)
      (fun j => by have h := hcc j; dsimp [c] at h; linarith)
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    let M : Matrix (Fin n) (Fin n) ℝ := fun i j => W i j+r i*c j/t
    have hM (i j : Fin n) : 0 ≤ M i j :=
      add_nonneg (hW i j) (div_nonneg (mul_nonneg (hr0 i) (hc0 j)) ht0)
    have hMr (i : Fin n) : (∑ j,M i j)=1 := by
      dsimp [M]
      rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.mul_sum,hct,mul_div_cancel_right₀ _ ht]
      dsimp [r]
      ring
    have hMc (j : Fin n) : (∑ i,M i j)=1 := by
      dsimp [M]
      rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_mul]
      change (∑ i,W i j)+(t*c j)/t=1
      rw [mul_div_cancel_left₀ _ ht]
      dsimp [c]
      ring
    have hle (i j : Fin n) : W i j ≤ M i j :=
      le_add_of_nonneg_right (div_nonneg (mul_nonneg (hr0 i) (hc0 j)) ht0)
    calc
      (∑ i,∑ j,W i j*a i*b j) ≤ ∑ i,∑ j,M i j*a i*b j :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hle i j) (ha0 i)) (hb0 j)))
      _ ≤ ∑ i,a i*b i := ordered_transport_rearrangement n a b M ha hb hM hMr hMc

section Frobenius
variable {O I J K : Type} [Fintype O] [Fintype I] [Fintype J] [Fintype K]

/-- The spectral Frobenius norm is nonnegative. -/
@[simp] theorem spectralFrobenius_nonneg (A : Matrix O I ℂ) : 0 ≤  spectralFrobenius A :=
  Real.sqrt_nonneg _

/-- The square of the spectral Frobenius norm is the sum of the squared norms of the matrix
entries. -/
theorem spectralFrobenius_sq (A : Matrix O I ℂ) :
    spectralFrobenius A^2=∑ i,∑ j,Complex.normSq (A i j) :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => Complex.normSq_nonneg _)))

/-- The square of the spectral Frobenius norm is the real part of the trace of `Aᴴ * A`. -/
theorem spectralFrobenius_sq_trace [DecidableEq I] (A : Matrix O I ℂ) :
    spectralFrobenius A^2=(Matrix.trace (Aᴴ*A)).re := by
  rw [spectralFrobenius_sq]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Complex.ofReal_re] using!
    congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := A j i))

/-- Left multiplication by a matrix with `Uᴴ * U = 1` preserves the spectral Frobenius norm. -/
theorem spectralFrobenius_left [DecidableEq O] [DecidableEq I] [DecidableEq J]
    (U : Matrix J O ℂ) (A : Matrix O I ℂ) (hU : Uᴴ*U=1) :
    spectralFrobenius (U*A)=spectralFrobenius A := by
  apply (sq_eq_sq₀ (spectralFrobenius_nonneg _) (spectralFrobenius_nonneg _)).mp
  rw [spectralFrobenius_sq_trace,spectralFrobenius_sq_trace,Matrix.conjTranspose_mul]
  congr 1
  rw [Matrix.mul_assoc,← Matrix.mul_assoc Uᴴ,hU,Matrix.one_mul]

/-- Right multiplication by a matrix with `V * Vᴴ = 1` preserves the spectral Frobenius norm. -/
theorem spectralFrobenius_right [DecidableEq O] [DecidableEq I] [DecidableEq J]
    (A : Matrix O I ℂ) (V : Matrix I J ℂ) (hV : V*Vᴴ=1) :
    spectralFrobenius (A*V)=spectralFrobenius A := by
  apply (sq_eq_sq₀ (spectralFrobenius_nonneg _) (spectralFrobenius_nonneg _)).mp
  rw [spectralFrobenius_sq_trace,spectralFrobenius_sq_trace,Matrix.conjTranspose_mul]
  congr 1
  rw [Matrix.mul_assoc,Matrix.trace_mul_comm Vᴴ,Matrix.mul_assoc,Matrix.mul_assoc,hV,
    Matrix.mul_one]

/-- The operator norm of a finite complex matrix is at most its spectral Frobenius norm. -/
theorem spectral_operator_norm_le_frobenius [DecidableEq I] (A : Matrix O I ℂ) :
    ‖A‖ ≤ spectralFrobenius A := by
  apply l2_opNorm_le_of_mulVec_le (spectralFrobenius_nonneg A) A
  intro v
  let u := toEuclidean_fromVec v
  change ‖toEuclidean_fromVec (A*ᵥv)‖ ≤ spectralFrobenius A*‖u‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (spectralFrobenius_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,spectralFrobenius_sq]
  have hrow (i : O) : ‖(A*ᵥv) i‖^2 ≤ (∑ j,Complex.normSq (A i j))*‖u‖^2 := by
    let r : EuclideanSpace ℂ I := WithLp.toLp 2 (fun j => star (A i j))
    have hi : (A*ᵥv) i=inner ℂ r u := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Matrix.mulVec,
        r,u,toEuclidean_fromVec,WithLp.ofLp_toLp,Pi.star_apply,star_star,mul_comm]
    have hr : ‖r‖^2=∑ j,Complex.normSq (A i j) := by
      simp only [EuclideanSpace.norm_sq_eq,r,WithLp.ofLp_toLp,norm_star,Complex.sq_norm]
    rw [hi]
    have hc : ‖inner ℂ r u‖^2 ≤ (‖r‖*‖u‖)^2 :=
      (sq_le_sq₀ (norm_nonneg (inner ℂ r u)) (mul_nonneg (norm_nonneg r) (norm_nonneg u))).mpr
      (norm_inner_le_norm r u)
    simpa only [mul_pow,hr] using! hc
  calc
    ‖toEuclidean_fromVec (A*ᵥv)‖^2=
        ∑ i,‖(A*ᵥv) i‖^2 := EuclideanSpace.norm_sq_eq _
    _ ≤ ∑ i,(∑ j,Complex.normSq (A i j))*‖u‖^2 := Finset.sum_le_sum (fun i _ => hrow i)
    _=(∑ i,∑ j,Complex.normSq (A i j))*‖u‖^2 := (Finset.sum_mul _ _ _).symm

end Frobenius

section BasisTransport
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

omit [DecidableEq I] in

/-- Multiplying a spectral diagonal matrix by its basis column matrix equals multiplying the
basis column matrix by the coefficient diagonal. -/
theorem spectralDiagonal_mul_basis (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I))
    (f : J → ℂ) : spectralDiagonal b f*basisColumns b=basisColumns b*diagonal f := by
  simp only [spectralDiagonal,Matrix.mul_assoc,basisColumns_adjoint_mul,Matrix.mul_one]

omit [DecidableEq I] in

/-- The adjoint basis column matrix intertwines a spectral diagonal matrix with its coefficient
diagonal. -/
theorem basis_adjoint_mul_spectralDiagonal (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I))
    (f : J → ℂ) : (basisColumns b)ᴴ*spectralDiagonal b f=diagonal f*(basisColumns b)ᴴ := by
  simp only [spectralDiagonal,← Matrix.mul_assoc,basisColumns_adjoint_mul,Matrix.one_mul]

/-- Changing the row and column orthonormal bases preserves the spectral Frobenius norm. -/
theorem spectralFrobenius_bases (A : Matrix I I ℂ)
    (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I))
    (c : OrthonormalBasis K ℂ (EuclideanSpace ℂ I)) :
    spectralFrobenius ((basisColumns b)ᴴ*A*basisColumns c)=spectralFrobenius A := by
  rw [spectralFrobenius_right _ _ (by simp),spectralFrobenius_left _ _ (by simp)]

/-- The squared Frobenius distance between two spectral diagonal matrices is the sum of squared
coefficient differences weighted by squared eigenbasis overlaps. -/
theorem spectralFrobenius_cross_difference
    (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I))
    (c : OrthonormalBasis K ℂ (EuclideanSpace ℂ I)) (f : J → ℂ) (g : K → ℂ) :
    spectralFrobenius (spectralDiagonal b f-spectralDiagonal c g)^2=
      ∑ i,∑ j,Complex.normSq (((basisColumns b)ᴴ*basisColumns c) i j)*
        Complex.normSq (f i-g j) := by
  let Q := (basisColumns b)ᴴ*basisColumns c
  have hm : (basisColumns b)ᴴ*(spectralDiagonal b f-spectralDiagonal c g)*basisColumns c=
      diagonal f*Q-Q*diagonal g := by
    rw [Matrix.mul_sub,Matrix.sub_mul,basis_adjoint_mul_spectralDiagonal]
    rw [Matrix.mul_assoc (diagonal f),Matrix.mul_assoc (basisColumns b)ᴴ,
      spectralDiagonal_mul_basis,← Matrix.mul_assoc]
    simp only [Q,Matrix.mul_assoc]
  rw [← spectralFrobenius_bases _ b c,spectralFrobenius_sq,hm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  have he : f i*Q i j-Q i j*g j=Q i j*(f i-g j) := by ring
  rw [he,Complex.normSq_mul]

/-- The squared overlap entries between two orthonormal bases have unit row sums and unit column
sums. -/
theorem spectralBasisTransport_marginals
    (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I))
    (c : OrthonormalBasis K ℂ (EuclideanSpace ℂ I)) :
    (∀ i,∑ j,Complex.normSq (((basisColumns b)ᴴ*basisColumns c) i j)=1) ∧
    (∀ j,∑ i,Complex.normSq (((basisColumns b)ᴴ*basisColumns c) i j)=1) := by
  let Q := (basisColumns b)ᴴ*basisColumns c
  have hrow : Q*Qᴴ=1 := by
    dsimp [Q]
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    calc
      (basisColumns b)ᴴ*basisColumns c*((basisColumns c)ᴴ*basisColumns b)=
          (basisColumns b)ᴴ*(basisColumns c*(basisColumns c)ᴴ)*basisColumns b := by
        simp only [Matrix.mul_assoc]
      _=1 := by simp
  have hcol : Qᴴ*Q=1 := by
    dsimp [Q]
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    calc
      (basisColumns c)ᴴ*basisColumns b*((basisColumns b)ᴴ*basisColumns c)=
          (basisColumns c)ᴴ*(basisColumns b*(basisColumns b)ᴴ)*basisColumns c := by
        simp only [Matrix.mul_assoc]
      _=1 := by simp
  constructor
  · intro i
    change (∑ j,Complex.normSq (Q i j))=1
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum,Complex.normSq_eq_conj_mul_self,Complex.ofReal_one]
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply_eq,
      Complex.star_def,mul_comm] using! congrArg (fun M : Matrix J J ℂ => M i i) hrow
  · intro j
    change (∑ i,Complex.normSq (Q i j))=1
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum,Complex.normSq_eq_conj_mul_self,Complex.ofReal_one]
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply_eq,
      Complex.star_def] using! congrArg (fun M : Matrix K K ℂ => M j j) hcol

end BasisTransport

/-- The ordered Hermitian basis vector at index `i` is an eigenvector with eigenvalue
`orderedHermitianValues hA i`. -/
theorem orderedHermitianBasis_action {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} (hA : A.IsHermitian) (i : Fin (Fintype.card I)) :
    A.toEuclideanLin (orderedHermitianBasis hA i)=
      (orderedHermitianValues hA i : ℂ) • orderedHermitianBasis hA i :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).apply_eigenvectorBasis finrank_euclideanSpace i

/-- A Hermitian matrix equals its spectral diagonal reconstruction from the ordered eigenbasis
and eigenvalues. -/
theorem orderedHermitian_diagonal {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    A=spectralDiagonal (orderedHermitianBasis hA) (fun i => (orderedHermitianValues hA i : ℂ)) :=
  eq_spectralDiagonal_of_action _ _ _ (orderedHermitianBasis_action hA)

section OrderedRayleigh
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The subspace spanned by the basis vectors whose indices belong to the finite set `s`. -/
noncomputable def spectralSpan (b : OrthonormalBasis (Fin (Fintype.card I)) ℂ
    (EuclideanSpace ℂ I)) (s : Finset (Fin (Fintype.card I))) : Submodule ℂ (EuclideanSpace ℂ I) :=
  Submodule.span ℂ (b '' (s : Set (Fin (Fintype.card I))))

omit [DecidableEq I] in

/-- The dimension of the span of the basis vectors indexed by `s` equals `s.card`. -/
theorem spectralSpan_finrank (b : OrthonormalBasis (Fin (Fintype.card I)) ℂ
    (EuclideanSpace ℂ I)) (s : Finset (Fin (Fintype.card I))) :
    Module.finrank ℂ (spectralSpan b s)=s.card := by
  have he : Set.range (fun j : ↥s => b j)=b '' (s : Set (Fin (Fintype.card I))) := by
    ext x
    simp
  unfold spectralSpan
  rw [← he]
  simpa only [Fintype.card_coe] using!
    finrank_span_eq_card (b.toBasis.linearIndependent.comp (fun j : ↥s => j.val)
      Subtype.val_injective)

omit [DecidableEq I] in

/-- A vector in the span of basis vectors indexed by `s` has zero coordinates at indices outside
`s`. -/
theorem spectralSpan_repr_zero (b : OrthonormalBasis (Fin (Fintype.card I)) ℂ
    (EuclideanSpace ℂ I)) (s : Finset (Fin (Fintype.card I)))
    {v : EuclideanSpace ℂ I} (hv : v ∈ spectralSpan b s) {j : Fin (Fintype.card I)}
    (hj : j ∉ s) : b.repr v j=0 := by
  have hv' : v ∈ Submodule.span ℂ (b.toBasis '' (s : Set (Fin (Fintype.card I)))) := by
    simpa only [OrthonormalBasis.coe_toBasis,spectralSpan] using! hv
  have hs := b.toBasis.repr_support_subset_of_mem_span (s : Set (Fin (Fintype.card I))) hv'
  have hz : b.toBasis.repr v j=0 := by
    by_contra hn
    exact hj (hs (Finsupp.mem_support_iff.mpr hn))
  simpa only [OrthonormalBasis.coe_toBasis_repr_apply] using! hz

omit [DecidableEq I] in

/-- The squared norm of a vector is the sum of the squared norms of its coordinates in an
orthonormal basis. -/
theorem spectral_norm_sq_basis (b : OrthonormalBasis (Fin (Fintype.card I)) ℂ
    (EuclideanSpace ℂ I)) (v : EuclideanSpace ℂ I) :
    ‖v‖^2=∑ j,Complex.normSq (b.repr v j) := by
  rw [← b.repr.norm_map v,EuclideanSpace.norm_sq_eq]
  simp only [Complex.sq_norm]

/-- The real Rayleigh form of a Hermitian matrix is the sum of its ordered eigenvalues weighted
by squared eigenbasis coordinates. -/
theorem orderedHermitian_rayleigh {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (v : EuclideanSpace ℂ I) :
    (inner ℂ v (A.toEuclideanLin v)).re=∑ j,orderedHermitianValues hA j*
      Complex.normSq ((orderedHermitianBasis hA).repr v j) := by
  let b := orderedHermitianBasis hA
  rw [← b.repr.inner_map_map v (A.toEuclideanLin v),EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : b.repr (A.toEuclideanLin v) j=(orderedHermitianValues hA j : ℂ)*b.repr v j :=
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis_apply_self_apply
      finrank_euclideanSpace v j
  rw [hj]
  have he : star (b.repr v j)*((orderedHermitianValues hA j : ℂ)*b.repr v j)=
      ((orderedHermitianValues hA j*Complex.normSq (b.repr v j) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul,Complex.normSq_eq_conj_mul_self]
    change star (b.repr v j)*((orderedHermitianValues hA j : ℂ)*b.repr v j)=
      (orderedHermitianValues hA j : ℂ)*(star (b.repr v j)*b.repr v j)
    ring
  simpa only [Complex.ofReal_re,mul_comm,mul_left_comm,mul_assoc] using! congrArg Complex.re he

/-- The real Rayleigh form of a matrix at `v` is at most `‖A‖ * ‖v‖ ^ 2`. -/
theorem spectral_rayleigh_norm_bound (A : Matrix I I ℂ) (v : EuclideanSpace ℂ I) :
    (inner ℂ v (A.toEuclideanLin v)).re ≤ ‖A‖*‖v‖^2 := by
  have hmap : ‖A.toEuclideanLin v‖ ≤ ‖A‖*‖v‖ := Matrix.l2_opNorm_mulVec A v
  calc
    (inner ℂ v (A.toEuclideanLin v)).re ≤ ‖inner ℂ v (A.toEuclideanLin v)‖ := Complex.re_le_norm _
    _ ≤ ‖v‖*‖A.toEuclideanLin v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖*(‖A‖*‖v‖) := mul_le_mul_of_nonneg_left hmap (norm_nonneg _)
    _=‖A‖*‖v‖^2 := by ring

/-- The difference of corresponding ordered Hermitian eigenvalues is at most the operator norm
of the matrix difference. -/
theorem orderedHermitian_sub_le_norm (A B : Matrix I I ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (i : Fin (Fintype.card I)) :
    orderedHermitianValues hA i-orderedHermitianValues hB i ≤ ‖A-B‖ := by
  let S := spectralSpan (orderedHermitianBasis hA) (Finset.Iic i)
  let T := spectralSpan (orderedHermitianBasis hB) (Finset.Ici i)
  have hS : Module.finrank ℂ S=i.val+1 := by
    rw [spectralSpan_finrank,Fin.card_Iic]
  have hT : Module.finrank ℂ T=Fintype.card I-i.val := by
    rw [spectralSpan_finrank,Fin.card_Ici]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq S T
  have hsup : Module.finrank ℂ ↥(S ⊔ T) ≤ Fintype.card I := by
    simpa only [finrank_euclideanSpace] using! Submodule.finrank_le (S ⊔ T)
  have hinf : S ⊓ T ≠ ⊥ := by
    intro hz
    rw [hz,finrank_bot,hS,hT] at hdim
    have hi := i.isLt
    omega
  obtain ⟨v,hv,hv0⟩ := (S ⊓ T).ne_bot_iff.mp hinf
  have hlow : orderedHermitianValues hA i*‖v‖^2 ≤ (inner ℂ v (A.toEuclideanLin v)).re := by
    rw [orderedHermitian_rayleigh hA,spectral_norm_sq_basis (orderedHermitianBasis hA),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ≤ i
    · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone hj) (Complex.normSq_nonneg _)
    · rw [spectralSpan_repr_zero _ _ hv.1 (by simpa using! hj)]
      simp
  have hhigh : (inner ℂ v (B.toEuclideanLin v)).re ≤ orderedHermitianValues hB i*‖v‖^2 := by
    rw [orderedHermitian_rayleigh hB,spectral_norm_sq_basis (orderedHermitianBasis hB),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : i ≤ j
    · exact mul_le_mul_of_nonneg_right (hB.eigenvalues₀_antitone hj) (Complex.normSq_nonneg _)
    · rw [spectralSpan_repr_zero _ _ hv.2 (by simpa using! hj)]
      simp
  have hdiff : (inner ℂ v ((A-B).toEuclideanLin v)).re=
      (inner ℂ v (A.toEuclideanLin v)).re-(inner ℂ v (B.toEuclideanLin v)).re := by
    rw [map_sub,LinearMap.sub_apply,inner_sub_right,Complex.sub_re]
  have hbound := spectral_rayleigh_norm_bound (A-B) v
  rw [hdiff] at hbound
  have hsq : 0<‖v‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv0)
  apply (mul_le_mul_iff_right₀ hsq).mp
  nlinarith

end OrderedRayleigh

/-- The sum of squared differences of ordered Hermitian eigenvalues is at most the squared
Frobenius norm of the matrix difference. -/
theorem ordered_hermitian_hoffman_wielandt {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ i,(orderedHermitianValues hA i-orderedHermitianValues hB i)^2) ≤
      spectralFrobenius (A-B)^2 := by
  let a := orderedHermitianValues hA
  let b := orderedHermitianValues hB
  let W : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℝ :=
    fun i j => Complex.normSq (((basisColumns (orderedHermitianBasis hA))ᴴ*
      basisColumns (orderedHermitianBasis hB)) i j)
  have hm := spectralBasisTransport_marginals (orderedHermitianBasis hA) (orderedHermitianBasis hB)
  have hr : ∀ i,∑ j,W i j=1 := hm.1
  have hc : ∀ j,∑ i,W i j=1 := hm.2
  have ht := ordered_transport_rearrangement (Fintype.card I) a b W
    hA.eigenvalues₀_antitone hB.eigenvalues₀_antitone
    (fun _ _ => Complex.normSq_nonneg _) hr hc
  have hcross := spectralFrobenius_cross_difference (orderedHermitianBasis hA)
    (orderedHermitianBasis hB) (fun i => (a i : ℂ)) (fun j => (b j : ℂ))
  rw [← orderedHermitian_diagonal hA,← orderedHermitian_diagonal hB] at hcross
  have hs : spectralFrobenius (A-B)^2=∑ i,∑ j,W i j*(a i-b j)^2 := by
    simpa only [← Complex.ofReal_sub,Complex.normSq_ofReal,pow_two] using! hcross
  have hra : (∑ i,∑ j,W i j*(a i)^2)=∑ i,(a i)^2 := by
    simp only [← Finset.sum_mul,hr,one_mul]
  have hcb : (∑ i,∑ j,W i j*(b j)^2)=∑ j,(b j)^2 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul,hc,one_mul]
  have hexpand : (∑ i,∑ j,W i j*(a i-b j)^2)=
      (∑ i,(a i)^2)+(∑ j,(b j)^2)-2*(∑ i,∑ j,W i j*a i*b j) := by
    have he (i j : Fin (Fintype.card I)) :
        W i j*(a i-b j)^2=W i j*(a i)^2+W i j*(b j)^2-2*(W i j*a i*b j) := by ring
    simp_rw [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
    rw [hra,hcb]
  have hdiag : (∑ i,(a i-b i)^2)=(∑ i,(a i)^2)+(∑ i,(b i)^2)-2*(∑ i,a i*b i) := by
    have he (i : Fin (Fintype.card I)) :
        (a i-b i)^2=(a i)^2+(b i)^2-2*(a i*b i) := by ring
    simp_rw [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  change (∑ i,(a i-b i)^2) ≤  spectralFrobenius (A-B)^2
  rw [hs,hexpand,hdiag]
  linarith

section SingularPerturbation
variable {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]

/-- Equal symmetric endomorphisms have equal chosen orthonormal eigenvector bases. -/
private theorem spectral_frame_congr (T S : Module.End ℂ (EuclideanSpace ℂ I))
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (h : T=S) :
    hT.eigenvectorBasis finrank_euclideanSpace=hS.eigenvectorBasis finrank_euclideanSpace := by
  subst S
  rfl

/-- Equal symmetric endomorphisms have equal chosen eigenvalue families. -/
private theorem spectral_values_congr (T S : Module.End ℂ (EuclideanSpace ℂ I))
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (h : T=S) :
    hT.eigenvalues finrank_euclideanSpace=hS.eigenvalues finrank_euclideanSpace := by
  subst S
  rfl

/-- The ordered eigenbasis of `Aᴴ * A` is the right singular basis of `A`, and its ordered
eigenvalues are the squared singular values. -/
theorem singular_gram_ordered (A : Matrix O I ℂ) :
    orderedHermitianBasis (Matrix.isHermitian_conjTranspose_mul_self A)=rightSingularBasis A ∧
      ∀ i : Fin (Fintype.card I),
        orderedHermitianValues (Matrix.isHermitian_conjTranspose_mul_self A) i=
          (matrixSingularValues A i)^2 := by
  have hb := spectral_frame_congr _ _
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_conjTranspose_mul_self A))
    A.toEuclideanLin.isSymmetric_adjoint_comp_self (toEuclideanLin_gram A)
  have hv := spectral_values_congr _ _
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_conjTranspose_mul_self A))
    A.toEuclideanLin.isSymmetric_adjoint_comp_self (toEuclideanLin_gram A)
  refine ⟨hb,?_⟩
  intro i
  exact (congrFun hv i).trans (A.toEuclideanLin.sq_singularValues_fin finrank_euclideanSpace i).symm

/-- The squared norm of `A v` is the sum of squared singular values weighted by squared
coordinates in the right singular basis. -/
theorem singular_norm_image_sq (A : Matrix O I ℂ) (v : EuclideanSpace ℂ I) :
    ‖A.toEuclideanLin v‖^2=∑ j : Fin (Fintype.card I),(matrixSingularValues A j)^2*
      Complex.normSq ((rightSingularBasis A).repr v j) := by
  have hi : ‖A.toEuclideanLin v‖^2=(inner ℂ v ((Aᴴ*A).toEuclideanLin v)).re := by
    rw [toEuclideanLin_gram,LinearMap.comp_apply,A.toEuclideanLin.adjoint_inner_right]
    exact norm_sq_eq_re_inner (𝕜 := ℂ) _
  rw [hi,orderedHermitian_rayleigh (Matrix.isHermitian_conjTranspose_mul_self A),
    (singular_gram_ordered A).1]
  simp_rw [(singular_gram_ordered A).2]

/-- The difference of corresponding singular values is at most the operator norm of the matrix
difference. -/
theorem singular_sub_le_norm (A B : Matrix O I ℂ) (i : Fin (Fintype.card I)) :
    matrixSingularValues A i-matrixSingularValues B i ≤ ‖A-B‖ := by
  let S := spectralSpan (rightSingularBasis A) (Finset.Iic i)
  let T := spectralSpan (rightSingularBasis B) (Finset.Ici i)
  have hS : Module.finrank ℂ S=i.val+1 := by rw [spectralSpan_finrank,Fin.card_Iic]
  have hT : Module.finrank ℂ T=Fintype.card I-i.val := by rw [spectralSpan_finrank,Fin.card_Ici]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq S T
  have hsup : Module.finrank ℂ ↥(S ⊔ T) ≤ Fintype.card I := by
    simpa only [finrank_euclideanSpace] using! Submodule.finrank_le (S ⊔ T)
  have hinf : S ⊓ T ≠ ⊥ := by
    intro hz
    rw [hz,finrank_bot,hS,hT] at hdim
    have hi := i.isLt
    omega
  obtain ⟨v,hv,hv0⟩ := (S ⊓ T).ne_bot_iff.mp hinf
  have hlow : (matrixSingularValues A i)^2*‖v‖^2 ≤ ‖A.toEuclideanLin v‖^2 := by
    rw [singular_norm_image_sq,spectral_norm_sq_basis (rightSingularBasis A),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ≤ i
    · have horder := A.toEuclideanLin.singularValues_antitone (Fin.le_iff_val_le_val.mp hj)
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (matrixSingularValues_nonneg A i) (matrixSingularValues_nonneg A j)).mpr horder)
        (Complex.normSq_nonneg _)
    · rw [spectralSpan_repr_zero _ _ hv.1 (by simpa using! hj)]
      simp
  have hhigh : ‖B.toEuclideanLin v‖^2 ≤ (matrixSingularValues B i)^2*‖v‖^2 := by
    rw [singular_norm_image_sq,spectral_norm_sq_basis (rightSingularBasis B),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : i ≤ j
    · have horder := B.toEuclideanLin.singularValues_antitone (Fin.le_iff_val_le_val.mp hj)
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (matrixSingularValues_nonneg B j) (matrixSingularValues_nonneg B i)).mpr horder)
        (Complex.normSq_nonneg _)
    · rw [spectralSpan_repr_zero _ _ hv.2 (by simpa using! hj)]
      simp
  have hlowNorm : matrixSingularValues A i*‖v‖ ≤ ‖A.toEuclideanLin v‖ :=
    (sq_le_sq₀ (mul_nonneg (matrixSingularValues_nonneg A i) (norm_nonneg _)) (norm_nonneg _)).mp
      (by simpa only [mul_pow] using! hlow)
  have hhighNorm : ‖B.toEuclideanLin v‖ ≤ matrixSingularValues B i*‖v‖ :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (matrixSingularValues_nonneg B i) (norm_nonneg _))).mp
      (by simpa only [mul_pow] using! hhigh)
  have hmap : ‖(A-B).toEuclideanLin v‖ ≤ ‖A-B‖*‖v‖ := Matrix.l2_opNorm_mulVec (A-B) v
  have hnorm := norm_sub_norm_le (A.toEuclideanLin v) (B.toEuclideanLin v)
  have hdiff : A.toEuclideanLin v-B.toEuclideanLin v=(A-B).toEuclideanLin v := by
    rw [map_sub,LinearMap.sub_apply]
  rw [hdiff] at hnorm
  apply (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hv0)).mp
  nlinarith

/-- A square matrix with operator norm at most one has sums of squared entry norms at most one
in every row and column. -/
theorem contraction_normSq_marginals (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : ‖Q‖ ≤ 1) :
    (∀ i,∑ j,Complex.normSq (Q i j) ≤ 1) ∧ (∀ j,∑ i,Complex.normSq (Q i j) ≤ 1) := by
  have hcol (P : Matrix (Fin n) (Fin n) ℂ) (hP : ‖P‖ ≤ 1) (j : Fin n) :
      (∑ i,Complex.normSq (P i j)) ≤ 1 := by
    let e := EuclideanSpace.basisFun (Fin n) ℂ j
    have he : P.toEuclideanLin e=WithLp.toLp 2 (fun i => P i j) := by
      ext i
      simp [e,Matrix.toLpLin_apply,EuclideanSpace.basisFun_apply,Matrix.mulVec_single_one]
    have h := Matrix.l2_opNorm_mulVec P e
    change ‖P.toEuclideanLin e‖ ≤ ‖P‖*‖e‖ at h
    have he1 : ‖e‖=1 := (EuclideanSpace.basisFun (Fin n) ℂ).norm_eq_one j
    rw [he1,mul_one] at h
    have hs : ‖P.toEuclideanLin e‖^2 ≤ 1 := by
      nlinarith [h.trans hP,norm_nonneg (P.toEuclideanLin e)]
    rw [he,EuclideanSpace.norm_sq_eq] at hs
    simpa only [WithLp.ofLp_toLp,Complex.sq_norm] using! hs
  refine ⟨?_,hcol Q hQ⟩
  intro i
  have h := hcol Qᴴ (by simpa only [Matrix.l2_opNorm_conjTranspose] using! hQ) i
  simpa only [Matrix.conjTranspose_apply,Complex.star_def,Complex.normSq_conj] using! h

/-- The real part of `z * star w` is at most the average of the squared norms of `z` and `w`. -/
theorem complex_overlap_real_le (z w : ℂ) :
    (z*star w).re ≤ (Complex.normSq z+Complex.normSq w)/2 := by
  have h := Complex.normSq_nonneg (z-w)
  rw [Complex.normSq_sub] at h
  simp only [Complex.star_def] at h ⊢
  linarith

/-- Expand the real trace inner product of two factored matrices as a sum of coefficient
products weighted by left and right factor overlaps. -/
theorem singular_cross_trace (n : ℕ) (LA LB : Matrix O (Fin n) ℂ)
    (RA RB : Matrix I (Fin n) ℂ) (a b : Fin n → ℝ) :
    (Matrix.trace ((LA*diagonal (fun i => (a i : ℂ))*RAᴴ)ᴴ*
      (LB*diagonal (fun i => (b i : ℂ))*RBᴴ))).re=
    ∑ i,∑ j,a i*b j*((LAᴴ*LB) i j*star ((RAᴴ*RB) i j)).re := by
  let Da := diagonal (fun i => (a i : ℂ))
  let Db := diagonal (fun i => (b i : ℂ))
  let QL := LAᴴ*LB
  let QR := RAᴴ*RB
  have hDa : Daᴴ=Da := by
    ext i j
    by_cases hij : i=j <;> simp [Da,Matrix.conjTranspose_apply,hij,Ne.symm]
  have hQR : QRᴴ=RBᴴ*RA := by
    simp only [QR,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  have he : Matrix.trace ((LA*Da*RAᴴ)ᴴ*(LB*Db*RBᴴ))=
      Matrix.trace (Da*QL*Db*QRᴴ) := by
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hDa]
    calc
      Matrix.trace (RA*(Da*LAᴴ)*(LB*Db*RBᴴ))=
          Matrix.trace ((RA*(Da*QL*Db))*RBᴴ) := by simp only [QL,Matrix.mul_assoc]
      _=Matrix.trace (RBᴴ*(RA*(Da*QL*Db))) := Matrix.trace_mul_comm _ _
      _=Matrix.trace ((RBᴴ*RA)*(Da*QL*Db)) := by rw [← Matrix.mul_assoc]
      _=Matrix.trace ((Da*QL*Db)*(RBᴴ*RA)) := Matrix.trace_mul_comm _ _
      _=Matrix.trace (Da*QL*Db*QRᴴ) := by rw [hQR]
  change (Matrix.trace ((LA*Da*RAᴴ)ᴴ*(LB*Db*RBᴴ))).re=_
  rw [he]
  simp only [Matrix.trace,Matrix.diag_apply,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.conjTranspose_apply]
  change (((a i : ℂ)*QL i j*(b j : ℂ))*star (QR i j)).re=
    a i*b j*(QL i j*star (QR i j)).re
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero]
  ring

/-- The trace of a spectral diagonal matrix is the sum of its spectral coefficients. -/
theorem spectralDiagonal_trace (n : ℕ)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ I)) (f : Fin n → ℂ) :
    Matrix.trace (spectralDiagonal b f)=∑ i,f i := by
  unfold spectralDiagonal
  rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,basisColumns_adjoint_mul,Matrix.one_mul,
    Matrix.trace_diagonal]

/-- The squared Frobenius norm is the sum of squared singular values over the input dimension. -/
theorem spectralFrobenius_sq_singular (A : Matrix O I ℂ) :
    spectralFrobenius A^2=∑ i : Fin (Fintype.card I),(matrixSingularValues A i)^2 := by
  have hGram : Aᴴ*A=spectralDiagonal (rightSingularBasis A)
      (fun i => (matrixSingularValues A i : ℂ)^2) :=
    eq_spectralDiagonal_of_action _ _ _ (gram_apply_rightSingularBasis A)
  rw [spectralFrobenius_sq_trace,hGram,spectralDiagonal_trace]
  simp only [Complex.re_sum,← Complex.ofReal_pow,Complex.ofReal_re]

/-- The squared Frobenius norm of `A - B` equals the sum of their squared Frobenius norms minus
twice the real trace inner product. -/
theorem spectralFrobenius_sq_sub (A B : Matrix O I ℂ) :
    spectralFrobenius (A-B)^2=spectralFrobenius A^2+spectralFrobenius B^2-
      2*(Matrix.trace (Aᴴ*B)).re := by
  have he : (A-B)ᴴ*(A-B)=Aᴴ*A+Bᴴ*B-(Aᴴ*B+Bᴴ*A) := by
    simp only [Matrix.conjTranspose_sub,Matrix.sub_mul,Matrix.mul_sub]
    abel
  have ht : (Matrix.trace (Bᴴ*A)).re=(Matrix.trace (Aᴴ*B)).re := by
    have h : Matrix.trace (Bᴴ*A)=star (Matrix.trace (Aᴴ*B)) := by
      calc
        Matrix.trace (Bᴴ*A)=Matrix.trace (Aᴴ*B)ᴴ := by
          simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
        _=star (Matrix.trace (Aᴴ*B)) := Matrix.trace_conjTranspose _
    simpa only [Complex.star_def,Complex.conj_re] using! congrArg Complex.re h
  rw [spectralFrobenius_sq_trace,spectralFrobenius_sq_trace,spectralFrobenius_sq_trace,he,
    Matrix.trace_sub,Matrix.trace_add,Matrix.trace_add,Complex.sub_re,Complex.add_re,Complex.add_re,ht]
  ring

/-- The product `Cᴴ * D` of the adjoint of a contraction with a contraction has operator norm at
most one. -/
private theorem contraction_overlap_norm_le {X : Type} [Fintype X] [DecidableEq X]
    (n : ℕ) (C D : Matrix X (Fin n) ℂ) (hC : ‖C‖ ≤ 1) (hD : ‖D‖ ≤ 1) :
    ‖Cᴴ*D‖ ≤ 1 := by
  have hCa : ‖Cᴴ‖ ≤ 1 := by simpa only [Matrix.l2_opNorm_conjTranspose] using! hC
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul hCa hD (norm_nonneg _) zero_le_one).trans_eq (by norm_num))

/-- The real trace inner product of two matrices is at most the sum of the products of their
corresponding ordered singular values. -/
theorem singular_cross_trace_le (A B : Matrix O I ℂ) :
    (Matrix.trace (Aᴴ*B)).re ≤ ∑ i : Fin (Fintype.card I),matrixSingularValues A i*matrixSingularValues B i := by
  let LA := leftSingularColumns A
  let LB := leftSingularColumns B
  let RA := basisColumns (rightSingularBasis A)
  let RB := basisColumns (rightSingularBasis B)
  let a : Fin (Fintype.card I) → ℝ := fun i => matrixSingularValues A i
  let b : Fin (Fintype.card I) → ℝ := fun i => matrixSingularValues B i
  let QL := LAᴴ*LB
  let QR := RAᴴ*RB
  let W : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℝ := fun i j =>
    (Complex.normSq (QL i j)+Complex.normSq (QR i j))/2
  have hQL : ‖QL‖ ≤ 1 := contraction_overlap_norm_le _ LA LB
    (leftSingularColumns_norm_le A) (leftSingularColumns_norm_le B)
  have hQR : ‖QR‖ ≤ 1 := contraction_overlap_norm_le _ RA RB
    (basisColumns_norm_le _) (basisColumns_norm_le _)
  have hLM := contraction_normSq_marginals _ QL hQL
  have hRM := contraction_normSq_marginals _ QR hQR
  have hWr (i : Fin (Fintype.card I)) : (∑ j,W i j) ≤ 1 := by
    dsimp only [W]
    rw [← Finset.sum_div,Finset.sum_add_distrib]
    linarith [hLM.1 i,hRM.1 i]
  have hWc (j : Fin (Fintype.card I)) : (∑ i,W i j) ≤ 1 := by
    dsimp only [W]
    rw [← Finset.sum_div,Finset.sum_add_distrib]
    linarith [hLM.2 j,hRM.2 j]
  have hnonneg (i j : Fin (Fintype.card I)) : 0 ≤ W i j :=
    div_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (by norm_num)
  have hAa : A=LA*diagonal (fun i => (a i : ℂ))*RAᴴ := (oddSingularTransform_id A).symm
  have hBb : B=LB*diagonal (fun i => (b i : ℂ))*RBᴴ := (oddSingularTransform_id B).symm
  have hc : (Matrix.trace (Aᴴ*B)).re=∑ i,∑ j,a i*b j*(QL i j*star (QR i j)).re := by
    calc
      (Matrix.trace (Aᴴ*B)).re=(Matrix.trace ((LA*diagonal (fun i => (a i : ℂ))*RAᴴ)ᴴ*
          (LB*diagonal (fun i => (b i : ℂ))*RBᴴ))).re :=
        congrArg₂ (fun X Y : Matrix O I ℂ => (Matrix.trace (Xᴴ*Y)).re) hAa hBb
      _=∑ i,∑ j,a i*b j*(QL i j*star (QR i j)).re := singular_cross_trace _ LA LB RA RB a b
  have hpoint (i j : Fin (Fintype.card I)) : a i*b j*(QL i j*star (QR i j)).re ≤ W i j*a i*b j := by
    have h := mul_le_mul_of_nonneg_left (complex_overlap_real_le (QL i j) (QR i j))
      (mul_nonneg (matrixSingularValues_nonneg A i) (matrixSingularValues_nonneg B j))
    simpa only [mul_comm,mul_left_comm,mul_assoc] using! h
  rw [hc]
  calc
    (∑ i,∑ j,a i*b j*(QL i j*star (QR i j)).re) ≤ ∑ i,∑ j,W i j*a i*b j :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpoint i j))
    _ ≤ ∑ i,a i*b i := ordered_subtransport_rearrangement _ a b W
      (fun _ _ h => A.toEuclideanLin.singularValues_antitone (Fin.le_iff_val_le_val.mp h))
      (fun _ _ h => B.toEuclideanLin.singularValues_antitone (Fin.le_iff_val_le_val.mp h))
      (fun i => matrixSingularValues_nonneg A i) (fun i => matrixSingularValues_nonneg B i) hnonneg hWr hWc

/-- The sum of squared differences of corresponding singular values is at most the squared
Frobenius norm of the matrix difference. -/
theorem singular_mirsky_bound (A B : Matrix O I ℂ) :
    (∑ i : Fin (Fintype.card I),(matrixSingularValues A i-matrixSingularValues B i)^2) ≤
      spectralFrobenius (A-B)^2 := by
  have ht := singular_cross_trace_le A B
  have he : (∑ i : Fin (Fintype.card I),(matrixSingularValues A i-matrixSingularValues B i)^2)=
      (∑ i : Fin (Fintype.card I),(matrixSingularValues A i)^2)+
      (∑ i : Fin (Fintype.card I),(matrixSingularValues B i)^2)-
      2*(∑ i : Fin (Fintype.card I),matrixSingularValues A i*matrixSingularValues B i) := by
    have h (i : Fin (Fintype.card I)) :
        (matrixSingularValues A i-matrixSingularValues B i)^2=(matrixSingularValues A i)^2+
          (matrixSingularValues B i)^2-2*(matrixSingularValues A i*matrixSingularValues B i) := by ring
    simp_rw [h,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [he,spectralFrobenius_sq_sub,spectralFrobenius_sq_singular,spectralFrobenius_sq_singular]
  linarith

end SingularPerturbation

/-- Ordered Hermitian eigenvalue differences satisfy the absolute Weyl operator norm bound and
the squared Hoffman–Wielandt Frobenius bound. -/
theorem ordered_hermitian_weyl_and_hoffman_wielandt : ∀ (I : Type) [Fintype I]
    [DecidableEq I] (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian),
    (∀ i,|orderedHermitianValues hA i-orderedHermitianValues hB i| ≤ ‖A-B‖) ∧
    (∑ i,(orderedHermitianValues hA i-orderedHermitianValues hB i)^2) ≤
      spectralFrobenius (A-B)^2 := by
  intro I _ _ A B hA hB
  refine ⟨?_,ordered_hermitian_hoffman_wielandt A B hA hB⟩
  intro i
  apply abs_le.mpr
  have hAB := orderedHermitian_sub_le_norm A B hA hB i
  have hBA := orderedHermitian_sub_le_norm B A hB hA i
  rw [norm_sub_rev] at hBA
  constructor <;> linarith

/-- Rectangular matrix singular value differences satisfy the absolute Weyl operator norm bound
at every natural index and the squared Mirsky Frobenius bound over the input dimension. -/
theorem rectangular_singular_weyl_and_mirsky : ∀ (O I : Type) [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A B : Matrix O I ℂ),
    (∀ i : ℕ,|matrixSingularValues A i-matrixSingularValues B i| ≤ ‖A-B‖) ∧
    (∑ i∈Finset.range (Fintype.card I),(matrixSingularValues A i-matrixSingularValues B i)^2) ≤
      spectralFrobenius (A-B)^2 := by
  intro O I _ _ _ _ A B
  refine ⟨?_,?_⟩
  · intro i
    by_cases hi : i<Fintype.card I
    · have hAB := singular_sub_le_norm A B ⟨i,hi⟩
      have hBA := singular_sub_le_norm B A ⟨i,hi⟩
      rw [norm_sub_rev] at hBA
      apply abs_le.mpr
      constructor <;> linarith
    · rw [matrixSingularValues_of_card_le A (by omega),matrixSingularValues_of_card_le B (by omega)]
      simp only [sub_self,abs_zero]
      exact norm_nonneg _
  · rw [← Fin.sum_univ_eq_sum_range]
    exact singular_mirsky_bound A B

end Qatlib.Concepts.SpectralSketch.SpectrumPerturb
