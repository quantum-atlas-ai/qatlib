/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws

/-!
# Spectral Bounds for Rank-One Perturbed Hamiltonians

This module proves finite-dimensional spectral inequalities associated with
Lemma 3 of Boixo and Somma for the Hamiltonian family
`H_x = -|x⟩⟨x| + F / 4`, where `F` is an `x`-independent Hermitian perturbation
satisfying `‖F‖ ≤ 1`. It establishes upper bounds on the ground-state energy,
lower bounds on the first excited eigenvalue and spectral gap, and a constant
lower bound on the ground-state overlap `|⟨x|ψ_x⟩|²`.

The lowest-eigenvalue bound assumes `0 < M`; the second-eigenvalue, gap, and
overlap bounds assume `3 ≤ M`. Eigenvalues are ordered decreasingly, so the
last two indices represent the two smallest eigenvalues. The overlap theorem
concerns the selected normalized eigenvector in `orderedHermitianBasis`.
These are matrix inequalities, with no algorithmic spectral-gap amplification
or oracle complexity theorem asserted.

## Main statements

* `source_lowest_eigenvalue_le`: the ground-state eigenvalue obeys `E_0 ≤ -3 / 4`.
* `source_second_eigenvalue_ge`: the second-smallest eigenvalue obeys `E_1 ≥ -1 / 4`.
* `source_spectral_gap_ge`: the spectral gap obeys `Δ = E_1 - E_0 ≥ 1 / 2`.
* `source_ground_overlap`: the ground-state overlap obeys `|⟨x|ψ_x⟩|² ≥ 1 / 2`.

## References

* [Boixo and Somma, 2012][BoixoSomma2012SpectralGap], Lemma 3, Eq. (25), p. 9.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.SpectralGap11.MainResults

variable {M : ℕ}

/-- The matrix expression `H_x = -|x⟩⟨x| + F / 4` of Lemma 3, Eq. (25).
Hermiticity and a norm bound on `F` are separate hypotheses of later theorems. -/
def sourceH (F : Matrix (Fin M) (Fin M) ℂ) (x : Fin M) : Matrix (Fin M) (Fin M) ℂ :=
  -outerProduct (Ket x) + (1 / 4 : ℂ) • F

/-- `H_x` is Hermitian whenever `F` is Hermitian. -/
theorem sourceH_isHermitian (F : Matrix (Fin M) (Fin M) ℂ) (hF : F.IsHermitian) (x : Fin M) :
    (sourceH F x).IsHermitian := by
  unfold sourceH
  refine IsHermitian.add ?_ ?_
  · exact (isOrthogonalProjector_outerProduct (normalized_ket x)).isSelfAdjoint.neg
  · have h : (1 / 4 : ℂ) = ((1 / 4 : ℚ) : ℂ) := by norm_num
    rw [h]
    exact hF.smul (IsSelfAdjoint.ratCast (1 / 4 : ℚ))

/-- The last ordered index `M - 1`, corresponding to the smallest eigenvalue. -/
def finLast (hM : 0 < M) : Fin (Fintype.card (Fin M)) :=
  ⟨M - 1, by rw [Fintype.card_fin]; omega⟩

/-- `finLast` is the maximal ordered index. -/
lemma le_finLast (hM : 0 < M) (j : Fin (Fintype.card (Fin M))) : j ≤ finLast hM := by
  have hj : j.val ≤ M - 1 := by
    have h1 : j.val < Fintype.card (Fin M) := j.isLt
    have h2 : Fintype.card (Fin M) = M := Fintype.card_fin M
    omega
  exact hj

/-- The second-smallest ordered index `M - 2`. -/
def finPrev (hM : 2 ≤ M) : Fin (Fintype.card (Fin M)) :=
  ⟨M - 2, by rw [Fintype.card_fin]; omega⟩

/-- Bridge between `inner` on `EuclideanSpace` and `Qatlib.Foundations.PureStateMath.Inner`. -/
lemma inner_toLp (v w : Fin M → ℂ) :
    inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 w)
      = Qatlib.Foundations.PureStateMath.Inner v w := by
  rw [Qatlib.Foundations.PureStateMath.Inner,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- The minimal ordered eigenvalue is at most the Rayleigh quotient of any unit vector. -/
lemma ordered_last_le_rayleigh (hM : 0 < M) {A : Matrix (Fin M) (Fin M) ℂ}
    (hA : A.IsHermitian) (v : EuclideanSpace ℂ (Fin M)) (hv : ‖v‖ = 1) :
    orderedHermitianValues hA (finLast hM) ≤ (inner ℂ v (A.toEuclideanLin v)).re := by
  let b := orderedHermitianBasis hA
  have hmax : ∀ j : Fin (Fintype.card (Fin M)), j ≤ finLast hM := fun j => le_finLast hM j
  have hparse : ∑ j, Complex.normSq (b.repr v j) = 1 := by
    have := spectral_norm_sq_basis b v
    rw [hv] at this; norm_num at this; exact this.symm
  rw [orderedHermitian_rayleigh hA]
  calc orderedHermitianValues hA (finLast hM)
      = orderedHermitianValues hA (finLast hM) * (∑ j, Complex.normSq (b.repr v j)) := by
        rw [hparse, mul_one]
    _ = ∑ j, orderedHermitianValues hA (finLast hM) * Complex.normSq (b.repr v j) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ j, orderedHermitianValues hA j * Complex.normSq (b.repr v j) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone (hmax j)) (Complex.normSq_nonneg _)
    _ = _ := by rfl

/-- The computational basis ket `Ket x` has Euclidean norm one. -/
lemma norm_toLp_ket (x : Fin M) : ‖WithLp.toLp 2 (Ket x : Fin M → ℂ)‖ = 1 := by
  have hsq : ‖WithLp.toLp 2 (Ket x : Fin M → ℂ)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hk := normalized_ket x
    simp [Complex.sq_norm, Ket] at hk ⊢
  nlinarith [norm_nonneg (WithLp.toLp 2 (Ket x : Fin M → ℂ))]

/-- `Inner (Ket x) w = w x`: the `x`-th coordinate functional. -/
lemma inner_ket_eq (x : Fin M) (w : Fin M → ℂ) :
    Qatlib.Foundations.PureStateMath.Inner (Ket x) w = w x := by
  rw [inner_apply, Finset.sum_eq_single x]
  · simp [Ket]
  · intro b _ hb; simp [Ket, hb]
  · intro hx; exact absurd (Finset.mem_univ x) hx

/-- `Inner (Ket x) (A *ᵥ Ket x) = A x x`, the `(x, x)` diagonal entry. -/
lemma inner_ket_mulVec (A : Matrix (Fin M) (Fin M) ℂ) (x : Fin M) :
    Qatlib.Foundations.PureStateMath.Inner (Ket x) (A *ᵥ Ket x) = A x x := by
  rw [inner_ket_eq]
  simp [Matrix.mulVec, dotProduct, Ket]

/-- `|x⟩⟨x|` fixes `|x⟩`. -/
lemma ket_mulVec_ket (x : Fin M) :
    outerProduct (Ket x) *ᵥ (Ket x : Fin M → ℂ) = Ket x := by
  rw [outerProduct_mulVec, inner_ket_ket]
  simp

/-- `H_x` applied to `|x⟩`. -/
lemma sourceH_mulVec_ket (F : Matrix (Fin M) (Fin M) ℂ) (x : Fin M) :
    (sourceH F x) *ᵥ (Ket x : Fin M → ℂ) = -(Ket x) + (1 / 4 : ℂ) • (F *ᵥ Ket x) := by
  rw [sourceH, Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec, ket_mulVec_ket]

/-- `H_x` applied to a vector with zero `x`-coordinate reduces to `F / 4`. -/
lemma sourceH_mulVec_of_coord_zero (F : Matrix (Fin M) (Fin M) ℂ) (x : Fin M)
    (u : Fin M → ℂ) (hu : u x = 0) :
    (sourceH F x) *ᵥ u = (1 / 4 : ℂ) • (F *ᵥ u) := by
  rw [sourceH, Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec,
    outerProduct_mulVec, inner_ket_eq, hu]
  simp

/-- **Lemma 3 (lowest eigenvalue)**: for `H_x = -|x⟩⟨x| + F / 4` with `‖F‖ ≤ 1`,
the ground-state energy obeys `E_0 ≤ -3 / 4`. -/
theorem source_lowest_eigenvalue_le (hM : 0 < M) (F : Matrix (Fin M) (Fin M) ℂ)
    (hF : F.IsHermitian) (hFn : ‖F‖ ≤ 1) (x : Fin M) :
    orderedHermitianValues (sourceH_isHermitian F hF x) (finLast hM) ≤ -3 / 4 := by
  have hH := sourceH_isHermitian F hF x
  have hv : ‖WithLp.toLp 2 (Ket x : Fin M → ℂ)‖ = 1 := norm_toLp_ket x
  have h := ordered_last_le_rayleigh hM hH (WithLp.toLp 2 (Ket x)) hv
  have hmvx : ((sourceH F x) *ᵥ (Ket x : Fin M → ℂ)) x = -1 + (1 / 4 : ℂ) * F x x := by
    rw [sourceH_mulVec_ket]
    simp [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Ket, Matrix.mulVec, dotProduct]
  have hcomp : (inner ℂ (WithLp.toLp 2 (Ket x : Fin M → ℂ))
      ((sourceH F x).toEuclideanLin (WithLp.toLp 2 (Ket x : Fin M → ℂ)))).re
      = -1 + (1 / 4) * (F x x).re := by
    rw [Matrix.toLpLin_apply, inner_toLp, inner_ket_eq, hmvx, Complex.add_re,
      Complex.mul_re]
    norm_num
  rw [hcomp] at h
  have hbound : (F x x).re ≤ 1 := by
    have := spectral_rayleigh_norm_bound F (WithLp.toLp 2 (Ket x : Fin M → ℂ))
    rw [Matrix.toLpLin_apply, inner_toLp, inner_ket_mulVec, hv] at this
    nlinarith [hFn]
  linarith

/-- Rayleigh quotient upper bound for a vector in the span of the two smallest
ordered eigenvectors. -/
lemma rayleigh_le_of_mem_span_Ici (hM : 2 ≤ M) {A : Matrix (Fin M) (Fin M) ℂ}
    (hA : A.IsHermitian) {v : EuclideanSpace ℂ (Fin M)}
    (hv : v ∈ spectralSpan (orderedHermitianBasis hA) (Finset.Ici (finPrev hM))) :
    (inner ℂ v (A.toEuclideanLin v)).re
      ≤ orderedHermitianValues hA (finPrev hM) * ‖v‖ ^ 2 := by
  let b := orderedHermitianBasis hA
  rw [orderedHermitian_rayleigh hA, spectral_norm_sq_basis b v, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjm : j ∈ Finset.Ici (finPrev hM)
  · have hle : finPrev hM ≤ j := by simpa using hjm
    exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone hle) (Complex.normSq_nonneg _)
  · rw [spectralSpan_repr_zero b _ hv hjm]
    simp

/-- On vectors with zero `x`-coordinate the Rayleigh quotient of `H_x` is one
quarter of that of `F`. -/
lemma source_rayleigh_of_coord_zero (F : Matrix (Fin M) (Fin M) ℂ) (x : Fin M)
    (v : EuclideanSpace ℂ (Fin M)) (hv : v.ofLp x = 0) :
    (inner ℂ v ((sourceH F x).toEuclideanLin v)).re
      = (1 / 4) * (inner ℂ v (F.toEuclideanLin v)).re := by
  rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply, inner_toLp, inner_toLp,
    sourceH_mulVec_of_coord_zero F x v.ofLp hv]
  rw [Qatlib.Foundations.PureStateMath.Inner,
    Qatlib.Foundations.PureStateMath.Inner, dotProduct_smul, smul_eq_mul,
    Complex.mul_re]
  norm_num

/-- For `3 ≤ M`, Hermitian `F`, and `‖F‖ ≤ 1`, the second-smallest eigenvalue
of `sourceH F x` satisfies `λ_{M-2} ≥ -1 / 4`. -/
theorem source_second_eigenvalue_ge (hM : 3 ≤ M) (F : Matrix (Fin M) (Fin M) ℂ)
    (hF : F.IsHermitian) (hFn : ‖F‖ ≤ 1) (x : Fin M) :
    -(1 / 4) ≤ orderedHermitianValues (sourceH_isHermitian F hF x) (finPrev (by omega)) := by
  have hH := sourceH_isHermitian F hF x
  set S := spectralSpan (orderedHermitianBasis hH) (Finset.Ici (finPrev (by omega : 2 ≤ M)))
    with hSdef
  have hSdim : Module.finrank ℂ S = 2 := by
    rw [hSdef, spectralSpan_finrank]
    have hc : (Finset.Ici (finPrev (by omega : 2 ≤ M))).card = 2 := by
      rw [Fin.card_Ici]
      simp only [finPrev, Fintype.card_fin]
      omega
    exact hc
  let g : S →ₗ[ℂ] ℂ := (EuclideanSpace.projₗ x).comp S.subtype
  have hker : LinearMap.ker g ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [hSdim, Module.finrank_self]
    norm_num
  rcases (Submodule.ne_bot_iff (LinearMap.ker g)).mp hker with ⟨w, hwker, hwne⟩
  have hgw : g w = 0 := LinearMap.mem_ker.mp hwker
  set u : EuclideanSpace ℂ (Fin M) := (w : S).1 with hudef
  have hux : u.ofLp x = 0 := by
    simpa [g, u, LinearMap.comp_apply] using hgw
  have hune : u ≠ 0 := by
    intro h
    apply hwne
    apply Subtype.ext
    simpa [u] using h
  have humem : u ∈ S := (w : S).2
  have hub : (inner ℂ u ((sourceH F x).toEuclideanLin u)).re
      ≤ orderedHermitianValues hH (finPrev (by omega : 2 ≤ M)) * ‖u‖ ^ 2 := by
    apply rayleigh_le_of_mem_span_Ici (by omega : 2 ≤ M) hH
    simpa [hSdef] using humem
  have hlas : (inner ℂ u ((sourceH F x).toEuclideanLin u)).re
      = (1 / 4) * (inner ℂ u (F.toEuclideanLin u)).re := by
    exact source_rayleigh_of_coord_zero F x u hux
  have hFlb : -(‖u‖ ^ 2) ≤ (inner ℂ u (F.toEuclideanLin u)).re := by
    have h := spectral_rayleigh_norm_bound (-F) u
    have hnegapp : ((-F).toEuclideanLin u) = -(F.toEuclideanLin u) := by
      rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply, Matrix.neg_mulVec]
      simp
    rw [hnegapp, inner_neg_right, norm_neg] at h
    rw [Complex.neg_re] at h
    have hs : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
    have hmul : ‖F‖ * ‖u‖ ^ 2 ≤ 1 * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right hFn hs
    nlinarith [h, hmul]
  have hpos : 0 < ‖u‖ ^ 2 := by
    have : 0 < ‖u‖ := norm_pos_iff.mpr hune
    positivity
  nlinarith [hub, hlas, hFlb, hpos]

/-- For `3 ≤ M`, Hermitian `F`, and `‖F‖ ≤ 1`, the two smallest eigenvalues
of `sourceH F x` satisfy `λ_{M-2} - λ_{M-1} ≥ 1 / 2`. -/
theorem source_spectral_gap_ge (hM : 3 ≤ M) (F : Matrix (Fin M) (Fin M) ℂ)
    (hF : F.IsHermitian) (hFn : ‖F‖ ≤ 1) (x : Fin M) :
    1 / 2 ≤ orderedHermitianValues (sourceH_isHermitian F hF x) (finPrev (by omega))
            - orderedHermitianValues (sourceH_isHermitian F hF x) (finLast (by omega)) := by
  have h1 := source_second_eigenvalue_ge hM F hF hFn x
  have h2 := source_lowest_eigenvalue_le (by omega : 0 < M) F hF hFn x
  linarith

/-- For `3 ≤ M`, Hermitian `F`, and `‖F‖ ≤ 1`, the selected ground state
`ψ_x = orderedHermitianBasis hH (finLast _)` of `H_x = -|x⟩⟨x| + F / 4` satisfies
`|⟨x|ψ_x⟩|² = ‖ψ_x(x)‖² ≥ 1 / 2`. -/
theorem source_ground_overlap (hM : 3 ≤ M) (F : Matrix (Fin M) (Fin M) ℂ)
    (hF : F.IsHermitian) (hFn : ‖F‖ ≤ 1) (x : Fin M) :
    1 / 2 ≤ ‖(orderedHermitianBasis (sourceH_isHermitian F hF x)
      (finLast (by omega : 0 < M))).ofLp x‖ ^ 2 := by
  have hM0 : 0 < M := by omega
  let hH := sourceH_isHermitian F hF x
  let idx := finLast hM0
  let ψ := orderedHermitianBasis hH idx
  have hnorm : ‖ψ‖ = 1 := (orderedHermitianBasis hH).orthonormal.1 idx
  have heig : (inner ℂ ψ ((sourceH F x).toEuclideanLin ψ)).re = orderedHermitianValues hH idx := by
    rw [orderedHermitianBasis_action hH idx, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [hnorm]
  have hlow : orderedHermitianValues hH idx ≤ -3 / 4 :=
    source_lowest_eigenvalue_le hM0 F hF hFn x
  have hket : (inner ℂ ψ ((outerProduct (Ket x)).toEuclideanLin ψ)).re = ‖ψ.ofLp x‖ ^ 2 := by
    have hmv : outerProduct (Ket x) *ᵥ ψ.ofLp = (ψ.ofLp x) • (Ket x : Fin M → ℂ) := by
      rw [outerProduct_mulVec, inner_ket_eq]
    have hin : inner ℂ ψ ((outerProduct (Ket x)).toEuclideanLin ψ) =
        (starRingEnd ℂ) (ψ.ofLp x) * ψ.ofLp x := by
      rw [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct, hmv]
      simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single x]
      · simp [Ket]
        ring
      · intro j _ hj; simp [Ket, hj]
      · intro hx; exact absurd (Finset.mem_univ x) hx
    rw [hin]
    have hns : ((starRingEnd ℂ) (ψ.ofLp x) * ψ.ofLp x).re = Complex.normSq (ψ.ofLp x) := by
      simpa only [Complex.ofReal_re] using
        congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := ψ.ofLp x)).symm
    rw [hns, Complex.normSq_eq_norm_sq]
  have hdecomp : (inner ℂ ψ ((sourceH F x).toEuclideanLin ψ)).re =
      -(‖ψ.ofLp x‖ ^ 2) + (1 / 4) * (inner ℂ ψ (F.toEuclideanLin ψ)).re := by
    have happ : (sourceH F x).toEuclideanLin ψ =
        -((outerProduct (Ket x)).toEuclideanLin ψ) + (1 / 4 : ℂ) • (F.toEuclideanLin ψ) := by
      rw [sourceH, Matrix.toLpLin_apply, Matrix.toLpLin_apply, Matrix.toLpLin_apply,
        Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec]
      simp
    rw [happ, inner_add_right, inner_neg_right, inner_smul_right,
      Complex.add_re, Complex.neg_re, Complex.mul_re, hket]
    norm_num
  have hFlb : -1 ≤ (inner ℂ ψ (F.toEuclideanLin ψ)).re := by
    have h := spectral_rayleigh_norm_bound (-F) ψ
    have hnegapp : ((-F).toEuclideanLin ψ) = -(F.toEuclideanLin ψ) := by
      rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply, Matrix.neg_mulVec]
      simp
    rw [hnegapp, inner_neg_right, norm_neg, Complex.neg_re, hnorm] at h
    nlinarith [h, hFn]
  linarith [heig, hlow, hdecomp, hFlb]

end Qatlib.Papers.SpectralGap11.MainResults
