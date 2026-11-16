/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullSourceGapForm
public import Qatlib.Concepts.GibbsSource.SourceForms.FullPauliSparse

@[expose] public section


/-! # Complete source domination for row/column sparse proposals

The physical transition family has at most two active labels at each
output coordinate. The existing two-frequency source kernel is therefore
sufficient even when the entire proposal has many distinct frequencies.
The two labels may coincide, and repeated frequencies remain coherent.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {κ : Type*} [Fintype κ]

/-- A real PSD kernel contracts nonnegatively against arbitrary complex scalars. -/
theorem fullRealKernel_scalar_nonneg (M : Matrix κ κ ℝ) (hM : M.PosSemidef)
    (v : κ → ℂ) :
    0 ≤ ∑ a, ∑ b, M a b * (star (v a) * v b).re := by
  have hr := hM.dotProduct_mulVec_nonneg (fun a => (v a).re)
  have hi := hM.dotProduct_mulVec_nonneg (fun a => (v a).im)
  have he : (∑ a, ∑ b, M a b * (star (v a) * v b).re) =
      star (fun a => (v a).re) ⬝ᵥ (M *ᵥ (fun a => (v a).re)) +
      star (fun a => (v a).im) ⬝ᵥ (M *ᵥ (fun a => (v a).im)) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [he]
  exact add_nonneg hr hi

/-- Only the support of the complex input needs two labels. Other
frequencies in the complete transition index are unrestricted. -/
theorem fullSourcePairSupport_nonneg (β : ℝ) (ν : κ → ℝ)
    (a b : κ) (v : κ → ℂ)
    (hv : ∀ k, k ≠ a → k ≠ b → v k = 0) :
    0 ≤ ∑ k, ∑ l, (ckgSourceWeight β (ν k) (ν l) *
      (3 / 4 - phaseKernel β (ν k - ν l))) * (star (v k) * v l).re := by
  classical
  let s : κ → Fin 2 := fun k => if k = a then 0 else 1
  let N := (ckgSourceKernel β ![ν a, ν b]).submatrix s s
  have hN : N.PosSemidef := (ckgSourceKernel_pair_posSemidef β (ν a) (ν b)).submatrix s
  have hs (k : κ) (hk : v k ≠ 0) : ![ν a, ν b] (s k) = ν k := by
    by_cases hka : k = a
    · simp [s, hka]
    · have hkb : k = b := by
        by_contra hkb
        exact hk (hv k hka hkb)
      dsimp only [s]
      rw [ite_eq_right hka]
      simpa using congrArg ν hkb.symm
  have he : (∑ k, ∑ l, (ckgSourceWeight β (ν k) (ν l) *
      (3 / 4 - phaseKernel β (ν k - ν l))) * (star (v k) * v l).re) =
      ∑ k, ∑ l, N k l * (star (v k) * v l).re := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases hk : v k = 0
    · simp [hk]
    by_cases hl : v l = 0
    · simp [hl]
    simp only [N, Matrix.submatrix_apply, ckgSourceKernel_apply, hs k hk, hs l hl]
  rw [he]
  exact fullRealKernel_scalar_nonneg N hN v

variable {D : ℕ}

/-- Row/column support of the actual thermal factor, on a complete output
coordinate. This statement derives its two labels from the proposal. -/
theorem fullTransitionFactor_pairSupport (lam : Fin D → ℝ) (β : ℝ)
    (A : Operator D) (hA : fullMatrixOneSparse A) (X : Operator D)
    (r : FullCoord D) :
    ∃ a b : FullCoord D, ∀ k, k ≠ a → k ≠ b →
      (parentFactor (gibbsDiag lam β) (fullTransition A k) X) r.1 r.2 = 0 := by
  obtain ⟨j, hj⟩ := hA.1 r.1
  obtain ⟨i, hi⟩ := hA.2 r.2
  refine ⟨(r.1, j), (i, r.2), ?_⟩
  intro k hka hkb
  rw [fullTransition_eq_smul, parentFactor_smul, Matrix.smul_apply, smul_eq_mul,
    parentFactor_matUnit_entry]
  by_cases hrow : r.1 = k.1
  · have hcol : k.2 ≠ j := by
      intro he
      exact hka (Prod.ext hrow.symm he)
    rw [← hrow, hj _ hcol, zero_mul]
  · by_cases hcol : r.2 = k.2
    · have hrow' : k.1 ≠ i := by
        intro he
        exact hkb (Prod.ext he hcol.symm)
      rw [← hcol, hi _ hrow', zero_mul]
    · simp [hrow, hcol]

/-- Full Monomial sum rotate for the stated finite source data. -/
private theorem fullMonomial_sum_rotate {α γ δ : Type*}
    [Fintype α] [Fintype γ] [Fintype δ] (f : α → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ r, f a b r) = ∑ r, ∑ a, ∑ b, f a b r := by
  classical
  calc
    _ = ∑ a, ∑ r, ∑ b, f a b r :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The actual complete source kernel contracts nonnegatively for a
row/column sparse proposal. All complex operator coordinates are retained. -/
theorem fullMonomial_sourceContraction_nonneg (lam : Fin D → ℝ) (β : ℝ)
    (A : Operator D) (hA : fullMatrixOneSparse A) (X : Operator D) :
    0 ≤ ∑ a, ∑ b, (ckgSourceWeight β (fullNu lam a) (fullNu lam b) *
      (3 / 4 - phaseKernel β (fullNu lam a - fullNu lam b))) *
      (hsInner (parentFactor (gibbsDiag lam β) (fullTransition A a) X)
        (parentFactor (gibbsDiag lam β) (fullTransition A b) X)).re := by
  classical
  let F := fun a => parentFactor (gibbsDiag lam β) (fullTransition A a) X
  have he (a b : FullCoord D) : (hsInner (F a) (F b)).re =
      ∑ r : FullCoord D, (star (F a r.1 r.2) * F b r.1 r.2).re := by
    simp only [hsInner_eq_sum, Fintype.sum_prod_type]
    change complexReAddMonoidHom (∑ i, ∑ j, star (F a i j) * F b i j) =
      ∑ i, ∑ j, complexReAddMonoidHom (star (F a i j) * F b i j)
    simp only [map_sum]
  change 0 ≤ ∑ a, ∑ b, _ * (hsInner (F a) (F b)).re
  simp_rw [he, Finset.mul_sum]
  rw [fullMonomial_sum_rotate]
  refine Finset.sum_nonneg fun r _ => ?_
  obtain ⟨a, b, hab⟩ := fullTransitionFactor_pairSupport lam β A hA X r
  exact fullSourcePairSupport_nonneg β (fullNu lam) a b
    (fun k => F k r.1 r.2) hab

/-- Physical `W/2` source domination for one sparse proposal, without a
global two-frequency, Hermiticity, or frequency-injectivity hypothesis. -/
theorem fullMonomial_sourceDomination (lam : Fin D → ℝ) (β : ℝ)
    (A : Operator D) (hA : fullMatrixOneSparse A) :
    ckgSourceDomination β (gibbsDiag lam β) (fullNu lam) (fullTransition A) := by
  intro X
  have hcon := fullMonomial_sourceContraction_nonneg lam β A hA X
  have he : 3 / 2 * (ckgSourcePlainForm β (gibbsDiag lam β) (fullNu lam)
      (fullTransition A) X).re -
      (ckgSourceDampedForm β (gibbsDiag lam β) (fullNu lam) (fullTransition A) X).re =
      ∑ a, ∑ b, (ckgSourceWeight β (fullNu lam a) (fullNu lam b) *
        (3 / 4 - phaseKernel β (fullNu lam a - fullNu lam b))) *
        (hsInner (parentFactor (gibbsDiag lam β) (fullTransition A a) X)
          (parentFactor (gibbsDiag lam β) (fullTransition A b) X)).re := by
    rw [ckgSourcePlainForm, ckgSourceDampedForm, wplainForm_re_eq, wdampedForm_re]
    simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [← he] at hcon
  linarith

variable {ι : Type*} [Fintype ι]

/-- Complete matrix Rayleigh domination, summed only over the independent
physical proposals; there are no cross-proposal Gram terms. -/
theorem fullGramMatrix_monomial_rayleigh_le (lam : Fin D → ℝ) (β : ℝ)
    (A : ι → Operator D) (hA : ∀ P, fullMatrixOneSparse (A P))
    (z : FullCoord D → ℂ) :
    fullRayleigh (fullGramMatrix lam β (fun ω => 2 * phaseKernel β ω) A) z ≤
      3 / 2 * fullRayleigh (fullGramMatrix lam β (fun _ => 1) A) z := by
  rw [fullGramMatrix_damped_rayleigh_source, fullGramMatrix_plain_rayleigh_source,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun P _ =>
    fullMonomial_sourceDomination lam β (A P) (hA P) (fun i j => z (i, j))

/-- Actual complete Loewner comparison, with the physical half retained. -/
theorem fullGramMatrix_monomial_domination (lam : Fin D → ℝ) (β : ℝ)
    (A : ι → Operator D) (hA : ∀ P, fullMatrixOneSparse (A P)) :
    ((3 / 2 : ℂ) • fullGramMatrix lam β (fun _ => 1) A -
      fullGramMatrix lam β (fun ω => 2 * phaseKernel β ω) A).PosSemidef := by
  have hs : IsSelfAdjoint (3 / 2 : ℂ) := by simp [IsSelfAdjoint]
  have hd : (fullGramMatrix lam β (fun ω => 2 * phaseKernel β ω) A).IsHermitian := by
    apply fullGramMatrix_isHermitian_of_weight_symm
    intro a b
    simp only [fullWeight]
    rw [ckgSourceWeight_symm β (fullNu lam a) (fullNu lam b),
      show fullNu lam a - fullNu lam b = -(fullNu lam b - fullNu lam a) by ring,
      phaseKernel_neg]
  have hh := ((fullGramMatrix_plain_isHermitian lam β A).smul hs).sub
    hd
  apply (fullHermitian_posSemidef_iff hh).mpr
  intro z
  have h := fullGramMatrix_monomial_rayleigh_le lam β A hA z
  rw [fullRayleigh_sub]
  have hc : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by norm_num
  rw [hc, fullRayleigh_real_smul]
  linarith

/-- The full attained gaps obey the same size-independent upper bound.
Sparsity alone is sufficient; kernel uniqueness is not assumed here. -/
theorem fullSourceGap_monomial_upper (hD : 2 ≤ D) (lam : Fin D → ℝ) (β : ℝ)
    (A : ι → Operator D) (hA : ∀ P, fullMatrixOneSparse (A P)) :
    fullSourceDampedGap lam β A ≤ 3 / 2 * fullSourcePlainGap lam β A := by
  obtain ⟨z, hz, he, _⟩ := fullRayleighGap_attained
    (fullGramMatrix lam β (fun _ => 1) A) (fullGibbsVector lam β)
    (fullGibbsUnitOrthogonal_nonempty hD lam β)
  have hd := fullRayleighGap_le
    (fullGramMatrix lam β (fun ω => 2 * phaseKernel β ω) A)
    (fullGibbsVector lam β) z hz
  have hu := fullGramMatrix_monomial_rayleigh_le lam β A hA z
  change fullSourceDampedGap lam β A ≤ 3 / 2 * fullRayleighGap _ _
  rw [he]
  exact hd.trans hu

end Qatlib.Concepts.GibbsSource.SourceForms
