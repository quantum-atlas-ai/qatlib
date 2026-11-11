/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.MatrixComputationDefs

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# Certified Hermitian spectrum computation

This module constructs rational diagonal congruence certificates for symmetric rational
matrices. Invariance of the negative index under invertible congruence identifies the
certificate counts with eigenvalue counts below rational thresholds. `checkPoints` verifies a
finite grid certificate, and `certifiedSpectrum` returns rational samples together with such a
certificate. The matrix-theoretic background is described in [HornJohnson2013] and [Bhatia1997].

For complex Hermitian matrices with rational real and imaginary parts, `blockRealFin` gives a
real symmetric representation whose eigenvalue multiplicities are doubled.
`certifiedPointsCSharp` uses the enclosure `sharpBoundC`, and `certifiedSpectrumC` divides the
cumulative block counts by two when decoding samples. The module also bounds the stored
generation step and operation counts, rational witness heights, and assigned point-checking
costs.

## Main statements

* `negCount_congr`: invertible real congruence preserves the negative eigenvalue count of a
  Hermitian matrix.
* `certificate_sound`: valid certificates give exact counts in consecutive half-open intervals
  and enclose the spectrum.
* `eigenvalues_fin_eq_two_mul`: the real block representation doubles every complex eigenvalue
  multiplicity.
* `certifiedSpectrum_spec`: the real construction returns `n` samples and an accepted
  certificate, with each eigenvalue within the requested positive tolerance of a sample.
* `certifiedSpectrumC_spec`: the corresponding guarantee for rational complex Hermitian data.

## References

* [Horn and Johnson, 2013][HornJohnson2013]
* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false


namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb
namespace CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

variable {n : ℕ}

/-- A pair of rational endpoints for an interval, with no ordering condition imposed. -/
structure RatInterval where

  lo : ℚ

  hi : ℚ
deriving DecidableEq, Repr

/-- Data for a spectral counting certificate at a rational threshold, consisting of a matrix and
diagonal entries. -/
structure Point (n : ℕ) where

  q : ℚ

  M : Matrix (Fin n) (Fin n) ℚ

  d : Fin n → ℚ
deriving DecidableEq

/-- The number of strictly negative entries of a rational diagonal vector. -/
def negCountOf {n : ℕ} (d : Fin n → ℚ) : ℕ :=
  (Finset.univ.filter (fun i => d i < 0)).card

/-- The rational matrix obtained by subtracting `q` times the identity from `A`. -/
def shift {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (q : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  A - scalar (Fin n) q

/-- The condition that the data in `p` express `shift A p.q` as the congruence `p.Mᵀ * diagonal
p.d * p.M`. -/
def PointCongruent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (p : Point n) : Prop :=
  p.Mᵀ * diagonal p.d * p.M = shift A p.q

/-- The condition that `p` gives a diagonal congruence for the shifted matrix with a nonzero
determinant. -/
def PointValid {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (p : Point n) : Prop :=
  p.M.det ≠ 0 ∧ PointCongruent A p

/-- The condition that the thresholds in a list of certificate points are strictly increasing. -/
def GridStrict {n : ℕ} (pts : List (Point n)) : Prop :=
  pts.Pairwise fun p q => p.q < q.q

/-- The endpoint conditions requiring negative counts zero at the first point and `n` at the
last point, whenever these points exist. -/
def OuterCounts {n : ℕ} (pts : List (Point n)) : Prop :=
  (∀ p, pts.head? = some p → negCountOf p.d = 0) ∧
  (∀ p, pts.getLast? = some p → negCountOf p.d = n)

/-- Validity of a nonempty certificate list: every point is valid, thresholds strictly increase,
and the endpoint counts are zero and `n`. -/
def Valid {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (pts : List (Point n)) : Prop :=
  pts ≠ [] ∧ (∀ p ∈ pts, PointValid A p) ∧ GridStrict pts ∧ OuterCounts pts

/-- A Boolean check of the determinant and diagonal congruence conditions for a single
certificate point. -/
def checkPoint {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (p : Point n) : Bool :=
  (p.M.det != 0) && decide (p.Mᵀ * diagonal p.d * p.M = shift A p.q)

/-- A Boolean check of nonemptiness, increasing thresholds, point validity, and the two endpoint
counts. -/
def checkPoints {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (pts : List (Point n)) : Bool :=
  (!pts.isEmpty) &&
  decide (pts.Pairwise fun p q : Point n => p.q < q.q) &&
  pts.all (checkPoint A) &&
  (pts.head?.map (fun p => negCountOf p.d == 0)).getD false &&
  (pts.getLast?.map (fun p => negCountOf p.d == n)).getD false

/-- The rational endpoint pairs formed by consecutive certificate points. -/
def intervalsOf {n : ℕ} (pts : List (Point n)) : List RatInterval :=
  (pts.zip (pts.drop 1)).map fun pq => ⟨pq.1.q, pq.2.q⟩

/-- The natural-number difference between the negative counts at `q` and `p`. -/
def countBetween {n : ℕ} (p q : Point n) : ℕ := negCountOf q.d - negCountOf p.d

/-- The number of negative real roots of a matrix's characteristic polynomial, counted with
multiplicity. -/
noncomputable def negCount {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : ℕ :=
  (B.charpoly.roots.filter fun r => r < 0).card

/-- The number of strictly negative entries of a real diagonal vector. -/
noncomputable def negCountDiag {n : ℕ} (d : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter fun i => d i < 0).card

end CertifiedHermitianSpectrum
end CertifiedStage
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- The roots of a product of real linear factors form the multiset of their specified roots. -/
lemma roots_prod_X_sub_C {n : ℕ} (v : Fin n → ℝ) :
    (∏ i, (Polynomial.X - Polynomial.C (v i))).roots = Finset.univ.val.map v := by
  have hne : (∏ i : Fin n, (Polynomial.X - Polynomial.C (v i))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact Polynomial.X_sub_C_ne_zero (v i)
  rw [Polynomial.roots_prod (fun i => Polynomial.X - Polynomial.C (v i)) Finset.univ hne]
  simp [Polynomial.roots_X_sub_C, Multiset.bind_singleton]

/-- The negative-root count of a real diagonal matrix equals the number of its negative diagonal
entries. -/
lemma negCount_diagonal {n : ℕ} (d : Fin n → ℝ) :
    negCount (diagonal d) = negCountDiag d := by
  unfold negCount negCountDiag
  rw [Matrix.charpoly_diagonal, roots_prod_X_sub_C, Multiset.filter_map, Multiset.card_map,
    ← Finset.filter_val]
  simp only [Function.comp_apply]
  rfl

/-- For a real Hermitian matrix, the negative-root count equals the number of negative
eigenvalues, counted by index. -/
lemma negCount_eq_card_filter_eigenvalues {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) :
    negCount B = (Finset.univ.filter fun i => hB.eigenvalues i < 0).card := by
  unfold negCount
  rw [hB.roots_charpoly_eq_eigenvalues, Multiset.filter_map, Multiset.card_map,
    ← Finset.filter_val]
  congr 1

/-- The negative-root count of a Hermitian matrix shifted by `q` equals the number of
eigenvalues strictly below `q`. -/
lemma negCount_shift {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (q : ℝ) :
    negCount (A - scalar (Fin n) q) =
      (Finset.univ.filter fun i => hA.eigenvalues i < q).card := by
  have hcp : (A - scalar (Fin n) q).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (hA.eigenvalues i - q)) := by
    rw [Matrix.charpoly_sub_scalar, hA.charpoly_eq, Polynomial.prod_comp]
    refine Finset.prod_congr rfl ?_
    intro i _
    simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    rw [Polynomial.C_sub]
    abel
  unfold negCount
  rw [hcp, roots_prod_X_sub_C, Multiset.filter_map, Multiset.card_map]
  have hset : (Multiset.filter ((fun r => r < 0) ∘ fun i => hA.eigenvalues i - q)
        Finset.univ.val) = (Finset.univ.filter (fun i => hA.eigenvalues i < q)).val := by
    rw [Finset.filter_val]
    apply Multiset.filter_congr
    intro i _
    simp only [Function.comp_apply]
    constructor <;> intro h <;> linarith
  rw [hset]
  rfl

/-- The number of values in the half-open interval `[a, b)` is the difference of the counts
strictly below its endpoints. -/
lemma card_filter_interval {n : ℕ} (lam : Fin n → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (Finset.univ.filter fun i => a ≤ lam i ∧ lam i < b).card =
      (Finset.univ.filter fun i => lam i < b).card -
        (Finset.univ.filter fun i => lam i < a).card := by
  classical
  set A := Finset.univ.filter (fun i => lam i < a) with hA
  set B := Finset.univ.filter (fun i => lam i < b) with hB
  set T := Finset.univ.filter (fun i => a ≤ lam i ∧ lam i < b) with hT
  have hunion : B = A ∪ T := by
    ext i
    simp only [hA, hB, hT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h
      by_cases h' : lam i < a
      · exact Or.inl h'
      · exact Or.inr ⟨le_of_not_gt h', h⟩
    · rintro (h | ⟨h1, h2⟩)
      · linarith
      · exact h2
  have hdisj : Disjoint A T := by
    rw [Finset.disjoint_left]
    intro i hi hj
    simp only [hA, hT, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    linarith [hi, hj.1]
  rw [hunion, Finset.card_union_of_disjoint hdisj, hT, hA]
  omega

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- The real quadratic form `x ↦ (B *ᵥ x) ⬝ᵥ x` associated with a matrix. -/
def qform {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  (B *ᵥ x) ⬝ᵥ x

/-- The quadratic form of a diagonal matrix is the sum of its diagonal entries times the squared
coordinates. -/
lemma qform_diagonal {n : ℕ} (d : Fin n → ℝ) (x : Fin n → ℝ) :
    qform (diagonal d) x = ∑ j, d j * (x j) ^ 2 := by
  unfold qform
  rw [dotProduct]
  simp only [Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

/-- A transpose can be moved across a real dot product as matrix-vector multiplication on the
other argument. -/
lemma dotProduct_transpose_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (y x : Fin n → ℝ) : (Mᵀ *ᵥ y) ⬝ᵥ x = y ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.mulVec_transpose M y, dotProduct_mulVec]

/-- Matrix congruence transforms a quadratic form by composing its argument with the congruence
matrix. -/
lemma qform_congruence {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : qform (Mᵀ * B * M) x = qform B (M *ᵥ x) := by
  unfold qform
  rw [← Matrix.mulVec_mulVec x (Mᵀ * B) M, ← Matrix.mulVec_mulVec (M *ᵥ x) Mᵀ B]
  exact dotProduct_transpose_mulVec M (B *ᵥ (M *ᵥ x)) x

/-- The condition that `f` is injective and the quadratic form of `B` is strictly negative on
images of nonzero vectors. -/
def NegativeOn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) {k : ℕ}
    (f : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ)) : Prop :=
  Function.Injective ⇑f ∧ ∀ c : Fin k → ℝ, c ≠ 0 → qform B (f c) < 0

/-- The condition that `m` is the largest dimension of a linearly embedded subspace on which the
quadratic form is strictly negative. -/
def HasNegIndex {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) : Prop :=
  (∃ f : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ), NegativeOn B f) ∧
    ∀ k : ℕ, (∃ f : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ), NegativeOn B f) → k ≤ m

/-- The maximal dimension of a negative subspace, when specified by `HasNegIndex`, is unique. -/
theorem hasNegIndex_unique {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} {m m' : ℕ}
    (h : HasNegIndex B m) (h' : HasNegIndex B m') : m = m' := by
  have h1 : m ≤ m' := h'.2 m h.1
  have h2 : m' ≤ m := h.2 m' h'.1
  omega

/-- Congruence by a real matrix with nonzero determinant preserves the negative index. -/
theorem hasNegIndex_congr {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.det ≠ 0) (m : ℕ) :
    HasNegIndex (Mᵀ * B * M) m ↔ HasNegIndex B m := by
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hinjM : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det M).mpr hunit)
  have hmul : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hunit
  have hMinj : Function.Injective M⁻¹.mulVec := by
    intro a b hab
    have h : M *ᵥ (M⁻¹ *ᵥ a) = M *ᵥ (M⁻¹ *ᵥ b) := by rw [hab]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec,
      Matrix.one_mulVec] at h
    exact h
  constructor
  · rintro ⟨⟨f, hf_inj, hf_neg⟩, hmax⟩
    refine ⟨⟨M.mulVecLin.comp f, ?_, ?_⟩, ?_⟩
    · exact hinjM.comp hf_inj
    · intro c hc
      have h := hf_neg c hc
      rw [qform_congruence] at h
      simpa [LinearMap.comp_apply, Matrix.mulVecLin_apply] using! h
    · intro k hk
      obtain ⟨g, hg_inj, hg_neg⟩ := hk
      refine hmax k ⟨M⁻¹.mulVecLin.comp g, ?_, ?_⟩
      · exact hMinj.comp hg_inj
      · intro c hc
        rw [qform_congruence]
        have hco : M *ᵥ (M⁻¹.mulVecLin.comp g) c = g c := by
          simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hmul,
            Matrix.one_mulVec]
        rw [hco]
        exact hg_neg c hc
  · rintro ⟨⟨f, hf_inj, hf_neg⟩, hmax⟩
    refine ⟨⟨M⁻¹.mulVecLin.comp f, ?_, ?_⟩, ?_⟩
    · exact hMinj.comp hf_inj
    · intro c hc
      rw [qform_congruence]
      have hco : M *ᵥ (M⁻¹.mulVecLin.comp f) c = f c := by
        simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hmul,
          Matrix.one_mulVec]
      rw [hco]
      exact hf_neg c hc
    · intro k hk
      obtain ⟨g, hg_inj, hg_neg⟩ := hk
      refine hmax k ⟨M.mulVecLin.comp g, ?_, ?_⟩
      · exact hinjM.comp hg_inj
      · intro c hc
        have h := hg_neg c hc
        rw [qform_congruence] at h
        simpa [LinearMap.comp_apply, Matrix.mulVecLin_apply] using! h

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix
open scoped BigOperators

/-- The star of a real matrix equals its transpose. -/
lemma star_eq_transpose {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : star M = Mᵀ := by
  ext i j
  simp [Matrix.star_apply, Matrix.transpose_apply]

/-- A real matrix equal to its transpose is Hermitian. -/
lemma isHermitian_of_transpose {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (h : Xᵀ = X) :
    X.IsHermitian := by
  simpa [Matrix.IsHermitian, star_eq_transpose] using! h

/-- A real diagonal matrix has negative index equal to its number of negative diagonal entries. -/
theorem hasNegIndex_diagonal {n : ℕ} (d : Fin n → ℝ) :
    HasNegIndex (diagonal d) (negCountDiag d) := by
  classical
  have hcard : Fintype.card {i : Fin n // d i < 0} = negCountDiag d := by
    rw [Fintype.card_subtype]
    rfl
  let ec : Fin (negCountDiag d) ≃ {i : Fin n // d i < 0} :=
    (Fintype.equivFinOfCardEq hcard).symm
  constructor
  · let f : (Fin (negCountDiag d) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun j => if h : d j < 0 then LinearMap.proj (ec.symm ⟨j, h⟩) else 0
    have hcoord : ∀ (c : Fin (negCountDiag d) → ℝ) (i : Fin (negCountDiag d)),
        f c (ec i).1 = c i := by
      intro c i
      simp only [f, LinearMap.pi_apply]
      rw [dif_pos (ec i).2, LinearMap.proj_apply, Equiv.symm_apply_apply]
    have hfinj : Function.Injective ⇑f := by
      intro c c' hcc
      funext i
      have := congrFun hcc (ec i).1
      rwa [hcoord c i, hcoord c' i] at this
    have hfneg : ∀ c : Fin (negCountDiag d) → ℝ, c ≠ 0 → qform (diagonal d) (f c) < 0 := by
      intro c hc
      rw [qform_diagonal]
      have hzero : ∀ j, ¬ d j < 0 → f c j = 0 := by
        intro j hj
        simp only [f, LinearMap.pi_apply, dif_neg hj, LinearMap.zero_apply]
      have hsplit : (∑ j, d j * (f c j) ^ 2) =
          (Finset.univ.filter (fun j => d j < 0)).sum (fun j => d j * (f c j) ^ 2) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro j _
        by_cases hj : d j < 0
        · simp [hj]
        · simp [hj, hzero j hj]
      rw [hsplit]
      have hex : ∃ i, c i ≠ 0 := by
        by_contra h
        rw [not_exists] at h
        exact hc (funext fun i => not_not.mp (h i))
      obtain ⟨i0, hi0⟩ := hex
      have hle : ∀ j ∈ Finset.univ.filter (fun j => d j < 0),
          d j * (f c j) ^ 2 ≤ (0 : ℝ) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hj) (sq_nonneg _)
      have hstrict : ∃ j ∈ Finset.univ.filter (fun j => d j < 0),
          d j * (f c j) ^ 2 < (0 : ℝ) := by
        refine ⟨(ec i0).1, ?_, ?_⟩
        · simp [(ec i0).2]
        · rw [hcoord c i0]
          exact mul_neg_of_neg_of_pos (ec i0).2 (sq_pos_of_ne_zero hi0)
      have hlt := Finset.sum_lt_sum (s := Finset.univ.filter (fun j => d j < 0))
        (f := fun j => d j * (f c j) ^ 2) (g := fun _ => (0 : ℝ)) hle hstrict
      simpa using! hlt
    exact ⟨f, And.intro hfinj hfneg⟩
  · intro k hk
    obtain ⟨f, hf_inj, hf_neg⟩ := hk
    let proj : (Fin n → ℝ) →ₗ[ℝ] ({i : Fin n // d i < 0} → ℝ) :=
      LinearMap.pi fun j => LinearMap.proj j.1
    have hz : ∀ (c : Fin k → ℝ) (j : {i : Fin n // d i < 0}), proj (f c) j = f c j.1 := by
      intro c j
      simp only [proj, LinearMap.pi_apply, LinearMap.proj_apply]
    have hker : ∀ c : Fin k → ℝ, proj (f c) = 0 → c = 0 := by
      intro c hc0
      by_contra hcne
      have hnonzero : ∀ j : {i : Fin n // d i < 0}, f c j.1 = 0 := by
        intro j
        have := congrFun hc0 j
        rwa [hz c j] at this
      have hnonneg : 0 ≤ qform (diagonal d) (f c) := by
        rw [qform_diagonal]
        refine Finset.sum_nonneg fun j _ => ?_
        by_cases hj : d j < 0
        · rw [hnonzero ⟨j, hj⟩]; simp
        · exact mul_nonneg (le_of_not_gt hj) (sq_nonneg _)
      have hneg := hf_neg c hcne
      linarith
    have hinj : Function.Injective ⇑(proj.comp f) := by
      intro a b hab
      have h : proj (f (a - b)) = 0 := by
        rw [map_sub f a b, map_sub proj (f a) (f b)]
        exact sub_eq_zero.mpr hab
      exact sub_eq_zero.mp (hker (a - b) h)
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, hcard] at hle
    simpa using! hle

/-- The negative-root count of a real Hermitian matrix is its negative index. -/
theorem negCount_hasNegIndex {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) :
    HasNegIndex B (negCount B) := by
  classical
  set U : Matrix (Fin n) (Fin n) ℝ := (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  have hUU : Uᵀ * U = 1 := by
    have h := Unitary.coe_star_mul_self hB.eigenvectorUnitary
    rw [hU]
    rwa [star_eq_transpose] at h
  have hUdet : U.det ≠ 0 := by
    intro h0
    have h1 : Uᵀ.det * U.det = 1 := by
      rw [← Matrix.det_mul, hUU, Matrix.det_one]
    rw [Matrix.det_transpose, h0, mul_zero] at h1
    exact zero_ne_one h1
  have hspec : Uᵀ * B * U = diagonal hB.eigenvalues := by
    have h := hB.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at h
    simp only [Unitary.coe_star] at h
    rw [star_star] at h
    rw [hU]
    rwa [star_eq_transpose] at h
  have hcount : negCount B = negCountDiag hB.eigenvalues := by
    rw [negCount_eq_card_filter_eigenvalues hB]
    rfl
  rw [hcount]
  refine (hasNegIndex_congr B hUdet (negCountDiag hB.eigenvalues)).mp ?_
  rw [hspec]
  exact hasNegIndex_diagonal hB.eigenvalues

/-- Congruence by an invertible real matrix preserves the negative eigenvalue count of a
Hermitian matrix; see [HornJohnson2013]. -/
theorem negCount_congr {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.det ≠ 0) :
    negCount (Mᵀ * B * M) = negCount B := by
  have hherm : (Mᵀ * B * M).IsHermitian := by
    have hBt : Bᵀ = B := by simpa using! hB
    refine isHermitian_of_transpose ?_
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hBt,
      Matrix.mul_assoc]
  refine hasNegIndex_unique (negCount_hasNegIndex hherm) ?_
  exact (hasNegIndex_congr B hM (negCount B)).mpr (negCount_hasNegIndex hB)

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- The real matrix obtained by casting each rational entry of `A` to the reals. -/
noncomputable def realify {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  A.map (algebraMap ℚ ℝ)

/-- The condition that a rational matrix equals its transpose. -/
def IsSymmRat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Prop := Aᵀ = A

/-- Casting rational matrix entries to the reals preserves matrix multiplication. -/
lemma realify_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℚ) :
    realify (M * N) = realify M * realify N := by
  simp only [realify]
  rw [Matrix.map_mul (f := (algebraMap ℚ ℝ : ℚ →+* ℝ))]

/-- Casting rational matrix entries to the reals preserves subtraction. -/
lemma realify_sub {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℚ) :
    realify (M - N) = realify M - realify N := by
  simp only [realify]
  rw [Matrix.map_sub (algebraMap ℚ ℝ) (fun a b => map_sub (algebraMap ℚ ℝ) a b)]

/-- Casting rational matrix entries to the reals commutes with transposition. -/
lemma realify_transpose {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    realify Mᵀ = (realify M)ᵀ := by
  simp only [realify]
  rw [Matrix.transpose_map]

/-- Casting a rational diagonal matrix to the reals casts its diagonal entries. -/
lemma realify_diagonal {n : ℕ} (d : Fin n → ℚ) :
    realify (diagonal d) = diagonal (fun i => (d i : ℝ)) := by
  simp only [realify]
  rw [Matrix.diagonal_map (map_zero (algebraMap ℚ ℝ))]
  rfl

/-- Casting a rational scalar matrix to the reals casts its scalar. -/
lemma realify_scalar {n : ℕ} (q : ℚ) :
    realify (scalar (Fin n) q) = scalar (Fin n) (q : ℝ) := by
  simp only [Matrix.scalar_apply, realify]
  rw [Matrix.diagonal_map (map_zero (algebraMap ℚ ℝ))]
  rfl

/-- Casting a rational shift to the reals gives the corresponding real scalar shift. -/
lemma realify_shift {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (q : ℚ) :
    realify (shift A q) = realify A - scalar (Fin n) (q : ℝ) := by
  simp only [shift]
  rw [realify_sub, realify_scalar]

/-- The real matrix obtained from a symmetric rational matrix is Hermitian. -/
lemma realify_isHermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} (hA : IsSymmRat A) :
    (realify A).IsHermitian := by
  have hAh : A.IsHermitian := by
    simpa [Matrix.IsHermitian] using! hA
  exact hAh.map (algebraMap ℚ ℝ) (fun x => by simp)

/-- A rational matrix with nonzero determinant retains a nonzero determinant after casting to
the reals. -/
lemma realify_det_ne_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} (h : M.det ≠ 0) :
    (realify M).det ≠ 0 := by
  have hmap : (algebraMap ℚ ℝ) M.det = (realify M).det := by
    simp only [realify]
    exact RingHom.map_det (algebraMap ℚ ℝ) M
  intro h0
  have hz : (algebraMap ℚ ℝ) M.det = 0 := by rw [hmap, h0]
  have hzero : ((M.det : ℚ) : ℝ) = ((0 : ℚ) : ℝ) := by simpa using! hz
  exact h (Rat.cast_injective hzero)

/-- Casting rational diagonal entries to the reals preserves their negative count. -/
lemma negCountDiag_cast {n : ℕ} (d : Fin n → ℚ) :
    negCountDiag (fun i => (d i : ℝ)) = negCountOf d := by
  unfold negCountDiag negCountOf
  congr 1
  apply Finset.filter_congr
  intro i _
  have h := Rat.cast_lt (K := ℝ) (p := d i) (q := 0)
  rwa [Rat.cast_zero] at h

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- Subtracting a real scalar matrix from a real Hermitian matrix preserves the Hermitian
property. -/
lemma isHermitian_shift {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (q : ℝ) : (B - scalar (Fin n) q).IsHermitian := by
  refine isHermitian_of_transpose ?_
  have hBs : Bᵀ = B := by simpa using! hB
  have hcs : (scalar (Fin n) q)ᵀ = scalar (Fin n) q := by
    rw [Matrix.scalar_apply, Matrix.diagonal_transpose]
  rw [Matrix.transpose_sub, hBs, hcs]

/-- Every real diagonal matrix is Hermitian. -/
lemma isHermitian_diagonal_real {n : ℕ} (d : Fin n → ℝ) :
    (diagonal d).IsHermitian := by
  refine isHermitian_of_transpose ?_
  rw [Matrix.diagonal_transpose]

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum
open Matrix

/-- A valid point for a symmetric rational matrix counts exactly the eigenvalues strictly below
its threshold. -/
theorem point_count_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} (hA : IsSymmRat A)
    {p : Point n} (hp : PointValid A p) :
    (Finset.univ.filter fun i => (realify_isHermitian hA).eigenvalues i < (p.q : ℝ)).card
      = negCountOf p.d := by
  have hher : (realify A).IsHermitian := realify_isHermitian hA
  have hcongr : (realify p.M)ᵀ * diagonal (fun i => (p.d i : ℝ)) * realify p.M
      = realify (shift A p.q) := by
    have h := congrArg realify hp.2
    rw [realify_mul, realify_mul, realify_transpose, realify_diagonal] at h
    exact h
  have hB : (diagonal (fun i => (p.d i : ℝ))).IsHermitian := isHermitian_diagonal_real _
  have hc : negCount (realify (shift A p.q)) = negCount (diagonal (fun i => (p.d i : ℝ))) := by
    have h := negCount_congr (B := diagonal (fun i => (p.d i : ℝ))) hB (realify p.M)
      (realify_det_ne_zero hp.1)
    rwa [hcongr] at h
  calc (Finset.univ.filter fun i => (realify_isHermitian hA).eigenvalues i < (p.q : ℝ)).card
      = negCount (realify A - scalar (Fin n) (p.q : ℝ)) :=
        (negCount_shift hher (p.q : ℝ)).symm
    _ = negCount (realify (shift A p.q)) := by rw [realify_shift]
    _ = negCount (diagonal (fun i => (p.d i : ℝ))) := hc
    _ = negCountDiag (fun i => (p.d i : ℝ)) := negCount_diagonal _
    _ = negCountOf p.d := negCountDiag_cast p.d

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- A pairwise relation on a list holds for each consecutive pair in its zip with the
one-element drop. -/
lemma pairwise_of_mem_zip_drop {α : Type*} {r : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise r → ∀ {p q : α}, (p, q) ∈ l.zip (l.drop 1) → r p q := by
  intro l
  induction l with
  | nil => intro h p q hpq; simp at hpq
  | cons a l ih =>
    intro h p q hpq
    cases l with
    | nil => simp at hpq
    | cons b rest =>
      rw [List.pairwise_cons] at h
      have hdrop : (a :: b :: rest).drop 1 = b :: rest := rfl
      rw [hdrop, List.zip_cons_cons] at hpq
      rcases List.mem_cons.mp hpq with hhead | htail
      · rw [Prod.mk.injEq] at hhead
        rw [hhead.1]
        exact h.1 q (by rw [← hhead.2]; exact List.mem_cons_self)
      · exact ih h.2 htail

/-- Membership of a pair in a zip implies membership of each component in its respective list. -/
lemma mem_of_mem_zip {α β : Type*} {l : List α} {l' : List β} {p : α} {q : β}
    (h : (p, q) ∈ l.zip l') : p ∈ l ∧ q ∈ l' := by
  induction l generalizing l' with
  | nil => simp at h
  | cons a t ih =>
    cases l' with
    | nil => simp at h
    | cons b s =>
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | htail
      · exact ⟨List.mem_cons_self, List.mem_cons_self⟩
      · obtain ⟨hp, hq⟩ := ih htail
        exact ⟨List.mem_cons_of_mem a hp, List.mem_cons_of_mem b hq⟩

/-- If no indexed value is strictly below `a`, then every value is at least `a`. -/
lemma le_of_card_filter_lt_eq_zero {n : ℕ} {lam : Fin n → ℝ} {a : ℝ}
    (h : (Finset.univ.filter fun i => lam i < a).card = 0) (i : Fin n) : a ≤ lam i := by
  by_contra hi
  have hmem : i ∈ Finset.univ.filter (fun i => lam i < a) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    linarith [not_le.mp hi]
  have hpos : 0 < (Finset.univ.filter fun i => lam i < a).card :=
    Finset.card_pos.mpr ⟨i, hmem⟩
  omega

/-- If all `n` indices are counted below `a`, then every indexed value is strictly below `a`. -/
lemma lt_of_card_filter_lt_eq_card {n : ℕ} {lam : Fin n → ℝ} {a : ℝ}
    (h : (Finset.univ.filter fun i => lam i < a).card = n) (i : Fin n) : lam i < a := by
  have hle : Finset.univ.filter (fun i => lam i < a) ⊆ Finset.univ := Finset.subset_univ _
  have heq : Finset.univ.filter (fun i => lam i < a) = Finset.univ := by
    refine Finset.eq_of_subset_of_card_le hle ?_
    rw [h, Finset.card_univ, Fintype.card_fin]
  have hmem : i ∈ Finset.univ.filter (fun i => lam i < a) := by
    rw [heq]
    exact Finset.mem_univ i
  simpa using! hmem

/-- A valid certificate for a symmetric rational matrix gives exact eigenvalue counts on
consecutive half-open intervals and bounds every eigenvalue between its endpoint thresholds. -/
theorem certificate_sound {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} (hA : IsSymmRat A)
    {pts : List (Point n)} (hvalid : Valid A pts) :
    (∀ p q, (p, q) ∈ pts.zip (pts.drop 1) →
        (Finset.univ.filter fun i => (p.q : ℝ) ≤ (realify_isHermitian hA).eigenvalues i ∧
          (realify_isHermitian hA).eigenvalues i < (q.q : ℝ)).card = countBetween p q)
    ∧ (∀ a, pts.head? = some a → ∀ b, pts.getLast? = some b → ∀ i,
        (a.q : ℝ) ≤ (realify_isHermitian hA).eigenvalues i ∧
          (realify_isHermitian hA).eigenvalues i < (b.q : ℝ)) := by
  obtain ⟨-, hall, hgrid, houter⟩ := hvalid
  constructor
  · intro p q hpq
    have hppts : p ∈ pts := (mem_of_mem_zip hpq).1
    have hqpts : q ∈ pts := List.mem_of_mem_drop (mem_of_mem_zip hpq).2
    have hpqlt : p.q < q.q := pairwise_of_mem_zip_drop hgrid hpq
    have hle : (p.q : ℝ) ≤ (q.q : ℝ) := by exact_mod_cast le_of_lt hpqlt
    rw [card_filter_interval (fun i => (realify_isHermitian hA).eigenvalues i) hle]
    rw [point_count_eq hA (hall p hppts), point_count_eq hA (hall q hqpts)]
    rfl
  · intro a ha b hb i
    have hcount0 : (Finset.univ.filter fun i =>
        (realify_isHermitian hA).eigenvalues i < (a.q : ℝ)).card = 0 := by
      rw [point_count_eq hA (hall a (List.mem_of_mem_head? (by simpa using! ha)))]
      exact houter.1 a ha
    have hcountn : (Finset.univ.filter fun i =>
        (realify_isHermitian hA).eigenvalues i < (b.q : ℝ)).card = n := by
      rw [point_count_eq hA (hall b (List.mem_of_mem_getLast? (by simpa using! hb)))]
      exact houter.2 b hb
    exact ⟨le_of_card_filter_lt_eq_zero hcount0 i, lt_of_card_filter_lt_eq_card hcountn i⟩

/-- The consecutive point pairs whose negative counts have zero difference. -/
def gapPairs {n : ℕ} (pts : List (Point n)) : List (Point n × Point n) :=
  (pts.zip (pts.drop 1)).filter fun p => countBetween p.1 p.2 = 0

/-- The rational endpoint intervals selected by `gapPairs`. -/
def gapsOf {n : ℕ} (pts : List (Point n)) : List RatInterval :=
  (gapPairs pts).map fun p => ⟨p.1.q, p.2.q⟩

/-- Every interval selected by `gapsOf` from a valid certificate contains no eigenvalue in its
half-open range. -/
theorem gapsOf_sound {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {hA : IsSymmRat A}
    {pts : List (Point n)} (hvalid : Valid A pts) :
    ∀ I ∈ gapsOf pts, ¬ ∃ i, (I.lo : ℝ) ≤ (realify_isHermitian hA).eigenvalues i ∧
      (realify_isHermitian hA).eigenvalues i < (I.hi : ℝ) := by
  intro I hI
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hI
  obtain ⟨hpz, hzero⟩ := List.mem_filter.mp hp
  have hcount := (certificate_sound hA hvalid).1 p.1 p.2 hpz
  rw [of_decide_eq_true hzero] at hcount
  have hempty : (Finset.univ.filter fun i =>
      (p.1.q : ℝ) ≤ (realify_isHermitian hA).eigenvalues i ∧
        (realify_isHermitian hA).eigenvalues i < (p.2.q : ℝ)) = ∅ :=
    Finset.card_eq_zero.mp hcount
  rintro ⟨i, hi⟩
  have hmem : i ∈ Finset.univ.filter (fun i =>
      (p.1.q : ℝ) ≤ (realify_isHermitian hA).eigenvalues i ∧
        (realify_isHermitian hA).eigenvalues i < (p.2.q : ℝ)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  rw [hempty] at hmem
  simp at hmem

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- The single-point Boolean checker returns true exactly when the point is valid. -/
lemma checkPoint_eq_true_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (p : Point n) :
    checkPoint A p = true ↔ PointValid A p := by
  unfold checkPoint PointValid PointCongruent
  rw [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]

/-- The list Boolean checker returns true exactly when the certificate list is valid. -/
lemma checkPoints_eq_true_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (pts : List (Point n)) : checkPoints A pts = true ↔ Valid A pts := by
  unfold checkPoints Valid GridStrict OuterCounts
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨hne, hgrid⟩, hall⟩, hhead⟩, hlast⟩
    refine ⟨?_, ?_, of_decide_eq_true hgrid, ?_⟩
    · intro h
      rw [h] at hne
      simp at hne
    · intro p hp
      exact (checkPoint_eq_true_iff A p).mp (List.all_eq_true.mp hall p hp)
    · constructor
      · intro p hp
        have h := hhead
        rw [hp] at h
        simpa using! h
      · intro p hp
        have h := hlast
        rw [hp] at h
        simpa using! h
  · rintro ⟨hne, hall, hgrid, hhead, hlast⟩
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simpa using! hne
    · exact decide_eq_true hgrid
    · exact List.all_eq_true.mpr fun p hp => (checkPoint_eq_true_iff A p).mpr (hall p hp)
    · cases hh : pts.head? with
      | none =>
        exfalso
        apply hne
        cases pts with
        | nil => rfl
        | cons p t => simp at hh
      | some p =>
        simpa using! hhead p hh
    · cases hl : pts.getLast? with
      | none =>
        exfalso
        apply hne
        cases pts with
        | nil => rfl
        | cons p t => simp at hl
      | some p =>
        simpa using! hlast p hl

/-- The one-by-one rational matrix with entry `a`. -/
def oneByOne (a : ℚ) : Matrix (Fin 1) (Fin 1) ℚ := Matrix.of fun _ _ => a

/-- Every entry of `oneByOne a` equals `a`. -/
@[simp] lemma oneByOne_apply (a : ℚ) (i j : Fin 1) : oneByOne a i j = a := rfl

/-- Multiplication of one-by-one matrices agrees with multiplication of their entries. -/
lemma oneByOne_mul (a b : ℚ) : oneByOne a * oneByOne b = oneByOne (a * b) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [oneByOne, Matrix.mul_apply]

/-- The one-by-one matrix with entry one is the identity. -/
@[simp] lemma oneByOne_one : oneByOne 1 = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [oneByOne]

/-- A one-by-one matrix is unchanged by transposition. -/
@[simp] lemma oneByOne_transpose (a : ℚ) : (oneByOne a)ᵀ = oneByOne a := by
  ext i j
  fin_cases i
  fin_cases j
  simp [oneByOne]

/-- The determinant of a one-by-one matrix is its entry. -/
lemma oneByOne_det (a : ℚ) : (oneByOne a).det = a := by
  rw [Matrix.det_fin_one]
  simp

/-- A one-by-one matrix with nonzero entry is nonzero. -/
lemma oneByOne_ne_zero {a : ℚ} (ha : a ≠ 0) : oneByOne a ≠ 0 := by
  intro h
  have h' : oneByOne a 0 0 = (0 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 := by rw [h]
  exact ha (by simpa [oneByOne] using! h')

/-- A one-by-one matrix with nonzero entry times the matrix of its reciprocal is the identity. -/
lemma oneByOne_mul_inv {r : ℚ} (hr : r ≠ 0) : oneByOne r * oneByOne r⁻¹ = 1 := by
  rw [oneByOne_mul, mul_inv_cancel₀ hr, oneByOne_one]

/-- The matrix of the reciprocal times a one-by-one matrix with nonzero entry is the identity. -/
lemma oneByOne_inv_mul {r : ℚ} (hr : r ≠ 0) : oneByOne r⁻¹ * oneByOne r = 1 := by
  rw [oneByOne_mul, inv_mul_cancel₀ hr, oneByOne_one]

/-- The upper triangular block matrix with identity diagonal blocks and upper-right block `t`. -/
def upperUnit {n : ℕ} (t : Matrix (Fin 1) (Fin n) ℚ) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℚ :=
  fromBlocks 1 t 0 1

/-- The lower triangular block matrix with identity diagonal blocks and lower-left block `s`. -/
def lowerUnit {n : ℕ} (s : Matrix (Fin n) (Fin 1) ℚ) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℚ :=
  fromBlocks 1 0 s 1

/-- Multiplying `upperUnit t` by the upper block shear with parameter `-t` gives the identity. -/
lemma upperUnit_mul_neg {n : ℕ} (t : Matrix (Fin 1) (Fin n) ℚ) :
    upperUnit t * upperUnit (-t) = 1 := by
  rw [upperUnit, upperUnit, fromBlocks_multiply]
  simp

/-- Multiplying the upper block shear with parameter `-t` by `upperUnit t` gives the identity. -/
lemma upperUnit_neg_mul {n : ℕ} (t : Matrix (Fin 1) (Fin n) ℚ) :
    upperUnit (-t) * upperUnit t = 1 := by
  rw [upperUnit, upperUnit, fromBlocks_multiply]
  simp

/-- Multiplying `lowerUnit s` by the lower block shear with parameter `-s` gives the identity. -/
lemma lowerUnit_mul_neg {n : ℕ} (s : Matrix (Fin n) (Fin 1) ℚ) :
    lowerUnit s * lowerUnit (-s) = 1 := by
  rw [lowerUnit, lowerUnit, fromBlocks_multiply]
  simp

/-- Multiplying the lower block shear with parameter `-s` by `lowerUnit s` gives the identity. -/
lemma lowerUnit_neg_mul {n : ℕ} (s : Matrix (Fin n) (Fin 1) ℚ) :
    lowerUnit (-s) * lowerUnit s = 1 := by
  rw [lowerUnit, lowerUnit, fromBlocks_multiply]
  simp

/-- An upper block shear eliminates the off-diagonal row of a symmetric block matrix with
nonzero scalar pivot, leaving its Schur complement. -/
lemma upperUnit_elim {n : ℕ} {r : ℚ} (hr : r ≠ 0)
    (u : Matrix (Fin 1) (Fin n) ℚ) (C : Matrix (Fin n) (Fin n) ℚ) :
    (upperUnit (-(oneByOne r⁻¹ * u)))ᵀ * fromBlocks (oneByOne r) u uᵀ C
        * upperUnit (-(oneByOne r⁻¹ * u))
      = fromBlocks (oneByOne r) 0 0 (C - uᵀ * (oneByOne r⁻¹ * u)) := by
  have h1 : oneByOne r * oneByOne r⁻¹ = 1 := oneByOne_mul_inv hr
  have h2 : oneByOne r⁻¹ * oneByOne r = 1 := oneByOne_inv_mul hr
  have hcross₁ : (-(oneByOne r⁻¹ * u))ᵀ * oneByOne r + uᵀ = 0 := by
    rw [Matrix.transpose_neg, Matrix.transpose_mul, oneByOne_transpose, Matrix.neg_mul,
      Matrix.mul_assoc, h2, Matrix.mul_one, neg_add_cancel]
  have hcross₂ : oneByOne r * (-(oneByOne r⁻¹ * u)) + u = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, h1, Matrix.one_mul, neg_add_cancel]
  have hcorner : (-(oneByOne r⁻¹ * u))ᵀ * u + C = C - uᵀ * (oneByOne r⁻¹ * u) := by
    rw [Matrix.transpose_neg, Matrix.transpose_mul, oneByOne_transpose, Matrix.neg_mul,
      Matrix.mul_assoc, sub_eq_add_neg, add_comm]
  rw [upperUnit, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simpa using! hcross₂
  · simpa using! hcross₁
  · simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    rw [hcross₁, hcorner]
    simp

/-- Congruence by a lower block shear has the displayed block expansion. -/
lemma lowerUnit_conj {n : ℕ} {r : ℚ} (u : Matrix (Fin 1) (Fin n) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (s : Matrix (Fin n) (Fin 1) ℚ) :
    (lowerUnit s)ᵀ * fromBlocks (oneByOne r) u uᵀ C * lowerUnit s
      = fromBlocks (oneByOne r + sᵀ * uᵀ + u * s + sᵀ * C * s)
          (u + sᵀ * C) (uᵀ + C * s) C := by
  rw [lowerUnit, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Matrix.add_mul]
    abel
  · simp
  · simp
  · simp

/-- Every rational one-by-one matrix is determined by its entry at `(0, 0)`. -/
lemma eq_oneByOne_of_fin_one (A : Matrix (Fin 1) (Fin 1) ℚ) : A = oneByOne (A 0 0) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [oneByOne]

/-- Addition of one-by-one matrices agrees with addition of their entries. -/
lemma oneByOne_add (a b : ℚ) : oneByOne a + oneByOne b = oneByOne (a + b) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [oneByOne]

/-- Equality of one-by-one matrices is equivalent to equality of their entries. -/
lemma oneByOne_inj {a b : ℚ} : oneByOne a = oneByOne b ↔ a = b := by
  constructor
  · intro h
    have h' := congrFun (congrFun h 0) 0
    simpa [oneByOne] using! h'
  · intro h
    rw [h]

/-- The one-by-one matrix with entry zero is the zero matrix. -/
lemma oneByOne_zero : oneByOne 0 = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [oneByOne]

/-- Scalar multiplication of a one-by-one matrix multiplies its entry. -/
lemma oneByOne_smul (c a : ℚ) : c • oneByOne a = oneByOne (c * a) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [oneByOne]

/-- The entry of a rational row vector times its transpose is the sum of the squares of its
entries. -/
lemma rowVec_mul_self_apply {n : ℕ} (u : Matrix (Fin 1) (Fin n) ℚ) :
    (u * uᵀ) 0 0 = ∑ j : Fin n, u 0 j * u 0 j := by
  simp [Matrix.mul_apply]

/-- For a nonzero rational row vector, its product with its transpose has nonzero scalar entry. -/
lemma rowVec_mul_self_ne_zero {n : ℕ} {u : Matrix (Fin 1) (Fin n) ℚ} (hu : u ≠ 0) :
    (u * uᵀ) 0 0 ≠ 0 := by
  rw [rowVec_mul_self_apply]
  intro h
  apply hu
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin n)), u 0 j * u 0 j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (u 0 j)).mp h
  ext i j
  have hij : u 0 j * u 0 j = 0 := hterm j (Finset.mem_univ j)
  have hzero : u 0 j = 0 := by simpa using! hij
  have hi : i = 0 := Subsingleton.elim i 0
  rw [hi]
  simpa using! hzero

/-- The scalar entry of `u * C * uᵀ` is the double sum of the corresponding coordinate products. -/
lemma rowVec_conj_apply {n : ℕ} (u : Matrix (Fin 1) (Fin n) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) :
    (u * C * uᵀ) 0 0 = ∑ j : Fin n, ∑ i : Fin n, u 0 i * C i j * u 0 j := by
  simp [Matrix.mul_apply, Finset.sum_mul, mul_assoc]

/-- Congruence by the lower shear with block `c • uᵀ` updates the pivot and off-diagonal blocks
by the displayed formulas. -/
lemma lowerUnit_shear_row {n : ℕ} (r : ℚ) (u : Matrix (Fin 1) (Fin n) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) :
    (lowerUnit (c • uᵀ))ᵀ * fromBlocks (oneByOne r) u uᵀ C * lowerUnit (c • uᵀ)
      = fromBlocks (oneByOne (r + 2 * c * ((u * uᵀ) 0 0) + c ^ 2 * ((u * C * uᵀ) 0 0)))
          (u + c • (u * C)) (uᵀ + c • (C * uᵀ)) C := by
  have htrans : (c • uᵀ)ᵀ = c • u := by
    rw [Matrix.transpose_smul, Matrix.transpose_transpose]
  rw [lowerUnit_conj, htrans, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [fromBlocks_inj]
  refine ⟨?_, rfl, ?_, rfl⟩
  · rw [eq_oneByOne_of_fin_one (u * uᵀ), eq_oneByOne_of_fin_one (u * C * uᵀ)]
    rw [oneByOne_smul, oneByOne_smul, oneByOne_add, oneByOne_add]
    simp only [oneByOne_apply]
    rw [oneByOne_add, oneByOne_inj]
    ring
  · rw [Matrix.mul_smul]

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- Congruence by a rational matrix with nonzero determinant is undone by congruence with its
inverse. -/
theorem conj_inv_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E B : Matrix ι ι ℚ) (hE : E.det ≠ 0) :
    (E⁻¹)ᵀ * (Eᵀ * B * E) * E⁻¹ = B := by
  have hEE : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv E (isUnit_iff_ne_zero.mpr hE)
  have h1 : (E⁻¹)ᵀ * Eᵀ = 1 := by
    rw [← Matrix.transpose_mul, hEE, Matrix.transpose_one]
  calc (E⁻¹)ᵀ * (Eᵀ * B * E) * E⁻¹
      = ((E⁻¹)ᵀ * Eᵀ) * B * (E * E⁻¹) := by noncomm_ring
    _ = B := by rw [h1, hEE]; simp

/-- A diagonal congruence witness for `X` transfers to `B` across the invertible congruence `Eᵀ
* B * E = X`. -/
theorem diagonalization_of_congruent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B X : Matrix ι ι ℚ} {E : Matrix ι ι ℚ} (hE : E.det ≠ 0)
    {M : Matrix ι ι ℚ} {d : ι → ℚ}
    (hM : M.det ≠ 0) (hX : Mᵀ * diagonal d * M = X) (h : Eᵀ * B * E = X) :
    (M * E⁻¹).det ≠ 0 ∧ (M * E⁻¹)ᵀ * diagonal d * (M * E⁻¹) = B := by
  constructor
  · rw [Matrix.det_mul]
    refine mul_ne_zero hM ?_
    intro h0
    have hdet : E⁻¹.det * E.det = 1 :=
      Matrix.det_nonsing_inv_mul_det E (isUnit_iff_ne_zero.mpr hE)
    rw [h0, zero_mul] at hdet
    exact zero_ne_one hdet
  · rw [Matrix.transpose_mul]
    calc (E⁻¹)ᵀ * Mᵀ * diagonal d * (M * E⁻¹)
        = (E⁻¹)ᵀ * (Mᵀ * diagonal d * M) * E⁻¹ := by noncomm_ring
      _ = (E⁻¹)ᵀ * X * E⁻¹ := by rw [hX]
      _ = (E⁻¹)ᵀ * (Eᵀ * B * E) * E⁻¹ := by rw [← h]
      _ = B := conj_inv_eq E B hE

/-- The inverse of an upper block shear is the shear with negated parameter. -/
lemma upperUnit_inv {n : ℕ} (t : Matrix (Fin 1) (Fin n) ℚ) :
    (upperUnit t)⁻¹ = upperUnit (-t) :=
  Matrix.inv_eq_left_inv (A := upperUnit t) (upperUnit_neg_mul t)

/-- The inverse of the upper block shear with negated parameter is the original shear. -/
lemma upperUnit_neg_inv {n : ℕ} (t : Matrix (Fin 1) (Fin n) ℚ) :
    (upperUnit (-t))⁻¹ = upperUnit t :=
  Matrix.inv_eq_left_inv (A := upperUnit (-t)) (upperUnit_mul_neg t)

/-- The inverse of a lower block shear is the shear with negated parameter. -/
lemma lowerUnit_inv {n : ℕ} (s : Matrix (Fin n) (Fin 1) ℚ) :
    (lowerUnit s)⁻¹ = lowerUnit (-s) :=
  Matrix.inv_eq_left_inv (A := lowerUnit s) (lowerUnit_neg_mul s)

/-- A diagonal vector on `Fin 1 ⊕ Fin n` splits into a scalar diagonal block and its remaining
diagonal block. -/
lemma diagonal_sumElim {n : ℕ} (r : ℚ) (d : Fin n → ℚ) :
    diagonal (Sum.elim (fun _ => r) d) = fromBlocks (oneByOne r) 0 0 (diagonal d) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · have hij : i = j := Subsingleton.elim i j
    subst hij
    simp [oneByOne]
  · simp [Matrix.diagonal]
  · simp [Matrix.diagonal]
  · simp [Matrix.diagonal]

/-- Congruence by a block diagonal matrix with first block the identity acts only on the
trailing diagonal block. -/
lemma blockDiag_one_mul {n : ℕ} (M₂ : Matrix (Fin n) (Fin n) ℚ) (r : ℚ) (d : Fin n → ℚ) :
    (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 M₂)ᵀ
        * fromBlocks (oneByOne r) 0 0 (diagonal d)
        * fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 M₂
      = fromBlocks (oneByOne r) 0 0 (M₂ᵀ * diagonal d * M₂) := by
  rw [fromBlocks_transpose]
  simp only [Matrix.transpose_one, Matrix.transpose_zero]
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- The leading scalar entry of a matrix indexed by `Fin 1 ⊕ Fin n`. -/
def blockPivot {n : ℕ} (B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℚ) : ℚ :=
  B (Sum.inl 0) (Sum.inl 0)

/-- The upper-right row block of a matrix indexed by `Fin 1 ⊕ Fin n`. -/
def blockRow {n : ℕ} (B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℚ) :
    Matrix (Fin 1) (Fin n) ℚ :=
  Matrix.of fun _ j => B (Sum.inl 0) (Sum.inr j)

/-- The trailing square block of a matrix indexed by `Fin 1 ⊕ Fin n`. -/
def blockTail {n : ℕ} (B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => B (Sum.inr i) (Sum.inr j)

/-- A symmetric matrix on `Fin 1 ⊕ Fin n` is reconstructed from its pivot, row block, and
trailing block. -/
lemma fromBlocks_block {n : ℕ} {B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℚ}
    (hB : Bᵀ = B) :
    B = fromBlocks (oneByOne (blockPivot B)) (blockRow B) (blockRow B)ᵀ (blockTail B) := by
  conv_lhs => rw [← fromBlocks_toBlocks B]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, rfl⟩
  · exact eq_oneByOne_of_fin_one B.toBlocks₁₁
  · ext i j
    fin_cases i
    rfl
  · ext i j
    fin_cases j
    have h := congrFun (congrFun hB (Sum.inl 0)) (Sum.inr i)
    simpa [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.transpose_apply, blockRow] using! h

/-- The trailing block of a symmetric rational block matrix is symmetric. -/
lemma blockTail_transpose {n : ℕ} {B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℚ}
    (hB : Bᵀ = B) : (blockTail B)ᵀ = blockTail B := by
  ext i j
  have h := congrFun (congrFun hB (Sum.inr j)) (Sum.inr i)
  simpa [blockTail, Matrix.transpose_apply] using! h.symm

/-- Subtracting the symmetric rank-one term `uᵀ * (oneByOne q * u)` from a symmetric matrix
preserves symmetry. -/
lemma schur_transpose {n : ℕ} {C : Matrix (Fin n) (Fin n) ℚ} (hC : Cᵀ = C)
    (u : Matrix (Fin 1) (Fin n) ℚ) (q : ℚ) :
    (C - uᵀ * (oneByOne q * u))ᵀ = C - uᵀ * (oneByOne q * u) := by
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, oneByOne_transpose,
    Matrix.transpose_transpose, hC, Matrix.mul_assoc]

/-- Transposition of the sheared row has the stated column expression when the trailing matrix
is symmetric. -/
lemma row_shear_transpose {n : ℕ} {u : Matrix (Fin 1) (Fin n) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} (hC : Cᵀ = C) (c : ℚ) :
    (u + c • (u * C))ᵀ = uᵀ + c • (C * uᵀ) := by
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul, hC]

/-- The operation count `2 * n ^ 2 + n + 1` assigned to scalar-pivot elimination with trailing
dimension `n`. -/
def elimOps (n : ℕ) : ℕ := 2 * n ^ 2 + n + 1

/-- The operation count `2 * n ^ 2 + 5 * n + 7` assigned to preparing a shear. -/
def shearPrepOps (n : ℕ) : ℕ := 2 * n ^ 2 + 5 * n + 7

/-- The operation count `2 * n * (n + 1)` assigned to assembling a sheared witness. -/
def shearAssemblyOps (n : ℕ) : ℕ := 2 * n * (n + 1)

/-- The combined operation count for elimination, shear preparation, and shear assembly. -/
def shearOps (n : ℕ) : ℕ := elimOps n + shearPrepOps n + shearAssemblyOps n

/-- A rational diagonal congruence witness with a matrix of nonzero determinant, diagonal
entries, and stored step and operation counts. -/
structure DiagWitness {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℚ) where

  M : Matrix ι ι ℚ

  d : ι → ℚ

  hinv : M.det ≠ 0

  hdiag : Mᵀ * diagonal d * M = B

  steps : ℕ

  ops : ℕ

/-- Extends a Schur-complement diagonalization witness across a nonzero scalar pivot. -/
def diagWitness_pivot {n : ℕ} {r : ℚ} (hr : r ≠ 0) (u : Matrix (Fin 1) (Fin n) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (w : DiagWitness (C - uᵀ * (oneByOne r⁻¹ * u))) :
    DiagWitness (fromBlocks (oneByOne r) u uᵀ C) := by
  have hE : (upperUnit (-(oneByOne r⁻¹ * u))).det ≠ 0 := by
    rw [upperUnit, Matrix.det_fromBlocks_zero₂₁]
    simp
  have hM : (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 w.M).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₁₂]
    simpa using! w.hinv
  have hX : (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 w.M)ᵀ
      * diagonal (Sum.elim (fun _ => r) w.d)
      * fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 w.M
      = fromBlocks (oneByOne r) 0 0 (C - uᵀ * (oneByOne r⁻¹ * u)) := by
    rw [diagonal_sumElim, blockDiag_one_mul, w.hdiag]
  have h := diagonalization_of_congruent
    (B := fromBlocks (oneByOne r) u uᵀ C)
    (X := fromBlocks (oneByOne r) 0 0 (C - uᵀ * (oneByOne r⁻¹ * u)))
    (E := upperUnit (-(oneByOne r⁻¹ * u))) (M := fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 w.M)
    (d := Sum.elim (fun _ => r) w.d) hE hM hX (upperUnit_elim hr u C)
  rw [upperUnit_neg_inv] at h
  exact
    { M := fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 w.M * upperUnit (oneByOne r⁻¹ * u)
      d := Sum.elim (fun _ => r) w.d
      hinv := h.1
      hdiag := h.2
      steps := w.steps + 1
      ops := w.ops + elimOps n }

/-- The congruence matrix of the pivot witness is the block extension of `w.M` followed by the
inverse elimination shear. -/
@[simp] lemma diagWitness_pivot_M {n : ℕ} {r : ℚ} (hr : r ≠ 0)
    (u : Matrix (Fin 1) (Fin n) ℚ) (C : Matrix (Fin n) (Fin n) ℚ)
    (w : DiagWitness (C - uᵀ * (oneByOne r⁻¹ * u))) :
    (diagWitness_pivot hr u C w).M
      = fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 w.M * upperUnit (oneByOne r⁻¹ * u) :=
  rfl

/-- The diagonal vector of the pivot witness prepends the scalar pivot to `w.d`. -/
@[simp] lemma diagWitness_pivot_d {n : ℕ} {r : ℚ} (hr : r ≠ 0)
    (u : Matrix (Fin 1) (Fin n) ℚ) (C : Matrix (Fin n) (Fin n) ℚ)
    (w : DiagWitness (C - uᵀ * (oneByOne r⁻¹ * u))) :
    (diagWitness_pivot hr u C w).d = Sum.elim (fun _ => r) w.d :=
  rfl

/-- Extending a witness across a scalar pivot adds one to its stored step count. -/
@[simp] lemma diagWitness_pivot_steps {n : ℕ} {r : ℚ} (hr : r ≠ 0)
    (u : Matrix (Fin 1) (Fin n) ℚ) (C : Matrix (Fin n) (Fin n) ℚ)
    (w : DiagWitness (C - uᵀ * (oneByOne r⁻¹ * u))) :
    (diagWitness_pivot hr u C w).steps = w.steps + 1 := rfl

/-- Extends a diagonalization witness by a zero pivot when the off-diagonal row is zero. -/
def diagWitness_zero {n : ℕ} {u : Matrix (Fin 1) (Fin n) ℚ} {C : Matrix (Fin n) (Fin n) ℚ}
    (hu : u = 0) (w : DiagWitness C) :
    DiagWitness (fromBlocks (oneByOne 0) u uᵀ C) := by
  refine
    { M := fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 w.M
      d := Sum.elim (fun _ => (0 : ℚ)) w.d
      hinv := ?_
      hdiag := ?_
      steps := w.steps + 1
      ops := w.ops }
  · rw [Matrix.det_fromBlocks_zero₁₂]
    simpa using! w.hinv
  · rw [hu, Matrix.transpose_zero, diagonal_sumElim, blockDiag_one_mul, w.hdiag]

/-- The congruence matrix of the zero-pivot extension is block diagonal with first block the
identity. -/
@[simp] lemma diagWitness_zero_M {n : ℕ} {u : Matrix (Fin 1) (Fin n) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} (hu : u = 0) (w : DiagWitness C) :
    (diagWitness_zero hu w).M = fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 w.M :=
  rfl

/-- The zero-pivot extension prepends zero to the diagonal vector. -/
@[simp] lemma diagWitness_zero_d {n : ℕ} {u : Matrix (Fin 1) (Fin n) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} (hu : u = 0) (w : DiagWitness C) :
    (diagWitness_zero hu w).d = Sum.elim (fun _ => (0 : ℚ)) w.d :=
  rfl

/-- The zero-pivot extension adds one to the stored step count. -/
@[simp] lemma diagWitness_zero_steps {n : ℕ} {u : Matrix (Fin 1) (Fin n) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} (hu : u = 0) (w : DiagWitness C) :
    (diagWitness_zero hu w).steps = w.steps + 1 := rfl

/-- Builds a diagonal congruence witness by applying a shear that produces a nonzero pivot and
then extending a Schur-complement witness. -/
def diagWitness_shear {n : ℕ} {r : ℚ} {u : Matrix (Fin 1) (Fin n) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} (hC : Cᵀ = C) {c : ℚ} {r' : ℚ}
    {u' : Matrix (Fin 1) (Fin n) ℚ}
    (hr' : r' = r + 2 * c * ((u * uᵀ) 0 0) + c ^ 2 * ((u * C * uᵀ) 0 0))
    (hu' : u' = u + c • (u * C)) (hne : r' ≠ 0)
    (w : DiagWitness (C - u'ᵀ * (oneByOne r'⁻¹ * u'))) :
    DiagWitness (fromBlocks (oneByOne r) u uᵀ C) := by
  have hE : (lowerUnit (c • uᵀ)).det ≠ 0 := by
    rw [lowerUnit, Matrix.det_fromBlocks_zero₁₂]
    simp
  have hcongr : (lowerUnit (c • uᵀ))ᵀ * fromBlocks (oneByOne r) u uᵀ C * lowerUnit (c • uᵀ)
      = fromBlocks (oneByOne r') u' u'ᵀ C := by
    rw [lowerUnit_shear_row, ← row_shear_transpose hC c, ← hu', ← hr']
  have wp := diagWitness_pivot (r := r') hne u' C w
  have h := diagonalization_of_congruent
    (B := fromBlocks (oneByOne r) u uᵀ C) (X := fromBlocks (oneByOne r') u' u'ᵀ C)
    (E := lowerUnit (c • uᵀ)) (M := wp.M) (d := wp.d) hE wp.hinv wp.hdiag hcongr
  rw [lowerUnit_inv] at h
  exact
    { M := wp.M * lowerUnit (-(c • uᵀ))
      d := wp.d
      hinv := h.1
      hdiag := h.2
      steps := wp.steps
      ops := w.ops + shearOps n }

/-- The congruence matrix of the shear witness is the pivot witness matrix multiplied by the
inverse lower shear. -/
@[simp] lemma diagWitness_shear_M {n : ℕ} {r : ℚ} {u : Matrix (Fin 1) (Fin n) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} (hC : Cᵀ = C) {c : ℚ} {r' : ℚ}
    {u' : Matrix (Fin 1) (Fin n) ℚ}
    (hr' : r' = r + 2 * c * ((u * uᵀ) 0 0) + c ^ 2 * ((u * C * uᵀ) 0 0))
    (hu' : u' = u + c • (u * C)) (hne : r' ≠ 0)
    (w : DiagWitness (C - u'ᵀ * (oneByOne r'⁻¹ * u'))) :
    (diagWitness_shear hC hr' hu' hne w).M
      = (diagWitness_pivot (r := r') hne u' C w).M * lowerUnit (-(c • uᵀ)) :=
  rfl

/-- The shear witness uses the same diagonal vector as the corresponding pivot witness. -/
@[simp] lemma diagWitness_shear_d {n : ℕ} {r : ℚ} {u : Matrix (Fin 1) (Fin n) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} (hC : Cᵀ = C) {c : ℚ} {r' : ℚ}
    {u' : Matrix (Fin 1) (Fin n) ℚ}
    (hr' : r' = r + 2 * c * ((u * uᵀ) 0 0) + c ^ 2 * ((u * C * uᵀ) 0 0))
    (hu' : u' = u + c • (u * C)) (hne : r' ≠ 0)
    (w : DiagWitness (C - u'ᵀ * (oneByOne r'⁻¹ * u'))) :
    (diagWitness_shear hC hr' hu' hne w).d
      = (diagWitness_pivot (r := r') hne u' C w).d :=
  rfl

/-- The shear construction adds one to the trailing witness's stored step count. -/
@[simp] lemma diagWitness_shear_steps {n : ℕ} {r : ℚ} {u : Matrix (Fin 1) (Fin n) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} (hC : Cᵀ = C) {c : ℚ} {r' : ℚ}
    {u' : Matrix (Fin 1) (Fin n) ℚ}
    (hr' : r' = r + 2 * c * ((u * uᵀ) 0 0) + c ^ 2 * ((u * C * uᵀ) 0 0))
    (hu' : u' = u + c • (u * C)) (hne : r' ≠ 0)
    (w : DiagWitness (C - u'ᵀ * (oneByOne r'⁻¹ * u'))) :
    (diagWitness_shear hC hr' hu' hne w).steps = w.steps + 1 := rfl

/-- Reindexing a diagonal matrix along an equivalence composes its diagonal vector with that
equivalence. -/
lemma reindex_diagonal {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (d : κ → ℚ) :
    Matrix.reindex e.symm e.symm (diagonal d) = diagonal (d ∘ e) := by
  rw [Matrix.reindex_apply]
  exact Matrix.submatrix_diagonal_equiv d e

/-- Reindexing a diagonal congruence reindexes its matrix and composes its diagonal vector with
the equivalence. -/
lemma reindex_conj {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (M : Matrix κ κ ℚ) (d : κ → ℚ) :
    Matrix.reindex e.symm e.symm (Mᵀ * diagonal d * M)
      = (Matrix.reindex e.symm e.symm M)ᵀ * diagonal (d ∘ e)
        * Matrix.reindex e.symm e.symm M := by
  have hmul : ∀ (P Q : Matrix κ κ ℚ),
      Matrix.reindex e.symm e.symm (P * Q)
        = Matrix.reindex e.symm e.symm P * Matrix.reindex e.symm e.symm Q := fun P Q =>
    Matrix.reindexAlgEquiv_mul (R := ℚ) (A := ℚ) (e := e.symm) (M := P) (N := Q)
  rw [Matrix.transpose_reindex, hmul, hmul, ← reindex_diagonal]

/-- Reindexing a matrix along an equivalence and then its inverse recovers the matrix. -/
lemma reindex_symm_reindex {ι κ : Type*} (e : ι ≃ κ) (A : Matrix ι ι ℚ) :
    Matrix.reindex e.symm e.symm (Matrix.reindex e e A) = A := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply]
  simp

/-- Transfers a diagonal congruence witness from a reindexed matrix back to its original index
type. -/
def diagWitness_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) {B : Matrix ι ι ℚ} {w : DiagWitness (Matrix.reindex e e B)} :
    DiagWitness B :=
  { M := Matrix.reindex e.symm e.symm w.M
    d := w.d ∘ e
    hinv := by
      rw [Matrix.reindex_apply, Matrix.det_submatrix_equiv_self]
      exact w.hinv
    hdiag := by
      rw [← reindex_conj e w.M w.d, w.hdiag, reindex_symm_reindex e B]
    steps := w.steps
    ops := w.ops }

/-- The matrix of a transferred witness is obtained by reindexing the original witness matrix
along the inverse equivalence. -/
@[simp] lemma diagWitness_reindex_M {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {B : Matrix ι ι ℚ}
    {w : DiagWitness (Matrix.reindex e e B)} :
    (diagWitness_reindex e (w := w)).M = Matrix.reindex e.symm e.symm w.M := rfl

/-- The diagonal vector of a transferred witness is the original diagonal vector composed with
the equivalence. -/
@[simp] lemma diagWitness_reindex_d {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {B : Matrix ι ι ℚ}
    {w : DiagWitness (Matrix.reindex e e B)} :
    (diagWitness_reindex e (w := w)).d = w.d ∘ e := rfl

/-- Transferring a witness across an index equivalence preserves its stored step count. -/
@[simp] lemma diagWitness_reindex_steps {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {B : Matrix ι ι ℚ}
    {w : DiagWitness (Matrix.reindex e e B)} :
    (diagWitness_reindex e (w := w)).steps = w.steps := rfl

/-- The equivalence splitting `Fin (n + 1)` into a singleton index and `Fin n`. -/
def finSplit (n : ℕ) : Fin (n + 1) ≃ Fin 1 ⊕ Fin n :=
  (finSumFinEquiv.trans (finCongr (Nat.one_add n))).symm

/-- A symmetric block matrix with zero leading pivot is reconstructed with an explicitly zero
scalar block. -/
lemma fromBlocks_block_zero {n : ℕ} {B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℚ}
    (hB : Bᵀ = B) (h0 : blockPivot B = 0) :
    B = fromBlocks (oneByOne 0) (blockRow B) (blockRow B)ᵀ (blockTail B) := by
  conv_lhs => rw [fromBlocks_block hB]
  rw [h0]

/-- Chooses a rational coefficient, either one or two, making `2 * c * a + c ^ 2 * b` nonzero
when `a` is nonzero. -/
def shearCoeff (a b : ℚ) (ha : a ≠ 0) : {c : ℚ // 2 * c * a + c ^ 2 * b ≠ 0} :=
  if h : 2 * a + b ≠ 0 then ⟨1, by simpa using! h⟩
  else
    ⟨2, by
      have h2 : 2 * a + b = 0 := not_not.mp h
      intro hc
      apply ha
      linarith⟩

/-- Recursively constructs a rational diagonal congruence witness for a symmetric rational
matrix, using a shear when a zero pivot has a nonzero row. -/
def diagAux : (n : ℕ) → (B : Matrix (Fin n) (Fin n) ℚ) → IsSymmRat B → DiagWitness B
  | 0, _, _ =>
    { M := 1
      d := fun i => i.elim0
      hinv := by simp
      hdiag := by
        ext i j
        exact i.elim0
      steps := 0
      ops := 0 }
  | n + 1, B, hB => by
    let e := finSplit n
    let B' := Matrix.reindex e e B
    have hB' : B'ᵀ = B' := by
      rw [show B' = Matrix.reindex e e B from rfl, Matrix.transpose_reindex, hB]
    have hdec : B' = fromBlocks (oneByOne (blockPivot B')) (blockRow B') (blockRow B')ᵀ
        (blockTail B') := fromBlocks_block hB'
    have hC : (blockTail B')ᵀ = blockTail B' := blockTail_transpose hB'
    by_cases hr : blockPivot B' ≠ 0
    · let Cd := blockTail B' - (blockRow B')ᵀ * (oneByOne (blockPivot B')⁻¹ * blockRow B')
      let hCd : IsSymmRat Cd := schur_transpose hC (blockRow B') (blockPivot B')⁻¹
      let w := diagAux n Cd hCd
      have hwb : DiagWitness (fromBlocks (oneByOne (blockPivot B')) (blockRow B')
          (blockRow B')ᵀ (blockTail B')) :=
        diagWitness_pivot hr (blockRow B') (blockTail B') w
      have hwb' : DiagWitness B' := hdec.symm ▸ hwb
      exact diagWitness_reindex e (w := hwb')
    · by_cases hu : blockRow B' = 0
      · let w := diagAux n (blockTail B') hC
        have hwb : DiagWitness (fromBlocks (oneByOne 0) (blockRow B') (blockRow B')ᵀ
            (blockTail B')) :=
          diagWitness_zero hu w
        have hdec0 : B' = fromBlocks (oneByOne 0) (blockRow B') (blockRow B')ᵀ
            (blockTail B') := fromBlocks_block_zero hB' (not_not.mp hr)
        have hwb' : DiagWitness B' := hdec0.symm ▸ hwb
        exact diagWitness_reindex e (w := hwb')
      · let a : ℚ := ((blockRow B') * (blockRow B')ᵀ) 0 0
        let b : ℚ := ((blockRow B') * (blockTail B') * (blockRow B')ᵀ) 0 0
        have ha : a ≠ 0 := rowVec_mul_self_ne_zero hu
        let sc := shearCoeff a b ha
        let c : ℚ := sc.1
        have hc2 : 2 * c * a + c ^ 2 * b ≠ 0 := sc.2
        have hr0 : blockPivot B' = 0 := not_not.mp hr
        have hne : blockPivot B' + 2 * c * a + c ^ 2 * b ≠ 0 := by
          rw [hr0, zero_add]
          exact hc2
        let u' := blockRow B' + c • (blockRow B' * blockTail B')
        let Cd := blockTail B' - u'ᵀ * (oneByOne (blockPivot B' + 2 * c * a + c ^ 2 * b)⁻¹ * u')
        let hCd : IsSymmRat Cd := schur_transpose hC u' _
        let w := diagAux n Cd hCd
        have hwb : DiagWitness (fromBlocks (oneByOne (blockPivot B')) (blockRow B')
            (blockRow B')ᵀ (blockTail B')) :=
          diagWitness_shear (r := blockPivot B') (C := blockTail B') hC (c := c)
            (r' := blockPivot B' + 2 * c * a + c ^ 2 * b) (u' := u') rfl rfl hne w
        have hwb' : DiagWitness B' := hdec.symm ▸ hwb
        exact diagWitness_reindex e (w := hwb')

/-- Transporting a diagonalization witness along an equality of matrices preserves its stored
step count. -/
lemma DiagWitness.steps_cast {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B B' : Matrix ι ι ℚ} (h : B = B') (w : DiagWitness B) :
    (h ▸ w).steps = w.steps := by
  cases h
  rfl

/-- The witness produced by `diagAux` for an `n`-dimensional matrix has stored step count `n`. -/
theorem diagAux_steps (n : ℕ) :
    ∀ (B : Matrix (Fin n) (Fin n) ℚ) (hB : IsSymmRat B), (diagAux n B hB).steps = n := by
  induction n with
  | zero =>
    intro B hB
    rfl
  | succ n ih =>
    intro B hB
    rw [diagAux]
    (try dsimp only)
    split
    · simp only [diagWitness_reindex_steps, DiagWitness.steps_cast,
        diagWitness_pivot_steps]
      rw [ih]
    · split
      · simp only [diagWitness_reindex_steps, DiagWitness.steps_cast,
          diagWitness_zero_steps]
        rw [ih]
      · simp only [diagWitness_reindex_steps, DiagWitness.steps_cast,
          diagWitness_shear_steps]
        rw [ih]

/-- Extending a witness across a nonzero pivot adds `elimOps n` to its stored operation count. -/
@[simp] lemma diagWitness_pivot_ops {n : ℕ} {r : ℚ} (hr : r ≠ 0)
    (u : Matrix (Fin 1) (Fin n) ℚ) (C : Matrix (Fin n) (Fin n) ℚ)
    (w : DiagWitness (C - uᵀ * (oneByOne r⁻¹ * u))) :
    (diagWitness_pivot hr u C w).ops = w.ops + elimOps n := rfl

/-- Extending a witness across a zero pivot and zero row preserves its stored operation count. -/
@[simp] lemma diagWitness_zero_ops {n : ℕ} {u : Matrix (Fin 1) (Fin n) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} (hu : u = 0) (w : DiagWitness C) :
    (diagWitness_zero hu w).ops = w.ops := rfl

/-- The shear construction adds `shearOps n` to the trailing witness's stored operation count. -/
@[simp] lemma diagWitness_shear_ops {n : ℕ} {r : ℚ} {u : Matrix (Fin 1) (Fin n) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} (hC : Cᵀ = C) {c : ℚ} {r' : ℚ}
    {u' : Matrix (Fin 1) (Fin n) ℚ}
    (hr' : r' = r + 2 * c * ((u * uᵀ) 0 0) + c ^ 2 * ((u * C * uᵀ) 0 0))
    (hu' : u' = u + c • (u * C)) (hne : r' ≠ 0)
    (w : DiagWitness (C - u'ᵀ * (oneByOne r'⁻¹ * u'))) :
    (diagWitness_shear hC hr' hu' hne w).ops = w.ops + shearOps n := rfl

/-- Transferring a diagonalization witness across an index equivalence preserves its stored
operation count. -/
@[simp] lemma diagWitness_reindex_ops {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {B : Matrix ι ι ℚ}
    {w : DiagWitness (Matrix.reindex e e B)} :
    (diagWitness_reindex e (w := w)).ops = w.ops := rfl

/-- Transporting a diagonalization witness along a matrix equality preserves its stored
operation count. -/
lemma DiagWitness.ops_cast {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B B' : Matrix ι ι ℚ} (h : B = B') (w : DiagWitness B) :
    (h ▸ w).ops = w.ops := by
  cases h
  rfl

/-- The cumulative operation bound obtained by summing `shearOps` over successive trailing
dimensions. -/
def opsBound : ℕ → ℕ
  | 0 => 0
  | n + 1 => opsBound n + shearOps n

/-- The scalar-pivot elimination count is at most the full shear count. -/
lemma elimOps_le_shearOps (n : ℕ) : elimOps n ≤ shearOps n := by
  unfold shearOps
  omega

/-- The stored operation count of the witness produced by `diagAux` is bounded by `opsBound n`. -/
theorem diagAux_ops_le (n : ℕ) :
    ∀ (B : Matrix (Fin n) (Fin n) ℚ) (hB : IsSymmRat B),
      (diagAux n B hB).ops ≤ opsBound n := by
  induction n with
  | zero =>
    intro B hB
    exact Nat.zero_le _
  | succ n ih =>
    intro B hB
    rw [diagAux]
    (try dsimp only)
    split
    · simp only [diagWitness_reindex_ops, DiagWitness.ops_cast, diagWitness_pivot_ops]
      rw [show opsBound (n + 1) = opsBound n + shearOps n from rfl]
      exact (Nat.add_le_add_right (ih _ _) (elimOps n)).trans
        (Nat.add_le_add_left (elimOps_le_shearOps n) (opsBound n))
    · split
      · simp only [diagWitness_reindex_ops, DiagWitness.ops_cast, diagWitness_zero_ops]
        rw [show opsBound (n + 1) = opsBound n + shearOps n from rfl]
        exact (ih _ _).trans (Nat.le_add_right (opsBound n) (shearOps n))
      · simp only [diagWitness_reindex_ops, DiagWitness.ops_cast, diagWitness_shear_ops]
        rw [show opsBound (n + 1) = opsBound n + shearOps n from rfl]
        exact Nat.add_le_add_right (ih _ _) (shearOps n)

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- A rational scalar shift of a symmetric rational matrix remains symmetric. -/
lemma shift_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} (hA : IsSymmRat A) (q : ℚ) :
    IsSymmRat (shift A q) := by
  unfold IsSymmRat shift
  rw [Matrix.transpose_sub, hA, Matrix.scalar_apply, Matrix.diagonal_transpose]

/-- Constructs a certificate point at `q` using the rational diagonalization of `shift A q`. -/
def pointOf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A) (q : ℚ) : Point n :=
  let w := diagAux n (shift A q) (shift_symm hA q)
  { q := q, M := w.M, d := w.d }

/-- The point constructed by `pointOf` is valid. -/
theorem pointOf_valid {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A) (q : ℚ) :
    PointValid A (pointOf A hA q) :=
  ⟨(diagAux n (shift A q) (shift_symm hA q)).hinv,
    (diagAux n (shift A q) (shift_symm hA q)).hdiag⟩

/-- The negative diagonal count of `pointOf A hA q` is exactly the number of eigenvalues below
`q`. -/
theorem pointOf_count {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A) (q : ℚ) :
    (Finset.univ.filter fun i =>
        (realify_isHermitian hA).eigenvalues i < (q : ℝ)).card
      = negCountOf (pointOf A hA q).d :=
  point_count_eq hA (pointOf_valid A hA q)

/-- A zero negative count at the constructed point implies that every eigenvalue is at least its
threshold. -/
theorem pointOf_le_of_count_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsSymmRat A) (q : ℚ) (h : negCountOf (pointOf A hA q).d = 0) (i : Fin n) :
    (q : ℝ) ≤ (realify_isHermitian hA).eigenvalues i :=
  le_of_card_filter_lt_eq_zero (by rw [pointOf_count A hA q, h]) i

/-- A negative count equal to the matrix dimension at the constructed point implies that every
eigenvalue is below its threshold. -/
theorem pointOf_lt_of_count_card {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsSymmRat A) (q : ℚ) (h : negCountOf (pointOf A hA q).d = n) (i : Fin n) :
    (realify_isHermitian hA).eigenvalues i < (q : ℝ) :=
  lt_of_card_filter_lt_eq_card (by rw [pointOf_count A hA q, h]) i

/-- Constructs certificate points for a symmetric rational matrix at each threshold in a list. -/
def ptsOf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A) (qs : List ℚ) :
    List (Point n) :=
  qs.map (pointOf A hA)

/-- A nonempty increasing threshold list with the required endpoint counts yields a certificate
accepted by `checkPoints`. -/
theorem checkPoints_ptsOf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    {qs : List ℚ} (hne : qs ≠ []) (hgrid : qs.Pairwise (· < ·))
    (hfirst : ∀ q, qs.head? = some q → negCountOf (pointOf A hA q).d = 0)
    (hlast : ∀ q, qs.getLast? = some q → negCountOf (pointOf A hA q).d = n) :
    checkPoints A (ptsOf A hA qs) = true := by
  rw [checkPoints_eq_true_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [ptsOf, hne]
  · intro p hp
    simp only [ptsOf, List.mem_map] at hp
    obtain ⟨q, -, rfl⟩ := hp
    exact pointOf_valid A hA q
  · simp only [ptsOf, GridStrict]
    rw [List.pairwise_map]
    simpa using! hgrid
  · constructor
    · intro p hp
      simp only [ptsOf, List.head?_map] at hp
      cases hq : qs.head? with
      | none => simp [hq] at hp
      | some q =>
        simp [hq] at hp
        subst hp
        simpa [pointOf] using! hfirst q hq
    · intro p hp
      simp only [ptsOf, List.getLast?_map] at hp
      cases hq : qs.getLast? with
      | none => simp [hq] at hp
      | some q =>
        simp [hq] at hp
        subst hp
        simpa [pointOf] using! hlast q hq

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- The sum of the absolute values of all entries of a rational matrix. -/
def absSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : ℚ :=
  ∑ i, ∑ j, |A i j|

/-- The sum of absolute values of matrix entries is nonnegative. -/
lemma absSum_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : 0 ≤ absSum A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Each absolute row sum is at most the sum of the absolute values of all matrix entries. -/
lemma abs_row_le_absSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) :
    (∑ j, |A i j|) ≤ absSum A :=
  Finset.single_le_sum (f := fun i' => ∑ j', |A i' j'|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- The absolute value of each matrix entry is at most `absSum A`. -/
lemma abs_apply_le_absSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    |A i j| ≤ absSum A :=
  (Finset.single_le_sum (f := fun j' => |A i j'|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ j)).trans (abs_row_le_absSum A i)

/-- Each entry of `realify A` is the real cast of the corresponding entry of `A`. -/
lemma realify_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    realify A i j = (A i j : ℝ) := by
  simp [realify]

/-- A uniform bound on the absolute row sums of a real Hermitian matrix bounds the absolute
value of every eigenvalue. -/
theorem abs_eigenvalue_le_of_row_sum {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) {R : ℝ} (hrow : ∀ i, ∑ k, |M i k| ≤ R) (j : Fin n) :
    |hM.eigenvalues j| ≤ R := by
  classical
  let v : Fin n → ℝ := ⇑(hM.eigenvectorBasis j)
  have horth : ‖hM.eigenvectorBasis j‖ = 1 := hM.eigenvectorBasis.orthonormal.1 j
  have hv : v ≠ 0 := by
    intro h
    have h0 : hM.eigenvectorBasis j = 0 := by
      ext i
      exact congrFun h i
    rw [h0, norm_zero] at horth
    exact zero_ne_one horth
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i0, hi0⟩ := hex
  obtain ⟨i, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun i => |v i|) ⟨i0, Finset.mem_univ i0⟩
  have hvi : 0 < |v i| := lt_of_lt_of_le (abs_pos.mpr hi0) (hmax i0 (Finset.mem_univ i0))
  have hcoord : (∑ k, M i k * v k) = hM.eigenvalues j * v i := by
    have h := congrFun (hM.mulVec_eigenvectorBasis j) i
    simpa [Matrix.mulVec, dotProduct, v, Pi.smul_apply, smul_eq_mul] using! h
  have h2 : |∑ k, M i k * v k| ≤ ∑ k, |M i k| * |v i| := by
    refine (Finset.abs_sum_le_sum_abs (fun k => M i k * v k) Finset.univ).trans ?_
    refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hmax k (Finset.mem_univ k)) (abs_nonneg _)
  have hkey : |hM.eigenvalues j| * |v i| ≤ R * |v i| := by
    calc |hM.eigenvalues j| * |v i| = |∑ k, M i k * v k| := by rw [hcoord, abs_mul]
      _ ≤ ∑ k, |M i k| * |v i| := h2
      _ = (∑ k, |M i k|) * |v i| := (Finset.sum_mul ..).symm
      _ ≤ R * |v i| := mul_le_mul_of_nonneg_right (hrow i) (abs_nonneg _)
  exact le_of_mul_le_mul_right hkey hvi

/-- Each eigenvalue of a symmetric rational matrix, viewed over the reals, has absolute value at
most `absSum A`. -/
theorem eigenvalue_abs_le_absSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (j : Fin n) :
    |(realify_isHermitian hA).eigenvalues j| ≤ (absSum A : ℝ) := by
  refine abs_eigenvalue_le_of_row_sum (realify_isHermitian hA) (R := (absSum A : ℝ)) ?_ j
  intro i
  have habs : ∀ k, |realify A i k| = ((|A i k| : ℚ) : ℝ) := fun k => by
    rw [realify_apply, Rat.cast_abs]
  have hsum : (∑ k, |realify A i k|) = ((∑ k, |A i k| : ℚ) : ℝ) := by
    simp only [habs, Rat.cast_sum]
  rw [hsum]
  exact_mod_cast abs_row_le_absSum A i

/-- The rational spectral enclosure radius `absSum A + 1`. -/
def spectrumBound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : ℚ :=
  absSum A + 1

/-- The spectral enclosure radius `spectrumBound A` is positive. -/
lemma spectrumBound_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : 0 < spectrumBound A := by
  have h := absSum_nonneg A
  unfold spectrumBound
  linarith

/-- The real cast of `spectrumBound A` is the real cast of `absSum A` plus one. -/
lemma cast_spectrumBound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    ((spectrumBound A : ℚ) : ℝ) = (absSum A : ℝ) + 1 := by
  unfold spectrumBound
  push_cast
  ring

/-- Every eigenvalue of a symmetric rational matrix lies strictly above the negative spectral
enclosure radius. -/
lemma neg_spectrumBound_lt_eigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsSymmRat A) (j : Fin n) :
    -(spectrumBound A : ℝ) < (realify_isHermitian hA).eigenvalues j := by
  have h := eigenvalue_abs_le_absSum A hA j
  have hc := cast_spectrumBound A
  linarith [neg_abs_le ((realify_isHermitian hA).eigenvalues j)]

/-- Every eigenvalue of a symmetric rational matrix lies strictly below the spectral enclosure
radius. -/
lemma eigenvalue_lt_spectrumBound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsSymmRat A) (j : Fin n) :
    (realify_isHermitian hA).eigenvalues j < (spectrumBound A : ℝ) := by
  have h := eigenvalue_abs_le_absSum A hA j
  have hc := cast_spectrumBound A
  linarith [le_abs_self ((realify_isHermitian hA).eigenvalues j)]

/-- The constructed point at the negative spectral enclosure radius has negative count zero. -/
theorem pointOf_negBound_count {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A) :
    negCountOf (pointOf A hA (-spectrumBound A)).d = 0 := by
  rw [← pointOf_count A hA (-spectrumBound A)]
  refine Finset.card_filter_eq_zero_iff.mpr ?_
  intro i _ hi
  push_cast at hi
  have hc := cast_spectrumBound A
  linarith [neg_spectrumBound_lt_eigenvalue A hA i]

/-- The positive rational grid spacing `1 / (m + 1)`. -/
def gridMesh (m : ℕ) : ℚ := ((m : ℚ) + 1)⁻¹

/-- The grid spacing is positive for every natural precision parameter. -/
lemma gridMesh_pos (m : ℕ) : 0 < gridMesh m := by
  unfold gridMesh
  positivity

/-- The natural ceiling of `2 * spectrumBound A * (m + 1)`, used as the number of grid
intervals. -/
def gridSteps {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) : ℕ :=
  Nat.ceil (2 * spectrumBound A * ((m : ℚ) + 1))

/-- The list of `k + 1` equally spaced rational points starting at `lo` with spacing `h`. -/
def gridAux (lo h : ℚ) : ℕ → List ℚ
  | 0 => [lo]
  | k + 1 => lo :: gridAux (lo + h) h k

/-- A grid with zero intervals consists only of its starting point. -/
@[simp] lemma gridAux_zero (lo h : ℚ) : gridAux lo h 0 = [lo] := rfl

/-- A grid with `k + 1` intervals consists of its starting point followed by a `k`-interval grid
starting one step later. -/
lemma gridAux_succ (lo h : ℚ) (k : ℕ) :
    gridAux lo h (k + 1) = lo :: gridAux (lo + h) h k := rfl

/-- An equally spaced grid always contains at least one point. -/
lemma gridAux_ne_nil (k : ℕ) (lo h : ℚ) : gridAux lo h k ≠ [] := by
  cases k with
  | zero => simp
  | succ k => rw [gridAux_succ]; simp

/-- The first point of `gridAux lo h k` is `lo`. -/
lemma gridAux_head (k : ℕ) (lo h : ℚ) : (gridAux lo h k).head? = some lo := by
  cases k with
  | zero => rfl
  | succ k => rw [gridAux_succ]; rfl

/-- An equally spaced grid with `k` intervals has `k + 1` points. -/
lemma gridAux_length (k : ℕ) (lo h : ℚ) : (gridAux lo h k).length = k + 1 := by
  induction k generalizing lo with
  | zero => rfl
  | succ k ih => rw [gridAux_succ, List.length_cons, ih (lo + h)]

/-- The last point of `gridAux lo h k` is `lo + k * h`. -/
lemma gridAux_getLast (k : ℕ) (lo h : ℚ) :
    (gridAux lo h k).getLast? = some (lo + k * h) := by
  induction k generalizing lo with
  | zero => simp
  | succ k ih =>
    rw [gridAux_succ, List.getLast?_cons, ih (lo + h)]
    simp
    ring

/-- Every point of a grid with nonnegative spacing is at least its starting point. -/
lemma gridAux_mem_ge (k : ℕ) (lo h x : ℚ) (hh : 0 ≤ h) (hx : x ∈ gridAux lo h k) :
    lo ≤ x := by
  induction k generalizing lo with
  | zero =>
    simp only [gridAux_zero, List.mem_singleton] at hx
    linarith
  | succ k ih =>
    rw [gridAux_succ] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_refl _
    · have hge := ih (lo + h) hx
      linarith

/-- A grid with positive spacing is pairwise strictly increasing. -/
lemma gridAux_pairwise (k : ℕ) (lo h : ℚ) (hh : 0 < h) :
    (gridAux lo h k).Pairwise (· < ·) := by
  induction k generalizing lo with
  | zero => simp
  | succ k ih =>
    rw [gridAux_succ, List.pairwise_cons]
    refine ⟨?_, ih (lo + h)⟩
    intro x hx
    have hge := gridAux_mem_ge k (lo + h) h x (le_of_lt hh) hx
    linarith

/-- The rational spectral grid starting at `-spectrumBound A` with spacing `gridMesh m` and
`gridSteps A m` intervals. -/
def gridOf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) : List ℚ :=
  gridAux (-spectrumBound A) (gridMesh m) (gridSteps A m)

/-- The spectral grid is nonempty. -/
lemma gridOf_ne_nil {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) : gridOf A m ≠ [] :=
  gridAux_ne_nil _ _ _

/-- The first point of the spectral grid is the negative spectral enclosure radius. -/
lemma gridOf_head {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) :
    (gridOf A m).head? = some (-spectrumBound A) :=
  gridAux_head _ _ _

/-- The last point of the spectral grid is its starting point plus `gridSteps A m` mesh steps. -/
lemma gridOf_getLast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) :
    (gridOf A m).getLast? =
      some (-spectrumBound A + (gridSteps A m : ℚ) * gridMesh m) :=
  gridAux_getLast _ _ _

/-- The thresholds in the spectral grid are pairwise strictly increasing. -/
lemma gridOf_pairwise {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) :
    (gridOf A m).Pairwise (· < ·) :=
  gridAux_pairwise _ _ _ (gridMesh_pos m)

/-- The last spectral grid point is at least the positive spectral enclosure radius. -/
theorem gridOf_last_ge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) :
    spectrumBound A ≤ -spectrumBound A + (gridSteps A m : ℚ) * gridMesh m := by
  have hceil : 2 * spectrumBound A * ((m : ℚ) + 1) ≤ (gridSteps A m : ℚ) :=
    Nat.le_ceil _
  have hm : (0 : ℚ) < (m : ℚ) + 1 := by positivity
  have hstep : 2 * spectrumBound A ≤ (gridSteps A m : ℚ) * gridMesh m := by
    have h := mul_le_mul_of_nonneg_right hceil (le_of_lt (inv_pos.mpr hm))
    have hcancel : 2 * spectrumBound A * ((m : ℚ) + 1) * ((m : ℚ) + 1)⁻¹
        = 2 * spectrumBound A := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hm), mul_one]
    unfold gridMesh
    calc 2 * spectrumBound A = 2 * spectrumBound A * ((m : ℚ) + 1) * ((m : ℚ) + 1)⁻¹ :=
          hcancel.symm
      _ ≤ (gridSteps A m : ℚ) * ((m : ℚ) + 1)⁻¹ := h
  linarith

/-- The constructed point at the last spectral grid threshold has negative count equal to the
matrix dimension. -/
theorem pointOf_last_count {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (m : ℕ) :
    negCountOf
        (pointOf A hA (-spectrumBound A + (gridSteps A m : ℚ) * gridMesh m)).d = n := by
  rw [← pointOf_count A hA (-spectrumBound A + (gridSteps A m : ℚ) * gridMesh m)]
  rw [Finset.filter_true_of_mem]
  · simp
  · intro i _
    have hq := gridOf_last_ge A m
    have hqcast : (spectrumBound A : ℝ) ≤
        ((-spectrumBound A + (gridSteps A m : ℚ) * gridMesh m : ℚ) : ℝ) := by
      exact_mod_cast hq
    have hlam : (realify_isHermitian hA).eigenvalues i < (spectrumBound A : ℝ) :=
      eigenvalue_lt_spectrumBound A hA i
    linarith

/-- The certificate points constructed at every threshold of the rational spectral grid. -/
def certifiedPoints {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A) (m : ℕ) :
    List (Point n) :=
  ptsOf A hA (gridOf A m)

/-- The certificate constructed on the spectral grid is accepted by `checkPoints`. -/
theorem certifiedPoints_check {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (m : ℕ) : checkPoints A (certifiedPoints A hA m) = true := by
  unfold certifiedPoints
  refine checkPoints_ptsOf A hA (gridOf_ne_nil A m) (gridOf_pairwise A m) ?_ ?_
  · intro q hq
    rw [gridOf_head] at hq
    cases hq
    exact pointOf_negBound_count A hA
  · intro q hq
    rw [gridOf_getLast] at hq
    cases hq
    exact pointOf_last_count A hA m

/-- The certificate constructed on the spectral grid is valid. -/
theorem certifiedPoints_valid {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (m : ℕ) : Valid A (certifiedPoints A hA m) :=
  (checkPoints_eq_true_iff A _).mp (certifiedPoints_check A hA m)

/-- Each consecutive pair of constructed certificate points gives the exact eigenvalue count in
its half-open interval. -/
theorem certifiedPoints_counts {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (m : ℕ) :
    ∀ p q, (p, q) ∈ (certifiedPoints A hA m).zip ((certifiedPoints A hA m).drop 1) →
      (Finset.univ.filter fun i => (p.q : ℝ) ≤ (realify_isHermitian hA).eigenvalues i ∧
        (realify_isHermitian hA).eigenvalues i < (q.q : ℝ)).card = countBetween p q :=
  (certificate_sound hA (certifiedPoints_valid A hA m)).1

/-- Every eigenvalue lies between the first spectral grid threshold, included, and the last
threshold, excluded. -/
theorem certifiedPoints_covers {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (m : ℕ) (i : Fin n) :
    ((-spectrumBound A : ℚ) : ℝ) ≤ (realify_isHermitian hA).eigenvalues i ∧
      (realify_isHermitian hA).eigenvalues i <
        ((-spectrumBound A + (gridSteps A m : ℚ) * gridMesh m : ℚ) : ℝ) := by
  constructor
  · exact pointOf_le_of_count_zero A hA (-spectrumBound A) (pointOf_negBound_count A hA) i
  · exact pointOf_lt_of_count_card A hA (-spectrumBound A + (gridSteps A m : ℚ) * gridMesh m)
      (pointOf_last_count A hA m) i

/-- The spectral certificate has one more point than the number of grid intervals. -/
theorem certifiedPoints_length {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (m : ℕ) : (certifiedPoints A hA m).length = gridSteps A m + 1 := by
  unfold certifiedPoints ptsOf gridOf
  rw [List.length_map, gridAux_length]

/-- The constructed spectral certificate passes its checker, gives exact interval counts,
encloses every eigenvalue, and has the stated number of points. -/
theorem frontier1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A) (m : ℕ) :
    checkPoints A (certifiedPoints A hA m) = true ∧
      (∀ p q, (p, q) ∈ (certifiedPoints A hA m).zip ((certifiedPoints A hA m).drop 1) →
        (Finset.univ.filter fun i => (p.q : ℝ) ≤ (realify_isHermitian hA).eigenvalues i ∧
          (realify_isHermitian hA).eigenvalues i < (q.q : ℝ)).card = countBetween p q) ∧
      (∀ i, ((-spectrumBound A : ℚ) : ℝ) ≤ (realify_isHermitian hA).eigenvalues i ∧
        (realify_isHermitian hA).eigenvalues i <
          ((-spectrumBound A + (gridSteps A m : ℚ) * gridMesh m : ℚ) : ℝ)) ∧
      (certifiedPoints A hA m).length = gridSteps A m + 1 :=
  ⟨certifiedPoints_check A hA m, certifiedPoints_counts A hA m,
    certifiedPoints_covers A hA m, certifiedPoints_length A hA m⟩

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- Every real value in a finite positive-mesh grid range belongs to one of its half-open grid
intervals. -/
lemma exists_grid_interval (lo h lam : ℝ) :
    ∀ k : ℕ, 0 < h → lo ≤ lam → lam < lo + k * h →
      ∃ j < k, lo + j * h ≤ lam ∧ lam < lo + (j + 1) * h
  | 0, _, hl, hk => by
    simp only [Nat.cast_zero] at hk
    linarith
  | k + 1, hh, hl, hk => by
    by_cases h1 : lam < lo + h
    · exact ⟨0, Nat.succ_pos k, by simpa using! hl, by simpa using! h1⟩
    · push Not at h1
      have hk' : lam < (lo + h) + k * h := by
        push_cast at hk ⊢
        linarith
      obtain ⟨j, hj, hjl, hjr⟩ :=
        exists_grid_interval (lo + h) h lam k hh (by linarith) hk'
      refine ⟨j + 1, Nat.succ_lt_succ hj, ?_, ?_⟩
      · push_cast
        linarith
      · push_cast
        linarith

/-- Each eigenvalue of a symmetric rational matrix lies in a half-open interval of its spectral
grid. -/
theorem certifiedPoints_interval {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsSymmRat A) (m : ℕ) (i : Fin n) :
    ∃ j < gridSteps A m,
      ((-spectrumBound A + (j : ℚ) * gridMesh m : ℚ) : ℝ) ≤
          (realify_isHermitian hA).eigenvalues i ∧
        (realify_isHermitian hA).eigenvalues i <
          ((-spectrumBound A + ((j : ℚ) + 1) * gridMesh m : ℚ) : ℝ) := by
  obtain ⟨hlow, hhigh⟩ := certifiedPoints_covers A hA m i
  have hh : (0 : ℝ) < ((gridMesh m : ℚ) : ℝ) := by exact_mod_cast gridMesh_pos m
  have hlow' : -((spectrumBound A : ℚ) : ℝ) ≤
      (realify_isHermitian hA).eigenvalues i := by
    have h := hlow
    push_cast at h
    exact h
  have hhigh' : (realify_isHermitian hA).eigenvalues i <
      -((spectrumBound A : ℚ) : ℝ) + (gridSteps A m : ℝ) * ((gridMesh m : ℚ) : ℝ) := by
    have h := hhigh
    push_cast at h
    exact h
  obtain ⟨j, hj, hjl, hjr⟩ :=
    exists_grid_interval (-((spectrumBound A : ℚ) : ℝ)) ((gridMesh m : ℚ) : ℝ)
      ((realify_isHermitian hA).eigenvalues i) (gridSteps A m) hh hlow' hhigh'
  refine ⟨j, hj, ?_, ?_⟩
  · push_cast
    exact hjl
  · push_cast
    exact hjr

/-- The difference of consecutive rational grid thresholds equals the grid spacing. -/
lemma grid_interval_width (lo h : ℚ) (j : ℕ) :
    lo + ((j : ℚ) + 1) * h - (lo + (j : ℚ) * h) = h := by
  ring

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- The stored diagonalization step count for the certificate point at a threshold. -/
def pointSteps {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A) (q : ℚ) : ℕ :=
  (diagAux n (shift A q) (shift_symm hA q)).steps

/-- Constructing a point for an `n`-dimensional matrix has stored step count `n`. -/
theorem pointSteps_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A) (q : ℚ) :
    pointSteps A hA q = n :=
  diagAux_steps n (shift A q) (shift_symm hA q)

/-- The sum of the stored diagonalization step counts over a list of thresholds. -/
def totalSteps {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (qs : List ℚ) : ℕ :=
  (qs.map (pointSteps A hA)).sum

/-- Prepending a threshold adds `n` to the total stored step count. -/
lemma totalSteps_cons {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (q : ℚ) (qs : List ℚ) :
    totalSteps A hA (q :: qs) = n + totalSteps A hA qs := by
  simp [totalSteps, pointSteps_eq]

/-- The total stored step count is the number of thresholds times the matrix dimension. -/
theorem totalSteps_eq_length {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (qs : List ℚ) : totalSteps A hA qs = qs.length * n := by
  induction qs with
  | nil => simp [totalSteps]
  | cons q qs ih =>
    rw [totalSteps_cons, ih, List.length_cons, Nat.succ_mul]
    omega

/-- The total stored step count on the spectral grid is `(gridSteps A m + 1) * n`. -/
theorem certifiedPoints_totalSteps {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsSymmRat A) (m : ℕ) :
    totalSteps A hA (gridOf A m) = (gridSteps A m + 1) * n := by
  rw [totalSteps_eq_length]
  congr 1
  unfold gridOf
  rw [gridAux_length]

/-- The stored diagonalization operation count for the certificate point at a threshold. -/
def pointOps {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A) (q : ℚ) : ℕ :=
  (diagAux n (shift A q) (shift_symm hA q)).ops

/-- The operation count stored for a constructed point is bounded by `opsBound n`. -/
theorem pointOps_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A) (q : ℚ) :
    pointOps A hA q ≤ opsBound n :=
  diagAux_ops_le n (shift A q) (shift_symm hA q)

/-- The sum of the stored diagonalization operation counts over a list of thresholds. -/
def totalOps {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (qs : List ℚ) : ℕ :=
  (qs.map (pointOps A hA)).sum

/-- The total stored operation count is at most the number of thresholds times `opsBound n`. -/
theorem totalOps_le_length {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (qs : List ℚ) : totalOps A hA qs ≤ qs.length * opsBound n := by
  induction qs with
  | nil => simp [totalOps]
  | cons q qs ih =>
    have hcons : totalOps A hA (q :: qs) = pointOps A hA q + totalOps A hA qs := by
      simp [totalOps]
    rw [hcons]
    calc pointOps A hA q + totalOps A hA qs
        ≤ opsBound n + qs.length * opsBound n :=
          Nat.add_le_add (pointOps_le A hA q) ih
      _ = qs.length * opsBound n + opsBound n := Nat.add_comm _ _
      _ = (q :: qs).length * opsBound n := by
          rw [List.length_cons, Nat.succ_mul]

/-- The total stored operation count on the spectral grid is at most `(gridSteps A m + 1) *
opsBound n`. -/
theorem certifiedPoints_ops {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsSymmRat A) (m : ℕ) :
    totalOps A hA (gridOf A m) ≤ (gridSteps A m + 1) * opsBound n := by
  have h := totalOps_le_length A hA (gridOf A m)
  have hlen : (gridOf A m).length = gridSteps A m + 1 := by
    unfold gridOf
    rw [gridAux_length]
  rwa [hlen] at h

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- The height of a rational number, defined as the maximum of its numerator's absolute value
and its denominator. -/
def Height (q : ℚ) : ℕ := max q.num.natAbs q.den

/-- The height of every rational number is positive. -/
lemma Height_pos (q : ℚ) : 0 < Height q :=
  lt_of_lt_of_le q.den_pos (Nat.le_max_right _ _)

/-- The height of rational zero is one. -/
@[simp] lemma Height_zero : Height (0 : ℚ) = 1 := by decide

/-- The height of rational one is one. -/
@[simp] lemma Height_one : Height (1 : ℚ) = 1 := by decide

/-- The absolute value of a rational number's numerator is at most its height. -/
lemma num_natAbs_le_Height (q : ℚ) : q.num.natAbs ≤ Height q :=
  Nat.le_max_left _ _

/-- The denominator of a rational number is at most its height. -/
lemma den_le_Height (q : ℚ) : q.den ≤ Height q :=
  Nat.le_max_right _ _

/-- Negation preserves rational height. -/
@[simp] lemma Height_neg (q : ℚ) : Height (-q) = Height q := by
  simp [Height]

/-- An integer divisor of a nonzero integer has absolute value at most that of the integer. -/
lemma natAbs_le_natAbs_of_dvd {a b : ℤ} (h : a ∣ b) (hb : b ≠ 0) : a.natAbs ≤ b.natAbs := by
  obtain ⟨c, rfl⟩ := h
  rw [Int.natAbs_mul]
  have hc : 0 < c.natAbs := by
    rw [Int.natAbs_pos]
    exact (mul_ne_zero_iff.mp hb).2
  exact Nat.le_mul_of_pos_right _ hc

/-- The height of a rational product is at most the product of the heights. -/
lemma Height_mul_le (q₁ q₂ : ℚ) : Height (q₁ * q₂) ≤ Height q₁ * Height q₂ := by
  have hden : ((q₁.den * q₂.den : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero q₁.den_ne_zero q₂.den_ne_zero :
      q₁.den * q₂.den ≠ 0)
  have hdiv : q₁ * q₂
      = Rat.divInt (q₁.num * q₂.num) ((q₁.den * q₂.den : ℕ) : ℤ) := by
    rw [Rat.mul_def, Rat.normalize_eq_mkRat, Rat.mkRat_eq_divInt]
  have hnum : (q₁ * q₂).num.natAbs ≤ q₁.num.natAbs * q₂.num.natAbs := by
    have hdvd : (q₁ * q₂).num ∣ q₁.num * q₂.num := by
      rw [hdiv]
      exact Rat.num_dvd _ hden
    rcases eq_or_ne (q₁.num * q₂.num) 0 with hzero | hne
    · have hz : q₁ * q₂ = 0 := by rw [hdiv, hzero, Rat.zero_divInt]
      rw [hz]
      simp
    · exact (natAbs_le_natAbs_of_dvd hdvd hne).trans (le_of_eq (Int.natAbs_mul _ _))
  have hden2 : (q₁ * q₂).den ≤ q₁.den * q₂.den := by
    have hdvd : ((q₁ * q₂).den : ℤ) ∣ ((q₁.den * q₂.den : ℕ) : ℤ) := by
      rw [hdiv]
      exact Rat.den_dvd _ _
    exact Nat.le_of_dvd (Nat.mul_pos q₁.den_pos q₂.den_pos)
      (Int.natCast_dvd_natCast.mp hdvd)
  calc Height (q₁ * q₂)
      = max (q₁ * q₂).num.natAbs (q₁ * q₂).den := rfl
    _ ≤ max (q₁.num.natAbs * q₂.num.natAbs) (q₁.den * q₂.den) := max_le_max hnum hden2
    _ ≤ Height q₁ * Height q₂ :=
      max_le (Nat.mul_le_mul (num_natAbs_le_Height q₁) (num_natAbs_le_Height q₂))
        (Nat.mul_le_mul (den_le_Height q₁) (den_le_Height q₂))

/-- The height of a rational sum is at most twice the product of the heights. -/
lemma Height_add_le (q₁ q₂ : ℚ) : Height (q₁ + q₂) ≤ 2 * (Height q₁ * Height q₂) := by
  have hden : ((q₁.den * q₂.den : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero q₁.den_ne_zero q₂.den_ne_zero :
      q₁.den * q₂.den ≠ 0)
  have hdiv : q₁ + q₂
      = Rat.divInt (q₁.num * (q₂.den : ℤ) + q₂.num * (q₁.den : ℤ))
          ((q₁.den * q₂.den : ℕ) : ℤ) := by
    rw [Rat.add_def, Rat.normalize_eq_mkRat, Rat.mkRat_eq_divInt]
  have hnum : (q₁ + q₂).num.natAbs ≤ 2 * (Height q₁ * Height q₂) := by
    have hdvd : (q₁ + q₂).num
        ∣ (q₁.num * (q₂.den : ℤ) + q₂.num * (q₁.den : ℤ)) := by
      rw [hdiv]
      exact Rat.num_dvd _ hden
    rcases eq_or_ne (q₁.num * (q₂.den : ℤ) + q₂.num * (q₁.den : ℤ)) 0 with hzero | hne
    · have hz : q₁ + q₂ = 0 := by rw [hdiv, hzero, Rat.zero_divInt]
      rw [hz]
      simp
    · refine (natAbs_le_natAbs_of_dvd hdvd hne).trans ?_
      calc (q₁.num * (q₂.den : ℤ) + q₂.num * (q₁.den : ℤ)).natAbs
          ≤ (q₁.num * (q₂.den : ℤ)).natAbs + (q₂.num * (q₁.den : ℤ)).natAbs :=
            Int.natAbs_add_le _ _
        _ = q₁.num.natAbs * q₂.den + q₂.num.natAbs * q₁.den := by
            rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
        _ ≤ Height q₁ * Height q₂ + Height q₁ * Height q₂ := by
            refine Nat.add_le_add ?_ ?_
            · exact Nat.mul_le_mul (num_natAbs_le_Height q₁) (den_le_Height q₂)
            · calc q₂.num.natAbs * q₁.den ≤ Height q₂ * Height q₁ :=
                    Nat.mul_le_mul (num_natAbs_le_Height q₂) (den_le_Height q₁)
                _ = Height q₁ * Height q₂ := Nat.mul_comm _ _
        _ = 2 * (Height q₁ * Height q₂) := by ring
  have hden2 : (q₁ + q₂).den ≤ Height q₁ * Height q₂ := by
    have hdvd : ((q₁ + q₂).den : ℤ) ∣ ((q₁.den * q₂.den : ℕ) : ℤ) := by
      rw [hdiv]
      exact Rat.den_dvd _ _
    refine (Nat.le_of_dvd (Nat.mul_pos q₁.den_pos q₂.den_pos)
      (Int.natCast_dvd_natCast.mp hdvd)).trans ?_
    exact Nat.mul_le_mul (den_le_Height q₁) (den_le_Height q₂)
  calc Height (q₁ + q₂)
      = max (q₁ + q₂).num.natAbs (q₁ + q₂).den := rfl
    _ ≤ 2 * (Height q₁ * Height q₂) :=
      max_le hnum (hden2.trans (Nat.le_mul_of_pos_left _ (by decide)))

/-- The height of a rational difference is at most twice the product of the heights. -/
lemma Height_sub_le (q₁ q₂ : ℚ) : Height (q₁ - q₂) ≤ 2 * (Height q₁ * Height q₂) := by
  have h := Height_add_le q₁ (-q₂)
  rw [Height_neg] at h
  rw [sub_eq_add_neg]
  exact h

/-- Taking the reciprocal of a rational number does not increase its height. -/
lemma Height_inv_le (q : ℚ) : Height q⁻¹ ≤ Height q := by
  by_cases hq : q = 0
  · subst hq
    simp
  · have hnum : (q⁻¹).num.natAbs ≤ q.den := by
      have hdvd : (q⁻¹).num ∣ (q.den : ℤ) := by
        rw [Rat.inv_def]
        exact Rat.num_dvd _ (Rat.num_ne_zero.mpr hq)
      have hne : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
      exact (natAbs_le_natAbs_of_dvd hdvd hne).trans (by simp)
    have hden : (q⁻¹).den ≤ q.num.natAbs := by
      rw [Rat.den_inv_of_ne_zero hq]
    calc Height q⁻¹ = max (q⁻¹).num.natAbs (q⁻¹).den := rfl
      _ ≤ max q.den q.num.natAbs := max_le_max hnum hden
      _ = Height q := by rw [Height, Nat.max_comm]

/-- The height of a natural number cast to the rationals is at most that number plus one. -/
lemma Height_natCast_le (n : ℕ) : Height (n : ℚ) ≤ n + 1 := by
  have h : Height (n : ℚ) = max n 1 := by
    unfold Height
    rw [Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast]
  rw [h]
  exact max_le (Nat.le_succ n) (Nat.succ_pos n)

/-- Membership in `gridAux lo h k` is equivalent to having the form `lo + j * h` for some `j ≤
k`. -/
lemma gridAux_mem_iff (k : ℕ) (lo h x : ℚ) :
    x ∈ gridAux lo h k ↔ ∃ j ≤ k, x = lo + (j : ℚ) * h := by
  induction k generalizing lo with
  | zero =>
    rw [gridAux_zero]
    constructor
    · intro hx
      rw [List.mem_singleton] at hx
      exact ⟨0, le_rfl, by rw [hx]; simp⟩
    · rintro ⟨j, hj, rfl⟩
      have : j = 0 := Nat.le_zero.mp hj
      subst this
      simp
  | succ k ih =>
    rw [gridAux_succ]
    constructor
    · intro hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨0, Nat.zero_le _, by simp⟩
      · obtain ⟨j, hj, rfl⟩ := (ih (lo + h)).mp hx
        exact ⟨j + 1, Nat.succ_le_succ hj, by push_cast; ring⟩
    · rintro ⟨j, hj, rfl⟩
      rcases j with _ | j
      · simp
      · refine List.mem_cons_of_mem _ ((ih (lo + h)).mpr ⟨j, Nat.succ_le_succ_iff.mp hj, ?_⟩)
        push_cast
        ring

/-- The height of `gridMesh m` is at most `2 * m + 2`. -/
lemma Height_gridMesh (m : ℕ) : Height (gridMesh m) ≤ 2 * m + 2 := by
  have hstep : Height (gridMesh m) ≤ Height ((m : ℚ) + 1) := by
    unfold gridMesh
    exact Height_inv_le _
  have hsum : Height ((m : ℚ) + 1) ≤ 2 * (Height (m : ℚ) * Height (1 : ℚ)) :=
    Height_add_le _ _
  rw [Height_one] at hsum
  have hm : Height (m : ℚ) ≤ m + 1 := Height_natCast_le m
  have hmono : Height (m : ℚ) * 1 ≤ (m + 1) * 1 := Nat.mul_le_mul_right _ hm
  nlinarith

/-- Every spectral grid threshold has height bounded by twice the product of the enclosure
height, the grid point count, and the mesh height. -/
theorem gridOf_height {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) {x : ℚ}
    (hx : x ∈ gridOf A m) :
    Height x ≤ 2 * (Height (spectrumBound A) *
      ((gridSteps A m + 1) * Height (gridMesh m))) := by
  obtain ⟨j, hj, rfl⟩ := (gridAux_mem_iff (gridSteps A m) (-spectrumBound A)
    (gridMesh m) x).mp hx
  have hadd := Height_add_le (-spectrumBound A) ((j : ℚ) * gridMesh m)
  rw [Height_neg] at hadd
  have hmul := Height_mul_le (j : ℚ) (gridMesh m)
  have hjq : Height (j : ℚ) ≤ j + 1 := Height_natCast_le j
  have hle : Height ((j : ℚ) * gridMesh m) ≤ (gridSteps A m + 1) * Height (gridMesh m) :=
    hmul.trans (Nat.mul_le_mul (hjq.trans (Nat.succ_le_succ hj)) le_rfl)
  refine hadd.trans ?_
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hle)

/-- The condition that a rational number has height at most `2 ^ b`. -/
def BitLe (b : ℕ) (q : ℚ) : Prop := Height q ≤ 2 ^ b

/-- The condition that every entry of a rational matrix has height at most `2 ^ b`. -/
def MatBitLe {m n : Type*} (b : ℕ) (A : Matrix m n ℚ) : Prop :=
  ∀ i j, BitLe b (A i j)

/-- Rational zero satisfies `BitLe b` for every natural exponent. -/
lemma bitLe_zero (b : ℕ) : BitLe b 0 := by
  unfold BitLe
  rw [Height_zero]
  exact Nat.one_le_two_pow

/-- Rational one satisfies `BitLe b` for every natural exponent. -/
lemma bitLe_one (b : ℕ) : BitLe b 1 := by
  unfold BitLe
  rw [Height_one]
  exact Nat.one_le_two_pow

/-- A rational height bound remains valid when its exponent is increased. -/
lemma BitLe.mono {b b' : ℕ} (h : b ≤ b') {q : ℚ} (hq : BitLe b q) : BitLe b' q :=
  hq.trans (Nat.pow_le_pow_right (by decide) h)

/-- Negation preserves the exponent in a rational height bound. -/
lemma BitLe.neg {b : ℕ} {q : ℚ} (hq : BitLe b q) : BitLe b (-q) := by
  unfold BitLe at *
  rwa [Height_neg]

/-- Multiplication adds the exponents of rational height bounds. -/
lemma BitLe.mul {b₁ b₂ : ℕ} {q₁ q₂ : ℚ} (h₁ : BitLe b₁ q₁) (h₂ : BitLe b₂ q₂) :
    BitLe (b₁ + b₂) (q₁ * q₂) := by
  unfold BitLe at *
  calc Height (q₁ * q₂) ≤ Height q₁ * Height q₂ := Height_mul_le q₁ q₂
    _ ≤ 2 ^ b₁ * 2 ^ b₂ := Nat.mul_le_mul h₁ h₂
    _ = 2 ^ (b₁ + b₂) := (Nat.pow_add ..).symm

/-- Addition combines rational height-bound exponents as `b₁ + b₂ + 1`. -/
lemma BitLe.add {b₁ b₂ : ℕ} {q₁ q₂ : ℚ} (h₁ : BitLe b₁ q₁) (h₂ : BitLe b₂ q₂) :
    BitLe (b₁ + b₂ + 1) (q₁ + q₂) := by
  unfold BitLe at *
  calc Height (q₁ + q₂) ≤ 2 * (Height q₁ * Height q₂) := Height_add_le q₁ q₂
    _ ≤ 2 * (2 ^ b₁ * 2 ^ b₂) := by
        refine Nat.mul_le_mul_left _ (Nat.mul_le_mul h₁ h₂)
    _ = 2 ^ (b₁ + b₂ + 1) := by
        rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]
        ring

/-- The sum of two rationals satisfying `BitLe b` satisfies `BitLe (b + b + 1)`. -/
lemma BitLe.add_same {b : ℕ} {q₁ q₂ : ℚ} (h₁ : BitLe b q₁) (h₂ : BitLe b q₂) :
    BitLe (b + b + 1) (q₁ + q₂) :=
  h₁.add h₂

/-- Subtraction combines rational height-bound exponents as `b₁ + b₂ + 1`. -/
lemma BitLe.sub {b₁ b₂ : ℕ} {q₁ q₂ : ℚ} (h₁ : BitLe b₁ q₁) (h₂ : BitLe b₂ q₂) :
    BitLe (b₁ + b₂ + 1) (q₁ - q₂) := by
  rw [sub_eq_add_neg]
  exact h₁.add h₂.neg

/-- Taking a reciprocal preserves a rational height-bound exponent. -/
lemma BitLe.inv {b : ℕ} {q : ℚ} (hq : BitLe b q) : BitLe b q⁻¹ :=
  (Height_inv_le q).trans hq

/-- A finite sum of rationals each satisfying `BitLe b` satisfies `BitLe (s.card * (b + 1))`. -/
lemma BitLe.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) {b : ℕ}
    (h : ∀ i ∈ s, BitLe b (f i)) : BitLe (s.card * (b + 1)) (s.sum f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    unfold BitLe
    simp only [Finset.sum_empty, Finset.card_empty, Nat.zero_mul]
    rw [Height_zero]
    exact Nat.one_le_two_pow
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have ha' : BitLe b (f a) := h a (Finset.mem_insert_self _ _)
    have hs' : BitLe (s.card * (b + 1)) (s.sum f) :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hadd := ha'.add hs'
    have hexp : b + (s.card * (b + 1)) + 1 = (s.card + 1) * (b + 1) := by
      rw [Nat.succ_mul]
      omega
    rwa [hexp] at hadd

/-- Every entry of the zero rational matrix satisfies any natural height-bound exponent. -/
lemma matBitLe_zero {m n : Type*} {b : ℕ} : MatBitLe b (0 : Matrix m n ℚ) :=
  fun i j => by
    rw [Matrix.zero_apply]
    exact bitLe_zero b

/-- Every entry of the rational identity matrix satisfies any natural height-bound exponent. -/
lemma matBitLe_one {m : Type*} [DecidableEq m] {b : ℕ} :
    MatBitLe b (1 : Matrix m m ℚ) :=
  fun i j => by
    rw [Matrix.one_apply]
    by_cases h : i = j
    · rw [if_pos h]
      exact bitLe_one b
    · rw [if_neg h]
      exact bitLe_zero b

/-- An entrywise rational matrix height bound remains valid when its exponent is increased. -/
lemma MatBitLe.mono {m n : Type*} {b b' : ℕ} (h : b ≤ b') {A : Matrix m n ℚ}
    (hA : MatBitLe b A) : MatBitLe b' A :=
  fun i j => (hA i j).mono h

/-- Matrix negation preserves an entrywise height-bound exponent. -/
lemma MatBitLe.neg {m n : Type*} {b : ℕ} {A : Matrix m n ℚ} (hA : MatBitLe b A) :
    MatBitLe b (-A) :=
  fun i j => by
    rw [Matrix.neg_apply]
    exact (hA i j).neg

/-- Matrix addition combines entrywise height-bound exponents as `b₁ + b₂ + 1`. -/
lemma MatBitLe.add {m n : Type*} {b₁ b₂ : ℕ} {A B : Matrix m n ℚ}
    (hA : MatBitLe b₁ A) (hB : MatBitLe b₂ B) : MatBitLe (b₁ + b₂ + 1) (A + B) :=
  fun i j => by
    rw [Matrix.add_apply]
    exact (hA i j).add (hB i j)

/-- Matrix subtraction combines entrywise height-bound exponents as `b₁ + b₂ + 1`. -/
lemma MatBitLe.sub {m n : Type*} {b₁ b₂ : ℕ} {A B : Matrix m n ℚ}
    (hA : MatBitLe b₁ A) (hB : MatBitLe b₂ B) : MatBitLe (b₁ + b₂ + 1) (A - B) :=
  fun i j => by
    rw [Matrix.sub_apply]
    exact (hA i j).sub (hB i j)

/-- Transposition preserves an entrywise rational matrix height bound. -/
lemma MatBitLe.transpose {m n : Type*} {b : ℕ} {A : Matrix m n ℚ}
    (hA : MatBitLe b A) : MatBitLe b Aᵀ :=
  fun i j => by
    rw [Matrix.transpose_apply]
    exact hA j i

/-- Scalar multiplication adds the height-bound exponent of the scalar to that of the matrix. -/
lemma MatBitLe.smul {m n : Type*} {b bc : ℕ} {c : ℚ} {A : Matrix m n ℚ}
    (hc : BitLe bc c) (hA : MatBitLe b A) : MatBitLe (bc + b) (c • A) :=
  fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact hc.mul (hA i j)

/-- A height bound on a rational entry gives the same entrywise bound on its one-by-one matrix. -/
lemma matBitLe_oneByOne {b : ℕ} {a : ℚ} (ha : BitLe b a) : MatBitLe b (oneByOne a) :=
  fun i j => by
    rw [oneByOne_apply]
    exact ha

/-- A uniform height bound on diagonal entries gives the same entrywise bound on the diagonal
matrix. -/
lemma matBitLe_diagonal {m : Type*} [DecidableEq m] {b : ℕ} {d : m → ℚ}
    (hd : ∀ i, BitLe b (d i)) : MatBitLe b (diagonal d) :=
  fun i j => by
    rw [Matrix.diagonal_apply]
    by_cases h : i = j
    · rw [if_pos h]
      exact hd i
    · rw [if_neg h]
      exact bitLe_zero b

/-- A common entrywise height bound for four blocks gives the same bound for their block matrix. -/
lemma matBitLe_fromBlocks {m n k l : Type*} {b : ℕ}
    {P : Matrix m k ℚ} {Q : Matrix m l ℚ} {R : Matrix n k ℚ} {S : Matrix n l ℚ}
    (hP : MatBitLe b P) (hQ : MatBitLe b Q) (hR : MatBitLe b R) (hS : MatBitLe b S) :
    MatBitLe b (fromBlocks P Q R S) := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simpa using! hP i j
  · simpa using! hQ i j
  · simpa using! hR i j
  · simpa using! hS i j

/-- Matrix multiplication yields entrywise height-bound exponent `Fintype.card κ * (bp + bq +
1)` from exponents `bp` and `bq`. -/
lemma matBitLe_mul {κ : Type*} [Fintype κ] {m n : Type*} {bp bq : ℕ}
    {P : Matrix m κ ℚ} {Q : Matrix κ n ℚ} (hP : MatBitLe bp P) (hQ : MatBitLe bq Q) :
    MatBitLe (Fintype.card κ * (bp + bq + 1)) (P * Q) :=
  fun i j => by
    rw [Matrix.mul_apply]
    have h := BitLe.sum (Finset.univ : Finset κ) (fun l => P i l * Q l j)
      (b := bp + bq) (fun l _ => (hP i l).mul (hQ l j))
    simpa [Finset.card_univ] using! h

/-- The condition that both the congruence matrix and the diagonal entries of a witness have
height at most `2 ^ b`. -/
def WitnessBitLe {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℚ}
    (b : ℕ) (w : DiagWitness B) : Prop :=
  MatBitLe b w.M ∧ ∀ i, BitLe b (w.d i)

/-- The height-bound exponent used for a row after shear preparation. -/
def shearRowExp (n b : ℕ) : ℕ := b + (1 + n * (b + b + 1)) + 1

/-- The height-bound exponent used for the pivot after shear preparation. -/
def shearPivotExp (n b : ℕ) : ℕ :=
  (b + (2 + n * (b + b + 1)) + 1) + (2 + n * (n * (b + b + 1) + b + 1)) + 1

/-- The height-bound exponent used for a Schur complement after shear preparation. -/
def tailExp (n b : ℕ) : ℕ := b + shearPivotExp n b + 2 * shearRowExp n b + 3

/-- A recursive height-bound exponent for the output of rational diagonalization in dimension
`n` with input exponent `b`. -/
def costExp : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, b =>
      (n + 1) * ((n + 1) * (costExp n (tailExp n b) + 2 * shearPivotExp n b + 2) + (b + 1) + 1)
        + costExp n b

/-- The shear row exponent is monotone in the input height-bound exponent. -/
lemma shearRowExp_mono {n b b' : ℕ} (h : b ≤ b') : shearRowExp n b ≤ shearRowExp n b' := by
  unfold shearRowExp
  have : b + b + 1 ≤ b' + b' + 1 := by omega
  have := Nat.mul_le_mul_left n this
  omega

/-- The shear pivot exponent is monotone in the input height-bound exponent. -/
lemma shearPivotExp_mono {n b b' : ℕ} (h : b ≤ b') :
    shearPivotExp n b ≤ shearPivotExp n b' := by
  unfold shearPivotExp
  have h1 : b + b + 1 ≤ b' + b' + 1 := by omega
  have h2 : n * (b + b + 1) ≤ n * (b' + b' + 1) := Nat.mul_le_mul_left n h1
  have h3 : b + (2 + n * (b + b + 1)) + 1 ≤ b' + (2 + n * (b' + b' + 1)) + 1 := by omega
  have h4 : n * (b + b + 1) + b + 1 ≤ n * (b' + b' + 1) + b' + 1 := by omega
  have h5 : n * (n * (b + b + 1) + b + 1) ≤ n * (n * (b' + b' + 1) + b' + 1) :=
    Nat.mul_le_mul_left n h4
  have h6 : 2 + n * (n * (b + b + 1) + b + 1) ≤ 2 + n * (n * (b' + b' + 1) + b' + 1) := by
    omega
  omega

/-- The Schur-complement exponent `tailExp` is monotone in the input height-bound exponent. -/
lemma tailExp_mono {n b b' : ℕ} (h : b ≤ b') : tailExp n b ≤ tailExp n b' := by
  unfold tailExp
  have h1 := shearPivotExp_mono (n := n) h
  have h2 := shearRowExp_mono (n := n) h
  omega

/-- For fixed dimension, `costExp` is monotone in the input height-bound exponent. -/
lemma costExp_mono (n : ℕ) {b b' : ℕ} (h : b ≤ b') : costExp n b ≤ costExp n b' := by
  induction n generalizing b b' with
  | zero => exact le_rfl
  | succ n ih =>
    show (n + 1) * ((n + 1) * (costExp n (tailExp n b) + 2 * shearPivotExp n b + 2)
          + (b + 1) + 1) + costExp n b
        ≤ (n + 1) * ((n + 1) * (costExp n (tailExp n b') + 2 * shearPivotExp n b' + 2)
          + (b' + 1) + 1) + costExp n b'
    have h1 := tailExp_mono (n := n) h
    have h2 := ih h1
    have h3 := shearPivotExp_mono (n := n) h
    have h4 := ih h
    have h5 : costExp n (tailExp n b) + 2 * shearPivotExp n b + 2 ≤
        costExp n (tailExp n b') + 2 * shearPivotExp n b' + 2 := by omega
    have h6 : (n + 1) * (costExp n (tailExp n b) + 2 * shearPivotExp n b + 2) + (b + 1) + 1 ≤
        (n + 1) * (costExp n (tailExp n b') + 2 * shearPivotExp n b' + 2) + (b' + 1) + 1 := by
      have := Nat.mul_le_mul_left (n + 1) h5
      omega
    have h7 := Nat.mul_le_mul_left (n + 1) h6
    omega

/-- If `x ≤ y`, then `x ≤ (n + 1) * y` for natural numbers. -/
lemma le_succ_mul {x y n : ℕ} (h : x ≤ y) : x ≤ (n + 1) * y :=
  h.trans (Nat.le_mul_of_pos_left _ (by omega))

/-- The shear row exponent is at least the input exponent. -/
lemma le_shearRowExp (n b : ℕ) : b ≤ shearRowExp n b := by
  unfold shearRowExp
  omega

/-- The shear pivot exponent is at least the input exponent. -/
lemma le_shearPivotExp (n b : ℕ) : b ≤ shearPivotExp n b := by
  unfold shearPivotExp
  omega

/-- The Schur-complement exponent is at least the input exponent. -/
lemma le_tailExp (n b : ℕ) : b ≤ tailExp n b := by
  unfold tailExp
  omega

/-- The input exponent `b` is at most the shear output exponent `(n + 1) * ((n + 1) * (bt + 2 *
shearPivotExp n b + 2) + (b + 1) + 1)`. -/
lemma le_shear_output_b (n b bt : ℕ) :
    b ≤ (n + 1) * ((n + 1) * (bt + 2 * shearPivotExp n b + 2) + (b + 1) + 1) := by
  have h1 : b ≤ (n + 1) * (bt + 2 * shearPivotExp n b + 2) := by
    refine le_succ_mul ?_
    have := le_shearPivotExp n b
    omega
  have h2 : (n + 1) * (bt + 2 * shearPivotExp n b + 2) ≤
      (n + 1) * (bt + 2 * shearPivotExp n b + 2) + (b + 1) + 1 := by omega
  exact le_succ_mul (h1.trans h2)

/-- The shear pivot exponent is at most the displayed shear output exponent assembled from `n`,
`b`, and `bt`. -/
lemma le_shear_output_pivot (n b bt : ℕ) :
    shearPivotExp n b ≤ (n + 1) * ((n + 1) * (bt + 2 * shearPivotExp n b + 2) + (b + 1) + 1) := by
  have h1 : shearPivotExp n b ≤ (n + 1) * (bt + 2 * shearPivotExp n b + 2) := by
    refine le_succ_mul ?_
    omega
  have h2 : (n + 1) * (bt + 2 * shearPivotExp n b + 2) ≤
      (n + 1) * (bt + 2 * shearPivotExp n b + 2) + (b + 1) + 1 := by omega
  exact le_succ_mul (h1.trans h2)

/-- The trailing witness exponent `bt` is at most the displayed shear output exponent assembled
from `n`, `b`, and `bt`. -/
lemma le_shear_output_bt (n b bt : ℕ) :
    bt ≤ (n + 1) * ((n + 1) * (bt + 2 * shearPivotExp n b + 2) + (b + 1) + 1) := by
  have h1 : bt ≤ (n + 1) * (bt + 2 * shearPivotExp n b + 2) :=
    le_succ_mul (by omega)
  have h2 : (n + 1) * (bt + 2 * shearPivotExp n b + 2) ≤
      (n + 1) * (bt + 2 * shearPivotExp n b + 2) + (b + 1) + 1 := by omega
  exact le_succ_mul (h1.trans h2)

/-- A pivot extension has witness height-bound exponent `(n + 1) * (bt + (b + b + 1) + 1)` when
the pivot and row have exponent `b` and the trailing witness has exponent `bt`. -/
lemma diagWitness_pivot_bitLe {n : ℕ} {r : ℚ} (hr : r ≠ 0)
    (u : Matrix (Fin 1) (Fin n) ℚ) (C : Matrix (Fin n) (Fin n) ℚ)
    (w : DiagWitness (C - uᵀ * (oneByOne r⁻¹ * u)))
    {b bt : ℕ} (hrb : BitLe b r) (hub : MatBitLe b u)
    (hwb : WitnessBitLe bt w) :
    WitnessBitLe ((n + 1) * (bt + (b + b + 1) + 1)) (diagWitness_pivot hr u C w) := by
  constructor
  · rw [diagWitness_pivot_M]
    have hdiag : MatBitLe bt (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 w.M) :=
      matBitLe_fromBlocks matBitLe_one matBitLe_zero matBitLe_zero hwb.1
    have ht : MatBitLe (b + b + 1) (oneByOne r⁻¹ * u) := by
      simpa using! matBitLe_mul (κ := Fin 1) (matBitLe_oneByOne hrb.inv) hub
    have hup : MatBitLe (b + b + 1)
        (upperUnit (oneByOne r⁻¹ * u)) := by
      refine matBitLe_fromBlocks matBitLe_one ht matBitLe_zero matBitLe_one
    have hmul := matBitLe_mul (κ := Fin 1 ⊕ Fin n) hdiag hup
    simpa [Fintype.card_sum, Nat.add_comm] using! hmul
  · intro i
    rw [diagWitness_pivot_d]
    rcases i with i | i
    · exact hrb.mono (le_succ_mul (by omega))
    · exact (hwb.2 i).mono (le_succ_mul (by omega))

/-- A zero-pivot extension preserves the trailing witness's height-bound exponent. -/
lemma diagWitness_zero_bitLe {n : ℕ} {u : Matrix (Fin 1) (Fin n) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} (hu : u = 0) (w : DiagWitness C)
    {bt : ℕ} (hwb : WitnessBitLe bt w) :
    WitnessBitLe bt (diagWitness_zero hu w) := by
  constructor
  · rw [diagWitness_zero_M]
    exact matBitLe_fromBlocks matBitLe_one matBitLe_zero matBitLe_zero hwb.1
  · intro i
    rw [diagWitness_zero_d]
    rcases i with i | i
    · exact bitLe_zero bt
    · exact hwb.2 i

/-- Under the stated bounds on the shear coefficient, row, new pivot, and trailing witness, the
shear witness satisfies the displayed assembled height bound. -/
lemma diagWitness_shear_bitLe {n : ℕ} {r : ℚ} {u : Matrix (Fin 1) (Fin n) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} (hC : Cᵀ = C) {c : ℚ} {r' : ℚ}
    {u' : Matrix (Fin 1) (Fin n) ℚ}
    (hr' : r' = r + 2 * c * ((u * uᵀ) 0 0) + c ^ 2 * ((u * C * uᵀ) 0 0))
    (hu' : u' = u + c • (u * C)) (hne : r' ≠ 0)
    (w : DiagWitness (C - u'ᵀ * (oneByOne r'⁻¹ * u')))
    {b bt : ℕ} (hc : BitLe 1 c) (hub : MatBitLe b u)
    (hr'B : BitLe (shearPivotExp n b) r') (hu'B : MatBitLe (shearRowExp n b) u')
    (hwb : WitnessBitLe bt w) :
    WitnessBitLe ((n + 1) * ((n + 1) * (bt + 2 * shearPivotExp n b + 2) + (b + 1) + 1))
      (diagWitness_shear hC hr' hu' hne w) := by
  have hmono1 : shearRowExp n b ≤ shearPivotExp n b := by
    unfold shearRowExp shearPivotExp
    omega
  have hmono2 : b ≤ shearPivotExp n b := by
    unfold shearPivotExp
    omega
  have hwp : WitnessBitLe ((n + 1) * (bt + (shearPivotExp n b + shearPivotExp n b + 1) + 1))
      (diagWitness_pivot (r := r') hne u' C w) :=
    diagWitness_pivot_bitLe hne u' C w hr'B (hu'B.mono hmono1) hwb
  constructor
  · rw [diagWitness_shear_M]
    have hs : MatBitLe (b + 1) (c • uᵀ) := by
      have := MatBitLe.smul hc hub.transpose
      simpa [Nat.add_comm] using! this
    have hlow : MatBitLe (b + 1) (lowerUnit (-(c • uᵀ))) :=
      matBitLe_fromBlocks matBitLe_one matBitLe_zero hs.neg matBitLe_one
    have hmul := matBitLe_mul (κ := Fin 1 ⊕ Fin n) hwp.1 hlow
    refine hmul.mono (le_of_eq ?_)
    simp only [Fintype.card_sum, Fintype.card_fin]
    ring
  · intro i
    rw [diagWitness_shear_d, diagWitness_pivot_d]
    rcases i with i | i
    · simpa using! hr'B.mono (le_shear_output_pivot n b bt)
    · simpa using! (hwb.2 i).mono (le_shear_output_bt n b bt)

/-- A witness height bound remains valid when its exponent is increased. -/
lemma WitnessBitLe.mono {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℚ}
    {b b' : ℕ} (h : b ≤ b') {w : DiagWitness B} (hw : WitnessBitLe b w) :
    WitnessBitLe b' w :=
  ⟨hw.1.mono h, fun i => (hw.2 i).mono h⟩

/-- Transferring a witness across an index equivalence preserves its height bound. -/
lemma WitnessBitLe.reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) {B : Matrix ι ι ℚ} {w : DiagWitness (Matrix.reindex e e B)}
    {b : ℕ} (h : WitnessBitLe b w) :
    WitnessBitLe b (diagWitness_reindex e (w := w)) := by
  constructor
  · rw [diagWitness_reindex_M]
    intro i j
    rw [Matrix.reindex_apply]
    exact h.1 _ _
  · intro i
    rw [diagWitness_reindex_d]
    exact h.2 (e i)

/-- Transporting a witness along an equality of matrices preserves its height bound. -/
lemma WitnessBitLe.cast {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B B' : Matrix ι ι ℚ} (h : B = B') {b : ℕ} {w : DiagWitness B}
    (hw : WitnessBitLe b w) : WitnessBitLe b (h ▸ w) := by
  cases h
  exact hw

/-- A witness satisfies a given height bound after transport along a matrix equality exactly
when it does before transport. -/
lemma witnessBitLe_cast_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B B' : Matrix ι ι ℚ} (h : B = B') {b : ℕ} {w : DiagWitness B} :
    WitnessBitLe b (h ▸ w) ↔ WitnessBitLe b w := by
  cases h
  exact Iff.rfl

/-- A transferred witness satisfies a given height bound exactly when the original witness does. -/
lemma witnessBitLe_reindex_iff {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) {B : Matrix ι ι ℚ} {w : DiagWitness (Matrix.reindex e e B)}
    {b : ℕ} :
    WitnessBitLe b (diagWitness_reindex e (w := w)) ↔ WitnessBitLe b w := by
  constructor
  · intro h
    constructor
    · intro i j
      have h' := h.1 (e.symm i) (e.symm j)
      simpa [diagWitness_reindex_M, Matrix.reindex_apply] using! h'
    · intro i
      have h' := h.2 (e.symm i)
      simpa [diagWitness_reindex_d, Function.comp] using! h'
  · exact WitnessBitLe.reindex e

/-- An entrywise height bound on a block matrix bounds its leading pivot with the same exponent. -/
lemma blockPivot_bitLe {n b : ℕ} {B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℚ}
    (hB : MatBitLe b B) : BitLe b (blockPivot B) :=
  hB (Sum.inl 0) (Sum.inl 0)

/-- An entrywise height bound on a block matrix bounds its upper-right row with the same
exponent. -/
lemma blockRow_bitLe {n b : ℕ} {B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℚ}
    (hB : MatBitLe b B) : MatBitLe b (blockRow B) :=
  fun _ j => hB (Sum.inl 0) (Sum.inr j)

/-- An entrywise height bound on a block matrix bounds its trailing square block with the same
exponent. -/
lemma blockTail_bitLe {n b : ℕ} {B : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℚ}
    (hB : MatBitLe b B) : MatBitLe b (blockTail B) :=
  fun i j => hB (Sum.inr i) (Sum.inr j)

/-- The rational number two satisfies `BitLe 1`. -/
lemma bitLe_two : BitLe 1 (2 : ℚ) := by
  unfold BitLe
  rw [show Height (2 : ℚ) = 2 from by decide]
  exact le_refl _

/-- The coefficient selected by `shearCoeff` satisfies `BitLe 1`. -/
lemma shearCoeff_bitLe (a b : ℚ) (ha : a ≠ 0) : BitLe 1 (shearCoeff a b ha).1 := by
  unfold shearCoeff
  split
  · exact bitLe_one 1
  · exact bitLe_two

/-- The Schur complement has entrywise height-bound exponent `bC + br + 2 * bu + 3` under the
respective bounds on its matrix, pivot, and row. -/
lemma schur_bitLe {n bC br bu : ℕ} {r : ℚ} {u : Matrix (Fin 1) (Fin n) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} (hr : BitLe br r) (hu : MatBitLe bu u)
    (hC : MatBitLe bC C) :
    MatBitLe (bC + br + 2 * bu + 3) (C - uᵀ * (oneByOne r⁻¹ * u)) := by
  have h1 : MatBitLe (br + bu + 1) (oneByOne r⁻¹ * u) := by
    simpa using! matBitLe_mul (κ := Fin 1) (matBitLe_oneByOne hr.inv) hu
  have h2 : MatBitLe (bu + (br + bu + 1) + 1) (uᵀ * (oneByOne r⁻¹ * u)) := by
    simpa using! matBitLe_mul (κ := Fin 1) hu.transpose h1
  have h3 : MatBitLe (bC + (bu + (br + bu + 1) + 1) + 1)
      (C - uᵀ * (oneByOne r⁻¹ * u)) :=
    MatBitLe.sub (b₁ := bC) (b₂ := bu + (br + bu + 1) + 1) hC h2
  refine h3.mono (le_of_eq ?_)
  ring

/-- A common exponent `b` for the pivot, row, and trailing matrix gives exponent `tailExp n b`
for their Schur complement. -/
lemma schur_bitLe_tail {n b : ℕ} {r : ℚ} {u : Matrix (Fin 1) (Fin n) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} (hr : BitLe b r) (hu : MatBitLe b u)
    (hC : MatBitLe b C) :
    MatBitLe (tailExp n b) (C - uᵀ * (oneByOne r⁻¹ * u)) := by
  have h := schur_bitLe (br := b) (bu := b) (bC := b) hr hu hC
  refine h.mono ?_
  unfold tailExp shearPivotExp shearRowExp
  omega

/-- A coefficient satisfying `BitLe 1` and input row and matrix bounds with exponent `b` give
exponent `shearRowExp n b` for the sheared row. -/
lemma shearRow_bitLe {n b : ℕ} {u : Matrix (Fin 1) (Fin n) ℚ}
    {C : Matrix (Fin n) (Fin n) ℚ} {c : ℚ} (hc : BitLe 1 c)
    (hu : MatBitLe b u) (hC : MatBitLe b C) :
    MatBitLe (shearRowExp n b) (u + c • (u * C)) := by
  have h1 : MatBitLe (n * (b + b + 1)) (u * C) := by
    simpa using! matBitLe_mul hu hC
  have h2 : MatBitLe (1 + n * (b + b + 1)) (c • (u * C)) :=
    MatBitLe.smul hc h1
  have h3 : MatBitLe (b + (1 + n * (b + b + 1)) + 1) (u + c • (u * C)) :=
    MatBitLe.add hu h2
  refine h3.mono (le_of_eq ?_)
  unfold shearRowExp
  ring

/-- The stated height bounds on the scalar inputs give exponent `shearPivotExp n b` for the
updated pivot. -/
lemma shearPivot_bitLe {n b : ℕ} {r c a bb : ℚ} (hr : BitLe b r) (hc : BitLe 1 c)
    (ha : BitLe (n * (b + b + 1)) a) (hb : BitLe (n * (n * (b + b + 1) + b + 1)) bb) :
    BitLe (shearPivotExp n b) (r + 2 * c * a + c ^ 2 * bb) := by
  have h2 : BitLe 1 (2 : ℚ) := by
    unfold BitLe
    rw [show Height (2 : ℚ) = 2 from by decide]
    exact le_refl _
  have h2c : BitLe (1 + 1) (2 * c) := h2.mul hc
  have h2ca : BitLe (1 + 1 + n * (b + b + 1)) (2 * c * a) := h2c.mul ha
  have hcc : BitLe (1 + 1) (c ^ 2) := by
    rw [pow_two]
    exact hc.mul hc
  have hccb : BitLe (1 + 1 + n * (n * (b + b + 1) + b + 1)) (c ^ 2 * bb) := hcc.mul hb
  have hfirst : BitLe (b + (1 + 1 + n * (b + b + 1)) + 1) (r + 2 * c * a) :=
    hr.add h2ca
  have hsum : BitLe ((b + (1 + 1 + n * (b + b + 1)) + 1)
      + (1 + 1 + n * (n * (b + b + 1) + b + 1)) + 1) (r + 2 * c * a + c ^ 2 * bb) :=
    hfirst.add hccb
  refine hsum.mono (le_of_eq ?_)
  unfold shearPivotExp
  ring

/-- The pivot witness output exponent is at most the shear witness output exponent for the same
`n`, `b`, and `bt`. -/
lemma pivot_output_le_costExp (n b bt : ℕ) :
    (n + 1) * (bt + (b + b + 1) + 1) ≤
      (n + 1) * ((n + 1) * (bt + 2 * shearPivotExp n b + 2) + (b + 1) + 1) := by
  refine Nat.mul_le_mul_left _ ?_
  have h1 : bt + (b + b + 1) + 1 ≤ (n + 1) * (bt + 2 * shearPivotExp n b + 2) := by
    refine le_succ_mul ?_
    have := le_shearPivotExp n b
    omega
  omega

/-- Increasing the dimension by one does not decrease `costExp`. -/
lemma costExp_le_succ (n b : ℕ) : costExp n b ≤ costExp (n + 1) b := by
  show costExp n b ≤ (n + 1) * ((n + 1) * (costExp n (tailExp n b)
    + 2 * shearPivotExp n b + 2) + (b + 1) + 1) + costExp n b
  exact Nat.le_add_left _ _

/-- Every natural number `n` is at most `2 ^ n`. -/
lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [Nat.pow_succ]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

/-- Reindexing a rational matrix along an equivalence preserves its entrywise height bound. -/
lemma matBitLe_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) {B : Matrix ι ι ℚ} {b : ℕ} (h : MatBitLe b B) :
    MatBitLe b (Matrix.reindex e e B) :=
  fun i j => by rw [Matrix.reindex_apply]; exact h _ _

/-- For a symmetric rational matrix with entrywise exponent `b`, the witness produced by
`diagAux` has height-bound exponent `costExp n b`. -/
theorem diagAux_bitLe (n : ℕ) :
    ∀ (B : Matrix (Fin n) (Fin n) ℚ) (hB : IsSymmRat B) (b : ℕ), MatBitLe b B →
      WitnessBitLe (costExp n b) (diagAux n B hB) := by
  induction n with
  | zero =>
    intro B hB b _
    exact ⟨matBitLe_one, fun i => i.elim0⟩
  | succ n ih =>
    intro B hB b hb
    let B' : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℚ :=
      (Matrix.reindex (finSplit n) (finSplit n)) B
    have hb' : MatBitLe b B' := matBitLe_reindex (finSplit n) hb
    have hs : B'ᵀ = B' := by
      show ((Matrix.reindex (finSplit n) (finSplit n)) B)ᵀ
        = (Matrix.reindex (finSplit n) (finSplit n)) B
      rw [Matrix.transpose_reindex, hB]
    have hC' : (blockTail B')ᵀ = blockTail B' := blockTail_transpose hs
    rw [diagAux.eq_def]
    (try dsimp only)
    split
    · rename_i hr
      have hdec : B' = fromBlocks (oneByOne (blockPivot B')) (blockRow B')
          (blockRow B')ᵀ (blockTail B') := fromBlocks_block hs
      have hcd : MatBitLe (tailExp n b)
          (blockTail B' - (blockRow B')ᵀ * (oneByOne (blockPivot B')⁻¹ * blockRow B')) :=
        schur_bitLe_tail (blockPivot_bitLe hb') (blockRow_bitLe hb') (blockTail_bitLe hb')
      have hw : WitnessBitLe (costExp n (tailExp n b))
          (diagAux n (blockTail B' - (blockRow B')ᵀ *
            (oneByOne (blockPivot B')⁻¹ * blockRow B'))
            (schur_transpose hC' (blockRow B') (blockPivot B')⁻¹)) :=
        ih _ _ (tailExp n b) hcd
      have hp : WitnessBitLe ((n + 1) * (costExp n (tailExp n b) + (b + b + 1) + 1))
          (diagWitness_pivot hr (blockRow B') (blockTail B') (diagAux n _ _)) :=
        diagWitness_pivot_bitLe hr (blockRow B') (blockTail B') (diagAux n _ _)
          (blockPivot_bitLe hb') (blockRow_bitLe hb') hw
      refine WitnessBitLe.mono
        (b := (n + 1) * (costExp n (tailExp n b) + (b + b + 1) + 1)) ?_ ?_
      · exact (pivot_output_le_costExp n b (costExp n (tailExp n b))).trans
          (Nat.le_add_right _ _)
      · refine (WitnessBitLe.reindex (finSplit n) ?_)
        exact (witnessBitLe_cast_iff (h := hdec.symm)).mpr hp
    · split
      · rename_i hr0 hu
        have hdec0 : B' = fromBlocks (oneByOne 0) (blockRow B') (blockRow B')ᵀ
            (blockTail B') := fromBlocks_block_zero hs (not_not.mp hr0)
        have hw : WitnessBitLe (costExp n b) (diagAux n (blockTail B') hC') :=
          ih _ _ b (blockTail_bitLe hb')
        have hz : WitnessBitLe (costExp n b)
            (diagWitness_zero hu (diagAux n (blockTail B') hC')) :=
          diagWitness_zero_bitLe hu (diagAux n (blockTail B') hC') hw
        refine WitnessBitLe.mono (b := costExp n b) (costExp_le_succ n b) ?_
        refine (WitnessBitLe.reindex (finSplit n) ?_)
        exact (witnessBitLe_cast_iff (h := hdec0.symm)).mpr hz
      · rename_i hr0 hu
        let a : ℚ := ((blockRow B') * (blockRow B')ᵀ) 0 0
        let bb : ℚ := ((blockRow B') * (blockTail B') * (blockRow B')ᵀ) 0 0
        let c : ℚ := (shearCoeff a bb (rowVec_mul_self_ne_zero hu)).1
        let u' : Matrix (Fin 1) (Fin n) ℚ := blockRow B' + c • (blockRow B' * blockTail B')
        let r' : ℚ := blockPivot B' + 2 * c * a + c ^ 2 * bb
        have hdec : B' = fromBlocks (oneByOne (blockPivot B')) (blockRow B')
            (blockRow B')ᵀ (blockTail B') := fromBlocks_block hs
        have ha : a ≠ 0 := rowVec_mul_self_ne_zero hu
        have hc : BitLe 1 c := shearCoeff_bitLe a bb ha
        have haB : BitLe (n * (b + b + 1)) a := by
          have h := matBitLe_mul (κ := Fin n) (blockRow_bitLe hb')
            (blockRow_bitLe hb').transpose
          simpa [a] using! h 0 0
        have hbB : BitLe (n * (n * (b + b + 1) + b + 1)) bb := by
          have h1 := matBitLe_mul (κ := Fin n) (blockRow_bitLe hb') (blockTail_bitLe hb')
          have h2 := matBitLe_mul (κ := Fin n) h1 (blockRow_bitLe hb').transpose
          simpa [bb] using! h2 0 0
        have hr'B : BitLe (shearPivotExp n b) r' :=
          shearPivot_bitLe (blockPivot_bitLe hb') hc haB hbB
        have hu'B : MatBitLe (shearRowExp n b) u' :=
          shearRow_bitLe hc (blockRow_bitLe hb') (blockTail_bitLe hb')
        have hcd : MatBitLe (tailExp n b)
            (blockTail B' - u'ᵀ * (oneByOne r'⁻¹ * u')) := by
          have h := schur_bitLe (br := shearPivotExp n b) (bu := shearRowExp n b)
            (bC := b) hr'B hu'B (blockTail_bitLe hb')
          simpa [tailExp] using! h
        have hne : r' ≠ 0 := by
          show blockPivot B' + 2 * c * a + c ^ 2 * bb ≠ 0
          rw [not_not.mp hr0, zero_add]
          exact (shearCoeff a bb ha).2
        have hw : WitnessBitLe (costExp n (tailExp n b))
            (diagAux n (blockTail B' - u'ᵀ * (oneByOne r'⁻¹ * u'))
              (schur_transpose hC' u' r'⁻¹)) :=
          ih _ _ (tailExp n b) hcd
        have hsh : WitnessBitLe ((n + 1) * ((n + 1) * (costExp n (tailExp n b)
            + 2 * shearPivotExp n b + 2) + (b + 1) + 1))
            (diagWitness_shear hC' rfl rfl hne (diagAux n _ _)) :=
          diagWitness_shear_bitLe hC' rfl rfl hne (diagAux n _ _) hc
            (blockRow_bitLe hb') hr'B hu'B hw
        refine WitnessBitLe.mono
          (b := (n + 1) * ((n + 1) * (costExp n (tailExp n b)
            + 2 * shearPivotExp n b + 2) + (b + 1) + 1)) ?_ ?_
        · exact Nat.le_add_right _ _
        · refine (WitnessBitLe.reindex (finSplit n) ?_)
          exact (witnessBitLe_cast_iff (h := hdec.symm)).mpr hsh

/-- The sum of the heights of all entries of a rational matrix. -/
def matBits {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  Finset.univ.sum (fun i => Finset.univ.sum (fun j => Height (A i j)))

/-- The height of every entry of `A` is at most `matBits A`. -/
lemma Height_apply_le_matBits {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    Height (A i j) ≤ matBits A := by
  have h1 : Height (A i j) ≤ Finset.univ.sum (fun k => Height (A i k)) :=
    Finset.single_le_sum (f := fun k => Height (A i k)) (fun k _ => Nat.zero_le _)
      (Finset.mem_univ j)
  have h2 : Finset.univ.sum (fun k => Height (A i k))
      ≤ Finset.univ.sum (fun r => Finset.univ.sum fun k => Height (A r k)) :=
    Finset.single_le_sum (f := fun r => Finset.univ.sum fun k => Height (A r k))
      (fun r _ => Nat.zero_le _) (Finset.mem_univ i)
  exact h1.trans h2

/-- Every entry of `A` has height at most `2 ^ matBits A`. -/
lemma matBitLe_matBits {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : MatBitLe (matBits A) A :=
  fun i j => (Height_apply_le_matBits A i j).trans (nat_le_two_pow _)

/-- The scalar shift of `A` by `q` has entrywise height-bound exponent `matBits A + Height q +
1`. -/
lemma shift_bitLe {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (q : ℚ) :
    MatBitLe (matBits A + Height q + 1) (shift A q) := by
  intro i j
  have hA : BitLe (matBits A) (A i j) := matBitLe_matBits A i j
  have hq : BitLe (Height q) q := nat_le_two_pow _
  have hd : BitLe (Height q) (scalar (Fin n) q i j) := by
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split
    · exact hq
    · exact bitLe_zero _
  have := hA.sub hd
  simpa [shift, Matrix.sub_apply] using! this

/-- The witness height-bound exponent obtained by applying `costExp` to the shifted matrix input
bound. -/
def pointBits {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (q : ℚ) : ℕ :=
  costExp n (matBits A + Height q + 1)

/-- The diagonalization witness used by `pointOf` satisfies the exponent bound `pointBits A q`. -/
theorem pointOf_witness_bitLe {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (q : ℚ) :
    WitnessBitLe (pointBits A q) (diagAux n (shift A q) (shift_symm hA q)) :=
  diagAux_bitLe n (shift A q) (shift_symm hA q) (matBits A + Height q + 1) (shift_bitLe A q)

/-- A uniform witness height-bound exponent for all thresholds in the spectral grid. -/
def certificateBits {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) : ℕ :=
  costExp n (matBits A + 2 * (Height (spectrumBound A) *
    ((gridSteps A m + 1) * Height (gridMesh m))) + 1)

/-- Every diagonalization witness used on the spectral grid satisfies the uniform bound
`certificateBits A m`. -/
theorem certifiedPoints_bits {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (m : ℕ) {q : ℚ} (hq : q ∈ gridOf A m) :
    WitnessBitLe (certificateBits A m) (diagAux n (shift A q) (shift_symm hA q)) := by
  have hb : MatBitLe (matBits A + Height q + 1) (shift A q) := shift_bitLe A q
  have hw := diagAux_bitLe n (shift A q) (shift_symm hA q) _ hb
  refine hw.mono ?_
  refine costExp_mono n ?_
  have hgrid := gridOf_height A m hq
  omega

/-- The spectral certificate has the stated total step count, total operation bound, and uniform
witness height bound. -/
theorem frontier1_cost {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (m : ℕ) :
    totalSteps A hA (gridOf A m) = (gridSteps A m + 1) * n ∧
      totalOps A hA (gridOf A m) ≤ (gridSteps A m + 1) * opsBound n ∧
      (∀ q ∈ gridOf A m,
        WitnessBitLe (certificateBits A m) (diagAux n (shift A q) (shift_symm hA q))) :=
  ⟨certifiedPoints_totalSteps A hA m, certifiedPoints_ops A hA m,
    fun _ hq => certifiedPoints_bits A hA m hq⟩

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

variable {n : ℕ}

/-- The rational conditions for `X + iY` to be Hermitian: `X` is symmetric and `Y` is
skew-symmetric. -/
def IsHermRat {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) : Prop := Xᵀ = X ∧ Yᵀ = -Y

/-- The rational real block representation of `X + iY`, with blocks `X`, `-Y`, `Y`, and `X`. -/
def blockReal {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ :=
  fromBlocks X (-Y) Y X

/-- The transpose of the real block representation has the corresponding transposed blocks. -/
theorem blockReal_transpose {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    (blockReal X Y)ᵀ = fromBlocks Xᵀ Yᵀ (-Y)ᵀ Xᵀ := by
  unfold blockReal
  rw [fromBlocks_transpose]

/-- The real block representation of rational Hermitian data is symmetric. -/
theorem blockReal_isSymm {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ} (h : IsHermRat X Y) :
    (blockReal X Y)ᵀ = blockReal X Y := by
  obtain ⟨hX, hY⟩ := h
  rw [blockReal_transpose]
  simp only [hX, hY, Matrix.transpose_neg, neg_neg]
  unfold blockReal
  rfl

/-- A symmetric rational matrix on any finite index type becomes Hermitian after casting its
entries to the reals. -/
theorem realify_isHermitian' {ι : Type*} [Fintype ι] {A : Matrix ι ι ℚ} (hA : Aᵀ = A) :
    (A.map (algebraMap ℚ ℝ)).IsHermitian := by
  have hAh : A.IsHermitian := by
    simpa [Matrix.IsHermitian] using! hA
  exact hAh.map (algebraMap ℚ ℝ) (fun x => by simp)

/-- The real block representation reindexed by `Fin (n + n)`. -/
def blockRealFin {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℚ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (blockReal X Y)

/-- The finite-index real block representation of rational Hermitian data is symmetric. -/
theorem blockRealFin_symm {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ} (h : IsHermRat X Y) :
    IsSymmRat (blockRealFin X Y) := by
  unfold blockRealFin IsSymmRat
  rw [Matrix.transpose_reindex, blockReal_isSymm h]

/-- The complex matrix with rational real part `X` and rational imaginary part `Y`. -/
noncomputable def cplx {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℂ :=
  X.map (algebraMap ℚ ℂ) + Complex.I • Y.map (algebraMap ℚ ℂ)

/-- Rational data satisfying `IsHermRat` define a Hermitian complex matrix. -/
theorem cplx_isHermitian {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ} (h : IsHermRat X Y) :
    (cplx X Y).IsHermitian := by
  obtain ⟨hX, hY⟩ := h
  ext i j
  rw [Matrix.conjTranspose_apply]
  simp only [cplx, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  have hx : X j i = X i j := by
    have h := congrArg (fun M => M j i) hX
    simpa [Matrix.transpose_apply] using! h.symm
  have hy : Y j i = -Y i j := by
    have h : Y i j = -Y j i := by
      have h' := congrArg (fun M => M j i) hY
      simpa [Matrix.transpose_apply] using! h'
    simpa using! (congrArg Neg.neg h).symm
  rw [hx, hy]
  rw [star_add, star_mul']
  simp

/-- The complex matrix obtained by casting every rational entry of `M`. -/
noncomputable def matC {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℂ :=
  M.map (algebraMap ℚ ℂ)

/-- The complex block matrix obtained by casting the blocks of the real representation of `X +
iY`. -/
noncomputable def blockCplx {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  fromBlocks (matC X) (-(matC Y)) (matC Y) (matC X)

/-- The complex block representation is the entrywise complex cast of the rational real block
representation. -/
lemma blockCplx_eq_map {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    blockCplx X Y = (blockReal X Y).map (algebraMap ℚ ℂ) := by
  unfold blockCplx blockReal
  rw [fromBlocks_map]
  rw [Matrix.map_neg (f := (algebraMap ℚ ℂ)) (fun a => by simp)]
  simp only [matC]

/-- The entrywise complex conjugate of `cplx X Y`. -/
noncomputable def conjCplx {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (cplx X Y).map (starRingEnd ℂ)

/-- The conjugate complex matrix equals `matC X - Complex.I • matC Y`. -/
lemma conjCplx_sub {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    conjCplx X Y = matC X - Complex.I • matC Y := by
  ext i j
  simp [conjCplx, cplx, matC, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    sub_eq_add_neg]

/-- Left multiplication by a scalar multiple of the complex identity equals scalar
multiplication of the matrix. -/
lemma smul_one_mul_mat {n : ℕ} (a : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    (a • (1 : Matrix (Fin n) (Fin n) ℂ)) * M = a • M := by
  rw [Matrix.smul_mul, Matrix.one_mul]

/-- Right multiplication by a scalar multiple of the complex identity equals scalar
multiplication of the matrix. -/
lemma mul_smul_one_mat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (a : ℂ) :
    M * (a • (1 : Matrix (Fin n) (Fin n) ℂ)) = a • M := by
  rw [Matrix.mul_smul, Matrix.mul_one]

/-- The complex scalar one half. -/
noncomputable def c2 : ℂ := (2 : ℂ)⁻¹

/-- The block change of coordinates with rows `(1, i)` and `(1, -i)` that separates the complex
matrix and its conjugate. -/
noncomputable def simS {n : ℕ} : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  fromBlocks 1 (Complex.I • 1) 1 ((-Complex.I) • 1)

/-- The inverse block change of coordinates to `simS`, with blocks one half, one half, minus `i
/ 2`, and `i / 2`. -/
noncomputable def simT {n : ℕ} : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  fromBlocks (c2 • 1) (c2 • 1) ((-(c2 * Complex.I)) • 1) ((c2 * Complex.I) • 1)

/-- Adding the complex scalar `c2` to itself gives one. -/
lemma scalar_half_add : c2 + c2 = (1 : ℂ) := by
  unfold c2
  norm_num

/-- Multiplying `i` by `-(c2 * i)` gives `c2`. -/
lemma scalar_cancel_I : Complex.I * (-(c2 * Complex.I)) = c2 := by
  have h : Complex.I * (-(c2 * Complex.I)) = -(c2 * (Complex.I * Complex.I)) := by ring
  rw [h, Complex.I_mul_I]
  ring

/-- Multiplying `i` by `c2 * i` gives `-c2`. -/
lemma scalar_cancel_I' : Complex.I * (c2 * Complex.I) = -c2 := by
  have h : Complex.I * (c2 * Complex.I) = c2 * (Complex.I * Complex.I) := by ring
  rw [h, Complex.I_mul_I]
  ring

/-- Multiplying `-i` by `-(c2 * i)` gives `-c2`. -/
lemma scalar_cancel_I'' : (-Complex.I) * (-(c2 * Complex.I)) = -c2 := by
  have h : (-Complex.I) * (-(c2 * Complex.I)) = c2 * (Complex.I * Complex.I) := by ring
  rw [h, Complex.I_mul_I]
  ring

/-- Multiplying `-i` by `c2 * i` gives `c2`. -/
lemma scalar_cancel_I''' : (-Complex.I) * (c2 * Complex.I) = c2 := by
  have h : (-Complex.I) * (c2 * Complex.I) = -(c2 * (Complex.I * Complex.I)) := by ring
  rw [h, Complex.I_mul_I]
  ring

/-- The product `simS * simT` is the identity matrix. -/
lemma simS_mul_simT {n : ℕ} : simS (n := n) * simT = 1 := by
  unfold simS simT
  rw [fromBlocks_multiply, ← fromBlocks_one (l := Fin n) (m := Fin n), fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.one_mul, smul_one_mul_mat, smul_smul, scalar_cancel_I, ← add_smul,
      scalar_half_add, one_smul]
  · rw [Matrix.one_mul, smul_one_mul_mat, smul_smul, scalar_cancel_I', ← add_smul]
    rw [show c2 + -c2 = (0 : ℂ) from by ring, zero_smul]
  · rw [Matrix.one_mul, smul_one_mul_mat, smul_smul, scalar_cancel_I'', ← add_smul,
      show c2 + -c2 = (0 : ℂ) from by ring, zero_smul]
  · rw [Matrix.one_mul, smul_one_mul_mat, smul_smul, scalar_cancel_I''', ← add_smul,
      scalar_half_add, one_smul]

/-- The product `simT * simS` is the identity matrix. -/
lemma simT_mul_simS {n : ℕ} : simT (n := n) * simS = 1 := by
  unfold simS simT
  rw [fromBlocks_multiply, ← fromBlocks_one (l := Fin n) (m := Fin n), fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_one]
    rw [← add_smul, scalar_half_add, one_smul]
  · rw [mul_smul_one_mat, mul_smul_one_mat, ← add_smul,
      show Complex.I + -Complex.I = (0 : ℂ) from by ring, zero_smul]
  · simp only [Matrix.mul_one]
    rw [← add_smul,
      show -(c2 * Complex.I) + c2 * Complex.I = (0 : ℂ) from by ring, zero_smul]
  · rw [mul_smul_one_mat, mul_smul_one_mat, smul_smul, smul_smul, ← add_smul,
      scalar_cancel_I, scalar_cancel_I''', scalar_half_add, one_smul]

/-- The product of `-i` and `i` is one. -/
lemma scalar_negI_mul_I : (-Complex.I) * Complex.I = (1 : ℂ) := by
  have h : (-Complex.I) * Complex.I = -(Complex.I * Complex.I) := by ring
  rw [h, Complex.I_mul_I]
  ring

/-- The matrix `simS` intertwines the complex block representation with the block diagonal
matrix of `cplx X Y` and its conjugate. -/
lemma simS_mul_blockCplx {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    simS * blockCplx X Y = fromBlocks (cplx X Y) 0 0 (conjCplx X Y) * simS := by
  unfold simS blockCplx
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.one_mul, smul_one_mul_mat, Matrix.mul_one, Matrix.zero_mul, add_zero]
    rfl
  · rw [Matrix.one_mul, smul_one_mul_mat, mul_smul_one_mat, Matrix.zero_mul, add_zero]
    rw [show cplx X Y = matC X + Complex.I • matC Y from rfl]
    rw [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
    abel
  · rw [conjCplx_sub, Matrix.one_mul, smul_one_mul_mat, Matrix.zero_mul, zero_add, neg_smul,
      sub_eq_add_neg, Matrix.mul_one]
  · rw [conjCplx_sub, Matrix.zero_mul, Matrix.one_mul, smul_one_mul_mat,
      mul_smul_one_mat, zero_add, smul_sub, smul_smul, scalar_negI_mul_I, one_smul]
    abel

/-- For rational Hermitian data, the complex matrix and its entrywise conjugate have the same
characteristic polynomial. -/
lemma charpoly_conjCplx {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ} (h : IsHermRat X Y) :
    (conjCplx X Y).charpoly = (cplx X Y).charpoly := by
  have hC : (cplx X Y).IsHermitian := cplx_isHermitian h
  unfold conjCplx
  rw [Matrix.charpoly_map, hC.charpoly_eq, Polynomial.map_prod]
  refine Finset.prod_congr rfl ?_
  intro i _
  simp [Complex.conj_ofReal]

/-- For rational Hermitian data, the characteristic polynomial of the complex block
representation is the square of that of `cplx X Y`. -/
lemma charpoly_blockCplx_eq {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ} (h : IsHermRat X Y) :
    (blockCplx X Y).charpoly = (cplx X Y).charpoly ^ 2 := by
  have hSB := simS_mul_blockCplx X Y
  have hB : blockCplx X Y = simT * fromBlocks (cplx X Y) 0 0 (conjCplx X Y) * simS := by
    calc blockCplx X Y = (simT * simS) * blockCplx X Y := by rw [simT_mul_simS, one_mul]
      _ = simT * (simS * blockCplx X Y) := by rw [mul_assoc]
      _ = simT * (fromBlocks (cplx X Y) 0 0 (conjCplx X Y) * simS) := by rw [hSB]
      _ = simT * fromBlocks (cplx X Y) 0 0 (conjCplx X Y) * simS := by rw [mul_assoc]
  rw [hB]
  calc (simT * fromBlocks (cplx X Y) 0 0 (conjCplx X Y) * simS).charpoly
      = (simS * (simT * fromBlocks (cplx X Y) 0 0 (conjCplx X Y))).charpoly :=
        Matrix.charpoly_mul_comm _ _
    _ = ((simS * simT) * fromBlocks (cplx X Y) 0 0 (conjCplx X Y)).charpoly := by rw [mul_assoc]
    _ = (fromBlocks (cplx X Y) 0 0 (conjCplx X Y)).charpoly := by rw [simS_mul_simT, one_mul]
    _ = (cplx X Y).charpoly * (conjCplx X Y).charpoly := charpoly_fromBlocks_zero₁₂ _ _ _
    _ = (cplx X Y).charpoly * (cplx X Y).charpoly := by rw [charpoly_conjCplx h]
    _ = (cplx X Y).charpoly ^ 2 := by ring

/-- Casting rational matrix entries first to the reals and then to the complexes equals casting
directly to the complexes. -/
lemma map_rat_real_complex {m n : Type*} (M : Matrix m n ℚ) :
    (M.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ) = M.map (algebraMap ℚ ℂ) := by
  rw [Matrix.map_map]
  have h : ((algebraMap ℝ ℂ) ∘ (algebraMap ℚ ℝ)) = (algebraMap ℚ ℂ) := by
    ext q
    simp
  rw [h]

/-- The characteristic polynomial of the real block representation, mapped to the complexes, is
the square of the complex matrix's characteristic polynomial. -/
lemma charpoly_blockReal_map {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ} (h : IsHermRat X Y) :
    ((blockReal X Y).map (algebraMap ℚ ℝ)).charpoly.map (algebraMap ℝ ℂ)
      = (cplx X Y).charpoly ^ 2 := by
  rw [← Matrix.charpoly_map, map_rat_real_complex]
  rw [← blockCplx_eq_map]
  exact charpoly_blockCplx_eq h

/-- The roots of a product of complex linear factors form the multiset of their specified roots. -/
lemma roots_prod_X_sub_C_cplx {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    (∏ i, (Polynomial.X - Polynomial.C (v i))).roots = Finset.univ.val.map v := by
  classical
  have hne : (∏ i : ι, (Polynomial.X - Polynomial.C (v i))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact Polynomial.X_sub_C_ne_zero (v i)
  rw [Polynomial.roots_prod (fun i => Polynomial.X - Polynomial.C (v i)) Finset.univ hne]
  simp [Polynomial.roots_X_sub_C, Multiset.bind_singleton]

/-- Mapping a multiset commutes with doubling its multiplicities. -/
lemma multiset_map_two_smul {α β : Type*} (f : α → β) (s : Multiset α) :
    Multiset.map f (2 • s) = 2 • Multiset.map f s := by
  rw [two_smul ℕ s, two_smul ℕ (Multiset.map f s), Multiset.map_add]

/-- The eigenvalue multiset of the real block representation is the complex Hermitian matrix's
eigenvalue multiset with every multiplicity doubled. -/
theorem eigenvalues_block_eq_two_mul {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ}
    (h : IsHermRat X Y) :
    (Finset.univ.val.map (realify_isHermitian' (blockReal_isSymm h)).eigenvalues)
      = 2 • (Finset.univ.val.map (cplx_isHermitian h).eigenvalues) := by
  classical
  have hB : ((blockReal X Y).map (algebraMap ℚ ℝ)).IsHermitian :=
    realify_isHermitian' (blockReal_isSymm h)
  have hC : (cplx X Y).IsHermitian := cplx_isHermitian h
  have hpoly : (∏ j, (Polynomial.X - Polynomial.C ((hB.eigenvalues j : ℝ) : ℂ)))
      = (∏ i, (Polynomial.X - Polynomial.C ((hC.eigenvalues i : ℝ) : ℂ))) ^ 2 := by
    have hmap := charpoly_blockReal_map h
    rw [hB.charpoly_eq, hC.charpoly_eq, Polynomial.map_prod] at hmap
    simpa only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] using! hmap
  have hroots := congrArg Polynomial.roots hpoly
  rw [roots_prod_X_sub_C_cplx, Polynomial.roots_pow, roots_prod_X_sub_C_cplx] at hroots
  have hcast : (Finset.univ.val.map fun j => ((hB.eigenvalues j : ℝ) : ℂ))
      = 2 • (Finset.univ.val.map fun i => ((hC.eigenvalues i : ℝ) : ℂ)) := hroots
  apply Multiset.map_injective Complex.ofReal_injective
  rw [Multiset.map_map, multiset_map_two_smul, Multiset.map_map]
  exact hcast

/-- Casting rational matrix entries to the reals commutes with reindexing. -/
lemma realify_reindex {ι κ : Type*} (e : ι ≃ κ) (A : Matrix ι ι ℚ) :
    (Matrix.reindex e e A).map (algebraMap ℚ ℝ) = Matrix.reindex e e (A.map (algebraMap ℚ ℝ)) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_map]

/-- Two real Hermitian matrices with the same characteristic polynomial have the same eigenvalue
multiset. -/
lemma eigenvalues_eq_of_charpoly {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {B : Matrix ι ι ℝ} {C : Matrix κ κ ℝ} (hB : B.IsHermitian)
    (hC : C.IsHermitian) (h : B.charpoly = C.charpoly) :
    (Finset.univ.val.map hB.eigenvalues) = (Finset.univ.val.map hC.eigenvalues) := by
  have hB' : B.charpoly.roots = Finset.univ.val.map hB.eigenvalues := by
    simpa using! hB.roots_charpoly_eq_eigenvalues
  have hC' : C.charpoly.roots = Finset.univ.val.map hC.eigenvalues := by
    simpa using! hC.roots_charpoly_eq_eigenvalues
  rw [← hB', ← hC', h]

/-- Filtering a multiset commutes with doubling its multiplicities. -/
lemma multiset_filter_two_smul {α : Type*} (p : α → Prop) [DecidablePred p] (s : Multiset α) :
    Multiset.filter p (2 • s) = 2 • Multiset.filter p s := by
  rw [two_smul ℕ s, two_smul ℕ (Multiset.filter p s), Multiset.filter_add]

/-- Doubling every multiplicity doubles a multiset's cardinality. -/
lemma multiset_card_two_smul {α : Type*} (s : Multiset α) : (2 • s).card = 2 * s.card := by
  rw [two_smul ℕ s, Multiset.card_add]
  omega

/-- Counting indices with values below `q` equals the cardinality of the eigenvalue-style
multiset filtered below `q`. -/
lemma card_filter_eigenvalues_eq_card {α : Type*} [Fintype α] (f : α → ℝ) (q : ℝ) :
    (Finset.univ.filter fun i => f i < q).card
      = (Multiset.filter (fun r : ℝ => r < q) (Finset.univ.val.map f)).card := by
  rw [← Finset.card_val, Finset.filter_val, Multiset.filter_map, Multiset.card_map]
  simp only [Function.comp_apply]

/-- If one indexed multiset doubles another, its count below any threshold is twice the
corresponding count. -/
lemma card_filter_two_mul {ι κ : Type*} [Fintype ι] [Fintype κ] {μ : ι → ℝ} {lam : κ → ℝ}
    (hm : (Finset.univ.val.map μ) = 2 • (Finset.univ.val.map lam)) (q : ℝ) :
    (Finset.univ.filter fun i => μ i < q).card
      = 2 * (Finset.univ.filter fun i => lam i < q).card := by
  rw [card_filter_eigenvalues_eq_card μ q, hm, multiset_filter_two_smul, multiset_card_two_smul,
    ← card_filter_eigenvalues_eq_card lam q]

/-- A valid point for the real block representation has negative count twice the number of
complex eigenvalues below its threshold. -/
theorem point_count_eq_cplx {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ} (h : IsHermRat X Y)
    {p : Point (n + n)} (hp : PointValid (blockRealFin X Y) p) :
    negCountOf p.d
      = 2 * (Finset.univ.filter fun i => (cplx_isHermitian h).eigenvalues i < (p.q : ℝ)).card := by
  have hfin : (realify (blockRealFin X Y)).IsHermitian := realify_isHermitian (blockRealFin_symm h)
  have hsum : ((blockReal X Y).map (algebraMap ℚ ℝ)).IsHermitian :=
    realify_isHermitian' (blockReal_isSymm h)
  have hchar : (realify (blockRealFin X Y)).charpoly
      = ((blockReal X Y).map (algebraMap ℚ ℝ)).charpoly := by
    have h1 : realify (blockRealFin X Y)
        = Matrix.reindex finSumFinEquiv finSumFinEquiv ((blockReal X Y).map (algebraMap ℚ ℝ)) := by
      rw [blockRealFin]
      exact realify_reindex finSumFinEquiv (blockReal X Y)
    rw [h1, Matrix.charpoly_reindex]
  have hm : (Finset.univ.val.map hfin.eigenvalues)
      = 2 • (Finset.univ.val.map (cplx_isHermitian h).eigenvalues) := by
    rw [eigenvalues_eq_of_charpoly hfin hsum hchar, eigenvalues_block_eq_two_mul h]
  have hpc := point_count_eq (blockRealFin_symm h) hp
  rw [← hpc]
  exact card_filter_two_mul hm (p.q : ℝ)

/-- Counting indices satisfying a predicate on their values equals filtering the multiset of
values and taking its cardinality. -/
lemma card_filter_map_eq_card {α : Type*} [Fintype α] (f : α → ℝ) (P : ℝ → Prop)
    [DecidablePred P] :
    (Finset.univ.filter fun i => P (f i)).card
      = (Multiset.filter P (Finset.univ.val.map f)).card := by
  rw [← Finset.card_val, Finset.filter_val, Multiset.filter_map, Multiset.card_map]
  simp only [Function.comp_apply]

/-- If one indexed multiset doubles another, filtering by any decidable predicate doubles the
corresponding count. -/
lemma card_filter_two_mul_of {ι κ : Type*} [Fintype ι] [Fintype κ] {μ : ι → ℝ} {lam : κ → ℝ}
    (P : ℝ → Prop) [DecidablePred P]
    (hm : (Finset.univ.val.map μ) = 2 • (Finset.univ.val.map lam)) :
    (Finset.univ.filter fun i => P (μ i)).card
      = 2 * (Finset.univ.filter fun i => P (lam i)).card := by
  rw [card_filter_map_eq_card μ P, hm, multiset_filter_two_smul, multiset_card_two_smul,
    ← card_filter_map_eq_card lam P]

/-- The finite-index real block matrix has the complex Hermitian eigenvalue multiset with every
multiplicity doubled. -/
theorem eigenvalues_fin_eq_two_mul {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ} (h : IsHermRat X Y) :
    (Finset.univ.val.map (realify_isHermitian (blockRealFin_symm h)).eigenvalues)
      = 2 • (Finset.univ.val.map (cplx_isHermitian h).eigenvalues) := by
  have hfin : (realify (blockRealFin X Y)).IsHermitian := realify_isHermitian (blockRealFin_symm h)
  have hsum : ((blockReal X Y).map (algebraMap ℚ ℝ)).IsHermitian :=
    realify_isHermitian' (blockReal_isSymm h)
  have hchar : (realify (blockRealFin X Y)).charpoly
      = ((blockReal X Y).map (algebraMap ℚ ℝ)).charpoly := by
    have h1 : realify (blockRealFin X Y)
        = Matrix.reindex finSumFinEquiv finSumFinEquiv ((blockReal X Y).map (algebraMap ℚ ℝ)) := by
      rw [blockRealFin]
      exact realify_reindex finSumFinEquiv (blockReal X Y)
    rw [h1, Matrix.charpoly_reindex]
  rw [eigenvalues_eq_of_charpoly hfin hsum hchar, eigenvalues_block_eq_two_mul h]

/-- The spectral certificate constructed for the real block representation of rational complex
Hermitian data. -/
def certifiedPointsC {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) : List (Point (n + n)) :=
  certifiedPoints (blockRealFin X Y) (blockRealFin_symm h) m

/-- The certificate for rational complex Hermitian data passes the real block matrix checker. -/
theorem certifiedPointsC_check {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (h : IsHermRat X Y)
    (m : ℕ) : checkPoints (blockRealFin X Y) (certifiedPointsC X Y h m) = true :=
  certifiedPoints_check _ _ _

/-- The certificate for rational complex Hermitian data is valid for the real block matrix. -/
theorem certifiedPointsC_valid {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (h : IsHermRat X Y)
    (m : ℕ) : Valid (blockRealFin X Y) (certifiedPointsC X Y h m) :=
  certifiedPoints_valid _ _ _

/-- The complex-data certificate has one more point than the number of intervals in its real
block spectral grid. -/
theorem certifiedPointsC_length {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (h : IsHermRat X Y)
    (m : ℕ) : (certifiedPointsC X Y h m).length = gridSteps (blockRealFin X Y) m + 1 :=
  certifiedPoints_length _ _ _

/-- For consecutive complex-data certificate points, the negative-count difference is twice the
complex eigenvalue count in the half-open interval. -/
theorem certifiedPointsC_counts {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ} (h : IsHermRat X Y)
    (m : ℕ) :
    ∀ p q, (p, q) ∈ (certifiedPointsC X Y h m).zip ((certifiedPointsC X Y h m).drop 1) →
      2 * (Finset.univ.filter fun i => (p.q : ℝ) ≤ (cplx_isHermitian h).eigenvalues i ∧
        (cplx_isHermitian h).eigenvalues i < (q.q : ℝ)).card = countBetween p q := by
  intro p q hpq
  have hsound :=
      (certificate_sound (blockRealFin_symm h) (certifiedPointsC_valid X Y h m)).1 p q hpq
  have hm := eigenvalues_fin_eq_two_mul h
  have hle : (p.q : ℝ) ≤ (q.q : ℝ) := by
    have hgrid := (certifiedPointsC_valid X Y h m).2.2.1
    have := pairwise_of_mem_zip_drop hgrid hpq
    exact_mod_cast le_of_lt this
  have hsplit := card_filter_two_mul_of
    (fun r : ℝ => (p.q : ℝ) ≤ r ∧ r < (q.q : ℝ)) hm
  rw [hsound] at hsplit
  exact hsplit.symm

/-- The first and last complex-data certificate thresholds enclose every complex eigenvalue in a
half-open range. -/
theorem certifiedPointsC_covers {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ} (h : IsHermRat X Y)
    (m : ℕ) :
    ∀ a, (certifiedPointsC X Y h m).head? = some a →
      ∀ b, (certifiedPointsC X Y h m).getLast? = some b → ∀ i,
        (a.q : ℝ) ≤ (cplx_isHermitian h).eigenvalues i ∧
          (cplx_isHermitian h).eigenvalues i < (b.q : ℝ) := by
  intro a ha b hb i
  have hcovers :=
      (certificate_sound (blockRealFin_symm h) (certifiedPointsC_valid X Y h m)).2 a ha b hb
  have hm := eigenvalues_fin_eq_two_mul h
  have hmem : (cplx_isHermitian h).eigenvalues i
      ∈ (Finset.univ.val.map (realify_isHermitian (blockRealFin_symm h)).eigenvalues) := by
    rw [hm, two_smul ℕ (Finset.univ.val.map (cplx_isHermitian h).eigenvalues),
      Multiset.mem_add]
    exact Or.inl (Multiset.mem_map_of_mem _ (Finset.mem_univ i))
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hmem
  rw [← hj]
  exact hcovers j

/-- Every valid point for the real block matrix has negative count twice the complex eigenvalue
count below its threshold. -/
theorem certifiedPointsC_counts_even {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ}
    (h : IsHermRat X Y) {p : Point (n + n)} (hp : PointValid (blockRealFin X Y) p) :
    negCountOf p.d
      = 2 * (Finset.univ.filter fun i => (cplx_isHermitian h).eigenvalues i < (p.q : ℝ)).card :=
  point_count_eq_cplx h hp

/-- Every complex eigenvalue lies in a half-open interval of the real block spectral grid. -/
theorem certifiedPointsC_interval {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) (i : Fin n) :
    ∃ j < gridSteps (blockRealFin X Y) m,
      ((-spectrumBound (blockRealFin X Y) + (j : ℚ) * gridMesh m : ℚ) : ℝ) ≤
          (cplx_isHermitian h).eigenvalues i ∧
        (cplx_isHermitian h).eigenvalues i <
          ((-spectrumBound (blockRealFin X Y) + ((j : ℚ) + 1) * gridMesh m : ℚ) : ℝ) := by
  have hm := eigenvalues_fin_eq_two_mul h
  have hmem : (cplx_isHermitian h).eigenvalues i
      ∈ (Finset.univ.val.map (realify_isHermitian (blockRealFin_symm h)).eigenvalues) := by
    rw [hm, two_smul ℕ (Finset.univ.val.map (cplx_isHermitian h).eigenvalues),
      Multiset.mem_add]
    exact Or.inl (Multiset.mem_map_of_mem _ (Finset.mem_univ i))
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hmem
  obtain ⟨k, hk, hkl, hkr⟩ :=
    certifiedPoints_interval (blockRealFin X Y) (blockRealFin_symm h) m j
  exact ⟨k, hk, by rw [← hj]; exact hkl, by rw [← hj]; exact hkr⟩

/-- The gap intervals extracted from the complex-data certificate contain no complex eigenvalues
in their half-open ranges. -/
theorem certifiedPointsC_gaps {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ} (h : IsHermRat X Y)
    (m : ℕ) :
    ∀ I ∈ gapsOf (certifiedPointsC X Y h m),
      ¬ ∃ i, (I.lo : ℝ) ≤ (cplx_isHermitian h).eigenvalues i ∧
        (cplx_isHermitian h).eigenvalues i < (I.hi : ℝ) := by
  intro I hI
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hI
  obtain ⟨hpz, hzero⟩ := List.mem_filter.mp hp
  have hcount := certifiedPointsC_counts h m p.1 p.2 hpz
  rw [of_decide_eq_true hzero] at hcount
  have hzeroC : (Finset.univ.filter fun i =>
      (p.1.q : ℝ) ≤ (cplx_isHermitian h).eigenvalues i ∧
        (cplx_isHermitian h).eigenvalues i < (p.2.q : ℝ)).card = 0 := by
    have := hcount
    omega
  rintro ⟨i, hi⟩
  have hmem : i ∈ Finset.univ.filter (fun i =>
      (p.1.q : ℝ) ≤ (cplx_isHermitian h).eigenvalues i ∧
        (cplx_isHermitian h).eigenvalues i < (p.2.q : ℝ)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  rw [Finset.card_eq_zero.mp hzeroC] at hmem
  simp at hmem

/-- The complex-data certificate satisfies the stated step count, operation bound, and witness
height bound in dimension `n + n`. -/
theorem certifiedPointsC_cost {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (h : IsHermRat X Y)
    (m : ℕ) :
    totalSteps (blockRealFin X Y) (blockRealFin_symm h) (gridOf (blockRealFin X Y) m)
        = (gridSteps (blockRealFin X Y) m + 1) * (n + n)
    ∧ totalOps (blockRealFin X Y) (blockRealFin_symm h) (gridOf (blockRealFin X Y) m)
        ≤ (gridSteps (blockRealFin X Y) m + 1) * opsBound (n + n)
    ∧ ∀ q ∈ gridOf (blockRealFin X Y) m,
        WitnessBitLe (certificateBits (blockRealFin X Y) m)
          (diagAux (n + n) (shift (blockRealFin X Y) q) (shift_symm (blockRealFin_symm h) q)) :=
  frontier1_cost (blockRealFin X Y) (blockRealFin_symm h) m

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- The determinant operation count `n.factorial * (n + 1)` used by the certificate checker. -/
def detOps (n : ℕ) : ℕ := n.factorial * (n + 1)

/-- The square-matrix multiplication operation count `n ^ 3 + n ^ 2 * (n - 1)` used by the
checker. -/
def mulOps (n : ℕ) : ℕ := n ^ 3 + n ^ 2 * (n - 1)

/-- The operation count `n ^ 2` assigned to forming a scalar shift. -/
def shiftOps (n : ℕ) : ℕ := n ^ 2

/-- The full point-checking operation count, comprising one determinant, two matrix products,
and one scalar shift. -/
def checkPointOps (n : ℕ) : ℕ := detOps n + (2 * mulOps n + shiftOps n)

/-- Checks a certificate point while returning its assigned operation count, stopping after the
determinant test when it fails. -/
def checkPointCost {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (p : Point n) : Bool × ℕ :=
  match p.M.det != 0 with
  | false => (false, detOps n)
  | true =>
    (decide (p.Mᵀ * diagonal p.d * p.M = shift A p.q),
      detOps n + (2 * mulOps n + shiftOps n))

/-- The Boolean component of `checkPointCost` agrees with `checkPoint`. -/
theorem checkPointCost_fst {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (p : Point n) :
    (checkPointCost A p).1 = checkPoint A p := by
  unfold checkPointCost checkPoint
  cases h : p.M.det != 0 <;> simp

/-- The operation count returned by `checkPointCost` is at most `checkPointOps n`. -/
theorem checkPointCost_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (p : Point n) :
    (checkPointCost A p).2 ≤ checkPointOps n := by
  unfold checkPointCost checkPointOps
  split <;> omega

/-- A point accepted by `checkPoint` incurs the full assigned operation count `checkPointOps n`. -/
theorem checkPointCost_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (p : Point n)
    (h : checkPoint A p = true) : (checkPointCost A p).2 = checkPointOps n := by
  cases hc : p.M.det != 0 with
  | false =>
    have h' : checkPoint A p = false := by simp [checkPoint, hc]
    rw [h'] at h
    exact absurd h (by simp)
  | true => simp [checkPointCost, hc, checkPointOps]

/-- Checks a list from left to right, stopping at the first false result and summing the costs
of the checked elements. -/
def allCost {α : Type*} (f : α → Bool × ℕ) : List α → Bool × ℕ
  | [] => (true, 0)
  | a :: as =>
    match (f a).1 with
    | true => ((allCost f as).1, (f a).2 + (allCost f as).2)
    | false => (false, (f a).2)

/-- The Boolean component of `allCost` is the conjunction of the Boolean results on the list. -/
theorem allCost_fst {α : Type*} (f : α → Bool × ℕ) (as : List α) :
    (allCost f as).1 = as.all (fun a => (f a).1) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [allCost, List.all_cons]
    cases h : (f a).1 <;> simp [ih]

/-- If each list element has cost at most `c`, then the accumulated cost is at most the list
length times `c`. -/
theorem allCost_snd_le {α : Type*} (f : α → Bool × ℕ) (as : List α) {c : ℕ}
    (hf : ∀ a ∈ as, (f a).2 ≤ c) : (allCost f as).2 ≤ as.length * c := by
  induction as with
  | nil => simp [allCost]
  | cons a as ih =>
    have ha : (f a).2 ≤ c := hf a (by simp)
    have ih' := ih (fun b hb => hf b (by simp [hb]))
    rw [allCost]
    cases h : (f a).1 with
    | false =>
      simp only [List.length_cons]
      calc (f a).2 ≤ c := ha
        _ ≤ (as.length + 1) * c := by
            have h1 : 1 ≤ as.length + 1 := Nat.succ_le_succ (Nat.zero_le _)
            simpa using! Nat.mul_le_mul_right c h1
    | true =>
      simp only [List.length_cons]
      calc (f a).2 + (allCost f as).2 ≤ c + as.length * c := Nat.add_le_add ha ih'
        _ = (as.length + 1) * c := by ring

/-- If every successful element check costs `c`, then a successful list check has total cost
equal to the list length times `c`. -/
theorem allCost_snd_eq {α : Type*} (f : α → Bool × ℕ) (as : List α) {c : ℕ}
    (hf : ∀ a ∈ as, (f a).1 = true → (f a).2 = c) :
    (allCost f as).1 = true → (allCost f as).2 = as.length * c := by
  induction as with
  | nil => intro _; simp [allCost]
  | cons a as ih =>
    intro h
    have ha : (f a).1 = true := by
      by_contra hc
      cases h' : (f a).1 with
      | false => simp [allCost, h'] at h
      | true => exact hc h'
    have hc : (f a).2 = c := hf a (by simp) ha
    have htail : (allCost f as).1 = true := by
      rw [allCost] at h
      simpa [ha] using! h
    have ih' := ih (fun b hb => hf b (by simp [hb])) htail
    rw [allCost, ha, hc, ih', List.length_cons]
    ring

/-- Checks a certificate list and returns the accumulated point-checking cost together with the
Boolean certificate result. -/
def checkPointsCost {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (pts : List (Point n)) :
    Bool × ℕ :=
  let r := allCost (checkPointCost A) pts
  ((!pts.isEmpty) && decide (pts.Pairwise fun p q : Point n => p.q < q.q) && r.1 &&
    (pts.head?.map (fun p => negCountOf p.d == 0)).getD false &&
    (pts.getLast?.map (fun p => negCountOf p.d == n)).getD false, r.2)

/-- The Boolean component of `checkPointsCost` agrees with `checkPoints`. -/
theorem checkPointsCost_fst {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (pts : List (Point n)) :
    (checkPointsCost A pts).1 = checkPoints A pts := by
  have hall : (allCost (checkPointCost A) pts).1 = pts.all (checkPoint A) := by
    rw [allCost_fst]
    congr 1
    funext p
    exact checkPointCost_fst A p
  simp only [checkPointsCost, checkPoints, hall]

/-- The point-checking cost returned for a certificate list is at most its length times
`checkPointOps n`. -/
theorem checkPointsCost_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (pts : List (Point n)) :
    (checkPointsCost A pts).2 ≤ pts.length * checkPointOps n := by
  have h := allCost_snd_le (checkPointCost A) pts (fun p _ => checkPointCost_le A p)
  simpa [checkPointsCost] using! h

/-- An accepted certificate list has point-checking cost equal to its length times
`checkPointOps n`. -/
theorem checkPointsCost_eq_of_check {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (pts : List (Point n)) (h : checkPoints A pts = true) :
    (checkPointsCost A pts).2 = pts.length * checkPointOps n := by
  have hall : pts.all (checkPoint A) = true := by
    cases h' : pts.all (checkPoint A) with
    | false => simp [checkPoints, h'] at h
    | true => rfl
  have hfst : (allCost (checkPointCost A) pts).1 = true := by
    rw [allCost_fst]
    calc pts.all (fun p => (checkPointCost A p).1) = pts.all (checkPoint A) := by
          congr 1
          funext p
          exact checkPointCost_fst A p
      _ = true := hall
  have h := allCost_snd_eq (checkPointCost A) pts (c := checkPointOps n)
    (fun p _ hp => checkPointCost_eq A p (by rwa [checkPointCost_fst A p] at hp)) hfst
  simpa [checkPointsCost] using! h

/-- Checking the constructed real spectral certificate has assigned cost `(gridSteps A m + 1) *
checkPointOps n`. -/
theorem certifiedPoints_checker_ops {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsSymmRat A) (m : ℕ) :
    (checkPointsCost A (certifiedPoints A hA m)).2
      = (gridSteps A m + 1) * checkPointOps n := by
  rw [checkPointsCost_eq_of_check A _ (certifiedPoints_check A hA m),
    certifiedPoints_length A hA m]

/-- The constructed real spectral certificate satisfies the stated generation step count,
operation bound, witness height bound, and exact point-checking cost. -/
theorem frontier1_resources {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (m : ℕ) :
    totalSteps A hA (gridOf A m) = (gridSteps A m + 1) * n ∧
      totalOps A hA (gridOf A m) ≤ (gridSteps A m + 1) * opsBound n ∧
      (∀ q ∈ gridOf A m,
        WitnessBitLe (certificateBits A m) (diagAux n (shift A q) (shift_symm hA q))) ∧
      (checkPointsCost A (certifiedPoints A hA m)).2
        = (gridSteps A m + 1) * checkPointOps n :=
  ⟨certifiedPoints_totalSteps A hA m, certifiedPoints_ops A hA m,
    fun _ hq => certifiedPoints_bits A hA m hq, certifiedPoints_checker_ops A hA m⟩

/-- Checking the complex-data certificate has assigned cost equal to its grid point count times
`checkPointOps (n + n)`. -/
theorem certifiedPointsC_checker_ops {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) :
    (checkPointsCost (blockRealFin X Y) (certifiedPointsC X Y h m)).2
      = (gridSteps (blockRealFin X Y) m + 1) * checkPointOps (n + n) := by
  rw [checkPointsCost_eq_of_check (blockRealFin X Y) _ (certifiedPointsC_check X Y h m),
    certifiedPointsC_length X Y h m]

/-- The constructed complex-data certificate satisfies the stated generation counts, witness
height bound, and exact point-checking cost for its real block matrix. -/
theorem certifiedPointsC_resources {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) :
    totalSteps (blockRealFin X Y) (blockRealFin_symm h) (gridOf (blockRealFin X Y) m)
        = (gridSteps (blockRealFin X Y) m + 1) * (n + n)
    ∧ totalOps (blockRealFin X Y) (blockRealFin_symm h) (gridOf (blockRealFin X Y) m)
        ≤ (gridSteps (blockRealFin X Y) m + 1) * opsBound (n + n)
    ∧ (∀ q ∈ gridOf (blockRealFin X Y) m,
        WitnessBitLe (certificateBits (blockRealFin X Y) m)
          (diagAux (n + n) (shift (blockRealFin X Y) q) (shift_symm (blockRealFin_symm h) q)))
    ∧ (checkPointsCost (blockRealFin X Y) (certifiedPointsC X Y h m)).2
        = (gridSteps (blockRealFin X Y) m + 1) * checkPointOps (n + n) :=
  ⟨(certifiedPointsC_cost X Y h m).1, (certifiedPointsC_cost X Y h m).2.1,
    (certifiedPointsC_cost X Y h m).2.2, certifiedPointsC_checker_ops X Y h m⟩

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- The sum of the absolute values of entries of a rational matrix on an arbitrary finite index
type. -/
def absSumAny {ι : Type*} [Fintype ι] (A : Matrix ι ι ℚ) : ℚ := ∑ i, ∑ j, |A i j|

/-- Reindexing a rational matrix along an equivalence preserves the sum of absolute entry
values. -/
theorem absSumAny_reindex {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (A : Matrix α α ℚ) : absSumAny (Matrix.reindex e e A) = absSumAny A := by
  unfold absSumAny
  have hinner : ∀ i : β, (∑ j : β, |Matrix.reindex e e A i j|)
      = ∑ j : α, |A (e.symm i) j| := by
    intro i
    rw [show (∑ j : β, |Matrix.reindex e e A i j|)
        = ∑ j : β, |A (e.symm i) (e.symm j)| by
      exact Finset.sum_congr rfl fun j _ => by rfl]
    exact Equiv.sum_comp e.symm (fun j : α => |A (e.symm i) j|)
  rw [Finset.sum_congr rfl fun i _ => hinner i]
  exact Equiv.sum_comp e.symm (fun i : α => ∑ j : α, |A i j|)

/-- The absolute-entry sum of the real block representation is twice `absSum X + absSum Y`. -/
theorem absSumAny_blockReal {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    absSumAny (blockReal X Y) = 2 * (absSum X + absSum Y) := by
  unfold absSumAny absSum blockReal
  simp only [Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.neg_apply, abs_neg,
    Finset.sum_add_distrib]
  ring

/-- The absolute-entry sum of the finite-index real block representation is twice `absSum X +
absSum Y`. -/
theorem absSum_blockRealFin {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    absSum (blockRealFin X Y) = 2 * (absSum X + absSum Y) := by
  have h : absSumAny (blockRealFin X Y) = 2 * (absSum X + absSum Y) := by
    rw [show blockRealFin X Y
        = Matrix.reindex finSumFinEquiv finSumFinEquiv (blockReal X Y) from rfl,
      absSumAny_reindex, absSumAny_blockReal]
  exact h

/-- The sum `absSum X + absSum Y` of absolute-entry sums of the rational real and imaginary
parts. -/
def absSumC {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) : ℚ := absSum X + absSum Y

/-- The combined absolute-entry sum `absSumC X Y` is nonnegative. -/
lemma absSumC_nonneg {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) : 0 ≤ absSumC X Y :=
  add_nonneg (absSum_nonneg X) (absSum_nonneg Y)

/-- The rational radius `2 * absSumC X Y + 1` inherited from the real block matrix enclosure. -/
def spectrumBoundC {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) : ℚ :=
  2 * absSumC X Y + 1

/-- The spectral enclosure radius of the real block matrix equals `spectrumBoundC X Y`. -/
theorem spectrumBound_blockRealFin {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    spectrumBound (blockRealFin X Y) = spectrumBoundC X Y := by
  unfold spectrumBound spectrumBoundC absSumC
  rw [absSum_blockRealFin]

/-- The natural ceiling of `2 * spectrumBoundC X Y * (m + 1)`, giving the complex-data grid
interval count. -/
def gridStepsC {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) : ℕ :=
  Nat.ceil (2 * spectrumBoundC X Y * ((m : ℚ) + 1))

/-- The spectral grid interval count of the real block matrix equals `gridStepsC X Y m`. -/
theorem gridSteps_blockRealFin {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) :
    gridSteps (blockRealFin X Y) m = gridStepsC X Y m := by
  unfold gridSteps gridStepsC
  rw [spectrumBound_blockRealFin]

/-- The sum of the rational entry heights of a matrix on an arbitrary finite index type. -/
def matBitsAny {ι : Type*} [Fintype ι] (A : Matrix ι ι ℚ) : ℕ :=
  Finset.univ.sum (fun i => Finset.univ.sum (fun j => Height (A i j)))

/-- Reindexing a rational matrix along an equivalence preserves the sum of its entry heights. -/
theorem matBitsAny_reindex {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (A : Matrix α α ℚ) : matBitsAny (Matrix.reindex e e A) = matBitsAny A := by
  unfold matBitsAny
  have hinner : ∀ i : β,
      (Finset.univ.sum (fun j : β => Height (Matrix.reindex e e A i j)))
        = Finset.univ.sum (fun j : α => Height (A (e.symm i) j)) := by
    intro i
    rw [show (Finset.univ.sum (fun j : β => Height (Matrix.reindex e e A i j)))
        = Finset.univ.sum (fun j : β => Height (A (e.symm i) (e.symm j))) by
      exact Finset.sum_congr rfl fun j _ => by rfl]
    exact Equiv.sum_comp e.symm (fun j : α => Height (A (e.symm i) j))
  rw [Finset.sum_congr rfl fun i _ => hinner i]
  exact Equiv.sum_comp e.symm (fun i : α => Finset.univ.sum fun j : α => Height (A i j))

/-- The sum of entry heights of the real block representation is twice the sum of the
entry-height sums of `X` and `Y`. -/
theorem matBitsAny_blockReal {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    matBitsAny (blockReal X Y) = 2 * (matBits X + matBits Y) := by
  unfold matBitsAny matBits blockReal
  simp only [Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.neg_apply, Height_neg,
    Finset.sum_add_distrib]
  ring

/-- The sum of entry heights of the finite-index real block representation is twice `matBits X +
matBits Y`. -/
theorem matBits_blockRealFin {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    matBits (blockRealFin X Y) = 2 * (matBits X + matBits Y) := by
  have h : matBitsAny (blockRealFin X Y) = 2 * (matBits X + matBits Y) := by
    rw [show blockRealFin X Y
        = Matrix.reindex finSumFinEquiv finSumFinEquiv (blockReal X Y) from rfl,
      matBitsAny_reindex, matBitsAny_blockReal]
  exact h

/-- The uniform witness exponent for the real block certificate has the displayed expression in
terms of the rational real and imaginary data. -/
theorem certificateBits_blockRealFin {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) :
    certificateBits (blockRealFin X Y) m
      = costExp (n + n) (2 * (matBits X + matBits Y) + 2 * (Height (spectrumBoundC X Y) *
          ((gridStepsC X Y m + 1) * Height (gridMesh m))) + 1) := by
  unfold certificateBits
  rw [matBits_blockRealFin, spectrumBound_blockRealFin, gridSteps_blockRealFin]

/-- The full shear operation count simplifies to `6 * n ^ 2 + 8 * n + 8`. -/
theorem shearOps_eq (n : ℕ) : shearOps n = 6 * n ^ 2 + 8 * n + 8 := by
  unfold shearOps elimOps shearPrepOps shearAssemblyOps
  ring

/-- The cumulative diagonalization operation bound is at most `6 * n ^ 3 + 4 * n ^ 2 + 8 * n`. -/
theorem opsBound_le_cubic (n : ℕ) : opsBound n ≤ 6 * n ^ 3 + 4 * n ^ 2 + 8 * n := by
  induction n with
  | zero => simp [opsBound]
  | succ k ih =>
    have hstep : opsBound (k + 1) = opsBound k + shearOps k := rfl
    rw [hstep, shearOps_eq]
    nlinarith [ih]

/-- The cubic bound `48 * n ^ 3 + 16 * n ^ 2 + 16 * n` for diagonalization operations in the
doubled real dimension. -/
def opsBoundC (n : ℕ) : ℕ := 48 * n ^ 3 + 16 * n ^ 2 + 16 * n

/-- The operation bound in dimension `n + n` is at most `opsBoundC n`. -/
theorem opsBound_two_mul_le (n : ℕ) : opsBound (n + n) ≤ opsBoundC n := by
  calc opsBound (n + n) ≤ 6 * (n + n) ^ 3 + 4 * (n + n) ^ 2 + 8 * (n + n) :=
        opsBound_le_cubic _
    _ = opsBoundC n := by unfold opsBoundC; ring

/-- The assigned matrix multiplication count in dimension `m` is at most `2 * m ^ 3`. -/
theorem mulOps_le_two_mul_cube (m : ℕ) : mulOps m ≤ 2 * m ^ 3 := by
  unfold mulOps
  have h : m ^ 2 * (m - 1) ≤ m ^ 2 * m := Nat.mul_le_mul_left _ (Nat.sub_le m 1)
  nlinarith [h]

/-- The assigned scalar-shift operation count in dimension `n + n` is `4 * n ^ 2`. -/
theorem shiftOps_two_mul (n : ℕ) : shiftOps (n + n) = 4 * n ^ 2 := by
  unfold shiftOps
  ring

/-- The explicit point-checking operation bound in doubled dimension, expressed in the complex
dimension `n`. -/
def checkPointOpsC (n : ℕ) : ℕ := (n + n).factorial * (n + n + 1) + 32 * n ^ 3 + 4 * n ^ 2

/-- The full point-checking operation count in dimension `n + n` is at most `checkPointOpsC n`. -/
theorem checkPointOps_two_mul_le (n : ℕ) : checkPointOps (n + n) ≤ checkPointOpsC n := by
  unfold checkPointOps checkPointOpsC detOps
  have hm : mulOps (n + n) ≤ 2 * (n + n) ^ 3 := mulOps_le_two_mul_cube _
  have hs : shiftOps (n + n) = 4 * n ^ 2 := shiftOps_two_mul n
  nlinarith [hm, hs]

/-- Generating the complex-data grid certificate has total stored step count `(gridStepsC X Y m
+ 1) * (n + n)`. -/
theorem certifiedPointsC_totalStepsC {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) :
    totalSteps (blockRealFin X Y) (blockRealFin_symm h) (gridOf (blockRealFin X Y) m)
      = (gridStepsC X Y m + 1) * (n + n) := by
  rw [certifiedPoints_totalSteps, gridSteps_blockRealFin]

/-- The complex-data certificate generation operation count is at most its grid point count
times `opsBoundC n`. -/
theorem certifiedPointsC_opsC {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) :
    totalOps (blockRealFin X Y) (blockRealFin_symm h) (gridOf (blockRealFin X Y) m)
      ≤ (gridStepsC X Y m + 1) * opsBoundC n := by
  refine (certifiedPoints_ops (blockRealFin X Y) (blockRealFin_symm h) m).trans ?_
  rw [gridSteps_blockRealFin]
  exact Nat.mul_le_mul_left _ (opsBound_two_mul_le n)

/-- The complex-data certificate has exact point-checking cost given by its grid point count
times `checkPointOps (n + n)`, and the corresponding bound using `checkPointOpsC n`. -/
theorem certifiedPointsC_checker_opsC {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) :
    (checkPointsCost (blockRealFin X Y) (certifiedPointsC X Y h m)).2
        = (gridStepsC X Y m + 1) * checkPointOps (n + n)
      ∧ (checkPointsCost (blockRealFin X Y) (certifiedPointsC X Y h m)).2
        ≤ (gridStepsC X Y m + 1) * checkPointOpsC n := by
  have hexact := certifiedPointsC_checker_ops X Y h m
  rw [gridSteps_blockRealFin] at hexact
  refine ⟨hexact, ?_⟩
  rw [hexact]
  exact Nat.mul_le_mul_left _ (checkPointOps_two_mul_le n)

/-- The complex-data certificate satisfies generation step, generation operation, witness
height, and point-checking bounds expressed using `gridStepsC`, `opsBoundC`, and
`checkPointOpsC`. -/
theorem certifiedPointsC_resourcesComplex {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) :
    totalSteps (blockRealFin X Y) (blockRealFin_symm h) (gridOf (blockRealFin X Y) m)
        = (gridStepsC X Y m + 1) * (n + n)
      ∧ totalOps (blockRealFin X Y) (blockRealFin_symm h) (gridOf (blockRealFin X Y) m)
        ≤ (gridStepsC X Y m + 1) * opsBoundC n
      ∧ (∀ q ∈ gridOf (blockRealFin X Y) m,
          WitnessBitLe (certificateBits (blockRealFin X Y) m)
            (diagAux (n + n) (shift (blockRealFin X Y) q) (shift_symm (blockRealFin_symm h) q)))
      ∧ (checkPointsCost (blockRealFin X Y) (certifiedPointsC X Y h m)).2
        ≤ (gridStepsC X Y m + 1) * checkPointOpsC n :=
  ⟨certifiedPointsC_totalStepsC X Y h m, certifiedPointsC_opsC X Y h m,
    (certifiedPointsC_resources X Y h m).2.2.1,
    (certifiedPointsC_checker_opsC X Y h m).2⟩

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- A uniform bound on sums of entry norms in each row of a complex Hermitian matrix bounds the
absolute value of every eigenvalue. -/
theorem abs_eigenvalue_le_of_row_sum_cplx {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) {R : ℝ} (hrow : ∀ i, ∑ k, ‖M i k‖ ≤ R) (j : Fin n) :
    |hM.eigenvalues j| ≤ R := by
  classical
  let v : Fin n → ℂ := ⇑(hM.eigenvectorBasis j)
  have horth : ‖hM.eigenvectorBasis j‖ = 1 := hM.eigenvectorBasis.orthonormal.1 j
  have hv : v ≠ 0 := by
    intro h
    have h0 : hM.eigenvectorBasis j = 0 := by
      ext i
      exact congrFun h i
    rw [h0, norm_zero] at horth
    exact zero_ne_one horth
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i0, hi0⟩ := hex
  obtain ⟨i, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun i => ‖v i‖) ⟨i0, Finset.mem_univ i0⟩
  have hvi : 0 < ‖v i‖ := lt_of_lt_of_le (norm_pos_iff.mpr hi0) (hmax i0 (Finset.mem_univ i0))
  have hcoord : (∑ k, M i k * v k) = (hM.eigenvalues j : ℂ) * v i := by
    have h := congrFun (hM.mulVec_eigenvectorBasis j) i
    simpa [Matrix.mulVec, dotProduct, v, Pi.smul_apply, smul_eq_mul] using! h
  have h2 : ‖∑ k, M i k * v k‖ ≤ ∑ k, ‖M i k‖ * ‖v i‖ := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun k _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hmax k (Finset.mem_univ k)) (norm_nonneg _)
  have hkey : |hM.eigenvalues j| * ‖v i‖ ≤ R * ‖v i‖ := by
    have h1 : |hM.eigenvalues j| * ‖v i‖ = ‖∑ k, M i k * v k‖ := by
      rw [hcoord, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [h1]
    calc ‖∑ k, M i k * v k‖ ≤ ∑ k, ‖M i k‖ * ‖v i‖ := h2
      _ = (∑ k, ‖M i k‖) * ‖v i‖ := (Finset.sum_mul ..).symm
      _ ≤ R * ‖v i‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)
  exact le_of_mul_le_mul_right hkey hvi

/-- The norm of an entry of `cplx X Y` is at most the sum of the absolute values of its rational
real and imaginary parts. -/
lemma norm_cplx_apply_le {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    ‖cplx X Y i j‖ ≤ ((|X i j| + |Y i j| : ℚ) : ℝ) := by
  have hx : cplx X Y i j = ((X i j : ℚ) : ℂ) + Complex.I * ((Y i j : ℚ) : ℂ) := by
    simp [cplx, Matrix.map_apply, Matrix.smul_apply]
  rw [hx]
  refine (norm_add_le _ _).trans ?_
  have hX : ‖((X i j : ℚ) : ℂ)‖ = ((|X i j| : ℚ) : ℝ) := by
    have : ((X i j : ℚ) : ℂ) = (((X i j : ℚ) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, Rat.cast_abs]
  have hY : ‖Complex.I * ((Y i j : ℚ) : ℂ)‖ = ((|Y i j| : ℚ) : ℝ) := by
    rw [norm_mul, Complex.norm_I, one_mul]
    have : ((Y i j : ℚ) : ℂ) = (((Y i j : ℚ) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, Rat.cast_abs]
  rw [hX, hY]
  push_cast
  exact le_refl _

/-- Every row norm sum of `cplx X Y` is at most the real cast of `absSum X + absSum Y`. -/
lemma row_sum_cplx_le {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) :
    ∑ k, ‖cplx X Y i k‖ ≤ ((absSum X + absSum Y : ℚ) : ℝ) := by
  have hterm : ∀ k, ‖cplx X Y i k‖ ≤ ((|X i k| + |Y i k| : ℚ) : ℝ) :=
    fun k => norm_cplx_apply_le X Y i k
  calc ∑ k, ‖cplx X Y i k‖ ≤ ∑ k, ((|X i k| + |Y i k| : ℚ) : ℝ) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = ((∑ k, (|X i k| + |Y i k|) : ℚ) : ℝ) := by push_cast; ring
    _ ≤ ((absSum X + absSum Y : ℚ) : ℝ) := by
        have hX : (∑ k, |X i k|) ≤ absSum X := abs_row_le_absSum X i
        have hY : (∑ k, |Y i k|) ≤ absSum Y := abs_row_le_absSum Y i
        have hsum : (∑ k, (|X i k| + |Y i k|)) ≤ absSum X + absSum Y := by
          rw [Finset.sum_add_distrib]
          exact add_le_add hX hY
        exact_mod_cast hsum

/-- Every eigenvalue of the rational complex Hermitian matrix has absolute value at most the
real cast of `absSumC X Y`. -/
theorem eigenvalue_abs_le_absSumC {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ}
    (h : IsHermRat X Y) (j : Fin n) :
    |(cplx_isHermitian h).eigenvalues j| ≤ ((absSumC X Y : ℚ) : ℝ) := by
  have hb := abs_eigenvalue_le_of_row_sum_cplx (cplx_isHermitian h) (row_sum_cplx_le X Y) j
  unfold absSumC
  exact hb

/-- Every complex eigenvalue has absolute value strictly below the real cast of `absSumC X Y`
plus one. -/
theorem eigenvalue_abs_lt_absSumC_add_one {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ}
    (h : IsHermRat X Y) (j : Fin n) :
    |(cplx_isHermitian h).eigenvalues j| < ((absSumC X Y : ℚ) : ℝ) + 1 := by
  have hb := eigenvalue_abs_le_absSumC h j
  linarith

/-- Every complex eigenvalue lies strictly between minus and plus the real cast of `absSumC X Y`
plus one. -/
theorem eigenvalue_mem_absSumC_interval {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ}
    (h : IsHermRat X Y) (j : Fin n) :
    -(((absSumC X Y : ℚ) : ℝ) + 1) < (cplx_isHermitian h).eigenvalues j ∧
      (cplx_isHermitian h).eigenvalues j < ((absSumC X Y : ℚ) : ℝ) + 1 := by
  have hb := eigenvalue_abs_lt_absSumC_add_one h j
  exact ⟨by linarith [neg_abs_le ((cplx_isHermitian h).eigenvalues j)],
    by linarith [le_abs_self ((cplx_isHermitian h).eigenvalues j)]⟩

/-- The radius `absSumC X Y + 1` is at most the block-derived radius `spectrumBoundC X Y`. -/
theorem absSumC_add_one_le_spectrumBoundC {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    absSumC X Y + 1 ≤ spectrumBoundC X Y := by
  have h := absSumC_nonneg X Y
  unfold spectrumBoundC
  linarith

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- The natural ceiling of `2 * R * (m + 1)`, used as a grid interval count for a chosen
rational radius. -/
def gridStepsR (R : ℚ) (m : ℕ) : ℕ :=
  Nat.ceil (2 * R * ((m : ℚ) + 1))

/-- The rational grid starting at `-R` with spacing `gridMesh m` and interval count `gridStepsR
R m`. -/
def gridOfR (R : ℚ) (m : ℕ) : List ℚ :=
  gridAux (-R) (gridMesh m) (gridStepsR R m)

/-- Choosing `spectrumBound A` as the radius recovers the original spectral grid interval count. -/
lemma gridStepsR_spectrumBound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) :
    gridStepsR (spectrumBound A) m = gridSteps A m := rfl

/-- Choosing `spectrumBound A` as the radius recovers the original spectral grid. -/
lemma gridOfR_spectrumBound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) :
    gridOfR (spectrumBound A) m = gridOf A m := rfl

/-- The grid associated with any rational radius is nonempty. -/
lemma gridOfR_ne_nil (R : ℚ) (m : ℕ) : gridOfR R m ≠ [] :=
  gridAux_ne_nil _ _ _

/-- The first point of `gridOfR R m` is `-R`. -/
lemma gridOfR_head (R : ℚ) (m : ℕ) : (gridOfR R m).head? = some (-R) :=
  gridAux_head _ _ _

/-- The last point of `gridOfR R m` is `-R + gridStepsR R m * gridMesh m`. -/
lemma gridOfR_getLast (R : ℚ) (m : ℕ) :
    (gridOfR R m).getLast? = some (-R + (gridStepsR R m : ℚ) * gridMesh m) :=
  gridAux_getLast _ _ _

/-- The radius-based grid is pairwise strictly increasing. -/
lemma gridOfR_pairwise (R : ℚ) (m : ℕ) : (gridOfR R m).Pairwise (· < ·) :=
  gridAux_pairwise _ _ _ (gridMesh_pos m)

/-- The radius-based grid has `gridStepsR R m + 1` points. -/
lemma gridOfR_length (R : ℚ) (m : ℕ) : (gridOfR R m).length = gridStepsR R m + 1 :=
  gridAux_length _ _ _

/-- The last point of the radius-based grid is at least `R`. -/
theorem gridOfR_last_ge (R : ℚ) (m : ℕ) :
    R ≤ -R + (gridStepsR R m : ℚ) * gridMesh m := by
  by_cases hR : 0 ≤ R
  · have hceil : 2 * R * ((m : ℚ) + 1) ≤ (gridStepsR R m : ℚ) := Nat.le_ceil _
    have hm : (0 : ℚ) < (m : ℚ) + 1 := by positivity
    have hstep : 2 * R ≤ (gridStepsR R m : ℚ) * gridMesh m := by
      have h := mul_le_mul_of_nonneg_right hceil (le_of_lt (inv_pos.mpr hm))
      have hcancel : 2 * R * ((m : ℚ) + 1) * ((m : ℚ) + 1)⁻¹ = 2 * R := by
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hm), mul_one]
      unfold gridMesh
      calc 2 * R = 2 * R * ((m : ℚ) + 1) * ((m : ℚ) + 1)⁻¹ := hcancel.symm
        _ ≤ (gridStepsR R m : ℚ) * ((m : ℚ) + 1)⁻¹ := h
    linarith
  · have hneg : R < 0 := not_le.mp hR
    have hzero : gridStepsR R m = 0 := by
      unfold gridStepsR
      rw [Nat.ceil_eq_zero]
      have hm : (0 : ℚ) < (m : ℚ) + 1 := by positivity
      nlinarith
    rw [hzero]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    linarith

/-- The radius-based grid interval count is monotone in the radius. -/
theorem gridStepsR_mono {R R' : ℚ} (h : R ≤ R') (m : ℕ) :
    gridStepsR R m ≤ gridStepsR R' m := by
  unfold gridStepsR
  refine Nat.ceil_mono ?_
  have hm : (0 : ℚ) ≤ (m : ℚ) + 1 := by positivity
  nlinarith

/-- If all eigenvalue absolute values are strictly below `R`, the constructed point at `-R` has
negative count zero. -/
theorem pointOf_negR_count {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    {R : ℚ} (hR : ∀ i, |(realify_isHermitian hA).eigenvalues i| < (R : ℝ)) :
    negCountOf (pointOf A hA (-R)).d = 0 := by
  rw [← pointOf_count A hA (-R)]
  refine Finset.card_filter_eq_zero_iff.mpr ?_
  intro i _ hi
  have hgt : -((R : ℚ) : ℝ) < (realify_isHermitian hA).eigenvalues i := by
    have h := hR i
    have h1 := neg_abs_le ((realify_isHermitian hA).eigenvalues i)
    linarith
  have hlt : (realify_isHermitian hA).eigenvalues i < -((R : ℚ) : ℝ) := by
    have h := hi
    push_cast at h
    exact h
  linarith

/-- If all eigenvalue absolute values are strictly below `R`, the constructed point at the last
radius-based grid threshold has negative count `n`. -/
theorem pointOf_lastR_count {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    {R : ℚ} (hR : ∀ i, |(realify_isHermitian hA).eigenvalues i| < (R : ℝ))
    (m : ℕ) :
    negCountOf (pointOf A hA (-R + (gridStepsR R m : ℚ) * gridMesh m)).d = n := by
  rw [← pointOf_count A hA (-R + (gridStepsR R m : ℚ) * gridMesh m)]
  rw [Finset.filter_true_of_mem]
  · simp
  · intro i _
    have hq := gridOfR_last_ge R m
    have hqcast : (R : ℝ) ≤
        ((-R + (gridStepsR R m : ℚ) * gridMesh m : ℚ) : ℝ) := by
      exact_mod_cast hq
    have hlam : (realify_isHermitian hA).eigenvalues i < (R : ℝ) := (abs_lt.mp (hR i)).2
    linarith

/-- The certificate points constructed on the grid for a chosen rational radius `R`. -/
def certifiedPointsR {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A) (R : ℚ)
    (m : ℕ) : List (Point n) :=
  ptsOf A hA (gridOfR R m)

/-- The radius-based certificate passes its checker when all eigenvalue absolute values are
strictly below `R`. -/
theorem certifiedPointsR_check {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    {R : ℚ} (hR : ∀ i, |(realify_isHermitian hA).eigenvalues i| < (R : ℝ))
    (m : ℕ) : checkPoints A (certifiedPointsR A hA R m) = true := by
  unfold certifiedPointsR
  refine checkPoints_ptsOf A hA (gridOfR_ne_nil R m) (gridOfR_pairwise R m) ?_ ?_
  · intro q hq
    rw [gridOfR_head] at hq
    cases hq
    exact pointOf_negR_count A hA hR
  · intro q hq
    rw [gridOfR_getLast] at hq
    cases hq
    exact pointOf_lastR_count A hA hR m

/-- The radius-based certificate is valid when all eigenvalue absolute values are strictly below
`R`. -/
theorem certifiedPointsR_valid {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    {R : ℚ} (hR : ∀ i, |(realify_isHermitian hA).eigenvalues i| < (R : ℝ))
    (m : ℕ) : Valid A (certifiedPointsR A hA R m) :=
  (checkPoints_eq_true_iff A _).mp (certifiedPointsR_check A hA hR m)

/-- Under the strict spectral radius bound, consecutive radius-based certificate points give
exact eigenvalue counts on their half-open intervals. -/
theorem certifiedPointsR_counts {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    {R : ℚ} (hR : ∀ i, |(realify_isHermitian hA).eigenvalues i| < (R : ℝ))
    (m : ℕ) :
    ∀ p q, (p, q) ∈ (certifiedPointsR A hA R m).zip ((certifiedPointsR A hA R m).drop 1) →
      (Finset.univ.filter fun i => (p.q : ℝ) ≤ (realify_isHermitian hA).eigenvalues i ∧
        (realify_isHermitian hA).eigenvalues i < (q.q : ℝ)).card = countBetween p q :=
  (certificate_sound hA (certifiedPointsR_valid A hA hR m)).1

/-- Under the strict spectral radius bound, every eigenvalue lies between the first radius-based
grid threshold, included, and the last, excluded. -/
theorem certifiedPointsR_covers {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    {R : ℚ} (hR : ∀ i, |(realify_isHermitian hA).eigenvalues i| < (R : ℝ))
    (m : ℕ) (i : Fin n) :
    ((-R : ℚ) : ℝ) ≤ (realify_isHermitian hA).eigenvalues i ∧
      (realify_isHermitian hA).eigenvalues i <
        ((-R + (gridStepsR R m : ℚ) * gridMesh m : ℚ) : ℝ) := by
  constructor
  · exact pointOf_le_of_count_zero A hA (-R) (pointOf_negR_count A hA hR) i
  · exact pointOf_lt_of_count_card A hA (-R + (gridStepsR R m : ℚ) * gridMesh m)
      (pointOf_lastR_count A hA hR m) i

/-- The radius-based certificate contains `gridStepsR R m + 1` points. -/
theorem certifiedPointsR_length {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (R : ℚ) (m : ℕ) : (certifiedPointsR A hA R m).length = gridStepsR R m + 1 := by
  unfold certifiedPointsR ptsOf
  rw [List.length_map]
  exact gridOfR_length R m

/-- Under the strict spectral radius bound, every eigenvalue belongs to a half-open interval of
the radius-based grid. -/
theorem certifiedPointsR_interval {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    {R : ℚ} (hR : ∀ i, |(realify_isHermitian hA).eigenvalues i| < (R : ℝ))
    (m : ℕ) (i : Fin n) :
    ∃ j < gridStepsR R m,
      ((-R + (j : ℚ) * gridMesh m : ℚ) : ℝ) ≤ (realify_isHermitian hA).eigenvalues i ∧
        (realify_isHermitian hA).eigenvalues i <
          ((-R + ((j : ℚ) + 1) * gridMesh m : ℚ) : ℝ) := by
  obtain ⟨hlow, hhigh⟩ := certifiedPointsR_covers A hA hR m i
  have hh : (0 : ℝ) < ((gridMesh m : ℚ) : ℝ) := by exact_mod_cast gridMesh_pos m
  have hlow' : -((R : ℚ) : ℝ) ≤ (realify_isHermitian hA).eigenvalues i := by
    have h := hlow
    push_cast at h
    exact h
  have hhigh' : (realify_isHermitian hA).eigenvalues i <
      -((R : ℚ) : ℝ) + (gridStepsR R m : ℝ) * ((gridMesh m : ℚ) : ℝ) := by
    have h := hhigh
    push_cast at h
    exact h
  obtain ⟨j, hj, hjl, hjr⟩ :=
    exists_grid_interval (-((R : ℚ) : ℝ)) ((gridMesh m : ℚ) : ℝ)
      ((realify_isHermitian hA).eigenvalues i) (gridStepsR R m) hh hlow' hhigh'
  refine ⟨j, hj, ?_, ?_⟩
  · push_cast
    exact hjl
  · push_cast
    exact hjr

/-- Under the strict spectral radius bound, the radius-based certificate passes its checker,
gives exact interval counts, encloses every eigenvalue, and has the stated length. -/
theorem frontier1R {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    {R : ℚ} (hR : ∀ i, |(realify_isHermitian hA).eigenvalues i| < (R : ℝ))
    (m : ℕ) :
    checkPoints A (certifiedPointsR A hA R m) = true ∧
      (∀ p q, (p, q) ∈ (certifiedPointsR A hA R m).zip ((certifiedPointsR A hA R m).drop 1) →
        (Finset.univ.filter fun i => (p.q : ℝ) ≤ (realify_isHermitian hA).eigenvalues i ∧
          (realify_isHermitian hA).eigenvalues i < (q.q : ℝ)).card = countBetween p q) ∧
      (∀ i, ((-R : ℚ) : ℝ) ≤ (realify_isHermitian hA).eigenvalues i ∧
        (realify_isHermitian hA).eigenvalues i <
          ((-R + (gridStepsR R m : ℚ) * gridMesh m : ℚ) : ℝ)) ∧
      (certifiedPointsR A hA R m).length = gridStepsR R m + 1 :=
  ⟨certifiedPointsR_check A hA hR m, certifiedPointsR_counts A hA hR m,
    certifiedPointsR_covers A hA hR m, certifiedPointsR_length A hA R m⟩

/-- The total stored generation step count on a radius-based grid is its point count times `n`. -/
theorem certifiedPointsR_totalSteps {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (R : ℚ) (m : ℕ) :
    totalSteps A hA (gridOfR R m) = (gridStepsR R m + 1) * n := by
  rw [totalSteps_eq_length, gridOfR_length]

/-- The total stored generation operation count on a radius-based grid is at most its point
count times `opsBound n`. -/
theorem certifiedPointsR_ops {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (R : ℚ) (m : ℕ) :
    totalOps A hA (gridOfR R m) ≤ (gridStepsR R m + 1) * opsBound n := by
  have h := totalOps_le_length A hA (gridOfR R m)
  rwa [gridOfR_length] at h

/-- A uniform witness height-bound exponent for certificate points on a grid with chosen
rational radius. -/
def certificateBitsR {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (R : ℚ) (m : ℕ) : ℕ :=
  costExp n (matBits A + 2 * (Height R * ((gridStepsR R m + 1) * Height (gridMesh m))) + 1)

/-- Every radius-based grid threshold has height bounded by twice the product of the radius
height, grid point count, and mesh height. -/
theorem gridOfR_height {R : ℚ} (m : ℕ) {x : ℚ} (hx : x ∈ gridOfR R m) :
    Height x ≤ 2 * (Height R * ((gridStepsR R m + 1) * Height (gridMesh m))) := by
  obtain ⟨j, hj, rfl⟩ := (gridAux_mem_iff (gridStepsR R m) (-R) (gridMesh m) x).mp hx
  have hadd := Height_add_le (-R) ((j : ℚ) * gridMesh m)
  rw [Height_neg] at hadd
  have hmul := Height_mul_le (j : ℚ) (gridMesh m)
  have hjq : Height (j : ℚ) ≤ j + 1 := Height_natCast_le j
  have hle : Height ((j : ℚ) * gridMesh m) ≤
      (gridStepsR R m + 1) * Height (gridMesh m) :=
    hmul.trans (Nat.mul_le_mul (hjq.trans (Nat.succ_le_succ hj)) le_rfl)
  refine hadd.trans ?_
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hle)

/-- Each diagonalization witness used on the radius-based grid satisfies the uniform bound
`certificateBitsR A R m`. -/
theorem certifiedPointsR_bits {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (R : ℚ) (m : ℕ) {q : ℚ} (hq : q ∈ gridOfR R m) :
    WitnessBitLe (certificateBitsR A R m) (diagAux n (shift A q) (shift_symm hA q)) := by
  have hb : MatBitLe (matBits A + Height q + 1) (shift A q) := shift_bitLe A q
  have hw := diagAux_bitLe n (shift A q) (shift_symm hA q) _ hb
  refine hw.mono ?_
  refine costExp_mono n ?_
  have hgrid := gridOfR_height (R := R) m hq
  omega

/-- Under the strict spectral radius bound, checking the radius-based certificate has assigned
cost equal to its point count times `checkPointOps n`. -/
theorem certifiedPointsR_checker_ops {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsSymmRat A) {R : ℚ}
    (hR : ∀ i, |(realify_isHermitian hA).eigenvalues i| < (R : ℝ)) (m : ℕ) :
    (checkPointsCost A (certifiedPointsR A hA R m)).2 = (gridStepsR R m + 1) * checkPointOps n := by
  rw [checkPointsCost_eq_of_check A _ (certifiedPointsR_check A hA hR m),
    certifiedPointsR_length A hA R m]

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage
namespace CertifiedHermitianSpectrum

open Matrix

/-- The rational enclosure radius `absSumC X Y + 1` for the complex Hermitian spectrum. -/
def sharpBoundC {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) : ℚ := absSumC X Y + 1

/-- The complex spectral enclosure radius `sharpBoundC X Y` is positive. -/
lemma sharpBoundC_pos {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) : 0 < sharpBoundC X Y := by
  have h := absSumC_nonneg X Y
  unfold sharpBoundC
  linarith

/-- The radius `sharpBoundC X Y` is at most the block-derived radius `spectrumBoundC X Y`. -/
theorem sharpBoundC_le_spectrumBoundC {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) :
    sharpBoundC X Y ≤ spectrumBoundC X Y := by
  have h := absSumC_nonneg X Y
  unfold sharpBoundC spectrumBoundC
  linarith

/-- If the combined absolute-entry sum is positive, `sharpBoundC X Y` is strictly smaller than
`spectrumBoundC X Y`. -/
theorem sharpBoundC_lt_spectrumBoundC {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ}
    (h : 0 < absSumC X Y) : sharpBoundC X Y < spectrumBoundC X Y := by
  unfold sharpBoundC spectrumBoundC
  linarith

/-- Every eigenvalue of the real block matrix has absolute value strictly below the real cast of
`sharpBoundC X Y`. -/
theorem blockRealFin_eigenvalue_abs_lt {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ}
    (h : IsHermRat X Y) (j : Fin (n + n)) :
    |(realify_isHermitian (blockRealFin_symm h)).eigenvalues j| < ((sharpBoundC X Y : ℚ) : ℝ) := by
  have hm := eigenvalues_fin_eq_two_mul h
  have hmem0 : (realify_isHermitian (blockRealFin_symm h)).eigenvalues j
      ∈ (Finset.univ.val.map (realify_isHermitian (blockRealFin_symm h)).eigenvalues) :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ j)
  rw [hm, two_smul ℕ (Finset.univ.val.map (cplx_isHermitian h).eigenvalues),
    Multiset.mem_add] at hmem0
  have hmem : (realify_isHermitian (blockRealFin_symm h)).eigenvalues j
      ∈ (Finset.univ.val.map (cplx_isHermitian h).eigenvalues) := by
    rcases hmem0 with h' | h' <;> exact h'
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hmem
  rw [← hi]
  have hb := eigenvalue_abs_le_absSumC h i
  unfold sharpBoundC
  push_cast
  linarith

/-- The real block certificate constructed with the smaller complex spectral radius `sharpBoundC
X Y`. -/
def certifiedPointsCSharp {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (h : IsHermRat X Y)
    (m : ℕ) : List (Point (n + n)) :=
  certifiedPointsR (blockRealFin X Y) (blockRealFin_symm h) (sharpBoundC X Y) m

/-- The complex-data certificate using `sharpBoundC` passes the real block matrix checker. -/
theorem certifiedPointsCSharp_check {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (h : IsHermRat X Y)
    (m : ℕ) : checkPoints (blockRealFin X Y) (certifiedPointsCSharp X Y h m) = true :=
  certifiedPointsR_check (blockRealFin X Y) (blockRealFin_symm h)
    (blockRealFin_eigenvalue_abs_lt h) m

/-- The complex-data certificate using `sharpBoundC` is valid for the real block matrix. -/
theorem certifiedPointsCSharp_valid {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (h : IsHermRat X Y)
    (m : ℕ) : Valid (blockRealFin X Y) (certifiedPointsCSharp X Y h m) :=
  certifiedPointsR_valid (blockRealFin X Y) (blockRealFin_symm h)
    (blockRealFin_eigenvalue_abs_lt h) m

/-- The certificate using `sharpBoundC` has `gridStepsR (sharpBoundC X Y) m + 1` points. -/
theorem certifiedPointsCSharp_length {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (h : IsHermRat X Y)
    (m : ℕ) : (certifiedPointsCSharp X Y h m).length = gridStepsR (sharpBoundC X Y) m + 1 :=
  certifiedPointsR_length (blockRealFin X Y) (blockRealFin_symm h) (sharpBoundC X Y) m

/-- For consecutive certificate points using `sharpBoundC`, the negative-count difference is
twice the complex eigenvalue count in the half-open interval. -/
theorem certifiedPointsCSharp_counts {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ}
    (h : IsHermRat X Y) (m : ℕ) :
    ∀ p q, (p, q) ∈ (certifiedPointsCSharp X Y h m).zip
        ((certifiedPointsCSharp X Y h m).drop 1) →
      2 * (Finset.univ.filter fun i => (p.q : ℝ) ≤ (cplx_isHermitian h).eigenvalues i ∧
        (cplx_isHermitian h).eigenvalues i < (q.q : ℝ)).card = countBetween p q := by
  intro p q hpq
  have hsound :=
    (certificate_sound (blockRealFin_symm h) (certifiedPointsCSharp_valid X Y h m)).1 p q hpq
  have hm := eigenvalues_fin_eq_two_mul h
  have hle : (p.q : ℝ) ≤ (q.q : ℝ) := by
    have hgrid := (certifiedPointsCSharp_valid X Y h m).2.2.1
    have := pairwise_of_mem_zip_drop hgrid hpq
    exact_mod_cast le_of_lt this
  have hsplit := card_filter_two_mul_of
    (fun r : ℝ => (p.q : ℝ) ≤ r ∧ r < (q.q : ℝ)) hm
  rw [hsound] at hsplit
  exact hsplit.symm

/-- Every complex eigenvalue lies between the first threshold of the `sharpBoundC` grid,
included, and its last threshold, excluded. -/
theorem certifiedPointsCSharp_bounds {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ}
    (h : IsHermRat X Y) (m : ℕ) (i : Fin n) :
    ((-(sharpBoundC X Y) : ℚ) : ℝ) ≤ (cplx_isHermitian h).eigenvalues i ∧
      (cplx_isHermitian h).eigenvalues i <
        ((-(sharpBoundC X Y) + (gridStepsR (sharpBoundC X Y) m : ℚ) * gridMesh m : ℚ) : ℝ) := by
  have hmem : (cplx_isHermitian h).eigenvalues i
      ∈ (Finset.univ.val.map (realify_isHermitian (blockRealFin_symm h)).eigenvalues) := by
    have hm := eigenvalues_fin_eq_two_mul h
    rw [hm, two_smul ℕ (Finset.univ.val.map (cplx_isHermitian h).eigenvalues), Multiset.mem_add]
    exact Or.inl (Multiset.mem_map_of_mem _ (Finset.mem_univ i))
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hmem
  rw [← hj]
  exact certifiedPointsR_covers (blockRealFin X Y) (blockRealFin_symm h)
    (blockRealFin_eigenvalue_abs_lt h) m j

/-- Every complex eigenvalue belongs to a half-open interval of the grid using `sharpBoundC`. -/
theorem certifiedPointsCSharp_interval {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℚ}
    (h : IsHermRat X Y) (m : ℕ) (i : Fin n) :
    ∃ j < gridStepsR (sharpBoundC X Y) m,
      ((-(sharpBoundC X Y) + (j : ℚ) * gridMesh m : ℚ) : ℝ) ≤
          (cplx_isHermitian h).eigenvalues i ∧
        (cplx_isHermitian h).eigenvalues i <
          ((-(sharpBoundC X Y) + ((j : ℚ) + 1) * gridMesh m : ℚ) : ℝ) := by
  obtain ⟨hlow, hhigh⟩ := certifiedPointsCSharp_bounds h m i
  have hh : (0 : ℝ) < ((gridMesh m : ℚ) : ℝ) := by exact_mod_cast gridMesh_pos m
  have hlow' : -((sharpBoundC X Y : ℚ) : ℝ) ≤ (cplx_isHermitian h).eigenvalues i := by
    have h := hlow
    push_cast at h
    exact h
  have hhigh' : (cplx_isHermitian h).eigenvalues i <
      -((sharpBoundC X Y : ℚ) : ℝ) + (gridStepsR (sharpBoundC X Y) m : ℝ) *
        ((gridMesh m : ℚ) : ℝ) := by
    have h := hhigh
    push_cast at h
    exact h
  obtain ⟨j, hj, hjl, hjr⟩ :=
    exists_grid_interval (-((sharpBoundC X Y : ℚ) : ℝ)) ((gridMesh m : ℚ) : ℝ)
      ((cplx_isHermitian h).eigenvalues i) (gridStepsR (sharpBoundC X Y) m) hh hlow' hhigh'
  refine ⟨j, hj, ?_, ?_⟩
  · push_cast
    exact hjl
  · push_cast
    exact hjr

/-- The total stored generation step count for the `sharpBoundC` grid is its point count times
`n + n`. -/
theorem certifiedPointsCSharp_totalSteps {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) :
    totalSteps (blockRealFin X Y) (blockRealFin_symm h) (gridOfR (sharpBoundC X Y) m)
      = (gridStepsR (sharpBoundC X Y) m + 1) * (n + n) :=
  certifiedPointsR_totalSteps (blockRealFin X Y) (blockRealFin_symm h) (sharpBoundC X Y) m

/-- The total stored generation operation count for the `sharpBoundC` grid is at most its point
count times `opsBound (n + n)`. -/
theorem certifiedPointsCSharp_ops {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) :
    totalOps (blockRealFin X Y) (blockRealFin_symm h) (gridOfR (sharpBoundC X Y) m)
      ≤ (gridStepsR (sharpBoundC X Y) m + 1) * opsBound (n + n) :=
  certifiedPointsR_ops (blockRealFin X Y) (blockRealFin_symm h) (sharpBoundC X Y) m

/-- Every witness used by the complex-data certificate with `sharpBoundC` satisfies the
corresponding `certificateBitsR` height bound. -/
theorem certifiedPointsCSharp_bits {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) {q : ℚ} (hq : q ∈ gridOfR (sharpBoundC X Y) m) :
    WitnessBitLe (certificateBitsR (blockRealFin X Y) (sharpBoundC X Y) m)
      (diagAux (n + n) (shift (blockRealFin X Y) q) (shift_symm (blockRealFin_symm h) q)) :=
  certifiedPointsR_bits (blockRealFin X Y) (blockRealFin_symm h) (sharpBoundC X Y) m hq

/-- Checking the complex-data certificate with `sharpBoundC` has assigned cost equal to its
point count times `checkPointOps (n + n)`. -/
theorem certifiedPointsCSharp_checker_ops {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) :
    (checkPointsCost (blockRealFin X Y) (certifiedPointsCSharp X Y h m)).2
      = (gridStepsR (sharpBoundC X Y) m + 1) * checkPointOps (n + n) :=
  certifiedPointsR_checker_ops (blockRealFin X Y) (blockRealFin_symm h)
    (blockRealFin_eigenvalue_abs_lt h) m

/-- The complex-data certificate using `sharpBoundC` satisfies the stated generation step count,
operation bound, witness height bound, and exact point-checking cost. -/
theorem certifiedPointsCSharp_resources {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) :
    totalSteps (blockRealFin X Y) (blockRealFin_symm h) (gridOfR (sharpBoundC X Y) m)
        = (gridStepsR (sharpBoundC X Y) m + 1) * (n + n)
      ∧ totalOps (blockRealFin X Y) (blockRealFin_symm h) (gridOfR (sharpBoundC X Y) m)
        ≤ (gridStepsR (sharpBoundC X Y) m + 1) * opsBound (n + n)
      ∧ (∀ q ∈ gridOfR (sharpBoundC X Y) m,
          WitnessBitLe (certificateBitsR (blockRealFin X Y) (sharpBoundC X Y) m)
            (diagAux (n + n) (shift (blockRealFin X Y) q) (shift_symm (blockRealFin_symm h) q)))
      ∧ (checkPointsCost (blockRealFin X Y) (certifiedPointsCSharp X Y h m)).2
        = (gridStepsR (sharpBoundC X Y) m + 1) * checkPointOps (n + n) :=
  ⟨certifiedPointsCSharp_totalSteps X Y h m, certifiedPointsCSharp_ops X Y h m,
    fun _ hq => certifiedPointsCSharp_bits X Y h m hq,
    certifiedPointsCSharp_checker_ops X Y h m⟩

/-- The grid interval count using `sharpBoundC` is at most the original complex-data interval
count `gridStepsC X Y m`. -/
theorem gridStepsR_sharpC_le_gridStepsC {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) :
    gridStepsR (sharpBoundC X Y) m ≤ gridStepsC X Y m := by
  unfold gridStepsR gridStepsC
  refine Nat.ceil_mono ?_
  have h := sharpBoundC_le_spectrumBoundC X Y
  have hm : (0 : ℚ) ≤ (m : ℚ) + 1 := by positivity
  nlinarith

/-- The grid interval count using `sharpBoundC` is at most the spectral grid interval count of
the real block matrix. -/
theorem gridStepsR_sharpC_le_block {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (m : ℕ) :
    gridStepsR (sharpBoundC X Y) m ≤ gridSteps (blockRealFin X Y) m := by
  rw [gridSteps_blockRealFin]
  exact gridStepsR_sharpC_le_gridStepsC X Y m

/-- The assigned point-checking cost of the complex-data certificate using `sharpBoundC` is at
most that of the original block-derived certificate. -/
theorem certifiedPointsCSharp_checker_ops_le_block {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) :
    (checkPointsCost (blockRealFin X Y) (certifiedPointsCSharp X Y h m)).2
      ≤ (checkPointsCost (blockRealFin X Y) (certifiedPointsC X Y h m)).2 := by
  rw [certifiedPointsCSharp_checker_ops, certifiedPointsC_checker_ops]
  exact Nat.mul_le_mul_right _ (Nat.succ_le_succ (gridStepsR_sharpC_le_block X Y m))

end CertifiedHermitianSpectrum
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage.CertifiedHermitianSpectrum

open Matrix

/-- The list of grid left endpoints, each repeated by the natural-number increment in the
supplied cumulative counts. -/
def gridSamples (lo h : ℚ) (counts : ℕ → ℕ) : ℕ → List ℚ
  | 0 => []
  | k + 1 => gridSamples lo h counts k ++
      List.replicate (counts (k + 1) - counts k) (lo + (k : ℚ) * h)

/-- The grid sample list can be split into the repetitions of its first endpoint followed by the
samples on the shifted grid. -/
theorem gridSamples_succ_head (lo h : ℚ) (counts : ℕ → ℕ) (k : ℕ) :
    gridSamples lo h counts (k + 1) = List.replicate (counts 1 - counts 0) lo ++
      gridSamples (lo + h) h (fun j => counts (j + 1)) k := by
  induction k with
  | zero => simp [gridSamples]
  | succ k ih =>
    rw [gridSamples, ih]
    have hq : lo + ((k + 1 : ℕ) : ℚ) * h = lo + h + (k : ℚ) * h := by
      push_cast
      ring
    simp only [gridSamples, List.append_assoc, hq]

/-- Decodes a certificate by repeating each left threshold according to the difference of the
consecutive negative counts after natural-number division by `divisor`. -/
def samplesFromCertificate {n : ℕ} (divisor : ℕ) : List (Point n) → List ℚ
  | [] => []
  | [_] => []
  | p :: q :: ps => List.replicate
      (negCountOf q.d / divisor - negCountOf p.d / divisor) p.q ++
      samplesFromCertificate divisor (q :: ps)

/-- Decodes certificate samples while counting the consecutive point pairs processed. -/
def samplesFromCertificateWithSteps {n : ℕ} (divisor : ℕ) :
    List (Point n) → List ℚ × ℕ
  | [] => ([], 0)
  | [_] => ([], 0)
  | p :: q :: ps =>
      let tail := samplesFromCertificateWithSteps divisor (q :: ps)
      (List.replicate (negCountOf q.d / divisor - negCountOf p.d / divisor) p.q ++ tail.1,
        tail.2 + 1)

/-- The decoder with steps returns the same samples as `samplesFromCertificate` and processes
`pts.length - 1` consecutive pairs. -/
theorem samplesFromCertificateWithSteps_spec {n : ℕ} (divisor : ℕ) (pts : List (Point n)) :
    (samplesFromCertificateWithSteps divisor pts).1 = samplesFromCertificate divisor pts ∧
      (samplesFromCertificateWithSteps divisor pts).2 = pts.length - 1 := by
  induction pts with
  | nil => simp [samplesFromCertificateWithSteps, samplesFromCertificate]
  | cons p ps ih =>
    cases ps with
    | nil => simp [samplesFromCertificateWithSteps, samplesFromCertificate]
    | cons q ps =>
      simp only [samplesFromCertificateWithSteps, samplesFromCertificate,
        List.length_cons] at ih ⊢
      exact ⟨by rw [ih.1], by rw [ih.2]; omega⟩

/-- Decoding points at equally spaced thresholds agrees with `gridSamples` using their divided
negative counts. -/
theorem samplesFromCertificate_grid {n : ℕ} (divisor : ℕ) (point : ℚ → Point n)
    (hpoint : ∀ q, (point q).q = q) (lo h : ℚ) (k : ℕ) :
    samplesFromCertificate divisor ((gridAux lo h k).map point) =
      gridSamples lo h (fun j => negCountOf (point (lo + (j : ℚ) * h)).d / divisor) k := by
  induction k generalizing lo with
  | zero => simp [gridAux, samplesFromCertificate, gridSamples]
  | succ k ih =>
    rw [gridSamples_succ_head]
    have hshift : (fun j : ℕ => negCountOf (point (lo + h + (j : ℚ) * h)).d / divisor) =
        (fun j : ℕ => negCountOf (point (lo + ((j + 1 : ℕ) : ℚ) * h)).d / divisor) := by
      funext j
      have hq : lo + h + (j : ℚ) * h = lo + ((j + 1 : ℕ) : ℚ) * h := by
        push_cast
        ring
      rw [hq]
    rw [← hshift, ← ih (lo + h)]
    cases k <;> simp [gridAux, samplesFromCertificate, hpoint]

/-- For monotone cumulative counts, the grid sample list has length `counts k - counts 0`. -/
theorem gridSamples_length (lo h : ℚ) (counts : ℕ → ℕ) (hc : Monotone counts) (k : ℕ) :
    (gridSamples lo h counts k).length = counts k - counts 0 := by
  induction k with
  | zero => simp [gridSamples]
  | succ k ih =>
    simp only [gridSamples, List.length_append, List.length_replicate, ih]
    have h0 : counts 0 ≤ counts k := hc (Nat.zero_le k)
    have h1 : counts k ≤ counts (k + 1) := hc (Nat.le_succ k)
    change counts k - counts 0 + (counts (k + 1) - counts k) = counts (k + 1) - counts 0
    omega

/-- A grid left endpoint occurs in the sample list whenever the cumulative count strictly
increases across that interval. -/
theorem mem_gridSamples (lo h : ℚ) (counts : ℕ → ℕ) {j k : ℕ}
    (hj : j < k) (hc : counts j < counts (j + 1)) :
    lo + (j : ℚ) * h ∈ gridSamples lo h counts k := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [gridSamples, List.mem_append]
    by_cases hjk : j < k
    · exact Or.inl (ih hjk)
    · have heq : j = k := by omega
      subst j
      exact Or.inr (List.mem_replicate.mpr ⟨by omega, rfl⟩)

/-- Counts of indexed values below successive grid thresholds are monotone when the grid spacing
is nonnegative. -/
theorem gridCounts_mono {n : ℕ} (lam : Fin n → ℝ) (lo h : ℚ) (hh : 0 ≤ h)
    (counts : ℕ → ℕ)
    (hc : ∀ j, counts j =
      (Finset.univ.filter fun i => lam i < ((lo + (j : ℚ) * h : ℚ) : ℝ)).card) :
    Monotone counts := by
  classical
  intro a b hab
  rw [hc a, hc b]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have habq : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast hab
  have hq : lo + (a : ℚ) * h ≤ lo + (b : ℚ) * h := by nlinarith
  exact lt_of_lt_of_le hi (by exact_mod_cast hq)

/-- If the grid encloses all indexed values and its cumulative counts are exact, every value is
within strictly one positive mesh spacing of a grid sample. -/
theorem gridSamples_approximates {n : ℕ} (lam : Fin n → ℝ) (lo h : ℚ)
    (hh : 0 < h) (counts : ℕ → ℕ)
    (hc : ∀ j, counts j =
      (Finset.univ.filter fun i => lam i < ((lo + (j : ℚ) * h : ℚ) : ℝ)).card)
    (k : ℕ) (hb : ∀ i, (lo : ℝ) ≤ lam i ∧
      lam i < ((lo + (k : ℚ) * h : ℚ) : ℝ)) (i : Fin n) :
    ∃ q ∈ gridSamples lo h counts k, |lam i - (q : ℝ)| < (h : ℝ) := by
  classical
  have hhr : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hb' := hb i
  push_cast at hb'
  obtain ⟨j, hj, hjl, hjr⟩ := exists_grid_interval (lo : ℝ) (h : ℝ) (lam i) k hhr
    hb'.1 hb'.2
  have hcast : ((lo + ((j + 1 : ℕ) : ℚ) * h : ℚ) : ℝ) =
      (lo : ℝ) + ((j : ℝ) + 1) * (h : ℝ) := by push_cast; rfl
  have hcast0 : ((lo + (j : ℚ) * h : ℚ) : ℝ) =
      (lo : ℝ) + (j : ℝ) * (h : ℝ) := by push_cast; rfl
  have hd : counts j < counts (j + 1) := by
    have hab : ((lo + (j : ℚ) * h : ℚ) : ℝ) ≤
        ((lo + ((j + 1 : ℕ) : ℚ) * h : ℚ) : ℝ) := by
      rw [hcast, hcast0]
      nlinarith
    have hint := card_filter_interval lam hab
    have hpos : 0 < (Finset.univ.filter fun t =>
        ((lo + (j : ℚ) * h : ℚ) : ℝ) ≤ lam t ∧
        lam t < ((lo + ((j + 1 : ℕ) : ℚ) * h : ℚ) : ℝ)).card := by
      apply Finset.card_pos.mpr
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by simpa only [hcast, hcast0] using! And.intro hjl hjr⟩⟩
    rw [hint, ← hc (j + 1), ← hc j] at hpos
    omega
  refine ⟨lo + (j : ℚ) * h, mem_gridSamples lo h counts hj hd, ?_⟩
  rw [hcast0, abs_of_nonneg (by linarith)]
  nlinarith

/-- The computed negative count at the `j`th threshold of the real spectral grid. -/
def spectrumGridCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (m j : ℕ) : ℕ :=
  negCountOf (pointOf A hA (-spectrumBound A + (j : ℚ) * gridMesh m)).d

/-- The computed real spectral grid count equals the number of eigenvalues strictly below its
threshold. -/
theorem spectrumGridCount_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsSymmRat A) (m j : ℕ) :
    spectrumGridCount A hA m j = (Finset.univ.filter fun i =>
      (realify_isHermitian hA).eigenvalues i <
        ((-spectrumBound A + (j : ℚ) * gridMesh m : ℚ) : ℝ)).card :=
  (pointOf_count A hA _).symm

/-- The rational sample list decoded from the real spectral certificate with divisor one. -/
def spectrumSamples {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (m : ℕ) : List ℚ :=
  samplesFromCertificate 1 (certifiedPoints A hA m)

/-- The decoded real spectrum samples agree with `gridSamples` using the computed cumulative
spectral counts. -/
theorem spectrumSamples_eq_gridSamples {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsSymmRat A) (m : ℕ) :
    spectrumSamples A hA m = gridSamples (-spectrumBound A) (gridMesh m)
      (spectrumGridCount A hA m) (gridSteps A m) := by
  unfold spectrumSamples certifiedPoints ptsOf gridOf
  rw [samplesFromCertificate_grid 1 (pointOf A hA) (fun _ => rfl)]
  simp only [Nat.div_one]
  rfl

/-- The real spectrum sample list is the grid histogram determined by exact cumulative
eigenvalue counts. -/
theorem spectrumSamples_histogram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsSymmRat A) (m : ℕ) :
    spectrumSamples A hA m = gridSamples (-spectrumBound A) (gridMesh m)
      (fun j => (Finset.univ.filter fun i => (realify_isHermitian hA).eigenvalues i <
        ((-spectrumBound A + (j : ℚ) * gridMesh m : ℚ) : ℝ)).card) (gridSteps A m) := by
  classical
  rw [spectrumSamples_eq_gridSamples]
  congr 1
  funext j
  exact spectrumGridCount_eq A hA m j

/-- The real spectrum sample list has length equal to the matrix dimension. -/
theorem spectrumSamples_length {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsSymmRat A) (m : ℕ) : (spectrumSamples A hA m).length = n := by
  rw [spectrumSamples_eq_gridSamples]
  rw [gridSamples_length _ _ _ (gridCounts_mono _ _ _ (le_of_lt (gridMesh_pos m)) _
    (spectrumGridCount_eq A hA m))]
  have h0 : spectrumGridCount A hA m 0 = 0 := by
    simpa [spectrumGridCount] using! pointOf_negBound_count A hA
  have hk : spectrumGridCount A hA m (gridSteps A m) = n := pointOf_last_count A hA m
  rw [h0, hk, Nat.sub_zero]

/-- Every eigenvalue of the symmetric rational matrix is within strictly `gridMesh m` of some
rational spectrum sample. -/
theorem spectrumSamples_approximates {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsSymmRat A) (m : ℕ) (i : Fin n) :
    ∃ q ∈ spectrumSamples A hA m,
      |(realify_isHermitian hA).eigenvalues i - (q : ℝ)| < (gridMesh m : ℝ) := by
  rw [spectrumSamples_eq_gridSamples]
  exact gridSamples_approximates _ _ _ (gridMesh_pos m) _ (spectrumGridCount_eq A hA m) _
    (certifiedPoints_covers A hA m) i

/-- The natural ceiling of `1 / ε`, used to choose a grid precision parameter. -/
def precisionFor (ε : ℚ) : ℕ := ⌈1 / ε⌉₊

/-- For positive rational `ε`, the mesh selected by `precisionFor ε` is at most `ε`. -/
theorem gridMesh_precisionFor_le {ε : ℚ} (hε : 0 < ε) : gridMesh (precisionFor ε) ≤ ε := by
  have hc : 1 / ε ≤ (precisionFor ε : ℚ) := Nat.le_ceil _
  have hp : (0 : ℚ) < (precisionFor ε : ℚ) + 1 := by positivity
  simpa only [gridMesh, one_div] using! (one_div_le hp hε).mpr (by linarith)

/-- The rational spectrum samples and their certificate for a symmetric rational matrix at the
precision selected from `ε`. -/
def certifiedSpectrum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsSymmRat A)
    (ε : ℚ) : List ℚ × List (Point n) :=
  let pts := certifiedPoints A hA (precisionFor ε)
  (samplesFromCertificate 1 pts, pts)

/-- For positive `ε`, `certifiedSpectrum` returns `n` samples and an accepted certificate, with
every eigenvalue within strictly `ε` of some returned sample. -/
theorem certifiedSpectrum_spec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsSymmRat A) {ε : ℚ} (hε : 0 < ε) :
    (certifiedSpectrum A hA ε).1.length = n ∧
      checkPoints A (certifiedSpectrum A hA ε).2 = true ∧
      ∀ i, ∃ q ∈ (certifiedSpectrum A hA ε).1,
        |(realify_isHermitian hA).eigenvalues i - (q : ℝ)| < (ε : ℝ) := by
  refine ⟨spectrumSamples_length A hA _, certifiedPoints_check A hA _, ?_⟩
  intro i
  obtain ⟨q, hq, he⟩ := spectrumSamples_approximates A hA (precisionFor ε) i
  refine ⟨q, hq, lt_of_lt_of_le he ?_⟩
  exact_mod_cast gridMesh_precisionFor_le hε

/-- Exact cumulative counts on a nonnegative-mesh grid enclosing all indexed values yield a
sample list of length `n`. -/
theorem gridSamples_length_of_bounds {n : ℕ} (lam : Fin n → ℝ) (lo h : ℚ)
    (hh : 0 ≤ h) (counts : ℕ → ℕ)
    (hc : ∀ j, counts j =
      (Finset.univ.filter fun i => lam i < ((lo + (j : ℚ) * h : ℚ) : ℝ)).card)
    (k : ℕ) (hb : ∀ i, (lo : ℝ) ≤ lam i ∧
      lam i < ((lo + (k : ℚ) * h : ℚ) : ℝ)) :
    (gridSamples lo h counts k).length = n := by
  classical
  rw [gridSamples_length _ _ _ (gridCounts_mono lam lo h hh counts hc) k, hc k, hc 0]
  have hk : (Finset.univ.filter fun i =>
      lam i < ((lo + (k : ℚ) * h : ℚ) : ℝ)).card = n := by
    rw [Finset.filter_true_of_mem]
    · simp
    · intro i _
      exact (hb i).2
  have h0 : (Finset.univ.filter fun i =>
      lam i < ((lo + ((0 : ℕ) : ℚ) * h : ℚ) : ℝ)).card = 0 := by
    apply Finset.card_filter_eq_zero_iff.mpr
    intro i _
    simpa only [Nat.cast_zero, zero_mul, add_zero] using! not_lt_of_ge (hb i).1
  rw [hk, h0, Nat.sub_zero]

/-- Half the computed negative count of the real block matrix at a threshold of the
`sharpBoundC` grid. -/
def spectrumGridCountC {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (h : IsHermRat X Y)
    (m j : ℕ) : ℕ :=
  negCountOf (pointOf (blockRealFin X Y) (blockRealFin_symm h)
    (-sharpBoundC X Y + (j : ℚ) * gridMesh m)).d / 2

/-- The halved block negative count equals the number of complex eigenvalues strictly below the
grid threshold. -/
theorem spectrumGridCountC_eq {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m j : ℕ) :
    spectrumGridCountC X Y h m j = (Finset.univ.filter fun i =>
      (cplx_isHermitian h).eigenvalues i <
        ((-sharpBoundC X Y + (j : ℚ) * gridMesh m : ℚ) : ℝ)).card := by
  unfold spectrumGridCountC
  rw [point_count_eq_cplx h (pointOf_valid (blockRealFin X Y) (blockRealFin_symm h) _)]
  simp only [pointOf]
  omega

/-- The rational sample list decoded from the complex-data certificate using `sharpBoundC`,
dividing cumulative block counts by two. -/
def spectrumSamplesC {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (h : IsHermRat X Y)
    (m : ℕ) : List ℚ :=
  samplesFromCertificate 2 (certifiedPointsCSharp X Y h m)

/-- The decoded complex spectrum samples agree with `gridSamples` using the computed complex
cumulative counts. -/
theorem spectrumSamplesC_eq_gridSamples {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) :
    spectrumSamplesC X Y h m = gridSamples (-sharpBoundC X Y) (gridMesh m)
      (spectrumGridCountC X Y h m) (gridStepsR (sharpBoundC X Y) m) := by
  unfold spectrumSamplesC certifiedPointsCSharp certifiedPointsR ptsOf gridOfR
  exact samplesFromCertificate_grid 2 (pointOf (blockRealFin X Y) (blockRealFin_symm h))
    (fun _ => rfl) _ _ _

/-- The complex spectrum sample list is the grid histogram determined by exact cumulative
complex eigenvalue counts. -/
theorem spectrumSamplesC_histogram {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) :
    spectrumSamplesC X Y h m = gridSamples (-sharpBoundC X Y) (gridMesh m)
      (fun j => (Finset.univ.filter fun i => (cplx_isHermitian h).eigenvalues i <
        ((-sharpBoundC X Y + (j : ℚ) * gridMesh m : ℚ) : ℝ)).card)
      (gridStepsR (sharpBoundC X Y) m) := by
  classical
  rw [spectrumSamplesC_eq_gridSamples]
  congr 1
  funext j
  exact spectrumGridCountC_eq X Y h m j

/-- The complex spectrum sample list has length equal to the complex matrix dimension. -/
theorem spectrumSamplesC_length {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) : (spectrumSamplesC X Y h m).length = n := by
  rw [spectrumSamplesC_eq_gridSamples]
  exact gridSamples_length_of_bounds _ _ _ (le_of_lt (gridMesh_pos m)) _
    (spectrumGridCountC_eq X Y h m) _ (certifiedPointsCSharp_bounds h m)

/-- Every complex eigenvalue is within strictly `gridMesh m` of some rational complex spectrum
sample. -/
theorem spectrumSamplesC_approximates {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) (i : Fin n) :
    ∃ q ∈ spectrumSamplesC X Y h m,
      |(cplx_isHermitian h).eigenvalues i - (q : ℝ)| < (gridMesh m : ℝ) := by
  rw [spectrumSamplesC_eq_gridSamples]
  exact gridSamples_approximates _ _ _ (gridMesh_pos m) _ (spectrumGridCountC_eq X Y h m) _
    (certifiedPointsCSharp_bounds h m) i

/-- The counted decoder returns `spectrumSamplesC X Y h m` and processes exactly `gridStepsR
(sharpBoundC X Y) m` consecutive pairs. -/
theorem spectrumSamplesC_decoder_steps {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) (m : ℕ) :
    (samplesFromCertificateWithSteps 2 (certifiedPointsCSharp X Y h m)).1 =
        spectrumSamplesC X Y h m ∧
      (samplesFromCertificateWithSteps 2 (certifiedPointsCSharp X Y h m)).2 =
        gridStepsR (sharpBoundC X Y) m := by
  obtain ⟨hf, hs⟩ := samplesFromCertificateWithSteps_spec 2 (certifiedPointsCSharp X Y h m)
  exact ⟨hf, by rw [hs, certifiedPointsCSharp_length]; omega⟩

/-- The rational spectrum samples and their real block certificate for rational Hermitian data
at the precision selected from `ε`. -/
def certifiedSpectrumC {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ) (h : IsHermRat X Y)
    (ε : ℚ) : List ℚ × List (Point (n + n)) :=
  let pts := certifiedPointsCSharp X Y h (precisionFor ε)
  (samplesFromCertificate 2 pts, pts)

/-- For positive `ε`, `certifiedSpectrumC` returns `n` samples and an accepted real block
certificate, with every complex eigenvalue within strictly `ε` of some returned sample. -/
theorem certifiedSpectrumC_spec {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℚ)
    (h : IsHermRat X Y) {ε : ℚ} (hε : 0 < ε) :
    (certifiedSpectrumC X Y h ε).1.length = n ∧
      checkPoints (blockRealFin X Y) (certifiedSpectrumC X Y h ε).2 = true ∧
      ∀ i, ∃ q ∈ (certifiedSpectrumC X Y h ε).1,
        |(cplx_isHermitian h).eigenvalues i - (q : ℝ)| < (ε : ℝ) := by
  refine ⟨spectrumSamplesC_length X Y h _, certifiedPointsCSharp_check X Y h _, ?_⟩
  intro i
  obtain ⟨q, hq, he⟩ := spectrumSamplesC_approximates X Y h (precisionFor ε) i
  refine ⟨q, hq, lt_of_lt_of_le he ?_⟩
  exact_mod_cast gridMesh_precisionFor_le hε

end CertifiedHermitianSpectrum
