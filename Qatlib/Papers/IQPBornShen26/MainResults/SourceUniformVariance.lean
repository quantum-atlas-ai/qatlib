/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IQPBornShen26.MainResults.SourceCharFunVariance
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# c004 — Theorem 3.8: variance `2^{-r_a}` of IQP characteristic values under
uniform initialization

Shen–Pielawa–Dunjko–Wang, arXiv:2602.11042v2.
Theorem 3.8 (printed p. 7, Eq. (9) = appendix Eq. (43)): with parameters
initialized i.i.d. uniform on `[0, 2π)` and a fixed Fourier frequency `a`,
`Var_θ[C_θ^a] = 2^{-r_a}`, where the critical rank `r_a = dim span_F₂(S^a)` is
the number of `F₂`-linearly independent generators in `S^a`.

The Lean proof instantiates the moment form of Theorem 3.2
(`theorem3_2_var_charFun_moments`) with the uniform moments
`E[sin²(2θ)] = E[cos²(2θ)] = 1/2`, `E[cos(2θ)] = 0` (computed from first
principles by the fundamental theorem of calculus), reducing the variance to
`|Ξ^a| · 2^{-m_a}`.  The combinatorial core is the identification of the
zero-sum subsets `Ξ^a` with the kernel of the `F₂`-linear span map
`v ↦ Σ_i v_i s_i` on `↥S^a → F₂`: `|Ξ^a| = 2^{dim ker φ}`, and rank–nullity
gives `dim ker φ = m_a − r_a`, so `|Ξ^a| · 2^{-m_a} = 2^{-r_a}`.

Boundary case: the paper states Eq. (9) for `a ≠ 0`, but as an identity about
the decomposed characteristic function it requires `S^a ≠ ∅` — if every
generator is orthogonal to `a` then `C^a` is constant in `θ` and the variance
is `0`, not `2^0 = 1`.  The Lean theorem therefore carries the hypothesis
`(supportGen s a).Nonempty` (which `a ≠ 0` does not imply), recorded here as a
clarification of the paper's statement rather than a gap in its regime of
interest.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open intervalIntegral Qatlib.Papers.IQPBornShen26.MainResults

namespace Qatlib.Papers.IQPBornShen26.MainResults.UniformVariance

/-- Two is prime, giving the binary field structure used by the generator map. -/
instance : Fact ((2:ℕ).Prime) := ⟨Nat.prime_two⟩

variable {D n : ℕ} (s : Fin D → (Fin n → ZMod 2)) (a : Fin n → ZMod 2)

/-! ## The span map and the critical rank -/

/-- The `F₂`-linear span map `φ : v ↦ Σ_{i ∈ S^a} v_i • s_i` from indicator
vectors over `S^a` to `F₂^n`; its range is `span_F₂(S^a)` and its kernel is
the linear space of zero-sum subsets. -/
def genMap : (↥(supportGen s a) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun v := ∑ i, v i • s ↑i
  map_add' v w := by
    ext k
    simp only [Finset.sum_apply, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    ext k
    have h1 : ∀ i : ↥(supportGen s a), (((c • v) i) • s ↑i) k = c * ((v i • s ↑i) k) := by
      intro i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    calc (∑ i, (c • v) i • s ↑i) k = ∑ i, (((c • v) i) • s ↑i) k := Finset.sum_apply _ _ _
      _ = ∑ i, c * ((v i • s ↑i) k) :=
          Finset.sum_congr rfl fun i _ => h1 i
      _ = c * ∑ i, (v i • s ↑i) k := (Finset.mul_sum _ _ _).symm
      _ = ((RingHom.id (ZMod 2)) c • ∑ i, v i • s ↑i) k := by simp

/-- The generator map evaluates to the indicated binary sum. -/
lemma genMap_apply (v : ↥(supportGen s a) → ZMod 2) :
    genMap s a v = ∑ i, v i • s ↑i := rfl

/-- The kernel of the finite binary generator map is a finite type. -/
noncomputable instance : Fintype ↥(LinearMap.ker (genMap s a)) :=
  Fintype.ofFinite _

/-- The critical rank `r_a = dim span_F₂(S^a)` of arXiv:2602.11042v2,
Theorem 3.8: the number of `F₂`-linearly independent generators among
`{s_j : a · s_j = 1}`, as the dimension of the range of the span map. -/
def critRank : ℕ := Module.finrank (ZMod 2) (LinearMap.range (genMap s a))

/-- Rank–nullity for the span map: `r_a + dim ker φ = |S^a|`. -/
lemma critRank_add_ker : critRank s a
    + Module.finrank (ZMod 2) (LinearMap.ker (genMap s a)) = (supportGen s a).card := by
  rw [critRank, LinearMap.finrank_range_add_finrank_ker, Module.finrank_pi (ZMod 2),
    Fintype.card_coe]

/-! ## Zero-sum subsets as the kernel of the span map -/

/-- The indicator vector of a subset `J ⊆ S^a` in `↥S^a → F₂`. -/
def indVec (J : Finset (Fin D)) : ↥(supportGen s a) → ZMod 2 :=
  fun i => if (i : Fin D) ∈ J then 1 else 0

/-- The subset of `S^a` carried by a `↥S^a → F₂` vector (its `1`-support). -/
def vecSup (v : ↥(supportGen s a) → ZMod 2) : Finset (Fin D) :=
  (Finset.univ.filter fun i => v i = 1).image Subtype.val

/-- A binary residue different from one equals zero. -/
lemma zmod2_ne_one {x : ZMod 2} (h : x ≠ 1) : x = 0 := by
  by_contra h0
  exact absurd h (by revert h h0 x; decide)

/-- The support of a coefficient vector is contained in the generator support. -/
lemma vecSup_subset (v : ↥(supportGen s a) → ZMod 2) :
    vecSup s a v ⊆ supportGen s a := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
  exact i.2

/-- The indicator of the support recovers the binary vector. -/
lemma indVec_vecSup (v : ↥(supportGen s a) → ZMod 2) :
    indVec s a (vecSup s a v) = v := by
  funext i
  have hmem : (i : Fin D) ∈ vecSup s a v ↔ v i = 1 := by
    constructor
    · intro h
      obtain ⟨i', hi', heq⟩ := Finset.mem_image.1 h
      rw [Subtype.val_injective heq] at hi'
      exact (Finset.mem_filter.1 hi').2
    · intro hv
      exact Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩, rfl⟩
  by_cases h : v i = 1
  · simp [indVec, hmem.2 h, h]
  · rw [zmod2_ne_one h]
    simp [indVec, fun hh : v i = 1 => h hh, hmem]

/-- Taking the support of an indicator recovers its finite set. -/
lemma vecSup_indVec {J : Finset (Fin D)} (hJ : J ⊆ supportGen s a) :
    vecSup s a (indVec s a J) = J := by
  ext j
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
    have hv : indVec s a J i = 1 := (Finset.mem_filter.1 hi).2
    have hval : (i : Fin D) ∈ J := by
      by_cases h : (i : Fin D) ∈ J
      · exact h
      · simp [indVec, h] at hv
    exact hval
  · intro hj
    exact Finset.mem_image.2 ⟨⟨j, hJ hj⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [indVec, hj]⟩, rfl⟩

/-- Applying the generator map to an indicator gives the sum over its support. -/
lemma genMap_indVec {J : Finset (Fin D)} (hJ : J ⊆ supportGen s a) :
    genMap s a (indVec s a J) = ∑ j ∈ J, s j := by
  have himg : ((Finset.univ.filter fun i : ↥(supportGen s a) => (i : Fin D) ∈ J)).image
      Subtype.val = J := by
    ext j
    constructor
    · intro h
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
      exact (Finset.mem_filter.1 hi).2
    · intro hj
      exact Finset.mem_image.2 ⟨⟨j, hJ hj⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩, rfl⟩
  have hterm : ∀ i : ↥(supportGen s a),
      indVec s a J i • s ↑i = if (i : Fin D) ∈ J then s ↑i else 0 := by
    intro i
    by_cases h : (i : Fin D) ∈ J <;> simp [indVec, h]
  calc genMap s a (indVec s a J)
      = ∑ i : ↥(supportGen s a), indVec s a J i • s ↑i := genMap_apply _ _ _
    _ = ∑ i ∈ Finset.univ.filter fun i : ↥(supportGen s a) => (i : Fin D) ∈ J, s ↑i := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun i _ => hterm i
    _ = ∑ i ∈ ((Finset.univ.filter fun i : ↥(supportGen s a) => (i : Fin D) ∈ J)).image
          Subtype.val, s i :=
        (Finset.sum_image (Subtype.val_injective.injOn)).symm
    _ = ∑ j ∈ J, s j := by rw [himg]

/-- Summing over binary vectors equals summing over their finite supports. -/
lemma sum_vecSup (v : ↥(supportGen s a) → ZMod 2) :
    ∑ j ∈ vecSup s a v, s j = genMap s a v := by
  rw [genMap_apply, vecSup, Finset.sum_image (Subtype.val_injective.injOn),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : v i = 1
  · simp [h, one_smul]
  · rw [zmod2_ne_one h]
    simp [zero_smul]

/-- Membership in the zero-sum sets is equivalent to the vanishing generator sum. -/
lemma mem_zeroSumSets_iff {J : Finset (Fin D)} :
    J ∈ zeroSumSets s a ↔ J ⊆ supportGen s a ∧ ∑ j ∈ J, s j = 0 := by
  simp [zeroSumSets, Finset.mem_filter]

/-- Cardinality of the zero-sum subsets: `|Ξ^a| = 2^{dim ker φ}` with `φ` the
span map (arXiv:2602.11042v2, proof of Theorem 3.8). -/
lemma card_zeroSumSets :
    (zeroSumSets s a).card
      = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (genMap s a)) := by
  have key : Fintype.card {J : Finset (Fin D) // J ∈ zeroSumSets s a}
      = Fintype.card ↥(LinearMap.ker (genMap s a)) := by
    refine Fintype.card_of_bijective (f := fun J : {J : Finset (Fin D) // J ∈ zeroSumSets s a} =>
      ⟨indVec s a J.1, LinearMap.mem_ker.2 (by
        rw [genMap_indVec s a (mem_zeroSumSets_iff s a |>.1 J.2).1]
        exact (mem_zeroSumSets_iff s a |>.1 J.2).2)⟩) ?_
    constructor
    · intro J K hJK
      have hsubJ : J.1 ⊆ supportGen s a := (mem_zeroSumSets_iff s a |>.1 J.2).1
      have hsubK : K.1 ⊆ supportGen s a := (mem_zeroSumSets_iff s a |>.1 K.2).1
      have h : indVec s a J.1 = indVec s a K.1 := congrArg Subtype.val hJK
      exact Subtype.ext (by
        calc J.1 = vecSup s a (indVec s a J.1) := (vecSup_indVec s a hsubJ).symm
          _ = vecSup s a (indVec s a K.1) := by rw [h]
          _ = K.1 := vecSup_indVec s a hsubK)
    · intro v
      refine ⟨⟨vecSup s a (v : ↥(supportGen s a) → ZMod 2), ?_⟩, ?_⟩
      · rw [mem_zeroSumSets_iff s a]
        exact ⟨vecSup_subset s a _, by rw [sum_vecSup s a _, LinearMap.mem_ker.1 v.2]⟩
      · exact Subtype.ext (indVec_vecSup s a _)
  have hcard := Module.card_eq_pow_finrank (K := ZMod 2)
    (V := ↥(LinearMap.ker (genMap s a)))
  calc (zeroSumSets s a).card
      = Fintype.card ↥(zeroSumSets s a) := (Fintype.card_coe (zeroSumSets s a)).symm
    _ = Fintype.card ↥(LinearMap.ker (genMap s a)) := key
    _ = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) (LinearMap.ker (genMap s a)) := hcard
    _ = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (genMap s a)) := by rw [ZMod.card (n := 2)]

/-! ## The uniform measure on `[0, 2π)` and its moments -/

/-- The uniform probability measure on `[0, 2π)`. -/
def unif2pi : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) • volume.restrict (Set.Ioc (0:ℝ) (2 * Real.pi))

/-- The normalized angle measure has total mass one. -/
instance : IsProbabilityMeasure unif2pi where
  measure_univ := by
    rw [unif2pi, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
      smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
    field_simp
    exact ENNReal.ofReal_one

/-- The cosine of four pi equals one. -/
private lemma cos_4pi : Real.cos (4 * Real.pi) = 1 := by
  rw [show (4:ℝ) * Real.pi = 2 * (2 * Real.pi) from by ring, Real.cos_two_mul,
    Real.cos_two_pi]
  norm_num

/-- The sine of four pi vanishes. -/
private lemma sin_4pi : Real.sin (4 * Real.pi) = 0 := by
  rw [show (4:ℝ) * Real.pi = 2 * (2 * Real.pi) from by ring, Real.sin_two_mul,
    Real.sin_two_pi]
  norm_num

/-- The sine of eight pi vanishes. -/
private lemma sin_8pi : Real.sin (8 * Real.pi) = 0 := by
  rw [show (8:ℝ) * Real.pi = 2 * (4 * Real.pi) from by ring, Real.sin_two_mul, sin_4pi,
    cos_4pi]
  norm_num

/-- Multiplication by two has constant derivative two. -/
private lemma hasDeriv_two_mul (x : ℝ) :
    HasDerivAt (fun y : ℝ => 2 * y) (2:ℝ) x := by
  have h := HasDerivAt.const_mul (2:ℝ) (hasDerivAt_id x)
  simp only [id_eq, mul_one] at h
  exact h

/-- Multiplication by four has constant derivative four. -/
private lemma hasDeriv_four_mul (x : ℝ) :
    HasDerivAt (fun y : ℝ => 4 * y) (4:ℝ) x := by
  have h := HasDerivAt.const_mul (4:ℝ) (hasDerivAt_id x)
  simp only [id_eq, mul_one] at h
  exact h

/-- The derivative of cosine at twice the argument includes the factor two. -/
private lemma hasDeriv_cos2x (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos (2 * y)) (-Real.sin (2 * x) * (2:ℝ)) x :=
  HasDerivAt.cos (hasDeriv_two_mul x)

/-- The derivative of sine at twice the argument includes the factor two. -/
private lemma hasDeriv_sin2x (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (2 * y)) (Real.cos (2 * x) * (2:ℝ)) x :=
  HasDerivAt.sin (hasDeriv_two_mul x)

/-- The sine of twice the argument has zero integral over the angle interval. -/
private lemma integral_sin_Ioc :
    ∫ x in Set.Ioc (0:ℝ) (2 * Real.pi), Real.sin (2 * x) ∂volume = 0 := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  have hint : IntervalIntegrable (fun x : ℝ => Real.sin (2 * x)) volume 0 (2 * Real.pi) :=
    Continuous.intervalIntegrable (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)) _ _
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
      HasDerivAt (fun y : ℝ => -(Real.cos (2 * y) / 2)) (Real.sin (2 * x)) x := by
    intro x _
    have h := ((hasDeriv_cos2x x).div_const (2:ℝ)).neg
    rw [show -(-Real.sin (2 * x) * (2:ℝ) / (2:ℝ)) = Real.sin (2 * x) from by
        field_simp] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    show (2:ℝ) * (2 * Real.pi) = 4 * Real.pi from by ring, cos_4pi,
    show (2:ℝ) * 0 = 0 from by ring, Real.cos_zero]
  norm_num

/-- The cosine of twice the argument has zero integral over the angle interval. -/
private lemma integral_cos_Ioc :
    ∫ x in Set.Ioc (0:ℝ) (2 * Real.pi), Real.cos (2 * x) ∂volume = 0 := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  have hint : IntervalIntegrable (fun x : ℝ => Real.cos (2 * x)) volume 0 (2 * Real.pi) :=
    Continuous.intervalIntegrable (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)) _ _
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
      HasDerivAt (fun y : ℝ => Real.sin (2 * y) / 2) (Real.cos (2 * x)) x := by
    intro x _
    have h := (hasDeriv_sin2x x).div_const (2:ℝ)
    rw [show Real.cos (2 * x) * (2:ℝ) / (2:ℝ) = Real.cos (2 * x) from by
        field_simp] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    show (2:ℝ) * (2 * Real.pi) = 4 * Real.pi from by ring, sin_4pi,
    show (2:ℝ) * 0 = 0 from by ring, Real.sin_zero]
  norm_num

/-- The sine-cosine product has zero integral over the angle interval. -/
private lemma integral_sin_cos_Ioc :
    ∫ x in Set.Ioc (0:ℝ) (2 * Real.pi), Real.sin (2 * x) * Real.cos (2 * x) ∂volume = 0 := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  have hint : IntervalIntegrable
      (fun x : ℝ => Real.sin (2 * x) * Real.cos (2 * x)) volume 0 (2 * Real.pi) :=
    Continuous.intervalIntegrable ((Real.continuous_sin.mul Real.continuous_cos).comp
      (continuous_const.mul continuous_id)) _ _
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
      HasDerivAt (fun y : ℝ => Real.sin (2 * y) * Real.sin (2 * y) / 4)
        (Real.sin (2 * x) * Real.cos (2 * x)) x := by
    intro x _
    have h3 := ((hasDeriv_sin2x x).mul (hasDeriv_sin2x x)).div_const (4:ℝ)
    rw [show (Real.cos (2 * x) * (2:ℝ) * Real.sin (2 * x)
        + Real.sin (2 * x) * (Real.cos (2 * x) * (2:ℝ))) / (4:ℝ)
        = Real.sin (2 * x) * Real.cos (2 * x) from by ring] at h3
    exact h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    show (2:ℝ) * (2 * Real.pi) = 4 * Real.pi from by ring, sin_4pi,
    show (2:ℝ) * 0 = 0 from by ring, Real.sin_zero]
  norm_num

/-- The squared sine has its half-period average over the angle interval. -/
private lemma integral_sin_sq_Ioc :
    ∫ x in Set.Ioc (0:ℝ) (2 * Real.pi), Real.sin (2 * x) ^ 2 ∂volume = Real.pi := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  have hint : IntervalIntegrable (fun x : ℝ => Real.sin (2 * x) ^ 2) volume 0 (2 * Real.pi) :=
    Continuous.intervalIntegrable
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2) _ _
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
      HasDerivAt (fun y : ℝ => y / 2 - Real.sin (4 * y) / 8)
        (Real.sin (2 * x) ^ 2) x := by
    intro x _
    have hs : HasDerivAt (fun y : ℝ => Real.sin (4 * y)) (Real.cos (4 * x) * (4:ℝ)) x :=
      HasDerivAt.sin (hasDeriv_four_mul x)
    have h3 := ((hasDerivAt_id x).div_const (2:ℝ)).sub (hs.div_const (8:ℝ))
    have hkey : Real.sin (2 * x) ^ 2 = 1 / 2 - Real.cos (4 * x) / 2 := by
      have h4 : Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 - 1 := by
        rw [show (4:ℝ) * x = 2 * (2 * x) from by ring]
        exact Real.cos_two_mul (2 * x)
      rw [Real.sin_sq, h4]
      ring
    rw [show (1:ℝ) / 2 - Real.cos (4 * x) * (4:ℝ) / (8:ℝ)
        = Real.sin (2 * x) ^ 2 from by rw [hkey]; ring] at h3
    exact h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    show (4:ℝ) * (2 * Real.pi) = 8 * Real.pi from by ring, sin_8pi,
    show (4:ℝ) * 0 = 0 from by ring, Real.sin_zero]
  norm_num

/-- The squared cosine has its half-period average over the angle interval. -/
private lemma integral_cos_sq_Ioc :
    ∫ x in Set.Ioc (0:ℝ) (2 * Real.pi), Real.cos (2 * x) ^ 2 ∂volume = Real.pi := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  have hint : IntervalIntegrable (fun x : ℝ => Real.cos (2 * x) ^ 2) volume 0 (2 * Real.pi) :=
    Continuous.intervalIntegrable
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).pow 2) _ _
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
      HasDerivAt (fun y : ℝ => y / 2 + Real.sin (4 * y) / 8)
        (Real.cos (2 * x) ^ 2) x := by
    intro x _
    have hs : HasDerivAt (fun y : ℝ => Real.sin (4 * y)) (Real.cos (4 * x) * (4:ℝ)) x :=
      HasDerivAt.sin (hasDeriv_four_mul x)
    have h3 := ((hasDerivAt_id x).div_const (2:ℝ)).add (hs.div_const (8:ℝ))
    have hkey : Real.cos (2 * x) ^ 2 = 1 / 2 + Real.cos (4 * x) / 2 := by
      have h4 : Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 - 1 := by
        rw [show (4:ℝ) * x = 2 * (2 * x) from by ring]
        exact Real.cos_two_mul (2 * x)
      rw [h4]
      ring
    rw [show (1:ℝ) / 2 + Real.cos (4 * x) * (4:ℝ) / (8:ℝ)
        = Real.cos (2 * x) ^ 2 from by rw [hkey]; ring] at h3
    exact h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    show (4:ℝ) * (2 * Real.pi) = 8 * Real.pi from by ring, sin_8pi,
    show (4:ℝ) * 0 = 0 from by ring, Real.sin_zero]
  norm_num

/-- The uniform-angle expectation of sine vanishes. -/
lemma integral_sin_unif : ∫ x, Real.sin (2 * x) ∂unif2pi = 0 := by
  rw [unif2pi, MeasureTheory.integral_smul_measure, integral_sin_Ioc, smul_zero]

/-- The uniform-angle expectation of the sine-cosine product vanishes. -/
lemma integral_sin_cos_unif : ∫ x, Real.sin (2 * x) * Real.cos (2 * x) ∂unif2pi = 0 := by
  rw [unif2pi, MeasureTheory.integral_smul_measure, integral_sin_cos_Ioc, smul_zero]

/-- The uniform-angle expectation of cosine vanishes. -/
lemma integral_cos_unif : ∫ x, Real.cos (2 * x) ∂unif2pi = 0 := by
  rw [unif2pi, MeasureTheory.integral_smul_measure, integral_cos_Ioc, smul_zero]

/-- The uniform-angle expectation of squared sine is one half. -/
lemma integral_sin_sq_unif : ∫ x, Real.sin (2 * x) ^ 2 ∂unif2pi = 1 / 2 := by
  rw [unif2pi, MeasureTheory.integral_smul_measure, integral_sin_sq_Ioc, smul_eq_mul,
    ENNReal.toReal_ofReal (by positivity)]
  field_simp

/-- The uniform-angle expectation of squared cosine is one half. -/
lemma integral_cos_sq_unif : ∫ x, Real.cos (2 * x) ^ 2 ∂unif2pi = 1 / 2 := by
  rw [unif2pi, MeasureTheory.integral_smul_measure, integral_cos_sq_Ioc, smul_eq_mul,
    ENNReal.toReal_ofReal (by positivity)]
  field_simp

/-! ## Theorem 3.8 -/

/-- **Theorem 3.8** (variance of the characteristic function value under
uniform initialization, arXiv:2602.11042v2, Eq. (9)): for i.i.d.
`θ_j ~ U[0, 2π)` and `S^a ≠ ∅`,
`Var_θ[C_θ^a] = 2^{-r_a}` with `r_a` the critical rank `dim span_F₂(S^a)`,
formalized as `finrank` of the range of the span map `genMap`.  The sign
function `η` of the commutation decomposition is constrained to `±1` on `Ξ^a`.
The nonemptiness hypothesis `S^a ≠ ∅` is an implicit assumption of the paper's
statement (see the module docstring for the degenerate case). -/
theorem theorem3_8_var_uniform (η : Finset (Fin D) → ℝ)
    (hη : ∀ J ∈ zeroSumSets s a, η J * η J = 1)
    (hm : (supportGen s a).Nonempty) :
    ProbabilityTheory.variance (charFunIQP s a η) (Measure.pi fun _ : Fin D => unif2pi)
      = (2:ℝ) ^ (-(critRank s a : ℤ)) := by
  have hm1 : 1 ≤ (supportGen s a).card := Finset.card_pos.2 hm
  rw [CharVariance.theorem3_2_var_charFun_moments integral_sin_unif integral_sin_cos_unif hη,
    integral_sin_sq_unif, integral_cos_sq_unif, integral_cos_unif]
  have hcard : ∀ J ∈ zeroSumSets s a,
      ((1:ℝ) / 2) ^ J.card * ((1:ℝ) / 2) ^ (supportGen s a \ J).card
        = ((1:ℝ) / 2) ^ (supportGen s a).card := by
    intro J hJ
    have hsub := (mem_zeroSumSets_iff s a |>.1 hJ).1
    rw [← pow_add, Finset.card_sdiff, Finset.inter_eq_left.2 hsub,
      Nat.add_sub_cancel' (Finset.card_le_card hsub)]
  rw [Finset.sum_congr rfl fun J hJ => hcard J hJ, Finset.sum_const, nsmul_eq_mul,
    zero_pow (by omega), sub_zero]
  rw [card_zeroSumSets]
  have hrk := critRank_add_ker s a
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (genMap s a))
      = (supportGen s a).card - critRank s a := by omega
  have e1 : (((2:ℕ) ^ Module.finrank (ZMod 2) (LinearMap.ker (genMap s a)) : ℕ) : ℝ)
      = (2:ℝ) ^ ((Module.finrank (ZMod 2) (LinearMap.ker (genMap s a)) : ℕ) : ℤ) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, zpow_natCast]
  have e2 : ∀ k : ℕ, ((1:ℝ) / 2) ^ k = (2:ℝ) ^ (-(k : ℤ)) := by
    intro k
    rw [one_div, inv_pow, ← zpow_natCast, zpow_neg]
  have hcomb := zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)
    ((Module.finrank (ZMod 2) (LinearMap.ker (genMap s a)) : ℕ) : ℤ)
    (-((supportGen s a).card : ℤ))
  rw [e1, e2 (supportGen s a).card, ← hcomb]
  congr 1
  rw [hker]
  omega

end Qatlib.Papers.IQPBornShen26.MainResults.UniformVariance
