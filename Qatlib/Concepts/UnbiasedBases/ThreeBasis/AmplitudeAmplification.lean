/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.Register
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Amplitude Amplification and Phase Geometry

The marked projection `goodProj` and weight `goodProb` describe a finite coordinate event, while
`ampStep` composes its sign oracle with reflection about a reference state. The two-component
family `ampState` exposes the rotation underlying amplitude amplification: for a unit input with
marked probability `a` strictly between zero and one, `amplitude_amplification` gives the exact
success probability after any natural number of iterations, following [BrassardEtAl2002].

The phase vectors `eigenPlus` and `eigenMinus` diagonalize this rotation under the stated
orthonormality and support conditions. The analytic bounds also convert angle error into
amplitude error and control the average success over a finite range of iteration counts, as used
in randomized search [BoyerEtAl1998].

## Main statements

- `ampStep_iterate`: the angle after `j` steps is `(2j + 1)θ`.
* `amplitude_amplification_succeeds` and `amplification_query_bound`: the selected integer count
  achieves success at least `1 - a` and is at most `π / (4 sqrt a)`.
- `ampStep_eigenPlus` and `ampStep_eigenMinus`: the eigenvalues are `exp (±2θ * I)`.
* `amplitude_estimation_error`: an angular error of at most `ε` gives amplitude error at most `2
  sqrt (a(1 - a)) ε + ε²`.
* `qsearch_average`: a sufficiently long range of iteration counts has total success probability
  at least one quarter of its length.

## References

- [Brassard et al., 2002][BrassardEtAl2002]
- [Boyer et al., 1998][BoyerEtAl1998]
-/

section

open scoped ComplexConjugate

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restrict the amplitudes of `ψ` to the marked index set `G`, replacing all coordinates
outside `G` by zero. -/
noncomputable def goodProj (G : Finset ι) (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  (WithLp.equiv 2 (ι → ℂ)).symm (fun i => if i ∈ G then ψ i else 0)

omit [Fintype ι] in

/-- The marked projection retains coordinate `i` when `i ∈ G` and returns zero otherwise. -/
@[simp] lemma goodProj_apply (G : Finset ι) (ψ : EuclideanSpace ℂ ι) (i : ι) :
    goodProj G ψ i = if i ∈ G then ψ i else 0 := rfl

/-- Define the total squared amplitude on the marked set `G` as the sum of `‖ψ i‖^2` over its
indices. For a unit vector this is the probability of observing a marked outcome. -/
noncomputable def goodProb (G : Finset ι) (ψ : EuclideanSpace ℂ ι) : ℝ := ∑ i ∈ G, ‖ψ i‖ ^ 2

omit [Fintype ι] [DecidableEq ι] in

/-- The total squared amplitude on any marked set is nonnegative. -/
lemma goodProb_nonneg (G : Finset ι) (ψ : EuclideanSpace ℂ ι) : 0 ≤ goodProb G ψ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [Fintype ι] [DecidableEq ι] in

/-- Express the marked weight as the sum of the individual coordinate weights `prob ψ i` over
`G`. -/
lemma goodProb_eq_sum_prob (G : Finset ι) (ψ : EuclideanSpace ℂ ι) :
    goodProb G ψ = ∑ i ∈ G, prob ψ i := rfl

/-- Apply the marked sign flip `ψ - 2 • goodProj G ψ`, negating marked coordinates and retaining
the others. -/
noncomputable def oracleFlip (G : Finset ι) (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  ψ - (2 : ℂ) • goodProj G ψ

omit [Fintype ι] in

/-- Compute each coordinate of the marked sign flip as `ψ i` minus twice its marked projection. -/
lemma oracleFlip_apply (G : Finset ι) (ψ : EuclideanSpace ℂ ι) (i : ι) :
    oracleFlip G ψ i = ψ i - 2 * (if i ∈ G then ψ i else 0) := by
  rw [oracleFlip, WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul, Pi.smul_apply,
    goodProj_apply, smul_eq_mul]

/-- Define the map sending `ψ` to `2 * inner ℂ φ ψ • φ - ψ`. When `φ` has unit norm, this is
reflection about its complex span. -/
noncomputable def reflect (φ ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  (2 * inner ℂ φ ψ) • φ - ψ

/-- Compose the marked sign flip with the reflection map about `φ` to form one
amplitude-amplification step. -/
noncomputable def ampStep (φ : EuclideanSpace ℂ ι) (G : Finset ι)
    (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  reflect φ (oracleFlip G ψ)

/-- Form the two-component state `sin γ • g + cos γ • b`. The definition imposes no
normalization or support conditions on `g` and `b`. -/
noncomputable def ampState (g b : EuclideanSpace ℂ ι) (γ : ℝ) : EuclideanSpace ℂ ι :=
  (Real.sin γ : ℂ) • g + (Real.cos γ : ℂ) • b

omit [Fintype ι] [DecidableEq ι] in

/-- Evaluate the sine-weighted good component and cosine-weighted bad component at a single
coordinate. -/
lemma ampState_apply (g b : EuclideanSpace ℂ ι) (γ : ℝ) (i : ι) :
    ampState g b γ i = (Real.sin γ : ℂ) * g i + (Real.cos γ : ℂ) * b i := by
  rw [ampState, WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul, WithLp.ofLp_smul,
    Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]

omit [Fintype ι] in

/-- If `g` is supported on `G` and `b` vanishes on `G`, the marked projection of `ampState g b
γ` is exactly `sin γ • g`. -/
lemma goodProj_ampState {G : Finset ι} {g b : EuclideanSpace ℂ ι}
    (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0) (γ : ℝ) :
    goodProj G (ampState g b γ) = (Real.sin γ : ℂ) • g := by
  ext i
  rw [goodProj_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i ∈ G
  · rw [if_pos hi, ampState_apply, hbsupp i hi, mul_zero, add_zero]
  · rw [if_neg hi, hgsupp i hi, mul_zero]

omit [Fintype ι] in

/-- For components supported respectively on and off `G`, the marked sign flip sends the angle
parameter `γ` to `-γ`. -/
lemma oracleFlip_ampState {G : Finset ι} {g b : EuclideanSpace ℂ ι}
    (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0) (γ : ℝ) :
    oracleFlip G (ampState g b γ) = ampState g b (-γ) := by
  rw [oracleFlip, goodProj_ampState hgsupp hbsupp, ampState, ampState,
    Real.sin_neg, Real.cos_neg]
  push_cast
  module

omit [DecidableEq ι] in

/-- For orthonormal components `g` and `b`, the inner product of the states at angles `θ` and
`δ` is the complex cast of `cos (θ - δ)`. -/
lemma inner_ampState {g b : EuclideanSpace ℂ ι}
    (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1) (hgb : inner ℂ g b = 0) (θ δ : ℝ) :
    inner ℂ (ampState g b θ) (ampState g b δ) = (Real.cos (θ - δ) : ℂ) := by
  have hbg : inner ℂ b g = 0 := by
    rw [← inner_conj_symm, hgb, map_zero]
  rw [ampState, ampState]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hgg, hbb, hgb, hbg, Complex.conj_ofReal, mul_zero, mul_one]
  push_cast [Real.cos_sub]
  ring

/-- Rewrite the sine coefficient produced by reflection, `2 cos(θ - δ) sin θ - sin δ`, as
`sin(2θ - δ)`. -/
lemma two_cos_sub_mul_sin (θ δ : ℝ) :
    2 * Real.cos (θ - δ) * Real.sin θ - Real.sin δ = Real.sin (2 * θ - δ) := by
  rw [show 2 * θ - δ = θ + (θ - δ) from by ring, Real.sin_add, Real.sin_sub, Real.cos_sub]
  linear_combination Real.sin δ * Real.sin_sq_add_cos_sq θ

/-- Rewrite the cosine coefficient produced by reflection, `2 cos(θ - δ) cos θ - cos δ`, as
`cos(2θ - δ)`. -/
lemma two_cos_sub_mul_cos (θ δ : ℝ) :
    2 * Real.cos (θ - δ) * Real.cos θ - Real.cos δ = Real.cos (2 * θ - δ) := by
  rw [show 2 * θ - δ = θ + (θ - δ) from by ring, Real.cos_add, Real.sin_sub, Real.cos_sub]
  linear_combination Real.cos δ * Real.sin_sq_add_cos_sq θ

omit [DecidableEq ι] in

/-- For orthonormal `g` and `b`, reflecting the state at angle `δ` about the state at angle `θ`
produces the state at angle `2θ - δ`. -/
lemma reflect_ampState {g b : EuclideanSpace ℂ ι}
    (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1) (hgb : inner ℂ g b = 0) (θ δ : ℝ) :
    reflect (ampState g b θ) (ampState g b δ) = ampState g b (2 * θ - δ) := by
  rw [reflect, inner_ampState hgg hbb hgb]
  rw [ampState, ampState, ampState, ← two_cos_sub_mul_sin θ δ, ← two_cos_sub_mul_cos θ δ]
  push_cast
  module

/-- For orthonormal components supported on and off `G`, one amplification step about the state
at angle `θ` increases the input angle `γ` by `2θ`, as in [BrassardEtAl2002]. -/
theorem ampStep_ampState {G : Finset ι} {g b : EuclideanSpace ℂ ι}
    (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1) (hgb : inner ℂ g b = 0)
    (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0) (θ γ : ℝ) :
    ampStep (ampState g b θ) G (ampState g b γ) = ampState g b (γ + 2 * θ) := by
  rw [ampStep, oracleFlip_ampState hgsupp hbsupp, reflect_ampState hgg hbb hgb θ (-γ),
    show 2 * θ - -γ = γ + 2 * θ from by ring]

/-- For orthonormal marked and unmarked components, `j` amplification steps starting at angle
`θ` produce angle `(2j + 1)θ`, the rotation formula of [BrassardEtAl2002]. -/
theorem ampStep_iterate {G : Finset ι} {g b : EuclideanSpace ℂ ι}
    (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1) (hgb : inner ℂ g b = 0)
    (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0) (θ : ℝ) (j : ℕ) :
    (ampStep (ampState g b θ) G)^[j] (ampState g b θ)
      = ampState g b ((2 * j + 1) * θ) := by
  induction j with
  | zero =>
    rw [Function.iterate_zero_apply,
      show ((2 * (0 : ℕ) + 1) : ℝ) * θ = θ from by push_cast; ring]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ampStep_ampState hgg hbb hgb hgsupp hbsupp]
    congr 1
    push_cast
    ring

omit [Fintype ι] [DecidableEq ι] in

/-- If `b` vanishes on `G` and the squared amplitudes of `g` sum to one on `G`, the marked
weight of the state at angle `γ` is `sin γ ^ 2`. -/
lemma goodProb_ampState {G : Finset ι} {g b : EuclideanSpace ℂ ι}
    (hbsupp : ∀ i ∈ G, b i = 0) (hgood : ∑ i ∈ G, ‖g i‖ ^ 2 = 1) (γ : ℝ) :
    goodProb G (ampState g b γ) = Real.sin γ ^ 2 := by
  rw [goodProb]
  have hterm : ∀ i ∈ G, ‖ampState g b γ i‖ ^ 2 = Real.sin γ ^ 2 * ‖g i‖ ^ 2 := by
    intro i hi
    rw [ampState_apply, hbsupp i hi, mul_zero, add_zero, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hgood, mul_one]

/-- Scale the marked projection of `ψ` by the reciprocal of the complex cast of `sqrt (goodProb
G ψ)`. Positive marked weight makes this component a unit vector. -/
noncomputable def goodUnit (G : Finset ι) (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  (Real.sqrt (goodProb G ψ) : ℂ)⁻¹ • goodProj G ψ

/-- Scale the complementary component `ψ - goodProj G ψ` by the reciprocal of the complex cast
of `sqrt (1 - goodProb G ψ)`. For a unit input with marked weight below one, this is the
normalized unmarked component. -/
noncomputable def badUnit (G : Finset ι) (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  (Real.sqrt (1 - goodProb G ψ) : ℂ)⁻¹ • (ψ - goodProj G ψ)

omit [Fintype ι] in

/-- Compute a coordinate of the scaled marked component by multiplying the marked amplitude by
the reciprocal square root of the marked weight. -/
lemma goodUnit_apply (G : Finset ι) (ψ : EuclideanSpace ℂ ι) (i : ι) :
    goodUnit G ψ i = (Real.sqrt (goodProb G ψ) : ℂ)⁻¹ * (if i ∈ G then ψ i else 0) := by
  rw [goodUnit, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, goodProj_apply]

omit [Fintype ι] in

/-- Compute a coordinate of the scaled unmarked component by multiplying the complementary
amplitude by the reciprocal square root of `1 - goodProb G ψ`. -/
lemma badUnit_apply (G : Finset ι) (ψ : EuclideanSpace ℂ ι) (i : ι) :
    badUnit G ψ i = (Real.sqrt (1 - goodProb G ψ) : ℂ)⁻¹
      * (ψ i - (if i ∈ G then ψ i else 0)) := by
  rw [badUnit, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_sub, Pi.sub_apply,
    goodProj_apply]

omit [Fintype ι] in

/-- The scaled marked component vanishes at every index outside `G`. -/
lemma goodUnit_supp (G : Finset ι) (ψ : EuclideanSpace ℂ ι) :
    ∀ i ∉ G, goodUnit G ψ i = 0 := by
  intro i hi
  rw [goodUnit_apply, if_neg hi, mul_zero]

omit [Fintype ι] in

/-- The scaled unmarked component vanishes at every index in `G`. -/
lemma badUnit_supp (G : Finset ι) (ψ : EuclideanSpace ℂ ι) :
    ∀ i ∈ G, badUnit G ψ i = 0 := by
  intro i hi
  rw [badUnit_apply, if_pos hi, sub_self, mul_zero]

section Decomposition

variable {G : Finset ι} {ψ : EuclideanSpace ℂ ι}

omit [Fintype ι] [DecidableEq ι] in

/-- Positive marked weight gives a nonzero complex cast of its real square root. -/
private lemma sqrt_goodProb_ne (ha0 : 0 < goodProb G ψ) :
    ((Real.sqrt (goodProb G ψ) : ℝ) : ℂ) ≠ 0 := by
  rw [ne_eq, Complex.ofReal_eq_zero]
  exact (Real.sqrt_pos.mpr ha0).ne'

omit [Fintype ι] [DecidableEq ι] in

/-- Marked weight strictly below one gives a nonzero complex cast of the square root of its
complement. -/
private lemma sqrt_badProb_ne (ha1 : goodProb G ψ < 1) :
    ((Real.sqrt (1 - goodProb G ψ) : ℝ) : ℂ) ≠ 0 := by
  rw [ne_eq, Complex.ofReal_eq_zero]
  exact (Real.sqrt_pos.mpr (by linarith)).ne'

omit [Fintype ι] in

/-- When the marked weight is positive, the squared amplitudes of `goodUnit G ψ` sum to one over
`G`. -/
lemma goodUnit_weight (ha0 : 0 < goodProb G ψ) :
    ∑ i ∈ G, ‖goodUnit G ψ i‖ ^ 2 = 1 := by
  have hterm : ∀ i ∈ G, ‖goodUnit G ψ i‖ ^ 2 = (goodProb G ψ)⁻¹ * ‖ψ i‖ ^ 2 := by
    intro i hi
    rw [goodUnit_apply, if_pos hi, norm_mul, mul_pow, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (goodProb_nonneg G ψ)]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  exact inv_mul_cancel₀ ha0.ne'

/-- Positive marked weight makes the self-inner-product of the scaled marked component equal to
one. -/
lemma inner_goodUnit_self (ha0 : 0 < goodProb G ψ) :
    inner ℂ (goodUnit G ψ) (goodUnit G ψ) = 1 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply', RCLike.conj_mul]
  norm_cast
  have hfull : ∑ i : ι, ‖goodUnit G ψ i‖ ^ 2 = ∑ i ∈ G, ‖goodUnit G ψ i‖ ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ G) (fun i _ hi => by
      rw [goodUnit_supp G ψ i hi, norm_zero]; norm_num)).symm
  rw [hfull, goodUnit_weight ha0]
  norm_num

/-- For a unit input whose marked weight is below one, the scaled unmarked component has
self-inner-product one. -/
lemma inner_badUnit_self (hψ : ‖ψ‖ = 1) (ha1 : goodProb G ψ < 1) :
    inner ℂ (badUnit G ψ) (badUnit G ψ) = 1 := by
  have hane : (1 : ℝ) - goodProb G ψ ≠ 0 := by linarith
  have hoff : ∑ i ∈ Gᶜ, ‖ψ i‖ ^ 2 = 1 - goodProb G ψ := by
    have htot : ∑ i, ‖ψ i‖ ^ 2 = 1 := by
      have h := normSq_eq_sum_prob ψ
      rw [hψ, one_pow] at h
      simpa [prob] using h.symm
    have hsplit := Finset.sum_add_sum_compl G (fun i => ‖ψ i‖ ^ 2)
    rw [htot] at hsplit
    rw [goodProb]
    linarith [hsplit]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply', RCLike.conj_mul]
  norm_cast
  have hfull : ∑ i : ι, ‖badUnit G ψ i‖ ^ 2 = ∑ i ∈ Gᶜ, ‖badUnit G ψ i‖ ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ Gᶜ) (fun i _ hi => by
      rw [badUnit_supp G ψ i (by simpa using hi), norm_zero]; norm_num)).symm
  have hterm : ∀ i ∈ Gᶜ, ‖badUnit G ψ i‖ ^ 2
      = (1 - goodProb G ψ)⁻¹ * ‖ψ i‖ ^ 2 := by
    intro i hi
    have hiG : i ∉ G := by simpa using hi
    rw [badUnit_apply, if_neg hiG, sub_zero, norm_mul, mul_pow, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - goodProb G ψ)]
  have hsum2 : ∑ i ∈ Gᶜ, ‖badUnit G ψ i‖ ^ 2
      = (1 - goodProb G ψ)⁻¹ * ∑ i ∈ Gᶜ, ‖ψ i‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  rw [hfull, hsum2, hoff, inv_mul_cancel₀ hane]
  norm_num

/-- The scaled marked and unmarked components are orthogonal because their supports are
disjoint. -/
lemma inner_goodUnit_badUnit :
    inner ℂ (goodUnit G ψ) (badUnit G ψ) = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i ∈ G
  · rw [RCLike.inner_apply', badUnit_supp G ψ i hi, mul_zero]
  · rw [RCLike.inner_apply', goodUnit_supp G ψ i hi, map_zero, zero_mul]

omit [Fintype ι] in

/-- If the marked weight lies strictly between zero and one, reconstruct `ψ` from its scaled
marked and unmarked components at angle `arcsin (sqrt (goodProb G ψ))`. -/
lemma ampState_decomposition (ha0 : 0 < goodProb G ψ) (ha1 : goodProb G ψ < 1) :
    ψ = ampState (goodUnit G ψ) (badUnit G ψ)
        (Real.arcsin (Real.sqrt (goodProb G ψ))) := by
  have hs1 : Real.sqrt (goodProb G ψ) ≤ 1 := by
    calc Real.sqrt (goodProb G ψ) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt ha1.le
      _ = 1 := Real.sqrt_one
  have hsin : Real.sin (Real.arcsin (Real.sqrt (goodProb G ψ)))
      = Real.sqrt (goodProb G ψ) :=
    Real.sin_arcsin (le_trans (by norm_num : (-1:ℝ) ≤ 0) (Real.sqrt_nonneg _)) hs1
  have hcos : Real.cos (Real.arcsin (Real.sqrt (goodProb G ψ)))
      = Real.sqrt (1 - goodProb G ψ) := by
    rw [Real.cos_arcsin, Real.sq_sqrt (goodProb_nonneg G ψ)]
  rw [ampState, hsin, hcos, goodUnit, badUnit, smul_smul, smul_smul,
    mul_inv_cancel₀ (sqrt_goodProb_ne ha0), mul_inv_cancel₀ (sqrt_badProb_ne ha1),
    one_smul, one_smul, add_sub_cancel]

/-- For a unit input with initial marked probability `a` strictly between zero and one, `j`
amplification steps give marked probability `sin ((2j + 1) * arcsin (sqrt a)) ^ 2`
[BrassardEtAl2002]. -/
theorem amplitude_amplification (G : Finset ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (ha0 : 0 < goodProb G ψ) (ha1 : goodProb G ψ < 1) (j : ℕ) :
    goodProb G ((ampStep ψ G)^[j] ψ)
      = Real.sin ((2 * j + 1) * Real.arcsin (Real.sqrt (goodProb G ψ))) ^ 2 := by
  have hgg := inner_goodUnit_self (G := G) (ψ := ψ) ha0
  have hbb := inner_badUnit_self (G := G) (ψ := ψ) hψ ha1
  have hgb := inner_goodUnit_badUnit (G := G) (ψ := ψ)
  have hgs := goodUnit_supp G ψ
  have hbs := badUnit_supp G ψ
  have hdec := ampState_decomposition (G := G) (ψ := ψ) ha0 ha1
  calc goodProb G ((ampStep ψ G)^[j] ψ)
      = goodProb G ((ampStep (ampState (goodUnit G ψ) (badUnit G ψ)
            (Real.arcsin (Real.sqrt (goodProb G ψ)))) G)^[j]
          (ampState (goodUnit G ψ) (badUnit G ψ)
            (Real.arcsin (Real.sqrt (goodProb G ψ))))) := by rw [← hdec]
    _ = goodProb G (ampState (goodUnit G ψ) (badUnit G ψ)
          ((2 * j + 1) * Real.arcsin (Real.sqrt (goodProb G ψ)))) := by
        rw [ampStep_iterate hgg hbb hgb hgs hbs]
    _ = Real.sin ((2 * j + 1) * Real.arcsin (Real.sqrt (goodProb G ψ))) ^ 2 :=
        goodProb_ampState hbs (goodUnit_weight ha0) _

end Decomposition

section OptimalCount

variable {G : Finset ι} {ψ : EuclideanSpace ℂ ι}

/-- For a unit input with marked probability `a` in `(0, 1)`, using `floor (π / (4 * arcsin
(sqrt a)))` amplification steps achieves marked probability at least `1 - a`
[BrassardEtAl2002]. -/
theorem amplitude_amplification_succeeds (hψ : ‖ψ‖ = 1)
    (ha0 : 0 < goodProb G ψ) (ha1 : goodProb G ψ < 1) :
    1 - goodProb G ψ ≤ goodProb G
      ((ampStep ψ G)^[⌊Real.pi
          / (4 * Real.arcsin (Real.sqrt (goodProb G ψ)))⌋₊] ψ) := by
  set a := goodProb G ψ with ha
  set θ := Real.arcsin (Real.sqrt a) with hθdef
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr ha0)
  have hθhalf : θ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hsin : Real.sin θ = Real.sqrt a := by
    rw [hθdef]
    exact Real.sin_arcsin (le_trans (by norm_num) (Real.sqrt_nonneg a))
      (by calc Real.sqrt a ≤ Real.sqrt 1 := Real.sqrt_le_sqrt ha1.le
            _ = 1 := Real.sqrt_one)
  set m := ⌊Real.pi / (4 * θ)⌋₊ with hm
  rw [amplitude_amplification G ψ hψ ha0 ha1 m]
  set x := (2 * (m : ℝ) + 1) * θ with hx

  have hfl : (m : ℝ) ≤ Real.pi / (4 * θ) := Nat.floor_le (by positivity)
  have hfu : Real.pi / (4 * θ) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hwin : |Real.pi / 2 - x| ≤ θ := by
    rw [abs_le]
    constructor
    · have h1 : 2 * (m : ℝ) * θ ≤ Real.pi / 2 := by
        have := mul_le_mul_of_nonneg_right hfl (le_of_lt (by positivity : (0:ℝ) < 2 * θ))
        calc 2 * (m : ℝ) * θ = (m : ℝ) * (2 * θ) := by ring
          _ ≤ Real.pi / (4 * θ) * (2 * θ) := this
          _ = Real.pi / 2 := by field_simp; ring
      rw [hx]; nlinarith [h1]
    · have h2 : Real.pi / 2 < 2 * ((m : ℝ) + 1) * θ := by
        have := mul_lt_mul_of_pos_right hfu (by positivity : (0:ℝ) < 2 * θ)
        calc Real.pi / 2 = Real.pi / (4 * θ) * (2 * θ) := by field_simp; ring
          _ < ((m : ℝ) + 1) * (2 * θ) := this
          _ = 2 * ((m : ℝ) + 1) * θ := by ring
      rw [hx]; nlinarith [h2]

  have hsinx : Real.cos θ ≤ Real.sin x := by
    have h1 : Real.sin x = Real.cos (Real.pi / 2 - x) := (Real.cos_pi_div_two_sub x).symm
    have h2 : Real.cos (Real.pi / 2 - x) = Real.cos |Real.pi / 2 - x| :=
      (Real.cos_abs _).symm
    rw [h1, h2]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (le_trans hθhalf (by linarith [Real.pi_pos])) hwin

  have hcossq : Real.cos θ ^ 2 = 1 - a := by
    rw [Real.cos_sq', hsin, Real.sq_sqrt ha0.le]
  have hcos0 : 0 ≤ Real.cos θ := by
    rw [hθdef]; exact Real.cos_arcsin_nonneg _
  calc 1 - a = Real.cos θ ^ 2 := hcossq.symm
    _ ≤ Real.sin x ^ 2 := by nlinarith [hsinx, hcos0]

omit [Fintype ι] [DecidableEq ι] in

/-- For marked weight `a` in `(0, 1)`, the selected iteration count `floor (π / (4 * arcsin
(sqrt a)))` is at most `π / (4 * sqrt a)`, giving the inverse-square-root count bound of
[BrassardEtAl2002]. -/
theorem amplification_query_bound (ha0 : 0 < goodProb G ψ) (ha1 : goodProb G ψ < 1) :
    (⌊Real.pi / (4 * Real.arcsin (Real.sqrt (goodProb G ψ)))⌋₊ : ℝ)
      ≤ Real.pi / (4 * Real.sqrt (goodProb G ψ)) := by
  set a := goodProb G ψ
  set θ := Real.arcsin (Real.sqrt a) with hθdef
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr ha0)
  have hsin : Real.sin θ = Real.sqrt a := by
    rw [hθdef]
    exact Real.sin_arcsin (le_trans (by norm_num) (Real.sqrt_nonneg a))
      (by calc Real.sqrt a ≤ Real.sqrt 1 := Real.sqrt_le_sqrt ha1.le
            _ = 1 := Real.sqrt_one)
  have hle : Real.sqrt a ≤ θ := by
    rw [← hsin]
    exact Real.sin_le hθ0.le
  calc (⌊Real.pi / (4 * θ)⌋₊ : ℝ) ≤ Real.pi / (4 * θ) := Nat.floor_le (by positivity)
    _ ≤ Real.pi / (4 * Real.sqrt a) := by
        apply div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (by positivity)
        nlinarith [hle]

/-- A unit state with marked probability exactly `1/4` reaches marked probability one after a
single amplification step [BrassardEtAl2002]. -/
theorem amplification_quarter (hψ : ‖ψ‖ = 1) (ha : goodProb G ψ = 1 / 4) :
    goodProb G (ampStep ψ G ψ) = 1 := by
  have h := amplitude_amplification G ψ hψ (by rw [ha]; norm_num) (by rw [ha]; norm_num) 1
  rw [Function.iterate_one] at h
  rw [h, ha]
  have hsqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
  have harcsin : Real.arcsin (1 / 2 : ℝ) = Real.pi / 6 := by
    rw [← Real.sin_pi_div_six]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [hsqrt, harcsin,
    show (2 * (1 : ℕ) + 1) * (Real.pi / 6) = Real.pi / 2 from by push_cast; ring,
    Real.sin_pi_div_two, one_pow]

end OptimalCount

section EigenStructure

omit [Fintype ι] in

/-- The marked projection preserves addition of state vectors. -/
lemma goodProj_add (G : Finset ι) (ψ χ : EuclideanSpace ℂ ι) :
    goodProj G (ψ + χ) = goodProj G ψ + goodProj G χ := by
  ext i
  simp only [WithLp.ofLp_add, Pi.add_apply, goodProj_apply]
  split_ifs
  · rfl
  · norm_num

omit [Fintype ι] in

/-- The marked projection commutes with multiplication by any complex scalar. -/
lemma goodProj_smul (G : Finset ι) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    goodProj G (c • ψ) = c • goodProj G ψ := by
  ext i
  simp only [WithLp.ofLp_smul, Pi.smul_apply, goodProj_apply, smul_eq_mul]
  split_ifs
  · rfl
  · rw [mul_zero]

omit [Fintype ι] in

/-- The marked sign flip preserves addition of state vectors. -/
lemma oracleFlip_add (G : Finset ι) (ψ χ : EuclideanSpace ℂ ι) :
    oracleFlip G (ψ + χ) = oracleFlip G ψ + oracleFlip G χ := by
  rw [oracleFlip, oracleFlip, oracleFlip, goodProj_add]
  module

omit [Fintype ι] in

/-- The marked sign flip commutes with multiplication by any complex scalar. -/
lemma oracleFlip_smul (G : Finset ι) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    oracleFlip G (c • ψ) = c • oracleFlip G ψ := by
  rw [oracleFlip, oracleFlip, goodProj_smul]
  module

omit [DecidableEq ι] in

/-- For a fixed reference vector `φ`, the reflection map is additive in its input. -/
lemma reflect_add (φ ψ χ : EuclideanSpace ℂ ι) :
    reflect φ (ψ + χ) = reflect φ ψ + reflect φ χ := by
  rw [reflect, reflect, reflect, inner_add_right]
  module

omit [DecidableEq ι] in

/-- For a fixed reference vector `φ`, the reflection map commutes with complex scalar
multiplication in its input. -/
lemma reflect_smul (φ : EuclideanSpace ℂ ι) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    reflect φ (c • ψ) = c • reflect φ ψ := by
  rw [reflect, reflect, inner_smul_right]
  module

/-- For fixed reference vector and marked set, one amplification step preserves addition. -/
lemma ampStep_add (φ : EuclideanSpace ℂ ι) (G : Finset ι) (ψ χ : EuclideanSpace ℂ ι) :
    ampStep φ G (ψ + χ) = ampStep φ G ψ + ampStep φ G χ := by
  rw [ampStep, ampStep, ampStep, oracleFlip_add, reflect_add]

/-- For fixed reference vector and marked set, one amplification step commutes with complex
scalar multiplication. -/
lemma ampStep_smul (φ : EuclideanSpace ℂ ι) (G : Finset ι) (c : ℂ)
    (ψ : EuclideanSpace ℂ ι) :
    ampStep φ G (c • ψ) = c • ampStep φ G ψ := by
  rw [ampStep, ampStep, oracleFlip_smul, reflect_smul]

omit [Fintype ι] [DecidableEq ι] in

/-- The state at angle zero is exactly the component `b`. -/
lemma ampState_zero (g b : EuclideanSpace ℂ ι) : ampState g b 0 = b := by
  rw [ampState, Real.sin_zero, Real.cos_zero]
  push_cast
  module

omit [Fintype ι] [DecidableEq ι] in

/-- The state at angle `π/2` is exactly the component `g`. -/
lemma ampState_pi_div_two (g b : EuclideanSpace ℂ ι) :
    ampState g b (Real.pi / 2) = g := by
  rw [ampState, Real.sin_pi_div_two, Real.cos_pi_div_two]
  push_cast
  module

/-- Express the complex exponential of `x * I` as `cos x + sin x * I` for real `x`. -/
lemma exp_ofReal_mul_I (x : ℝ) :
    Complex.exp ((x : ℝ) * Complex.I)
      = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- Define the unnormalized vector `g + I • b`, used for the positive-phase eigenvalue of the
amplification step. -/
noncomputable def eigenPlus (g b : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  g + Complex.I • b

/-- Define the unnormalized vector `g - I • b`, used for the negative-phase eigenvalue of the
amplification step. -/
noncomputable def eigenMinus (g b : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  g - Complex.I • b

omit [Fintype ι] [DecidableEq ι] in

/-- The sum of the two phase vectors is twice `g`. -/
lemma eigenPlus_add_eigenMinus (g b : EuclideanSpace ℂ ι) :
    eigenPlus g b + eigenMinus g b = (2 : ℂ) • g := by
  rw [eigenPlus, eigenMinus]
  module

omit [Fintype ι] [DecidableEq ι] in

/-- The difference of the two phase vectors is `2 * I • b`. -/
lemma eigenPlus_sub_eigenMinus (g b : EuclideanSpace ℂ ι) :
    eigenPlus g b - eigenMinus g b = (2 * Complex.I) • b := by
  rw [eigenPlus, eigenMinus]
  module

variable {G : Finset ι} {g b : EuclideanSpace ℂ ι}

/-- For orthonormal marked and unmarked components, amplification about the state at angle `θ`
sends `g` to the state at angle `π/2 + 2θ`. -/
private lemma ampStep_g (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) :
    ampStep (ampState g b θ) G g = ampState g b (Real.pi / 2 + 2 * θ) := by
  have h := ampStep_ampState hgg hbb hgb hgsupp hbsupp θ (Real.pi / 2)
  rwa [ampState_pi_div_two] at h

/-- For orthonormal marked and unmarked components, amplification about the state at angle `θ`
sends `b` to the state at angle `2θ`. -/
private lemma ampStep_b (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) :
    ampStep (ampState g b θ) G b = ampState g b (2 * θ) := by
  have h := ampStep_ampState hgg hbb hgb hgsupp hbsupp θ 0
  rw [ampState_zero] at h
  rwa [zero_add] at h

/-- For orthonormal marked and unmarked components, `g + I • b` is an eigenvector of
amplification about the state at angle `θ`, with eigenvalue `exp (2θ * I)`
[BrassardEtAl2002]. -/
theorem ampStep_eigenPlus (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) :
    ampStep (ampState g b θ) G (eigenPlus g b)
      = Complex.exp ((2 * θ : ℝ) * Complex.I) • eigenPlus g b := by
  rw [eigenPlus, ampStep_add, ampStep_smul,
    ampStep_g hgg hbb hgb hgsupp hbsupp θ, ampStep_b hgg hbb hgb hgsupp hbsupp θ]
  have hsin : Real.sin (Real.pi / 2 + 2 * θ) = Real.cos (2 * θ) := by
    rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  have hcos : Real.cos (Real.pi / 2 + 2 * θ) = -Real.sin (2 * θ) := by
    rw [Real.cos_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  ext i
  simp only [WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    ampState_apply, hsin, hcos, exp_ofReal_mul_I, Complex.ofReal_neg]
  linear_combination (-(Real.sin (2 * θ) : ℂ) * b i) * Complex.I_mul_I

/-- For orthonormal marked and unmarked components, `g - I • b` is an eigenvector of
amplification about the state at angle `θ`, with eigenvalue `exp (-2θ * I)`
[BrassardEtAl2002]. -/
theorem ampStep_eigenMinus (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) :
    ampStep (ampState g b θ) G (eigenMinus g b)
      = Complex.exp ((-(2 * θ) : ℝ) * Complex.I) • eigenMinus g b := by
  rw [eigenMinus, sub_eq_add_neg, ← neg_smul, ampStep_add, ampStep_smul,
    ampStep_g hgg hbb hgb hgsupp hbsupp θ, ampStep_b hgg hbb hgb hgsupp hbsupp θ]
  have hsin : Real.sin (Real.pi / 2 + 2 * θ) = Real.cos (2 * θ) := by
    rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  have hcos : Real.cos (Real.pi / 2 + 2 * θ) = -Real.sin (2 * θ) := by
    rw [Real.cos_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  rw [show Complex.exp ((-(2 * θ) : ℝ) * Complex.I)
      = (Real.cos (2 * θ) : ℂ) - (Real.sin (2 * θ) : ℂ) * Complex.I from by
    rw [exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]; ring]
  ext i
  simp only [WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    ampState_apply, hsin, hcos, Complex.ofReal_neg]
  linear_combination (-(Real.sin (2 * θ) : ℂ) * b i) * Complex.I_mul_I

/-- Under the orthonormality and support assumptions, `j` amplification steps multiply
`eigenPlus g b` by `exp (2jθ * I)`. -/
theorem ampStep_iterate_eigenPlus (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) (j : ℕ) :
    (ampStep (ampState g b θ) G)^[j] (eigenPlus g b)
      = Complex.exp ((2 * j * θ : ℝ) * Complex.I) • eigenPlus g b := by
  induction j with
  | zero =>
    rw [Function.iterate_zero_apply,
      show ((2 * (0 : ℕ) * θ : ℝ)) = 0 from by push_cast; ring, Complex.ofReal_zero,
      zero_mul, Complex.exp_zero, one_smul]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ampStep_smul,
      ampStep_eigenPlus hgg hbb hgb hgsupp hbsupp θ, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- Under the orthonormality and support assumptions, `j` amplification steps multiply
`eigenMinus g b` by `exp (-2jθ * I)`. -/
theorem ampStep_iterate_eigenMinus (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) (hgsupp : ∀ i ∉ G, g i = 0) (hbsupp : ∀ i ∈ G, b i = 0)
    (θ : ℝ) (j : ℕ) :
    (ampStep (ampState g b θ) G)^[j] (eigenMinus g b)
      = Complex.exp ((-(2 * j * θ) : ℝ) * Complex.I) • eigenMinus g b := by
  induction j with
  | zero =>
    rw [Function.iterate_zero_apply,
      show ((-(2 * (0 : ℕ) * θ) : ℝ)) = 0 from by push_cast; ring, Complex.ofReal_zero,
      zero_mul, Complex.exp_zero, one_smul]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ampStep_smul,
      ampStep_eigenMinus hgg hbb hgb hgsupp hbsupp θ, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- Every natural iterate of an amplification step preserves addition. -/
lemma ampStep_iterate_add (φ : EuclideanSpace ℂ ι) (G : Finset ι) (j : ℕ)
    (ψ χ : EuclideanSpace ℂ ι) :
    (ampStep φ G)^[j] (ψ + χ) = (ampStep φ G)^[j] ψ + (ampStep φ G)^[j] χ := by
  induction j with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply,
      Function.iterate_zero_apply]
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, ampStep_add]

/-- Every natural iterate of an amplification step commutes with complex scalar multiplication. -/
lemma ampStep_iterate_smul (φ : EuclideanSpace ℂ ι) (G : Finset ι) (j : ℕ) (k : ℂ)
    (ψ : EuclideanSpace ℂ ι) :
    (ampStep φ G)^[j] (k • ψ) = k • (ampStep φ G)^[j] ψ := by
  induction j with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      ampStep_smul]

omit [Fintype ι] [DecidableEq ι] in

/-- Expand the state at angle `γ` in the phase vectors `g ± I • b`, with respective coefficients
`(-I/2) exp (γ * I)` and `(I/2) exp (-γ * I)`. -/
lemma ampState_eq_eigen (g b : EuclideanSpace ℂ ι) (γ : ℝ) :
    ampState g b γ
      = (-Complex.I / 2 * Complex.exp ((γ : ℝ) * Complex.I)) • eigenPlus g b
        + (Complex.I / 2 * Complex.exp ((-γ : ℝ) * Complex.I)) • eigenMinus g b := by
  rw [show Complex.exp ((-γ : ℝ) * Complex.I)
      = (Real.cos γ : ℂ) - (Real.sin γ : ℂ) * Complex.I from by
    rw [exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]; ring,
    exp_ofReal_mul_I]
  ext i
  simp only [eigenPlus, eigenMinus, ampState_apply, WithLp.ofLp_add, Pi.add_apply,
    WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  linear_combination ((Real.sin γ : ℂ) * g i + (Real.cos γ : ℂ) * b i) * Complex.I_mul_I

omit [DecidableEq ι] in

/-- If `g` and `b` are orthonormal, the phase vectors `g + I • b` and `g - I • b` are
orthogonal. -/
lemma inner_eigenPlus_eigenMinus (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) :
    inner ℂ (eigenPlus g b) (eigenMinus g b) = 0 := by
  have hbg : inner ℂ b g = 0 := by rw [← inner_conj_symm, hgb, map_zero]
  simp only [eigenPlus, eigenMinus, inner_add_left, inner_sub_right, inner_smul_left,
    inner_smul_right, hgg, hbb, hgb, hbg, Complex.conj_I]
  linear_combination Complex.I_mul_I

omit [DecidableEq ι] in

/-- For orthonormal `g` and `b`, the self-inner-product of `eigenPlus g b` is two. -/
lemma inner_eigenPlus_self (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) :
    inner ℂ (eigenPlus g b) (eigenPlus g b) = 2 := by
  have hbg : inner ℂ b g = 0 := by rw [← inner_conj_symm, hgb, map_zero]
  simp only [eigenPlus, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hgg, hbb, hgb, hbg, Complex.conj_I]
  linear_combination (-1 : ℂ) * Complex.I_mul_I

omit [DecidableEq ι] in

/-- For orthonormal `g` and `b`, the self-inner-product of `eigenMinus g b` is two. -/
lemma inner_eigenMinus_self (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) :
    inner ℂ (eigenMinus g b) (eigenMinus g b) = 2 := by
  have hbg : inner ℂ b g = 0 := by rw [← inner_conj_symm, hgb, map_zero]
  simp only [eigenMinus, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hgg, hbb, hgb, hbg, Complex.conj_I]
  linear_combination (-1 : ℂ) * Complex.I_mul_I

omit [DecidableEq ι] in

/-- For orthonormal `g` and `b`, the squared coordinate norms of `eigenPlus g b` sum to two. -/
lemma sum_sq_eigenPlus (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) :
    ∑ y, ‖eigenPlus g b y‖ ^ 2 = 2 := by
  have h : (inner ℂ (eigenPlus g b) (eigenPlus g b) : ℂ)
      = ((∑ y, ‖eigenPlus g b y‖ ^ 2 : ℝ) : ℂ) := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply', RCLike.conj_mul]
    norm_cast
  have h2 := h.symm.trans (inner_eigenPlus_self hgg hbb hgb)
  exact_mod_cast h2

omit [DecidableEq ι] in

/-- For orthonormal `g` and `b`, the squared coordinate norms of `eigenMinus g b` sum to two. -/
lemma sum_sq_eigenMinus (hgg : inner ℂ g g = 1) (hbb : inner ℂ b b = 1)
    (hgb : inner ℂ g b = 0) :
    ∑ y, ‖eigenMinus g b y‖ ^ 2 = 2 := by
  have h : (inner ℂ (eigenMinus g b) (eigenMinus g b) : ℂ)
      = ((∑ y, ‖eigenMinus g b y‖ ^ 2 : ℝ) : ℂ) := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply', RCLike.conj_mul]
    norm_cast
  have h2 := h.symm.trans (inner_eigenMinus_self hgg hbb hgb)
  exact_mod_cast h2

end EigenStructure

omit [Fintype ι] [DecidableEq ι] in

/-- Factor the difference `sin x ^ 2 - sin y ^ 2` as `sin (x + y) * sin (x - y)`. -/
lemma sin_sq_sub_sin_sq (x y : ℝ) :
    Real.sin x ^ 2 - Real.sin y ^ 2 = Real.sin (x + y) * Real.sin (x - y) := by
  rw [Real.sin_add, Real.sin_sub]
  linear_combination (-(Real.sin x ^ 2)) * Real.sin_sq_add_cos_sq y
    + (Real.sin y ^ 2) * Real.sin_sq_add_cos_sq x

omit [Fintype ι] [DecidableEq ι] in

/-- Bound the change in squared sine by `|sin (2y)| * |x - y| + |x - y|^2`, retaining its
dependence on the reference angle. -/
theorem abs_sin_sq_sub_sin_sq_le (x y : ℝ) :
    |Real.sin x ^ 2 - Real.sin y ^ 2| ≤ |Real.sin (2 * y)| * |x - y| + |x - y| ^ 2 := by
  rw [sin_sq_sub_sin_sq, abs_mul]
  have h1 : |Real.sin (x + y)| ≤ |Real.sin (2 * y)| + |x - y| := by
    have hlip := Real.abs_sin_sub_sin_le (x + y) (2 * y)
    rw [show x + y - 2 * y = x - y from by ring] at hlip
    have htri : |Real.sin (x + y)| - |Real.sin (2 * y)|
        ≤ |Real.sin (x + y) - Real.sin (2 * y)| := abs_sub_abs_le_abs_sub _ _
    linarith
  have h2 : |Real.sin (x - y)| ≤ |x - y| := Real.abs_sin_le_abs
  nlinarith [h1, h2, abs_nonneg (x - y), abs_nonneg (Real.sin (x + y))]

omit [Fintype ι] [DecidableEq ι] in

/-- If `sin θ = sqrt a`, `cos θ = sqrt (1 - a)`, and the angular error is at most `ε`, the
squared-sine estimate has error at most `2 * sqrt (a * (1 - a)) * ε + ε^2`
[BrassardEtAl2002]. -/
theorem amplitude_estimation_error {a : ℝ} (ha0 : 0 ≤ a)
    {θ θ' : ℝ} (hθ : Real.sin θ = Real.sqrt a) (hθc : Real.cos θ = Real.sqrt (1 - a))
    {ε : ℝ} (hδ : |θ' - θ| ≤ ε) :
    |Real.sin θ' ^ 2 - a| ≤ 2 * Real.sqrt (a * (1 - a)) * ε + ε ^ 2 := by
  have hsin2 : |Real.sin (2 * θ)| = 2 * Real.sqrt (a * (1 - a)) := by
    rw [Real.sin_two_mul, hθ, hθc, Real.sqrt_mul ha0,
      abs_of_nonneg (by positivity)]
    ring
  have ha' : Real.sin θ ^ 2 = a := by rw [hθ, Real.sq_sqrt ha0]
  have h := abs_sin_sq_sub_sin_sq_le θ' θ
  rw [ha', hsin2] at h
  have habs2 : |θ' - θ| ^ 2 ≤ ε ^ 2 := by nlinarith [abs_nonneg (θ' - θ)]
  have hmul : 2 * Real.sqrt (a * (1 - a)) * |θ' - θ|
      ≤ 2 * Real.sqrt (a * (1 - a)) * ε :=
    mul_le_mul_of_nonneg_left hδ (by positivity)
  linarith

omit [Fintype ι] [DecidableEq ι] in

/-- Express `cos (2t)` as `1 - 2 * sin t ^ 2`. -/
lemma cos_two_mul_odd (t : ℝ) :
    Real.cos (2 * t) = 1 - 2 * Real.sin t ^ 2 := by
  rw [Real.cos_two_mul]
  linear_combination 2 * Real.sin_sq_add_cos_sq t

omit [Fintype ι] [DecidableEq ι] in

/-- Evaluate the sum of the first `M` odd-angle squared sines after multiplication by `4 sin
(2θ)`, obtaining `2M sin (2θ) - sin (4Mθ)`. -/
lemma sum_sin_sq_odd_mul (θ : ℝ) (M : ℕ) :
    4 * Real.sin (2 * θ) * ∑ m ∈ Finset.range M, Real.sin ((2 * m + 1) * θ) ^ 2
      = 2 * M * Real.sin (2 * θ) - Real.sin (4 * M * θ) := by
  induction M with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have key : Real.sin (4 * ((k : ℝ) + 1) * θ) - Real.sin (4 * k * θ)
        = 2 * Real.sin (2 * θ) * (1 - 2 * Real.sin ((2 * k + 1) * θ) ^ 2) := by
      rw [show 4 * ((k : ℝ) + 1) * θ = 2 * ((2 * k + 1) * θ) + 2 * θ from by ring,
        show 4 * (k : ℝ) * θ = 2 * ((2 * k + 1) * θ) - 2 * θ from by ring,
        Real.sin_add, Real.sin_sub, cos_two_mul_odd ((2 * (k : ℝ) + 1) * θ)]
      ring
    push_cast
    linear_combination key

omit [Fintype ι] [DecidableEq ι] in

/-- If `sin (2θ)` is positive and `M sin (2θ) ≥ 1`, the sum of `sin ((2m + 1)θ)^2` for `m < M`
is at least `M/4`. -/
lemma sum_sin_sq_odd_ge (θ : ℝ) (M : ℕ) (hpos : 0 < Real.sin (2 * θ))
    (hM : 1 ≤ M * Real.sin (2 * θ)) :
    (M : ℝ) / 4 ≤ ∑ m ∈ Finset.range M, Real.sin ((2 * m + 1) * θ) ^ 2 := by
  have h := sum_sin_sq_odd_mul θ M
  have hb : Real.sin (4 * M * θ) ≤ 1 := Real.sin_le_one _
  nlinarith [h, hb, hM, hpos]

/-- For a unit input with marked probability `a` in `(0, 1)`, if `2M sqrt (a(1 - a)) ≥ 1`, the
first `M` amplification success probabilities sum to at least `M/4`. This gives the
constant-average-success estimate used in randomized quantum search [BoyerEtAl1998]. -/
theorem qsearch_average (G : Finset ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (ha0 : 0 < goodProb G ψ) (ha1 : goodProb G ψ < 1) (M : ℕ)
    (hM : 1 ≤ M * (2 * Real.sqrt (goodProb G ψ * (1 - goodProb G ψ)))) :
    (M : ℝ) / 4 ≤ ∑ m ∈ Finset.range M, goodProb G ((ampStep ψ G)^[m] ψ) := by
  set a := goodProb G ψ with ha
  set θ := Real.arcsin (Real.sqrt a) with hθdef
  have hterm : ∀ m : ℕ, goodProb G ((ampStep ψ G)^[m] ψ) = Real.sin ((2 * m + 1) * θ) ^ 2 :=
    fun m => amplitude_amplification G ψ hψ ha0 ha1 m
  rw [Finset.sum_congr rfl fun m _ => hterm m]
  have hsqle : Real.sqrt a ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ha1.le
  have hsθ : Real.sin θ = Real.sqrt a :=
    Real.sin_arcsin (le_trans (by norm_num) (Real.sqrt_nonneg a)) hsqle
  have hcθ : Real.cos θ = Real.sqrt (1 - a) := by
    rw [hθdef, Real.cos_arcsin, Real.sq_sqrt ha0.le]
  have hs2 : Real.sin (2 * θ) = 2 * Real.sqrt (a * (1 - a)) := by
    rw [Real.sin_two_mul, hsθ, hcθ, Real.sqrt_mul ha0.le]
    ring
  have hpos : 0 < Real.sin (2 * θ) := by
    rw [hs2]
    have h1a : 0 < a * (1 - a) := mul_pos ha0 (by linarith)
    have := Real.sqrt_pos.mpr h1a
    linarith
  refine sum_sin_sq_odd_ge θ M hpos ?_
  rw [hs2]
  exact hM

end Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo
