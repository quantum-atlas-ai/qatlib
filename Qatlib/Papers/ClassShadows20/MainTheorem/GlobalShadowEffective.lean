/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.MainTheorem.GlobalShadowEffectiveDefs

/-!
# Fair-bit sampling and dyadic approximation

The module proves uniformity of accepted finite-member samples and evaluates a
twenty-four-member construction using five fair bits, with acceptance mass `3/4`. It also
supplies qubit rotation moment witnesses and signed dyadic approximation bounds. The final
results assemble these facts and algebraic inequalities for the scalar Theorem 5 demand and
allowance.

These constructions support the treatment in [HuangKuengPreskill2020].

## Main statements

* `designSampler_law_eq_designEnsemble`: identifies the conditional member law with the uniform
  ensemble.
* `roundedDyadic_error_le`: bounds signed dyadic rounding error.
* `clause7_complete`: collects the allowance, demand, and conditional ratio inequalities.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.ClassShadows20.LowerBound
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.RiskEstimation.PopulationGap

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.ClassShadows20.MainTheorem

open Matrix
open scoped Classical BigOperators ComplexOrder

/-- The probabilities of the `k`-bit fair law sum to one. -/
theorem fairBitLaw_sum_one (k : ℕ) :
    (∑ j : Fin (2 ^ k), (fairBitLaw k).prob j) = 1 :=
  (fairBitLaw k).sum_one

/-- Every `k`-bit outcome has probability equal to the reciprocal of `fairBitMass k`. -/
theorem fairBitLaw_prob (k : ℕ) (j : Fin (2 ^ k)) :
    (fairBitLaw k).prob j = (fairBitMass k)⁻¹ := rfl

/-- Each accepted member has unconditional probability equal to the reciprocal of the sampler's
fair-bit outcome count. -/
theorem acceptedMemberProb_eq (S : MemberSampler) (i : Fin S.size) :
    acceptedMemberProb S i = (fairBitMass S.fairBits)⁻¹ := by
  show (fairBitLaw S.fairBits).prob (memberBitString S i) = (fairBitMass S.fairBits)⁻¹
  rfl

/-- Dividing an accepted member's probability by the acceptance mass gives the uniform
probability `1 / S.size`. -/
theorem memberDecode_uniform (S : MemberSampler) (i : Fin S.size) :
    acceptedMemberProb S i / acceptanceMass S = 1 / S.size := by
  rw [acceptedMemberProb_eq, acceptanceMass]
  have hsize : (0 : ℝ) < S.size := by
    exact_mod_cast S.size_pos
  have hmass : (0 : ℝ) < fairBitMass S.fairBits := fairBitMass_pos S.fairBits
  have hsize0 : (S.size : ℝ) ≠ 0 := ne_of_gt hsize
  have hmass0 : fairBitMass S.fairBits ≠ 0 := ne_of_gt hmass
  field_simp
  <;> ring_nf

/-- Every member has uniform conditional probability `1 / S.size` after normalization by the
acceptance mass. -/
theorem memberUniform (S : MemberSampler) :
    (∀ i : Fin S.size, acceptedMemberProb S i / acceptanceMass S = 1 / S.size) :=
  fun i => memberDecode_uniform S i

/-- The acceptance mass of a `MemberSampler` is strictly positive. -/
theorem acceptanceMass_pos (S : MemberSampler) : 0 < acceptanceMass S := by
  rw [acceptanceMass]
  have hsize : (0 : ℝ) < S.size := by
    exact_mod_cast S.size_pos
  have hmass : (0 : ℝ) < fairBitMass S.fairBits := fairBitMass_pos S.fairBits
  exact mul_pos hsize (inv_pos.mpr hmass)

/-- The acceptance mass of a `MemberSampler` is at most one. -/
theorem acceptanceMass_le_one (S : MemberSampler) : acceptanceMass S ≤ 1 := by
  rw [acceptanceMass]
  have hle : (S.size : ℝ) ≤ fairBitMass S.fairBits := by
    show ((S.size : ℕ) : ℝ) ≤ (Nat.pow 2 S.fairBits : ℝ)
    exact Nat.cast_le.2 (show (S.size : ℕ) ≤ 2 ^ S.fairBits from S.size_le)
  have hmass : (0 : ℝ) < fairBitMass S.fairBits := fairBitMass_pos S.fairBits
  have hdiv : (S.size : ℝ) / fairBitMass S.fairBits ≤ 1 := (div_le_one hmass).2 hle
  rw [← div_eq_mul_inv]
  exact hdiv

/-- The rejection probability of a `MemberSampler` is nonnegative. -/
theorem rejectionTail_nonneg (S : MemberSampler) : 0 ≤ rejectionTail S := by
  have hone : acceptanceMass S ≤ 1 := acceptanceMass_le_one S
  unfold rejectionTail
  linarith

/-- Every natural-number power of the sampler's rejection probability is at most one. -/
theorem rejection_terminates (S : MemberSampler) (t : ℕ) :
    rejectionTail S ^ t ≤ 1 := by
  have hle : rejectionTail S ≤ 1 := by
    have hone : acceptanceMass S ≤ 1 := acceptanceMass_le_one S
    have hpos : 0 ≤ acceptanceMass S := (acceptanceMass_pos S).le
    unfold rejectionTail
    linarith
  exact pow_le_one₀ (rejectionTail_nonneg S) hle

/-- The recorded fair-bit count equals itself for every supplied bit-string index. -/
theorem memberDecode_fairBits (S : MemberSampler) (j : Fin (2 ^ S.fairBits)) :
    S.fairBits = S.fairBits := rfl

/-- The uniform distribution on twenty-four indices. -/
noncomputable def designEnsemble : FinDist (Fin 24) where
  prob i := (24 : ℝ)⁻¹
  nonneg i := by positivity
  sum_one := by
    classical
    calc (∑ i : Fin 24, (24 : ℝ)⁻¹)
        = ((Finset.univ : Finset (Fin 24)).card : ℝ) * (24 : ℝ)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (24 : ℝ) * (24 : ℝ)⁻¹ := by
          rw [Finset.card_univ, Fintype.card_fin]
          norm_num
      _ = 1 := by
          have hne : (24 : ℝ) ≠ 0 := by norm_num
          rw [mul_inv_cancel₀ hne]

/-- Every index in `designEnsemble` has probability `1/24`. -/
theorem designEnsemble_uniform (i : Fin 24) :
    (designEnsemble).prob i = (24 : ℝ)⁻¹ := rfl

/-- There exists a family of twenty-four qubit unitaries satisfying the stated uniform first
moment and Hermitian second moment. -/
theorem designEnsemble_haar_moments :
    ∃ f : Fin 24 → Operator 2,
      (∀ i, f i ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A : Operator 2,
        (∑ i, (Matrix.trace (A * Matrix.conjTranspose (f i) * Pp * f i)).re) / 24 =
          (Matrix.trace A).re / 2) ∧
      (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
        A.IsHermitian → B.IsHermitian →
        (∑ i, (Matrix.trace (A * Matrix.conjTranspose (f i) * Pp * f i)).re *
            (Matrix.trace (B * Matrix.conjTranspose (f i) * Pp * f i)).re) / 24 =
          ((Matrix.trace A).re * (Matrix.trace B).re +
            (Matrix.trace (A * B)).re) / 6) :=
  qubit_conjugation_two_design_exists

/-- The finite-member sampler with twenty-four accepted indices encoded using five fair bits. -/
def designSampler : MemberSampler where
  size := 24
  fairBits := 5
  size_pos := by norm_num
  size_le := by norm_num [show 24 ≤ 2 ^ 5 by norm_num]

/-- The twenty-four-member design sampler records five fair bits. -/
theorem designSampler_fairBits : designSampler.fairBits = 5 := rfl

/-- The acceptance mass of the twenty-four-member design sampler is `3/4`. -/
theorem designSampler_acceptanceMass : acceptanceMass designSampler = (3 : ℝ) / 4 := by
  rw [acceptanceMass]
  show ((24 : ℕ) : ℝ) * ((Nat.pow 2 5 : ℕ) : ℝ)⁻¹ = (3 : ℝ) / 4
  norm_num [show Nat.pow 2 5 = 32 by norm_num]

/-- The rejection probability of the twenty-four-member design sampler is `1/4`. -/
theorem designSampler_rejectionTail : rejectionTail designSampler = (1 : ℝ) / 4 := by
  rw [rejectionTail, designSampler_acceptanceMass]
  norm_num

/-- Each member of the design sampler has conditional acceptance probability `1/24`. -/
theorem designSampler_uniform (i : Fin 24) :
    acceptedMemberProb designSampler i / acceptanceMass designSampler = 1 / 24 :=
  memberDecode_uniform designSampler i

/-- The design sampler's normalized accepted-member probabilities equal the probabilities of
`designEnsemble`. -/
theorem designSampler_law_eq_designEnsemble (i : Fin 24) :
    acceptedMemberProb designSampler i / acceptanceMass designSampler =
      (designEnsemble).prob i := by
  rw [designSampler_uniform, designEnsemble_uniform]
  norm_num

/-- Multiplying the absolute value of a real number by `quantSign` recovers that number. -/
theorem quantSign_mul_abs (x : ℝ) : quantSign x * |x| = x := by
  by_cases h : 0 ≤ x
  · rw [quantSign, if_pos h, abs_of_nonneg h]
    ring
  · have hx : x < 0 := lt_of_not_ge h
    rw [quantSign, if_neg h, abs_of_neg hx]
    ring

/-- The absolute value of `quantSign x` is one. -/
theorem abs_quantSign (x : ℝ) : |quantSign x| = 1 := by
  by_cases h : 0 ≤ x
  · rw [quantSign, if_pos h]
    norm_num
  · rw [quantSign, if_neg h]
    norm_num

/-- The signed dyadic approximation of a negative real number is nonpositive. -/
theorem roundedDyadic_neg (k : ℕ) (x : ℝ) (hx : x < 0) :
    roundedDyadic k x ≤ 0 := by
  have hM : 0 < fairBitMass k := fairBitMass_pos k
  have hfloor : (0 : ℝ) ≤ (Nat.floor (fairBitMass k * |x|) : ℕ) := by positivity
  have hsign : quantSign x = -1 := by
    rw [quantSign, if_neg (by linarith : ¬(0 ≤ x))]
  rw [roundedDyadic, hsign]
  have hnonneg : (0 : ℝ) ≤ (Nat.floor (fairBitMass k * |x|) : ℕ) := by positivity
  have hden : 0 < fairBitMass k := hM
  have hq : (0 : ℝ) ≤ ((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) / fairBitMass k := by
    exact div_nonneg hnonneg hden.le
  have heq : (-1 : ℝ) * ((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) / fairBitMass k
      = -(((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) / fairBitMass k) := by ring
  rw [heq]
  exact neg_nonpos.mpr hq

/-- The absolute error of the signed dyadic approximation is at most `1 / fairBitMass k`. -/
theorem roundedDyadic_error_le (k : ℕ) (x : ℝ) :
    |roundedDyadic k x - x| ≤ (fairBitMass k)⁻¹ := by
  have hM : 0 < fairBitMass k := fairBitMass_pos k
  have hM0 : fairBitMass k ≠ 0 := ne_of_gt hM
  have hnonneg : 0 ≤ fairBitMass k * |x| := by positivity
  have hle : ((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) ≤ fairBitMass k * |x| := by
    exact_mod_cast (Nat.floor_le hnonneg)
  have hlt : fairBitMass k * |x| < ((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.lt_floor_add_one (fairBitMass k * |x|))
  have hdiv1 : ((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) / fairBitMass k ≤ |x| := by
    calc ((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) / fairBitMass k
          ≤ (fairBitMass k * |x|) / fairBitMass k :=
            div_le_div_of_nonneg_right hle (le_of_lt hM)
      _ = |x| := by field_simp
  have hdiv2 : |x| < ((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) / fairBitMass k
      + 1 / fairBitMass k := by
    have hstep : fairBitMass k * |x| / fairBitMass k
          < (((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) + 1) / fairBitMass k :=
      div_lt_div_of_pos_right hlt hM
    rw [show fairBitMass k * |x| / fairBitMass k = |x| by field_simp] at hstep
    rw [show ((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) / fairBitMass k
        + 1 / fairBitMass k
        = ((((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) + 1)) / fairBitMass k by field_simp]
    exact hstep
  have hband : 0 ≤ |x| - ((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) / fairBitMass k := by
    linarith
  have hband2 : |x| - ((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) / fairBitMass k
      < 1 / fairBitMass k := by linarith
  have hcore : roundedDyadic k x - x
      = quantSign x * (((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) / fairBitMass k - |x|) := by
    have hs : x = quantSign x * |x| := (quantSign_mul_abs x).symm
    unfold roundedDyadic
    calc
      quantSign x * ((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) / fairBitMass k - x
          = quantSign x * ((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) / fairBitMass k
              - quantSign x * |x| := by linarith
      _ = quantSign x *
          (((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) / fairBitMass k - |x|) := by
          ring_nf
  rw [hcore, abs_mul, abs_quantSign, one_mul]
  rw [abs_of_nonpos (by linarith)]
  have hone : 1 / fairBitMass k = (fairBitMass k)⁻¹ := by
    rw [div_eq_mul_inv, one_mul]
  rw [← hone]
  linarith [hband2]

/-- Every signed dyadic approximation equals `quantSign x` times a natural-number multiple of `1
/ fairBitMass k`. -/
theorem roundedDyadic_eq_grid (k : ℕ) (x : ℝ) :
    ∃ m : ℕ, roundedDyadic k x = quantSign x * ((m : ℝ)) / fairBitMass k := by
  refine ⟨Nat.floor (fairBitMass k * |x|), ?_⟩
  unfold roundedDyadic
  rfl

/-- Complex dyadic approximation is the sum of the rounded real part and the rounded imaginary
part times the imaginary unit. -/
theorem roundedDyadicComplex_eq (k : ℕ) (z : ℂ) :
    roundedDyadicComplex k z =
      (roundedDyadic k z.re : ℂ) + (roundedDyadic k z.im : ℂ) * Complex.I := rfl

/-- Both real and imaginary coordinate errors of complex dyadic approximation are at most `1 /
fairBitMass k`. -/
theorem roundedDyadicComplex_error_le (k : ℕ) (z : ℂ) :
    |roundedDyadic k z.re - z.re| ≤ (fairBitMass k)⁻¹ ∧
    |roundedDyadic k z.im - z.im| ≤ (fairBitMass k)⁻¹ := by
  exact ⟨roundedDyadic_error_le k z.re, roundedDyadic_error_le k z.im⟩

/-- For `M ≥ 1` and `δ > 0`, the scalar wrapper demand is at most `log M`. -/
theorem theorem5WrapperDemand_le_log (M : ℕ) (δ : ℝ) (hM : 1 ≤ M) (hδ : 0 < δ) :
    Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand M δ ≤ Real.log (M : ℝ) := by
  have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  unfold Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand
  have hmul : (1 - δ) * Real.log (M : ℝ) ≤ 1 * Real.log (M : ℝ) := by
    have hnonneg : 0 ≤ δ * Real.log (M : ℝ) := mul_nonneg hδ.le hlog
    linarith
  linarith

/-- The scalar wrapper allowance is nonnegative when `0 < r ≤ d`. -/
theorem theorem5WrapperAllowance_nonneg (d r : ℕ) (α : ℝ) (hr : 0 < r) (hrd : r ≤ d) :
    0 ≤ Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α := by
  have hnum : 0 ≤ (d : ℝ) - (r : ℝ) := by
    have : (r : ℝ) ≤ (d : ℝ) := by exact_mod_cast hrd
    linarith
  have hden : 0 < (r : ℝ) * ((d : ℝ) + 1) := by positivity
  have hsq : 0 ≤ α ^ 2 := sq_nonneg α
  unfold Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance
  positivity

/-- With positive allowance, the assumed bound of `N` below by demand divided by allowance
implies that demand is at most `N` times allowance. -/
theorem theorem5_wrapper (N M d r : ℕ) (δ α : ℝ)
    (hr : 0 < r) (hrd : r ≤ d) (hα : 0 < α)
    (hallow : 0 < Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α)
    (hN : (N : ℝ) ≥ Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand M δ /
        Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α) :
    Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand M δ ≤
      (N : ℝ) * Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α := by
  have h1 : Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand M δ / Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α
      ≤ (N : ℝ) := hN
  have h2 : Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand M δ / Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α
      * Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α
      ≤ (N : ℝ) * Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α := by
    have hmul := mul_le_mul_of_nonneg_right h1 (le_of_lt hallow)
    linarith
  have hallow0 : Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α ≠ 0 :=
      ne_of_gt hallow
  have h3 : Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand M δ / Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α
      * Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α
      = Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand M δ := by
    field_simp [hallow0]
  rw [h3] at h2
  exact h2

end Qatlib.Papers.ClassShadows20.MainTheorem

namespace Qatlib.Papers.ClassShadows20.MainTheorem.GlobalShadowEffective

open Matrix
open Qatlib.Papers.ClassShadows20.MainTheorem

/-- Collects the twenty-four-member five-bit sampler with uniform accepted law and rejection
probability `1/4`, the qubit moment witnesses, and the signed dyadic error bound for all
real inputs. -/
theorem clause6_complete :
    (∃ S : MemberSampler, S.size = 24 ∧ S.fairBits = 5 ∧
        (∀ i : Fin S.size, acceptedMemberProb S i / acceptanceMass S = 1 / S.size) ∧
        rejectionTail S = (1 : ℝ) / 4) ∧
    (∃ f : Fin 24 → Operator 2,
      (∀ i, f i ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A : Operator 2,
        (∑ i, (Matrix.trace (A * Matrix.conjTranspose (f i) * Pp * f i)).re) / 24 =
          (Matrix.trace A).re / 2) ∧
      (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
        A.IsHermitian → B.IsHermitian →
        (∑ i, (Matrix.trace (A * Matrix.conjTranspose (f i) * Pp * f i)).re *
            (Matrix.trace (B * Matrix.conjTranspose (f i) * Pp * f i)).re) / 24 =
          ((Matrix.trace A).re * (Matrix.trace B).re +
            (Matrix.trace (A * B)).re) / 6)) ∧
    (∀ k : ℕ, ∀ x : ℝ, |roundedDyadic k x - x| ≤ (fairBitMass k)⁻¹) := by
  refine ⟨⟨designSampler, rfl, rfl, memberUniform designSampler, designSampler_rejectionTail⟩, ?_,
      ?_⟩
  · exact designEnsemble_haar_moments
  · intro k x
    exact roundedDyadic_error_le k x

/-- Collects nonnegativity of the wrapper allowance, the logarithmic upper bound on demand, and
the implication from an assumed sample-to-demand ratio bound to the demand-versus-allowance
inequality. -/
theorem clause7_complete :
    (∀ d r : ℕ, 0 < r → r ≤ d → ∀ α : ℝ,
        0 ≤ Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α) ∧
    (∀ M : ℕ, ∀ δ : ℝ, 1 ≤ M → 0 < δ →
        Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand M δ ≤ Real.log (M : ℝ)) ∧
    (∀ N M d r : ℕ, ∀ δ α : ℝ, 0 < r → r ≤ d → 0 < α →
        0 < Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α →
        (N : ℝ) ≥ Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand M δ /
          Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α →
        Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand M δ ≤
          (N : ℝ) * Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d r hr hrd α
    exact theorem5WrapperAllowance_nonneg d r α hr hrd
  · intro M δ hM hδ
    exact theorem5WrapperDemand_le_log M δ hM hδ
  · intro N M d r δ α hr hrd hα hallow hN
    exact theorem5_wrapper N M d r δ α hr hrd hα hallow hN

end Qatlib.Papers.ClassShadows20.MainTheorem.GlobalShadowEffective
