/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalWordConstructionDefs

/-!
# Public fixed-point word guarantees

This module assembles response, width, endpoint, resource, and nesting interfaces for the public
fixed-point word of [YoderLowChuang2014]. The general response theorem
`clause1_response_of_bridges` takes the two recurrence bridges explicitly, while the analytic
results provide a common successful length and bounds on its resource counts.

The module also transports the public word to a selected register fiber and develops the phase
and failure-amplitude identities for length three. Conditional output statements identify the
target direction without asserting a positive branch probability.

## Main statements

* `clause1_response_of_bridges`: the exact response from the recurrence bridges.
* `clause1_uniform_success`: a common length with a uniform response bound.
* `clause2_complete`: access bounds, phase approximation, and polynomial bounds.
* `clause3_nesting_semigroup`: response composition under length multiplication.
* `clause3_block_encoding_consumer`: the lifted word and its selected block.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Qatlib
open Matrix
open Polynomial
open Qatlib.Papers.FixedPtSearch14.FixedPoint

/-- The public word is the product of the public iterate list in reverse order. -/
theorem clause1_word_is_public (l : ℕ) (delta lam : ℝ) :
    publicWord l delta lam = (publicIterateList l delta lam).reverse.prod := by
  rfl

/-- Expands a public iterate into its source and target reflections. The scheduled phase
arguments depend on `l` and `delta`, while `lam` enters through the source reflection. -/
theorem clause1_good_mass_enters_only_through_the_axis (l : ℕ) (delta lam : ℝ) (i : ℕ) :
    publicIterate l delta lam i =
      -(stateReflection lam (wordPhase (2 * l + 1) (i + 1) (ylcGamma (2 * l + 1) delta)) *
        targetReflection (-wordPhase (2 * l + 1) (l - i) (ylcGamma (2 * l + 1) delta))) := by
  rfl

/-- Assuming both recurrence bridges, the public success probability is the degree-`2 * l + 1`
Chebyshev response, and the failure probability is the displayed squared Chebyshev amplitude
for valid probability parameters [YoderLowChuang2014]. -/
theorem clause1_response_of_bridges
    (hre : ylcBridgeRec_rearrangement) (hmi : ylcBridgeRec_miracle)
    (l : ℕ) (delta lam : ℝ) (hd : 0 < delta) (hd' : delta < 1) (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    publicSuccessProb l delta lam = responseProb (2 * l + 1) delta lam ∧
      publicFailureProb l delta lam =
        (delta * cheb (2 * l + 1) (Real.sqrt (1 - lam) / ylcGamma (2 * l + 1) delta)) ^ 2 := by
  have hmaster := ylc_master_response_of_bridges hre hmi l delta lam hd hd' hl hl'
  have hsucc : publicSuccessProb l delta lam = responseProb (2 * l + 1) delta lam := by
    unfold publicSuccessProb publicSuccessAmplitude
    rw [publicWord_eq]
    simpa only [ylcTargetVec] using! hmaster
  have hnorm : ‖publicFailureAmplitude l delta lam‖ ^ 2
      + ‖publicSuccessAmplitude l delta lam‖ ^ 2 = 1 := by
    have htwo := two_component_normSq (publicWord l delta lam *ᵥ ampState lam)
    have hψ : Normalized (publicWord l delta lam *ᵥ ampState lam) := by
      have hU := publicWord_unitary l delta lam hl hl'
      have hs := ampState_normalized hl hl'
      simpa [ApplyGate] using normalized_applyGate hU hs
    have hsum : (∑ i, ‖(publicWord l delta lam *ᵥ ampState lam) i‖ ^ 2) = 1 := hψ
    have h1 := htwo
    rw [hsum] at h1
    simpa [publicFailureAmplitude, publicSuccessAmplitude, add_comm] using h1
  have hresp : responseProb (2 * l + 1) delta lam =
      1 - (delta * cheb (2 * l + 1)
        (Real.sqrt (1 - lam) / ylcGamma (2 * l + 1) delta)) ^ 2 := responseProb_eq _ _ _
  have h1 : publicFailureProb l delta lam + publicSuccessProb l delta lam = 1 := by
    rw [publicFailureProb, publicSuccessProb]
    linarith [hnorm]
  have h2 : publicFailureProb l delta lam = 1 - publicSuccessProb l delta lam := by
    linarith [h1]
  refine ⟨hsucc, ?_⟩
  rw [h2, hsucc, hresp]
  ring

/-- For `0 < delta < 1` and `lam ∈ [0, 1]`, the zero-iterate success probability and length-one
response equal `lam`, and the failure probability is their complement. -/
theorem clause1_response_l0 (delta lam : ℝ) (hd : 0 < delta) (hd' : delta < 1)
    (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    publicSuccessProb 0 delta lam = responseProb 1 delta lam ∧
      publicFailureProb 0 delta lam = 1 - responseProb 1 delta lam ∧
        responseProb 1 delta lam = lam := by
  have hmain := ylcMainIdentity_l0 delta lam hd hd' hl hl'
  have hresp : responseProb 1 delta lam = lam := responseProb_one_eq hl hl' delta hd hd'
  have hsucc : publicSuccessProb 0 delta lam = responseProb 1 delta lam := by
    unfold publicSuccessProb publicSuccessAmplitude
    rw [publicWord_eq]
    simpa only [ylcTargetVec] using! hmain
  have hnorm : ‖publicFailureAmplitude 0 delta lam‖ ^ 2
      + ‖publicSuccessAmplitude 0 delta lam‖ ^ 2 = 1 := by
    have htwo := two_component_normSq (publicWord 0 delta lam *ᵥ ampState lam)
    have hψ : Normalized (publicWord 0 delta lam *ᵥ ampState lam) := by
      have hU := publicWord_unitary 0 delta lam hl hl'
      have hs := ampState_normalized hl hl'
      simpa [ApplyGate] using normalized_applyGate hU hs
    have hsum : (∑ i, ‖(publicWord 0 delta lam *ᵥ ampState lam) i‖ ^ 2) = 1 := hψ
    have h1 := htwo
    rw [hsum] at h1
    simpa [publicFailureAmplitude, publicSuccessAmplitude, add_comm] using h1
  have h1 : publicFailureProb 0 delta lam + publicSuccessProb 0 delta lam = 1 := by
    rw [publicFailureProb, publicSuccessProb]
    linarith [hnorm]
  refine ⟨hsucc, ?_, hresp⟩
  linarith [h1]

/-- For positive length and `0 < delta < 1`, the width lies in `(0, 1)` and its reciprocal has
Chebyshev value `1 / delta`. -/
theorem clause1_width_identity :
    ∀ (L : ℕ) (delta : ℝ), 0 < L → 0 < delta ∧ delta < 1 →
      0 < ylcGamma L delta ∧ ylcGamma L delta < 1 ∧
        cheb L (1 / ylcGamma L delta) = 1 / delta :=
  widthIdentity

/-- For `lam0, delta ∈ (0, 1)`, the public length is positive and odd and gives Chebyshev
response at least `1 - delta ^ 2` for every `lam ∈ [lam0, 1]` [YoderLowChuang2014]. -/
theorem clause1_uniform_success :
    ∀ (lam0 delta : ℝ), 0 < lam0 ∧ lam0 < 1 → 0 < delta ∧ delta < 1 →
      Odd (publicLength lam0 delta) ∧ 1 ≤ publicLength lam0 delta ∧
        ∀ lam, lam0 ≤ lam ∧ lam ≤ 1 →
          1 - delta ^ 2 ≤ responseProb (publicLength lam0 delta) delta lam :=
  unifiedChoice

/-- For positive odd length and `0 < delta < 1`, the Chebyshev response is zero at good mass
zero and one at good mass one. -/
theorem clause1_endpoints :
    ∀ (L : ℕ) (delta : ℝ), Odd L → 1 ≤ L → 0 < delta ∧ delta < 1 →
      responseProb L delta 0 = 0 ∧ responseProb L delta 1 = 1 :=
  responseEndpoints

/-- For `0 < delta < 1`, a unit lower bound on good mass selects public length one, whose
response is one for every `lam ≥ 1`. -/
theorem clause1_trivial_bound :
    ∀ (delta : ℝ), 0 < delta ∧ delta < 1 →
      publicLength 1 delta = 1 ∧ ∀ lam, 1 ≤ lam → responseProb 1 delta lam = 1 :=
  fun delta hd => ⟨ylcLength_one delta, responseProb_one_of_one_le delta hd.1 hd.2⟩

/-- A positive universal constant bounds the chosen public iterate count by `C * log (2 / delta)
/ √lam0`, uniformly for `lam0, delta ∈ (0, 1)` and `lam ∈ [lam0, 1]` [YoderLowChuang2014]. -/
theorem clause2_uniform_constant_before_good_mass :
    ∃ C : ℝ, 0 < C ∧
      ∀ (lam0 delta : ℝ), 0 < lam0 → lam0 < 1 → 0 < delta → delta < 1 →
        ∀ lam : ℝ, lam0 ≤ lam → lam ≤ 1 →
          ((publicIterateCount lam0 delta : ℕ) : ℝ) ≤
            C * Real.log (2 / delta) / Real.sqrt lam0 := by
  obtain ⟨C, hC, hbound⟩ := accessCountOBound
  refine ⟨C, hC, ?_⟩
  intro lam0 delta hl0 hl0' hd hd' lam _ _
  have h := hbound lam0 delta hl0 hl0' hd hd'
  simpa [publicIterateCount, publicLength] using h.1

/-- Packages the universal access-count bound, exact ledgers, phase counts, and dyadic
approximation at fixed or arbitrary precision. It also includes Chebyshev suppression and
degree bounds, the chosen-length inequality, and width monotonicity [YoderLowChuang2014]. -/
theorem clause2_complete :
    (∃ C : ℝ, 0 < C ∧
      ∀ (lam0 delta : ℝ), 0 < lam0 → lam0 < 1 → 0 < delta → delta < 1 →
        let L := publicLength lam0 delta
        let l := (L - 1) / 2
        let bound := C * Real.log (2 / delta) / Real.sqrt lam0
        (l : ℝ) ≤ bound ∧
          (publicPreparationCost l : ℝ) ≤ bound ∧
            (publicQueryCost l : ℝ) ≤ bound ∧
              (delta ≤ 1 / 2 → Real.log (2 / delta) ≤ 2 * Real.log (1 / delta))) ∧
    (∀ l : ℕ,
      publicPreparationCost l = l + l ∧ publicQueryCost l = 2 * l ∧
        publicQueryCost l + 1 = 2 * l + 1) ∧
    (∀ (l : ℕ) (delta : ℝ), 0 < delta → delta < 1 →
      (wordPhaseSequence l delta).length = 2 * l) ∧
    (∀ (b : ℕ) (theta : ℝ), 0 < b →
      ∃ q : ℤ, |theta - (2 * Real.pi * (q : ℝ)) / (2:ℝ) ^ b| ≤ Real.pi / (2:ℝ) ^ b) ∧
    (∀ (theta : ℝ) (eps : ℝ), 0 < eps →
      ∃ b : ℕ, 0 < b ∧ ∃ q : ℤ,
        |theta - (2 * Real.pi * (q : ℝ)) / (2:ℝ) ^ b| ≤ eps) ∧
    (∀ (L : ℕ) (delta : ℝ) (q : ℝ[X]) (a : ℝ),
      1 ≤ L → 0 < delta → delta < 1 → q.degree ≤ (L : ℕ) → q.eval 1 = 1 →
        0 < a → (∀ y ∈ Set.Icc (-a) a, |q.eval y| ≤ delta) → a ≤ ylcGamma L delta) ∧
    (∀ (L : ℕ) (lam0 delta : ℝ) (q : ℝ[X]),
      1 ≤ L → 0 < lam0 → lam0 < 1 → 0 < delta → delta < 1 →
        q.degree ≤ (L : ℕ) → q.eval 1 = 1 →
          (∀ y ∈ Set.Icc (-Real.sqrt (1 - lam0)) (Real.sqrt (1 - lam0)),
            |q.eval y| ≤ delta) →
          Real.arcosh (1 / delta) / (L : ℝ) ≤
            Real.arcosh (1 / Real.sqrt (1 - lam0))) ∧
    (∀ (lam0 delta : ℝ), 0 < lam0 → lam0 < 1 → 0 < delta → delta < 1 →
      Real.arcosh (1 / delta) / ((publicLength lam0 delta : ℝ)) ≤
        Real.arcosh (1 / Real.sqrt (1 - lam0))) ∧
    (∀ (L : ℕ) (delta : ℝ), 0 < L → 0 < delta → delta < 1 →
      ylcGamma L delta ≤ ylcGamma (L + 1) delta) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨C, hC, hbound⟩ := accessCountOBound
    refine ⟨C, hC, ?_⟩
    intro lam0 delta hl0 hl0' hd hd'
    have h := hbound lam0 delta hl0 hl0' hd hd'
    simpa [publicLength, publicPreparationCost, publicQueryCost] using h
  · intro l
    refine ⟨?_, rfl, rfl⟩
    rw [publicPreparationCost_eq]
    ring
  · intro l delta _ _
    exact wordPhaseSequence_length l delta
  · exact fun b theta hb => phaseCompilation_surrogate b hb theta
  · exact phaseCompilation_attain
  · exact chebyshevOptimalSuppression
  · exact chebyshevDegreeLowerBound
  · intro lam0 delta hl0 hl0' hd hd'
    exact unifiedLengthMeetsLowerBound lam0 delta hl0 hl0' hd hd'
  · exact widthWidening

/-- The phase compilation cost is `2 * l * b`, and adding it to the public access cost gives `4
* l + 2 * l * b`. -/
theorem clause2_phase_compiler_is_separate (l b : ℕ) :
    phaseCompileCost l b = 2 * l * b ∧
      publicAccessCost l + phaseCompileCost l b = 4 * l + 2 * l * b := by
  refine ⟨rfl, ?_⟩
  rw [publicAccessCost_eq]
  simp [phaseCompileCost]

/-- For normalized source and target with zero good mass and `0 < delta < 1`, the full-register
word has zero success probability. -/
theorem clause3_zero_good_mass_fails :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (s T : QState I) (L : ℕ) (delta : ℝ),
      Normalized s → Normalized T → 0 < delta → delta < 1 →
        goodMass T s = 0 → fullSuccessProb s T L delta = 0 :=
  zeroMassFails

/-- The public query and preparation costs are additive in the iterate count. -/
theorem clause3_resource_transport :
    ∀ (l₁ l₂ : ℕ),
      publicQueryCost (l₁ + l₂) = publicQueryCost l₁ + publicQueryCost l₂ ∧
        publicPreparationCost (l₁ + l₂) =
          publicPreparationCost l₁ + publicPreparationCost l₂ := by
  intro l₁ l₂
  simp [publicQueryCost, publicPreparationCost, wordQueryCount_eq, wordPreparationCount_eq,
    mul_add]

/-- For positive lengths, `0 < delta < 1`, and `lam ∈ [0, 1]`, composing responses with the
prescribed inner error parameter gives the response of length `L1 * L2`
[YoderLowChuang2014]. -/
theorem clause3_nesting_semigroup :
    ∀ (L1 L2 : ℕ) (delta lam : ℝ), 1 ≤ L1 → 1 ≤ L2 → 0 < delta → delta < 1 →
      0 ≤ lam → lam ≤ 1 →
        responseProb L2 delta (responseProb L1 (ylcGamma L2 delta) lam) =
          responseProb (L1 * L2) delta lam :=
  nestedResponseIdentity

/-- The public conditional output is a complex scalar multiple of the two-level target vector. -/
theorem clause3_success_branch_direction (l : ℕ) (delta lam : ℝ) :
    ∃ c : ℂ, publicConditionalOutput l delta lam = c • ylcTargetVec :=
  ⟨(publicSuccessAmplitude l delta lam / (‖publicSuccessAmplitude l delta lam‖ : ℂ)),
    publicConditionalOutput_onTargetRay l delta lam⟩

/-- The target basis vector in the register fiber at `j₀`, extended by zero on every other
fiber. -/
noncomputable def fiberTarget {J : Type} [DecidableEq J] (j₀ : J) : QState (J × Fin 2) :=
  fun p => if p.1 = j₀ then ylcTargetVec p.2 else 0

/-- The block corner of the lifted public word at `j₀` is the original two-level word. Acting on
a tensor state supported at that fiber applies the word to its two-level factor. -/
theorem clause3_block_encoding_consumer {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) :
    BlockCorner (publicWordFiber j₀ l delta lam) j₀ = publicWord l delta lam ∧
      ∀ ψ : QState (Fin 2),
        publicWordFiber j₀ l delta lam *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket j₀) ψ =
          TensorState (Qatlib.Foundations.PureStateMath.Ket j₀) (publicWord l delta lam *ᵥ ψ) := by
  constructor
  · exact publicWordFiber_corner j₀ l delta lam
  · intro ψ
    exact publicWordFiber_apply j₀ l delta lam ψ

/-- The inner product of a vector with a tensor of a basis state and `ψ` equals the inner
product of that vector's selected fiber with `ψ`. -/
private theorem inner_tensorState_ket {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (a : I) (ψ : QState J) (v : QState (I × J)) :
    Qatlib.Foundations.PureStateMath.Inner v (TensorState (Qatlib.Foundations.PureStateMath.Ket a) ψ) = Qatlib.Foundations.PureStateMath.Inner (fun j => v (a, j)) ψ := by
  rw [inner_apply, inner_apply]
  simp only [Fintype.sum_prod_type, tensorState_apply, Qatlib.Foundations.PureStateMath.Ket]
  rw [Finset.sum_eq_single a]
  · simp
  · intro i _ hi
    rw [Finset.sum_eq_zero]
    intro j _
    simp [hi]
  · intro hcon
    exact absurd (Finset.mem_univ a) hcon

/-- The target-overlap probability of the lifted word on the selected fiber equals the public
two-level success probability. -/
theorem clause3_fiber_success_probability {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) :
    ‖Qatlib.Foundations.PureStateMath.Inner (fiberTarget j₀)
        (publicWordFiber j₀ l delta lam *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket j₀) (ampState lam))‖ ^ 2
      = publicSuccessProb l delta lam := by
  have hstate := publicWordFiber_apply j₀ l delta lam (ampState lam)
  have hinner : Qatlib.Foundations.PureStateMath.Inner (fiberTarget j₀)
      (publicWordFiber j₀ l delta lam *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket j₀) (ampState lam)) =
      Qatlib.Foundations.PureStateMath.Inner ylcTargetVec (publicWord l delta lam *ᵥ ampState lam) := by
    rw [hstate]
    have h := inner_tensorState_ket j₀ (publicWord l delta lam *ᵥ ampState lam) (fiberTarget j₀)
    have h2 : (fun j : Fin 2 => fiberTarget j₀ (j₀, j)) = ylcTargetVec := by
      funext j
      show (if j₀ = j₀ then ylcTargetVec j else 0) = ylcTargetVec j
      simp
    rw [h2] at h
    exact h
  rw [publicSuccessProb]
  have h2 : Qatlib.Foundations.PureStateMath.Inner (fiberTarget j₀)
      (publicWordFiber j₀ l delta lam *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket j₀) (ampState lam)) =
      publicSuccessAmplitude l delta lam := hinner
  rw [h2]

/-- The analytic source phase `ylcAlpha 3 1 (ylcGamma 3 delta)` for the length-three word. -/
noncomputable def l3Phase (delta : ℝ) : ℝ := ylcAlpha 3 1 (ylcGamma 3 delta)

/-- The square root `√(1 - (ylcGamma 3 delta) ^ 2)` associated with the length-three width. -/
noncomputable def l3HalfWidth (delta : ℝ) : ℝ := Real.sqrt (1 - (ylcGamma 3 delta) ^ 2)

/-- The complex phase `exp(-i * l3Phase delta)`. -/
noncomputable def l3PhaseUnit (delta : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (l3Phase delta : ℝ)))

/-- The cosine of the length-three phase equals the displayed rational expression in the square
of `l3HalfWidth delta`. -/
theorem l3_cos_identity (delta : ℝ) :
    Real.cos (l3Phase delta) =
      -((1 - 3 * (l3HalfWidth delta) ^ 2) / (1 + 3 * (l3HalfWidth delta) ^ 2)) := by
  rw [l3Phase, l3HalfWidth]
  have htan : Real.tan (2 * Real.pi * (1:ℕ) / (3:ℕ)) = -Real.sqrt 3 := by
    have h : 2 * Real.pi * (1:ℕ) / (3:ℕ) = Real.pi - Real.pi / 3 := by ring
    rw [h, Real.tan_pi_sub, Real.tan_pi_div_three]
  have hsq : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [ylcAlpha, htan]
  have han : (-Real.sqrt 3) * Real.sqrt (1 - (ylcGamma 3 delta) ^ 2) =
      -(Real.sqrt 3 * Real.sqrt (1 - (ylcGamma 3 delta) ^ 2)) := by ring
  rw [han]
  have harctan : Real.arctan (-(Real.sqrt 3 * Real.sqrt (1 - (ylcGamma 3 delta) ^ 2))) =
      -Real.arctan (Real.sqrt 3 * Real.sqrt (1 - (ylcGamma 3 delta) ^ 2)) := by
    rw [Real.arctan_neg]
  have hpi : 2 * (Real.pi / 2 -
      Real.arctan (-(Real.sqrt 3 * Real.sqrt (1 - (ylcGamma 3 delta) ^ 2)))) =
      2 * Real.arctan (Real.sqrt 3 * Real.sqrt (1 - (ylcGamma 3 delta) ^ 2)) + Real.pi := by
    rw [harctan]
    ring
  rw [hpi, Real.cos_add_pi]
  have hcos2 : Real.cos
      (2 * Real.arctan (Real.sqrt 3 * Real.sqrt (1 - (ylcGamma 3 delta) ^ 2))) =
      (1 - 3 * (Real.sqrt (1 - (ylcGamma 3 delta) ^ 2)) ^ 2) /
        (1 + 3 * (Real.sqrt (1 - (ylcGamma 3 delta) ^ 2)) ^ 2) := by
    rw [Real.cos_two_mul, Real.cos_arctan]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    have h3 : (Real.sqrt 3 * Real.sqrt (1 - (ylcGamma 3 delta) ^ 2)) ^ 2 =
        3 * (Real.sqrt (1 - (ylcGamma 3 delta) ^ 2)) ^ 2 := by
      rw [mul_pow, hsq]
    rw [h3]
    field_simp
    ring
  rw [hcos2]

/-- The degree-three Chebyshev polynomial evaluates to `4 * x ^ 3 - 3 * x`. -/
theorem cheb_three (x : ℝ) : cheb 3 x = 4 * x ^ 3 - 3 * x := by
  have h2 : Polynomial.Chebyshev.T ℝ (2:ℤ) = 2 * Polynomial.X ^ 2 - 1 := by
    rw [Polynomial.Chebyshev.T_eq]
    rw [show (2:ℤ) - 1 = (1:ℤ) by norm_num, show (2:ℤ) - 2 = (0:ℤ) by norm_num,
      Polynomial.Chebyshev.T_one, Polynomial.Chebyshev.T_zero]
    ring
  have h3 : Polynomial.Chebyshev.T ℝ ((3:ℕ) : ℤ) = 4 * Polynomial.X ^ 3 - 3 * Polynomial.X := by
    rw [Polynomial.Chebyshev.T_eq]
    rw [show ((3:ℕ) : ℤ) - 1 = (2:ℤ) by norm_num,
      show ((3:ℕ) : ℤ) - 2 = (1:ℤ) by norm_num, h2, Polynomial.Chebyshev.T_one]
    ring
  rw [cheb_eq, h3]
  simp

/-- For `lam ∈ [0, 1]`, the one-iterate public failure amplitude is the displayed expression in
the square-root amplitudes and `l3PhaseUnit delta`. -/
theorem l3_failure_amplitude (delta lam : ℝ) (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    publicFailureAmplitude 1 delta lam =
      -(((1 - (lam:ℂ)) * l3PhaseUnit delta + (lam:ℂ)) * ((Real.sqrt (1 - lam) : ℝ) : ℂ) +
        ((Real.sqrt (1 - lam) : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) * (l3PhaseUnit delta - 1) *
          (l3PhaseUnit delta * ((Real.sqrt lam : ℝ) : ℂ))) := by

  have hword : publicWord 1 delta lam =
      -(stateReflection lam (l3Phase delta) * targetReflection (-(l3Phase delta))) := by
    have e : publicWord 1 delta lam = groverIterate lam (l3Phase delta) (-(l3Phase delta)) := by
      have hrange : List.range 1 = [0] := by simp [List.range_succ]
      rw [publicWord, hrange]
      simp [publicIterate, wordPhase, l3Phase]
    rw [e]
    rfl

  have hSs00 : stateReflection lam (l3Phase delta) 0 0 =
      (1 - (lam:ℂ)) * l3PhaseUnit delta + (lam:ℂ) := by
    rw [stateReflection_entry lam (l3Phase delta) hl hl']
    show ((1 - (lam:ℂ)) * Complex.exp (-(Complex.I * l3Phase delta)) + (lam:ℂ) : ℂ) =
      (1 - (lam:ℂ)) * l3PhaseUnit delta + (lam:ℂ)
    rfl
  have hSs01 : stateReflection lam (l3Phase delta) 0 1 =
      ((Real.sqrt (1 - lam) : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) * (l3PhaseUnit delta - 1) := by
    rw [stateReflection_entry lam (l3Phase delta) hl hl']
    show ((Real.sqrt (1 - lam) : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) *
        (Complex.exp (-(Complex.I * l3Phase delta)) - 1) =
      ((Real.sqrt (1 - lam) : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) * (l3PhaseUnit delta - 1)
    rfl
  have hSt00 : targetReflection (-(l3Phase delta)) 0 0 = 1 := by
    simp [targetReflection]
  have hSt01 : targetReflection (-(l3Phase delta)) 0 1 = 0 := by
    simp [targetReflection]
  have hSt10 : targetReflection (-(l3Phase delta)) 1 0 = 0 := by
    simp [targetReflection]
  have hAmp0 : ampState lam 0 = ((Real.sqrt (1 - lam) : ℝ) : ℂ) := by
    simp [ampState]
  have hAmp1 : ampState lam 1 = ((Real.sqrt lam : ℝ) : ℂ) := by
    simp [ampState]
  have hSt11 : targetReflection (-(l3Phase delta)) 1 1 = l3PhaseUnit delta := by
    simp [targetReflection]
    rfl

  have hval : (publicWord 1 delta lam *ᵥ ampState lam) 0 =
      -(((1 - (lam:ℂ)) * l3PhaseUnit delta + (lam:ℂ)) * ((Real.sqrt (1 - lam) : ℝ) : ℂ) +
        ((Real.sqrt (1 - lam) : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) * (l3PhaseUnit delta - 1) *
          (l3PhaseUnit delta * ((Real.sqrt lam : ℝ) : ℂ))) := by
    rw [hword, Matrix.neg_mulVec]
    congr 1
    rw [← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
    rw [hSs00, hSs01, hSt00, hSt01, hSt10, hSt11, hAmp0, hAmp1]
    ring

  have hamp : publicFailureAmplitude 1 delta lam =
      (publicWord 1 delta lam *ᵥ ampState lam) 0 := by
    show Qatlib.Foundations.PureStateMath.Inner ylcFailVec
        (publicWord 1 delta lam *ᵥ ampState lam) = _
    rw [inner_ylcFailVec]
  rw [hamp, hval]

end Qatlib.Papers.FixedPtSearch14.FixedPoint
