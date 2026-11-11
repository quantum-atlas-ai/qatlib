/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Amplified GEQAE gradient estimation (Corollary 1)

Source: "Quantum Deep Learning", arXiv:1412.3489v2, Corollary 1, pp.16-17
(eqs. C6-C11) and its proof.

When a lower bound `P_u` on the rejection-sampling success probability is known,
`m` rounds of amplitude amplification turn the success probability `P(1)` into

  `P_s = sin²((2m+1)·arcsin(√(P(1))))`   (eq. C6),

which can be inverted (principal branch, `(2m+1)arcsin(√P(1)) ≤ π/2`) to recover
`P(1) = sin²(arcsin(√P_s)/(2m+1))` (eq. C7). The proof of the corollary bounds the
error amplification of this inversion by `O(Δ₀/m²)` (eqs. C10-C11), yielding
`Õ((√κ + √max_v κ_v)/(δ/P_u))` queries and `Õ(E(√κ + √max_v κ_v)/(δ/P_u))`
operations.

We prove the exact invertibility identity (C6 → C7), the analytic derivative and
mean-value bounds (C8-C11), and the cost bookkeeping. The source's lower bound
`-P_s ≤ Δ₀` is explicit in the formal statement, so both probabilities lie in
`[0,1/4]` and the Mean-Value Theorem applies on their closed interval.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDeepLearn14.MainResults.AmplifiedGradient

/-- Grover amplification factor `2m+1`. -/
def groverFactor (m : ℕ) : ℝ := 2 * (m : ℝ) + 1

/-- Outcome probability after `m` rounds of amplitude amplification
(arXiv:1412.3489 eq. C6), given the base success probability `P1`. -/
def amplifiedProbability (m : ℕ) (P1 : ℝ) : ℝ :=
  Real.sin (groverFactor m * Real.arcsin (Real.sqrt P1)) ^ 2

/-- `2m+1 > 0`. -/
theorem groverFactor_pos (m : ℕ) : 0 < groverFactor m := by
  unfold groverFactor
  positivity

/-- `2m+1 ≥ 1`. -/
theorem one_le_groverFactor (m : ℕ) : 1 ≤ groverFactor m := by
  unfold groverFactor
  have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  linarith

/-- **Corollary 1 (invertibility, eqs. C6-C7)** of arXiv:1412.3489 p.16: on the
principal branch `(2m+1)·arcsin(√P1) ≤ π/2`, the amplified probability `P_s` of
eq. C6 can be inverted to recover the base probability `P1` exactly via eq. C7,
`P1 = sin²(arcsin(√P_s)/(2m+1))`. -/
theorem corollary1_amplificationInverse
    (m : ℕ) (P1 : ℝ) (hP10 : 0 ≤ P1) (hP11 : P1 ≤ 1)
    (hangle : groverFactor m * Real.arcsin (Real.sqrt P1) ≤ Real.pi / 2) :
    Real.sin
        (Real.arcsin (Real.sqrt (amplifiedProbability m P1)) / groverFactor m) ^ 2
      = P1 := by
  have hsqrt0 : 0 ≤ Real.sqrt P1 := Real.sqrt_nonneg P1
  have hsqrt1 : Real.sqrt P1 ≤ 1 := by
    nlinarith [Real.sq_sqrt hP10, hP11]
  set θ := Real.arcsin (Real.sqrt P1) with hθ
  have hsinθ : Real.sin θ = Real.sqrt P1 := by
    rw [hθ]
    exact Real.sin_arcsin (by linarith) hsqrt1
  have hsin2θ : Real.sin θ ^ 2 = P1 := by
    rw [hsinθ, Real.sq_sqrt hP10]
  have hθ0 : 0 ≤ θ := by
    rw [hθ]
    exact (Real.arcsin_nonneg).mpr hsqrt0
  have hgp : 0 < groverFactor m := groverFactor_pos m
  set x := groverFactor m * θ with hx
  have hx0 : 0 ≤ x := mul_nonneg (le_of_lt hgp) hθ0
  have hxpi : x ≤ Real.pi / 2 := hangle
  have hamp : amplifiedProbability m P1 = Real.sin x ^ 2 := by
    unfold amplifiedProbability
    rw [← hθ, ← hx]
  have hsqrtamp : Real.sqrt (amplifiedProbability m P1) = Real.sin x := by
    rw [hamp, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos, hxpi]))]
  have harc : Real.arcsin (Real.sin x) = x :=
    Real.arcsin_sin (by linarith) hxpi
  have harg : Real.arcsin (Real.sqrt (amplifiedProbability m P1)) / groverFactor m = θ := by
    rw [hsqrtamp, harc, hx]
    field_simp [hgp.ne']
  rw [harg, hsin2θ]

/-- Recovered base probability after inverting Grover amplification with
amplification factor `g` (eq. C7). -/
def recoveredProbability (g Ps : ℝ) : ℝ :=
  Real.sin (Real.arcsin (Real.sqrt Ps) / g) ^ 2

/-- The derivative of `recoveredProbability` on `0 < Ps < 1` (eq. C8). -/
def recoveredProbabilitySlope (g Ps : ℝ) : ℝ :=
  Real.sin (2 * (Real.arcsin (Real.sqrt Ps) / g)) /
    (2 * g * Real.sqrt Ps * Real.sqrt (1 - Ps))

/-- On `[0,1/4]`, concavity of sine on `[0,π/6]` gives the sharp secant bound
`arcsin √y ≤ (π/3)√y` used in eq. C10. -/
theorem arcsin_sqrt_le_pi_div_three_mul_sqrt
    {y : ℝ} (hy0 : 0 ≤ y) (hy14 : y ≤ 1 / 4) :
    Real.arcsin (Real.sqrt y) ≤ Real.pi / 3 * Real.sqrt y := by
  have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hs1 : Real.sqrt y ≤ 1 / 2 := by
    nlinarith [Real.sq_sqrt hy0]
  have hc := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    (show Real.pi / 6 ∈ Set.Icc 0 Real.pi from
      ⟨by positivity, by linarith [Real.pi_pos]⟩)
    (show 0 ≤ 1 - 2 * Real.sqrt y by linarith)
    (show 0 ≤ 2 * Real.sqrt y by positivity)
  have hsin : Real.sqrt y ≤ Real.sin (Real.pi / 3 * Real.sqrt y) := by
    convert hc using 1 <;> simp [Real.sin_pi_div_six, smul_eq_mul] <;> ring
  apply (Real.arcsin_le_iff_le_sin ?_ ?_).mpr hsin
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by nlinarith [Real.pi_pos, Real.sqrt_nonneg y], by nlinarith [Real.pi_pos]⟩

/-- The recovered probability is continuous on all of `ℝ`, including the
endpoints of the interval `[0,1/4]` where the closed-interval MVT is used. -/
theorem continuous_recoveredProbability (g : ℝ) :
    Continuous (recoveredProbability g) := by
  unfold recoveredProbability
  fun_prop

/-- Chain-rule formula for eq. C8 on `0 < Ps < 1`. -/
theorem hasDerivAt_recoveredProbability
    {g y : ℝ} (hg : g ≠ 0) (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt (recoveredProbability g) (recoveredProbabilitySlope g y) y := by
  have hsy0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hsy1 : Real.sqrt y < 1 := by nlinarith [Real.sq_sqrt hy0.le, hsy0]
  have hbase : HasDerivAt (fun p : ℝ => Real.arcsin (Real.sqrt p))
      (1 / Real.sqrt (1 - y) * (1 / (2 * Real.sqrt y))) y := by
    convert (Real.hasDerivAt_arcsin (by linarith) (ne_of_lt hsy1)).comp y
      (Real.hasDerivAt_sqrt hy0.ne') using 1 <;>
      first | rfl | simp [Function.comp, Real.sq_sqrt hy0.le]
  have hdiv := hbase.div_const g
  have hsin := hdiv.sin
  have hsq := hsin.pow 2
  unfold recoveredProbability recoveredProbabilitySlope
  convert hsq using 1
  rw [Real.sin_two_mul]
  field_simp [hg, (Real.sqrt_pos.mpr hy0).ne',
    (Real.sqrt_pos.mpr (sub_pos.mpr hy1)).ne']
  ring

/-- The derivative in eq. C8 is nonnegative on the source's interval. -/
theorem recoveredProbabilitySlope_nonneg
    {g y : ℝ} (hg : 1 ≤ g) (hy0 : 0 < y) (hy14 : y < 1 / 4) :
    0 ≤ recoveredProbabilitySlope g y := by
  have hg0 : 0 < g := by linarith
  have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hs1 : Real.sqrt y ≤ 1 / 2 := by
    nlinarith [Real.sq_sqrt hy0.le]
  have hθ0 : 0 ≤ Real.arcsin (Real.sqrt y) := Real.arcsin_nonneg.mpr hs0
  have hθle := arcsin_sqrt_le_pi_div_three_mul_sqrt hy0.le hy14.le
  have h2a0 : 0 ≤ 2 * (Real.arcsin (Real.sqrt y) / g) := by positivity
  have h2api : 2 * (Real.arcsin (Real.sqrt y) / g) ≤ Real.pi := by
    have hpi : Real.pi / 3 * Real.sqrt y ≤ Real.pi / 6 := by nlinarith [Real.pi_pos]
    have hdiv : Real.arcsin (Real.sqrt y) / g ≤ Real.pi / 6 := by
      apply (div_le_iff₀ hg0).mpr
      nlinarith
    linarith [Real.pi_pos]
  exact div_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi h2a0 h2api)
    (by positivity : 0 ≤ 2 * g * Real.sqrt y * Real.sqrt (1 - y))

/-- Sharp derivative bound `2π/(3√3·g²)` from eq. C10, valid for
`0 < y < 1/4` and amplification factor `g ≥ 1`. -/
theorem recoveredProbabilitySlope_le
    {g y : ℝ} (hg : 1 ≤ g) (hy0 : 0 < y) (hy14 : y < 1 / 4) :
    recoveredProbabilitySlope g y ≤ (2 * Real.pi / (3 * Real.sqrt 3)) / g ^ 2 := by
  have hg0 : 0 < g := by linarith
  have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hs1 : Real.sqrt (1 - y) > 0 := Real.sqrt_pos.mpr (by linarith)
  have hθ0 : 0 ≤ Real.arcsin (Real.sqrt y) := Real.arcsin_nonneg.mpr hs0.le
  have hθle := arcsin_sqrt_le_pi_div_three_mul_sqrt hy0.le hy14.le
  have h2a0 : 0 ≤ 2 * (Real.arcsin (Real.sqrt y) / g) := by positivity
  have ht : Real.sqrt 3 / 2 ≤ Real.sqrt (1 - y) := by
    rw [Real.le_sqrt (by positivity) (by linarith)]
    nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have hD : 0 < 2 * g * Real.sqrt y * Real.sqrt (1 - y) := by positivity
  have hD' : 0 < g ^ 2 * Real.sqrt y * Real.sqrt (1 - y) := by positivity
  have hT : 0 < 3 * g ^ 2 * (Real.sqrt 3 / 2) := by positivity
  unfold recoveredProbabilitySlope
  calc
    Real.sin (2 * (Real.arcsin (Real.sqrt y) / g)) /
        (2 * g * Real.sqrt y * Real.sqrt (1 - y))
      ≤ (2 * (Real.arcsin (Real.sqrt y) / g)) /
        (2 * g * Real.sqrt y * Real.sqrt (1 - y)) :=
      (div_le_div_iff_of_pos_right hD).mpr (Real.sin_le h2a0)
    _ = Real.arcsin (Real.sqrt y) /
        (g ^ 2 * Real.sqrt y * Real.sqrt (1 - y)) := by
      field_simp [hg0.ne', hs0.ne']
    _ ≤ (Real.pi / 3 * Real.sqrt y) /
        (g ^ 2 * Real.sqrt y * Real.sqrt (1 - y)) :=
      (div_le_div_iff_of_pos_right hD').mpr hθle
    _ = Real.pi / (3 * g ^ 2 * Real.sqrt (1 - y)) := by
      field_simp [hg0.ne', hs0.ne']
    _ ≤ Real.pi / (3 * g ^ 2 * (Real.sqrt 3 / 2)) :=
      div_le_div_of_nonneg_left Real.pi_pos.le hT (by nlinarith)
    _ = (2 * Real.pi / (3 * Real.sqrt 3)) / g ^ 2 := by
      field_simp [hg0.ne', (Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num)).ne']

/-- **Corollary 1 (error propagation, eqs. C8-C11)** of arXiv:1412.3489 p.17.
If `P_s ∈ (0,1/4]` and `-P_s ≤ Δ₀ ≤ 1/4-P_s`, then recovering `P(1)` from
an estimate of `P_s+Δ₀` changes it by at most
`(2π/(3√3))·|Δ₀|/(2m+1)²`. -/
theorem corollary1_errorPropagation
    (m : ℕ) (Ps Δ0 : ℝ) (hPs0 : 0 < Ps) (hPs14 : Ps ≤ 1 / 4)
    (hΔlow : -Ps ≤ Δ0) (hsmall : |Δ0| ≤ 1 / 4 - Ps) :
    |Real.sin (Real.arcsin (Real.sqrt (Ps + Δ0)) / groverFactor m) ^ 2
        - Real.sin (Real.arcsin (Real.sqrt Ps) / groverFactor m) ^ 2|
      ≤ (2 * Real.pi / (3 * Real.sqrt 3)) * |Δ0| / groverFactor m ^ 2 := by
  let g := groverFactor m
  let z := Ps + Δ0
  have hg : 1 ≤ g := one_le_groverFactor m
  have hg0 : 0 < g := by linarith
  have hz0 : 0 ≤ z := by dsimp [z]; linarith
  have hz14 : z ≤ 1 / 4 := by
    have hupper : Δ0 ≤ 1 / 4 - Ps := le_trans (le_abs_self Δ0) hsmall
    dsimp [z]
    linarith
  change |recoveredProbability g z - recoveredProbability g Ps| ≤
    (2 * Real.pi / (3 * Real.sqrt 3)) * |Δ0| / g ^ 2
  rw [show (2 * Real.pi / (3 * Real.sqrt 3)) * |Δ0| / g ^ 2 =
    ((2 * Real.pi / (3 * Real.sqrt 3)) / g ^ 2) * |Δ0| by ring]
  by_cases heq : Ps = z
  · have hΔ : Δ0 = 0 := by dsimp [z] at heq; linarith
    simp [heq, hΔ]
  let a := min Ps z
  let b := max Ps z
  have ha0 : 0 ≤ a := by dsimp [a]; exact le_min hPs0.le hz0
  have hb14 : b ≤ 1 / 4 := by dsimp [b]; exact max_le hPs14 hz14
  have hab : a < b := by dsimp [a, b]; exact min_lt_max.mpr heq
  have hderiv : ∀ y ∈ Set.Ioo a b,
      HasDerivAt (recoveredProbability g) (recoveredProbabilitySlope g y) y := by
    intro y hy
    exact hasDerivAt_recoveredProbability hg0.ne'
      (lt_of_le_of_lt ha0 hy.1) (by linarith [hy.2, hb14])
  obtain ⟨c, hcmem, hc⟩ := exists_hasDerivAt_eq_slope
    (recoveredProbability g) (recoveredProbabilitySlope g) hab
    (continuous_recoveredProbability g).continuousOn hderiv
  have hc0 : 0 < c := lt_of_le_of_lt ha0 hcmem.1
  have hc14 : c < 1 / 4 := by linarith [hcmem.2, hb14]
  have habs : |recoveredProbabilitySlope g c| ≤
      (2 * Real.pi / (3 * Real.sqrt 3)) / g ^ 2 := by
    rw [abs_of_nonneg (recoveredProbabilitySlope_nonneg hg hc0 hc14)]
    exact recoveredProbabilitySlope_le hg hc0 hc14
  have hsub : recoveredProbability g b - recoveredProbability g a =
      recoveredProbabilitySlope g c * (b - a) := by
    rw [hc]
    field_simp [sub_ne_zero.mpr hab.ne']
  have hbound : |recoveredProbability g b - recoveredProbability g a| ≤
      ((2 * Real.pi / (3 * Real.sqrt 3)) / g ^ 2) * |b - a| := by
    rw [hsub, abs_mul]
    exact mul_le_mul_of_nonneg_right habs (abs_nonneg _)
  rcases le_total Ps z with hPz | hPz
  · have ha : a = Ps := by dsimp [a]; exact min_eq_left hPz
    have hb : b = z := by dsimp [b]; exact max_eq_right hPz
    rw [ha, hb] at hbound
    have hba : |z - Ps| = |Δ0| := by congr 1; dsimp [z]; ring
    rwa [hba] at hbound
  · have ha : a = z := by dsimp [a]; exact min_eq_right hPz
    have hb : b = Ps := by dsimp [b]; exact max_eq_left hPz
    rw [ha, hb] at hbound
    have hba : |Ps - z| = |Δ0| := by
      rw [show Ps - z = -Δ0 by dsimp [z]; ring, abs_neg]
    rwa [hba, abs_sub_comm] at hbound

/-- Algebraic rearrangement of the query-count factor in Corollary 1 of
arXiv:1412.3489 p.16. This scalar identity does not construct the amplified
estimator or prove its expected asymptotic cost. -/
theorem corollary1_queryCost
    (δ Pu κ maxκ : ℝ) (hPu : Pu ≠ 0) (hδ : δ ≠ 0) :
    Pu / δ * (Real.sqrt κ + Real.sqrt maxκ)
      = (Real.sqrt κ + Real.sqrt maxκ) / (δ / Pu) := by
  field_simp [hPu, hδ]

/-- The operation-count factor for Corollary 1 is `E` times the query-count
factor. The source's polylogarithmic factors and algorithmic cost bound are not
asserted by this identity. -/
theorem corollary1_operationCost
    (δ Pu E κ maxκ : ℝ) (hPu : Pu ≠ 0) (hδ : δ ≠ 0) :
    E * (Pu / δ * (Real.sqrt κ + Real.sqrt maxκ))
      = E * (Real.sqrt κ + Real.sqrt maxκ) / (δ / Pu) := by
  rw [corollary1_queryCost δ Pu κ maxκ hPu hδ]
  field_simp [hPu, hδ]

end Qatlib.Papers.QDeepLearn14.MainResults.AmplifiedGradient
