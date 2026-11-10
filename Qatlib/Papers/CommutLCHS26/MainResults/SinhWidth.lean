/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.SinhStrip
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.MainResults.SinhWidth
open Complex Matrix Set Filter MeasureTheory
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
open Qatlib.Papers.CommutLCHS26.MainResults.SinhStrip
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule (transformed)
set_option warningAsError false
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance : ContinuousENorm (Matrix ι ι ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm

def denominator (n : ℕ) (b η : ℝ) (z : ℂ) : ℂ :=
  (1 - I * ((η : ℂ) * Complex.sinh z)) *
    ((b : ℂ) + I * ((η : ℂ) * Complex.sinh z)) ^ n

def numerator (n : ℕ) (b c d η : ℝ) (z : ℂ) : ℂ :=
  ((η : ℂ) * Complex.cosh z) *
    (((b + 1 : ℝ) ^ n / (2 * Real.pi) : ℝ) : ℂ) *
    Complex.exp ((d : ℂ) * (1 - I * ((η : ℂ) * Complex.sinh z))) *
    Complex.exp (-(((η : ℂ) * Complex.sinh z) ^ 2 + 1) / (4 * (c : ℂ) ^ 2))

theorem product_identity (n : ℕ) (b c d T η : ℝ) (H L : Matrix ι ι ℂ) (z : ℂ)
    (hz : denominator n b η z ≠ 0) :
    denominator n b η z • transformed n b c d T η H L z =
      numerator n b c d η z • propagator H L T ((η : ℂ) * Complex.sinh z) := by
  unfold transformed integrand
  rw [smul_smul, smul_smul]
  congr 1
  unfold coefficient numerator
  change denominator n b η z * _ * (_ / denominator n b η z) = _
  field_simp [hz]

theorem numerator_ne_zero (n : ℕ) {b η y : ℝ} (hb : 0 < b) (hη : 0 < η)
    (hy : |y| < Real.pi / 2) (c d : ℝ) : numerator n b c d η ((y : ℂ) * I) ≠ 0 := by
  have hcos : Real.cos y ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [(abs_lt.mp hy).1], (abs_lt.mp hy).2⟩).ne'
  have hj : (η : ℂ) * Complex.cosh ((y : ℂ) * I) ≠ 0 := by
    rw [Complex.cosh_mul_I, ← Complex.ofReal_cos]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hη.ne') (Complex.ofReal_ne_zero.mpr hcos)
  unfold numerator
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hj (Complex.ofReal_ne_zero.mpr
    (by positivity : (b + 1) ^ n / (2 * Real.pi) ≠ 0))) (Complex.exp_ne_zero _))
      (Complex.exp_ne_zero _)

theorem denominator_ne_zero_off_axis (n : ℕ) (b : ℝ) {η x y : ℝ} (hη : 0 < η)
    (hx : x ≠ 0) (hy : |y| < Real.pi / 2) :
    denominator n b η ((x : ℂ) + y * I) ≠ 0 := by
  have hcos : Real.cos y ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [(abs_lt.mp hy).1], (abs_lt.mp hy).2⟩).ne'
  have him : η * Real.sinh x * Real.cos y ≠ 0 :=
    mul_ne_zero (mul_ne_zero hη.ne' (by simpa only [ne_eq, Real.sinh_eq_zero] using! hx)) hcos
  have hp (κ : ℝ) : pole κ η ((x : ℂ) + y * I) ≠ 0 := by
    intro he
    apply him
    simpa only [pole_im, Complex.zero_im] using! congrArg Complex.im he
  have hl : 1 - I * ((η : ℂ) * Complex.sinh ((x : ℂ) + y * I)) ≠ 0 := by
    have hh := hp (-1)
    dsimp [pole] at hh
    norm_num only [Complex.ofReal_neg, Complex.ofReal_one] at hh
    intro he
    apply hh
    linear_combination -he
  exact mul_ne_zero hl (pow_ne_zero n (hp b))

theorem not_continuous_pole [Nonempty ι] (n : ℕ) {b η y : ℝ} (hb : 0 < b) (hη : 0 < η)
    (hy : |y| < Real.pi / 2) (c d T : ℝ) (H L : Matrix ι ι ℂ)
    (hz : denominator n b η ((y : ℂ) * I) = 0) :
    ¬ ContinuousAt (transformed n b c d T η H L) ((y : ℂ) * I) := by
  intro hc
  let z₀ := (y : ℂ) * I
  have hline : Tendsto (fun t : ℝ => (t : ℂ) + y * I) (𝓝[>] 0) (𝓝 z₀) := by
    have ht : ContinuousAt (fun t : ℝ => (t : ℂ) + y * I) 0 := by fun_prop
    simpa only [Complex.ofReal_zero, zero_add] using! ht.tendsto.mono_left nhdsWithin_le_nhds
  have hD : ContinuousAt (denominator n b η) z₀ := by unfold denominator; fun_prop
  have hQ : ContinuousAt (fun z : ℂ => numerator n b c d η z •
      propagator H L T ((η : ℂ) * Complex.sinh z)) z₀ := by
    apply ContinuousAt.smul (f := numerator n b c d η)
      (g := fun z => propagator H L T ((η : ℂ) * Complex.sinh z))
    · unfold numerator
      fun_prop
    · exact ((propagator_analytic H L T _).comp (by fun_prop)).continuousAt
  have hleft : Tendsto (fun t : ℝ => denominator n b η ((t : ℂ) + y * I) •
      transformed n b c d T η H L ((t : ℂ) + y * I)) (𝓝[>] 0)
      (𝓝 (denominator n b η z₀ • transformed n b c d T η H L z₀)) :=
    (hD.smul hc).tendsto.comp hline
  have hright := hQ.tendsto.comp hline
  have heq : (fun t : ℝ => denominator n b η ((t : ℂ) + y * I) •
      transformed n b c d T η H L ((t : ℂ) + y * I)) =ᶠ[𝓝[>] 0]
      (fun t : ℝ => numerator n b c d η ((t : ℂ) + y * I) •
        propagator H L T ((η : ℂ) * Complex.sinh ((t : ℂ) + y * I))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact product_identity n b c d T η H L _
      (denominator_ne_zero_off_axis n b hη (ne_of_gt ht) hy)
  have he := tendsto_nhds_unique_of_eventuallyEq hleft hright heq
  have hp : propagator H L T ((η : ℂ) * Complex.sinh z₀) ≠ 0 :=
    (Matrix.isUnit_exp _).ne_zero
  have hn := smul_ne_zero (numerator_ne_zero n hb hη hy c d) hp
  apply hn
  simpa only [z₀, hz, zero_smul] using! he.symm

theorem denominator_ne_zero_of_continuous [Nonempty ι] (n : ℕ) {b η : ℝ}
    (hb : 0 < b) (hη : 0 < η) (c d T : ℝ) (H L : Matrix ι ι ℂ) {z : ℂ}
    (hz : |z.im| < Real.pi / 2) (hc : ContinuousAt (transformed n b c d T η H L) z) :
    denominator n b η z ≠ 0 := by
  intro hd
  have hx : z.re = 0 := by
    by_contra hx
    apply denominator_ne_zero_off_axis n b hη hx hz
    simpa only [Complex.re_add_im] using! hd
  have he : (z.im : ℂ) * I = z := by
    conv_rhs => rw [← Complex.re_add_im z, hx]
    simp
  apply not_continuous_pole n hb hη hz c d T H L (by simpa only [he] using! hd)
  simpa only [he] using! hc

theorem transformed_analytic_iff [Nonempty ι] (n : ℕ) {b η β : ℝ} (hb : 0 < b)
    (hη : 0 < η) (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 2)
    (c d T : ℝ) (H L : Matrix ι ι ℂ) :
    AnalyticOnNhd ℂ (transformed n b c d T η H L) {z : ℂ | |z.im| ≤ β} ↔
      η * Real.sin β < 1 ∧ (n = 0 ∨ η * Real.sin β < b) := by
  constructor
  · intro ha
    have hD (z : ℂ) (hz : |z.im| ≤ β) : denominator n b η z ≠ 0 :=
      denominator_ne_zero_of_continuous n hb hη c d T H L (hz.trans_lt hβ) (ha z hz).continuousAt
    constructor
    · apply (pole_free_iff (by norm_num : (0 : ℝ) < 1) hη hβ₀ hβ).mp
      intro z hz he
      have hd := hD (-z) (by simpa using! hz)
      apply hd
      have hh : 1 - I * ((η : ℂ) * Complex.sinh (-z)) = pole 1 η z := by
        simp only [pole, Complex.ofReal_one, Complex.sinh_neg, mul_neg, sub_neg_eq_add]
      unfold denominator
      rw [hh, he, zero_mul]
    · by_cases hn : n = 0
      · exact Or.inl hn
      · right
        apply (pole_free_iff hb hη hβ₀ hβ).mp
        intro z hz he
        have hd := hD z hz
        apply hd
        change (1 - I * ((η : ℂ) * Complex.sinh z)) * (pole b η z) ^ n = 0
        rw [he, zero_pow hn, mul_zero]
  · rintro ⟨hgap, hbn⟩
    exact transformed_analytic n b c d T η β hη hβ₀ hβ hgap hbn H L

def analyticWidth (n : ℕ) (b c d T η : ℝ) (H L : Matrix ι ι ℂ) : EReal :=
  sSup {w : EReal | ∃ β : ℝ, 0 < β ∧ w = (β : EReal) ∧
    AnalyticOnNhd ℂ (transformed n b c d T η H L) {z : ℂ | |z.im| ≤ β}}

theorem lt_analyticWidth_iff (n : ℕ) (b c d T η β : ℝ) (H L : Matrix ι ι ℂ) :
    (β : EReal) < analyticWidth n b c d T η H L ↔
      ∃ γ : ℝ, 0 < γ ∧ β < γ ∧
        AnalyticOnNhd ℂ (transformed n b c d T η H L) {z : ℂ | |z.im| ≤ γ} := by
  unfold analyticWidth
  rw [lt_sSup_iff]
  constructor
  · rintro ⟨w, ⟨γ, hγ, rfl, ha⟩, hlt⟩
    exact ⟨γ, hγ, EReal.coe_lt_coe_iff.mp hlt, ha⟩
  · rintro ⟨γ, hγ, hlt, ha⟩
    exact ⟨(γ : EReal), ⟨γ, hγ, rfl, ha⟩, EReal.coe_lt_coe hlt⟩

theorem analytic_of_lt_width (n : ℕ) (b c d T η β : ℝ) (H L : Matrix ι ι ℂ)
    (hβ : (β : EReal) < analyticWidth n b c d T η H L) :
    AnalyticOnNhd ℂ (transformed n b c d T η H L) {z : ℂ | |z.im| ≤ β} := by
  obtain ⟨γ, _, hγ, ha⟩ := (lt_analyticWidth_iff n b c d T η β H L).mp hβ
  exact ha.mono (fun _ hz => hz.trans hγ.le)

theorem gaps_of_lt_width [Nonempty ι] (n : ℕ) {b η β : ℝ} (hb : 0 < b)
    (hη : 0 < η) (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 2)
    (c d T : ℝ) (H L : Matrix ι ι ℂ)
    (hw : (β : EReal) < analyticWidth n b c d T η H L) :
    η * Real.sin β < 1 ∧ (n = 0 ∨ η * Real.sin β < b) := by
  exact (transformed_analytic_iff n hb hη hβ₀ hβ c d T H L).mp
    (analytic_of_lt_width n b c d T η β H L hw)

theorem lt_width_of_gaps (n : ℕ) {η β : ℝ} (hη : 0 < η) (hβ₀ : 0 ≤ β)
    (hβ : β < Real.pi / 2) (b c d T : ℝ) (H L : Matrix ι ι ℂ)
    (hgap : η * Real.sin β < 1) (hbn : n = 0 ∨ η * Real.sin β < b) :
    (β : EReal) < analyticWidth n b c d T η H L := by
  have hs : ContinuousAt (fun γ : ℝ => η * Real.sin γ) β := by fun_prop
  have h1 : ∀ᶠ γ in 𝓝 β, η * Real.sin γ < 1 := hs.eventually_lt continuousAt_const hgap
  have h2 : ∀ᶠ γ in 𝓝 β, n = 0 ∨ η * Real.sin γ < b := by
    rcases hbn with hn | hb
    · exact Filter.Eventually.of_forall fun _ => Or.inl hn
    · exact (hs.eventually_lt continuousAt_const hb).mono fun _ h => Or.inr h
  have h3 : ∀ᶠ γ in 𝓝 β, γ < Real.pi / 2 := eventually_lt_nhds hβ
  have hev : ∀ᶠ γ in 𝓝[>] β,
      (η * Real.sin γ < 1 ∧ (n = 0 ∨ η * Real.sin γ < b) ∧ γ < Real.pi / 2) ∧ β < γ :=
    ((h1.and (h2.and h3)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨γ, ⟨hg1, hgn, hgπ⟩, hγ⟩ := hev.exists
  have hg₀ : 0 < γ := hβ₀.trans_lt hγ
  exact (lt_analyticWidth_iff n b c d T η β H L).mpr ⟨γ, hg₀, hγ,
    transformed_analytic n b c d T η γ hη hg₀.le hgπ hg1 hgn H L⟩

theorem lt_width_iff_gaps [Nonempty ι] (n : ℕ) {b η β : ℝ} (hb : 0 < b)
    (hη : 0 < η) (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 2)
    (c d T : ℝ) (H L : Matrix ι ι ℂ) :
    (β : EReal) < analyticWidth n b c d T η H L ↔
      η * Real.sin β < 1 ∧ (n = 0 ∨ η * Real.sin β < b) := by
  exact ⟨gaps_of_lt_width n hb hη hβ₀ hβ c d T H L,
    fun h => lt_width_of_gaps n hη hβ₀ hβ b c d T H L h.1 h.2⟩

theorem transformed_empty [IsEmpty ι] (n : ℕ) (b c d T η : ℝ) (H L : Matrix ι ι ℂ) (z : ℂ) :
    transformed n b c d T η H L z = 0 := Subsingleton.elim _ _

theorem analytic_empty [IsEmpty ι] (n : ℕ) (b c d T η : ℝ) (H L : Matrix ι ι ℂ) (β : ℝ) :
    AnalyticOnNhd ℂ (transformed n b c d T η H L) {z : ℂ | |z.im| ≤ β} := by
  have he : transformed n b c d T η H L = fun _ => 0 := funext (transformed_empty n b c d T η H L)
  rw [he]
  exact analyticOnNhd_const

theorem analyticWidth_empty [IsEmpty ι] (n : ℕ) (b c d T η : ℝ) (H L : Matrix ι ι ℂ) :
    analyticWidth n b c d T η H L = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro β
  apply (lt_analyticWidth_iff n b c d T η β H L).mpr
  refine ⟨max β 0 + 1, by positivity, ?_, analytic_empty n b c d T η H L _⟩
  linarith [le_max_left β 0]

theorem mass_nonneg (n : ℕ) {b c d η β K : ℝ} (hb : 0 < b) (hη : 0 < η) (hβ₀ : 0 ≤ β) :
    0 ≤ stripMass n b c d η β K :=
  mul_nonneg (amplitude_nonneg n hb hη hβ₀) (Real.sqrt_nonneg _)

theorem original_strip_estimates (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 4)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef) {T : ℝ} (hT : 0 ≤ T)
    (hw : (β : EReal) < analyticWidth n b c d T η H L) :
    AnalyticOnNhd ℂ (transformed n b c d T η H L) {z : ℂ | |z.im| ≤ β} ∧
      Qatlib.Papers.CommutLCHS26.MainResults.StripContour.UniformDecay
        (transformed n b c d T η H L) (-β) β ∧
      ∀ y : ℝ, |y| ≤ β →
        Integrable (fun x : ℝ => transformed n b c d T η H L ((x : ℂ) + y * I)) ∧
        (∫ x : ℝ, ‖transformed n b c d T η H L ((x : ℂ) + y * I)‖) ≤
          stripMass n b c d η β (T * ‖L‖) := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    letI := hι
    refine ⟨analytic_empty n b c d T η H L β, ?_, ?_⟩
    · intro ε hε
      exact ⟨0, fun x _ y _ => by simpa only [transformed_empty, norm_zero] using! hε.le⟩
    · intro y _
      constructor
      · simpa only [transformed_empty] using!
          (Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule.actual_integrability
            n b c d hb hc H L hH hL hT hη).2
      · simpa only [transformed_empty, norm_zero, integral_zero] using!
          (mass_nonneg n hb hη hβ₀ : 0 ≤ stripMass n b c d η β (T * ‖L‖))
  | inr hι =>
    letI := hι
    obtain ⟨hgap, hbn⟩ := gaps_of_lt_width n hb hη hβ₀ (by linarith [Real.pi_pos]) c d T H L hw
    exact transformed_strip_estimates n b c d η β hb hc hη hβ₀ hβ hgap hbn H L hH hL hT

theorem original_mesh_error (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 < β) (hβ : β < Real.pi / 4)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h)
    (hw : (β : EReal) < analyticWidth n b c d T η H L) :
    ‖(∫ x : ℝ, transformed n b c d T η H L (x : ℂ)) -
        h • ∑' j : ℤ, transformed n b c d T η H L ((h * (j : ℝ) : ℝ) : ℂ)‖ ≤
      2 * stripMass n b c d η β (T * ‖L‖) / (Real.exp (2 * Real.pi * β / h) - 1) := by
  have hs := original_strip_estimates n b c d η β hb hc hη hβ₀.le hβ H L hH hL hT hw
  apply Qatlib.Papers.CommutLCHS26.MainResults.StripSampling.analytic_strip_mesh_error
    _ _ _ _ hβ₀ hh hs.1 hs.2.1
  · intro y hy
    exact (hs.2.2 y (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)).1
  · intro y hy
    exact (hs.2.2 y (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)).2

theorem original_mass_supremum (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 4)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef) {T : ℝ} (hT : 0 ≤ T)
    (hw : (β : EReal) < analyticWidth n b c d T η H L) :
    sSup {r : ℝ | ∃ y : ℝ, |y| ≤ β ∧
      r = ∫ x : ℝ, ‖transformed n b c d T η H L ((x : ℂ) + y * I)‖} ≤
      stripMass n b c d η β (T * ‖L‖) := by
  apply csSup_le
  · exact ⟨_, 0, by simpa using! hβ₀, rfl⟩
  · rintro r ⟨y, hy, rfl⟩
    exact (original_strip_estimates n b c d η β hb hc hη hβ₀ hβ H L hH hL hT hw).2.2 y hy |>.2

theorem original_estimates (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 < β) (hβ : β < Real.pi / 4)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef) {T : ℝ} (hT : 0 ≤ T)
    (hw : (β : EReal) < analyticWidth n b c d T η H L) :
    AnalyticOnNhd ℂ (transformed n b c d T η H L) {z : ℂ | |z.im| ≤ β} ∧
      Qatlib.Papers.CommutLCHS26.MainResults.StripContour.UniformDecay
        (transformed n b c d T η H L) (-β) β ∧
      (sSup {r : ℝ | ∃ y : ℝ, |y| ≤ β ∧
        r = ∫ x : ℝ, ‖transformed n b c d T η H L ((x : ℂ) + y * I)‖} ≤
          stripMass n b c d η β (T * ‖L‖)) ∧
      ∀ h : ℝ, 0 < h →
        ‖(∫ x : ℝ, transformed n b c d T η H L (x : ℂ)) -
            h • ∑' j : ℤ, transformed n b c d T η H L ((h * (j : ℝ) : ℝ) : ℂ)‖ ≤
          2 * stripMass n b c d η β (T * ‖L‖) / (Real.exp (2 * Real.pi * β / h) - 1) := by
  have hs := original_strip_estimates n b c d η β hb hc hη hβ₀.le hβ H L hH hL hT hw
  exact ⟨hs.1, hs.2.1, original_mass_supremum n b c d η β hb hc hη hβ₀.le hβ H L hH hL hT hw,
    fun _ hh => original_mesh_error n b c d η β hb hc hη hβ₀ hβ H L hH hL hT hh hw⟩

end Qatlib.Papers.CommutLCHS26.MainResults.SinhWidth
