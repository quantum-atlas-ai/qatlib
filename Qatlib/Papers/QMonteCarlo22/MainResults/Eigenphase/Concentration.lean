/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Papers.QMonteCarlo22.MainResults.Eigenphase.SpectralModel

@[expose] public section


set_option backward.isDefEq.respectTransparency false



/-!
# Finite eigenphase concentration

Markov concentration of the normalized haversine gives phase concentration when
phases are principal values and the mean is bounded by the second-moment scale.
Source: arXiv:2208.07544v1, Theorem 3.21 and Corollary 3.23, pp. 17–19.
The existential Theorem 3.18 is derived with the nontrivial failure bound `2/9`,
using the same principal-phase and second-moment-scale premises.
These premises admit a normalized singleton law: take `s = 1/32`, `θ = 1/64`,
and `μ = sqrt (1+s²) sin (1/128)`. Then `0 < μ ≤ s`, the normalized height is
one, and the moment in Equation (54) is zero.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

namespace Qatlib.Papers.QMonteCarlo22.MainResults.Eigenphase
open Qatlib.Papers.QMonteCarlo22.MainResults.Eigenphase

/-- Finite Markov inequality: if `q` is a nonnegative weight function, `X` is
nonnegative and `∑ q j * X j ≤ A`, then the `q`-mass of the set where `X` exceeds `a`
is at most `A / a`. -/
theorem markovFinset {J : Type*} [Fintype J] (q X : J → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hX0 : ∀ j, 0 ≤ X j)
    (A a : ℝ) (ha : 0 < a) (hmean : ∑ j, q j * X j ≤ A) :
    ∑ j ∈ Finset.univ.filter (fun j => a < X j), q j ≤ A / a := by
  have hstep : a * ∑ j ∈ Finset.univ.filter (fun j => a < X j), q j
      ≤ ∑ j, q j * X j := by
    calc
      a * ∑ j ∈ Finset.univ.filter (fun j => a < X j), q j
          = ∑ j ∈ Finset.univ.filter (fun j => a < X j), q j * a := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j => a < X j), q j * X j := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_left (Finset.mem_filter.1 hj).2.le (hq0 j)
      _ ≤ ∑ j, q j * X j := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro j _ _
            exact mul_nonneg (hq0 j) (hX0 j)
  have hmain : a * ∑ j ∈ Finset.univ.filter (fun j => a < X j), q j ≤ A :=
    le_trans hstep hmean
  rw [le_div_iff₀ ha]
  linarith

/-- For `t ≥ 0`, `t < |x|` is equivalent to `t² < x²`. -/
theorem lt_abs_iff_sq_lt_sq {x t : ℝ} (ht : 0 ≤ t) :
    t < |x| ↔ t ^ 2 < x ^ 2 := by
  constructor
  · intro h
    have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [abs_nonneg x]
  · intro h
    by_contra hnot
    have hnot := le_of_not_gt hnot
    have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [abs_nonneg x]

/-- The algebraic step of Theorem 3.21, Equation (55): for `h > 0` and `0 ≤ t < 1`,
`|1 - h⁻¹| ≤ t` if and only if `h ∈ [1/(1+t), 1/(1-t)]`. -/
theorem abs_one_sub_inv_le_iff {h t : ℝ} (hh : 0 < h) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    |1 - h⁻¹| ≤ t ↔ h ∈ Set.Icc (1 / (1 + t)) (1 / (1 - t)) := by
  have h1 : (0 : ℝ) < 1 - t := by linarith
  have h2 : (0 : ℝ) < 1 + t := by linarith
  have hrec : h⁻¹ * h = 1 := inv_mul_cancel₀ hh.ne'
  have hinv : 0 < h⁻¹ := inv_pos.2 hh
  rw [abs_le]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hmul1 : 1 ≤ (1 + t) * h := by
      have hle : h⁻¹ ≤ 1 + t := by linarith
      have := mul_le_mul_of_nonneg_right hle hh.le
      rwa [hrec] at this
    have hmul2 : (1 - t) * h ≤ 1 := by
      have hle : 1 - t ≤ h⁻¹ := by linarith
      have := mul_le_mul_of_nonneg_right hle hh.le
      rwa [hrec] at this
    constructor
    · rw [div_le_iff₀ h2]
      nlinarith
    · rw [le_div_iff₀ h1]
      nlinarith
  · rintro ⟨hlo, hhi⟩
    have hmul1 : 1 ≤ (1 + t) * h := by
      rw [div_le_iff₀ h2] at hlo
      nlinarith
    have hmul2 : (1 - t) * h ≤ 1 := by
      rw [le_div_iff₀ h1] at hhi
      nlinarith
    have hleft : h⁻¹ ≤ 1 + t := by nlinarith [hmul1, hrec, hinv]
    have hright : 1 - t ≤ h⁻¹ := by nlinarith [hmul2, hrec, hinv]
    constructor <;> linarith

/-- The normalized height `h = (√(1+s²)/|μ|)·√(hav θ)` of Theorem 3.21,
Equation (50). -/
noncomputable def hOf {J : Type*} (s μ : ℝ) (θ : J → ℝ) (j : J) : ℝ :=
  Real.sqrt (1 + s ^ 2) / |μ| * Real.sqrt (hav (θ j))

/-- Theorem 3.21 (p. 17), Equation (48).  Fix `C ≥ 1`; assume `0 ≤ s` and `C s < 1`
(the paper's `s ≤ 1/C`, with the strict inequality needed for the endpoint
`1/(1-Cs)`), `μ ≠ 0`, and the moment bound of Equation (54),
`∑ j, q j * (1 - h⁻¹)² ≤ 2 s²`, where `h` is the normalized height of
Equation (50). Then the `q`-weight outside `[1/(1+Cs), 1/(1-Cs)]` is at most
`2/C²`. For normalized Born weights this gives the paper's probability bound,
since `h = |sin(θ/2)| / (|μ|/√(1+s²))`. -/
theorem theorem3_21 {J : Type*} [Fintype J]
    (q : J → ℝ) (θ : J → ℝ) (μ s C : ℝ)
    (hq0 : ∀ j, 0 ≤ q j)
    (hμ : μ ≠ 0) (hC : 1 ≤ C) (hs0 : 0 ≤ s) (hsC : C * s < 1)
    (hθ0 : ∀ j, hav (θ j) ≠ 0)
    (hmoment : ∑ j, q j * (1 - (hOf s μ θ j)⁻¹) ^ 2 ≤ 2 * s ^ 2) :
    (∑ j ∈ Finset.univ.filter (fun j =>
        ¬ hOf s μ θ j ∈ Set.Icc (1 / (1 + C * s)) (1 / (1 - C * s))), q j)
      ≤ 2 / C ^ 2 := by
  have hCpos : 0 < C := by linarith
  have hpos : ∀ j, 0 < hOf s μ θ j := by
    intro j
    unfold hOf
    have hnum : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.2 (by nlinarith [sq_nonneg s])
    have hden : 0 < |μ| := abs_pos.2 hμ
    have hhav : 0 < hav (θ j) := lt_of_le_of_ne (hav_nonneg (θ j)) (Ne.symm (hθ0 j))
    have hsq : 0 < Real.sqrt (hav (θ j)) := Real.sqrt_pos.2 hhav
    exact mul_pos (div_pos hnum hden) hsq
  rcases eq_or_lt_of_le hs0 with hs | hspos
  · -- Degenerate case `s = 0`: the moment bound forces `h = 1` wherever `q` is positive.
    subst hs
    have hzero : ∀ j, q j * (1 - (hOf 0 μ θ j)⁻¹) ^ 2 = 0 := by
      intro j
      have hle : q j * (1 - (hOf 0 μ θ j)⁻¹) ^ 2
          ≤ ∑ i, q i * (1 - (hOf 0 μ θ i)⁻¹) ^ 2 := by
        refine Finset.single_le_sum
          (f := fun i => q i * (1 - (hOf 0 μ θ i)⁻¹) ^ 2)
          (fun i _ => mul_nonneg (hq0 i) (sq_nonneg _)) (Finset.mem_univ j)
      have hnn : 0 ≤ q j * (1 - (hOf 0 μ θ j)⁻¹) ^ 2 :=
        mul_nonneg (hq0 j) (sq_nonneg _)
      have := hmoment
      linarith
    have hsum0 : (∑ j ∈ Finset.univ.filter (fun j =>
        ¬ hOf 0 μ θ j ∈ Set.Icc (1 / (1 + C * 0)) (1 / (1 - C * 0))), q j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hmem := (Finset.mem_filter.1 hj).2
      rcases mul_eq_zero.1 (hzero j) with hq | hsq
      · exact hq
      · exfalso
        have h1 : 1 - (hOf 0 μ θ j)⁻¹ = 0 := sq_eq_zero_iff.1 hsq
        have h2 : (hOf 0 μ θ j)⁻¹ = 1 := by linarith
        have h3 : hOf 0 μ θ j = 1 := by
          have := congrArg Inv.inv h2
          simpa using this
        exact hmem (by simp [h3])
    rw [hsum0]
    positivity
  · -- Main case `s > 0`: Markov's inequality at threshold `(C s)²`.
    have ht0 : 0 ≤ C * s := mul_nonneg hCpos.le hspos.le
    have ht1 : C * s < 1 := hsC
    have hfilter :
        Finset.univ.filter (fun j =>
            ¬ hOf s μ θ j ∈ Set.Icc (1 / (1 + C * s)) (1 / (1 - C * s)))
          = Finset.univ.filter (fun j =>
              (C * s) ^ 2 < (1 - (hOf s μ θ j)⁻¹) ^ 2) := by
      apply Finset.filter_congr
      intro j _
      rw [← abs_one_sub_inv_le_iff (hpos j) ht0 ht1, ← lt_abs_iff_sq_lt_sq ht0]
      exact not_le
    rw [hfilter]
    have ha : 0 < (C * s) ^ 2 := by positivity
    have hmark := markovFinset q (fun j => (1 - (hOf s μ θ j)⁻¹) ^ 2) hq0
      (fun j => sq_nonneg _) (2 * s ^ 2) ((C * s) ^ 2) ha hmoment
    have hAC : 2 * s ^ 2 / (C * s) ^ 2 = 2 / C ^ 2 := by
      have hsne : s ≠ 0 := hspos.ne'
      have hCne : C ≠ 0 := hCpos.ne'
      field_simp
    calc
      ∑ j ∈ Finset.univ.filter (fun j => (C * s) ^ 2 < (1 - (hOf s μ θ j)⁻¹) ^ 2), q j
          ≤ 2 * s ^ 2 / (C * s) ^ 2 := hmark
      _ = 2 / C ^ 2 := hAC



/-- Transfer a normalized haversine interval to the explicit phase interval. -/
private theorem phaseTransfer (θ μ s : ℝ) (hμ : μ ≠ 0)
    (hs : 0 ≤ s) (hs1 : s ≤ 1 / 16) (hms : |μ| ≤ s)
    (hθ : |θ| ≤ Real.pi)
    (hh : Real.sqrt (1 + s ^ 2) / |μ| * Real.sqrt (hav θ) ∈
      Set.Icc (16 / 19) (16 / 13)) :
    (13 / 16 : ℝ) * 2 * |μ| ≤ |θ| ∧ |θ| ≤ (5 / 4 : ℝ) * 2 * |μ| := by
  let a := |θ|
  let b := Real.sin (a / 2)
  let R := Real.sqrt (1 + s ^ 2)
  have ha : 0 ≤ a := abs_nonneg θ
  have hap : a ≤ Real.pi := hθ
  have hb : 0 ≤ b := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    (by linarith [Real.pi_pos])
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
  have hR : 1 ≤ R := by nlinarith [sq_nonneg s]
  have hRmax : R ≤ 257 / 256 := by nlinarith
  have hm : 0 < |μ| := abs_pos.mpr hμ
  have heq : Real.sqrt (hav θ) = b := by
    rw [hav, Real.sqrt_sq_eq_abs, Real.abs_sin_eq_sin_abs_of_abs_le_pi]
    · simp [b, a, abs_div]
    · rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [Real.pi_pos]
  rw [heq] at hh
  have hlo : (16 / 19 : ℝ) * |μ| ≤ R * b := by
    have := (le_div_iff₀ hm).mp (show (16 / 19 : ℝ) ≤ R * b / |μ| by
      simpa [R, div_mul_eq_mul_div] using hh.1)
    exact this
  have hhi : R * b ≤ (16 / 13 : ℝ) * |μ| := by
    have := (div_le_iff₀ hm).mp (show R * b / |μ| ≤ (16 / 13 : ℝ) by
      simpa [R, div_mul_eq_mul_div] using hh.2)
    exact this
  have hbhi : b ≤ (16 / 13 : ℝ) * |μ| := by nlinarith
  have hblo : (16 / 19 : ℝ) * |μ| ≤ (257 / 256 : ℝ) * b :=
    hlo.trans (mul_le_mul_of_nonneg_right hRmax hb)
  have hba : b ≤ a / 2 := Real.sin_le (by positivity)
  have hj := Real.mul_le_sin (x := a / 2) (by positivity) (by linarith)
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have haj : a ≤ 4 * b := by
    have := (div_le_iff₀ Real.pi_pos).mp
      (show a / Real.pi ≤ b by convert hj using 1; ring)
    nlinarith
  have hamax : a ≤ 4 / 13 := by nlinarith
  have hcubic : a ^ 3 ≤ (4 / 13 : ℝ) ^ 2 * a := by
    have : a ^ 2 ≤ (4 / 13 : ℝ) ^ 2 := by nlinarith
    exact (by nlinarith [mul_le_mul_of_nonneg_right this ha])
  have hc := Real.sin_ge_sub_cube (x := a / 2) (by positivity)
  constructor
  · change (13 / 16 : ℝ) * 2 * |μ| ≤ a
    nlinarith
  · change a ≤ (5 / 4 : ℝ) * 2 * |μ|
    nlinarith

/-- Corollary 3.23 (p. 18), for principal phases and `|μ| ≤ s`: fixing `t ≥ 1`,
the exceptional `q`-weight bound is `2/(9t²)` with `s0 = 1/(16t)`, lower factor `13/16`,
and upper factor `5/4`. -/
theorem corollary3_23 (t : ℝ) (ht : 1 ≤ t) :
    ∀ {J : Type*} [Fintype J] (q : J → ℝ) (θ : J → ℝ) (μ s : ℝ),
      (∀ j, 0 ≤ q j) → μ ≠ 0 → 0 ≤ s → s ≤ 1 / (16 * t) →
      |μ| ≤ s → (∀ j, |θ j| ≤ Real.pi) →
      (∀ j, hav (θ j) ≠ 0) →
      (∑ j, q j * (1 - (hOf s μ θ j)⁻¹) ^ 2 ≤ 2 * s ^ 2) →
      (∑ j ∈ Finset.univ.filter (fun j =>
          ¬ ((1 - 3 * t * (1 / (16 * t))) * 2 * |μ| ≤ |θ j| ∧
            |θ j| ≤ (1 + 4 * t * (1 / (16 * t))) * 2 * |μ|)), q j)
        ≤ 2 / (9 * t ^ 2) := by
  intro J _ q θ μ s hq hμ hs hsmax hms hprincipal hθ hm
  have htpos : 0 < t := by linarith
  have hts : t * s ≤ 1 / 16 := by
    have := (le_div_iff₀ (show 0 < 16 * t by positivity)).mp hsmax
    nlinarith
  have hs1 : s ≤ 1 / 16 := by nlinarith
  have hcon := theorem3_21 q θ μ s (3 * t) hq hμ (by linarith) hs
    (by linarith) hθ hm
  have hsub :
      Finset.univ.filter (fun j =>
        ¬ ((1 - 3 * t * (1 / (16 * t))) * 2 * |μ| ≤ |θ j| ∧
          |θ j| ≤ (1 + 4 * t * (1 / (16 * t))) * 2 * |μ|)) ⊆
      Finset.univ.filter (fun j => ¬ hOf s μ θ j ∈
        Set.Icc (1 / (1 + (3 * t) * s)) (1 / (1 - (3 * t) * s))) := by
    intro j hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hgood
    have hlo : (16 / 19 : ℝ) ≤ hOf s μ θ j := by
      have hd : 0 < 1 + (3 * t) * s := by positivity
      have := (div_le_iff₀ hd).mp hgood.1
      have hp : 0 ≤ hOf s μ θ j := le_trans (by positivity) hgood.1
      nlinarith [mul_le_mul_of_nonneg_right (show (3 * t) * s ≤ 3 / 16 by nlinarith) hp]
    have hhi : hOf s μ θ j ≤ (16 / 13 : ℝ) := by
      have hd : 0 < 1 - (3 * t) * s := by linarith
      have := (le_div_iff₀ hd).mp hgood.2
      have hp : 0 ≤ hOf s μ θ j := le_trans (by positivity) hgood.1
      nlinarith [mul_le_mul_of_nonneg_right (show (3 * t) * s ≤ 3 / 16 by nlinarith) hp]
    have hp := phaseTransfer (θ j) μ s hμ hs hs1 hms (hprincipal j) ⟨hlo, hhi⟩
    have hc : t * (1 / (16 * t)) = 1 / 16 := by field_simp
    apply (Finset.mem_filter.mp hj).2
    constructor <;> nlinarith [hp.1, hp.2]
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬ hOf s μ θ j ∈
        Set.Icc (1 / (1 + (3 * t) * s)) (1 / (1 - (3 * t) * s))), q j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hq j)
    _ ≤ 2 / (3 * t) ^ 2 := hcon
    _ = 2 / (9 * t ^ 2) := by ring

/-- Theorem 3.18 for principal phases with `|μ| ≤ s`, with failure mass at most
`2/9` (success probability at least `7/9` for normalized weights); the moment
premise is Equation (54). -/
theorem theorem3_18 :
    ∃ s0 c0 C0 δ0 : ℝ,
      0 < s0 ∧ 0 < c0 ∧ 0 < C0 ∧ 0 < δ0 ∧ δ0 < 1 ∧
      ∀ {J : Type*} [Fintype J] (q : J → ℝ) (θ : J → ℝ) (μ s : ℝ),
        (∀ j, 0 ≤ q j) → μ ≠ 0 → 0 ≤ s → s ≤ s0 →
        |μ| ≤ s → (∀ j, |θ j| ≤ Real.pi) →
        (∀ j, hav (θ j) ≠ 0) →
        (∑ j, q j * (1 - (hOf s μ θ j)⁻¹) ^ 2 ≤ 2 * s ^ 2) →
        (∑ j ∈ Finset.univ.filter (fun j =>
            ¬ (c0 * 2 * |μ| ≤ |θ j| ∧ |θ j| ≤ C0 * 2 * |μ|)), q j) ≤ δ0 := by
  refine ⟨1 / 16, 13 / 16, 5 / 4, 2 / 9,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro J _ q θ μ s hq hμ hs hsmax hms hprincipal hθ hm
  have hcon := corollary3_23 1 (by norm_num) q θ μ s hq hμ hs
    (by norm_num at hsmax ⊢; exact hsmax) hms hprincipal hθ hm
  norm_num at hcon ⊢
  exact hcon

end Qatlib.Papers.QMonteCarlo22.MainResults.Eigenphase
