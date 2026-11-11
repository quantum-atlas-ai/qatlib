/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.Transport
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.Seeds
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# Finite-interval existence of the horizontal-coordinate ODE

A bounded radial modification admits Picard--Lindelof solutions on the whole
requested interval. Pure imaginary right coefficients preserve unit norm,
so the modification is identically the original equation along the solution.
This is mathematical existence, not an executable solver or parameter-smooth
periodic reference field.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace Topology NNReal ContDiff
open Set Metric
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of radial Unit in the Hopf Atlas construction. -/
private def radialUnit (q : ℍ) : ℍ := (2/(1+‖q‖) : ℝ) • q

/-- Original `radialUnit_norm` guarantee for the `Existence` construction; the complete source hypotheses are retained. -/
private theorem radialUnit_norm (q : ℍ) : ‖radialUnit q‖ ≤ 2 := by
  have hp : 0 < 1+‖q‖ := by positivity
  rw [radialUnit, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_mul_eq_mul_div, div_le_iff₀ hp]
  nlinarith [norm_nonneg q]

/-- Original `radialUnit_lipschitz` guarantee for the `Existence` construction; the complete source hypotheses are retained. -/
private theorem radialUnit_lipschitz : LipschitzWith 4 radialUnit := by
  apply LipschitzWith.of_dist_le_mul
  intro q p
  have hq : 0 < 1+‖q‖ := by positivity
  have hp : 0 < 1+‖p‖ := by positivity
  have heq : radialUnit q-radialUnit p =
      (2/(1+‖q‖) : ℝ) • (q-p) +
        (2*(‖p‖-‖q‖)/((1+‖q‖)*(1+‖p‖)) : ℝ) • p := by
    have hr : 2*(‖p‖-‖q‖)/((1+‖q‖)*(1+‖p‖)) =
        2/(1+‖q‖)-2/(1+‖p‖) := by
      field_simp
      ring
    rw [hr, radialUnit, radialUnit, smul_sub, sub_smul]
    abel
  rw [dist_eq_norm, heq]
  calc
    _ ≤ ‖(2/(1+‖q‖) : ℝ) • (q-p)‖ +
        ‖(2*(‖p‖-‖q‖)/((1+‖q‖)*(1+‖p‖)) : ℝ) • p‖ := norm_add_le _ _
    _ ≤ 2*‖q-p‖+2*‖q-p‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_pos hq, abs_of_pos hp, abs_of_pos (by norm_num : (0 : ℝ)<2)]
      apply add_le_add
      · have h : 2/(1+‖q‖) ≤ (2 : ℝ) := (div_le_iff₀ hq).mpr (by nlinarith [norm_nonneg q])
        exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
      · rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos hq hp)]
        have hn : |‖p‖-‖q‖| ≤ ‖q-p‖ := by
          simpa [norm_sub_rev] using abs_norm_sub_norm_le p q
        have hnp := norm_nonneg p
        have hnq := norm_nonneg q
        have hnd := norm_nonneg (q-p)
        nlinarith [mul_le_mul_of_nonneg_right hn hnp,
          mul_nonneg hnq hnp, mul_nonneg hnd (mul_nonneg hnq hnp),
          mul_nonneg hnd hnq]
    _ = (4 : ℝ)*dist q p := by rw [dist_eq_norm]; ring

/-- Original `radialUnit_eq` guarantee for the `Existence` construction; the complete source hypotheses are retained. -/
private theorem radialUnit_eq (q : ℍ) (hq : ‖q‖=1) : radialUnit q=q := by
  norm_num [radialUnit, hq]

/-- Original `right_derivative_of_Icc` guarantee for the `Existence` construction; the complete source hypotheses are retained. -/
private theorem right_derivative_of_Icc {q : ℝ → ℍ} {v : ℍ} {a b t : ℝ}
    (ht : t ∈ Ico a b) (hq : HasDerivWithinAt q v (Icc a b) t) :
    HasDerivWithinAt q v (Ici t) t := by
  apply hq.mono_of_mem_nhdsWithin
  exact Filter.mem_of_superset
    (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)) self_mem_nhdsWithin) (by
    intro u hu
    exact ⟨le_trans ht.1 hu.2, le_of_lt hu.1⟩)

/-- Existence on any finite interval for continuous, bounded pure right coefficients.
Only the initial quaternion is supplied; the solution is an output. -/
theorem right_transport_exists {k : ℝ → ℍ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn k (Icc a b)) (K : ℝ≥0)
    (hb : ∀ t ∈ Icc a b, ‖k t‖ ≤ K)
    (hp : ∀ t ∈ Icc a b, (k t).re=0) (q₀ : ℍ) (h₀ : ‖q₀‖=1) :
    ∃ q : ℝ → ℍ, q a=q₀ ∧ ContinuousOn q (Icc a b) ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt q (q t*k t) (Icc a b) t) ∧
      ∀ t ∈ Icc a b, ‖q t‖=1 := by
  let T : ℝ≥0 := ⟨b-a, sub_nonneg.mpr hab⟩
  let A : ℝ≥0 := 2*K*T+1
  let f : ℝ → ℍ → ℍ := fun t q => radialUnit q*k t
  have hf : IsPicardLindelof f (⟨a, le_rfl, hab⟩ : Icc a b) q₀ A 0 (2*K) (4*K) := by
    constructor
    · intro t ht
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro q p
      change dist (radialUnit q*k t) (radialUnit p*k t) ≤ _
      calc
        _ = dist (radialUnit q) (radialUnit p)*‖k t‖ := by
          simp only [dist_eq_norm, ← sub_mul, norm_mul]
        _ ≤ ((4 : ℝ)*dist q p)*(K : ℝ) :=
          mul_le_mul (radialUnit_lipschitz.dist_le_mul q p) (hb t ht)
            (norm_nonneg _) (by positivity)
        _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring
    · intro q _
      exact continuousOn_const.mul hc
    · intro t ht q _
      exact (norm_mul_le _ _).trans (mul_le_mul (radialUnit_norm q) (hb t ht)
        (norm_nonneg _) (by norm_num))
    · change (2*(K : ℝ))*max (b-a) (a-a) ≤ (2*(K : ℝ)*(b-a)+1)-0
      rw [sub_self, max_eq_left (sub_nonneg.mpr hab)]
      linarith
  obtain ⟨q, hqa, hqd⟩ := hf.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hcont : ContinuousOn q (Icc a b) := HasDerivWithinAt.continuousOn hqd
  have hnorm : ∀ t ∈ Icc a b, ‖q t‖=1 := by
    apply unit_transport (k := fun t => (2/(1+‖q t‖) : ℝ) • k t) hcont
    · intro t ht
      simpa [f, radialUnit, smul_mul_assoc, mul_smul_comm] using
        right_derivative_of_Icc ht (hqd t ⟨ht.1, ht.2.le⟩)
    · intro t ht
      simp [hp t ⟨ht.1, ht.2.le⟩]
    · simpa only [hqa] using h₀
  refine ⟨q, hqa, hcont, ?_, hnorm⟩
  intro t ht
  simpa only [f, radialUnit_eq (q t) (hnorm t ht)] using hqd t ht

/-- The source alone, plus a compatible initial point, generates horizontal transport.
The hypotheses contain neither an ODE solution nor its propagated Hopf identity. -/
theorem horizontal_transport_exists {s ds : ℝ → ℍ} {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ t, HasDerivAt s (ds t) t) (hr : ∀ t, (s t).re=0) (hn : ∀ t, ‖s t‖=1)
    (hc : ContinuousOn ds (Icc a b)) (M : ℝ≥0) (hb : ∀ t ∈ Icc a b, ‖ds t‖ ≤ M)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (hcompat : hopf q₀=s a) :
    ∃ q : ℝ → ℍ, q a=q₀ ∧ ContinuousOn q (Icc a b) ∧
      (∀ t ∈ Icc a b,
        HasDerivWithinAt q (q t*horizontalCoefficient (s t) (ds t)) (Icc a b) t) ∧
      ∀ t ∈ Icc a b, ‖q t‖=1 ∧ hopf (q t)=s t := by
  have hsc : ContinuousOn s (Icc a b) :=
    (continuous_iff_continuousAt.mpr (fun t => (hs t).continuousAt)).continuousOn
  have hkc : ContinuousOn (fun t => horizontalCoefficient (s t) (ds t)) (Icc a b) := by
    change ContinuousOn (fun t => (-1/2 : ℝ) • (s t * ds t)) (Icc a b)
    exact (hsc.mul hc).const_smul (-1/2 : ℝ)
  have hkb : ∀ t ∈ Icc a b, ‖horizontalCoefficient (s t) (ds t)‖ ≤ M := by
    intro t ht
    rw [horizontal_norm _ _ (hn t)]
    nlinarith [hb t ht, norm_nonneg (ds t)]
  obtain ⟨q, hqa, hqc, hqd, _⟩ := right_transport_exists hab hkc M hkb
    (fun t _ => horizontal_re _ _ (source_tangent hs hr hn t)) q₀ h₀
  refine ⟨q, hqa, hqc, hqd, ?_⟩
  apply horizontal_transport hs hr hn (M := (M : ℝ))
    (fun t ht => hb t ⟨ht.1, ht.2.le⟩) hqc
    (fun t ht => right_derivative_of_Icc ht (hqd t ⟨ht.1, ht.2.le⟩))
  · simpa [hqa] using h₀
  · simpa [hqa] using hcompat

/-- Initial lift points are constructed from the source charts, not supplied by an oracle. -/
theorem horizontal_lift_exists {s ds : ℝ → ℍ} {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ t, HasDerivAt s (ds t) t) (hr : ∀ t, (s t).re=0) (hn : ∀ t, ‖s t‖=1)
    (hc : ContinuousOn ds (Icc a b)) (M : ℝ≥0) (hb : ∀ t ∈ Icc a b, ‖ds t‖ ≤ M) :
    ∃ q : ℝ → ℍ, ContinuousOn q (Icc a b) ∧
      (∀ t ∈ Icc a b,
        HasDerivWithinAt q (q t*horizontalCoefficient (s t) (ds t)) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, ‖q t‖=1 ∧ hopf (q t)=s t) ∧
      ((q a=northSeed (s a) ∧ (1/2 : ℝ)<(q a).re) ∨
       (q a=southSeed (s a) ∧ (1/2 : ℝ)<(q a).imJ)) := by
  rcases chart_cover (s a) with h | h
  · obtain ⟨q, hqa, hqc, hqd, hqh⟩ := horizontal_transport_exists hab hs hr hn hc M hb
      (northSeed (s a)) (northSeed_norm _ (hr a) (hn a) h)
      (northSeed_hopf _ (hr a) (hn a) h)
    exact ⟨q, hqc, hqd, hqh, Or.inl ⟨hqa, hqa ▸ northSeed_margin _ h⟩⟩
  · obtain ⟨q, hqa, hqc, hqd, hqh⟩ := horizontal_transport_exists hab hs hr hn hc M hb
      (southSeed (s a)) (southSeed_norm _ (hr a) (hn a) h)
      (southSeed_hopf _ (hr a) (hn a) h)
    exact ⟨q, hqc, hqd, hqh, Or.inr ⟨hqa, hqa ▸ southSeed_margin _ h⟩⟩

/-- A smooth unit spin curve supplies both its derivative and the finite-interval bound.
The initial point is generated by a positive-margin chart. This existential
statement does not provide a computable bound or smooth dependence on parameters. -/
theorem smooth_horizontal_lift_exists {s : ℝ → ℍ} {a b : ℝ} (hab : a ≤ b)
    (hs : ContDiff ℝ ∞ s) (hr : ∀ t, (s t).re=0) (hn : ∀ t, ‖s t‖=1) :
    ∃ q : ℝ → ℍ, ContinuousOn q (Icc a b) ∧
      (∀ t ∈ Icc a b,
        HasDerivWithinAt q (q t*horizontalCoefficient (s t) (deriv s t)) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, ‖q t‖=1 ∧ hopf (q t)=s t) ∧
      ((q a=northSeed (s a) ∧ (1/2 : ℝ)<(q a).re) ∨
       (q a=southSeed (s a) ∧ (1/2 : ℝ)<(q a).imJ)) := by
  have hd : ContinuousOn (deriv s) (Icc a b) :=
    (hs.continuous_deriv (by simp)).continuousOn
  obtain ⟨M, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn hd
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb a ⟨le_rfl, hab⟩)
  exact horizontal_lift_exists hab (fun t => (hs.differentiable (by simp) t).hasDerivAt)
    hr hn hd ⟨M, hM⟩ hb

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
