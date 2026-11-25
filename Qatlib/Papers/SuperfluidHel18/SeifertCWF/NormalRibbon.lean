/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.ClosedWrithe
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.GaussHomotopy

import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Embedded narrow normal ribbons of closed curves

[Kedia2018SuperfluidHelicity], Section IV and Eq. (5),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
A regular simple closed curve and a nonvanishing periodic normal
determine an injective strip at sufficiently small widths. Projection
onto the tangent separates nearby parameters, while compactness
separates distant chords. The Gauss integral of the centerline and a
positive-width edge is independent of the width in this range.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfluidHel18.SeifertCWF

open Qatlib.Papers.KnottedLight08.HopfField (dot3)
open Qatlib.Papers.SuperfluidHel18.CenterlineCL
open Set
open scoped Real

/-- The normal offset at a signed ribbon width. -/
def normalRibbonPoint (γ N : ℝ → Fin 3 → ℝ) (a s : ℝ) : Fin 3 → ℝ :=
  γ s + a • N s

/-- Differentiating an offset in the centerline parameter holds the width fixed. -/
theorem hasDerivAt_normalRibbonPoint {γ N : ℝ → Fin 3 → ℝ} {s a : ℝ}
    (hγ : DifferentiableAt ℝ γ s) (hN : DifferentiableAt ℝ N s) :
    HasDerivAt (normalRibbonPoint γ N a) (deriv γ s + a • deriv N s) s :=
  hγ.hasDerivAt.fun_add (hN.hasDerivAt.const_smul a)

/-- The strip inherits the common period of the centerline and normal. -/
private theorem normalRibbonPoint_periodic {γ N : ℝ → Fin 3 → ℝ}
    (hγ : Function.Periodic γ (2 * π)) (hN : Function.Periodic N (2 * π)) (a : ℝ) :
    Function.Periodic (normalRibbonPoint γ N a) (2 * π) := by
  intro s
  simp only [normalRibbonPoint, hγ s, hN s]

/-- Compactness of one period bounds any continuous periodic vector function. -/
theorem periodic_norm_bound {f : ℝ → Fin 3 → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f (2 * π)) : ∃ B : ℝ, ∀ s, ‖f s‖ ≤ B := by
  obtain ⟨B, hB⟩ := (hp.compact_of_continuous Real.two_pi_pos.ne' hf).isBounded.exists_norm_le
  exact ⟨B, fun s => hB _ (mem_range_self s)⟩

/-- Periodicity and regularity give a positive lower bound for squared Euclidean speed. -/
private theorem periodic_speed_sq_lower {γ : ℝ → Fin 3 → ℝ} (hγ : ContDiff ℝ 2 γ)
    (hp : Function.Periodic γ (2 * π)) (hreg : ∀ s, deriv γ s ≠ 0) :
    ∃ c > 0, ∀ s, c ≤ dot3 (deriv γ s) (deriv γ s) := by
  have hT : ContDiff ℝ 1 (deriv γ) := ContDiff.deriv' hγ
  have hTp := periodic_deriv_curve hp (hγ.differentiable (by norm_num))
  have hspeed : Function.Periodic (fun s => ‖deriv γ s‖) (2 * π) :=
    fun s => congrArg norm (hTp s)
  obtain ⟨τ, ⟨s₀, hs₀⟩, hmin⟩ :=
    (hspeed.compact_of_continuous Real.two_pi_pos.ne' hT.continuous.norm).exists_isMinOn
      (range_nonempty _) continuous_id.continuousOn
  have hτ : 0 < τ := hs₀ ▸ norm_pos_iff.mpr (hreg s₀)
  refine ⟨τ ^ 2, by positivity, ?_⟩
  intro s
  have hle : τ ≤ ‖deriv γ s‖ := hmin (mem_range_self s)
  calc
    _ ≤ euclideanLength (deriv γ s) ^ 2 :=
      pow_le_pow_left₀ hτ.le (hle.trans (norm_le_euclideanLength _)) 2
    _ = dot3 (deriv γ s) (deriv γ s) := by
      rw [euclideanLength, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      simp [dot3, pow_two]

/-- The tangent deviation estimate applies on either side of the base point. -/
private theorem tangent_deviation_abs {γ : ℝ → Fin 3 → ℝ} (hγ : ContDiff ℝ 2 γ)
    {B : ℝ} (hB : ∀ s, ‖deriv (deriv γ) s‖ ≤ B) (s t : ℝ) :
    ‖deriv γ s - deriv γ t‖ ≤ B * |s - t| := by
  rcases le_total t s with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact norm_deriv_sub_le γ hγ hB s t h
  · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
    exact norm_deriv_sub_le γ hγ hB t s h

/-- The tangent projection of a narrow edge is strictly increasing
on a common parameter neighborhood of the base point. -/
private theorem tangent_projection_strictMono {γ N : ℝ → Fin 3 → ℝ}
    (hγ : ContDiff ℝ 2 γ) (hN : Differentiable ℝ N) {c B δ a : ℝ}
    (hc : 0 < c) (hB : 0 < B)
    (hspeed : ∀ s, c ≤ dot3 (deriv γ s) (deriv γ s))
    (hT : ∀ s, ‖deriv γ s‖ ≤ B) (hT' : ∀ s, ‖deriv (deriv γ) s‖ ≤ B)
    (hN' : ∀ s, ‖deriv N s‖ ≤ B) (hδ : 6 * B ^ 2 * δ ≤ c / 2)
    (ha : |a| ≤ δ) (t : ℝ) :
    StrictMonoOn (fun s => dot3 (deriv γ t) (normalRibbonPoint γ N a s))
      (Icc (t - δ) (t + δ)) := by
  let L := dot3CLM (deriv γ t)
  have hder (s : ℝ) : HasDerivAt
      (fun u => dot3 (deriv γ t) (normalRibbonPoint γ N a u))
      (dot3 (deriv γ t) (deriv γ s + a • deriv N s)) s := by
    have hd := L.hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_normalRibbonPoint (a := a) (hγ.differentiable (by norm_num) s) (hN s))
    simpa only [L, Function.comp_def, dot3CLM_apply] using hd
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact (continuous_iff_continuousAt.mpr fun s => (hder s).continuousAt).continuousOn
  · intro s hs
    have hs' : s ∈ Icc (t - δ) (t + δ) := interior_subset hs
    have hst : |s - t| ≤ δ := abs_le.mpr ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
    let w := (deriv γ s - deriv γ t) + a • deriv N s
    have hw : ‖w‖ ≤ B * δ + δ * B := by
      calc
        _ ≤ ‖deriv γ s - deriv γ t‖ + ‖a • deriv N s‖ := norm_add_le _ _
        _ ≤ _ := by
          rw [norm_smul, Real.norm_eq_abs]
          exact add_le_add
            ((tangent_deviation_abs hγ hT' s t).trans (mul_le_mul_of_nonneg_left hst hB.le))
            (mul_le_mul ha (hN' s) (norm_nonneg _) ((abs_nonneg a).trans ha))
    have hdot : |dot3 (deriv γ t) w| ≤ c / 2 := by
      calc
        _ ≤ 3 * ‖deriv γ t‖ * ‖w‖ := abs_dot3_le _ _
        _ ≤ (3 * B) * (B * δ + δ * B) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hT t) (by norm_num)) hw
            (norm_nonneg _) (by positivity)
        _ = 6 * B ^ 2 * δ := by ring
        _ ≤ _ := hδ
    rw [(hder s).deriv]
    have he : dot3 (deriv γ t) (deriv γ s + a • deriv N s) =
        dot3 (deriv γ t) (deriv γ t) + dot3 (deriv γ t) w := by
      rw [← dot3CLM_apply, ← dot3CLM_apply, ← dot3CLM_apply, ← map_add]
      congr 1
      dsimp only [w]
      abel
    rw [he]
    linarith only [hspeed t, (abs_le.mp hdot).1, hc]

/-- Equality of offsets of the same base point determines the width
when the normal is nonzero. -/
private theorem normalRibbon_width_eq {γ N : ℝ → Fin 3 → ℝ} {a b t : ℝ}
    (hn : N t ≠ 0) (he : normalRibbonPoint γ N a t = normalRibbonPoint γ N b t) : a = b := by
  have hsmul : a • N t = b • N t := add_left_cancel he
  have hzero : (a - b) • N t = 0 := by rw [sub_smul, hsmul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hn)

/-- Nearby parameters cannot give equal ribbon points unless their
base points and widths agree. -/
private theorem nearby_normalRibbonPoint_eq {γ N : ℝ → Fin 3 → ℝ} {a b s t δ : ℝ}
    (hδ : 0 ≤ δ) (hst : |s - t| ≤ δ)
    (hmono : StrictMonoOn (fun u => dot3 (deriv γ t) (normalRibbonPoint γ N a u))
      (Icc (t - δ) (t + δ)))
    (horth : dot3 (deriv γ t) (N t) = 0) (hn : N t ≠ 0)
    (he : normalRibbonPoint γ N a s = normalRibbonPoint γ N b t) :
    s = t ∧ a = b := by
  have hs : s ∈ Icc (t - δ) (t + δ) := by
    obtain ⟨hl, hh⟩ := abs_le.mp hst
    exact ⟨by linarith, by linarith⟩
  have ht : t ∈ Icc (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
  have hproj (w : ℝ) : dot3 (deriv γ t) (normalRibbonPoint γ N w t) =
      dot3 (deriv γ t) (γ t) := by
    rw [normalRibbonPoint, ← dot3CLM_apply, map_add, dot3CLM_apply,
      dot3CLM_apply, dot3_smul_right, horth, mul_zero, add_zero]
  have he' := congrArg (dot3 (deriv γ t)) he
  have hst' : s = t := hmono.injOn hs ht
    (he'.trans ((hproj b).trans (hproj a).symm))
  exact ⟨hst', normalRibbon_width_eq hn (hst' ▸ he)⟩

/-- A simple regular periodic centerline with a periodic nonvanishing
normal has an injective normal strip at sufficiently small signed
widths, up to the periodic identification of the centerline. -/
theorem exists_normalRibbon_injective {γ N : ℝ → Fin 3 → ℝ}
    (hγ : ContDiff ℝ 2 γ) (hN : ContDiff ℝ 1 N)
    (hpγ : Function.Periodic γ (2 * π)) (hpN : Function.Periodic N (2 * π))
    (hinj : InjOn γ (Ico 0 (2 * π))) (hreg : ∀ s, deriv γ s ≠ 0)
    (hNnz : ∀ s, N s ≠ 0) (horth : ∀ s, dot3 (deriv γ s) (N s) = 0) :
    ∃ ε > 0, ∀ a b s t, |a| < ε → |b| < ε →
      normalRibbonPoint γ N a s = normalRibbonPoint γ N b t → γ s = γ t ∧ a = b := by
  have hT : ContDiff ℝ 1 (deriv γ) := ContDiff.deriv' hγ
  have hpT := periodic_deriv_curve hpγ (hγ.differentiable (by norm_num))
  obtain ⟨B₁, hB₁⟩ := periodic_norm_bound hT.continuous hpT
  obtain ⟨B₂, hB₂⟩ := periodic_norm_bound hT.continuous_deriv_one
    (periodic_deriv_curve hpT (hT.differentiable (by norm_num)))
  obtain ⟨B₃, hB₃⟩ := periodic_norm_bound hN.continuous hpN
  obtain ⟨B₄, hB₄⟩ := periodic_norm_bound hN.continuous_deriv_one
    (periodic_deriv_curve hpN (hN.differentiable (by norm_num)))
  let B := max 1 (max (max B₁ B₂) (max B₃ B₄))
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hb₁ : ∀ s, ‖deriv γ s‖ ≤ B := fun s =>
    (hB₁ s).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _)))
  have hb₂ : ∀ s, ‖deriv (deriv γ) s‖ ≤ B := fun s =>
    (hB₂ s).trans ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _)))
  have hb₃ : ∀ s, ‖N s‖ ≤ B := fun s =>
    (hB₃ s).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hb₄ : ∀ s, ‖deriv N s‖ ≤ B := fun s =>
    (hB₄ s).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  obtain ⟨c, hc, hspeed⟩ := periodic_speed_sq_lower hγ hpγ hreg
  let δ := min π (c / (12 * B ^ 2))
  have hδ : 0 < δ := lt_min Real.pi_pos (by positivity)
  have hδπ : δ ≤ π := min_le_left _ _
  have hδc : 6 * B ^ 2 * δ ≤ c / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 12 * B ^ 2)).mp
      (show δ ≤ c / (12 * B ^ 2) from min_le_right _ _)
    nlinarith only [h]
  obtain ⟨m, hm, hmfar⟩ := exists_closed_curve_chord_min hγ.continuous hpγ hinj hδ hδπ
  let ε := min δ (m / (4 * B))
  have hε : 0 < ε := lt_min hδ (by positivity)
  refine ⟨ε, hε, ?_⟩
  intro a b s t ha hb he
  have hnear (u v : ℝ) (hgap : |u - v| ≤ δ)
      (heq : normalRibbonPoint γ N a u = normalRibbonPoint γ N b v) : γ u = γ v ∧ a = b := by
    have hmono := tangent_projection_strictMono hγ (hN.differentiable (by norm_num)) hc hB
      hspeed hb₁ hb₂ hb₄ hδc (ha.le.trans (min_le_left _ _)) v
    obtain ⟨h, hw⟩ := nearby_normalRibbonPoint_eq hδ.le hgap hmono (horth v) (hNnz v) heq
    exact ⟨congrArg γ h, hw⟩
  let u := toIcoMod Real.two_pi_pos 0 s
  let v := toIcoMod Real.two_pi_pos 0 t
  have hu : u ∈ Icc 0 (2 * π) := Ico_subset_Icc_self (toIcoMod_mem_Ico' _ _)
  have hv : v ∈ Icc 0 (2 * π) := Ico_subset_Icc_self (toIcoMod_mem_Ico' _ _)
  have hmod {f : ℝ → Fin 3 → ℝ} (hf : Function.Periodic f (2 * π)) (x : ℝ) :
      f (toIcoMod Real.two_pi_pos 0 x) = f x := by
    exact hf.sub_zsmul_eq _
  have he' : normalRibbonPoint γ N a u = normalRibbonPoint γ N b v := by
    rw [show normalRibbonPoint γ N a u = normalRibbonPoint γ N a s from
      hmod (normalRibbonPoint_periodic hpγ hpN a) s,
      show normalRibbonPoint γ N b v = normalRibbonPoint γ N b t from
      hmod (normalRibbonPoint_periodic hpγ hpN b) t]
    exact he
  rw [← hmod hpγ s, ← hmod hpγ t]
  by_cases hclose : |u - v| ≤ δ
  · exact hnear u v hclose he'
  by_cases hfar : |u - v| ≤ 2 * π - δ
  · have hf := hmfar (u, v) ⟨hu, hv⟩ (by simpa only [abs_sub_comm] using (le_of_not_ge hclose))
        (by simpa only [abs_sub_comm] using hfar)
    have hc' : γ u - γ v = b • N v - a • N u := by
      dsimp only [normalRibbonPoint] at he'
      linear_combination he'
    have hbnd : ‖γ u - γ v‖ ≤ (|a| + |b|) * B := by
      rw [hc']
      calc
        _ ≤ ‖b • N v‖ + ‖a • N u‖ := norm_sub_le _ _
        _ ≤ |b| * B + |a| * B := by
          simp only [norm_smul, Real.norm_eq_abs]
          exact add_le_add (mul_le_mul_of_nonneg_left (hb₃ v) (abs_nonneg b))
            (mul_le_mul_of_nonneg_left (hb₃ u) (abs_nonneg a))
        _ = _ := by ring
    have hw : (|a| + |b|) * B ≤ m / 2 := by
      have hε' : ε * (4 * B) ≤ m :=
        (le_div_iff₀ (by positivity : 0 < 4 * B)).mp (min_le_right _ _)
      nlinarith only [hε', mul_le_mul_of_nonneg_right (add_le_add ha.le hb.le) hB.le]
    linarith only [hf, hbnd, hw, hm]
  · rcases le_total v u with huv | huv
    · rw [abs_of_nonneg (sub_nonneg.mpr huv)] at hfar
      have hgap : |(u - 2 * π) - v| ≤ δ :=
        abs_le.mpr ⟨by linarith, by linarith [hu.2, hv.1, hδ.le]⟩
      have hshift : normalRibbonPoint γ N a (u - 2 * π) = normalRibbonPoint γ N a u :=
        (normalRibbonPoint_periodic hpγ hpN a).sub_eq u
      obtain ⟨h, hw⟩ := hnear (u - 2 * π) v hgap (hshift.trans he')
      exact ⟨(hpγ.sub_eq u).symm.trans h, hw⟩
    · rw [abs_of_nonpos (sub_nonpos.mpr huv)] at hfar
      have hgap : |(u + 2 * π) - v| ≤ δ :=
        abs_le.mpr ⟨by linarith [hu.1, hv.2, hδ.le], by linarith⟩
      have hshift := normalRibbonPoint_periodic hpγ hpN a u
      obtain ⟨h, hw⟩ := hnear (u + 2 * π) v hgap (hshift.trans he')
      exact ⟨(hpγ u).symm.trans h, hw⟩

/-- Affine interpolation stays between the two endpoint widths. -/
private theorem width_between (a b t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    min a b ≤ (1 - t) * a + t * b ∧ (1 - t) * a + t * b ≤ max a b := by
  have ht' := sub_nonneg.mpr ht.2
  constructor
  · nlinarith only [mul_nonneg ht' (sub_nonneg.mpr (min_le_left a b)),
      mul_nonneg ht.1 (sub_nonneg.mpr (min_le_right a b))]
  · nlinarith only [mul_nonneg ht' (sub_nonneg.mpr (le_max_left a b)),
      mul_nonneg ht.1 (sub_nonneg.mpr (le_max_right a b))]

/-- Interpolating two ordered width pairs in a narrow strip preserves
the Gauss integral of their actual oriented curves. -/
private theorem normalRibbon_gaussLinking_interpolate {γ N : ℝ → Fin 3 → ℝ}
    (hγ : ContDiff ℝ 2 γ) (hN : ContDiff ℝ 2 N)
    (hpγ : Function.Periodic γ (2 * π)) (hpN : Function.Periodic N (2 * π))
    {ε : ℝ}
    (hstrip : ∀ a b s t, |a| < ε → |b| < ε →
      normalRibbonPoint γ N a s = normalRibbonPoint γ N b t → γ s = γ t ∧ a = b)
    {a b c d : ℝ} (ha : |a| < ε) (hb : |b| < ε) (hc : |c| < ε) (hd : |d| < ε)
    (hab : a < b) (hcd : c < d) :
    gaussLinking (normalRibbonPoint γ N a) (normalRibbonPoint γ N b) =
      gaussLinking (normalRibbonPoint γ N c) (normalRibbonPoint γ N d) := by
  let w (x y t : ℝ) := (1 - t) * x + t * y
  let Γ (x y : ℝ) (q : ℝ × ℝ) := normalRibbonPoint γ N (w x y q.1) q.2
  have hΓ (x y : ℝ) : ContDiff ℝ 2 (Γ x y) := by
    have hw : ContDiff ℝ 2 (fun p : ℝ × ℝ => w x y p.1) := by dsimp only [w]; fun_prop
    exact (hγ.comp contDiff_snd).add (hw.smul (hN.comp contDiff_snd))
  have hw_lt (x y t : ℝ) (hx : |x| < ε) (hy : |y| < ε)
      (ht : t ∈ Icc (0 : ℝ) 1) : |w x y t| < ε := by
    rw [abs_lt] at hx hy ⊢
    obtain ⟨hl, hu⟩ := width_between x y t ht
    exact ⟨(lt_min hx.1 hy.1).trans_le hl, hu.trans_lt (max_lt hx.2 hy.2)⟩
  have hne (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (s u : ℝ) :
      Γ a c (t, s) ≠ Γ b d (t, u) := by
    intro he
    have hw := (hstrip _ _ _ _ (hw_lt a c t ha hc ht) (hw_lt b d t hb hd ht) he).2
    have hg := (lt_min (sub_pos.mpr hab) (sub_pos.mpr hcd)).trans_le
      (width_between (b - a) (d - c) t ht).1
    dsimp only [w] at hw
    linarith only [hg, hw]
  have h := gaussLinking_eq_on_interval (Γ a c) (Γ b d) (by norm_num : (0 : ℝ) ≤ 1)
    (hΓ a c).contDiffOn (hΓ b d).contDiffOn hne
    (fun t _ => normalRibbonPoint_periodic hpγ hpN (w a c t))
    (fun t _ => normalRibbonPoint_periodic hpγ hpN (w b d t))
  simpa only [Γ, w, sub_zero, sub_self, one_mul, zero_mul, add_zero, zero_add] using h

/-- A sufficiently thin strip of a smooth closed normal ribbon is
injective on a half-open period and every ordered pair of lanes has
the same Gauss linking integral. This applies in particular to the
centerline and any positive-width edge. -/
theorem exists_normalRibbon_gaussLinking_stable {γ N : ℝ → Fin 3 → ℝ}
    (hγ : ContDiff ℝ 2 γ) (hN : ContDiff ℝ 2 N)
    (hpγ : Function.Periodic γ (2 * π)) (hpN : Function.Periodic N (2 * π))
    (hinj : InjOn γ (Ico 0 (2 * π))) (hreg : ∀ s, deriv γ s ≠ 0)
    (hNnz : ∀ s, N s ≠ 0) (horth : ∀ s, dot3 (deriv γ s) (N s) = 0) :
    ∃ ε > 0,
      InjOn (fun p : ℝ × ℝ => normalRibbonPoint γ N p.2 p.1)
        (Ico (0 : ℝ) (2 * π) ×ˢ Ioo (-ε) ε) ∧
      (∀ a b s t, |a| < ε → |b| < ε → a ≠ b →
        normalRibbonPoint γ N a s ≠ normalRibbonPoint γ N b t) ∧
      (∀ a b c d, |a| < ε → |b| < ε → |c| < ε → |d| < ε → a < b → c < d →
        gaussLinking (normalRibbonPoint γ N a) (normalRibbonPoint γ N b) =
          gaussLinking (normalRibbonPoint γ N c) (normalRibbonPoint γ N d)) := by
  obtain ⟨ε, hε, hstrip⟩ :=
    exists_normalRibbon_injective hγ (hN.of_le (by norm_num)) hpγ hpN hinj hreg hNnz horth
  refine ⟨ε, hε, ?_, ?_, ?_⟩
  · intro p hp q hq he
    obtain ⟨hbase, hwidth⟩ := hstrip p.2 q.2 p.1 q.1 (abs_lt.mpr hp.2) (abs_lt.mpr hq.2) he
    exact Prod.ext (hinj hp.1 hq.1 hbase) hwidth
  · intro a b s t ha hb hab he
    exact hab (hstrip a b s t ha hb he).2
  · exact fun _ _ _ _ ha hb hc hd hab hcd =>
      normalRibbon_gaussLinking_interpolate hγ hN hpγ hpN hstrip ha hb hc hd hab hcd

end Qatlib.Papers.SuperfluidHel18.SeifertCWF
