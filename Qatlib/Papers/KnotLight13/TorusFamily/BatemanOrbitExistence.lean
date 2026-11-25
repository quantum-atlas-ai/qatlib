/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPhysicalOrbits

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Complete Bateman magnetic orbits

The normalized sphere flow is constructed from a bounded extension of
its field. This file uses compatibility of Picard–Lindelöf solutions
on increasing finite intervals.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set Metric

/-- A globally Lipschitz bounded autonomous field has a complete
trajectory through every prescribed point. -/
theorem exists_globalIntegralCurve_of_lipschitz_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {V : E → E} {K L : NNReal} (hK : LipschitzWith K V) (hL : ∀ x, ‖V x‖ ≤ L)
    (x₀ : E) : ∃ γ : ℝ → E, γ 0 = x₀ ∧ IsIntegralCurve γ (fun _ => V) := by
  classical
  let R : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hR (n : ℕ) : 0 < R n := by unfold R; positivity
  have h0 (n : ℕ) : (0 : ℝ) ∈ Ioo (-(R n)) (R n) := ⟨neg_neg_of_pos (hR n), hR n⟩
  have hlocal (n : ℕ) :
      ∃ g : ℝ → E, g 0 = x₀ ∧
        ∀ t ∈ Ioo (-(R n)) (R n), HasDerivAt g (V (g t)) t := by
    let ℓ : NNReal := ⟨R n, (hR n).le⟩
    let t₀ : Icc (-(R n)) (R n) := ⟨0, Ioo_subset_Icc_self (h0 n)⟩
    have hp : IsPicardLindelof (fun _ => V) t₀ x₀ (L * ℓ) 0 L K := by
      apply IsPicardLindelof.of_time_independent (fun x _ => hL x) hK.lipschitzOnWith
      simp [ℓ, t₀]
      change (L : ℝ) * R n ≤ (L : ℝ) * R n
      exact le_rfl
    obtain ⟨g, hg₀, hg⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨g, hg₀, fun t ht => (hg t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩
  choose g hg₀ hg using hlocal
  have hagree (n m : ℕ) {s : ℝ}
      (hn : s ∈ Ioo (-(R n)) (R n)) (hm : s ∈ Ioo (-(R m)) (R m)) :
      g n s = g m s := by
    let A := max (-(R n)) (-(R m))
    let B := min (R n) (R m)
    have ha (t : ℝ) (ht : t ∈ Ioo A B) : t ∈ Ioo (-(R n)) (R n) :=
      ⟨(le_max_left _ _).trans_lt ht.1, ht.2.trans_le (min_le_left _ _)⟩
    have hb (t : ℝ) (ht : t ∈ Ioo A B) : t ∈ Ioo (-(R m)) (R m) :=
      ⟨(le_max_right _ _).trans_lt ht.1, ht.2.trans_le (min_le_right _ _)⟩
    have ht₀ : (0 : ℝ) ∈ Ioo A B :=
      ⟨max_lt (h0 n).1 (h0 m).1, lt_min (h0 n).2 (h0 m).2⟩
    exact ODE_solution_unique_of_mem_Ioo (v := fun _ => V) (s := fun _ => univ)
      (fun _ _ => hK.lipschitzOnWith) ht₀
      (fun t ht => ⟨hg n t (ha t ht), mem_univ _⟩)
      (fun t ht => ⟨hg m t (hb t ht), mem_univ _⟩)
      ((hg₀ n).trans (hg₀ m).symm) ⟨max_lt hn.1 hm.1, lt_min hn.2 hm.2⟩
  have hcover (t : ℝ) : ∃ n, t ∈ Ioo (-(R n)) (R n) := by
    obtain ⟨n, hn⟩ := exists_nat_gt |t|
    exact ⟨n, ⟨by have := neg_abs_le t; dsimp [R]; linarith,
      by have := le_abs_self t; dsimp [R]; linarith⟩⟩
  choose n hn using hcover
  let γ := fun t => g (n t) t
  refine ⟨γ, hg₀ _, ?_⟩
  intro t
  have hEq : γ =ᶠ[nhds t] g (n t) := by
    filter_upwards [Ioo_mem_nhds (hn t).1 (hn t).2] with s hs
    exact hagree (n s) (n t) (hn s) hs
  exact ((hg (n t) t (hn t)).congr_of_eventuallyEq hEq).congr_deriv rfl

open scoped ComplexConjugate

/-- The derivative of squared modulus, in terms of the original complex
coordinate and velocity. -/
private theorem hasDerivAt_orbitNormSq {z : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (h : HasDerivAt z v t) :
    HasDerivAt (fun s => Complex.normSq (z s)) (2 * (conj (z t) * v).re) t := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h
  have hd := (hr.mul hr).fun_add (hi.mul hi)
  change HasDerivAt (fun s => (z s).re * (z s).re + (z s).im * (z s).im)
    (v.re * (z t).re + (z t).re * v.re + (v.im * (z t).im + (z t).im * v.im)) t at hd
  have he : v.re * (z t).re + (z t).re * v.re + (v.im * (z t).im + (z t).im * v.im) =
      2 * (conj (z t) * v).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simpa only [Complex.normSq_apply, he] using hd

/-- The total squared radius has zero derivative along any real multiple
of the normalized sphere magnetic field, including a cut-off field. -/
theorem hasDerivAt_batemanSphereMagnetic_sumNormSq (p q : ℕ) {w : ℝ → ℂ × ℂ}
    {t : ℝ} {ν : ℝ} (hw : HasDerivAt w (ν • batemanSphereMagnetic p q (w t)) t) :
    HasDerivAt (fun s => Complex.normSq (w s).1 + Complex.normSq (w s).2) 0 t := by
  let z := w t
  let V := batemanSphereMagnetic p q z
  have h₁ : HasDerivAt (fun s => (w s).1) (ν • V.1) t := hw.fst
  have h₂ : HasDerivAt (fun s => (w s).2) (ν • V.2) t := hw.snd
  have hdot : conj z.1 * V.1 + conj z.2 * V.2 = 0 := by
    dsimp only [V, batemanSphereMagnetic, batemanSphereElectric]
    simp only [map_mul]
    ring
  have hsum : conj z.1 * (ν • V.1) + conj z.2 * (ν • V.2) = 0 := by
    simp only [Complex.real_smul]
    linear_combination (ν : ℂ) * hdot
  have hre := congrArg Complex.re hsum
  rw [Complex.add_re, Complex.zero_re] at hre
  exact ((hasDerivAt_orbitNormSq h₁).fun_add (hasDerivAt_orbitNormSq h₂)).congr_deriv (by
    change 2 * (conj z.1 * (ν • V.1)).re + 2 * (conj z.2 * (ν • V.2)).re = 0
    linarith only [hre])

/-- Every unit-sphere point has a complete normalized magnetic trajectory.
A compactly supported extension agrees with the polynomial field on
the invariant sphere. -/
theorem exists_batemanSphereMagneticIntegralCurve (p q : ℕ) (z₀ : ℂ × ℂ)
    (hz₀ : Complex.normSq z₀.1 + Complex.normSq z₀.2 = 1) :
    ∃ w : ℝ → ℂ × ℂ, w 0 = z₀ ∧
      IsIntegralCurve w (fun _ => batemanSphereMagnetic p q) ∧
      ∀ t, Complex.normSq (w t).1 + Complex.normSq (w t).2 = 1 := by
  let χ : ContDiffBump (0 : ℂ × ℂ) := ⟨1, 2, by norm_num, by norm_num⟩
  let V := batemanSphereMagnetic p q
  let F := fun z : ℂ × ℂ => χ z • V z
  have hχdiff : ContDiff ℝ 1 (χ : (ℂ × ℂ) → ℝ) := χ.contDiff
  have hF : ContDiff ℝ 1 F := hχdiff.smul ((contDiff_batemanSphereMagnetic p q).of_le le_top)
  have hS : HasCompactSupport F := χ.hasCompactSupport.smul_right (f' := V)
  obtain ⟨K, hK⟩ := hF.lipschitzWith_of_hasCompactSupport hS (by simp)
  obtain ⟨L, hL⟩ := hS.exists_bound_of_continuous hF.continuous
  let Lbound : NNReal := ⟨max L 0, le_max_right _ _⟩
  obtain ⟨w, hw₀, hw⟩ := exists_globalIntegralCurve_of_lipschitz_bounded
    hK (L := Lbound) (fun z => (hL z).trans (le_max_left _ _)) z₀
  have hd (t : ℝ) : HasDerivAt (fun s => Complex.normSq (w s).1 + Complex.normSq (w s).2) 0 t :=
    hasDerivAt_batemanSphereMagnetic_sumNormSq p q (hw t)
  have hs (t : ℝ) : Complex.normSq (w t).1 + Complex.normSq (w t).2 = 1 := by
    have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
    change Complex.normSq (w t).1 + Complex.normSq (w t).2 =
      Complex.normSq (w 0).1 + Complex.normSq (w 0).2 at h
    rwa [hw₀, hz₀] at h
  refine ⟨w, hw₀, ?_, hs⟩
  intro t
  have hb : w t ∈ closedBall (0 : ℂ × ℂ) 1 := by
    rw [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    have h := hs t
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
    constructor <;> by_contra! hn <;>
      nlinarith [pow_lt_pow_left₀ hn (by norm_num : (0 : ℝ) ≤ 1) (by decide : (2 : ℕ) ≠ 0)]
  have hχ : χ (w t) = 1 := χ.one_of_mem_closedBall hb
  have h := hw t
  change HasDerivAt w (χ (w t) • batemanSphereMagnetic p q (w t)) t at h
  rwa [hχ, one_smul] at h

/-- The real product label is conserved by the complete normalized magnetic
flow, since the product derivative is purely imaginary. -/
theorem batemanSphereMagneticIntegralCurve_realLevel {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {w : ℝ → ℂ × ℂ} (hw : IsIntegralCurve w (fun _ => batemanSphereMagnetic p q)) (t : ℝ) :
    ((w t).1 ^ p * (w t).2 ^ q).re = ((w 0).1 ^ p * (w 0).2 ^ q).re := by
  let F := fun s => ((w s).1 ^ p * (w s).2 ^ q).re
  have hd (s : ℝ) : HasDerivAt F 0 s := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_batemanSphereMagnetic_product hp hq (hw s))
    change HasDerivAt F _ s at h
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero] using h
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0

/-- Every point of a normalized magnetic product level has a complete
normalized trajectory in that level. -/
theorem exists_batemanSphereMagneticIntegralCurve_on_level {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {c : ℝ} {z₀ : ℂ × ℂ} (hz : z₀ ∈ poweredSphereRealLevel p q c) :
    ∃ w : ℝ → ℂ × ℂ, w 0 = z₀ ∧ IsIntegralCurve w (fun _ => batemanSphereMagnetic p q) ∧
      ∀ s, w s ∈ poweredSphereRealLevel p q c := by
  obtain ⟨w, hw₀, hw, hn⟩ := exists_batemanSphereMagneticIntegralCurve p q z₀ hz.1
  refine ⟨w, hw₀, hw, fun s => ⟨hn s, ?_⟩⟩
  rw [batemanSphereMagneticIntegralCurve_realLevel hp hq hw s, hw₀]
  exact hz.2

/-- Every point of a coprime strict intermediate physical magnetic torus
has a complete magnetic trajectory on its prescribed time slice. -/
theorem exists_batemanMagneticIntegralCurve_on_level
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    (t : ℝ) {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q)
    {x : ℝ × ℝ × ℝ} (hx : x ∈ poweredPhysicalRealLevel p q t c) :
    ∃ γ : ℝ → ℝ × ℝ × ℝ, γ 0 = x ∧
      IsIntegralCurve γ (fun _ => batemanMagneticVector p q t) ∧
      ∀ s, γ s ∈ poweredPhysicalRealLevel p q t c := by
  let E := poweredSphereRealLevelToPhysical (p := p) hq t h₀
  let z := E.symm ⟨x, hx⟩
  obtain ⟨w, hw₀, hw, hwlev⟩ :=
    exists_batemanSphereMagneticIntegralCurve_on_level hp hq z.property
  obtain ⟨e, hγ, hγ₀, hγlev⟩ := batemanSphereMagneticIntegralCurve_physical hp hq hpq t h₀ hc hw hwlev
  refine ⟨_, ?_, hγ, hγlev⟩
  rw [hγ₀, hw₀]
  exact congrArg Subtype.val (E.apply_symm_apply ⟨x, hx⟩)

open scoped Real in
/-- Every point of a coprime strict intermediate physical electric torus
has a complete electric trajectory. -/
theorem exists_batemanElectricIntegralCurve_on_level
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    (t : ℝ) {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q)
    {x : ℝ × ℝ × ℝ} (hx : x ∈ poweredPhysicalImagLevel p q t c) :
    ∃ γ : ℝ → ℝ × ℝ × ℝ, γ 0 = x ∧
      IsIntegralCurve γ (fun _ => batemanElectricVector p q t) ∧
      ∀ s, γ s ∈ poweredPhysicalImagLevel p q t c := by
  let θ := π / (2 * (q : ℝ))
  let R := batemanAxialHomeomorph θ
  let y := R.symm x
  have hy : y ∈ poweredPhysicalRealLevel p q t (-c) := by
    apply (poweredPhysicalLevel_axial_iff hq t c y).2
    change R (R.symm x) ∈ poweredPhysicalImagLevel p q t c
    rwa [R.apply_symm_apply]
  obtain ⟨g, hg₀, hg, hlev⟩ := exists_batemanMagneticIntegralCurve_on_level hp hq hpq t
    (neg_ne_zero.mpr h₀) (by rwa [abs_neg]) hy
  refine ⟨R ∘ g, ?_, ?_, fun s => (poweredPhysicalLevel_axial_iff hq t c (g s)).1 (hlev s)⟩
  · change R (g 0) = x
    rw [hg₀, R.apply_symm_apply]
  · intro s
    exact (hasDerivAt_batemanAxialRotation_curve θ (hg s)).congr_deriv
      (batemanAxialRotation_magnetic_to_electric p hq t (g s))

end Qatlib.Papers.KnotLight13.TorusFamily
