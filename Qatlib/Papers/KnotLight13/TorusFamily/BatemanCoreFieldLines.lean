/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanCoreVelocity
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanOrbitClock

import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Closed actual field lines on the extremal Bateman cores

[Kedia2013TyingKnots], p. 150404-3,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
From the core velocity bridge at the initial time, a general
circle-rate argument turns the constant-sign rate of the actual field
along the core circle into a global integral curve that covers the
whole core circle, moves with positive speed, closes after one lap,
and has lap time the integral of the reciprocal rate. The ray
transport then carries these closed core field lines to every physical
time slice with the Jacobian lap integral as the new period, and the
phase-root decomposition of the label covers arbitrary exponents by
their reduced coprime cores. A phase reduction against the half-open
fundamental interval shows that each lap time is the least positive
period and that every return time is an integral number of laps, for
the coprime circles, their transported copies on every slice, and the
gcd-component instances of arbitrary exponents. No closed-orbit
conclusion is assumed as a hypothesis anywhere.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set

local notation "Space" => ℝ × ℝ × ℝ

/-- A global integral curve of a positive-rate periodic
parametrization: it covers the whole image, closes after one lap, and
the lap time is the integral of the reciprocal rate. -/
theorem exists_periodicIntegralCurve_of_positive_rate
    {param vel : ℝ → Space} {W : Space → Space} {rate : ℝ → ℝ} {M : ℝ} (hM₀ : 0 < M)
    (hderiv : ∀ θ, HasDerivAt param (vel θ) θ)
    (hfield : ∀ θ, W (param θ) = rate θ • vel θ)
    (hcont : Continuous rate) (hper : Function.Periodic rate (2 * Real.pi))
    (hpper : Function.Periodic param (2 * Real.pi))
    (hpos : ∀ θ, 0 < rate θ) (hM : ∀ θ, rate θ ≤ M)
    (hinj : Set.InjOn param (Set.Ico 0 (2 * Real.pi))) :
    ∃ γ : ℝ → Space, ∃ T : ℝ,
      (∀ s, HasDerivAt γ (W (γ s)) s) ∧
      Set.range γ = Set.range param ∧
      0 < T ∧ T = ∫ θ in (0 : ℝ)..2 * Real.pi, (rate θ)⁻¹ ∧
      Function.Periodic γ T ∧
      Set.InjOn γ (Set.Ico 0 T) := by
  have hvcont : Continuous (fun θ => (rate θ)⁻¹) := hcont.inv₀ (fun θ => (hpos θ).ne')
  have hvper : Function.Periodic (fun θ => (rate θ)⁻¹) (2 * Real.pi) :=
    fun θ => by simp only [hper θ]
  have hMpos : 0 < M⁻¹ := inv_pos.mpr hM₀
  have hbound : ∀ s : ℝ, M⁻¹ ≤ (rate s)⁻¹ := fun s =>
    (inv_le_inv₀ hM₀ (hpos s)).mpr (hM s)
  have hclock := hasDerivAt_orbitClock hvcont
  let e := orbitClockOrderIso (fun θ => (rate θ)⁻¹) hvcont hMpos hbound
  have hfun : ∀ x : ℝ, e x = ∫ u in (0 : ℝ)..x, (rate u)⁻¹ := fun _ => rfl
  have hezero : e 0 = 0 := by rw [hfun]; exact intervalIntegral.integral_same
  have hP : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hshift : ∀ θ : ℝ, e (θ + 2 * Real.pi) = e θ + e (2 * Real.pi) := by
    intro θ
    have h := orbitClock_increment_of_periodic hclock hvper θ
    simp only [intervalIntegral.integral_same] at h
    rw [← hfun (θ + 2 * Real.pi), ← hfun θ, ← hfun (2 * Real.pi)] at h
    linarith
  refine ⟨fun s => param ((e.symm : ℝ → ℝ) s), e (2 * Real.pi), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    have hEsymm := hasDerivAt_orbitClockOrderIso_symm (fun θ => (rate θ)⁻¹) hvcont hMpos hbound s
    simp only at hEsymm
    have hcomp := (hderiv ((e.symm : ℝ → ℝ) s)).scomp s hEsymm
    refine hcomp.congr_deriv ?_
    rw [inv_inv]
    exact (hfield _).symm
  · show Set.range (fun s => param ((e.symm : ℝ → ℝ) s)) = Set.range param
    ext x
    simp only [Set.mem_range]
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · obtain ⟨s, hs⟩ := hs
      exact ⟨(e.symm : ℝ → ℝ) s, hs⟩
    · obtain ⟨θ, hθ⟩ := hs
      obtain ⟨u, hu⟩ := e.symm.surjective θ
      exact ⟨u, by rw [hu]; exact hθ⟩
  · have hmono := e.strictMono hP
    rwa [hezero] at hmono
  · rw [hfun]
  · intro s
    have hstep : (e.symm : ℝ → ℝ) (s + e (2 * Real.pi)) =
        (e.symm : ℝ → ℝ) s + 2 * Real.pi := by
      apply e.injective
      rw [e.apply_symm_apply, hshift, e.apply_symm_apply]
    show param ((e.symm : ℝ → ℝ) (s + e (2 * Real.pi))) = param ((e.symm : ℝ → ℝ) s)
    rw [hstep]
    exact hpper _
  · intro s₁ hs₁ s₂ hs₂ hγ
    have hmem : ∀ s : ℝ, s ∈ Set.Ico 0 (e (2 * Real.pi)) →
        (e.symm : ℝ → ℝ) s ∈ Set.Ico 0 (2 * Real.pi) := by
      intro s hs
      have h1 : (0 : ℝ) ≤ (e.symm : ℝ → ℝ) s := by
        refine (e.le_iff_le).mp ?_
        rw [hezero, e.apply_symm_apply]
        exact hs.1
      have h2 : (e.symm : ℝ → ℝ) s < 2 * Real.pi := by
        refine (e.lt_iff_lt).mp ?_
        rw [e.apply_symm_apply]
        exact hs.2
      exact ⟨h1, h2⟩
    exact e.symm.injective (hinj (hmem s₁ hs₁) (hmem s₂ hs₂) hγ)

/-- A global integral curve of a negative-rate periodic
parametrization: it covers the whole image against the parameter
direction, closes after one lap, and the lap time is the integral of
the reciprocal absolute rate. -/
theorem exists_periodicIntegralCurve_of_negative_rate
    {param vel : ℝ → Space} {W : Space → Space} {rate : ℝ → ℝ} {M : ℝ} (hM₀ : 0 < M)
    (hderiv : ∀ θ, HasDerivAt param (vel θ) θ)
    (hfield : ∀ θ, W (param θ) = rate θ • vel θ)
    (hcont : Continuous rate) (hper : Function.Periodic rate (2 * Real.pi))
    (hpper : Function.Periodic param (2 * Real.pi))
    (hneg : ∀ θ, rate θ < 0) (hM : ∀ θ, -M ≤ rate θ)
    (hinj : Set.InjOn param (Set.Ico 0 (2 * Real.pi))) :
    ∃ γ : ℝ → Space, ∃ T : ℝ,
      (∀ s, HasDerivAt γ (W (γ s)) s) ∧
      Set.range γ = Set.range param ∧
      0 < T ∧ T = ∫ θ in (0 : ℝ)..2 * Real.pi, (-rate θ)⁻¹ ∧
      Function.Periodic γ T ∧
      Set.InjOn γ (Set.Ico 0 T) := by
  have hvcont : Continuous (fun θ => (-rate θ)⁻¹) := (hcont.neg).inv₀
    (fun θ => (neg_pos.mpr (hneg θ)).ne')
  have hvper : Function.Periodic (fun θ => (-rate θ)⁻¹) (2 * Real.pi) :=
    fun θ => by simp only [hper θ]
  have hMpos : 0 < M⁻¹ := inv_pos.mpr hM₀
  have hbound : ∀ s : ℝ, M⁻¹ ≤ (-rate s)⁻¹ := fun s =>
    (inv_le_inv₀ hM₀ (neg_pos.mpr (hneg s))).mpr (by linarith [hM s])
  have hclock := hasDerivAt_orbitClock hvcont
  let e := orbitClockOrderIso (fun θ => (-rate θ)⁻¹) hvcont hMpos hbound
  have hfun : ∀ x : ℝ, e x = ∫ u in (0 : ℝ)..x, (-rate u)⁻¹ := fun _ => rfl
  have hezero : e 0 = 0 := by rw [hfun]; exact intervalIntegral.integral_same
  have hP : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hshift : ∀ θ : ℝ, e (θ + 2 * Real.pi) = e θ + e (2 * Real.pi) := by
    intro θ
    have h := orbitClock_increment_of_periodic hclock hvper θ
    simp only [intervalIntegral.integral_same] at h
    rw [← hfun (θ + 2 * Real.pi), ← hfun θ, ← hfun (2 * Real.pi)] at h
    linarith
  have hshift' : ∀ θ : ℝ, e (θ - 2 * Real.pi) = e θ - e (2 * Real.pi) := by
    intro θ
    have h2 := hshift (θ - 2 * Real.pi)
    rw [sub_add_cancel] at h2
    linarith
  have hm2 : e (-(2 * Real.pi)) = -e (2 * Real.pi) := by
    have h := hshift' 0
    simp only [hezero, zero_sub] at h
    exact h
  have hinjoc : Set.InjOn param (Set.Ioc (-(2 * Real.pi)) 0) := by
    intro a ha b hb hab
    have h0p : (0 : ℝ) ∈ Set.Ico 0 (2 * Real.pi) := ⟨le_rfl, hP⟩
    have key : ∀ x : ℝ, x ∈ Set.Ioc (-(2 * Real.pi)) 0 → x ≠ 0 →
        x + 2 * Real.pi ∈ Set.Ico 0 (2 * Real.pi) := by
      intro x hx hx0
      exact ⟨by linarith [hx.1], by linarith [hx.2, lt_of_le_of_ne hx.2 hx0]⟩
    by_cases h0 : a = 0
    · subst h0
      by_cases h0' : b = 0
      · exact h0'.symm
      · exact absurd (hinj (key b hb h0') h0p (by rw [hpper b]; exact hab.symm))
          (by linarith [hb.1])
    · have hap : a + 2 * Real.pi ∈ Set.Ico 0 (2 * Real.pi) := key a ha h0
      by_cases h0' : b = 0
      · subst h0'
        exact absurd (hinj h0p hap (by rw [hpper a]; exact hab.symm))
          (by linarith [ha.1])
      · have hbp : b + 2 * Real.pi ∈ Set.Ico 0 (2 * Real.pi) := key b hb h0'
        have h := hinj hap hbp (by rw [hpper a, hpper b]; exact hab)
        linarith
  refine ⟨fun s => param ((e.symm : ℝ → ℝ) (-s)), e (2 * Real.pi), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    have hEsymm := hasDerivAt_orbitClockOrderIso_symm (fun θ => (-rate θ)⁻¹) hvcont hMpos hbound
      (-(s : ℝ))
    simp only at hEsymm
    have hnegderiv : HasDerivAt (fun u : ℝ => -u) (-(1 : ℝ)) s := hasDerivAt_neg' s
    have hcomp := hEsymm.scomp s hnegderiv
    have hparam := (hderiv ((e.symm : ℝ → ℝ) (-s))).scomp s hcomp
    refine hparam.congr_deriv ?_
    rw [inv_inv, neg_one_smul, neg_neg]
    exact (hfield _).symm
  · show Set.range (fun s => param ((e.symm : ℝ → ℝ) (-s))) = Set.range param
    ext x
    simp only [Set.mem_range]
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · obtain ⟨s, hs⟩ := hs
      exact ⟨(e.symm : ℝ → ℝ) (-s), hs⟩
    · obtain ⟨θ, hθ⟩ := hs
      obtain ⟨u, hu⟩ := e.symm.surjective θ
      exact ⟨-u, by rw [neg_neg, hu]; exact hθ⟩
  · have hmono := e.strictMono hP
    rwa [hezero] at hmono
  · rw [hfun]
  · intro s
    have hstep : (e.symm : ℝ → ℝ) (-(s + e (2 * Real.pi))) =
        (e.symm : ℝ → ℝ) (-s) - 2 * Real.pi := by
      apply e.injective
      rw [e.apply_symm_apply, hshift', e.apply_symm_apply]
      ring
    show param ((e.symm : ℝ → ℝ) (-(s + e (2 * Real.pi)))) = param ((e.symm : ℝ → ℝ) (-s))
    rw [hstep]
    have h2 := hpper ((e.symm : ℝ → ℝ) (-s) - 2 * Real.pi)
    rw [sub_add_cancel] at h2
    exact h2.symm
  · intro s₁ hs₁ s₂ hs₂ hγ
    have hmem : ∀ s : ℝ, s ∈ Set.Ico 0 (e (2 * Real.pi)) →
        (e.symm : ℝ → ℝ) (-s) ∈ Set.Ioc (-(2 * Real.pi)) 0 := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := hs
      have h1 : -(2 * Real.pi) < (e.symm : ℝ → ℝ) (-s) := by
        refine (e.lt_iff_lt).mp ?_
        rw [hm2, e.apply_symm_apply]
        linarith
      have h2 : (e.symm : ℝ → ℝ) (-s) ≤ 0 := by
        refine (e.le_iff_le).mp ?_
        rw [hezero, e.apply_symm_apply]
        linarith
      exact ⟨h1, h2⟩
    exact neg_injective
      (e.symm.injective (hinjoc (hmem s₁ hs₁) (hmem s₂ hs₂) hγ))

/-- Any real parameter can be moved into the half-open fundamental
interval of a positive lap time by subtracting an integral number of
laps. -/
theorem exists_sub_int_mul_mem_Ico {T : ℝ} (hT : 0 < T) (a : ℝ) :
    ∃ n : ℤ, a - n * T ∈ Set.Ico 0 T := by
  refine ⟨⌊a / T⌋, ?_⟩
  have hne : T ≠ 0 := hT.ne'
  have hfr : a - (⌊a / T⌋ : ℝ) * T = T * Int.fract (a / T) := by
    rw [← Int.self_sub_fract]
    field_simp
    ring
  rw [hfr]
  refine ⟨mul_nonneg hT.le (Int.fract_nonneg _), ?_⟩
  have hlt := mul_lt_mul_of_pos_left (Int.fract_lt_one (a / T)) hT
  linarith

/-- A curve that closes after one lap and traces each half-open
fundamental interval injectively returns to any of its points exactly
at the integral multiples of its lap time. -/
theorem eq_iff_eq_int_mul_of_periodic_injOn {α : Type*} {γ : ℝ → α} {T : ℝ} (hT : 0 < T)
    (hper : Function.Periodic γ T) (hinj : Set.InjOn γ (Set.Ico 0 T)) (a b : ℝ) :
    γ a = γ b ↔ ∃ n : ℤ, a - b = n * T := by
  constructor
  · intro hab
    obtain ⟨na, ha⟩ := exists_sub_int_mul_mem_Ico hT a
    obtain ⟨nb, hb⟩ := exists_sub_int_mul_mem_Ico hT b
    have hγa : γ (a - na * T) = γ a := hper.sub_int_mul_eq na
    have hγb : γ (b - nb * T) = γ b := hper.sub_int_mul_eq nb
    have h : a - na * T = b - nb * T := hinj ha hb (by rw [hγa, hγb]; exact hab)
    refine ⟨na - nb, ?_⟩
    push_cast
    linarith
  · rintro ⟨n, hn⟩
    have hp : Function.Periodic γ (n * T) := hper.int_mul n
    rw [← hp b]
    congr 1
    linarith

/-- The lap time of a closed curve that traces its image exactly once
per lap is the least positive period. -/
theorem le_of_periodic_of_injOn {α : Type*} {γ : ℝ → α} {T S : ℝ} (hT : 0 < T)
    (hper : Function.Periodic γ T) (hinj : Set.InjOn γ (Set.Ico 0 T))
    (hS : 0 < S) (hSper : Function.Periodic γ S) : T ≤ S := by
  obtain ⟨n, hn⟩ := (eq_iff_eq_int_mul_of_periodic_injOn hT hper hinj S 0).mp hSper.eq
  rcases lt_or_ge n 1 with h1 | h1
  · have hn0 : n ≤ 0 := by linarith
    have hnn : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
    have hST : S ≤ 0 := by
      have hSval : S = (n : ℝ) * T := by linarith
      rw [hSval]
      exact mul_nonpos_of_nonpos_of_nonneg hnn hT.le
    exact absurd hST (not_le.mpr hS)
  · have h1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    have hSval : S = (n : ℝ) * T := by linarith
    rw [hSval]
    have hone := mul_le_mul_of_nonneg_right h1' hT.le
    linarith

/-- The stereographic scale is continuous on physical space. -/
theorem continuous_batemanStereoScale : Continuous (batemanStereoScale) := by
  unfold batemanStereoScale
  exact continuous_const.div
    ((((continuous_fst.pow 2).add ((continuous_fst.comp continuous_snd).pow 2)).add
      ((continuous_snd.comp continuous_snd).pow 2)).add continuous_const)
    (fun s => by positivity)

/-- The actual magnetic vector never vanishes as a vector on a core. -/
theorem batemanMagneticVector_ne_zero_on_core {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (t : ℝ)
    {phase : Circle} {s : Space} (hs : s ∈ poweredPhysicalCore p q t phase) :
    batemanMagneticVector p q t s ≠ 0 := by
  intro h
  exact (fields_nonzero_on_poweredPhysicalCore hp hq t hs).2
    ((batemanCartesianCoordinates.symm).map_eq_zero_iff.mp h)

/-- The actual electric vector never vanishes as a vector on a core. -/
theorem batemanElectricVector_ne_zero_on_core {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (t : ℝ)
    {phase : Circle} {s : Space} (hs : s ∈ poweredPhysicalCore p q t phase) :
    batemanElectricVector p q t s ≠ 0 := by
  intro h
  exact (fields_nonzero_on_poweredPhysicalCore hp hq t hs).1
    ((batemanCartesianCoordinates.symm).map_eq_zero_iff.mp h)

/-- The lifted physical core circle sweeps out the whole initial core. -/
theorem range_poweredPhysicalCoreExp {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (phase : Circle) :
    Set.range (poweredPhysicalCoreExp p q phase) = poweredPhysicalCore p q 0 phase := by
  obtain ⟨-, hrange⟩ := poweredPhysicalCoreParam_bijective hp hq hpq 0 phase
  ext s
  constructor
  · rintro ⟨θ, rfl⟩
    rw [← hrange]
    exact ⟨Circle.exp θ, rfl⟩
  · intro hs
    rw [← hrange] at hs
    obtain ⟨w, hw⟩ := hs
    obtain ⟨θ, rfl⟩ := Circle.exp_surjective w
    exact ⟨θ, hw⟩

/-- The positive speed of either actual field along a component core
circle of the reduced exponents, with field exponents scaled by `d`. -/
noncomputable def batemanCoreFieldSpeed (P Q d : ℕ) (s : Space) : ℝ :=
  batemanStereoScale s ^ 3 * (d * (((P : ℝ) + Q) * poweredPeakAmplitude P Q))

/-- The field speed along a core is strictly positive. -/
theorem batemanCoreFieldSpeed_pos (P Q d : ℕ) (hP : 0 < P) (hQ : 0 < Q) (hd : 0 < d)
    (s : Space) : 0 < batemanCoreFieldSpeed P Q d s := by
  have h1 : 0 < batemanStereoScale s := batemanStereoScale_pos s
  have h2 : 0 < ((P : ℝ) + Q) * poweredPeakAmplitude P Q :=
    mul_pos (by exact_mod_cast add_pos hP hQ) (poweredPeakAmplitude_pos hP hQ)
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  exact mul_pos (pow_pos h1 3) (mul_pos hd' h2)

/-- The stereographic scale is bounded by two. -/
theorem batemanStereoScale_le_two (s : Space) : batemanStereoScale s ≤ 2 := by
  unfold batemanStereoScale
  have h : (0 : ℝ) < s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2 + 1 := by positivity
  rw [div_le_iff₀ h]
  linarith [sq_nonneg s.1, sq_nonneg s.2.1, sq_nonneg s.2.2]

/-- The field speed along a core has the explicit uniform upper bound
eight times its constant factor. -/
theorem batemanCoreFieldSpeed_le (P Q d : ℕ) (hP : 0 < P) (hQ : 0 < Q) (s : Space) :
    batemanCoreFieldSpeed P Q d s ≤ 8 * (d * (((P : ℝ) + Q) * poweredPeakAmplitude P Q)) := by
  have h : batemanStereoScale s ^ 3 ≤ (2 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (batemanStereoScale_pos s).le (batemanStereoScale_le_two s) 3
  norm_num at h
  exact mul_le_mul_of_nonneg_right h (mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (poweredPeakAmplitude_pos hP hQ).le))

/-- The magnetic rate along a component core equals minus the real part
of the phase times the positive field speed. -/
theorem batemanMagneticCore_rate_eq (P Q d : ℕ) (phase : Circle) (s : Space) :
    batemanStereoScale s ^ 3 * (d * batemanCoreMagneticFactor P Q phase) =
      -((phase : ℂ).re) * batemanCoreFieldSpeed P Q d s := by
  unfold batemanCoreMagneticFactor batemanCoreFieldSpeed
  ring

/-- The electric rate along a component core equals the imaginary part
of the phase times the positive field speed. -/
theorem batemanElectricCore_rate_eq (P Q d : ℕ) (phase : Circle) (s : Space) :
    batemanStereoScale s ^ 3 * (d * batemanCoreElectricFactor P Q phase) =
      (phase : ℂ).im * batemanCoreFieldSpeed P Q d s := by
  unfold batemanCoreElectricFactor batemanCoreFieldSpeed
  ring

/-- The explicit uniform upper bound for the field speed is positive. -/
theorem batemanCoreFieldSpeed_bound_pos (P Q d : ℕ) (hP : 0 < P) (hQ : 0 < Q) (hd : 0 < d) :
    0 < 8 * (d * (((P : ℝ) + Q) * poweredPeakAmplitude P Q)) := by
  have h1 : 0 < ((P : ℝ) + Q) := by exact_mod_cast add_pos hP hQ
  have h2 : 0 < poweredPeakAmplitude P Q := poweredPeakAmplitude_pos hP hQ
  have h3 : 0 < (d : ℝ) := by exact_mod_cast hd
  exact mul_pos (by norm_num) (mul_pos h3 (mul_pos h1 h2))

/-- The one-lap period of a component core circle: the integral of the
reciprocal field speed along the lifted circle parametrization. -/
noncomputable def batemanCoreLoopPeriod (p q d : ℕ) (ζ : Circle) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    (batemanCoreFieldSpeed (p * d) (q * d) d (poweredPhysicalCoreExp p q ζ θ))⁻¹

/-- The rate function along the lifted core circle is continuous. -/
theorem continuous_batemanCoreFieldSpeed_exp {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (d : ℕ) (ζ : Circle) :
    Continuous (fun θ => batemanCoreFieldSpeed (p * d) (q * d) d
      (poweredPhysicalCoreExp p q ζ θ)) := by
  have hbase := (continuous_batemanStereoScale.comp
    (continuous_poweredPhysicalCoreExp hp hq hpq ζ)).pow 3
  exact hbase.mul continuous_const

/-- The rate function along the lifted core circle is periodic. -/
theorem periodic_batemanCoreFieldSpeed_exp (p q d : ℕ) (ζ : Circle) :
    Function.Periodic (fun θ => batemanCoreFieldSpeed (p * d) (q * d) d
      (poweredPhysicalCoreExp p q ζ θ)) (2 * Real.pi) :=
  fun θ => by simp only [periodic_poweredPhysicalCoreExp p q ζ θ]

/-- **Closed magnetic core field lines at the initial time.** For
coprime reduced exponents and any common scale `d`, each magnetic core
circle carries an actual global integral curve of the magnetic field
with scaled exponents; it moves with positive speed, covers the whole
core circle, closes after one lap with the reciprocal-speed lap
integral as period, traces the core exactly once per period, has that
lap time as its least positive period, and returns to each of its
points only at whole numbers of laps. -/
theorem exists_periodicMagneticCoreFieldLine {p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (hd : 0 < d) {phase ζ : Circle} (hζ : ζ ^ d = phase)
    (hphase : (phase : ℂ).im = 0) :
    ∃ γ : ℝ → Space,
      IsIntegralCurve γ (fun _ => batemanMagneticVector (p * d) (q * d) 0) ∧
      Set.range γ = poweredPhysicalCore p q 0 ζ ∧
      0 < batemanCoreLoopPeriod p q d ζ ∧
      Function.Periodic γ (batemanCoreLoopPeriod p q d ζ) ∧
      Set.InjOn γ (Set.Ico 0 (batemanCoreLoopPeriod p q d ζ)) ∧
      (∀ s, 0 < ‖batemanMagneticVector (p * d) (q * d) 0 (γ s)‖) ∧
      (∀ S, 0 < S → Function.Periodic γ S → batemanCoreLoopPeriod p q d ζ ≤ S) ∧
      (∀ a b, γ a = γ b ↔ ∃ n : ℤ,
        a - b = n * batemanCoreLoopPeriod p q d ζ) := by
  have hP : 0 < p * d := Nat.mul_pos hp hd
  have hQ : 0 < q * d := Nat.mul_pos hq hd
  have hbridge (θ : ℝ) : batemanMagneticVector (p * d) (q * d) 0
      (poweredPhysicalCoreExp p q ζ θ) =
      (-((phase : ℂ).re) * batemanCoreFieldSpeed (p * d) (q * d) d
        (poweredPhysicalCoreExp p q ζ θ)) • batemanCoreVelocity p q ζ θ := by
    rw [batemanMagneticVector_coreExp_eq hp hq hpq hd hζ hphase θ]
    congr 1
    exact batemanMagneticCore_rate_eq (p * d) (q * d) d phase
      (poweredPhysicalCoreExp p q ζ θ)
  have hspeedpos (θ : ℝ) : 0 < batemanCoreFieldSpeed (p * d) (q * d) d
      (poweredPhysicalCoreExp p q ζ θ) :=
    batemanCoreFieldSpeed_pos (p * d) (q * d) d hP hQ hd _
  have hM₀ := batemanCoreFieldSpeed_bound_pos (p * d) (q * d) d hP hQ hd
  have habs : |(phase : ℂ).re| = 1 := abs_re_eq_one_of_im_zero hphase
  have hrange := range_poweredPhysicalCoreExp hp hq hpq ζ
  rcases (abs_eq (by positivity)).mp habs with h1 | h1
  · have hfieldarg : ∀ θ : ℝ,
        batemanMagneticVector (p * d) (q * d) 0 (poweredPhysicalCoreExp p q ζ θ) =
        -(batemanCoreFieldSpeed (p * d) (q * d) d (poweredPhysicalCoreExp p q ζ θ)) •
          batemanCoreVelocity p q ζ θ := by
      intro θ
      rw [hbridge θ, h1]
      simp
    obtain ⟨γ, T, hder, hTrange, hTpos, hTeq, hper, hinj⟩ :=
      exists_periodicIntegralCurve_of_negative_rate
        (rate := fun θ => -(batemanCoreFieldSpeed (p * d) (q * d) d
          (poweredPhysicalCoreExp p q ζ θ))) (hM₀ := hM₀)
        (hasDerivAt_poweredPhysicalCoreExp hp hq hpq ζ)
        hfieldarg
        ((continuous_batemanCoreFieldSpeed_exp hp hq hpq d ζ).neg)
        (fun θ => by simp only [periodic_batemanCoreFieldSpeed_exp p q d ζ θ])
        (periodic_poweredPhysicalCoreExp p q ζ)
        (fun θ => neg_lt_zero.mpr (hspeedpos θ))
        (fun θ => neg_le_neg (batemanCoreFieldSpeed_le (p * d) (q * d) d hP hQ _))
        (injOn_poweredPhysicalCoreExp hp hq hpq ζ)
    have hloop : T = batemanCoreLoopPeriod p q d ζ := by
      unfold batemanCoreLoopPeriod
      rw [hTeq]
      try simp only [neg_neg]
    rw [hloop] at hTpos hper hinj
    refine ⟨γ, hder, ?_, hTpos, hper, hinj, ?_, ?_, ?_⟩
    · rw [hTrange, hrange]
    · intro s
      have hs0 : γ s ∈ Set.range γ := Set.mem_range_self s
      have hs : γ s ∈ poweredPhysicalCore p q 0 ζ := by
        rw [hTrange.trans hrange] at hs0
        exact hs0
      have hmem : γ s ∈ poweredPhysicalCore (p * d) (q * d) 0 phase := by
        rw [poweredPhysicalCore_mul_exponents hp hq hd 0 phase]
        exact Set.mem_iUnion.mpr ⟨⟨ζ, hζ⟩, hs⟩
      exact norm_pos_iff.mpr
        (batemanMagneticVector_ne_zero_on_core hP hQ 0 hmem)
    · exact fun S hS hSper => le_of_periodic_of_injOn hTpos hper hinj hS hSper
    · exact fun a b => eq_iff_eq_int_mul_of_periodic_injOn hTpos hper hinj a b
  · have hfieldarg : ∀ θ : ℝ,
        batemanMagneticVector (p * d) (q * d) 0 (poweredPhysicalCoreExp p q ζ θ) =
        batemanCoreFieldSpeed (p * d) (q * d) d (poweredPhysicalCoreExp p q ζ θ) •
          batemanCoreVelocity p q ζ θ := by
      intro θ
      rw [hbridge θ, h1]
      simp
    obtain ⟨γ, T, hder, hTrange, hTpos, hTeq, hper, hinj⟩ :=
      exists_periodicIntegralCurve_of_positive_rate
        (rate := fun θ => batemanCoreFieldSpeed (p * d) (q * d) d
          (poweredPhysicalCoreExp p q ζ θ)) (hM₀ := hM₀)
        (hasDerivAt_poweredPhysicalCoreExp hp hq hpq ζ)
        hfieldarg
        (continuous_batemanCoreFieldSpeed_exp hp hq hpq d ζ)
        (periodic_batemanCoreFieldSpeed_exp p q d ζ)
        (periodic_poweredPhysicalCoreExp p q ζ)
        hspeedpos
        (fun θ => batemanCoreFieldSpeed_le (p * d) (q * d) d hP hQ _)
        (injOn_poweredPhysicalCoreExp hp hq hpq ζ)
    have hloop : T = batemanCoreLoopPeriod p q d ζ := by
      unfold batemanCoreLoopPeriod
      rw [hTeq]
    rw [hloop] at hTpos hper hinj
    refine ⟨γ, hder, ?_, hTpos, hper, hinj, ?_, ?_, ?_⟩
    · rw [hTrange, hrange]
    · intro s
      have hs0 : γ s ∈ Set.range γ := Set.mem_range_self s
      have hs : γ s ∈ poweredPhysicalCore p q 0 ζ := by
        rw [hTrange.trans hrange] at hs0
        exact hs0
      have hmem : γ s ∈ poweredPhysicalCore (p * d) (q * d) 0 phase := by
        rw [poweredPhysicalCore_mul_exponents hp hq hd 0 phase]
        exact Set.mem_iUnion.mpr ⟨⟨ζ, hζ⟩, hs⟩
      exact norm_pos_iff.mpr
        (batemanMagneticVector_ne_zero_on_core hP hQ 0 hmem)
    · exact fun S hS hSper => le_of_periodic_of_injOn hTpos hper hinj hS hSper
    · exact fun a b => eq_iff_eq_int_mul_of_periodic_injOn hTpos hper hinj a b

/-- **Closed electric core field lines at the initial time.** For
coprime reduced exponents and any common scale `d`, each electric core
circle carries an actual global integral curve of the electric field
with scaled exponents; it moves with positive speed, covers the whole
core circle, closes after one lap with the reciprocal-speed lap
integral as period, traces the core exactly once per period, has that
lap time as its least positive period, and returns to each of its
points only at whole numbers of laps. -/
theorem exists_periodicElectricCoreFieldLine {p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (hd : 0 < d) {phase ζ : Circle} (hζ : ζ ^ d = phase)
    (hphase : (phase : ℂ).re = 0) :
    ∃ γ : ℝ → Space,
      IsIntegralCurve γ (fun _ => batemanElectricVector (p * d) (q * d) 0) ∧
      Set.range γ = poweredPhysicalCore p q 0 ζ ∧
      0 < batemanCoreLoopPeriod p q d ζ ∧
      Function.Periodic γ (batemanCoreLoopPeriod p q d ζ) ∧
      Set.InjOn γ (Set.Ico 0 (batemanCoreLoopPeriod p q d ζ)) ∧
      (∀ s, 0 < ‖batemanElectricVector (p * d) (q * d) 0 (γ s)‖) ∧
      (∀ S, 0 < S → Function.Periodic γ S → batemanCoreLoopPeriod p q d ζ ≤ S) ∧
      (∀ a b, γ a = γ b ↔ ∃ n : ℤ,
        a - b = n * batemanCoreLoopPeriod p q d ζ) := by
  have hP : 0 < p * d := Nat.mul_pos hp hd
  have hQ : 0 < q * d := Nat.mul_pos hq hd
  have hbridge (θ : ℝ) : batemanElectricVector (p * d) (q * d) 0
      (poweredPhysicalCoreExp p q ζ θ) =
      ((phase : ℂ).im * batemanCoreFieldSpeed (p * d) (q * d) d
        (poweredPhysicalCoreExp p q ζ θ)) • batemanCoreVelocity p q ζ θ := by
    rw [batemanElectricVector_coreExp_eq hp hq hpq hd hζ hphase θ]
    congr 1
    exact batemanElectricCore_rate_eq (p * d) (q * d) d phase
      (poweredPhysicalCoreExp p q ζ θ)
  have hspeedpos (θ : ℝ) : 0 < batemanCoreFieldSpeed (p * d) (q * d) d
      (poweredPhysicalCoreExp p q ζ θ) :=
    batemanCoreFieldSpeed_pos (p * d) (q * d) d hP hQ hd _
  have hM₀ := batemanCoreFieldSpeed_bound_pos (p * d) (q * d) d hP hQ hd
  have habs : |(phase : ℂ).im| = 1 := abs_im_eq_one_of_re_zero hphase
  have hrange := range_poweredPhysicalCoreExp hp hq hpq ζ
  rcases (abs_eq (by positivity)).mp habs with h1 | h1
  · have hfieldarg : ∀ θ : ℝ,
        batemanElectricVector (p * d) (q * d) 0 (poweredPhysicalCoreExp p q ζ θ) =
        batemanCoreFieldSpeed (p * d) (q * d) d (poweredPhysicalCoreExp p q ζ θ) •
          batemanCoreVelocity p q ζ θ := by
      intro θ
      rw [hbridge θ, h1]
      simp
    obtain ⟨γ, T, hder, hTrange, hTpos, hTeq, hper, hinj⟩ :=
      exists_periodicIntegralCurve_of_positive_rate
        (rate := fun θ => batemanCoreFieldSpeed (p * d) (q * d) d
          (poweredPhysicalCoreExp p q ζ θ)) (hM₀ := hM₀)
        (hasDerivAt_poweredPhysicalCoreExp hp hq hpq ζ)
        hfieldarg
        (continuous_batemanCoreFieldSpeed_exp hp hq hpq d ζ)
        (periodic_batemanCoreFieldSpeed_exp p q d ζ)
        (periodic_poweredPhysicalCoreExp p q ζ)
        hspeedpos
        (fun θ => batemanCoreFieldSpeed_le (p * d) (q * d) d hP hQ _)
        (injOn_poweredPhysicalCoreExp hp hq hpq ζ)
    have hloop : T = batemanCoreLoopPeriod p q d ζ := by
      unfold batemanCoreLoopPeriod
      rw [hTeq]
    rw [hloop] at hTpos hper hinj
    refine ⟨γ, hder, ?_, hTpos, hper, hinj, ?_, ?_, ?_⟩
    · rw [hTrange, hrange]
    · intro s
      have hs0 : γ s ∈ Set.range γ := Set.mem_range_self s
      have hs : γ s ∈ poweredPhysicalCore p q 0 ζ := by
        rw [hTrange.trans hrange] at hs0
        exact hs0
      have hmem : γ s ∈ poweredPhysicalCore (p * d) (q * d) 0 phase := by
        rw [poweredPhysicalCore_mul_exponents hp hq hd 0 phase]
        exact Set.mem_iUnion.mpr ⟨⟨ζ, hζ⟩, hs⟩
      exact norm_pos_iff.mpr
        (batemanElectricVector_ne_zero_on_core hP hQ 0 hmem)
    · exact fun S hS hSper => le_of_periodic_of_injOn hTpos hper hinj hS hSper
    · exact fun a b => eq_iff_eq_int_mul_of_periodic_injOn hTpos hper hinj a b
  · have hfieldarg : ∀ θ : ℝ,
        batemanElectricVector (p * d) (q * d) 0 (poweredPhysicalCoreExp p q ζ θ) =
        -(batemanCoreFieldSpeed (p * d) (q * d) d (poweredPhysicalCoreExp p q ζ θ)) •
          batemanCoreVelocity p q ζ θ := by
      intro θ
      rw [hbridge θ, h1]
      simp
    obtain ⟨γ, T, hder, hTrange, hTpos, hTeq, hper, hinj⟩ :=
      exists_periodicIntegralCurve_of_negative_rate
        (rate := fun θ => -(batemanCoreFieldSpeed (p * d) (q * d) d
          (poweredPhysicalCoreExp p q ζ θ))) (hM₀ := hM₀)
        (hasDerivAt_poweredPhysicalCoreExp hp hq hpq ζ)
        hfieldarg
        ((continuous_batemanCoreFieldSpeed_exp hp hq hpq d ζ).neg)
        (fun θ => by simp only [periodic_batemanCoreFieldSpeed_exp p q d ζ θ])
        (periodic_poweredPhysicalCoreExp p q ζ)
        (fun θ => neg_lt_zero.mpr (hspeedpos θ))
        (fun θ => neg_le_neg (batemanCoreFieldSpeed_le (p * d) (q * d) d hP hQ _))
        (injOn_poweredPhysicalCoreExp hp hq hpq ζ)
    have hloop : T = batemanCoreLoopPeriod p q d ζ := by
      unfold batemanCoreLoopPeriod
      rw [hTeq]
      try simp only [neg_neg]
    rw [hloop] at hTpos hper hinj
    refine ⟨γ, hder, ?_, hTpos, hper, hinj, ?_, ?_, ?_⟩
    · rw [hTrange, hrange]
    · intro s
      have hs0 : γ s ∈ Set.range γ := Set.mem_range_self s
      have hs : γ s ∈ poweredPhysicalCore p q 0 ζ := by
        rw [hTrange.trans hrange] at hs0
        exact hs0
      have hmem : γ s ∈ poweredPhysicalCore (p * d) (q * d) 0 phase := by
        rw [poweredPhysicalCore_mul_exponents hp hq hd 0 phase]
        exact Set.mem_iUnion.mpr ⟨⟨ζ, hζ⟩, hs⟩
      exact norm_pos_iff.mpr
        (batemanElectricVector_ne_zero_on_core hP hQ 0 hmem)
    · exact fun S hS hSper => le_of_periodic_of_injOn hTpos hper hinj hS hSper
    · exact fun a b => eq_iff_eq_int_mul_of_periodic_injOn hTpos hper hinj a b

/-- **Closed magnetic core field lines on every time slice.** The ray
transport of the initial closed magnetic core field line is a closed
actual magnetic integral curve on the slice at time `t`, covering the
whole core circle there; its period is the integral of the positive
spatial ray Jacobian along one lap of the initial curve, the monotone
clock coordinate keeps the transported line injective on the half-open
lap interval, the period is the least positive one, and every return
time is a whole number of laps. -/
theorem exists_periodicMagneticCoreFieldLine_slice {p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (hd : 0 < d) {phase ζ : Circle} (hζ : ζ ^ d = phase)
    (hphase : (phase : ℂ).im = 0) (t : ℝ) :
    ∃ γ : ℝ → Space, ∃ T : ℝ,
      IsIntegralCurve γ (fun _ => batemanMagneticVector (p * d) (q * d) t) ∧
      Set.range γ = poweredPhysicalCore p q t ζ ∧
      0 < T ∧ Function.Periodic γ T ∧
      Set.InjOn γ (Set.Ico 0 T) ∧
      (∀ s, 0 < ‖batemanMagneticVector (p * d) (q * d) t (γ s)‖) ∧
      (∀ S, 0 < S → Function.Periodic γ S → T ≤ S) ∧
      (∀ a b, γ a = γ b ↔ ∃ n : ℤ, a - b = n * T) ∧
      ∃ γ₀ : ℝ → Space,
        IsIntegralCurve γ₀ (fun _ => batemanMagneticVector (p * d) (q * d) 0) ∧
        Function.Periodic γ₀ (batemanCoreLoopPeriod p q d ζ) ∧
        T = batemanOrbitClock t γ₀ (batemanCoreLoopPeriod p q d ζ) := by
  have hP : 0 < p * d := Nat.mul_pos hp hd
  have hQ : 0 < q * d := Nat.mul_pos hq hd
  obtain ⟨γ₀, hcurve, hrange, hTpos, hper, hinj₀, -, -⟩ :=
    exists_periodicMagneticCoreFieldLine hp hq hpq hd hζ hphase
  obtain ⟨e, hE, hErange, hclockpos, hEper, hEinj⟩ :=
    batemanRay_periodicMagneticIntegralCurve (p * d) (q * d) t hcurve hTpos hper hinj₀
  refine ⟨batemanRay t ∘ γ₀ ∘ (e : ℝ → ℝ),
    batemanOrbitClock t γ₀ (batemanCoreLoopPeriod p q d ζ),
    hE, ?_, hclockpos, hEper, hEinj, ?_, ?_, ?_, γ₀, hcurve, hper, rfl⟩
  · rw [hErange, hrange]
    exact batemanSliceHomeomorph_image_poweredPhysicalCore p q t ζ
  · intro s
    have hrw : Set.range (batemanRay t ∘ γ₀ ∘ (e : ℝ → ℝ)) =
        poweredPhysicalCore p q t ζ := by
      rw [hErange, hrange]
      exact batemanSliceHomeomorph_image_poweredPhysicalCore p q t ζ
    have hs0 : (batemanRay t ∘ γ₀ ∘ (e : ℝ → ℝ)) s ∈
        Set.range (batemanRay t ∘ γ₀ ∘ (e : ℝ → ℝ)) := Set.mem_range_self s
    rw [hrw] at hs0
    have hmem : (batemanRay t ∘ γ₀ ∘ (e : ℝ → ℝ)) s ∈
        poweredPhysicalCore (p * d) (q * d) t phase := by
      rw [poweredPhysicalCore_mul_exponents hp hq hd t phase]
      exact Set.mem_iUnion.mpr ⟨⟨ζ, hζ⟩, hs0⟩
    exact norm_pos_iff.mpr (batemanMagneticVector_ne_zero_on_core hP hQ t hmem)
  · exact fun S hS hSper => le_of_periodic_of_injOn hclockpos hEper hEinj hS hSper
  · exact fun a b => eq_iff_eq_int_mul_of_periodic_injOn hclockpos hEper hEinj a b

/-- **Closed electric core field lines on every time slice.** The ray
transport of the initial closed electric core field line is a closed
actual electric integral curve on the slice at time `t`, covering the
whole core circle there; its period is the integral of the positive
spatial ray Jacobian along one lap of the initial curve, the monotone
clock coordinate keeps the transported line injective on the half-open
lap interval, the period is the least positive one, and every return
time is a whole number of laps. -/
theorem exists_periodicElectricCoreFieldLine_slice {p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (hd : 0 < d) {phase ζ : Circle} (hζ : ζ ^ d = phase)
    (hphase : (phase : ℂ).re = 0) (t : ℝ) :
    ∃ γ : ℝ → Space, ∃ T : ℝ,
      IsIntegralCurve γ (fun _ => batemanElectricVector (p * d) (q * d) t) ∧
      Set.range γ = poweredPhysicalCore p q t ζ ∧
      0 < T ∧ Function.Periodic γ T ∧
      Set.InjOn γ (Set.Ico 0 T) ∧
      (∀ s, 0 < ‖batemanElectricVector (p * d) (q * d) t (γ s)‖) ∧
      (∀ S, 0 < S → Function.Periodic γ S → T ≤ S) ∧
      (∀ a b, γ a = γ b ↔ ∃ n : ℤ, a - b = n * T) ∧
      ∃ γ₀ : ℝ → Space,
        IsIntegralCurve γ₀ (fun _ => batemanElectricVector (p * d) (q * d) 0) ∧
        Function.Periodic γ₀ (batemanCoreLoopPeriod p q d ζ) ∧
        T = batemanOrbitClock t γ₀ (batemanCoreLoopPeriod p q d ζ) := by
  have hP : 0 < p * d := Nat.mul_pos hp hd
  have hQ : 0 < q * d := Nat.mul_pos hq hd
  obtain ⟨γ₀, hcurve, hrange, hTpos, hper, hinj₀, -, -⟩ :=
    exists_periodicElectricCoreFieldLine hp hq hpq hd hζ hphase
  obtain ⟨e, hE, hErange, hclockpos, hEper, hEinj⟩ :=
    batemanRay_periodicElectricIntegralCurve (p * d) (q * d) t hcurve hTpos hper hinj₀
  refine ⟨batemanRay t ∘ γ₀ ∘ (e : ℝ → ℝ),
    batemanOrbitClock t γ₀ (batemanCoreLoopPeriod p q d ζ),
    hE, ?_, hclockpos, hEper, hEinj, ?_, ?_, ?_, γ₀, hcurve, hper, rfl⟩
  · rw [hErange, hrange]
    exact batemanSliceHomeomorph_image_poweredPhysicalCore p q t ζ
  · intro s
    have hrw : Set.range (batemanRay t ∘ γ₀ ∘ (e : ℝ → ℝ)) =
        poweredPhysicalCore p q t ζ := by
      rw [hErange, hrange]
      exact batemanSliceHomeomorph_image_poweredPhysicalCore p q t ζ
    have hs0 : (batemanRay t ∘ γ₀ ∘ (e : ℝ → ℝ)) s ∈
        Set.range (batemanRay t ∘ γ₀ ∘ (e : ℝ → ℝ)) := Set.mem_range_self s
    rw [hrw] at hs0
    have hmem : (batemanRay t ∘ γ₀ ∘ (e : ℝ → ℝ)) s ∈
        poweredPhysicalCore (p * d) (q * d) t phase := by
      rw [poweredPhysicalCore_mul_exponents hp hq hd t phase]
      exact Set.mem_iUnion.mpr ⟨⟨ζ, hζ⟩, hs0⟩
    exact norm_pos_iff.mpr (batemanElectricVector_ne_zero_on_core hP hQ t hmem)
  · exact fun S hS hSper => le_of_periodic_of_injOn hclockpos hEper hEinj hS hSper
  · exact fun a b => eq_iff_eq_int_mul_of_periodic_injOn hclockpos hEper hEinj a b

/-- **Closed magnetic core field lines cover the full core for
arbitrary exponents.** For any positive exponents and any real time,
every point of a magnetic extremal core lies on a closed actual
magnetic integral curve of positive speed which stays on the core,
is periodic with a positive period, traces its image exactly once per
period, has that period as its least positive one, and returns to each
of its points only at whole numbers of laps. -/
theorem exists_periodicMagneticCoreFieldLines_gcd {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {phase : Circle} (hphase : (phase : ℂ).im = 0) (t : ℝ) {s : Space}
    (hs : s ∈ poweredPhysicalCore p q t phase) :
    ∃ γ : ℝ → Space, ∃ T : ℝ,
      IsIntegralCurve γ (fun _ => batemanMagneticVector p q t) ∧
      0 < T ∧ Function.Periodic γ T ∧
      s ∈ Set.range γ ∧ Set.range γ ⊆ poweredPhysicalCore p q t phase ∧
      (∀ u, 0 < ‖batemanMagneticVector p q t (γ u)‖) ∧
      Set.InjOn γ (Set.Ico 0 T) ∧
      (∀ S, 0 < S → Function.Periodic γ S → T ≤ S) ∧
      (∀ a b, γ a = γ b ↔ ∃ n : ℤ, a - b = n * T) := by
  have hd : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left q hp
  have hp' : 0 < p / Nat.gcd p q :=
    Nat.div_pos (Nat.le_of_dvd hp (Nat.gcd_dvd_left p q)) hd
  have hq' : 0 < q / Nat.gcd p q :=
    Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right p q)) hd
  have hc : Nat.Coprime (p / Nat.gcd p q) (q / Nat.gcd p q) :=
    Nat.coprime_div_gcd_div_gcd hd
  have hpd : p / Nat.gcd p q * Nat.gcd p q = p :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left p q)
  have hqd : q / Nat.gcd p q * Nat.gcd p q = q :=
    Nat.div_mul_cancel (Nat.gcd_dvd_right p q)
  have hcore : poweredPhysicalCore (p / Nat.gcd p q * Nat.gcd p q)
      (q / Nat.gcd p q * Nat.gcd p q) t phase = poweredPhysicalCore p q t phase := by
    rw [hpd, hqd]
  rw [← hcore, poweredPhysicalCore_mul_exponents hp' hq' hd t phase] at hs
  obtain ⟨ζ, hζ⟩ := Set.mem_iUnion.mp hs
  obtain ⟨γ, T, hcurve, hrange, hTpos, hper, hinj, hspeed, -, -, -⟩ :=
    exists_periodicMagneticCoreFieldLine_slice hp' hq' hc hd (ζ := (ζ : Circle)) (phase := phase)
      ζ.property hphase t
  have hvec : batemanMagneticVector p q t = batemanMagneticVector
      (p / Nat.gcd p q * Nat.gcd p q) (q / Nat.gcd p q * Nat.gcd p q) t := by
    rw [hpd, hqd]
  refine ⟨γ, T, ?_, hTpos, hper, ?_, ?_, ?_, hinj, ?_, ?_⟩
  · rw [hvec]
    exact hcurve
  · rw [hrange]
    exact hζ
  · rw [hrange, ← hcore, poweredPhysicalCore_mul_exponents hp' hq' hd t phase]
    exact Set.subset_iUnion_of_subset ζ (fun x hx => hx)
  · rw [hvec]
    exact hspeed
  · exact fun S hS hSper => le_of_periodic_of_injOn hTpos hper hinj hS hSper
  · exact fun a b => eq_iff_eq_int_mul_of_periodic_injOn hTpos hper hinj a b

/-- **Closed electric core field lines cover the full core for
arbitrary exponents.** For any positive exponents and any real time,
every point of an electric extremal core lies on a closed actual
electric integral curve of positive speed which stays on the core,
is periodic with a positive period, traces its image exactly once per
period, has that period as its least positive one, and returns to each
of its points only at whole numbers of laps. -/
theorem exists_periodicElectricCoreFieldLines_gcd {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {phase : Circle} (hphase : (phase : ℂ).re = 0) (t : ℝ) {s : Space}
    (hs : s ∈ poweredPhysicalCore p q t phase) :
    ∃ γ : ℝ → Space, ∃ T : ℝ,
      IsIntegralCurve γ (fun _ => batemanElectricVector p q t) ∧
      0 < T ∧ Function.Periodic γ T ∧
      s ∈ Set.range γ ∧ Set.range γ ⊆ poweredPhysicalCore p q t phase ∧
      (∀ u, 0 < ‖batemanElectricVector p q t (γ u)‖) ∧
      Set.InjOn γ (Set.Ico 0 T) ∧
      (∀ S, 0 < S → Function.Periodic γ S → T ≤ S) ∧
      (∀ a b, γ a = γ b ↔ ∃ n : ℤ, a - b = n * T) := by
  have hd : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left q hp
  have hp' : 0 < p / Nat.gcd p q :=
    Nat.div_pos (Nat.le_of_dvd hp (Nat.gcd_dvd_left p q)) hd
  have hq' : 0 < q / Nat.gcd p q :=
    Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right p q)) hd
  have hc : Nat.Coprime (p / Nat.gcd p q) (q / Nat.gcd p q) :=
    Nat.coprime_div_gcd_div_gcd hd
  have hpd : p / Nat.gcd p q * Nat.gcd p q = p :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left p q)
  have hqd : q / Nat.gcd p q * Nat.gcd p q = q :=
    Nat.div_mul_cancel (Nat.gcd_dvd_right p q)
  have hcore : poweredPhysicalCore (p / Nat.gcd p q * Nat.gcd p q)
      (q / Nat.gcd p q * Nat.gcd p q) t phase = poweredPhysicalCore p q t phase := by
    rw [hpd, hqd]
  rw [← hcore, poweredPhysicalCore_mul_exponents hp' hq' hd t phase] at hs
  obtain ⟨ζ, hζ⟩ := Set.mem_iUnion.mp hs
  obtain ⟨γ, T, hcurve, hrange, hTpos, hper, hinj, hspeed, -, -, -⟩ :=
    exists_periodicElectricCoreFieldLine_slice hp' hq' hc hd (ζ := (ζ : Circle)) (phase := phase)
      ζ.property hphase t
  have hvec : batemanElectricVector p q t = batemanElectricVector
      (p / Nat.gcd p q * Nat.gcd p q) (q / Nat.gcd p q * Nat.gcd p q) t := by
    rw [hpd, hqd]
  refine ⟨γ, T, ?_, hTpos, hper, ?_, ?_, ?_, hinj, ?_, ?_⟩
  · rw [hvec]
    exact hcurve
  · rw [hrange]
    exact hζ
  · rw [hrange, ← hcore, poweredPhysicalCore_mul_exponents hp' hq' hd t phase]
    exact Set.subset_iUnion_of_subset ζ (fun x hx => hx)
  · rw [hvec]
    exact hspeed
  · exact fun S hS hSper => le_of_periodic_of_injOn hTpos hper hinj hS hSper
  · exact fun a b => eq_iff_eq_int_mul_of_periodic_injOn hTpos hper hinj a b

end Qatlib.Papers.KnotLight13.TorusFamily
