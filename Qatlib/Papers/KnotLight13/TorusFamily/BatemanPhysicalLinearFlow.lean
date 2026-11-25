/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanLinearFlow

/-!
# Linear orbits in physical Bateman coordinates

[Kedia2013TyingKnots], discussion of Fig. 2.
The normalized linear flow transfers to every physical intermediate
torus via an order-preserving global change of time along each orbit.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open scoped Real

/-- On a physical magnetic torus, the image of each linear orbit is a
physical integral curve after an increasing change of time on the whole
real line. The torus homeomorphism is shared by all starting points. -/
theorem exists_batemanMagnetic_linearOrbits
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    (t : ℝ) {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q)
    {x₀ : ℝ × ℝ × ℝ} (hx₀ : x₀ ∈ poweredPhysicalRealLevel p q t c) :
    let T := batemanMagneticQuotientPeriod hp hq h₀ hc
    0 < T ∧ ∃ (ω : ℝ) (e : (AddCircle T × Circle) ≃ₜ ↥(poweredPhysicalRealLevel p q t c)),
      e (0, 1) = ⟨x₀, hx₀⟩ ∧
      ∀ x : AddCircle T × Circle, ∃ clock : ℝ ≃o ℝ,
        let γ := fun s => (e (x.1 + (clock.symm s : AddCircle T),
          x.2 * Circle.exp (ω * clock.symm s))).val
        IsIntegralCurve γ (fun _ => batemanMagneticVector p q t) ∧ γ 0 = (e x).val := by
  let E := poweredSphereRealLevelToPhysical (p := p) hq t h₀
  let z := E.symm ⟨x₀, hx₀⟩
  obtain ⟨hT, ω, e, he, hflow⟩ :=
    exists_batemanSphereMagnetic_linearFlow hp hq hpq h₀ hc z.property
  refine ⟨hT, ω, e.trans E, ?_, ?_⟩
  · change E (e (0, 1)) = _
    rw [he, E.apply_symm_apply]
  · intro x
    let w := fun s : ℝ => e (x.1 + (s : AddCircle _), x.2 * Circle.exp (ω * s))
    obtain ⟨clock, hγ, hγ₀, _⟩ :=
      batemanSphereMagneticIntegralCurve_physical hp hq hpq t h₀ hc
        (hflow x) (fun s => (w s).property)
    refine ⟨clock, hγ, ?_⟩
    calc
      _ = batemanRay t (initialCartesianPoint (w 0).val) := hγ₀
      _ = (E (e x)).val := by
        rw [show w 0 = e x from by simp [w]]
        rfl

/-- The physical electric intermediate torus has linear orbit coordinates
after an increasing change of time along each orbit. -/
theorem exists_batemanElectric_linearOrbits
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    (t : ℝ) {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q)
    {x₀ : ℝ × ℝ × ℝ} (hx₀ : x₀ ∈ poweredPhysicalImagLevel p q t c) :
    let T := batemanMagneticQuotientPeriod hp hq (neg_ne_zero.mpr h₀) (by rwa [abs_neg])
    0 < T ∧ ∃ (ω : ℝ) (e : (AddCircle T × Circle) ≃ₜ ↥(poweredPhysicalImagLevel p q t c)),
      e (0, 1) = ⟨x₀, hx₀⟩ ∧
      ∀ x : AddCircle T × Circle, ∃ clock : ℝ ≃o ℝ,
        let γ := fun s => (e (x.1 + (clock.symm s : AddCircle T),
          x.2 * Circle.exp (ω * clock.symm s))).val
        IsIntegralCurve γ (fun _ => batemanElectricVector p q t) ∧ γ 0 = (e x).val := by
  let θ := π / (2 * (q : ℝ))
  let R := (batemanAxialHomeomorph θ).subtype (poweredPhysicalLevel_axial_iff (p := p) hq t c)
  let y := R.symm ⟨x₀, hx₀⟩
  obtain ⟨hT, ω, e, he, hflow⟩ := exists_batemanMagnetic_linearOrbits hp hq hpq t
    (neg_ne_zero.mpr h₀) (by rwa [abs_neg]) y.property
  refine ⟨hT, ω, e.trans R, ?_, ?_⟩
  · change R (e (0, 1)) = _
    rw [he, R.apply_symm_apply]
  · intro x
    obtain ⟨clock, hg, hg₀⟩ := hflow x
    let g := fun s : ℝ =>
      (e (x.1 + (clock.symm s : AddCircle _), x.2 * Circle.exp (ω * clock.symm s))).val
    refine ⟨clock, ?_, ?_⟩
    · intro s
      exact (hasDerivAt_batemanAxialRotation_curve θ (hg s)).congr_deriv
        (batemanAxialRotation_magnetic_to_electric p hq t (g s))
    · change batemanAxialRotation θ (g 0) = batemanAxialRotation θ (e x).val
      rw [show g 0 = (e x).val from hg₀]

end Qatlib.Papers.KnotLight13.TorusFamily
