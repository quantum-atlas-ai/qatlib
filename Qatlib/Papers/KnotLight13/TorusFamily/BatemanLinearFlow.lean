/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanOrbitExistence

public import Mathlib.Topology.Instances.AddCircle.Defs

import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Ring

/-!
# Linear coordinates for the normalized Bateman flow

[Kedia2013TyingKnots], discussion of Fig. 2.
The quotient orbit traverses its oval in one period. Removing the
accumulated weighted phase produces a periodic section and hence
linear coordinates on each coprime intermediate torus.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set

/-- Weighted fiber rotation preserves the powered complex label. -/
theorem batemanFiberRotate_label (p q : ℕ) (θ : Circle) (z : ℂ × ℂ) :
    (batemanFiberRotate p q θ z).1 ^ p * (batemanFiberRotate p q θ z).2 ^ q =
      z.1 ^ p * z.2 ^ q := by
  let a := (θ : ℂ) ^ (p * q)
  have ha : a ≠ 0 := pow_ne_zero _ (Circle.coe_ne_zero θ)
  simp only [batemanFiberRotate, mul_pow, div_pow, ← pow_mul, mul_comm q p]
  change a * z.1 ^ p * (z.2 ^ q / a) = z.1 ^ p * z.2 ^ q
  field_simp [ha]

/-- Weighted fiber rotation preserves each squared radius. -/
theorem batemanFiberRotate_normSq (p q : ℕ) (θ : Circle) (z : ℂ × ℂ) :
    Complex.normSq (batemanFiberRotate p q θ z).1 = Complex.normSq z.1 ∧
      Complex.normSq (batemanFiberRotate p q θ z).2 = Complex.normSq z.2 := by
  simp [batemanFiberRotate, Complex.normSq_eq_norm_sq, norm_pow]

/-- The real product level is invariant under the weighted circle action. -/
theorem batemanFiberRotate_mem_realLevel (p q : ℕ) {c : ℝ} (θ : Circle)
    {z : ℂ × ℂ} (hz : z ∈ poweredSphereRealLevel p q c) :
    batemanFiberRotate p q θ z ∈ poweredSphereRealLevel p q c := by
  obtain ⟨h₁, h₂⟩ := batemanFiberRotate_normSq p q θ z
  exact ⟨by rw [h₁, h₂]; exact hz.1, by rw [batemanFiberRotate_label]; exact hz.2⟩

/-- The quotient forgets weighted rotation along a fiber. -/
theorem batemanMagneticQuotient_fiberRotate (p q : ℕ) (θ : Circle) (z : ℂ × ℂ) :
    batemanMagneticQuotient p q (batemanFiberRotate p q θ z) =
      batemanMagneticQuotient p q z := by
  simp only [batemanMagneticQuotient, (batemanFiberRotate_normSq p q θ z).1,
    batemanFiberRotate_label]

/-- The weighted rotation is jointly continuous in the phase and the point. -/
theorem continuous_batemanFiberRotate (p q : ℕ) :
    Continuous (fun w : Circle × (ℂ × ℂ) => batemanFiberRotate p q w.1 w.2) := by
  have hθ : Continuous (fun w : Circle × (ℂ × ℂ) => (w.1 : ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  exact ((hθ.pow q).mul continuous_snd.fst).prodMk
    (continuous_snd.snd.div (hθ.pow p) (fun w => pow_ne_zero _ (Circle.coe_ne_zero w.1)))

/-- On a coprime strict intermediate level, translation of the first circle
and uniform rotation of the second circle give integral curves of the
normalized magnetic field through every point. -/
theorem exists_batemanSphereMagnetic_linearFlow
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q)
    {z₀ : ℂ × ℂ} (hz₀ : z₀ ∈ poweredSphereRealLevel p q c) :
    let T := batemanMagneticQuotientPeriod hp hq h₀ hc
    0 < T ∧ ∃ (ω : ℝ) (e : (AddCircle T × Circle) ≃ₜ ↥(poweredSphereRealLevel p q c)),
      e (0, 1) = ⟨z₀, hz₀⟩ ∧
      ∀ x : AddCircle T × Circle,
        IsIntegralCurve
          (fun t => (e (x.1 + (t : AddCircle T), x.2 * Circle.exp (ω * t))).val)
          (fun _ => batemanSphereMagnetic p q) := by
  classical
  let T := batemanMagneticQuotientPeriod hp hq h₀ hc
  obtain ⟨w, hw₀, hw, hlevel⟩ := exists_batemanSphereMagneticIntegralCurve_on_level hp hq hz₀
  obtain ⟨hT, _, hrange, hinj⟩ := batemanMagneticQuotient_one_lap hp hq h₀ hc hw hlevel
  obtain ⟨θ, hθ, _⟩ := batemanMagneticQuotient_fiber_return hp hq hpq h₀ hc hw hlevel
  obtain ⟨a, ha⟩ := Circle.exp_surjective θ
  let ω := a / T
  have hω : Circle.exp (ω * T) = θ := by
    rw [show ω * T = a from div_mul_cancel₀ _ hT.ne']
    exact ha
  let s := fun u : ℝ => batemanFiberRotate p q (Circle.exp (-(ω * u))) (w u)
  have hs : Function.Periodic s T := by
    intro u
    change batemanFiberRotate p q (Circle.exp (-(ω * (u + T)))) (w (u + T)) = s u
    rw [hθ u, mul_add, neg_add, Circle.exp_add, Circle.exp_neg (ω * T), hω,
      ← batemanFiberRotate_mul]
    simp [s]
  let S : AddCircle T → ℂ × ℂ := hs.lift
  have hS (u : ℝ) : S (u : AddCircle T) = s u := rfl
  have hSc : Continuous S := by
    rw [isQuotientMap_quotient_mk'.continuous_iff]
    change Continuous s
    have hphase : Continuous (fun u : ℝ => Circle.exp (-(ω * u))) :=
      Circle.exp.continuous.comp (continuous_const.mul continuous_id).neg
    exact (continuous_batemanFiberRotate p q).comp (hphase.prodMk (continuous_iff_continuousAt.mpr fun u => (hw u).continuousAt))
  have hSl (u : AddCircle T) : S u ∈ poweredSphereRealLevel p q c := by
    obtain ⟨a, rfl⟩ := Quotient.exists_rep u
    rw [hS a]
    exact batemanFiberRotate_mem_realLevel p q _ (hlevel a)
  let F : AddCircle T × Circle → ↥(poweredSphereRealLevel p q c) := fun x =>
    ⟨batemanFiberRotate p q x.2 (S x.1), batemanFiberRotate_mem_realLevel p q _ (hSl _)⟩
  have hFc : Continuous F := by
    exact ((continuous_batemanFiberRotate p q).comp
      (continuous_snd.prodMk (hSc.comp continuous_fst))).subtype_mk _
  have hFq (u : ℝ) (v : Circle) :
      batemanMagneticQuotient p q (F (u, v)).val =
        batemanMagneticQuotient p q (w u) := by
    change batemanMagneticQuotient p q (batemanFiberRotate p q v (S u)) = _
    rw [batemanMagneticQuotient_fiberRotate, hS, batemanMagneticQuotient_fiberRotate]
  let _ : Fact (0 < T) := ⟨hT⟩
  have hrep (u : AddCircle T) : ∃ a ∈ Ico 0 T, (a : AddCircle T) = u := by
    have h := AddCircle.coe_image_Ico_eq T (0 : ℝ)
    rw [zero_add] at h
    change u ∈ ((↑) : ℝ → AddCircle T) '' Ico 0 T
    rw [h]
    trivial
  have hFi : Function.Injective F := by
    rintro ⟨x, v⟩ ⟨y, z⟩ h
    obtain ⟨a, ha', rfl⟩ := hrep x
    obtain ⟨b, hb', rfl⟩ := hrep y
    have hab := hinj ha' hb' ((hFq a v).symm.trans
      ((congrArg (fun z : ↥(poweredSphereRealLevel p q c) => batemanMagneticQuotient p q z.val) h).trans
        (hFq b z)))
    subst b
    have heq : batemanMagneticQuotient p q (S (a : AddCircle T)) =
        batemanMagneticQuotient p q (F (a, v)).val :=
      (batemanMagneticQuotient_fiberRotate p q v (S a)).symm
    obtain ⟨φ, _, hφ⟩ := existsUnique_batemanFiberRotate_of_quotient_eq hp hq hpq h₀
      (hSl a) (F (a, v)).property heq
    have hv := hφ v rfl
    have hz := hφ z (congrArg Subtype.val h.symm)
    exact Prod.ext rfl (hv.trans hz.symm)
  have hFs : Function.Surjective F := by
    intro z
    have hz : batemanMagneticQuotient p q z.val ∈ batemanMagneticOval p q c := by
      have hz := batemanMagneticQuotient_mem_oval p q z.val z.property.1
      rw [show (z.val.1 ^ p * z.val.2 ^ q).re = c from z.property.2] at hz
      exact hz
    rw [← hrange] at hz
    obtain ⟨u, hu⟩ := hz
    have hSu : batemanMagneticQuotient p q (S (u : AddCircle T)) =
        batemanMagneticQuotient p q z.val := by
      rw [hS, batemanMagneticQuotient_fiberRotate]
      exact hu
    obtain ⟨v, hv, _⟩ := existsUnique_batemanFiberRotate_of_quotient_eq hp hq hpq h₀
      (hSl u) z.property hSu
    exact ⟨(u, v), Subtype.ext hv⟩
  let e := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hFi, hFs⟩) hFc
  refine ⟨hT, ω, e, ?_, ?_⟩
  · apply Subtype.ext
    change batemanFiberRotate p q 1 (S (0 : AddCircle T)) = z₀
    rw [batemanFiberRotate_one, ← AddCircle.coe_zero, hS]
    simp [s, hw₀, batemanFiberRotate_one]
  · rintro ⟨u, v⟩
    obtain ⟨a, rfl⟩ := Quotient.exists_rep u
    have he (t : ℝ) : (e ((a : AddCircle T) + (t : AddCircle T),
        v * Circle.exp (ω * t))).val =
        batemanFiberRotate p q (v * Circle.exp (-(ω * a))) (w (a + t)) := by
      change batemanFiberRotate p q (v * Circle.exp (ω * t)) (S ((a : AddCircle T) + (t : AddCircle T))) = _
      rw [← AddCircle.coe_add, hS, ← batemanFiberRotate_mul]
      congr 1
      rw [mul_assoc, ← Circle.exp_add]
      congr 2
      ring
    change ∀ t : ℝ, HasDerivAt _ _ t
    intro t
    rw [show (fun τ : ℝ => (e ((a : AddCircle T) + (τ : AddCircle T),
        v * Circle.exp (ω * τ))).val) =
        fun τ => batemanFiberRotate p q (v * Circle.exp (-(ω * a))) (w (a + τ)) from funext he]
    have hshift : HasDerivAt (fun τ : ℝ => a + τ) 1 t := (hasDerivAt_id t).const_add a
    have hwshift : HasDerivAt (fun τ : ℝ => w (a + τ))
        (batemanSphereMagnetic p q (w (a + t))) t :=
      ((hw (a + t)).scomp t hshift).congr_deriv (one_smul ℝ _)
    exact hasDerivAt_batemanFiberRotate hp hq _ hwshift

end Qatlib.Papers.KnotLight13.TorusFamily
