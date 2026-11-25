/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanCoreLinks

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.IsLocalHomeomorph

/-!
# The phase fibration of the torus polynomial

[Kedia2013TyingKnots], Eq. (6) and the torus-knot link of the weighted
homogeneous polynomial,
[DOI](https://doi.org/10.1103/PhysRevLett.111.150404).
On the unit three-sphere minus the zero link, the actual phase map is
locally a product with its phase-one fiber. The trivializations are
induced by the weighted circle action on the two complex coordinates.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set
open Qatlib.Papers.KnotLight13.TorusFamily (torusPolynomial weighted_homogeneity)

/-- The unit three-sphere with the zero link of the torus polynomial removed. -/
def torusPolynomialExterior (p q : ℕ) : Set (ℂ × ℂ) :=
  {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 = 1 ∧ torusPolynomial p q z.1 z.2 ≠ 0}

/-- On the sphere complement the polynomial, divided by its modulus,
defines its unit phase. -/
noncomputable def torusPolynomialPhase (p q : ℕ) (z : ↥(torusPolynomialExterior p q)) : Circle :=
  ⟨torusPolynomial p q z.val.1 z.val.2 / (‖torusPolynomial p q z.val.1 z.val.2‖ : ℂ), by
    change _ ∈ Metric.sphere 0 1
    rw [Metric.mem_sphere, dist_zero_right, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr z.property.2)]⟩

/-- The polynomial phase is continuous on the entire sphere complement. -/
theorem continuous_torusPolynomialPhase (p q : ℕ) : Continuous (torusPolynomialPhase p q) := by
  have ha : Continuous (fun z : ↥(torusPolynomialExterior p q) => z.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hb : Continuous (fun z : ↥(torusPolynomialExterior p q) => z.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have h : Continuous (fun z : ↥(torusPolynomialExterior p q) => torusPolynomial p q z.val.1 z.val.2) :=
    (ha.pow p).sub (hb.pow q)
  exact (h.div (Complex.continuous_ofReal.comp h.norm) (fun z => by
    change (‖torusPolynomial p q z.val.1 z.val.2‖ : ℂ) ≠ 0
    exact_mod_cast (norm_ne_zero_iff.mpr z.property.2 : ‖torusPolynomial p q z.val.1 z.val.2‖ ≠ 0))).subtype_mk _

/-- The weighted circle action rotates the first coordinate with
weight `q` and the second with weight `p`, preserving the sphere complement. -/
noncomputable def torusPolynomialRotate (p q : ℕ) (u : Circle)
    (z : ↥(torusPolynomialExterior p q)) : ↥(torusPolynomialExterior p q) :=
  ⟨((u : ℂ) ^ q * z.val.1, (u : ℂ) ^ p * z.val.2), by
    constructor
    · change ‖(u : ℂ) ^ q * z.val.1‖ ^ 2 + ‖(u : ℂ) ^ p * z.val.2‖ ^ 2 = 1
      simpa only [norm_mul, norm_pow, Circle.norm_coe, one_pow, one_mul] using z.property.1
    · change torusPolynomial p q ((u : ℂ) ^ q * z.val.1) ((u : ℂ) ^ p * z.val.2) ≠ 0
      rw [weighted_homogeneity]
      exact mul_ne_zero (pow_ne_zero _ (Circle.coe_ne_zero u)) z.property.2⟩

/-- Weighted rotation is continuous jointly in its phase and point. -/
theorem continuous_torusPolynomialRotate (p q : ℕ) :
    Continuous (fun a : Circle × ↥(torusPolynomialExterior p q) => torusPolynomialRotate p q a.1 a.2) := by
  have hu : Continuous (fun a : Circle × ↥(torusPolynomialExterior p q) => (a.1 : ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous (fun a : Circle × ↥(torusPolynomialExterior p q) => a.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact (((hu.pow q).mul hz.fst).prodMk ((hu.pow p).mul hz.snd)).subtype_mk _

/-- The degree of the phase change in one weighted rotation is `p*q`. -/
theorem torusPolynomialPhase_rotate (p q : ℕ) (u : Circle) (z : ↥(torusPolynomialExterior p q)) :
    torusPolynomialPhase p q (torusPolynomialRotate p q u z) = u ^ (p * q) * torusPolynomialPhase p q z := by
  apply Circle.ext
  change torusPolynomial p q ((u : ℂ) ^ q * z.val.1) ((u : ℂ) ^ p * z.val.2) /
    (‖torusPolynomial p q ((u : ℂ) ^ q * z.val.1) ((u : ℂ) ^ p * z.val.2)‖ : ℂ) =
      (u : ℂ) ^ (p * q) * (torusPolynomial p q z.val.1 z.val.2 /
        (‖torusPolynomial p q z.val.1 z.val.2‖ : ℂ))
  rw [weighted_homogeneity, norm_mul, norm_pow, Circle.norm_coe, one_pow, one_mul, mul_div_assoc]

/-- Multiplication of phases composes their weighted rotations. -/
theorem torusPolynomialRotate_mul (p q : ℕ) (u v : Circle) (z : ↥(torusPolynomialExterior p q)) :
    torusPolynomialRotate p q (u * v) z = torusPolynomialRotate p q u (torusPolynomialRotate p q v z) := by
  apply Subtype.ext
  change (((u : ℂ) * (v : ℂ)) ^ q * z.val.1, ((u : ℂ) * (v : ℂ)) ^ p * z.val.2) =
    ((u : ℂ) ^ q * ((v : ℂ) ^ q * z.val.1), (u : ℂ) ^ p * ((v : ℂ) ^ p * z.val.2))
  simp only [mul_pow, mul_assoc]

/-- The identity phase leaves the point fixed. -/
theorem torusPolynomialRotate_one (p q : ℕ) (z : ↥(torusPolynomialExterior p q)) :
    torusPolynomialRotate p q 1 z = z := by
  apply Subtype.ext
  change ((1 : ℂ) ^ q * z.val.1, (1 : ℂ) ^ p * z.val.2) = z.val
  simp

/-- The phase map reaches every unit phase. The weighted orbit of the
sphere point `(1,0)` already realizes all phases. -/
theorem torusPolynomialPhase_surjective {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    Function.Surjective (torusPolynomialPhase p q) := by
  let z : ↥(torusPolynomialExterior p q) := ⟨(1, 0), by
    change ‖(1 : ℂ)‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2 = 1 ∧ torusPolynomial p q (1 : ℂ) 0 ≠ 0
    simp [torusPolynomial, zero_pow hq.ne']⟩
  have hz : torusPolynomialPhase p q z = 1 := by
    apply Circle.ext
    simp [torusPolynomialPhase, torusPolynomial, z, zero_pow hq.ne']
  intro b
  have hn := Nat.mul_pos hp hq
  obtain ⟨roots⟩ := circlePhaseRoots_equiv_fin hn b
  let u := roots ⟨0, hn⟩
  refine ⟨torusPolynomialRotate p q u.val z, ?_⟩
  rw [torusPolynomialPhase_rotate, hz, mul_one, u.property]

/-- Around any base phase, the actual torus-polynomial phase map has a
product homeomorphism with its phase-one fiber, respecting the phase
projection on the first factor. -/
theorem torusPolynomialPhase_locally_product {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (b : Circle) :
    ∃ U : Set Circle, IsOpen U ∧ b ∈ U ∧
      ∃ h : ↥(torusPolynomialPhase p q ⁻¹' U) ≃ₜ
          (↥U × {z : ↥(torusPolynomialExterior p q) // torusPolynomialPhase p q z = 1}),
        ∀ z, (h z).1.val = torusPolynomialPhase p q z.val := by
  let n := p * q
  have hn : 0 < n := Nat.mul_pos hp hq
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨roots⟩ := circlePhaseRoots_equiv_fin hn b
  let u := roots ⟨0, hn⟩
  obtain ⟨e, hu, he⟩ := (Circle.isQuotientCoveringMap_npow n).isCoveringMap.isLocalHomeomorph u.val
  have hb : b ∈ e.target := by
    rw [← u.property, show u.val ^ n = e u.val from congrFun he u.val]
    exact e.map_source hu
  let σ (v : ↥e.target) : Circle := e.symm v.val
  have hσ : Continuous σ := continuousOn_iff_continuous_domRestrict.mp e.continuousOn_symm
  have hs (v : ↥e.target) : σ v ^ n = v.val :=
    (congrFun he (e.symm v.val)).trans (e.right_inv v.property)
  let X := ↥(torusPolynomialPhase p q ⁻¹' e.target)
  let Y := {z : ↥(torusPolynomialExterior p q) // torusPolynomialPhase p q z = 1}
  let base (z : X) : ↥e.target := ⟨torusPolynomialPhase p q z.val, z.property⟩
  let f (z : X) : ↥e.target × Y :=
    (base z, ⟨torusPolynomialRotate p q (σ (base z))⁻¹ z.val, by
      rw [torusPolynomialPhase_rotate, inv_pow, hs (base z)]
      exact inv_mul_cancel (base z).val⟩)
  let g (a : ↥e.target × Y) : X :=
    ⟨torusPolynomialRotate p q (σ a.1) a.2.val, by
      change torusPolynomialPhase p q (torusPolynomialRotate p q (σ a.1) a.2.val) ∈ e.target
      rw [torusPolynomialPhase_rotate, hs a.1, a.2.property, mul_one]
      exact a.1.property⟩
  have hbg (a : ↥e.target × Y) : base (g a) = a.1 := by
    apply Subtype.ext
    change torusPolynomialPhase p q (torusPolynomialRotate p q (σ a.1) a.2.val) = a.1.val
    rw [torusPolynomialPhase_rotate, hs a.1, a.2.property, mul_one]
  refine ⟨e.target, e.open_target, hb, ⟨⟨f, g, ?_, ?_⟩, ?_, ?_⟩, fun _ => rfl⟩
  · intro z
    apply Subtype.ext
    change torusPolynomialRotate p q (σ (base z))
      (torusPolynomialRotate p q (σ (base z))⁻¹ z.val) = z.val
    rw [← torusPolynomialRotate_mul, mul_inv_cancel, torusPolynomialRotate_one]
  · intro a
    refine Prod.ext (hbg a) (Subtype.ext ?_)
    change torusPolynomialRotate p q (σ (base (g a)))⁻¹
      (torusPolynomialRotate p q (σ a.1) a.2.val) = a.2.val
    rw [hbg, ← torusPolynomialRotate_mul, inv_mul_cancel, torusPolynomialRotate_one]
  · have hbase : Continuous base :=
      ((continuous_torusPolynomialPhase p q).comp continuous_subtype_val).subtype_mk _
    have hr := (continuous_torusPolynomialRotate p q).comp
      ((hσ.comp hbase).inv.prodMk (continuous_subtype_val : Continuous (fun z : X => z.val)))
    exact hbase.prodMk (hr.subtype_mk _)
  · have hr : Continuous (fun a : ↥e.target × Y => torusPolynomialRotate p q (σ a.1) a.2.val) :=
      (continuous_torusPolynomialRotate p q).comp
        ((hσ.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
    exact hr.subtype_mk _

end Qatlib.Papers.KnotLight13.TorusFamily
