/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanCoreLinks
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPhysicalTori

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Bateman torus polynomial with noncoprime exponents

[Kedia2013TyingKnots], Eqs. (5)–(6) and Fig. 2,
[DOI](https://doi.org/10.1103/PhysRevLett.111.150404).
The polynomial on the sphere factors into phase fibers. In physical
space each fiber is an axial rotation of the knot for the reduced
exponents, and the transported link has the same number of components.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set
open Qatlib.Papers.KnotLight13.TorusFamily
  (rationalAlpha rationalBeta complex_rational_pair_unit torusPolynomial)

local notation "Space" => ℝ × ℝ × ℝ

/-- The physical fiber where the first powered coordinate equals the
second powered coordinate times the specified unit phase. -/
def twistedSpatialKnotAt (p q : ℕ) (t : ℝ) (w : Circle) : Set Space :=
  {s | (batemanPairAt t s).1 ^ p = (w : ℂ) * (batemanPairAt t s).2 ^ q}

/-- Vanishing of the second coordinate on a twisted knot would force
both coordinates to vanish, contradicting the unit sphere identity. -/
private theorem secondBatemanCoordinate_ne_zero {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (t : ℝ) (s : Space) {w : ℂ}
    (h : (batemanPairAt t s).1 ^ p = w * (batemanPairAt t s).2 ^ q) :
    (batemanPairAt t s).2 ≠ 0 := by
  intro hb
  have hu : Complex.normSq (batemanPairAt t s).1 + Complex.normSq (batemanPairAt t s).2 = 1 :=
    complex_rational_pair_unit s.1 s.2.1 s.2.2 t
  rw [hb, zero_pow hq.ne', mul_zero, pow_eq_zero_iff hp.ne'] at h
  simp [h, hb] at hu

/-- The complete spatial Bateman polynomial zero set is the union of
the phase fibers indexed by roots of unity of the common factor. -/
theorem spatialKnotAt_mul_exponents {p q d : ℕ} (hp : 0 < p) (hq : 0 < q) (hd : 0 < d) (t : ℝ) :
    spatialKnotAt (p * d) (q * d) t =
      ⋃ w : {w : Circle // w ^ d = 1}, twistedSpatialKnotAt p q t w.1 := by
  ext s
  simp only [spatialKnotAt, twistedSpatialKnotAt, mem_ofPred_eq, mem_iUnion, torusPolynomial,
    sub_eq_zero, pow_mul]
  let z := batemanPairAt t s
  constructor
  · intro h
    have hz : z.2 ≠ 0 := secondBatemanCoordinate_ne_zero (Nat.mul_pos hp hd) (Nat.mul_pos hq hd) t s
      (show z.1 ^ (p * d) = (1 : ℂ) * z.2 ^ (q * d) by simpa only [one_mul, pow_mul] using h)
    have hb : z.2 ^ q ≠ 0 := pow_ne_zero q hz
    have hr : (z.1 ^ p / z.2 ^ q) ^ d = 1 := by
      rw [div_pow, h, div_self (pow_ne_zero d hb)]
    let w : Circle := ⟨z.1 ^ p / z.2 ^ q, by
      change z.1 ^ p / z.2 ^ q ∈ Metric.sphere 0 1
      rw [Metric.mem_sphere, dist_zero_right]
      apply (pow_left_inj₀ (norm_nonneg _) zero_le_one hd.ne').mp
      rw [← norm_pow, hr, norm_one, one_pow]⟩
    have hw : w ^ d = 1 := Circle.ext hr
    refine ⟨⟨w, hw⟩, ?_⟩
    change z.1 ^ p = (z.1 ^ p / z.2 ^ q) * z.2 ^ q
    rw [div_mul_cancel₀ _ hb]
  · rintro ⟨w, hw⟩
    rw [hw, mul_pow, ← Circle.coe_pow, w.property, Circle.coe_one, one_mul]

/-- Distinct unit phases define disjoint physical knots. Their second
coordinate never vanishes, so the phase is unique at each point. -/
theorem twistedSpatialKnotAt_disjoint {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (t : ℝ) {v w : Circle} (hvw : v ≠ w) :
    Disjoint (twistedSpatialKnotAt p q t v) (twistedSpatialKnotAt p q t w) := by
  refine Set.disjoint_left.mpr (fun s hv hw => hvw (Circle.ext ?_))
  exact mul_right_cancel₀ (pow_ne_zero q (secondBatemanCoordinate_ne_zero hp hq t s hv)) (hv.symm.trans hw)

/-- Every unit phase can be canceled by the axial phase raised to a positive power. -/
theorem exists_batemanAxialPhase_twist {q : ℕ} (hq : 0 < q) (w : Circle) :
    ∃ θ : ℝ, (w : ℂ) * batemanAxialPhase θ ^ q = 1 := by
  obtain ⟨u, hu⟩ := Circle.exp_surjective w
  have hq₀ : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  refine ⟨u / (q : ℝ), ?_⟩
  have he : (q : ℂ) * (-(↑(u / (q : ℝ)) : ℂ) * Complex.I) = -((u : ℂ) * Complex.I) := by
    push_cast
    field_simp [hq₀]
  rw [batemanAxialPhase, ← Complex.exp_nat_mul, he, Complex.exp_neg, ← Circle.coe_exp, hu,
    mul_inv_cancel₀ (Circle.coe_ne_zero w)]

/-- Rotation about the physical axis carries the unrotated reduced knot
onto the entire twisted phase fiber at the same time. -/
noncomputable def twistedSpatialKnotAt_rotation {p q : ℕ} (hq : 0 < q) (t : ℝ) (w : Circle) :
    ↥(spatialKnotAt p q t) ≃ₜ ↥(twistedSpatialKnotAt p q t w) := by
  let h := exists_batemanAxialPhase_twist hq w
  let θ := Classical.choose h
  have hθ := Classical.choose_spec h
  refine (batemanAxialHomeomorph θ).subtype ?_
  rintro ⟨x, y, z⟩
  change torusPolynomial p q (rationalAlpha x y z t) (rationalBeta x y z t) = 0 ↔
    (batemanPairAt t (batemanAxialRotation θ (x, y, z))).1 ^ p =
      (w : ℂ) * (batemanPairAt t (batemanAxialRotation θ (x, y, z))).2 ^ q
  rw [batemanPair_axialRotation, mul_pow, ← mul_assoc, hθ, one_mul, torusPolynomial, sub_eq_zero]

/-- For coprime positive powers the full spatial polynomial zero set is
an embedded circle on every physical time slice. -/
noncomputable def spatialKnotAt_coprime_homeomorph {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (t : ℝ) : Circle ≃ₜ ↥(spatialKnotAt p q t) := by
  let e := exists_balanced_torus_radii hp hq
  let a := Classical.choose e
  let b := Classical.choose (Classical.choose_spec e)
  have h := Classical.choose_spec (Classical.choose_spec e)
  exact (initialSpatialKnotHomeomorph hp hq hc h.1 h.2.1 h.2.2.1 h.2.2.2).trans
    (((batemanSliceHomeomorph t).image (initialSpatialKnot p q)).trans
      (Homeomorph.setCongr (batemanSliceHomeomorph_image_initialSpatialKnot p q t)))

/-- For reduced coprime exponents scaled by `d`, the entire physical
polynomial zero set is the disjoint union of exactly `d` embedded circles. -/
noncomputable def spatialKnotAt_mul_components {p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (hd : 0 < d) (t : ℝ) :
    Fin d × Circle ≃ₜ ↥(spatialKnotAt (p * d) (q * d) t) := by
  let phases := Classical.choice (circlePhaseRoots_equiv_fin hd 1)
  let knot (i : Fin d) := (spatialKnotAt_coprime_homeomorph hp hq hc t).trans
    (twistedSpatialKnotAt_rotation hq t (phases i).1)
  have hsplit := spatialKnotAt_mul_exponents hp hq hd t
  let f (x : Fin d × Circle) : ↥(spatialKnotAt (p * d) (q * d) t) :=
    ⟨(knot x.1 x.2).val, hsplit ▸ mem_iUnion.mpr ⟨phases x.1, (knot x.1 x.2).property⟩⟩
  have hf : Continuous f := by
    apply continuous_prod_of_discrete_left.mpr
    intro i
    exact (continuous_subtype_val.comp (knot i).continuous).subtype_mk _
  refine hf.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨?_, ?_⟩)
  · rintro ⟨i, u⟩ ⟨j, v⟩ h
    have eq : (knot i u).val = (knot j v).val := congrArg Subtype.val h
    have hij : i = j := by
      by_contra hne
      have hp' : (phases i).1 ≠ (phases j).1 :=
        fun h => hne (phases.injective (Subtype.ext h))
      exact Set.disjoint_left.mp (twistedSpatialKnotAt_disjoint hp hq t hp')
        (knot i u).property (eq.symm ▸ (knot j v).property)
    subst j
    exact Prod.ext rfl ((knot i).injective (Subtype.ext eq))
  · intro x
    have hm : x.val ∈ ⋃ w : {w : Circle // w ^ d = 1}, twistedSpatialKnotAt p q t w.1 := by
      rw [← hsplit]
      exact x.property
    obtain ⟨w, hw⟩ := mem_iUnion.mp hm
    let i := phases.symm w
    have hi : phases i = w := phases.apply_symm_apply w
    have hx : x.val ∈ twistedSpatialKnotAt p q t (phases i).1 := hi.symm ▸ hw
    obtain ⟨v, hv⟩ := (knot i).surjective ⟨x.val, hx⟩
    refine ⟨(i, v), Subtype.ext ?_⟩
    change (knot i v).val = x.val
    exact congrArg Subtype.val hv

/-- With arbitrary positive exponents, the complete physical polynomial
zero set has one connected component per unit phase of order `gcd p q`. -/
noncomputable def spatialKnotAt_gcd_components {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (t : ℝ) :
    Fin (p.gcd q) × Circle ≃ₜ ↥(spatialKnotAt p q t) := by
  let d := p.gcd q
  have hd : 0 < d := Nat.gcd_pos_of_pos_left q hp
  have hp₀ : 0 < p / d := Nat.div_pos (Nat.le_of_dvd hp (Nat.gcd_dvd_left p q)) hd
  have hq₀ : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right p q)) hd
  have hc : Nat.Coprime (p / d) (q / d) := Nat.coprime_div_gcd_div_gcd hd
  have he := congrArg₂ (fun a b => spatialKnotAt a b t)
    (Nat.div_mul_cancel (Nat.gcd_dvd_left p q)) (Nat.div_mul_cancel (Nat.gcd_dvd_right p q))
  exact (spatialKnotAt_mul_components hp₀ hq₀ hc hd t).trans (Homeomorph.setCongr he)

/-- The sphere polynomial zero set misses the omitted stereographic point
because its second coordinate is nonzero. -/
theorem unitTorusKnotLocus_re_lt_one {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {z : ℂ × ℂ}
    (hz : z ∈ unitTorusKnotLocus p q) : z.1.re < 1 := by
  obtain ⟨hS, hP⟩ := hz
  have hb : z.2 ≠ 0 := by
    intro hz₂
    rw [torusPolynomial, hz₂, zero_pow hq.ne', sub_zero, pow_eq_zero_iff hp.ne'] at hP
    simp [hP, hz₂] at hS
  have hpos : 0 < ‖z.2‖ := norm_pos_iff.mpr hb
  refine (Complex.re_le_norm z.1).trans_lt ?_
  nlinarith [sq_pos_of_pos hpos]

/-- The original Bateman pair maps the whole physical polynomial zero
set homeomorphically onto its zero set in the unit three-sphere. This
uses the stereographic chart on every component and at every time. -/
noncomputable def spatialKnotAt_sphere_homeomorph {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (t : ℝ) :
    ↥(spatialKnotAt p q t) ≃ₜ ↥(unitTorusKnotLocus p q) := by
  let f (s : ↥(spatialKnotAt p q t)) : ↥(unitTorusKnotLocus p q) :=
    ⟨batemanPairAt t s.val, (rational_pair_mem_unitTorusKnotLocus_iff p q
      s.val.1 s.val.2.1 s.val.2.2 t).mpr s.property⟩
  have hround (z : ↥(unitTorusKnotLocus p q)) :
      batemanPairAt t (batemanRay t (initialCartesianPoint z.val)) = z.val := by
    rw [batemanPairAt_batemanRay]
    exact initialBatemanPair_initialCartesianPoint _ z.property.1 (unitTorusKnotLocus_re_lt_one hp hq z.property)
  let g (z : ↥(unitTorusKnotLocus p q)) : ↥(spatialKnotAt p q t) :=
    ⟨batemanRay t (initialCartesianPoint z.val), by
      change torusPolynomial p q (batemanPairAt t (batemanRay t (initialCartesianPoint z.val))).1
        (batemanPairAt t (batemanRay t (initialCartesianPoint z.val))).2 = 0
      rw [hround]
      exact z.property.2⟩
  refine ⟨⟨f, g,
    fun s => Subtype.ext (batemanRay_initialCartesianPoint_batemanPairAt t s.val),
    fun z => Subtype.ext (hround z)⟩, ?_, ?_⟩
  · have hi : Continuous (fun s : Space => (s.1, s.2.1, s.2.2, t)) := by fun_prop
    have hc : Continuous (batemanPairAt t) :=
      (contDiff_rationalAlpha.continuous.comp hi).prodMk (contDiff_rationalBeta.continuous.comp hi)
    exact (hc.comp continuous_subtype_val).subtype_mk _
  · have ha : Continuous (fun z : ↥(unitTorusKnotLocus p q) => z.val.1) :=
      continuous_fst.comp continuous_subtype_val
    have hb : Continuous (fun z : ↥(unitTorusKnotLocus p q) => z.val.2) :=
      continuous_snd.comp continuous_subtype_val
    have hD : Continuous (fun z : ↥(unitTorusKnotLocus p q) => 1 - z.val.1.re) :=
      continuous_const.sub (Complex.continuous_re.comp ha)
    have hD₀ (z : ↥(unitTorusKnotLocus p q)) : 1 - z.val.1.re ≠ 0 :=
      (sub_pos.mpr (unitTorusKnotLocus_re_lt_one hp hq z.property)).ne'
    have hx := (Complex.continuous_re.comp hb).div hD hD₀
    have hy := (Complex.continuous_im.comp hb).neg.div hD hD₀
    have hz := (Complex.continuous_im.comp ha).div hD hD₀
    have hchart : Continuous (fun z : ↥(unitTorusKnotLocus p q) => initialCartesianPoint z.val) :=
      hx.prodMk (hy.prodMk hz)
    exact ((batemanSliceHomeomorph t).continuous.comp hchart).subtype_mk _

/-- The complete unit-sphere polynomial zero set has one circular
component for each of the `gcd p q` phase choices. -/
noncomputable def unitTorusKnotLocus_gcd_components {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    Fin (p.gcd q) × Circle ≃ₜ ↥(unitTorusKnotLocus p q) :=
  (spatialKnotAt_gcd_components hp hq 0).trans (spatialKnotAt_sphere_homeomorph hp hq 0)

end Qatlib.Papers.KnotLight13.TorusFamily
