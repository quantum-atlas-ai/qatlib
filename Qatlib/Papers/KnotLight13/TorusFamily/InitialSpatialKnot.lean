/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalDerivatives
public import Qatlib.Papers.KnotLight13.TorusFamily.TorusKnotLocus

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The initial torus knot in physical space

[Kedia2013TyingKnots], Eqs. (5)–(6) and Fig. 2,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
At time zero the rational Bateman pair gives an inverse stereographic
chart. The whole coprime torus knot avoids the omitted point, so its
standard phase circle parametrizes the zero locus in physical space
with the subspace topology.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily
  (rationalAlpha rationalBeta complex_rational_pair_unit torusPolynomial)

/-- The rational Bateman coordinate pair at time zero. -/
noncomputable def initialBatemanPair (s : ℝ × ℝ × ℝ) : ℂ × ℂ :=
  (rationalAlpha s.1 s.2.1 s.2.2 0, rationalBeta s.1 s.2.1 s.2.2 0)

/-- The Cartesian inverse of the initial stereographic chart, omitting
the point with first coordinate equal to one. -/
noncomputable def initialCartesianPoint (z : ℂ × ℂ) : ℝ × ℝ × ℝ :=
  let d := 1 - z.1.re
  (z.2.re / d, -z.2.im / d, z.1.im / d)

/-- The stereographic pair lies on the unit sphere. -/
theorem initialBatemanPair_unit (s : ℝ × ℝ × ℝ) :
    ‖(initialBatemanPair s).1‖ ^ 2 + ‖(initialBatemanPair s).2‖ ^ 2 = 1 := by
  simpa only [initialBatemanPair, Complex.normSq_eq_norm_sq] using
    complex_rational_pair_unit s.1 s.2.1 s.2.2 0

/-- The real coordinates of the initial pair have the common positive
stereographic denominator. -/
private theorem initialBatemanPair_coordinates (x y z : ℝ) :
    let d := x ^ 2 + y ^ 2 + z ^ 2 + 1
    let w := initialBatemanPair (x, y, z)
    w.1.re = (x ^ 2 + y ^ 2 + z ^ 2 - 1) / d ∧ w.1.im = 2 * z / d ∧
      w.2.re = 2 * x / d ∧ w.2.im = -(2 * y) / d := by
  simp only [initialBatemanPair, rational_alpha_stereographic_zero_time,
    rational_beta_stereographic_zero_time, Complex.div_ofReal_re, Complex.div_ofReal_im]
  norm_num [pow_two, Complex.mul_re, Complex.mul_im]

/-- The Cartesian inverse recovers every physical point. -/
theorem initialCartesianPoint_initialBatemanPair (s : ℝ × ℝ × ℝ) :
    initialCartesianPoint (initialBatemanPair s) = s := by
  rcases s with ⟨x, y, z⟩
  let d := x ^ 2 + y ^ 2 + z ^ 2 + 1
  have hd : 0 < d := by positivity
  obtain ⟨hαr, hαi, hβr, hβi⟩ := initialBatemanPair_coordinates x y z
  have hgap : 1 - (x ^ 2 + y ^ 2 + z ^ 2 - 1) / (x ^ 2 + y ^ 2 + z ^ 2 + 1) =
      2 / (x ^ 2 + y ^ 2 + z ^ 2 + 1) := by
    change 1 - (x ^ 2 + y ^ 2 + z ^ 2 - 1) / d = 2 / d
    field_simp [hd.ne']
    simp [d]
    ring
  simp only [initialCartesianPoint, hαr, hαi, hβr, hβi, hgap]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change (2 * x / d) / (2 / d) = x
    field_simp [hd.ne']
  · change (-(-(2 * y) / d)) / (2 / d) = y
    field_simp [hd.ne']
  · change (2 * z / d) / (2 / d) = z
    field_simp [hd.ne']

/-- Reconstructing a unit pair off the omitted pole and taking its
initial Bateman coordinates returns the same pair. -/
theorem initialBatemanPair_initialCartesianPoint (w : ℂ × ℂ)
    (hs : ‖w.1‖ ^ 2 + ‖w.2‖ ^ 2 = 1) (h : w.1.re < 1) :
    initialBatemanPair (initialCartesianPoint w) = w := by
  let d := 1 - w.1.re
  have hd : 0 < d := sub_pos.mpr h
  let x := w.2.re / d
  let y := -w.2.im / d
  let z := w.1.im / d
  have hs' : w.1.re ^ 2 + w.1.im ^ 2 + w.2.re ^ 2 + w.2.im ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, Complex.normSq_apply] at hs
    nlinarith
  have hden : x ^ 2 + y ^ 2 + z ^ 2 + 1 = 2 / d := by
    dsimp only [x, y, z]
    field_simp [hd.ne']
    dsimp only [d]
    nlinarith
  obtain ⟨hαr, hαi, hβr, hβi⟩ := initialBatemanPair_coordinates x y z
  change initialBatemanPair (x, y, z) = w
  refine Prod.ext (Complex.ext ?_ ?_) (Complex.ext ?_ ?_)
  · rw [hαr, show x ^ 2 + y ^ 2 + z ^ 2 - 1 = 2 / d - 2 by linarith, hden]
    field_simp [hd.ne']
    dsimp only [d]
    ring
  · rw [hαi, hden]
    dsimp only [z]
    field_simp [hd.ne']
  · rw [hβr, hden]
    dsimp only [x]
    field_simp [hd.ne']
  · rw [hβi, hden]
    dsimp only [y]
    field_simp [hd.ne']

/-- The physical zero locus of the torus polynomial of the initial wave. -/
def initialSpatialKnot (p q : ℕ) : Set (ℝ × ℝ × ℝ) :=
  {s | torusPolynomial p q (initialBatemanPair s).1 (initialBatemanPair s).2 = 0}

/-- The initial spatial torus parametrization is the inverse
stereographic image of the standard product-torus phase circle. -/
noncomputable def initialSpatialKnotParam (p q : ℕ) (a b : ℝ) (w : Circle) : ℝ × ℝ × ℝ :=
  initialCartesianPoint (torusKnotParam p q a b w)

/-- The positive second radius ensures the torus misses the stereographic pole. -/
theorem torusParam_re_lt_one (p q : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : a ^ 2 + b ^ 2 = 1) (w : Circle) : (torusKnotParam p q a b w).1.re < 1 := by
  have hlt : a < 1 := by
    have hb2 : 0 < b ^ 2 := pow_pos hb 2
    nlinarith
  have hnorm : ‖(torusKnotParam p q a b w).1‖ = a := by
    simp [torusKnotParam, norm_pow, Complex.norm_real, abs_of_pos ha]
  exact ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans_lt (by rwa [hnorm])

/-- The phase parametrization is a homeomorphism onto the complete
initial physical knot of coprime positive exponents. -/
noncomputable def initialSpatialKnotHomeomorph {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : a ^ 2 + b ^ 2 = 1) (he : a ^ p = b ^ q) :
    Circle ≃ₜ ↥(initialSpatialKnot p q) := by
  let knot := torusKnotParam p q a b
  have hknot (w : Circle) : knot w ∈ unitTorusKnotLocus p q :=
    torusKnotParam_mem_unitTorusKnotLocus p q ha.le hb.le hs he w
  have hinv (w : Circle) : initialBatemanPair (initialSpatialKnotParam p q a b w) = knot w :=
    initialBatemanPair_initialCartesianPoint _ (hknot w).1
      (torusParam_re_lt_one p q ha hb hs w)
  let f : Circle → ↥(initialSpatialKnot p q) := fun w =>
    ⟨initialSpatialKnotParam p q a b w, by
      change torusPolynomial p q _ _ = 0
      rw [hinv w]
      exact (hknot w).2⟩
  have hinj : Function.Injective f := by
    intro u v huv
    have h := congrArg (fun s : ↥(initialSpatialKnot p q) => initialBatemanPair s.val) huv
    change initialBatemanPair (initialSpatialKnotParam p q a b u) =
      initialBatemanPair (initialSpatialKnotParam p q a b v) at h
    rw [hinv, hinv] at h
    exact torusKnotParam_injective hpq ha hb h
  have hsurj : Function.Surjective f := by
    intro s
    have hmem : initialBatemanPair s.val ∈ unitTorusKnotLocus p q :=
      ⟨initialBatemanPair_unit s.val, s.property⟩
    obtain ⟨w, hw⟩ := exists_torusKnotParam_eq hp hq hpq ha hb hs he hmem
    refine ⟨w, Subtype.ext ?_⟩
    change initialCartesianPoint (torusKnotParam p q a b w) = s.val
    rw [hw, initialCartesianPoint_initialBatemanPair]
  have hκ : Continuous knot := continuous_torusKnotParam p q a b
  have hd : Continuous (fun w : Circle => 1 - (knot w).1.re) :=
    continuous_const.sub (Complex.continuous_re.comp hκ.fst)
  have hne (w : Circle) : 1 - (knot w).1.re ≠ 0 :=
    (sub_pos.mpr (torusParam_re_lt_one p q ha hb hs w)).ne'
  have hx := (Complex.continuous_re.comp hκ.snd).div hd hne
  have hy := (Complex.continuous_im.comp hκ.snd).neg.div hd hne
  have hz := (Complex.continuous_im.comp hκ.fst).div hd hne
  have hc : Continuous f := (hx.prodMk (hy.prodMk hz)).subtype_mk _
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f ⟨hinj, hsurj⟩) hc

end Qatlib.Papers.KnotLight13.TorusFamily
