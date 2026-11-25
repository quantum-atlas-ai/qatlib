/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.HopfFibers
public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Tactic.LinearCombination

/-!
# Initial magnetic Hopf circles in Euclidean coordinates

[IrvineBouwmeester2008KnottedLight], Eq. (2) and Figs. 1–2,
[DOI](https://doi.org/10.1038/nphys1056).
At the initial time every finite nonzero magnetic scalar value gives the
intersection of an explicit plane with a sphere centered in that plane.
This is a compact Euclidean circle. The projective pole corresponds to
the unit circle of the transverse plane, and the zero value gives the
axis through the point omitted by stereographic projection.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnottedLight08.HopfField

/-- The affine magnetic fiber at time zero, with the genuine chart
domain included so that poles do not get assigned a finite value. -/
def initialMagneticFiber (u v : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {s | etaDen (s 0) (s 1) (s 2) 0 ≠ 0 ∧
    ranadaEta (s 0) (s 1) (s 2) 0 = (u : ℂ) + Complex.I * (v : ℂ)}

/-- The actual initial magnetic fiber of a nonzero finite value is
given by one linear equation and one sphere equation. -/
theorem ranadaEta_initial_fiber_iff (u v x y z : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    (etaDen x y z 0 ≠ 0 ∧ ranadaEta x y z 0 = (u : ℂ) + Complex.I * (v : ℂ)) ↔
      (u ^ 2 + v ^ 2) * x = u * z - v * y ∧
      x ^ 2 + (y + u / (u ^ 2 + v ^ 2)) ^ 2 +
        (z + v / (u ^ 2 + v ^ 2)) ^ 2 = 1 + 1 / (u ^ 2 + v ^ 2) := by
  let d : ℝ := u ^ 2 + v ^ 2
  let c : ℝ := (x ^ 2 + y ^ 2 + z ^ 2 - 1) / 2
  let N : ℂ := (z : ℂ) - Complex.I * (y : ℂ)
  let D : ℂ := (x : ℂ) + Complex.I * (c : ℂ)
  let W : ℂ := (u : ℂ) + Complex.I * (v : ℂ)
  have hd' : d ≠ 0 := hd.ne'
  have hA : (ranadaA x y z 0 : ℂ) ≠ 0 := by
    exact_mod_cast (ranadaA_t_zero_pos x y z).ne'
  have hden : etaDen x y z 0 = (ranadaA x y z 0 : ℂ) * D := by
    simp only [etaDen, ranadaP, ranadaS, ranadaA, D, c]
    push_cast
    ring
  have hscalar : ranadaEta x y z 0 = N / D := ranadaEta_t_zero x y z
  have hND : ¬ (N = 0 ∧ D = 0) := by
    rintro ⟨hn, hz⟩
    have hx : x = 0 := (ofReal_add_iMul_eq_zero_iff x c).1 hz |>.1
    have hc : c = 0 := (ofReal_add_iMul_eq_zero_iff x c).1 hz |>.2
    have hn' : (z : ℂ) + Complex.I * ((-y : ℝ) : ℂ) = 0 := by
      simpa only [N, Complex.ofReal_neg, mul_neg, sub_eq_add_neg] using hn
    obtain ⟨hz', hy'⟩ := (ofReal_add_iMul_eq_zero_iff z (-y)).1 hn'
    have hy : y = 0 := neg_eq_zero.mp hy'
    norm_num [c, hx, hz', hy] at hc
  have hcomplex : (etaDen x y z 0 ≠ 0 ∧ ranadaEta x y z 0 = W) ↔ N = W * D := by
    constructor
    · rintro ⟨h, hEq⟩
      have hD : D ≠ 0 := by
        intro hD
        rw [hden, hD, mul_zero] at h
        exact h rfl
      rw [hscalar] at hEq
      exact (div_eq_iff hD).1 hEq
    · intro h
      have hD : D ≠ 0 := by
        intro hD
        exact hND ⟨by simpa only [hD, mul_zero] using h, hD⟩
      exact ⟨hden ▸ mul_ne_zero hA hD, hscalar.trans ((div_eq_iff hD).2 h)⟩
  have hcoordinates : N = W * D ↔ z = u * x - v * c ∧ -y = v * x + u * c := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · simpa [N, W, D, Complex.mul_re, Complex.mul_im, Complex.add_re,
          Complex.add_im, Complex.sub_re] using congrArg Complex.re h
      · simpa [N, W, D, Complex.mul_re, Complex.mul_im, Complex.add_re,
          Complex.add_im, Complex.sub_im, add_comm] using congrArg Complex.im h
    · rintro ⟨h₁, h₂⟩
      apply Complex.ext
      · simpa [N, W, D, Complex.mul_re, Complex.mul_im, Complex.add_re,
          Complex.add_im, Complex.sub_re] using h₁
      · simpa [N, W, D, Complex.mul_re, Complex.mul_im, Complex.add_re,
          Complex.add_im, Complex.sub_im, add_comm] using h₂
  have hsolve : (z = u * x - v * c ∧ -y = v * x + u * c) ↔
      (d * x = u * z - v * y ∧ d * c = -(u * y + v * z)) := by
    constructor
    · rintro ⟨h₁, h₂⟩
      dsimp only [d]
      constructor
      · linear_combination -u * h₁ - v * h₂
      · linear_combination v * h₁ - u * h₂
    · rintro ⟨h₁, h₂⟩
      constructor
      · apply mul_left_cancel₀ hd'
        dsimp only [d] at h₁ h₂ ⊢
        linear_combination -u * h₁ + v * h₂
      · apply mul_left_cancel₀ hd'
        dsimp only [d] at h₁ h₂ ⊢
        linear_combination -v * h₁ - u * h₂
  have hidentity :
      x ^ 2 + (y + u / d) ^ 2 + (z + v / d) ^ 2 - (1 + 1 / d) =
        (2 / d) * (d * c + u * y + v * z) := by
    field_simp [hd']
    dsimp only [d, c]
    ring
  have hsphere :
      d * c = -(u * y + v * z) ↔
        x ^ 2 + (y + u / d) ^ 2 + (z + v / d) ^ 2 = 1 + 1 / d := by
    conv_rhs => rw [← sub_eq_zero, hidentity, mul_eq_zero,
      or_iff_right (div_ne_zero (by norm_num) hd')]
    constructor <;> intro h <;> linarith
  change (etaDen x y z 0 ≠ 0 ∧ ranadaEta x y z 0 = W) ↔
    (d * x = u * z - v * y ∧ x ^ 2 + (y + u / d) ^ 2 + (z + v / d) ^ 2 = 1 + 1 / d)
  rw [hcomplex, hcoordinates, hsolve, hsphere]

/-- The center of the sphere cutting out the initial affine fiber. -/
noncomputable def initialMagneticFiberCenter (u v : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![0, -u / (u ^ 2 + v ^ 2), -v / (u ^ 2 + v ^ 2)]

/-- The initial finite nonzero magnetic fiber is a central planar
section of an explicit Euclidean sphere. -/
theorem initialMagneticFiber_eq_plane_inter_sphere (u v : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    initialMagneticFiber u v =
      {s | (u ^ 2 + v ^ 2) * s 0 = u * s 2 - v * s 1} ∩
        Metric.sphere (initialMagneticFiberCenter u v) (Real.sqrt (1 + 1 / (u ^ 2 + v ^ 2))) := by
  let d := u ^ 2 + v ^ 2
  let a := initialMagneticFiberCenter u v
  have hr : 0 ≤ 1 + 1 / d := by positivity
  ext s
  rw [Set.mem_inter_iff, Metric.mem_sphere, dist_eq_norm,
    ← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), Real.sq_sqrt hr]
  have hnorm : ‖s - a‖ ^ 2 = (s 0) ^ 2 + (s 1 + u / d) ^ 2 + (s 2 + v / d) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp [a, initialMagneticFiberCenter, d, sub_neg_eq_add, neg_div]
  rw [hnorm]
  exact ranadaEta_initial_fiber_iff u v (s 0) (s 1) (s 2) hd

/-- The sphere center lies in the fiber plane, whose defining linear
functional is nonzero because the coefficient of the first coordinate
is positive. -/
theorem initialMagneticFiberCenter_in_plane (u v : ℝ) :
    (u ^ 2 + v ^ 2) * initialMagneticFiberCenter u v 0 =
      u * initialMagneticFiberCenter u v 2 - v * initialMagneticFiberCenter u v 1 := by
  simp [initialMagneticFiberCenter]
  ring

/-- Every initial magnetic fiber for a nonzero finite value is compact
in physical Euclidean space. -/
theorem initialMagneticFiber_isCompact (u v : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    IsCompact (initialMagneticFiber u v) := by
  rw [initialMagneticFiber_eq_plane_inter_sphere u v hd]
  have hcont (j : Fin 3) : Continuous (fun s : EuclideanSpace ℝ (Fin 3) => s j) :=
    PiLp.continuous_apply 2 _ j
  exact (isCompact_sphere _ _).inter_left
    (isClosed_eq (continuous_const.mul (hcont 0))
      ((continuous_const.mul (hcont 2)).sub (continuous_const.mul (hcont 1))))

/-- The initial affine fiber of the zero magnetic scalar is exactly the
`x`-axis, the fiber through the omitted stereographic point. -/
theorem ranadaEta_initial_zero_iff (x y z : ℝ) :
    (etaDen x y z 0 ≠ 0 ∧ ranadaEta x y z 0 = 0) ↔ y = 0 ∧ z = 0 := by
  have hA := (ranadaA_t_zero_pos x y z).ne'
  have hnum : etaNum x y z 0 = 0 ↔ y = 0 ∧ z = 0 := by
    rw [etaNum, ofReal_add_iMul_eq_zero_iff]
    simp [ranadaQ, ranadaR, hA, and_comm]
  constructor
  · rintro ⟨hd, hz⟩
    rw [ranadaEta_def, div_eq_zero_iff, or_iff_left hd] at hz
    exact hnum.1 hz
  · rintro ⟨hy, hz⟩
    refine ⟨?_, ?_⟩
    · intro hd
      have hf := (ranadaEta_den_zero_t_zero_iff x y z).1 hd
      norm_num [hy, hz] at hf
    · rw [ranadaEta_def, hnum.2 ⟨hy, hz⟩, zero_div]

end Qatlib.Papers.KnottedLight08.NullLinking
