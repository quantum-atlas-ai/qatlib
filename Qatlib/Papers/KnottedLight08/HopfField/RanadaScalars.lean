/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# The Rañada scalars of the Hopf field, exactly as printed

[IrvineBouwmeester2008KnottedLight], equation (2), p. 717,
[DOI](https://doi.org/10.1038/nphys1056).
The paper prints two stereographic spacetime scalars built from the single
real function `A = (x^2 + y^2 + z^2 - t^2 + 1) / 2` and its component letters

`P = A x + t y`, `Q = A z + t (A - 1)`, `R = t x - A y`, `S = A (A - 1) - t z`

as the ratios `zeta = (P + iQ) / (R + iS)` (entering the electric field) and
`eta = (Q + iR) / (P + iS)` (entering the magnetic field). This module records
the printed orientation faithfully: the magnetic scalar is `eta` and the
electric scalar is `zeta`, with the shared imaginary part `S` and the rotated
numerator/denominator pattern above.

The four real components `(P, Q, R, S)` are proved to never vanish
simultaneously on spacetime: their squared norm factors as
`(A^2 + t^2) * (x^2 + y^2 + z^2 + (A - 1)^2)` with both factors strictly
positive. Consequently both scalars define globally non-singular maps into the
Riemann sphere once poles are read in the reciprocal chart. The exact pole
loci at `t = 0` are the two unit coordinate circles, and for every `t` both
scalars have genuine poles on the two lightlike lines `(0, 0, t ± 1, t)`.
This module is pure algebra: gradients, fields, Maxwell equations, decay and
linking remain in the companion modules.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.HopfField

/-- The real function `A` of equation (2): half of `r^2 - t^2 + 1`. -/
noncomputable def ranadaA (x y z t : ℝ) : ℝ := (x ^ 2 + y ^ 2 + z ^ 2 - t ^ 2 + 1) / 2

/-- The first component letter of equation (2): `P = A x + t y`. -/
noncomputable def ranadaP (x y z t : ℝ) : ℝ := ranadaA x y z t * x + t * y

/-- The second component letter of equation (2): `Q = A z + t (A - 1)`. -/
noncomputable def ranadaQ (x y z t : ℝ) : ℝ := ranadaA x y z t * z + t * (ranadaA x y z t - 1)

/-- The third component letter of equation (2): `R = t x - A y`. -/
noncomputable def ranadaR (x y z t : ℝ) : ℝ := t * x - ranadaA x y z t * y

/-- The fourth component letter of equation (2): `S = A (A - 1) - t z`. -/
noncomputable def ranadaS (x y z t : ℝ) : ℝ := ranadaA x y z t * (ranadaA x y z t - 1) - t * z

/-- The printed magnetic scalar `eta = (Q + iR) / (P + iS)` of equation (2). -/
noncomputable def ranadaEta (x y z t : ℝ) : ℂ :=
  (ranadaQ x y z t + Complex.I * ranadaR x y z t) /
  (ranadaP x y z t + Complex.I * ranadaS x y z t)

/-- The printed electric scalar `zeta = (P + iQ) / (R + iS)` of equation (2). -/
noncomputable def ranadaZeta (x y z t : ℝ) : ℂ :=
  (ranadaP x y z t + Complex.I * ranadaQ x y z t) /
  (ranadaR x y z t + Complex.I * ranadaS x y z t)

/-- The quaternionic coordinate of the Rañada construction, as a real quadruple. -/
noncomputable def ranadaQuat (x y z t : ℝ) : Fin 4 → ℝ :=
  ![ranadaP x y z t, ranadaQ x y z t, ranadaR x y z t, ranadaS x y z t]

/-- A real-plus-imaginary real pair vanishes exactly when both parts vanish. -/
theorem ofReal_add_iMul_eq_zero_iff (p s : ℝ) :
    (p : ℂ) + Complex.I * (s : ℂ) = 0 ↔ p = 0 ∧ s = 0 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, Complex.zero_im, zero_mul, mul_zero, one_mul,
      add_zero, sub_zero] at hre him
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-! ### Nonvanishing of the quaternionic coordinate -/

/-- The letters `P` and `R` combine into the transverse factor of `A^2 + t^2`. -/
theorem ranadaP_sq_add_R_sq (x y z t : ℝ) :
    ranadaP x y z t ^ 2 + ranadaR x y z t ^ 2 =
      (ranadaA x y z t ^ 2 + t ^ 2) * (x ^ 2 + y ^ 2) := by
  simp only [ranadaP, ranadaR, ranadaA]
  ring

/-- The letters `Q` and `S` combine into the remaining factor of `A^2 + t^2`. -/
theorem ranadaQ_sq_add_S_sq (x y z t : ℝ) :
    ranadaQ x y z t ^ 2 + ranadaS x y z t ^ 2 =
      (ranadaA x y z t ^ 2 + t ^ 2) * (z ^ 2 + (ranadaA x y z t - 1) ^ 2) := by
  simp only [ranadaQ, ranadaS, ranadaA]
  ring

/-- The squared norm of the quaternionic coordinate factors into two parts. -/
theorem ranadaNormSq_eq (x y z t : ℝ) :
    ranadaP x y z t ^ 2 + ranadaQ x y z t ^ 2 + ranadaR x y z t ^ 2 +
        ranadaS x y z t ^ 2 =
      (ranadaA x y z t ^ 2 + t ^ 2) *
        (x ^ 2 + y ^ 2 + z ^ 2 + (ranadaA x y z t - 1) ^ 2) := by
  have h1 := ranadaP_sq_add_R_sq x y z t
  have h2 := ranadaQ_sq_add_S_sq x y z t
  simp only [ranadaP, ranadaQ, ranadaR, ranadaS, ranadaA] at h1 h2 ⊢
  linear_combination h1 + h2

/-- The first factor `A^2 + t^2` is strictly positive on spacetime. -/
theorem ranadaA_sq_add_t_sq_pos (x y z t : ℝ) :
    0 < ranadaA x y z t ^ 2 + t ^ 2 := by
  rcases eq_or_ne t 0 with rfl | ht
  · have hA : ranadaA x y z 0 = (x ^ 2 + y ^ 2 + z ^ 2 + 1) / 2 := by
      simp only [ranadaA]
      ring
    have hpos : 0 < x ^ 2 + y ^ 2 + z ^ 2 + 1 := by
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hne : ranadaA x y z 0 ≠ 0 := ne_of_gt (by rw [hA]; linarith)
    have hsq := sq_pos_of_ne_zero hne
    simpa using hsq
  · rcases lt_or_gt_of_ne ht with h | h
    · have ht2 : 0 < t ^ 2 := by nlinarith [h]
      nlinarith [sq_nonneg (ranadaA x y z t)]
    · have ht2 : 0 < t ^ 2 := by nlinarith [h]
      nlinarith [sq_nonneg (ranadaA x y z t)]

/-- The second factor `r^2 + (A - 1)^2` is strictly positive on spacetime. -/
theorem ranadaRadialGap_pos (x y z t : ℝ) :
    0 < x ^ 2 + y ^ 2 + z ^ 2 + (ranadaA x y z t - 1) ^ 2 := by
  have hgap : x ^ 2 + y ^ 2 + z ^ 2 + (ranadaA x y z t - 1) ^ 2 =
      x ^ 2 + y ^ 2 + z ^ 2 + ((x ^ 2 + y ^ 2 + z ^ 2 - t ^ 2 - 1) / 2) ^ 2 := by
    simp only [ranadaA]
    ring
  rw [hgap]
  have hr : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hs : 0 ≤ ((x ^ 2 + y ^ 2 + z ^ 2 - t ^ 2 - 1) / 2) ^ 2 := by positivity
  rcases lt_or_eq_of_le (add_nonneg hr hs) with h | h
  · exact h
  · exfalso
    have h1 : x ^ 2 + y ^ 2 + z ^ 2 = 0 := by nlinarith
    have h2 : ((x ^ 2 + y ^ 2 + z ^ 2 - t ^ 2 - 1) / 2) ^ 2 = 0 := by nlinarith
    have h4 := sq_eq_zero_iff.mp h2
    have h5 : x ^ 2 + y ^ 2 + z ^ 2 - t ^ 2 - 1 = 0 := by
      have hdiv := div_eq_zero_iff.mp h4
      rcases hdiv with hc | hc
      · exact hc
      · exact absurd hc (by norm_num)
    have ht2 : t ^ 2 = -1 := by linarith
    have := sq_nonneg t
    linarith

/-- The quaternionic coordinate never vanishes on spacetime. -/
theorem ranadaNormSq_pos (x y z t : ℝ) :
    0 < ranadaP x y z t ^ 2 + ranadaQ x y z t ^ 2 + ranadaR x y z t ^ 2 +
      ranadaS x y z t ^ 2 := by
  rw [ranadaNormSq_eq]
  exact mul_pos (ranadaA_sq_add_t_sq_pos x y z t) (ranadaRadialGap_pos x y z t)

/-! ### Exact pole loci -/

/-- The value of `A` at `t = 0` in terms of the spatial radius. -/
theorem ranadaA_t_zero (x y z : ℝ) :
    ranadaA x y z 0 = (x ^ 2 + y ^ 2 + z ^ 2 + 1) / 2 := by
  simp only [ranadaA]
  ring

/-- At `t = 0`, `A` is bounded below by one half. -/
theorem ranadaA_t_zero_pos (x y z : ℝ) : 0 < ranadaA x y z 0 := by
  have hpos : 0 < x ^ 2 + y ^ 2 + z ^ 2 + 1 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  rw [ranadaA_t_zero]
  linarith

/-- At `t = 0` the magnetic scalar has poles exactly on the unit circle of the
`y`-`z` plane. -/
theorem ranadaEta_den_zero_t_zero_iff (x y z : ℝ) :
    ranadaP x y z 0 + Complex.I * ranadaS x y z 0 = 0 ↔ x = 0 ∧ y ^ 2 + z ^ 2 = 1 := by
  constructor
  · intro h
    obtain ⟨hP0, hS0⟩ := (ofReal_add_iMul_eq_zero_iff _ _).mp h
    have hApos := ranadaA_t_zero_pos x y z
    have hPx : ranadaA x y z 0 * x = 0 := by
      have h := hP0
      simp only [ranadaP, zero_mul, add_zero] at h
      exact h
    have hSA : ranadaA x y z 0 * (ranadaA x y z 0 - 1) = 0 := by
      have h := hS0
      simp only [ranadaS, zero_mul, sub_zero] at h
      exact h
    have hx : x = 0 := by
      by_contra hx
      exact mul_ne_zero (ne_of_gt hApos) hx hPx
    have hA1 : ranadaA x y z 0 - 1 = 0 := by
      by_contra hA1
      exact mul_ne_zero (ne_of_gt hApos) hA1 hSA
    have hAeq : ranadaA x y z 0 = 1 := by linarith
    subst hx
    rw [ranadaA_t_zero] at hAeq
    norm_num at hAeq
    exact ⟨rfl, by linarith⟩
  · rintro ⟨rfl, hyz⟩
    have hA1 : ranadaA 0 y z 0 = 1 := by
      norm_num [ranadaA, hyz]
    simp only [ranadaP, ranadaS, hA1]
    norm_num

/-- At `t = 0` the electric scalar has poles exactly on the unit circle of the
`x`-`z` plane. -/
theorem ranadaZeta_den_zero_t_zero_iff (x y z : ℝ) :
    ranadaR x y z 0 + Complex.I * ranadaS x y z 0 = 0 ↔ y = 0 ∧ x ^ 2 + z ^ 2 = 1 := by
  constructor
  · intro h
    obtain ⟨hR0, hS0⟩ := (ofReal_add_iMul_eq_zero_iff _ _).mp h
    have hApos := ranadaA_t_zero_pos x y z
    have hRy : ranadaA x y z 0 * y = 0 := by
      have h := hR0
      simp only [ranadaR, zero_mul] at h
      linarith
    have hSA : ranadaA x y z 0 * (ranadaA x y z 0 - 1) = 0 := by
      have h := hS0
      simp only [ranadaS, zero_mul, sub_zero] at h
      exact h
    have hy : y = 0 := by
      by_contra hy
      exact mul_ne_zero (ne_of_gt hApos) hy hRy
    have hA1 : ranadaA x y z 0 - 1 = 0 := by
      by_contra hA1
      exact mul_ne_zero (ne_of_gt hApos) hA1 hSA
    have hAeq : ranadaA x y z 0 = 1 := by linarith
    subst hy
    rw [ranadaA_t_zero] at hAeq
    norm_num at hAeq
    exact ⟨rfl, by linarith⟩
  · rintro ⟨rfl, hxz⟩
    have hA1 : ranadaA x 0 z 0 = 1 := by
      norm_num [ranadaA, hxz]
    simp only [ranadaR, ranadaS, hA1]
    norm_num

/-- Both scalars have genuine poles on the future lightlike line: the shared
denominator parts vanish while the shared numerator survives. -/
theorem ranada_pole_futureLine (t : ℝ) :
    ranadaP 0 0 (t + 1) t = 0 ∧ ranadaS 0 0 (t + 1) t = 0 ∧ ranadaR 0 0 (t + 1) t = 0 ∧
      ranadaQ 0 0 (t + 1) t ≠ 0 := by
  have hA : ranadaA 0 0 (t + 1) t = t + 1 := by
    simp only [ranadaA]
    ring
  refine ⟨by simp only [ranadaP, hA]; norm_num, ?_, ?_, ?_⟩
  · simp only [ranadaS, hA]
    ring
  · simp only [ranadaR, hA]
    ring
  · simp only [ranadaQ, hA]
    nlinarith [sq_nonneg (2 * t + 1)]

/-- Both scalars have genuine poles on the past lightlike line as well. -/
theorem ranada_pole_pastLine (t : ℝ) :
    ranadaP 0 0 (t - 1) t = 0 ∧ ranadaS 0 0 (t - 1) t = 0 ∧ ranadaR 0 0 (t - 1) t = 0 ∧
      ranadaQ 0 0 (t - 1) t ≠ 0 := by
  have hA : ranadaA 0 0 (t - 1) t = 1 - t := by
    simp only [ranadaA]
    ring
  refine ⟨by simp only [ranadaP, hA]; norm_num, ?_, ?_, ?_⟩
  · simp only [ranadaS, hA]
    ring
  · simp only [ranadaR, hA]
    ring
  · simp only [ranadaQ, hA]
    nlinarith [sq_nonneg (2 * t - 1)]

end Qatlib.Papers.KnottedLight08.HopfField
