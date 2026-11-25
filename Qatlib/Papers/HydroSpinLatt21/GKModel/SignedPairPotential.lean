/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-!
# Signed pair potential of the generalized Kuramoto model

[Saenz2021HydroSpinLattices], Methods equations (24)-(26), introduces the
generalized Kuramoto pair potential
`U_ij = (a/2) (cos φ_i - cos φ_j)^2 + (b/2) (sin φ_i - sin φ_j)^2`
between the orbital phases of two neighboring spin states, with the signed
coefficients `a/2` and `b/2` proportional, respectively, to the curvature
`J₀''(k_F L)` and the gradient `J₀' (k_F L)` of the coupling wave field. See
[the article](https://doi.org/10.1038/s41586-021-03682-1).

This file establishes the exact two-body theory of that potential. The
coefficients are opaque signed real parameters: the potential is symmetric
under exchange of the two phases, its negative phase gradient is the explicit
coupling force entering equation (23), and synchronized phases are always a
critical point. The main results classify the global minimizers for each sign
combination of the two coefficients, recovering the four synchronization
geometries of the paper's Figure 2f at the level of the pair potential:
in-phase rotation (FM+), phase-opposed azimuthal positions with opposite
sines (AFM+), out-of-phase rotation with vanishing sines (FM-), and the
out-of-phase counter-rotating geometry with vanishing cosines (AFM-). In the
quadrant where both coefficients are negative the minimum value is twice the
smaller coefficient, attained at the FM- geometry when `a < b` (curvature
coefficient more negative) and at the AFM- geometry when `b < a`, so the sign
pair selects the phase relation while the rotation sense is decided by the
relative magnitude; this refines the paper's sign-only quadrant picture. The physical
identification of the coefficients with derivatives of the Bessel-approximated
Faraday wave field (equations (25), (26)) is proved in
`Qatlib.Papers.HydroSpinLatt21.GKModel.BesselCoefficientBridge`; no Bessel
function enters here, and sign conclusions require nonzero parameters, since
synchronized phases are always critical.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HydroSpinLatt21.GKModel

open Real

/-- The squared cosine difference of two orbital phases, the coefficient of
`a / 2` in the pair potential of equation (24). -/
def cosGapSq (x y : ℝ) : ℝ := (cos x - cos y) ^ 2

/-- The squared sine difference of two orbital phases, the coefficient of
`b / 2` in the pair potential of equation (24). -/
def sinGapSq (x y : ℝ) : ℝ := (sin x - sin y) ^ 2

/-- The generalized Kuramoto pair potential, equation (24): the signed
coefficient `a / 2` weights the squared cosine difference and `b / 2` weights
the squared sine difference of the two orbital phases. -/
def gkPairPotential (a b x y : ℝ) : ℝ :=
  (a / 2) * ((cos x - cos y) * (cos x - cos y))
    + (b / 2) * ((sin x - sin y) * (sin x - sin y))

/-- The coupling force on the first phase, that is, the negative phase
gradient `-∂U_ij/∂φ_i` of the pair potential appearing in equation (23). -/
def gkPairForce (a b x y : ℝ) : ℝ :=
  a * sin x * (cos x - cos y) - b * cos x * (sin x - sin y)

/-- The pair potential splits into the signed cosine and sine gap contributions. -/
theorem gkPairPotential_eq (a b x y : ℝ) :
    gkPairPotential a b x y = (a / 2) * cosGapSq x y + (b / 2) * sinGapSq x y := by
  unfold gkPairPotential cosGapSq sinGapSq
  ring

/-- Equation (24) is symmetric under exchange of the two interacting
phases: `U_ij = U_ji`. -/
theorem gk_pair_potential_exchange (a b x y : ℝ) :
    gkPairPotential a b x y = gkPairPotential a b y x := by
  unfold gkPairPotential
  ring

/-- A real number with absolute value two is either of the two signed
values. -/
theorem eq_two_or_neg_two_of_abs_eq_two {v : ℝ} (hv : |v| = 2) :
    v = 2 ∨ v = -2 := by
  rcases lt_or_ge 0 v with hv' | hv'
  · exact Or.inl ((abs_of_nonneg hv'.le).symm.trans hv)
  · have hnp : -v = |v| := by rw [abs_of_nonpos (by linarith : v ≤ 0)]
    rw [hv] at hnp
    exact Or.inr (by linarith)

/-- The squared gaps satisfy the half-angle identity
`(cos x - cos y)^2 + (sin x - sin y)^2 = 4 sin^2((x - y)/2)`. -/
theorem cosGapSq_add_sinGapSq (x y : ℝ) :
    cosGapSq x y + sinGapSq x y = 4 * sin ((x - y) / 2) ^ 2 := by
  have hcos : cos (x - y) = cos x * cos y + sin x * sin y := Real.cos_sub x y
  have hsum : cosGapSq x y + sinGapSq x y = 2 - 2 * cos (x - y) := by
    unfold cosGapSq sinGapSq
    have p1 := Real.sin_sq_add_cos_sq x
    have p2 := Real.sin_sq_add_cos_sq y
    have e : (cos x - cos y) ^ 2 + (sin x - sin y) ^ 2
        = 2 - 2 * (cos x * cos y + sin x * sin y) := by
      linarith [p1, p2]
    rw [e, hcos]
  have hc2 : cos (x - y) = 2 * cos ((x - y) / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul ((x - y) / 2)
    have hu : 2 * ((x - y) / 2) = x - y := by ring
    rw [hu] at h
    exact h
  have hp : sin ((x - y) / 2) ^ 2 + cos ((x - y) / 2) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq ((x - y) / 2)
  have hs2 : sin ((x - y) / 2) ^ 2 = 1 - cos ((x - y) / 2) ^ 2 := by linarith
  rw [hsum, hc2, hs2]
  ring

/-- The squared difference of the phase cosines is nonnegative. -/
theorem cosGapSq_nonneg (x y : ℝ) : 0 ≤ cosGapSq x y := by
  unfold cosGapSq; exact sq_nonneg _

/-- The squared difference of the phase sines is nonnegative. -/
theorem sinGapSq_nonneg (x y : ℝ) : 0 ≤ sinGapSq x y := by
  unfold sinGapSq; exact sq_nonneg _

/-- The squared cosine gap is bounded by four for any two phases. -/
theorem cosGapSq_le_four (x y : ℝ) : cosGapSq x y ≤ 4 := by
  have h1 : -2 ≤ cos x - cos y := by
    linarith [Real.neg_one_le_cos x, Real.cos_le_one y]
  have h2 : cos x - cos y ≤ 2 := by
    linarith [Real.cos_le_one x, Real.neg_one_le_cos y]
  have h := sq_le_sq' h1 h2
  unfold cosGapSq at h ⊢
  exact h.trans_eq (by norm_num : (2 : ℝ) ^ 2 = 4)

/-- The squared sine gap is bounded by four for any two phases. -/
theorem sinGapSq_le_four (x y : ℝ) : sinGapSq x y ≤ 4 := by
  have h1 : -2 ≤ sin x - sin y := by
    linarith [Real.neg_one_le_sin x, Real.sin_le_one y]
  have h2 : sin x - sin y ≤ 2 := by
    linarith [Real.sin_le_one x, Real.neg_one_le_sin y]
  have h := sq_le_sq' h1 h2
  unfold sinGapSq at h ⊢
  exact h.trans_eq (by norm_num : (2 : ℝ) ^ 2 = 4)

/-- Both squared gaps are bounded by `4` in total, since they sum to a
squared sine. -/
theorem cosGapSq_add_sinGapSq_le_four (x y : ℝ) :
    cosGapSq x y + sinGapSq x y ≤ 4 := by
  rw [cosGapSq_add_sinGapSq]
  have h1 : sin ((x - y) / 2) ^ 2 ≤ 1 := by
    have h := sq_le_sq' (Real.neg_one_le_sin ((x - y) / 2))
      (Real.sin_le_one ((x - y) / 2))
    simpa using h
  have h2 : 4 * sin ((x - y) / 2) ^ 2 ≤ 4 * 1 := by
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  simpa using h2

/-- A phase whose sine equals one has vanishing cosine. -/
theorem cos_eq_zero_of_sin_eq_one {x : ℝ} (hx : sin x = 1) : cos x = 0 := by
  have h := Real.sin_sq_add_cos_sq x
  rw [hx] at h
  norm_num at h
  exact h

/-- A phase whose sine equals minus one has vanishing cosine. -/
theorem cos_eq_zero_of_sin_eq_neg_one {x : ℝ} (hx : sin x = -1) : cos x = 0 := by
  have h := Real.sin_sq_add_cos_sq x
  rw [hx] at h
  norm_num at h
  exact h

/-- A phase whose cosine equals one has vanishing sine. -/
theorem sin_eq_zero_of_cos_eq_one {x : ℝ} (hx : cos x = 1) : sin x = 0 := by
  have h := Real.sin_sq_add_cos_sq x
  rw [hx] at h
  norm_num at h
  exact h

/-- A phase whose cosine equals minus one has vanishing sine. -/
theorem sin_eq_zero_of_cos_eq_neg_one {x : ℝ} (hx : cos x = -1) : sin x = 0 := by
  have h := Real.sin_sq_add_cos_sq x
  rw [hx] at h
  norm_num at h
  exact h

/-- Two phases have squared cosine gap four exactly in the two antiphase
horizontal configurations. -/
theorem cosGapSq_eq_four_iff (x y : ℝ) :
    cosGapSq x y = 4 ↔
      cos x = 1 ∧ cos y = -1 ∧ sin x = 0 ∧ sin y = 0 ∨
      cos x = -1 ∧ cos y = 1 ∧ sin x = 0 ∧ sin y = 0 := by
  constructor
  · intro h
    have hsq : (cos x - cos y) ^ 2 = (2 : ℝ) ^ 2 := by
      unfold cosGapSq at h
      rw [h]
      norm_num
    rw [sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hsq
    rcases eq_two_or_neg_two_of_abs_eq_two hsq with h | h
    · have hcx : cos x = 1 := by
        have h1 := Real.cos_le_one x
        have h2 := Real.neg_one_le_cos y
        linarith
      have hcy : cos y = -1 := by
        have h1 := Real.cos_le_one y
        have h2 := Real.neg_one_le_cos x
        linarith
      refine Or.inl ⟨hcx, hcy, sin_eq_zero_of_cos_eq_one hcx, sin_eq_zero_of_cos_eq_neg_one hcy⟩
    · have hcx : cos x = -1 := by
        have h1 := Real.cos_le_one y
        have h2 := Real.neg_one_le_cos x
        linarith
      have hcy : cos y = 1 := by
        have h1 := Real.cos_le_one x
        have h2 := Real.neg_one_le_cos y
        linarith
      refine Or.inr ⟨hcx, hcy, sin_eq_zero_of_cos_eq_neg_one hcx, sin_eq_zero_of_cos_eq_one hcy⟩
  · rintro (⟨hx1, hy1, _, _⟩ | ⟨hx1, hy1, _, _⟩)
    · unfold cosGapSq; rw [hx1, hy1]; ring
    · unfold cosGapSq; rw [hx1, hy1]; ring

/-- Two phases have squared sine gap four exactly when their sines are
opposite extremes, which forces both cosines to vanish. -/
theorem sinGapSq_eq_four_iff (x y : ℝ) :
    sinGapSq x y = 4 ↔
      sin x = 1 ∧ sin y = -1 ∧ cos x = 0 ∧ cos y = 0 ∨
      sin x = -1 ∧ sin y = 1 ∧ cos x = 0 ∧ cos y = 0 := by
  constructor
  · intro h
    have hsq : (sin x - sin y) ^ 2 = (2 : ℝ) ^ 2 := by
      unfold sinGapSq at h
      rw [h]
      norm_num
    rw [sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hsq
    rcases eq_two_or_neg_two_of_abs_eq_two hsq with h | h
    · have hx1 : sin x = 1 := by
        have h1 := Real.sin_le_one x
        have h2 := Real.neg_one_le_sin y
        linarith
      have hy1 : sin y = -1 := by
        have h1 := Real.sin_le_one x
        have h2 := Real.neg_one_le_sin y
        linarith
      exact Or.inl ⟨hx1, hy1, cos_eq_zero_of_sin_eq_one hx1, cos_eq_zero_of_sin_eq_neg_one hy1⟩
    · have hx1 : sin x = -1 := by
        have h1 := Real.sin_le_one y
        have h2 := Real.neg_one_le_sin x
        linarith
      have hy1 : sin y = 1 := by
        have h1 := Real.sin_le_one y
        have h2 := Real.neg_one_le_sin x
        linarith
      exact Or.inr ⟨hx1, hy1, cos_eq_zero_of_sin_eq_neg_one hx1, cos_eq_zero_of_sin_eq_one hy1⟩
  · rintro (⟨hx1, hy1, _, _⟩ | ⟨hx1, hy1, _, _⟩)
    · unfold sinGapSq; rw [hx1, hy1]; ring
    · unfold sinGapSq; rw [hx1, hy1]; ring

/-- Both squared gaps vanish simultaneously exactly when the two phases
differ by an integer multiple of the full period. -/
theorem cosGapSq_eq_zero_and_sinGapSq_eq_zero_iff (x y : ℝ) :
    cosGapSq x y = 0 ∧ sinGapSq x y = 0 ↔ ∃ n : ℤ, x = y + (n : ℝ) * (2 * Real.pi) := by
  constructor
  · rintro ⟨hcos, hsin⟩
    have hc : cos x = cos y := by
      unfold cosGapSq at hcos
      have h := (sq_eq_zero_iff).1 hcos
      linarith [h]
    have hs : sin x = sin y := by
      unfold sinGapSq at hsin
      have h := (sq_eq_zero_iff).1 hsin
      linarith [h]
    have hsub : Real.sin (x - y) = sin x * cos y - cos x * sin y := Real.sin_sub x y
    have hsxy2 : sin x * cos y = sin y * cos y := by rw [← hs]
    have hcxy2 : cos x * sin y = cos y * sin y := by rw [← hc]
    have hsinxy : Real.sin (x - y) = 0 := by
      rw [hsub, hsxy2, hcxy2]
      ring
    have hexp : cos (x - y) = 1 := by
      have hcosxy : Real.cos (x - y) = cos y * cos y + sin y * sin y := by
        have hadd : Real.cos (x - y) = cos x * cos y + sin x * sin y := Real.cos_sub x y
        have hcxy : cos x * cos y = cos y * cos y := by rw [hc]
        have hsxy : sin x * sin y = sin y * sin y := by rw [hs]
        rw [hadd, hcxy, hsxy]
      have hpythy : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 :=
        Real.sin_sq_add_cos_sq y
      rw [hcosxy]
      linarith
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (x - y)).1 hexp
    exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩
    have hsin : sin (y + (n : ℝ) * (2 * Real.pi)) = sin y :=
      Real.sin_add_int_mul_two_pi y n
    have hcos : cos (y + (n : ℝ) * (2 * Real.pi)) = cos y :=
      Real.cos_add_int_mul_two_pi y n
    refine ⟨?_, ?_⟩
    · unfold cosGapSq; rw [hn, hcos]; ring
    · unfold sinGapSq; rw [hn, hsin]; ring

/-- The phase gradient of the pair potential in its first argument, as an
explicit polynomial in sines and cosines. -/
theorem gk_pair_potential_has_deriv_at_first (a b x y : ℝ) :
    HasDerivAt (fun t => gkPairPotential a b t y)
      (-a * sin x * (cos x - cos y) + b * cos x * (sin x - sin y)) x := by
  have hc : HasDerivAt (fun t => cos t - cos y) (-sin x) x := by
    refine HasDerivAt.congr_deriv
      (HasDerivAt.sub (hasDerivAt_cos x) (hasDerivAt_const x (cos y))) ?_
    ring
  have hs : HasDerivAt (fun t => sin t - sin y) (cos x) x := by
    refine HasDerivAt.congr_deriv
      (HasDerivAt.sub (hasDerivAt_sin x) (hasDerivAt_const x (sin y))) ?_
    ring
  have h1 : HasDerivAt (fun t => (a / 2) * ((cos t - cos y) * (cos t - cos y)))
      ((a / 2) * ((-sin x) * (cos x - cos y) + (cos x - cos y) * (-sin x))) x :=
    HasDerivAt.const_mul (a / 2) (HasDerivAt.mul hc hc)
  have h2 : HasDerivAt (fun t => (b / 2) * ((sin t - sin y) * (sin t - sin y)))
      ((b / 2) * (cos x * (sin x - sin y) + (sin x - sin y) * cos x)) x :=
    HasDerivAt.const_mul (b / 2) (HasDerivAt.mul hs hs)
  refine HasDerivAt.congr_deriv (HasDerivAt.add h1 h2) ?_
  ring

/-- The negative phase gradient of the pair potential is exactly the
coupling force `gkPairForce` of equation (23). -/
theorem gk_pair_potential_has_deriv_at (a b x y : ℝ) :
    HasDerivAt (fun t => gkPairPotential a b t y) (-(gkPairForce a b x y)) x :=
  HasDerivAt.congr_deriv (gk_pair_potential_has_deriv_at_first a b x y) (by
    unfold gkPairForce
    ring)

/-- By exchange symmetry, the phase gradient in the second argument is the
negated coupling force of the transposed pair. -/
theorem gk_pair_potential_has_deriv_at_second (a b x y : ℝ) :
    HasDerivAt (fun t => gkPairPotential a b x t) (-(gkPairForce a b y x)) y := by
  have h : (fun t => gkPairPotential a b x t) = (fun t => gkPairPotential a b t x) :=
    funext fun t => gk_pair_potential_exchange a b x t
  rw [h]
  exact gk_pair_potential_has_deriv_at a b y x

/-- Synchronized phases are a critical point of the pair potential: the
coupling force vanishes identically there, for all coefficient values. -/
theorem gk_pair_force_self_eq_zero (a b x : ℝ) : gkPairForce a b x x = 0 := by
  unfold gkPairForce
  ring

/-- Splitting lemma for the mixed-sign quadrant with positive curvature and
negative gradient coefficients: the weighted gap sum equals `2 * b` exactly
at vanishing cosine gap and maximal sine gap. -/
theorem gap_sum_eq_min_iff_of_a_pos_b_neg (a b x y : ℝ) (ha : 0 < a) (hb : b < 0) :
    (a / 2) * cosGapSq x y + (b / 2) * sinGapSq x y = 2 * b ↔
      cosGapSq x y = 0 ∧ sinGapSq x y = 4 := by
  constructor
  · intro h
    have hb2 : b / 2 < 0 := by linarith
    have hZ : (b / 2) * 4 = 2 * b := by ring
    have hB : sinGapSq x y = 4 := by
      by_contra hB
      rcases lt_or_gt_of_ne hB with hlt | hlt
      · have hraw := mul_lt_mul_of_neg_right hlt hb2
        rw [mul_comm 4 (b / 2), mul_comm (sinGapSq x y) (b / 2)] at hraw
        have hA : 0 ≤ (a / 2) * cosGapSq x y :=
          mul_nonneg (by linarith) (cosGapSq_nonneg x y)
        exact absurd h (by linarith)
      · exact absurd hlt (by linarith [sinGapSq_le_four x y])
    refine ⟨?_, hB⟩
    by_contra hA
    have hpos : 0 < (a / 2) * cosGapSq x y :=
      mul_pos (by linarith) (lt_of_le_of_ne (cosGapSq_nonneg x y) (Ne.symm hA))
    rw [hB, hZ] at h
    linarith
  · rintro ⟨hA, hB⟩
    rw [hA, hB]
    ring

/-- Splitting lemma for the mixed-sign quadrant with negative curvature and
positive gradient coefficients: the weighted gap sum equals `2 * a` exactly
at maximal cosine gap and vanishing sine gap. -/
theorem gap_sum_eq_min_iff_of_a_neg_b_pos (a b x y : ℝ) (ha : a < 0) (hb : 0 < b) :
    (a / 2) * cosGapSq x y + (b / 2) * sinGapSq x y = 2 * a ↔
      cosGapSq x y = 4 ∧ sinGapSq x y = 0 := by
  constructor
  · intro h
    have ha2 : a / 2 < 0 := by linarith
    have hZ : (a / 2) * 4 = 2 * a := by ring
    have hA : cosGapSq x y = 4 := by
      by_contra hA
      rcases lt_or_gt_of_ne hA with hlt | hlt
      · have hraw := mul_lt_mul_of_neg_right hlt ha2
        rw [mul_comm 4 (a / 2), mul_comm (cosGapSq x y) (a / 2)] at hraw
        have hB : 0 ≤ (b / 2) * sinGapSq x y :=
          mul_nonneg (by linarith) (sinGapSq_nonneg x y)
        exact absurd h (by linarith)
      · exact absurd hlt (by linarith [cosGapSq_le_four x y])
    refine ⟨hA, ?_⟩
    by_contra hB
    have hpos : 0 < (b / 2) * sinGapSq x y :=
      mul_pos (by linarith) (lt_of_le_of_ne (sinGapSq_nonneg x y) (Ne.symm hB))
    rw [hA, hZ] at h
    linarith
  · rintro ⟨hA, hB⟩
    rw [hA, hB]
    ring

/-- Both coefficient signs nonnegative make the pair potential nonnegative. -/
theorem gk_pair_potential_nonneg (a b x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ gkPairPotential a b x y := by
  rw [gkPairPotential_eq]
  exact add_nonneg (mul_nonneg (by positivity) (cosGapSq_nonneg x y))
    (mul_nonneg (by positivity) (sinGapSq_nonneg x y))

/-- With both coefficients positive, the pair potential is nonnegative, so
the in-phase configuration realizes the global minimum value zero. This is
the potential-level statement of the ferromagnetic in-phase preference
(FM+ in the notation of the paper's Figure 2f). -/
theorem gk_pair_potential_min_iff_of_a_pos_b_pos (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b) :
    gkPairPotential a b x y = 0 ↔ ∃ n : ℤ, x = y + (n : ℝ) * (2 * Real.pi) := by
  rw [gkPairPotential_eq]
  constructor
  · intro h
    have hA : cosGapSq x y = 0 := by
      by_contra hA
      have hpos : 0 < (a / 2) * cosGapSq x y :=
        mul_pos (by linarith) (lt_of_le_of_ne (cosGapSq_nonneg x y) (Ne.symm hA))
      have hB : 0 ≤ (b / 2) * sinGapSq x y :=
        mul_nonneg (by linarith) (sinGapSq_nonneg x y)
      linarith
    have hB : sinGapSq x y = 0 := by
      by_contra hB
      have hpos : 0 < (b / 2) * sinGapSq x y :=
        mul_pos (by linarith) (lt_of_le_of_ne (sinGapSq_nonneg x y) (Ne.symm hB))
      have hA : 0 ≤ (a / 2) * cosGapSq x y :=
        mul_nonneg (by linarith) (cosGapSq_nonneg x y)
      linarith
    exact (cosGapSq_eq_zero_and_sinGapSq_eq_zero_iff x y).1 ⟨hA, hB⟩
  · rintro ⟨n, hn⟩
    obtain ⟨hA, hB⟩ := (cosGapSq_eq_zero_and_sinGapSq_eq_zero_iff x y).2 ⟨n, hn⟩
    rw [hA, hB]
    ring

/-- With positive curvature coefficient and negative gradient coefficient,
the global minimum of the pair potential is `2 * b`, attained exactly when
the two phases carry opposite sines of unit magnitude and a common vanishing
cosine, the geometric signature of in-phase counter-rotating orbits (AFM+). -/
theorem gk_pair_potential_min_iff_of_a_pos_b_neg (a b x y : ℝ) (ha : 0 < a) (hb : b < 0) :
    gkPairPotential a b x y = 2 * b ↔
      sin x = 1 ∧ sin y = -1 ∧ cos x = 0 ∧ cos y = 0 ∨
      sin x = -1 ∧ sin y = 1 ∧ cos x = 0 ∧ cos y = 0 := by
  rw [gkPairPotential_eq, gap_sum_eq_min_iff_of_a_pos_b_neg a b x y ha hb]
  constructor
  · rintro ⟨_, hB4⟩
    exact (sinGapSq_eq_four_iff x y).1 hB4
  · rintro (⟨hx1, hy1, hc1, hc2⟩ | ⟨hx1, hy1, hc1, hc2⟩) <;>
      exact ⟨by unfold cosGapSq; rw [hc1, hc2]; ring,
        by unfold sinGapSq; rw [hx1, hy1]; ring⟩

/-- With negative curvature coefficient and positive gradient coefficient,
the global minimum of the pair potential is `2 * a`, attained exactly in the
two antiphase configurations with vanishing sines, the geometric signature
of out-of-phase co-rotating orbits (FM-). -/
theorem gk_pair_potential_min_iff_of_a_neg_b_pos (a b x y : ℝ) (ha : a < 0) (hb : 0 < b) :
    gkPairPotential a b x y = 2 * a ↔
      cos x = 1 ∧ cos y = -1 ∧ sin x = 0 ∧ sin y = 0 ∨
      cos x = -1 ∧ cos y = 1 ∧ sin x = 0 ∧ sin y = 0 := by
  rw [gkPairPotential_eq, gap_sum_eq_min_iff_of_a_neg_b_pos a b x y ha hb]
  constructor
  · rintro ⟨hA4, _⟩
    exact (cosGapSq_eq_four_iff x y).1 hA4
  · rintro (⟨hx1, hy1, hs1, hs2⟩ | ⟨hx1, hy1, hs1, hs2⟩) <;>
      exact ⟨by unfold cosGapSq; rw [hx1, hy1]; ring,
        by unfold sinGapSq; rw [hs1, hs2]; ring⟩

/-- With both coefficients negative and `a ≤ b`, the pair potential is
bounded below by twice the smaller coefficient `2 * min a b = 2 * a`. -/
theorem gk_pair_potential_ge_two_mul_min (a b x y : ℝ) (ha : a < 0) (_hb : b < 0)
    (hab : a ≤ b) :
    2 * min a b ≤ gkPairPotential a b x y := by
  have h2 : 2 * min a b = 2 * a := by rw [min_eq_left hab]
  rw [h2, gkPairPotential_eq]
  have hsplit : (a / 2) * cosGapSq x y + (b / 2) * sinGapSq x y - 2 * a
      = (a / 2) * (cosGapSq x y + sinGapSq x y - 4) + ((b - a) / 2) * sinGapSq x y := by
    ring
  have h1 : 0 ≤ (a / 2) * (cosGapSq x y + sinGapSq x y - 4) := by
    refine mul_nonneg_of_nonpos_of_nonpos (by linarith) ?_
    have hsum := cosGapSq_add_sinGapSq_le_four x y
    linarith
  have h2' : 0 ≤ ((b - a) / 2) * sinGapSq x y :=
    mul_nonneg (by linarith) (sinGapSq_nonneg x y)
  linarith

/-- With both coefficients negative and `b ≤ a`, the symmetric bound holds
with the roles of the two gaps exchanged. -/
theorem gk_pair_potential_ge_two_mul_min' (a b x y : ℝ) (_ha : a < 0) (hb : b < 0)
    (hab : b ≤ a) :
    2 * min a b ≤ gkPairPotential a b x y := by
  have h2 : 2 * min a b = 2 * b := by rw [min_eq_right hab]
  rw [h2, gkPairPotential_eq]
  have hsplit : (a / 2) * cosGapSq x y + (b / 2) * sinGapSq x y - 2 * b
      = (b / 2) * (cosGapSq x y + sinGapSq x y - 4) + ((a - b) / 2) * cosGapSq x y := by
    ring
  have h1 : 0 ≤ (b / 2) * (cosGapSq x y + sinGapSq x y - 4) := by
    refine mul_nonneg_of_nonpos_of_nonpos (by linarith) ?_
    have hsum := cosGapSq_add_sinGapSq_le_four x y
    linarith
  have h2' : 0 ≤ ((a - b) / 2) * cosGapSq x y :=
    mul_nonneg (by linarith) (cosGapSq_nonneg x y)
  linarith

/-- In the quadrant with both coefficients negative and `a < b` (the
curvature coefficient strictly more negative), the global minimum `2 * a` is
attained exactly at the out-of-phase co-rotating geometry (FM-); in this
quadrant the rotation sense is selected by the relative magnitudes, refining
the paper's sign-only quadrant picture. -/
theorem gk_pair_potential_min_iff_of_both_neg (a b x y : ℝ) (hb : b < 0)
    (hab : a < b) :
    gkPairPotential a b x y = 2 * a ↔
      cos x = 1 ∧ cos y = -1 ∧ sin x = 0 ∧ sin y = 0 ∨
      cos x = -1 ∧ cos y = 1 ∧ sin x = 0 ∧ sin y = 0 := by
  rw [gkPairPotential_eq]
  have hsplit : (a / 2) * cosGapSq x y + (b / 2) * sinGapSq x y - 2 * a
      = (a / 2) * (cosGapSq x y + sinGapSq x y - 4) + ((b - a) / 2) * sinGapSq x y := by
    ring
  have h1 : 0 ≤ (a / 2) * (cosGapSq x y + sinGapSq x y - 4) := by
    refine mul_nonneg_of_nonpos_of_nonpos (by linarith) ?_
    have hsum := cosGapSq_add_sinGapSq_le_four x y
    linarith
  have h2' : 0 < ((b - a) / 2) * sinGapSq x y ∨ ((b - a) / 2) * sinGapSq x y = 0 := by
    rcases eq_or_ne (sinGapSq x y) 0 with hzero | hne
    · exact Or.inr (by rw [hzero]; ring)
    · exact Or.inl (mul_pos (by linarith)
        (lt_of_le_of_ne (sinGapSq_nonneg x y) (Ne.symm hne)))
  constructor
  · intro h
    have hxy : (a / 2) * (cosGapSq x y + sinGapSq x y - 4)
        + ((b - a) / 2) * sinGapSq x y = 0 := by
      rw [← hsplit]
      linarith
    have hY : ((b - a) / 2) * sinGapSq x y = 0 := by
      rcases h2' with hpos | hzero
      · linarith
      · exact hzero
    have hX : (a / 2) * (cosGapSq x y + sinGapSq x y - 4) = 0 := by linarith
    have hane : a / 2 ≠ 0 := by linarith
    have hsum4 : cosGapSq x y + sinGapSq x y = 4 := by
      have := (mul_eq_zero).1 hX
      rcases this with hz | hz
      · exact absurd hz hane
      · linarith
    have hB0 : sinGapSq x y = 0 := by
      rcases (mul_eq_zero).1 hY with hz | hz
      · exact absurd hz (by linarith)
      · exact hz
    have hA4 : cosGapSq x y = 4 := by linarith
    exact (cosGapSq_eq_four_iff x y).1 hA4
  · rintro (⟨hx1, hy1, hs1, hs2⟩ | ⟨hx1, hy1, hs1, hs2⟩)
    · have hA : cosGapSq x y = 4 := by unfold cosGapSq; rw [hx1, hy1]; ring
      have hB : sinGapSq x y = 0 := by unfold sinGapSq; rw [hs1, hs2]; ring
      rw [hA, hB]; ring
    · have hA : cosGapSq x y = 4 := by unfold cosGapSq; rw [hx1, hy1]; ring
      have hB : sinGapSq x y = 0 := by unfold sinGapSq; rw [hs1, hs2]; ring
      rw [hA, hB]; ring

/-- In the quadrant with both coefficients negative and `b < a` (the
gradient coefficient strictly more negative), the global minimum `2 * b` is
attained exactly at the out-of-phase counter-rotating geometry (AFM-). -/
theorem gk_pair_potential_min_iff_of_both_neg' (a b x y : ℝ) (ha : a < 0)
    (hab : b < a) :
    gkPairPotential a b x y = 2 * b ↔
      sin x = 1 ∧ sin y = -1 ∧ cos x = 0 ∧ cos y = 0 ∨
      sin x = -1 ∧ sin y = 1 ∧ cos x = 0 ∧ cos y = 0 := by
  rw [gkPairPotential_eq]
  have hsplit : (a / 2) * cosGapSq x y + (b / 2) * sinGapSq x y - 2 * b
      = (b / 2) * (cosGapSq x y + sinGapSq x y - 4) + ((a - b) / 2) * cosGapSq x y := by
    ring
  have h1 : 0 ≤ (b / 2) * (cosGapSq x y + sinGapSq x y - 4) := by
    refine mul_nonneg_of_nonpos_of_nonpos (by linarith) ?_
    have hsum := cosGapSq_add_sinGapSq_le_four x y
    linarith
  have h2' : 0 < ((a - b) / 2) * cosGapSq x y ∨ ((a - b) / 2) * cosGapSq x y = 0 := by
    rcases eq_or_ne (cosGapSq x y) 0 with hzero | hne
    · exact Or.inr (by rw [hzero]; ring)
    · exact Or.inl (mul_pos (by linarith)
        (lt_of_le_of_ne (cosGapSq_nonneg x y) (Ne.symm hne)))
  constructor
  · intro h
    have hxy : (b / 2) * (cosGapSq x y + sinGapSq x y - 4)
        + ((a - b) / 2) * cosGapSq x y = 0 := by
      rw [← hsplit]
      linarith
    have hY : ((a - b) / 2) * cosGapSq x y = 0 := by
      rcases h2' with hpos | hzero
      · linarith
      · exact hzero
    have hX : (b / 2) * (cosGapSq x y + sinGapSq x y - 4) = 0 := by linarith
    have hbne : b / 2 ≠ 0 := by linarith
    have hsum4 : cosGapSq x y + sinGapSq x y = 4 := by
      have := (mul_eq_zero).1 hX
      rcases this with hz | hz
      · exact absurd hz hbne
      · linarith
    have hA0 : cosGapSq x y = 0 := by
      rcases (mul_eq_zero).1 hY with hz | hz
      · exact absurd hz (by linarith)
      · exact hz
    have hB4 : sinGapSq x y = 4 := by linarith
    exact (sinGapSq_eq_four_iff x y).1 hB4
  · rintro (⟨hx1, hy1, hc1, hc2⟩ | ⟨hx1, hy1, hc1, hc2⟩)
    · have hA : cosGapSq x y = 0 := by unfold cosGapSq; rw [hc1, hc2]; ring
      have hB : sinGapSq x y = 4 := by unfold sinGapSq; rw [hx1, hy1]; ring
      rw [hA, hB]; ring
    · have hA : cosGapSq x y = 0 := by unfold cosGapSq; rw [hc1, hc2]; ring
      have hB : sinGapSq x y = 4 := by unfold sinGapSq; rw [hx1, hy1]; ring
      rw [hA, hB]; ring

/-- In-phase orbits realize the pair potential value zero for every
coefficient pair. -/
theorem gk_pair_potential_in_phase (a b φ : ℝ) : gkPairPotential a b φ φ = 0 := by
  rw [gkPairPotential_eq]
  unfold cosGapSq sinGapSq
  ring

/-- Two horizontally antiphased orbits (phases `0` and `π`) realize the
pair potential value `2 * a`, the FM- minimum of the negative-curvature
quadrant. -/
theorem gk_pair_potential_anti_phase (a b : ℝ) :
    gkPairPotential a b 0 Real.pi = 2 * a := by
  rw [gkPairPotential_eq]
  unfold cosGapSq sinGapSq
  rw [Real.cos_zero, Real.cos_pi, Real.sin_zero, Real.sin_pi]
  ring

/-- Two vertically opposed orbits (phases `π/2` and `-π/2`) realize the pair
potential value `2 * b`, the AFM+ minimum of the mixed-sign quadrant. -/
theorem gk_pair_potential_vertical_opposition (a b : ℝ) :
    gkPairPotential a b (Real.pi / 2) (-(Real.pi / 2)) = 2 * b := by
  rw [gkPairPotential_eq]
  unfold cosGapSq sinGapSq
  rw [Real.sin_neg, Real.cos_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

/-- At a phase pair with `sin x = 1`, `cos x = 0` and `cos y = 1`, the
coupling force equals `-a`, independently of `b`. -/
theorem gk_pair_force_eq_neg_of_sin_eq_one (a b x y : ℝ)
    (hx₁ : sin x = 1) (hx₂ : cos x = 0) (hy : cos y = 1) :
    gkPairForce a b x y = -a := by
  unfold gkPairForce
  rw [hx₁, hx₂, hy]
  ring

/-- At a phase pair with `sin x = 0`, `cos x = 1` and `sin y = 1`, the
coupling force equals `b`, independently of `a`. -/
theorem gk_pair_force_eq_of_sin_eq_zero (a b x y : ℝ)
    (hx₁ : sin x = 0) (hx₂ : cos x = 1) (hy : sin y = 1) :
    gkPairForce a b x y = b := by
  unfold gkPairForce
  rw [hx₁, hx₂, hy]
  ring

/-- Explicit evaluation at the phase pair `(π / 2, 0)`: the coupling force
is `-a`. -/
theorem gk_pair_force_pi_half_zero (a b : ℝ) :
    gkPairForce a b (Real.pi / 2) 0 = -a :=
  gk_pair_force_eq_neg_of_sin_eq_one a b _ _ Real.sin_pi_div_two Real.cos_pi_div_two
    Real.cos_zero

/-- Explicit evaluation at the phase pair `(0, π / 2)`: the coupling force
is `b`. -/
theorem gk_pair_force_zero_pi_half (a b : ℝ) :
    gkPairForce a b 0 (Real.pi / 2) = b :=
  gk_pair_force_eq_of_sin_eq_zero a b _ _ Real.sin_zero Real.cos_zero
    Real.sin_pi_div_two

/-- Nondegenerate sign regression for the curvature coefficient: with
`0 < a`, the force on the first phase at `(π / 2, 0)` is strictly negative,
for every value of `b`. -/
theorem gk_pair_force_pi_half_zero_neg (a b : ℝ) (ha : 0 < a) :
    gkPairForce a b (Real.pi / 2) 0 < 0 := by
  rw [gk_pair_force_pi_half_zero, neg_lt_zero]
  exact ha

/-- Nondegenerate sign regression for the gradient coefficient: with
`0 < b`, the force on the first phase at `(0, π / 2)` is strictly positive,
for every value of `a`. -/
theorem gk_pair_force_zero_pi_half_pos (a b : ℝ) (hb : 0 < b) :
    0 < gkPairForce a b 0 (Real.pi / 2) := by
  rw [gk_pair_force_zero_pi_half]
  exact hb

/-- The sign of the coupling force is not determined by the sign of the
curvature coefficient alone: with both coefficients positive, the force at
`(0, π / 2)` is positive. -/
theorem gk_pair_force_sign_not_of_curvature_alone :
    ¬ ∀ a b x y : ℝ, 0 < a → gkPairForce a b x y < 0 := by
  intro h
  have h1 : gkPairForce 1 1 0 (Real.pi / 2) = 1 := gk_pair_force_zero_pi_half 1 1
  have h2 := h 1 1 0 (Real.pi / 2) (by norm_num)
  rw [h1] at h2
  exact absurd h2 (by norm_num)

end Qatlib.Papers.HydroSpinLatt21.GKModel

end
