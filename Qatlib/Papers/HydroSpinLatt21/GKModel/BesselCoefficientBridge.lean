/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.GKModel.SignedPairPotential
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Normed.Group.Basic

@[expose] public section

/-!
# Physical coefficient bridge from the Bessel wave force to the GK potential

[Saenz2021HydroSpinLattices], Methods equations (17)-(26), reduces the
wave-mediated pair force of the Bessel model to the generalized Kuramoto pair
potential. The wave field of each droplet is modelled by a zeroth-order
Bessel function `J₀(k_F |x - x_j|)`, and the coupling force of equation (17)
is the negative gradient of that field, with azimuthal component obtained
from the profile `g = J₀'` evaluated at the scaled inter-droplet distance;
the identity `J₁ = -J₀'` is exactly what connects the `J₁`-kernel force of
equations (14)-(16) to the `J₀'`-profile force of equation (17). See
[the article](https://doi.org/10.1038/s41586-021-03682-1).

This file proves the analytic content of that reduction for an abstract
profile `g` (the physical instance being `g = J₀'`, whose derivative enters
the curvature coefficient, so the derivative orders of equations (25), (26)
are respected):

* exact planar geometry of two neighbouring circular orbits (positions,
  azimuthal directions, distance decomposition);
* exact azimuthal projections `θ̂_i · (x_i - x_j)` of the pair separation,
  reproducing the bracket of equation (18);
* a Taylor remainder bound for a profile whose derivative is Lipschitz at
  the base point, giving equation (21) with controlled remainder;
* the coefficient bridge theorem: the azimuthal wave force equals the
  generalized Kuramoto force `gkPairForce` with the signed coefficients
  `α = ℱ k_F r g'(k_F L)` and `β = (ℱ r / L) g(k_F L)` of equations (25),
  (26), plus the explicit non-gradient single-spin term `-ℱ g(k_F L) sin φ_i`
  and an explicit remainder controlled by the profile Lipschitz constant, the
  squared orbit-to-lattice ratio and the squared scaled radius `(k_F r)^2`;
* an exact non-gradient witness: unless `ℱ g(k_F L) = 0`, the pair force
  cannot be the gradient of any exchange-symmetric pair potential, so the
  gradient structure of equation (23) is genuinely localized to the
  leading-order expansion and not a property of the full Bessel force.

Numerical simulations, experimental phase diagrams and the factor-two
amplitude mismatch discussed in the paper's Supplementary Figure 3 remain
outside the scope of this file.

A note on the printed form of equation (22): expanding the exact azimuthal
force of equation (17) using the linearization (21) produces the middle term
`(cos φ_i − cos φ_j) sin φ_i` scaled by `ℱ k_F r J₀″(k_F L)`, which is
precisely the `α`-part of the negative phase gradient of the potential (24)
with the coefficients (25), (26). The middle term of (22) as printed carries
the reversed difference order `(cos φ_{i+1} − cos φ_i) sin φ_i`, which is
algebraically inconsistent with equations (18) and (21) as printed and with
the potential (24). The theorems below follow the exact force of (17) and
the potential (24), and therefore match (18), (21) and (23)-(26).
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HydroSpinLatt21.GKModel

open Real

/-! ## Planar orbit geometry -/

/-- Cartesian coordinates of a droplet orbiting its own well centre with
orbital radius `r` and phase `φ`. -/
def orbitCoord (r φ : ℝ) : ℝ × ℝ := (r * cos φ, r * sin φ)

/-- The azimuthal unit direction of an orbit at phase `φ`. -/
def orbitAzimuth (φ : ℝ) : ℝ × ℝ := (-sin φ, cos φ)

/-- Position of the left droplet of a neighbouring pair, its well centre
taken as the origin. -/
def leftOrbitPos (r φ : ℝ) : ℝ × ℝ := orbitCoord r φ

/-- Position of the right droplet of a neighbouring pair, whose well centre
sits at `(L, 0)`. -/
def rightOrbitPos (r L φ : ℝ) : ℝ × ℝ := (L, 0) + orbitCoord r φ

/-- The squared Euclidean distance between the two droplets of a
neighbouring pair. -/
def pairSepSq (r L φi φj : ℝ) : ℝ :=
  ((leftOrbitPos r φi).1 - (rightOrbitPos r L φj).1) ^ 2
    + ((leftOrbitPos r φi).2 - (rightOrbitPos r L φj).2) ^ 2

/-- The Euclidean distance between the two droplets of a neighbouring
pair. -/
def pairDist (r L φi φj : ℝ) : ℝ := Real.sqrt (pairSepSq r L φi φj)

/-- The squared Cartesian separation of the droplets is nonnegative. -/
theorem pairSepSq_nonneg (r L φi φj : ℝ) : 0 ≤ pairSepSq r L φi φj := by
  unfold pairSepSq
  nlinarith [sq_nonneg ((leftOrbitPos r φi).1 - (rightOrbitPos r L φj).1),
    sq_nonneg ((leftOrbitPos r φi).2 - (rightOrbitPos r L φj).2)]

/-- The droplet in the left well follows a circle centered at the origin. -/
theorem leftOrbitPos_eq (r φ : ℝ) : leftOrbitPos r φ = (r * cos φ, r * sin φ) := rfl

/-- The droplet in the right well follows a circle centered at horizontal offset `L`. -/
theorem rightOrbitPos_eq (r L φ : ℝ) :
    rightOrbitPos r L φ = (L + r * cos φ, r * sin φ) := by
  simp [rightOrbitPos, orbitCoord]

/-- The Euclidean separation of the droplets is nonnegative. -/
theorem pairDist_nonneg (r L φi φj : ℝ) : 0 ≤ pairDist r L φi φj := by
  unfold pairDist
  exact Real.sqrt_nonneg _

/-- The squared pair distance decomposes into the longitudinal and
transverse orbit offsets, the exact form behind the approximation
`|x_i - x_j| ≈ L + r (cos φ_j - cos φ_i)` of equation (18). -/
theorem pairSepSq_eq (r L φi φj : ℝ) :
    pairSepSq r L φi φj
      = (L + r * (cos φj - cos φi)) ^ 2 + (r * (sin φi - sin φj)) ^ 2 := by
  unfold pairSepSq
  simp only [leftOrbitPos_eq, rightOrbitPos_eq]
  ring

/-- The squared pair distance of the pair distance itself has the same
decomposition. -/
theorem pairDist_sq_eq (r L φi φj : ℝ) :
    (pairDist r L φi φj) ^ 2
      = (L + r * (cos φj - cos φi)) ^ 2 + (r * (sin φi - sin φj)) ^ 2 := by
  rw [pairDist, Real.sq_sqrt (pairSepSq_nonneg r L φi φj), pairSepSq_eq]

/-- The azimuthal projection of the separation vector of the pair is the
bracket of equation (18) before the small-orbit expansion. -/
theorem azimuth_sep_projection_left (r L φi φj : ℝ) :
    (orbitAzimuth φi).1 * ((leftOrbitPos r φi).1 - (rightOrbitPos r L φj).1)
      + (orbitAzimuth φi).2 * ((leftOrbitPos r φi).2 - (rightOrbitPos r L φj).2)
        = L * sin φi + r * sin (φi - φj) := by
  unfold orbitAzimuth
  simp only [leftOrbitPos_eq, rightOrbitPos_eq]
  rw [sin_sub]
  ring

/-- The azimuthal projection seen by the right droplet is the transposed
bracket with the opposite sign. -/
theorem azimuth_sep_projection_right (r L φi φj : ℝ) :
    (orbitAzimuth φj).1 * ((rightOrbitPos r L φj).1 - (leftOrbitPos r φi).1)
      + (orbitAzimuth φj).2 * ((rightOrbitPos r L φj).2 - (leftOrbitPos r φi).2)
        = -(L * sin φj + r * sin (φi - φj)) := by
  unfold orbitAzimuth
  simp only [leftOrbitPos_eq, rightOrbitPos_eq]
  rw [sin_sub]
  ring

/-- The pair potential in the coordinate form of equation (24): with the
drop positions measured relative to the respective well centres, the two
forms of the potential agree. -/
theorem gk_pair_potential_eq_coord_form (a b r φi φj : ℝ) (hr : r ≠ 0) :
    gkPairPotential a b φi φj
      = a / (2 * r ^ 2) * ((orbitCoord r φi).1 - (orbitCoord r φj).1) ^ 2
        + b / (2 * r ^ 2) * ((orbitCoord r φi).2 - (orbitCoord r φj).2) ^ 2 := by
  unfold gkPairPotential orbitCoord
  field_simp

/-! ## Distance bounds in the small-orbit regime -/

/-- In the regime `r ≤ L/4` the inter-droplet distance stays above `L/2`,
so the pair separation never degenerates. -/
theorem pairDist_ge_half (r L φi φj : ℝ) (_hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L / 4) :
    L / 2 ≤ pairDist r L φi φj := by
  have hcos : -2 ≤ cos φj - cos φi := by
    linarith [neg_one_le_cos φj, cos_le_one φj, neg_one_le_cos φi, cos_le_one φi]
  have hmul : -2 * r ≤ r * (cos φj - cos φi) := by nlinarith [hr.le, hcos]
  have hbase : L / 2 ≤ L + r * (cos φj - cos φi) := by linarith
  have hbase' : 0 ≤ L + r * (cos φj - cos φi) := by linarith
  have h5 : (L / 2) ^ 2 ≤ (pairDist r L φi φj) ^ 2 := by
    rw [pairDist_sq_eq]
    have hsq : (L / 2) ^ 2 ≤ (L + r * (cos φj - cos φi)) ^ 2 :=
      sq_le_sq' (by linarith) hbase
    nlinarith [sq_nonneg (r * (sin φi - sin φj))]
  have h6 : Real.sqrt ((L / 2) ^ 2) ≤ Real.sqrt ((pairDist r L φi φj) ^ 2) :=
    Real.sqrt_le_sqrt h5
  rw [Real.sqrt_sq (pairDist_nonneg r L φi φj)] at h6
  rwa [Real.sqrt_sq (show (0:ℝ) ≤ L / 2 by linarith)] at h6

/-- The deviation of the pair distance from its longitudinal approximation
is second order in the orbital radius. -/
theorem pairDist_sub_longitudinal_le (r L φi φj : ℝ) (hL : 0 < L) (hr : 0 < r)
    (hrL : r ≤ L / 4) :
    |pairDist r L φi φj - (L + r * (cos φj - cos φi))| ≤ 4 * r ^ 2 / L := by
  have hcos : -2 ≤ cos φj - cos φi := by
    linarith [neg_one_le_cos φj, cos_le_one φj, neg_one_le_cos φi, cos_le_one φi]
  have hmul : -2 * r ≤ r * (cos φj - cos φi) := by nlinarith [hr.le, hcos]
  have hbase : L / 2 ≤ L + r * (cos φj - cos φi) := by linarith
  have hbase' : 0 ≤ L + r * (cos φj - cos φi) := by linarith
  have hsin : -2 ≤ sin φi - sin φj := by
    linarith [neg_one_le_sin φi, sin_le_one φj, neg_one_le_sin φj, sin_le_one φi]
  have hsin2 : sin φi - sin φj ≤ 2 := by
    linarith [sin_le_one φi, neg_one_le_sin φj, neg_one_le_sin φi, sin_le_one φj]
  have hlow : -(2 * r) ≤ r * (sin φi - sin φj) := by nlinarith [hr.le, hsin]
  have hhigh : r * (sin φi - sin φj) ≤ 2 * r := by nlinarith [hr.le, hsin2]
  have hE2 : (r * (sin φi - sin φj)) ^ 2 ≤ (2 * r) ^ 2 := sq_le_sq' hlow hhigh
  have hd0pos : (0:ℝ) < L + r * (cos φj - cos φi) := by linarith
  have hdpos : (0:ℝ) < pairDist r L φi φj :=
    lt_of_lt_of_le (by linarith) (pairDist_ge_half r L φi φj hL hr hrL)
  have hkey : (pairDist r L φi φj) ^ 2 - (L + r * (cos φj - cos φi)) ^ 2
      = (r * (sin φi - sin φj)) ^ 2 := by
    rw [pairDist_sq_eq]
    ring
  have hsplit : pairDist r L φi φj - (L + r * (cos φj - cos φi))
      = (r * (sin φi - sin φj)) ^ 2
        / (pairDist r L φi φj + (L + r * (cos φj - cos φi))) := by
    apply eq_div_of_mul_eq (by linarith)
    linear_combination hkey
  have hdd0 : L + r * (cos φj - cos φi) ≤ pairDist r L φi φj := by
    have h1 : Real.sqrt ((L + r * (cos φj - cos φi)) ^ 2) ≤ Real.sqrt (pairSepSq r L φi φj) := by
      rw [pairSepSq_eq]
      exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
    rw [Real.sqrt_sq hbase'] at h1
    exact h1
  rw [abs_of_nonneg (by linarith [hdd0]), hsplit]
  rw [div_le_div_iff₀ (by linarith) hL]
  have hsum : L ≤ pairDist r L φi φj + (L + r * (cos φj - cos φi)) := by
    have := pairDist_ge_half r L φi φj hL hr hrL
    linarith
  have hE2' : (r * (sin φi - sin φj)) ^ 2 ≤ (2 * r) ^ 2 := hE2
  nlinarith [hsum, hE2', sq_nonneg (pairDist r L φi φj),
    sq_nonneg (L + r * (cos φj - cos φi)), mul_nonneg hL.le hL.le]

/-- The pair distance deviates from the lattice spacing by at most three
orbital radii. -/
theorem pairDist_sub_L_le (r L φi φj : ℝ) (hL : 0 < L) (hr : 0 < r)
    (hrL : r ≤ L / 4) :
    |pairDist r L φi φj - L| ≤ 3 * r := by
  have h1 := pairDist_sub_longitudinal_le r L φi φj hL hr hrL
  have hcos : -2 ≤ cos φj - cos φi := by
    linarith [neg_one_le_cos φj, cos_le_one φj, neg_one_le_cos φi, cos_le_one φi]
  have hcos2 : cos φj - cos φi ≤ 2 := by
    linarith [neg_one_le_cos φj, cos_le_one φj, neg_one_le_cos φi, cos_le_one φi]
  have hlow : -(2 * r) ≤ r * (cos φj - cos φi) := by nlinarith [hr.le, hcos]
  have hhigh : r * (cos φj - cos φi) ≤ 2 * r := by nlinarith [hr.le, hcos2]
  have hmul : |r * (cos φj - cos φi)| ≤ 2 * r := abs_le.2 ⟨hlow, hhigh⟩
  have h2 : |L + r * (cos φj - cos φi) - L| ≤ 2 * r := by
    have heq : L + r * (cos φj - cos φi) - L = r * (cos φj - cos φi) := by ring
    rw [heq]
    exact hmul
  have h3 : 4 * r ^ 2 / L ≤ r := by
    rw [div_le_iff₀ hL]
    nlinarith [hrL, sq_nonneg r, hL.le]
  have h4 : |pairDist r L φi φj - L|
      ≤ |pairDist r L φi φj - (L + r * (cos φj - cos φi))|
        + |L + r * (cos φj - cos φi) - L| := by
    have heq : (pairDist r L φi φj - L)
        = (pairDist r L φi φj - (L + r * (cos φj - cos φi)))
          + (L + r * (cos φj - cos φi) - L) := by ring
    rw [heq]
    simp only [← Real.norm_eq_abs]
    exact norm_add_le _ _
  have h5 : |pairDist r L φi φj - L| ≤ 4 * r ^ 2 / L + 2 * r :=
    h4.trans (add_le_add h1 h2)
  have h6 : 4 * r ^ 2 / L + 2 * r ≤ 3 * r := by linarith
  exact h5.trans h6

/-! ## The azimuthal wave force and its gradient structure -/

/-- The azimuthal wave force on the left droplet of the pair, equation (17)
projected onto its azimuthal direction, with wave profile `g` (the paper's
`J₀'`) evaluated at the scaled pair distance. -/
def leftAzimuthForce (F : ℝ) (g : ℝ → ℝ) (k r L φi φj : ℝ) : ℝ :=
  -(F * g (k * pairDist r L φi φj) / pairDist r L φi φj)
    * (L * sin φi + r * sin (φi - φj))

/-- The azimuthal wave force on the right droplet of the pair. -/
def rightAzimuthForce (F : ℝ) (g : ℝ → ℝ) (k r L φi φj : ℝ) : ℝ :=
  (F * g (k * pairDist r L φi φj) / pairDist r L φi φj)
    * (L * sin φj + r * sin (φi - φj))

/-- A pair of phase force fields is generated by an exchange-symmetric pair
potential if the potential is differentiable in each argument and the forces
are its negative partial derivatives. -/
def IsSymmetricPairGradient (U f₁ f₂ : ℝ → ℝ → ℝ) : Prop :=
  (∀ x y, U x y = U y x) ∧
    (∀ x y, HasDerivAt (fun t => U t y) (-(f₁ x y)) x ∧
      HasDerivAt (fun t => U x t) (-(f₂ x y)) y)

/-- Forces generated by an exchange-symmetric pair potential satisfy the
exchange law `f₁ x y = f₂ y x`. -/
theorem symmetric_pair_gradient_exchange (U f₁ f₂ : ℝ → ℝ → ℝ)
    (h : IsSymmetricPairGradient U f₁ f₂) : ∀ x y, f₁ x y = f₂ y x := by
  obtain ⟨hsym, hderiv⟩ := h
  intro x y
  have hfun : (fun t => U t y) = (fun t => U y t) := funext fun t => hsym t y
  have d1 := (hderiv x y).1
  have d2 := (hderiv y x).2
  rw [hfun] at d1
  have := HasDerivAt.unique d1 d2
  exact neg_injective this

/-- At the phase pair `(π/2, π/2)` both droplets sit at the top of their
wells, the pair distance equals the lattice spacing, and the azimuthal
forces take the values `∓ℱ g(k_F L)`. -/
theorem azimuth_force_at_top (F : ℝ) (g : ℝ → ℝ) (k r L : ℝ) (hL : 0 < L) :
    leftAzimuthForce F g k r L (Real.pi / 2) (Real.pi / 2) = -F * g (k * L)
      ∧ rightAzimuthForce F g k r L (Real.pi / 2) (Real.pi / 2) = F * g (k * L) := by
  have hd : pairDist r L (Real.pi / 2) (Real.pi / 2) = L := by
    rw [pairDist, pairSepSq]
    simp only [leftOrbitPos_eq, rightOrbitPos_eq]
    rw [cos_pi_div_two, sin_pi_div_two]
    have hval : (r * 0 - (L + r * 0)) ^ 2 + (r * 1 - r * 1) ^ 2 = L ^ 2 := by ring
    rw [hval, Real.sqrt_sq hL.le]
  constructor
  · unfold leftAzimuthForce
    rw [hd, sin_sub, sin_pi_div_two, cos_pi_div_two]
    field_simp
    ring
  · unfold rightAzimuthForce
    rw [hd, sin_sub, sin_pi_div_two, cos_pi_div_two]
    field_simp
    ring

/-- Unless `ℱ g(k_F L) = 0`, the exact azimuthal wave force cannot be the
gradient of any exchange-symmetric pair potential: the gradient structure of
equation (23) is a property of the leading-order expansion only. This is the
explicit non-gradient hypothesis separating the Bessel model from the
generalized Kuramoto potential. -/
theorem wave_force_not_symmetric_pair_gradient (F : ℝ) (g : ℝ → ℝ) (k r L : ℝ) (hL : 0 < L)
    (hF : F * g (k * L) ≠ 0) :
    ¬ ∃ U : ℝ → ℝ → ℝ,
      IsSymmetricPairGradient U
        (fun φi φj => leftAzimuthForce F g k r L φi φj)
        (fun φi φj => rightAzimuthForce F g k r L φi φj) := by
  rintro ⟨U, hU⟩
  have hexch := symmetric_pair_gradient_exchange U _ _ hU (Real.pi / 2) (Real.pi / 2)
  obtain ⟨hleft, hright⟩ := azimuth_force_at_top F g k r L hL
  rw [hleft, hright] at hexch
  have hz : F * g (k * L) = 0 := by linarith [hexch]
  exact hF hz
/-! ## Taylor remainder and absolute value helpers -/

/-- If the derivative of a profile is Lipschitz at the base point `a`, the
first-order Taylor step of equation (21) holds with remainder controlled by
the Lipschitz constant and the squared increment. -/
theorem taylor_bound_of_lipschitz_deriv {f f' : ℝ → ℝ} {a x M : ℝ} (hM : 0 ≤ M)
    (hd : ∀ y, HasDerivAt f (f' y) y)
    (hlip : ∀ z, |z - a| ≤ |x - a| → |f' z - f' a| ≤ M * |z - a|) :
    |f x - f a - f' a * (x - a)| ≤ M * (x - a) ^ 2 := by
  rcases eq_or_ne x a with rfl | hxa
  · simp
  have hcont : ∀ u v : ℝ, ContinuousOn f (Set.Icc u v) := fun u v y _ =>
    (hd y).continuousAt.continuousWithinAt
  have hderiv : ∀ u v : ℝ, ∀ z ∈ Set.Ioo u v, HasDerivAt f (f' z) z := fun u v z _ => hd z
  have finalstep : ∀ c : ℝ, |c - a| ≤ |x - a| → |f' c - f' a| * |x - a| ≤ M * (x - a) ^ 2 := by
    intro c hcap
    have h2 := hlip c hcap
    have step1 : M * |c - a| * |x - a| ≤ M * |x - a| * |x - a| := by
      calc M * |c - a| * |x - a| = M * (|c - a| * |x - a|) := by ring
        _ ≤ M * (|x - a| * |x - a|) := mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hcap (abs_nonneg _)) hM
        _ = M * |x - a| * |x - a| := by ring
    have step2 : M * |x - a| * |x - a| = M * (x - a) ^ 2 := by
      rw [← sq_abs (x - a)]
      ring
    exact (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)).trans (step1.trans (le_of_eq step2))
  rcases lt_or_gt_of_ne hxa with hxa' | hxa'
  · obtain ⟨c, hcmem, hfc⟩ := exists_hasDerivAt_eq_slope f f' hxa' (hcont x a) (hderiv x a)
    obtain ⟨hc1, hc2⟩ := hcmem
    have hne : a - x ≠ 0 := by
      intro h
      linarith
    have hkey : f x - f a = f' c * (x - a) := by
      rw [hfc]
      field_simp [hne]
      ring
    have hrewrite : f x - f a - f' a * (x - a) = (f' c - f' a) * (x - a) := by
      linear_combination hkey
    have hcap : |c - a| ≤ |x - a| := by
      rw [abs_of_neg (by linarith : c - a < 0), abs_of_neg (by linarith : x - a < 0)]
      linarith
    rw [hrewrite, abs_mul]
    exact finalstep c hcap
  · obtain ⟨c, hcmem, hfc⟩ := exists_hasDerivAt_eq_slope f f' hxa' (hcont a x) (hderiv a x)
    obtain ⟨hc1, hc2⟩ := hcmem
    have hne2 : x - a ≠ 0 := by
      intro h
      apply hxa
      linarith
    have hkey : f x - f a = f' c * (x - a) := by
      rw [hfc]
      field_simp [hne2]
    have hrewrite : f x - f a - f' a * (x - a) = (f' c - f' a) * (x - a) := by
      linear_combination hkey
    have hcap : |c - a| ≤ |x - a| := by
      rw [abs_of_nonneg (by linarith : 0 ≤ c - a), abs_of_nonneg (by linarith : 0 ≤ x - a)]
      linarith
    rw [hrewrite, abs_mul]
    exact finalstep c hcap

/-- Absolute values on the reals multiply: a convenient restatement of the
norm multiplicativity for assembling remainder bounds. -/
theorem abs_mul_real (a b : ℝ) : |a * b| = |a| * |b| := by
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs, ← Real.norm_eq_abs, norm_mul]

/-- Two-term triangle inequality for real absolute values. -/
theorem abs_le_abs_add_abs (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  have h : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h

/-! ## The coefficient bridge with controlled remainder -/

set_option maxHeartbeats 1600000 in
/-- The azimuthal wave force of equation (17) agrees, up to an explicit
controlled remainder, with the generalized Kuramoto force of equation (23)
built from the pair potential of equation (24) with the signed coefficients
`α = ℱ k_F r g'(k_F L)` and `β = (ℱ r / L) g(k_F L)` of equations (25), (26),
where `g` is the wave profile derivative (the paper's `J₀'`, so that `α`
carries the second Bessel derivative order and `β` the first). The
difference consists of the explicit non-gradient single-spin term
`-ℱ g(k_F L) sin φ_i` plus a remainder bounded in terms of the profile
Lipschitz constant `M2`, the orbit-to-lattice ratio `r/L ≤ 1/4` and the
scaled radius `k_F r`; this is the quantitative form of the paper's
expansion steps in equations (18) to (22). Each remainder term records its
source: the leading-order projection mismatch, the transverse orbit
correction, the second-order longitudinal distance error, the Taylor error
of the profile at the lattice-scaled base point, and the reciprocal
distance error. -/
theorem left_azimuth_force_approx_gk_force (F : ℝ) (g gp : ℝ → ℝ)
    (k r L φi φj M2 : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L / 4) (hk : 0 < k) (hM : 0 ≤ M2)
    (hd : ∀ y, HasDerivAt g (gp y) y)
    (hlip : ∀ z, |z - k * L| ≤ 4 * k * r → |gp z - gp (k * L)| ≤ M2 * |z - k * L|) :
    |leftAzimuthForce F g k r L φi φj
        - (gkPairForce (F * k * r * gp (k * L)) (F * r / L * g (k * L)) φi φj
          - F * g (k * L) * Real.sin φi)|
      ≤ |F| * (2 * |g (k * L)| * r / L
        + 2 * |gp (k * L)| * k * r ^ 2 / L
        + 4 * |gp (k * L)| * k * r ^ 2 / L * (1 + r / L)
        + 9 * M2 * (k * r) ^ 2 * (1 + r / L)
        + 6 * r / L * (1 + r / L) * (|g (k * L)| + 3 * |gp (k * L)| * k * r
            + 9 * M2 * (k * r) ^ 2)) := by
  have hL2 : 0 < L / 2 := by linarith
  have hdge : L / 2 ≤ pairDist r L φi φj := pairDist_ge_half r L φi φj hL hr hrL
  have hdpos : 0 < pairDist r L φi φj := lt_of_lt_of_le hL2 hdge
  have habsdL : |pairDist r L φi φj - L| ≤ 3 * r :=
    pairDist_sub_L_le r L φi φj hL hr hrL
  have habsdd0 : |pairDist r L φi φj
      - (L + r * (Real.cos φj - Real.cos φi))| ≤ 4 * r ^ 2 / L :=
    pairDist_sub_longitudinal_le r L φi φj hL hr hrL
  have hs1 : |Real.sin φi| ≤ 1 := abs_le.2 ⟨Real.neg_one_le_sin φi, Real.sin_le_one φi⟩
  have hsig : |Real.sin (φi - φj)| ≤ 1 :=
    abs_le.2 ⟨Real.neg_one_le_sin (φi - φj), Real.sin_le_one (φi - φj)⟩
  have hcd : |Real.cos φi - Real.cos φj| ≤ 2 := by
    refine abs_le.2 ⟨?_, ?_⟩
    · linarith [Real.neg_one_le_cos φi, Real.cos_le_one φj]
    · linarith [Real.cos_le_one φi, Real.neg_one_le_cos φj]
  have hkle : |k * pairDist r L φi φj - k * L| ≤ 3 * k * r := by
    have hstep : k * (3 * r) = 3 * k * r := by ring
    have hraw : k * |pairDist r L φi φj - L| ≤ k * (3 * r) :=
      mul_le_mul_of_nonneg_left habsdL hk.le
    have hconv : k * pairDist r L φi φj - k * L = k * (pairDist r L φi φj - L) := by ring
    rw [hconv, abs_mul, abs_of_pos hk]
    exact hraw.trans_eq hstep
  have hlip' : ∀ z, |z - k * L| ≤ |k * pairDist r L φi φj - k * L| →
      |gp z - gp (k * L)| ≤ M2 * |z - k * L| := by
    intro z hz
    refine hlip z ?_
    refine (hz.trans hkle).trans ?_
    nlinarith [hk.le, hr.le]
  have hT := taylor_bound_of_lipschitz_deriv (f := g) (f' := gp) (a := k * L)
    (x := k * pairDist r L φi φj) hM hd hlip'
  have hεT : |g (k * pairDist r L φi φj) - g (k * L)
      - gp (k * L) * (k * pairDist r L φi φj - k * L)| ≤ 9 * M2 * (k * r) ^ 2 := by
    refine hT.trans ?_
    have habs3 : |k * pairDist r L φi φj - k * L| ≤ |3 * k * r| := by
      rw [abs_of_nonneg (show (0:ℝ) ≤ 3 * k * r by positivity)]
      exact hkle
    have hsq : (k * pairDist r L φi φj - k * L) ^ 2 ≤ (3 * k * r) ^ 2 :=
      sq_le_sq.mpr habs3
    have hmono : M2 * (k * pairDist r L φi φj - k * L) ^ 2 ≤ M2 * (3 * k * r) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hM
    exact hmono.trans_eq (by ring)
  have hδ : |1 / pairDist r L φi φj - 1 / L| ≤ 6 * r / L ^ 2 := by
    have hkey' : 1 / pairDist r L φi φj - 1 / L
        = (L - pairDist r L φi φj) / (pairDist r L φi φj * L) := by
      field_simp
    have hnum : |L - pairDist r L φi φj| ≤ 3 * r := by
      rw [abs_sub_comm]
      exact habsdL
    have hposDL : (0:ℝ) < pairDist r L φi φj * L := by positivity
    have hposL2 : (0:ℝ) < L ^ 2 := by positivity
    have hm : (0:ℝ) ≤ (pairDist r L φi φj - L / 2) * (L * r) :=
      mul_nonneg (sub_nonneg.2 hdge) (mul_nonneg hL.le hr.le)
    rw [hkey', abs_div, abs_of_pos hposDL, div_le_div_iff₀ hposDL hposL2]
    nlinarith [hnum, hm, sq_nonneg L]
  have key : leftAzimuthForce F g k r L φi φj
      - (gkPairForce (F * k * r * gp (k * L)) (F * r / L * g (k * L)) φi φj
          - F * g (k * L) * Real.sin φi)
      = (F * r / L) * g (k * L) * Real.sin φi * (Real.cos φi - Real.cos φj)
      + F * k * r * gp (k * L) * (Real.cos φi - Real.cos φj) * (r / L)
        * Real.sin (φi - φj)
      + (-(F * gp (k * L) * k * (pairDist r L φi φj
          - (L + r * (Real.cos φj - Real.cos φi)))
        * (L * Real.sin φi + r * Real.sin (φi - φj)) / L))
      + (-(F * (g (k * pairDist r L φi φj) - g (k * L)
          - gp (k * L) * (k * pairDist r L φi φj - k * L))
        * (L * Real.sin φi + r * Real.sin (φi - φj)) / L))
      + (-(F * (g (k * L) + gp (k * L) * (k * pairDist r L φi φj - k * L)
          + (g (k * pairDist r L φi φj) - g (k * L)
            - gp (k * L) * (k * pairDist r L φi φj - k * L)))
        * (L * Real.sin φi + r * Real.sin (φi - φj))
        * (1 / pairDist r L φi φj - 1 / L))) := by
    unfold leftAzimuthForce gkPairForce
    rw [Real.sin_sub]
    field_simp
    ring
  have hPbound : |L * Real.sin φi + r * Real.sin (φi - φj)| ≤ L + r := by
    have h1 := abs_le_abs_add_abs (L * Real.sin φi) (r * Real.sin (φi - φj))
    have h2 : |L * Real.sin φi| ≤ L := by
      rw [abs_mul_real, abs_of_pos hL]
      nlinarith [hs1, hL.le]
    have h3 : |r * Real.sin (φi - φj)| ≤ r := by
      rw [abs_mul_real, abs_of_nonneg hr.le]
      nlinarith [hsig, hr.le]
    linarith
  have hFnn : (0:ℝ) ≤ |F| := abs_nonneg F
  have hg0nn : (0:ℝ) ≤ |g (k * L)| := abs_nonneg _
  have hgp0nn : (0:ℝ) ≤ |gp (k * L)| := abs_nonneg _
  have hrLnn : (0:ℝ) ≤ r / L := div_nonneg hr.le hL.le
  have bx1 : |(F * r / L) * g (k * L) * Real.sin φi * (Real.cos φi - Real.cos φj)|
      ≤ |F| * (r / L) * |g (k * L)| * (1 * 2) := by
    have hsplit : |(F * r / L) * g (k * L) * Real.sin φi * (Real.cos φi - Real.cos φj)|
        = |F| * (r / L) * |g (k * L)|
          * (|Real.sin φi| * |Real.cos φi - Real.cos φj|) := by
      simp only [abs_mul_real, abs_div, abs_of_pos hL, abs_of_nonneg hr.le]
      field_simp
    have hA : (0:ℝ) ≤ |F| * (r / L) * |g (k * L)| := by positivity
    have hfac : |Real.sin φi| * |Real.cos φi - Real.cos φj| ≤ 1 * 2 :=
      mul_le_mul hs1 hcd (abs_nonneg _) zero_le_one
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hfac hA
  have bx2 : |F * k * r * gp (k * L) * (Real.cos φi - Real.cos φj) * (r / L)
      * Real.sin (φi - φj)|
      ≤ |F| * k * r * |gp (k * L)| * (r / L) * (2 * 1) := by
    have hsplit : |F * k * r * gp (k * L) * (Real.cos φi - Real.cos φj) * (r / L)
        * Real.sin (φi - φj)|
        = |F| * k * r * |gp (k * L)| * (r / L)
          * (|Real.cos φi - Real.cos φj| * |Real.sin (φi - φj)|) := by
      simp only [abs_mul_real, abs_div, abs_of_pos hk, abs_of_pos hL,
        abs_of_nonneg hr.le]
      field_simp
    have hA : (0:ℝ) ≤ |F| * k * r * |gp (k * L)| * (r / L) := by positivity
    have hfac : |Real.cos φi - Real.cos φj| * |Real.sin (φi - φj)| ≤ 2 * 1 :=
      mul_le_mul hcd hsig (abs_nonneg _) zero_le_two
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hfac hA
  have bx3 : |F * gp (k * L) * k * (pairDist r L φi φj
        - (L + r * (Real.cos φj - Real.cos φi)))
        * (L * Real.sin φi + r * Real.sin (φi - φj)) / L|
      ≤ |F| * |gp (k * L)| * k / L * ((4 * r ^ 2 / L) * (L + r)) := by
    have hsplit : |F * gp (k * L) * k * (pairDist r L φi φj
        - (L + r * (Real.cos φj - Real.cos φi)))
        * (L * Real.sin φi + r * Real.sin (φi - φj)) / L|
        = |F| * |gp (k * L)| * k / L
          * (|pairDist r L φi φj - (L + r * (Real.cos φj - Real.cos φi))|
            * |L * Real.sin φi + r * Real.sin (φi - φj)|) := by
      simp only [abs_mul_real, abs_div, abs_of_pos hk, abs_of_pos hL]
      field_simp
    have hA : (0:ℝ) ≤ |F| * |gp (k * L)| * k / L := by positivity
    have hfac : |pairDist r L φi φj - (L + r * (Real.cos φj - Real.cos φi))|
          * |L * Real.sin φi + r * Real.sin (φi - φj)|
        ≤ (4 * r ^ 2 / L) * (L + r) :=
      mul_le_mul habsdd0 hPbound (abs_nonneg _)
        (div_nonneg (by positivity) hL.le)
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hfac hA
  have bx4 : |F * (g (k * pairDist r L φi φj) - g (k * L)
        - gp (k * L) * (k * pairDist r L φi φj - k * L))
        * (L * Real.sin φi + r * Real.sin (φi - φj)) / L|
      ≤ |F| / L * ((9 * M2 * (k * r) ^ 2) * (L + r)) := by
    have hsplit : |F * (g (k * pairDist r L φi φj) - g (k * L)
        - gp (k * L) * (k * pairDist r L φi φj - k * L))
        * (L * Real.sin φi + r * Real.sin (φi - φj)) / L|
        = |F| / L * (|g (k * pairDist r L φi φj) - g (k * L)
            - gp (k * L) * (k * pairDist r L φi φj - k * L)|
            * |L * Real.sin φi + r * Real.sin (φi - φj)|) := by
      simp only [abs_mul_real, abs_div, abs_of_pos hL]
      field_simp
    have hA : (0:ℝ) ≤ |F| / L := by positivity
    have hfac : |g (k * pairDist r L φi φj) - g (k * L)
          - gp (k * L) * (k * pairDist r L φi φj - k * L)|
          * |L * Real.sin φi + r * Real.sin (φi - φj)|
        ≤ (9 * M2 * (k * r) ^ 2) * (L + r) :=
      mul_le_mul hεT hPbound (abs_nonneg _) (by positivity)
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hfac hA
  have bx5 : |F * (g (k * L) + gp (k * L) * (k * pairDist r L φi φj - k * L)
        + (g (k * pairDist r L φi φj) - g (k * L)
          - gp (k * L) * (k * pairDist r L φi φj - k * L)))
        * (L * Real.sin φi + r * Real.sin (φi - φj))
        * (1 / pairDist r L φi φj - 1 / L)|
      ≤ |F| * ((|g (k * L)| + 3 * |gp (k * L)| * k * r + 9 * M2 * (k * r) ^ 2)
          * (L + r)) * (6 * r / L ^ 2) := by
    have hc1 : |g (k * L) + gp (k * L) * (k * pairDist r L φi φj - k * L)
        + (g (k * pairDist r L φi φj) - g (k * L)
          - gp (k * L) * (k * pairDist r L φi φj - k * L))|
        ≤ |g (k * L)| + 3 * |gp (k * L)| * k * r + 9 * M2 * (k * r) ^ 2 := by
      have t1 := abs_le_abs_add_abs (g (k * L)
        + gp (k * L) * (k * pairDist r L φi φj - k * L))
        (g (k * pairDist r L φi φj) - g (k * L)
          - gp (k * L) * (k * pairDist r L φi φj - k * L))
      have t2 := abs_le_abs_add_abs (g (k * L))
        (gp (k * L) * (k * pairDist r L φi φj - k * L))
      have t3 : |gp (k * L) * (k * pairDist r L φi φj - k * L)|
          = |gp (k * L)| * |k * pairDist r L φi φj - k * L| := abs_mul_real _ _
      have t4 : |gp (k * L)| * |k * pairDist r L φi φj - k * L|
          ≤ |gp (k * L)| * (3 * k * r) :=
        mul_le_mul_of_nonneg_left hkle hgp0nn
      nlinarith [t1, t2, t3, t4, hεT]
    have hC : (0:ℝ) ≤ |g (k * L)| + 3 * |gp (k * L)| * k * r
        + 9 * M2 * (k * r) ^ 2 := by positivity
    have hsplit : |F * (g (k * L) + gp (k * L) * (k * pairDist r L φi φj - k * L)
        + (g (k * pairDist r L φi φj) - g (k * L)
          - gp (k * L) * (k * pairDist r L φi φj - k * L)))
        * (L * Real.sin φi + r * Real.sin (φi - φj))
        * (1 / pairDist r L φi φj - 1 / L)|
        = |F| * (|g (k * L) + gp (k * L) * (k * pairDist r L φi φj - k * L)
            + (g (k * pairDist r L φi φj) - g (k * L)
              - gp (k * L) * (k * pairDist r L φi φj - k * L))|
            * |L * Real.sin φi + r * Real.sin (φi - φj)|)
          * |1 / pairDist r L φi φj - 1 / L| := by
      simp only [abs_mul_real]
      try ring
    have hfac1 : |g (k * L) + gp (k * L) * (k * pairDist r L φi φj - k * L)
          + (g (k * pairDist r L φi φj) - g (k * L)
            - gp (k * L) * (k * pairDist r L φi φj - k * L))|
          * |L * Real.sin φi + r * Real.sin (φi - φj)|
        ≤ (|g (k * L)| + 3 * |gp (k * L)| * k * r + 9 * M2 * (k * r) ^ 2)
          * (L + r) :=
      mul_le_mul hc1 hPbound (abs_nonneg _) hC
    have step1 : |F| * (|g (k * L) + gp (k * L) * (k * pairDist r L φi φj - k * L)
          + (g (k * pairDist r L φi φj) - g (k * L)
            - gp (k * L) * (k * pairDist r L φi φj - k * L))|
          * |L * Real.sin φi + r * Real.sin (φi - φj)|)
        ≤ |F| * ((|g (k * L)| + 3 * |gp (k * L)| * k * r + 9 * M2 * (k * r) ^ 2)
          * (L + r)) :=
      mul_le_mul_of_nonneg_left hfac1 hFnn
    have hY : (0:ℝ) ≤ |F| * ((|g (k * L)| + 3 * |gp (k * L)| * k * r
        + 9 * M2 * (k * r) ^ 2) * (L + r)) := by positivity
    have step2 := mul_le_mul_of_nonneg_right step1
      (abs_nonneg (1 / pairDist r L φi φj - 1 / L))
    have step3 := mul_le_mul_of_nonneg_left hδ hY
    rw [hsplit]
    exact step2.trans step3
  have finalform : |F| * (r / L) * |g (k * L)| * (1 * 2)
      + |F| * k * r * |gp (k * L)| * (r / L) * (2 * 1)
      + |F| * |gp (k * L)| * k / L * ((4 * r ^ 2 / L) * (L + r))
      + |F| / L * ((9 * M2 * (k * r) ^ 2) * (L + r))
      + |F| * ((|g (k * L)| + 3 * |gp (k * L)| * k * r + 9 * M2 * (k * r) ^ 2)
          * (L + r)) * (6 * r / L ^ 2)
      = |F| * (2 * |g (k * L)| * r / L
        + 2 * |gp (k * L)| * k * r ^ 2 / L
        + 4 * |gp (k * L)| * k * r ^ 2 / L * (1 + r / L)
        + 9 * M2 * (k * r) ^ 2 * (1 + r / L)
        + 6 * r / L * (1 + r / L) * (|g (k * L)| + 3 * |gp (k * L)| * k * r
            + 9 * M2 * (k * r) ^ 2)) := by
    field_simp
  have n3 : |-(F * gp (k * L) * k * (pairDist r L φi φj
      - (L + r * (Real.cos φj - Real.cos φi)))
      * (L * Real.sin φi + r * Real.sin (φi - φj)) / L)|
      = |F * gp (k * L) * k * (pairDist r L φi φj
      - (L + r * (Real.cos φj - Real.cos φi)))
      * (L * Real.sin φi + r * Real.sin (φi - φj)) / L| := abs_neg _
  have n4 : |-(F * (g (k * pairDist r L φi φj) - g (k * L)
      - gp (k * L) * (k * pairDist r L φi φj - k * L))
      * (L * Real.sin φi + r * Real.sin (φi - φj)) / L)|
      = |F * (g (k * pairDist r L φi φj) - g (k * L)
      - gp (k * L) * (k * pairDist r L φi φj - k * L))
      * (L * Real.sin φi + r * Real.sin (φi - φj)) / L| := abs_neg _
  have n5 : |-(F * (g (k * L) + gp (k * L) * (k * pairDist r L φi φj - k * L)
      + (g (k * pairDist r L φi φj) - g (k * L)
        - gp (k * L) * (k * pairDist r L φi φj - k * L)))
      * (L * Real.sin φi + r * Real.sin (φi - φj))
      * (1 / pairDist r L φi φj - 1 / L))|
      = |F * (g (k * L) + gp (k * L) * (k * pairDist r L φi φj - k * L)
      + (g (k * pairDist r L φi φj) - g (k * L)
        - gp (k * L) * (k * pairDist r L φi φj - k * L)))
      * (L * Real.sin φi + r * Real.sin (φi - φj))
      * (1 / pairDist r L φi φj - 1 / L)| := abs_neg _
  have i1 := abs_le_abs_add_abs
    ((F * r / L) * g (k * L) * Real.sin φi * (Real.cos φi - Real.cos φj)
      + F * k * r * gp (k * L) * (Real.cos φi - Real.cos φj) * (r / L)
        * Real.sin (φi - φj)
      + (-(F * gp (k * L) * k * (pairDist r L φi φj
        - (L + r * (Real.cos φj - Real.cos φi)))
        * (L * Real.sin φi + r * Real.sin (φi - φj)) / L))
      + (-(F * (g (k * pairDist r L φi φj) - g (k * L)
        - gp (k * L) * (k * pairDist r L φi φj - k * L))
        * (L * Real.sin φi + r * Real.sin (φi - φj)) / L)))
    (-(F * (g (k * L) + gp (k * L) * (k * pairDist r L φi φj - k * L)
      + (g (k * pairDist r L φi φj) - g (k * L)
        - gp (k * L) * (k * pairDist r L φi φj - k * L)))
      * (L * Real.sin φi + r * Real.sin (φi - φj))
      * (1 / pairDist r L φi φj - 1 / L)))
  have i2 := abs_le_abs_add_abs
    ((F * r / L) * g (k * L) * Real.sin φi * (Real.cos φi - Real.cos φj)
      + F * k * r * gp (k * L) * (Real.cos φi - Real.cos φj) * (r / L)
        * Real.sin (φi - φj)
      + (-(F * gp (k * L) * k * (pairDist r L φi φj
        - (L + r * (Real.cos φj - Real.cos φi)))
        * (L * Real.sin φi + r * Real.sin (φi - φj)) / L)))
    (-(F * (g (k * pairDist r L φi φj) - g (k * L)
      - gp (k * L) * (k * pairDist r L φi φj - k * L))
      * (L * Real.sin φi + r * Real.sin (φi - φj)) / L))
  have i3 := abs_le_abs_add_abs
    ((F * r / L) * g (k * L) * Real.sin φi * (Real.cos φi - Real.cos φj)
      + F * k * r * gp (k * L) * (Real.cos φi - Real.cos φj) * (r / L)
        * Real.sin (φi - φj))
    (-(F * gp (k * L) * k * (pairDist r L φi φj
      - (L + r * (Real.cos φj - Real.cos φi)))
      * (L * Real.sin φi + r * Real.sin (φi - φj)) / L))
  have i4 := abs_le_abs_add_abs
    ((F * r / L) * g (k * L) * Real.sin φi * (Real.cos φi - Real.cos φj))
    (F * k * r * gp (k * L) * (Real.cos φi - Real.cos φj) * (r / L)
      * Real.sin (φi - φj))
  rw [key]
  linarith [i1, i2, i3, i4, n3, n4, n5, bx1, bx2, bx3, bx4, bx5, finalform]

/-! ## Pair structure and the two-neighbour assembly of equation (23) -/

/-- Within one pair, the azimuthal forces on the two droplets sum to a
term proportional to `sin φⱼ - sin φᵢ`: the single-spin contributions
`∓ℱ g(k_F L) sin φ` of equation (22) enter the two members of a pair with
opposite signs. This exact identity is the pair-level structure behind the
cancellation of the single-spin term when the forces from the two
neighbouring droplets are summed in equation (23). -/
theorem pair_azimuth_forces_sum (F : ℝ) (g : ℝ → ℝ) (k r L φi φj : ℝ) :
    leftAzimuthForce F g k r L φi φj + rightAzimuthForce F g k r L φi φj
      = (F * g (k * pairDist r L φi φj) / pairDist r L φi φj) * L
          * (Real.sin φj - Real.sin φi) := by
  unfold leftAzimuthForce rightAzimuthForce
  ring

/-- The two-neighbour tangential balance reduction: with the azimuthal
wave forces of the two nearest neighbours collected as `FL` (from the left
neighbour, `rightAzimuthForce` form) and `FR` (from the right neighbour,
`leftAzimuthForce` form), the balance (11) implies the phase equation in
the force form of equation (12); equation (23) is obtained by identifying
the neighbour forces with the negative phase gradients of the pair
potential, `FL + FR = -(∂U_{i-1,i}/∂φᵢ + ∂U_{i,i+1}/∂φᵢ)`, i.e. with
signed sums of `gkPairForce` — the potential of equation (24) absorbs the
`1/(m_w r)` factor of the force form, so the printed equation (23) has no
explicit `1/(m_w r)`. -/
theorem tangential_balance_reduction_pair (m r D τ u₀ ω₀ ωdot ω FL FR : ℝ)
    (hm : m ≠ 0) (hr : r ≠ 0)
    (hτ : τ = m / D) (hω₀ : ω₀ = u₀ / r)
    (hbal : m * (r * ωdot) = D * (1 - (r * ω) ^ 2 / u₀ ^ 2) * (r * ω) + FL + FR) :
    ωdot = 1 / τ * (1 - ω ^ 2 / ω₀ ^ 2) * ω + (FL + FR) / (m * r) := by
  rw [show (r * ω) ^ 2 = ω ^ 2 * r ^ 2 from by ring] at hbal
  have hmr : m * r ≠ 0 := mul_ne_zero hm hr
  rw [hτ, hω₀]
  rw [show 1 / (m / D) = D / m from by field_simp,
    show ω ^ 2 / (u₀ / r) ^ 2 = ω ^ 2 * r ^ 2 / u₀ ^ 2 from by field_simp]
  refine mul_right_cancel₀ hmr ?_
  rw [add_mul, div_mul_cancel₀ (FL + FR) hmr]
  rw [show D / m * (1 - ω ^ 2 * r ^ 2 / u₀ ^ 2) * ω * (m * r)
      = D * (1 - ω ^ 2 * r ^ 2 / u₀ ^ 2) * (r * ω) from by
    field_simp [hm]]
  rw [show ωdot * (m * r) = m * (r * ωdot) from by ring, hbal]
  ring

/-- The two-neighbour phase equation in generalized Kuramoto form, the
content of equation (23): if the two neighbour forces equal the signed
GK pair forces with coefficients `(a, b)` (right neighbour) and
`(a', b')` (left neighbour), then the phase dynamics reads
`ω̇ = (1/τ)(1 − ω²/ω₀²)ω + (gkPairForce a b φᵢ φ_R + gkPairForce a' b' φ_L φᵢ)/(m r)`,
the lattice version of equation (23) with the potential absorbing the
`1/(m_w r)` factor. -/
theorem gk_phase_equation_pair (m r D τ u₀ ω₀ ωdot ω a b a' b' φi φL φR : ℝ)
    (hm : m ≠ 0) (hr : r ≠ 0)
    (hτ : τ = m / D) (hω₀ : ω₀ = u₀ / r)
    (hbal : m * (r * ωdot) = D * (1 - (r * ω) ^ 2 / u₀ ^ 2) * (r * ω)
      + gkPairForce a b φi φR + gkPairForce a' b' φL φi) :
    ωdot = 1 / τ * (1 - ω ^ 2 / ω₀ ^ 2) * ω
      + (gkPairForce a b φi φR + gkPairForce a' b' φL φi) / (m * r) :=
  tangential_balance_reduction_pair m r D τ u₀ ω₀ ωdot ω
    (gkPairForce a b φi φR) (gkPairForce a' b' φL φi) hm hr hτ hω₀ hbal

end Qatlib.Papers.HydroSpinLatt21.GKModel

end
