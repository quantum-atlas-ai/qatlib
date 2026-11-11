/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ScatteringQFT11.MainResults.PositiveMassBounds
import Qatlib.Papers.ScatteringQFT11.MainResults.MomentBound

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 4: energy bounds in the negative-mass regime

Jordan–Lee–Preskill, *Quantum Computation of Scattering in Scalar Quantum Field
Theories* (arXiv:1112.4833v1), Proposition 4 (p. 23, inequalities (80)–(81)): let
`H` be the lattice `φ⁴` Hamiltonian (4) with `m₀² ≤ 0` and `λ₀ > 0`, and let `|ψ⟩`
be any state with `⟨ψ|H|ψ⟩ ≤ E`. Then for every lattice site `x`,

`⟨ψ|φ(x)²|ψ⟩ ≤ −6m₀²/λ₀ + √(36m₀⁴/λ₀² + (24/(λ₀a^d)) (E + 3(V − a^d)m₀⁴/(2λ₀)))`,
`⟨ψ|π(x)²|ψ⟩ ≤ (2/a^d) (E + 3V m₀⁴/(2λ₀))`,

where `V` is the total volume `(#sites)·a^d` of the lattice.

The paper's proof (p. 23):
* the on-site potential `U(φ) = m₀²φ²/2 + λ₀φ⁴/4!` has minimal eigenvalue
  `U_min = −3m₀⁴/(2λ₀)`, obtained by completing the square;
* dropping positive semidefinite terms from `H`, every site except `x`
  contributes at least `a^d U_min`, which produces (81), and produces (89) for the
  field at `x`;
* Proposition 2 applied to `φ(x)²` gives `⟨φ(x)⁴⟩ ≥ ⟨φ(x)²⟩²`, and the quadratic
  formula then yields (80).

In the finite model the "minimal eigenvalue" step is replaced by the equivalent
operator-free route: the scalar completion of squares on the two moments,
`U_min ≤ (m₀²/2)⟨φ²⟩ + (λ₀/24!)·⟨φ⁴⟩`, using `⟨φ⁴⟩ ≥ ⟨φ²⟩²` from Proposition 2.
Every dropped term is positive semidefinite exactly as in the paper.
-/

namespace Qatlib.Papers.ScatteringQFT11.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath

open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {sites : Type*} [Fintype sites] [DecidableEq sites]

/-- The scalar minimum `U_min = −3m₀⁴/(2λ₀)` of the on-site potential
`U(u) = (m₀²/2)u + (λ₀/24)u²` in `u = φ²` when `m₀² ≤ 0 < λ₀`, equation (83) of
the paper. -/
noncomputable def phi4PotentialMin (m0sq lam : ℝ) : ℝ := -3 * m0sq ^ 2 / (2 * lam)

/-- The **completion of squares** behind equation (83): for `λ₀ > 0` the scalar
potential is bounded below by `U_min` for every real profile `u`,
`−3m₀⁴/(2λ₀) ≤ (m₀²/2)u + (λ₀/24)u²`. -/
theorem phi4PotentialMin_le (m0sq lam u : ℝ) (hlam : 0 < lam) :
    phi4PotentialMin m0sq lam ≤ (m0sq / 2) * u + (lam / 24) * u ^ 2 := by
  have hpos : (0:ℝ) < lam / 24 := by linarith
  have hid : (m0sq / 2) * u + (lam / 24) * u ^ 2 - phi4PotentialMin m0sq lam
      = (lam / 24) * (u + 6 * m0sq / lam) ^ 2 := by
    rw [phi4PotentialMin]; field_simp; ring
  have hsq := sq_nonneg (u + 6 * m0sq / lam)
  nlinarith [hid, hsq, hpos]

/-- The **quadratic-form bound** behind inequality (80): if `X ≥ 0` satisfies
`(m/2)X + (λ/24)X² ≤ C` with `λ > 0`, then
`X ≤ −6m/λ + √(36m²/λ² + 24C/λ)`. This is the quadratic formula applied to
inequality (90) of the paper. -/
theorem phi4_quadratic_bound (m lam C X : ℝ) (hlam : 0 < lam) (hX : 0 ≤ X)
    (hineq : (m / 2) * X + (lam / 24) * X ^ 2 ≤ C) :
    X ≤ -6 * m / lam + Real.sqrt (36 * m ^ 2 / lam ^ 2 + 24 * C / lam) := by
  have hlam6 : (0:ℝ) < lam / 6 := by linarith
  have hlam12 : (0:ℝ) < lam / 12 := by linarith
  have hsq : (lam / 12 * X + m / 2)^2 ≤ m^2/4 + lam*C/6 := by
    have hscaled : (lam / 6) * ((m / 2) * X + (lam / 24) * X ^ 2) ≤ (lam / 6) * C :=
      mul_le_mul_of_nonneg_left hineq (le_of_lt hlam6)
    nlinarith [hscaled]
  set D : ℝ := m^2/4 + lam*C/6 with hD
  have habs : |lam/12 * X + m/2| ≤ Real.sqrt D := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  have hupper : lam/12 * X + m/2 ≤ Real.sqrt D := (abs_le.mp habs).2
  have hXb : X ≤ (12/lam) * (Real.sqrt D - m/2) := by
    have h1 : lam/12 * X ≤ Real.sqrt D - m/2 := by linarith
    rw [show (12/lam) * (Real.sqrt D - m/2) = (Real.sqrt D - m/2) / (lam/12) by field_simp]
    rw [le_div_iff₀ hlam12]
    nlinarith [h1]
  have hsqrt : (12/lam) * Real.sqrt D = Real.sqrt (36*m^2/lam^2 + 24*C/lam) := by
    have hT : 36*m^2/lam^2 + 24*C/lam = (12/lam)^2 * D := by
      rw [hD]; field_simp; ring
    rw [hT, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  calc X ≤ (12/lam) * (Real.sqrt D - m/2) := hXb
    _ = (12/lam) * Real.sqrt D - 6*m/lam := by field_simp; ring
    _ = -6*m/lam + Real.sqrt (36*m^2/lam^2 + 24*C/lam) := by rw [hsqrt]; ring

/-- **Equation (83)** at the level of expectations: with `λ₀ > 0` the on-site
potential energy of any unit-norm state is at least `U_min`, because
Proposition 2 gives `⟨φ⁴⟩ ≥ ⟨φ²⟩²` and the scalar potential is bounded by
`U_min` at `u = ⟨φ²⟩`. -/
theorem phi4_local_energy_ge_min (m0sq lam : ℝ) (hlam : 0 < lam)
    (phi : sites → Matrix n n ℂ) (hphi : ∀ y, (phi y)ᴴ = phi y)
    (ψ : QState n) (hψ : Normalized ψ) (y : sites) :
    phi4PotentialMin m0sq lam
      ≤ (m0sq / 2) * expectation (phi y * phi y) ψ
        + (lam / 24) * expectation (phi y ^ 4) ψ := by
  have hX : (0:ℝ) ≤ expectation (phi y * phi y) ψ := expectation_sq_nonneg (hphi y) ψ
  have hsq : expectation (phi y * phi y) ψ ^ 2 ≤ expectation (phi y ^ 4) ψ :=
    expectation_sq_le_expectation_pow_four (phi y) ψ (hphi y) hψ
  have hlam24 : (0:ℝ) ≤ lam / 24 := by linarith
  have h1 : (m0sq / 2) * expectation (phi y * phi y) ψ
      + (lam / 24) * expectation (phi y * phi y) ψ ^ 2
      ≤ (m0sq / 2) * expectation (phi y * phi y) ψ + (lam / 24) * expectation (phi y ^ 4) ψ := by
    nlinarith [mul_nonneg hlam24 (sub_nonneg.mpr hsq)]
  have h2 := phi4PotentialMin_le m0sq lam (expectation (phi y * phi y) ψ) hlam
  linarith

/-- Splitting a finite sum at a distinguished index. -/
theorem sum_eq_single_add_erase {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (x : ι) :
    ∑ y, f y = f x + ∑ y ∈ Finset.univ.erase x, f y := by
  classical
  have h := Finset.add_sum_erase (Finset.univ : Finset ι) f (Finset.mem_univ x)
  linarith [h]

/-- The erased sum of a constant. -/
theorem sum_erase_const {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℝ) (x : ι) :
    ∑ _y ∈ Finset.univ.erase x, c = ((Fintype.card ι : ℝ) - 1) * c := by
  classical
  have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨x⟩
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
    nsmul_eq_mul, Nat.cast_sub hpos, Nat.cast_one]

/-- **Proposition 4**, inequality (81) (p. 23): in the negative-mass regime
`m₀² ≤ 0 < λ₀`, the momentum fluctuations at each site are bounded by the energy,
`⟨ψ|π(x)²|ψ⟩ ≤ (2/a^d)(E + 3V m₀⁴/(2λ₀))` with `V = (#sites)·a^d` the lattice
volume. -/
theorem phi4_negative_mass_momentum_bound (d : ℕ) (a m0sq lam : ℝ)
    (ha : 0 < a) (hm : m0sq ≤ 0) (hl : 0 < lam)
    (gradSq phi piOp : sites → Matrix n n ℂ)
    (hgrad : ∀ y, (gradSq y).PosSemidef) (hphi : ∀ y, (phi y)ᴴ = phi y)
    (hpi : ∀ y, (piOp y)ᴴ = piOp y) (ψ : QState n) (hψ : Normalized ψ) {E : ℝ}
    (hE : expectation (phi4Hamiltonian d a m0sq lam gradSq phi piOp) ψ ≤ E) (x : sites) :
    expectation (piOp x * piOp x) ψ
      ≤ (2 / a ^ d) * (E + 3 * ((Fintype.card sites : ℝ) * a ^ d) * m0sq ^ 2 / (2 * lam)) := by
  classical
  have haD : (0:ℝ) < a ^ d := pow_pos ha d
  set Umin : ℝ := phi4PotentialMin m0sq lam with hUmin
  -- local energy of every site, decomposed into its four contributions
  set Lexp : sites → ℝ := fun y => (1 / 2) * expectation (piOp y * piOp y) ψ
      + (1 / 2) * expectation (gradSq y) ψ
      + (m0sq / 2) * expectation (phi y * phi y) ψ
      + (lam / 24) * expectation (phi y ^ 4) ψ with hLexp
  have hdecomp : expectation (phi4Hamiltonian d a m0sq lam gradSq phi piOp) ψ
      = ∑ y, a ^ d * Lexp y := by
    rw [expectation_phi4Hamiltonian]
  -- every site contributes at least `a^d U_min`
  have hsite : ∀ y, a ^ d * Umin ≤ a ^ d * Lexp y := by
    intro y
    have h1 : Umin ≤ (m0sq / 2) * expectation (phi y * phi y) ψ
        + (lam / 24) * expectation (phi y ^ 4) ψ :=
      phi4_local_energy_ge_min m0sq lam hl phi hphi ψ hψ y
    have h2 : (0:ℝ) ≤ expectation (piOp y * piOp y) ψ := expectation_sq_nonneg (hpi y) ψ
    have h3 : (0:ℝ) ≤ expectation (gradSq y) ψ := expectation_nonneg (hgrad y) ψ
    have hL : Umin ≤ Lexp y := by
      rw [hLexp]
      nlinarith [h1, h2, h3]
    exact mul_le_mul_of_nonneg_left hL (le_of_lt haD)
  -- the site `x` additionally carries its momentum term
  have hxterm : a ^ d * ((1 / 2) * expectation (piOp x * piOp x) ψ + Umin) ≤ a ^ d * Lexp x := by
    have h1 : Umin ≤ (m0sq / 2) * expectation (phi x * phi x) ψ
        + (lam / 24) * expectation (phi x ^ 4) ψ :=
      phi4_local_energy_ge_min m0sq lam hl phi hphi ψ hψ x
    have h3 : (0:ℝ) ≤ expectation (gradSq x) ψ := expectation_nonneg (hgrad x) ψ
    have hL : (1 / 2) * expectation (piOp x * piOp x) ψ + Umin ≤ Lexp x := by
      rw [hLexp]
      nlinarith [h1, h3]
    exact mul_le_mul_of_nonneg_left hL (le_of_lt haD)
  -- the total energy is at least the site term plus `U_min` on every site
  have hsplit := sum_eq_single_add_erase (fun y => a ^ d * Lexp y) x
  have hrest : ∑ y ∈ Finset.univ.erase x, a ^ d * Umin ≤ ∑ y ∈ Finset.univ.erase x, a ^ d * Lexp y :=
    Finset.sum_le_sum fun y _ => hsite y
  have hrestval : ∑ y ∈ Finset.univ.erase x, a ^ d * Umin
      = ((Fintype.card sites : ℝ) - 1) * (a ^ d * Umin) := by
    rw [sum_erase_const]
  have hrest' : ((Fintype.card sites : ℝ) - 1) * (a ^ d * Umin)
      ≤ ∑ y ∈ Finset.univ.erase x, a ^ d * Lexp y := by
    rw [← hrestval]
    exact hrest
  have htotal : a ^ d * ((1 / 2) * expectation (piOp x * piOp x) ψ + Umin)
      + ((Fintype.card sites : ℝ) - 1) * (a ^ d * Umin) ≤ E := by
    have h1 : a ^ d * ((1 / 2) * expectation (piOp x * piOp x) ψ + Umin)
        + ((Fintype.card sites : ℝ) - 1) * (a ^ d * Umin)
        ≤ a ^ d * Lexp x + ∑ y ∈ Finset.univ.erase x, a ^ d * Lexp y := by
      have := add_le_add hxterm hrest'
      linarith
    rw [hdecomp, hsplit] at hE
    linarith
  -- arithmetic: solve for the momentum fluctuation
  rw [hUmin, phi4PotentialMin] at htotal
  rw [show (2 / a ^ d) * (E + 3 * ((Fintype.card sites : ℝ) * a ^ d) * m0sq ^ 2 / (2 * lam))
      = 2 * (E + 3 * ((Fintype.card sites : ℝ) * a ^ d) * m0sq ^ 2 / (2 * lam)) / a ^ d by
    field_simp]
  rw [le_div_iff₀ haD]
  have h2 := mul_le_mul_of_nonneg_left htotal (le_of_lt hl)
  field_simp at h2 ⊢
  nlinarith [h2]

/-- **Proposition 4**, inequality (80) (p. 23): in the negative-mass regime
`m₀² ≤ 0 < λ₀`, the field fluctuations at each site obey

`⟨ψ|φ(x)²|ψ⟩ ≤ −6m₀²/λ₀ + √(36m₀⁴/λ₀² + (24/(λ₀a^d)) (E + 3(V − a^d)m₀⁴/(2λ₀)))`

with `V = (#sites)·a^d` the lattice volume. -/
theorem phi4_negative_mass_field_bound (d : ℕ) (a m0sq lam : ℝ)
    (ha : 0 < a) (hm : m0sq ≤ 0) (hl : 0 < lam)
    (gradSq phi piOp : sites → Matrix n n ℂ)
    (hgrad : ∀ y, (gradSq y).PosSemidef) (hphi : ∀ y, (phi y)ᴴ = phi y)
    (hpi : ∀ y, (piOp y)ᴴ = piOp y) (ψ : QState n) (hψ : Normalized ψ) {E : ℝ}
    (hE : expectation (phi4Hamiltonian d a m0sq lam gradSq phi piOp) ψ ≤ E) (x : sites) :
    expectation (phi x * phi x) ψ ≤ -6 * m0sq / lam
      + Real.sqrt (36 * m0sq ^ 2 / lam ^ 2
        + 24 / (lam * a ^ d)
          * (E + 3 * (((Fintype.card sites : ℝ) * a ^ d) - a ^ d) * m0sq ^ 2 / (2 * lam))) := by
  classical
  have haD : (0:ℝ) < a ^ d := pow_pos ha d
  set Umin : ℝ := phi4PotentialMin m0sq lam with hUmin
  set X : ℝ := expectation (phi x * phi x) ψ with hXdef
  set Y : ℝ := expectation (phi x ^ 4) ψ with hYdef
  set Lexp : sites → ℝ := fun y => (1 / 2) * expectation (piOp y * piOp y) ψ
      + (1 / 2) * expectation (gradSq y) ψ
      + (m0sq / 2) * expectation (phi y * phi y) ψ
      + (lam / 24) * expectation (phi y ^ 4) ψ with hLexp
  have hdecomp : expectation (phi4Hamiltonian d a m0sq lam gradSq phi piOp) ψ
      = ∑ y, a ^ d * Lexp y := by
    rw [expectation_phi4Hamiltonian]
  have hsite : ∀ y, a ^ d * Umin ≤ a ^ d * Lexp y := by
    intro y
    have h1 : Umin ≤ (m0sq / 2) * expectation (phi y * phi y) ψ
        + (lam / 24) * expectation (phi y ^ 4) ψ :=
      phi4_local_energy_ge_min m0sq lam hl phi hphi ψ hψ y
    have h2 : (0:ℝ) ≤ expectation (piOp y * piOp y) ψ := expectation_sq_nonneg (hpi y) ψ
    have h3 : (0:ℝ) ≤ expectation (gradSq y) ψ := expectation_nonneg (hgrad y) ψ
    have hL : Umin ≤ Lexp y := by
      rw [hLexp]
      nlinarith [h1, h2, h3]
    exact mul_le_mul_of_nonneg_left hL (le_of_lt haD)
  have hxterm : a ^ d * ((m0sq / 2) * X + (lam / 24) * Y) ≤ a ^ d * Lexp x := by
    have h2 : (0:ℝ) ≤ expectation (piOp x * piOp x) ψ := expectation_sq_nonneg (hpi x) ψ
    have h3 : (0:ℝ) ≤ expectation (gradSq x) ψ := expectation_nonneg (hgrad x) ψ
    have hL : (m0sq / 2) * X + (lam / 24) * Y ≤ Lexp x := by
      rw [hLexp, hXdef, hYdef]
      nlinarith [h2, h3]
    exact mul_le_mul_of_nonneg_left hL (le_of_lt haD)
  have hsplit := sum_eq_single_add_erase (fun y => a ^ d * Lexp y) x
  have hrest : ∑ y ∈ Finset.univ.erase x, a ^ d * Umin ≤ ∑ y ∈ Finset.univ.erase x, a ^ d * Lexp y :=
    Finset.sum_le_sum fun y _ => hsite y
  have hrestval : ∑ y ∈ Finset.univ.erase x, a ^ d * Umin
      = ((Fintype.card sites : ℝ) - 1) * (a ^ d * Umin) := by
    rw [sum_erase_const]
  have hrest' : ((Fintype.card sites : ℝ) - 1) * (a ^ d * Umin)
      ≤ ∑ y ∈ Finset.univ.erase x, a ^ d * Lexp y := by
    rw [← hrestval]
    exact hrest
  have htotal : a ^ d * ((m0sq / 2) * X + (lam / 24) * Y)
      + ((Fintype.card sites : ℝ) - 1) * (a ^ d * Umin) ≤ E := by
    have h1 : a ^ d * ((m0sq / 2) * X + (lam / 24) * Y)
        + ((Fintype.card sites : ℝ) - 1) * (a ^ d * Umin)
        ≤ a ^ d * Lexp x + ∑ y ∈ Finset.univ.erase x, a ^ d * Lexp y := by
      have := add_le_add hxterm hrest'
      linarith
    rw [hdecomp, hsplit] at hE
    linarith
  -- properties of the moments at `x`
  have hXnn : (0:ℝ) ≤ X := by
    rw [hXdef]; exact expectation_sq_nonneg (hphi x) ψ
  have hXY : X ^ 2 ≤ Y := by
    rw [hXdef, hYdef]
    exact expectation_sq_le_expectation_pow_four (phi x) ψ (hphi x) hψ
  have hlam24 : (0:ℝ) ≤ lam / 24 := by linarith
  -- replace `Y` by `X²` and drop the momentum and gradient terms
  have hineq : (m0sq / 2) * X + (lam / 24) * X ^ 2
      ≤ E / a ^ d - (((Fintype.card sites : ℝ) - 1) * Umin) := by
    have hstep : (m0sq / 2) * X + (lam / 24) * X ^ 2 ≤ (m0sq / 2) * X + (lam / 24) * Y := by
      nlinarith [mul_nonneg hlam24 (sub_nonneg.mpr hXY)]
    have hE' : a ^ d * ((m0sq / 2) * X + (lam / 24) * Y)
        ≤ E - ((Fintype.card sites : ℝ) - 1) * (a ^ d * Umin) := by linarith
    have hdiv : (m0sq / 2) * X + (lam / 24) * Y
        ≤ (E - ((Fintype.card sites : ℝ) - 1) * (a ^ d * Umin)) / a ^ d := by
      rw [le_div_iff₀ haD]
      nlinarith [hE']
    have hrhs : (E - ((Fintype.card sites : ℝ) - 1) * (a ^ d * Umin)) / a ^ d
        = E / a ^ d - (((Fintype.card sites : ℝ) - 1) * Umin) := by
      field_simp
    linarith
  -- the scalar quadratic bound
  have hquad := phi4_quadratic_bound m0sq lam
    (E / a ^ d - (((Fintype.card sites : ℝ) - 1) * Umin)) X hl hXnn hineq
  rw [hUmin, phi4PotentialMin] at hquad
  rw [hXdef] at hquad
  -- rewrite the square-root argument into the paper's form
  have harg : 36 * m0sq ^ 2 / lam ^ 2
      + 24 * (E / a ^ d - (((Fintype.card sites : ℝ) - 1) * (-3 * m0sq ^ 2 / (2 * lam)))) / lam
      = 36 * m0sq ^ 2 / lam ^ 2
        + 24 / (lam * a ^ d)
          * (E + 3 * (((Fintype.card sites : ℝ) * a ^ d) - a ^ d) * m0sq ^ 2 / (2 * lam)) := by
    field_simp
    ring
  rw [harg] at hquad
  exact hquad

end Qatlib.Papers.ScatteringQFT11.MainResults
