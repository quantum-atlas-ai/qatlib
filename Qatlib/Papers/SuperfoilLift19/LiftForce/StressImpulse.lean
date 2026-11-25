/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.LiftForce.ImpulseLift
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Stress-tensor contour force: wall and far-field contributions

[Musser2019Superfoil], p. 154502-3, Eq. (5), states that the `k`th component
of the force exerted by the superfluid on the airfoil is obtained by
integrating the stress-energy tensor
`T_jk = m ρ u_j u_k + δ_jk (g/2) ρ² − (ℏ²/4m) ρ ∂_j∂_k ln ρ`
around *any* path enclosing the airfoil. See
[the published article](https://doi.org/10.1103/PhysRevLett.123.154502).

This module develops the analytic content of that statement for
axis-parallel rectangular contours in the plane `ℝ × ℝ`:

* `stressTensor` transcribes Eq. (5) literally, with the quantum-pressure
  field `ρ ∂_j ∂_k ln ρ` supplied per component, and is symmetric for a
  symmetric quantum-pressure field (`stressTensor_symmetric`);
* `rectangleForce` is the contour integral `F_k = ∮ T_jk n_j dl` of a tensor
  around the boundary of a rectangle with outward normal;
* `flux_wall_eq_far_field_on_shell` proves that for a momentum flux which is
  divergence-free in the fluid region between an inner (wall) and an outer
  (far-field) box, the wall contour force equals the far-field contour force;
  the proof evaluates the divergence theorem of
  `Mathlib.MeasureTheory.Integral.DivergenceTheorem` on the four strips of the
  annulus and combines them with interval additivity;
* `wall_force_eq_ideal_lift` combines the equality with the locked
  impulse module: when the far-field flux is carried by an advected point
  vortex, the wall force is exactly the ideal Kutta--Joukowski lift;
* `flux_counterexample_of_nonzero_divergence` shows by an explicit linear
  field that path independence fails without the divergence-free premise.

Statements are phrased over a complete normed space `E` so that all force
arithmetic is elaborated uniformly; physical force components are the
`E = ℝ` instances. The divergence-free premise encodes steady momentum
conservation of the Madelung equations in the fluid region; it is a
hypothesis here, not derived from the Gross--Pitaevskii equation. Nothing is
claimed about the numerical force curves, the incompressible filtering
procedure, or near-zero drag.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfoilLift19.LiftForce

open Qatlib.Papers.SuperfoilLift19.LiftForce

/-- **The stress–energy tensor of Eq. (5)** of [Musser2019Superfoil],
p. 154502-3: `T_jk = m ρ u_j u_k + δ_jk (g/2) ρ² − (ℏ²/4m) ρ ∂_j∂_k ln ρ` as
component functions on the plane `ℝ × ℝ` indexed by `Fin 2`. The velocity
components are `u x j`; the field `q x j k` stands for the quantum-pressure
combination `ρ ∂_j ∂_k ln ρ` of the wavefunction amplitude, whose symmetry is
recorded in `stressTensor_symmetric`. -/
def stressTensor (mass gint hbar : ℝ) (rho : ℝ × ℝ → ℝ) (u : ℝ × ℝ → Fin 2 → ℝ)
    (q : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) (x : ℝ × ℝ) (j k : Fin 2) : ℝ :=
  mass * rho x * u x j * u x k +
    (if j = k then gint / 2 * rho x ^ 2 else 0) -
    hbar ^ 2 / (4 * mass) * q x j k

/-- The Eq. (5) tensor is symmetric whenever the quantum-pressure field is
symmetric, as it is for a `C²` amplitude since `∂_j ∂_k ln ρ = ∂_k ∂_j ln ρ`. -/
theorem stressTensor_symmetric (mass gint hbar : ℝ) (rho : ℝ × ℝ → ℝ)
    (u : ℝ × ℝ → Fin 2 → ℝ) (q : ℝ × ℝ → Fin 2 → Fin 2 → ℝ)
    (hq : ∀ x : ℝ × ℝ, q x 1 0 = q x 0 1) (x : ℝ × ℝ) (j k : Fin 2) :
    stressTensor mass gint hbar rho u q x j k =
      stressTensor mass gint hbar rho u q x k j := by
  unfold stressTensor
  fin_cases j <;> fin_cases k <;> simp [hq] <;> ring

/-- **The contour force of Eq. (5).** The `k`th component of the force on the
airfoil as the integral of the tensor `T` around the boundary of the
axis-parallel rectangle with corners `p` and `q`, with outward normal:
the top edge carries `T 1 k` (normal `+e₂`), the bottom `−T 1 k`, the right
edge `T 0 k` (normal `+e₁`), and the left `−T 0 k`. -/
def rectangleForce {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ × ℝ → Fin 2 → Fin 2 → E) (k : Fin 2) (p q : ℝ × ℝ) : E :=
  (((∫ x in p.1..q.1, T (x, q.2) (1 : Fin 2) k) - ∫ x in p.1..q.1, T (x, p.2) (1 : Fin 2) k) +
    ∫ y in p.2..q.2, T (q.1, y) (0 : Fin 2) k) -
    ∫ y in p.2..q.2, T (p.1, y) (0 : Fin 2) k

/-- Divergence-theorem core on one strip: if the momentum flux `(f, g)` is
continuous on the closed outer rectangle, differentiable with integrable
divergence on its interior, and divergence-free on the interior of a smaller
axis-parallel strip, then the total boundary integral of the strip vanishes. -/
private theorem strip_boundary_integral_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : ℝ × ℝ → E} {f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E} {c d : ℝ × ℝ}
    (Hcf : ContinuousOn f (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2))
    (Hcg : ContinuousOn g (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2))
    (Hdf : ∀ x ∈ Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2, HasFDerivAt f (f' x) x)
    (Hdg : ∀ x ∈ Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2, HasFDerivAt g (g' x) x)
    (Hi : MeasureTheory.IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1))
      (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2) MeasureTheory.volume)
    {p₁ q₁ p₂ q₂ : ℝ} (ho1 : c.1 ≤ p₁) (ho2 : q₁ ≤ d.1) (ho3 : c.2 ≤ p₂)
    (ho4 : q₂ ≤ d.2) (hpq1 : p₁ ≤ q₁) (hpq2 : p₂ ≤ q₂)
    (hfl : ∀ x ∈ Set.Ioo p₁ q₁ ×ˢ Set.Ioo p₂ q₂, f' x (1, 0) + g' x (0, 1) = 0) :
    (((∫ x in p₁..q₁, g (x, q₂)) - ∫ x in p₁..q₁, g (x, p₂)) + ∫ y in p₂..q₂, f (q₁, y)) -
      ∫ y in p₂..q₂, f (p₁, y) = 0 := by
  have hm1 : c.1 ≤ min p₁ q₁ := le_min ho1 (le_trans ho1 hpq1)
  have hM1 : max p₁ q₁ ≤ d.1 := max_le (le_trans hpq1 ho2) ho2
  have hm2 : c.2 ≤ min p₂ q₂ := le_min ho3 (le_trans ho3 hpq2)
  have hM2 : max p₂ q₂ ≤ d.2 := max_le (le_trans hpq2 ho4) ho4
  have hstripIcc : Set.uIcc p₁ q₁ ×ˢ Set.uIcc p₂ q₂ ⊆ Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2 := by
    rw [Set.uIcc_of_le hpq1, Set.uIcc_of_le hpq2]
    rintro z ⟨h1, h2⟩
    exact Set.mem_prod.2 ⟨⟨ho1.trans h1.1, h1.2.trans ho2⟩, ⟨ho3.trans h2.1, h2.2.trans ho4⟩⟩
  have hstripIoo : Set.Ioo (min p₁ q₁) (max p₁ q₁) ×ˢ Set.Ioo (min p₂ q₂) (max p₂ q₂) ⊆
      Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2 := by
    rintro z ⟨h1, h2⟩
    exact Set.mem_prod.2 ⟨⟨lt_of_le_of_lt hm1 h1.1, lt_of_lt_of_le h1.2 hM1⟩,
      ⟨lt_of_le_of_lt hm2 h2.1, lt_of_lt_of_le h2.2 hM2⟩⟩
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt f g f' g' p₁ p₂ q₁ q₂
    (Hcf.mono hstripIcc) (Hcg.mono hstripIcc)
    (fun x hx => Hdf x (hstripIoo hx)) (fun x hx => Hdg x (hstripIoo hx))
    (Hi.mono_set hstripIcc)
  have hzero : (∫ x in p₁..q₁, ∫ y in p₂..q₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)) = 0 := by
    have h0 : ∀ x ∈ Set.Ioo p₁ q₁,
        ∫ y in p₂..q₂, f' (x, y) (1, 0) + g' (x, y) (0, 1) = 0 := by
      intro x hx
      rw [intervalIntegral.integral_congr_Ioo_of_le hpq2
        (fun y hy => hfl (x, y) (Set.mem_prod.2 ⟨hx, hy⟩)), intervalIntegral.integral_zero]
    rw [intervalIntegral.integral_congr_Ioo_of_le hpq1 h0, intervalIntegral.integral_zero]
  rw [hzero] at key
  linear_combination (norm := abel_nf) -key

/-- The closed fluid shell between the two rectangular contours. The wall
and the outer contour belong to the shell. -/
def rectangularShell (c d a b : ℝ × ℝ) : Set (ℝ × ℝ) :=
  (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2) \
    (Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2)

/-- The open region of fluid strictly between the rectangular contours. -/
def rectangularShellInterior (c d a b : ℝ × ℝ) : Set (ℝ × ℝ) :=
  (Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2) \
    (Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2)

/-- The open fluid shell is open in the Cartesian plane. -/
theorem isOpen_rectangularShellInterior (c d a b : ℝ × ℝ) :
    IsOpen (rectangularShellInterior c d a b) :=
  (isOpen_Ioo.prod isOpen_Ioo).sdiff (isClosed_Icc.prod isClosed_Icc)

/-- Divergence-free flux on the open annulus gives equal wall and outer
contour fluxes. The differentiability, continuity, and integrability
requirements are local to the fluid shell. -/
theorem flux_wall_eq_far_field_on_shell
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : ℝ × ℝ → E} {f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E} {c d a b : ℝ × ℝ}
    (h1 : c.1 < a.1) (h2 : a.1 < b.1) (h3 : b.1 < d.1)
    (h4 : c.2 < a.2) (h5 : a.2 < b.2) (h6 : b.2 < d.2)
    (Hcf : ContinuousOn f (rectangularShell c d a b))
    (Hcg : ContinuousOn g (rectangularShell c d a b))
    (Hdf : ∀ x ∈ rectangularShellInterior c d a b, HasFDerivAt f (f' x) x)
    (Hdg : ∀ x ∈ rectangularShellInterior c d a b, HasFDerivAt g (g' x) x)
    (Hi : MeasureTheory.IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1))
      (rectangularShell c d a b) MeasureTheory.volume)
    (hdiv : ∀ x ∈ rectangularShellInterior c d a b, f' x (1, 0) + g' x (0, 1) = 0) :
    (((∫ x in a.1..b.1, g (x, b.2)) - ∫ x in a.1..b.1, g (x, a.2)) +
        ∫ y in a.2..b.2, f (b.1, y)) - ∫ y in a.2..b.2, f (a.1, y) =
      (((∫ x in c.1..d.1, g (x, d.2)) - ∫ x in c.1..d.1, g (x, c.2)) +
        ∫ y in c.2..d.2, f (d.1, y)) - ∫ y in c.2..d.2, f (c.1, y) := by
  have hc2a2 : c.2 ≤ a.2 := le_of_lt h4
  have hb2d2 : b.2 ≤ d.2 := le_of_lt h6
  have hb2c2 : c.2 ≤ b.2 := le_trans (le_of_lt h4) (le_of_lt h5)
  have ha2d2 : a.2 ≤ d.2 := le_trans (le_of_lt h5) (le_of_lt h6)
  have ha1d1 : a.1 ≤ d.1 := le_trans (le_of_lt h2) (le_of_lt h3)
  have hb1c1 : c.1 ≤ b.1 := le_trans (le_of_lt h1) (le_of_lt h2)
  have hc1d1 : c.1 ≤ d.1 := le_trans hb1c1 (le_of_lt h3)
  have hc1a1 : c.1 ≤ a.1 := le_of_lt h1
  have ha1b1 : a.1 ≤ b.1 := le_of_lt h2
  have hb1d1 : b.1 ≤ d.1 := le_of_lt h3
  have hc1b1 : c.1 ≤ b.1 := le_trans hc1a1 ha1b1
  have ha2b2 : a.2 ≤ b.2 := le_of_lt h5
  have hc2b2 : c.2 ≤ b.2 := le_trans hc2a2 ha2b2
  have hOpenTop : Set.Ioo c.1 d.1 ×ˢ Set.Ioo b.2 d.2 ⊆
      rectangularShellInterior c d a b := by
    rintro z ⟨hxA, hyB⟩
    refine ⟨⟨hxA, ⟨lt_of_le_of_lt hb2c2 hyB.1, hyB.2⟩⟩, ?_⟩
    intro hmem
    exact absurd (Set.mem_prod.1 hmem).2 (Set.notMem_Icc_of_gt hyB.1)
  have hOpenBottom : Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 a.2 ⊆
      rectangularShellInterior c d a b := by
    rintro z ⟨hxA, hyB⟩
    refine ⟨⟨hxA, ⟨hyB.1, lt_of_lt_of_le hyB.2 ha2d2⟩⟩, ?_⟩
    intro hmem
    exact absurd (Set.mem_prod.1 hmem).2 (Set.notMem_Icc_of_lt hyB.2)
  have hOpenLeft : Set.Ioo c.1 a.1 ×ˢ Set.Ioo a.2 b.2 ⊆
      rectangularShellInterior c d a b := by
    rintro z ⟨hxA, hyB⟩
    refine ⟨⟨⟨hxA.1, lt_of_lt_of_le hxA.2 ha1d1⟩,
      ⟨lt_of_le_of_lt hc2a2 hyB.1, lt_of_lt_of_le hyB.2 hb2d2⟩⟩, ?_⟩
    intro hmem
    exact absurd (Set.mem_prod.1 hmem).1 (Set.notMem_Icc_of_lt hxA.2)
  have hOpenRight : Set.Ioo b.1 d.1 ×ˢ Set.Ioo a.2 b.2 ⊆
      rectangularShellInterior c d a b := by
    rintro z ⟨hxA, hyB⟩
    refine ⟨⟨⟨lt_of_le_of_lt hb1c1 hxA.1, hxA.2⟩,
      ⟨lt_of_le_of_lt hc2a2 hyB.1, lt_of_lt_of_le hyB.2 hb2d2⟩⟩, ?_⟩
    intro hmem
    exact absurd (Set.mem_prod.1 hmem).1 (Set.notMem_Icc_of_gt hxA.1)
  have hClosedTop : Set.Icc c.1 d.1 ×ˢ Set.Icc b.2 d.2 ⊆ rectangularShell c d a b := by
    rintro z ⟨hx, hy⟩
    refine ⟨⟨hx, ⟨hb2c2.trans hy.1, hy.2⟩⟩, ?_⟩
    exact fun hm => (not_lt_of_ge hy.1) hm.2.2
  have hClosedBottom : Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 a.2 ⊆ rectangularShell c d a b := by
    rintro z ⟨hx, hy⟩
    refine ⟨⟨hx, ⟨hy.1, hy.2.trans ha2d2⟩⟩, ?_⟩
    exact fun hm => (not_lt_of_ge hy.2) hm.2.1
  have hClosedLeft : Set.Icc c.1 a.1 ×ˢ Set.Icc a.2 b.2 ⊆ rectangularShell c d a b := by
    rintro z ⟨hx, hy⟩
    refine ⟨⟨⟨hx.1, hx.2.trans ha1d1⟩, ⟨hc2a2.trans hy.1, hy.2.trans hb2d2⟩⟩, ?_⟩
    exact fun hm => (not_lt_of_ge hx.2) hm.1.1
  have hClosedRight : Set.Icc b.1 d.1 ×ˢ Set.Icc a.2 b.2 ⊆ rectangularShell c d a b := by
    rintro z ⟨hx, hy⟩
    refine ⟨⟨⟨hb1c1.trans hx.1, hx.2⟩, ⟨hc2a2.trans hy.1, hy.2.trans hb2d2⟩⟩, ?_⟩
    exact fun hm => (not_lt_of_ge hx.1) hm.1.2
  have hTop := strip_boundary_integral_zero (c := (c.1, b.2)) (d := d)
    (Hcf.mono hClosedTop) (Hcg.mono hClosedTop) (fun z hz => Hdf z (hOpenTop hz))
    (fun z hz => Hdg z (hOpenTop hz)) (Hi.mono_set hClosedTop)
    le_rfl le_rfl le_rfl le_rfl hc1d1 hb2d2 (fun z hz => hdiv z (hOpenTop hz))
  have hBottom := strip_boundary_integral_zero (c := c) (d := (d.1, a.2))
    (Hcf.mono hClosedBottom) (Hcg.mono hClosedBottom) (fun z hz => Hdf z (hOpenBottom hz))
    (fun z hz => Hdg z (hOpenBottom hz)) (Hi.mono_set hClosedBottom)
    le_rfl le_rfl le_rfl le_rfl hc1d1 hc2a2 (fun z hz => hdiv z (hOpenBottom hz))
  have hLeft := strip_boundary_integral_zero (c := (c.1, a.2)) (d := (a.1, b.2))
    (Hcf.mono hClosedLeft) (Hcg.mono hClosedLeft) (fun z hz => Hdf z (hOpenLeft hz))
    (fun z hz => Hdg z (hOpenLeft hz)) (Hi.mono_set hClosedLeft)
    le_rfl le_rfl le_rfl le_rfl hc1a1 ha2b2 (fun z hz => hdiv z (hOpenLeft hz))
  have hRight := strip_boundary_integral_zero (c := (b.1, a.2)) (d := (d.1, b.2))
    (Hcf.mono hClosedRight) (Hcg.mono hClosedRight) (fun z hz => Hdf z (hOpenRight hz))
    (fun z hz => Hdg z (hOpenRight hz)) (Hi.mono_set hClosedRight)
    le_rfl le_rfl le_rfl le_rfl hb1d1 ha2b2 (fun z hz => hdiv z (hOpenRight hz))
  have hgint (t : ℝ) (ht : t ∈ Set.Icc c.2 d.2) (hside : t ≤ a.2 ∨ b.2 ≤ t)
      (p q : ℝ) (hp : c.1 ≤ p) (hpq : p ≤ q) (hq : q ≤ d.1) :
      IntervalIntegrable (fun x => g (x, t)) MeasureTheory.volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hpq]
    refine Hcg.comp (continuous_id.prodMk continuous_const).continuousOn ?_
    intro x hx
    refine ⟨⟨⟨hp.trans hx.1, hx.2.trans hq⟩, ht⟩, ?_⟩
    exact fun hm => hside.elim (fun ha => (not_lt_of_ge ha) hm.2.1)
      (fun hb => (not_lt_of_ge hb) hm.2.2)
  have hfint (r : ℝ) (hr : r ∈ Set.Icc c.1 d.1) (hside : r ≤ a.1 ∨ b.1 ≤ r)
      (p q : ℝ) (hp : c.2 ≤ p) (hpq : p ≤ q) (hq : q ≤ d.2) :
      IntervalIntegrable (fun y => f (r, y)) MeasureTheory.volume p q := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hpq]
    refine Hcf.comp (continuous_const.prodMk continuous_id).continuousOn ?_
    intro y hy
    refine ⟨⟨hr, ⟨hp.trans hy.1, hy.2.trans hq⟩⟩, ?_⟩
    exact fun hm => hside.elim (fun ha => (not_lt_of_ge ha) hm.1.1)
      (fun hb => (not_lt_of_ge hb) hm.1.2)
  have hb2 : b.2 ∈ Set.Icc c.2 d.2 := ⟨hb2c2, hb2d2⟩
  have ha2 : a.2 ∈ Set.Icc c.2 d.2 := ⟨hc2a2, ha2d2⟩
  have hd1 : d.1 ∈ Set.Icc c.1 d.1 := ⟨hc1d1, le_rfl⟩
  have hc1 : c.1 ∈ Set.Icc c.1 d.1 := ⟨le_rfl, hc1d1⟩
  have hgUpper := hgint b.2 hb2 (Or.inr le_rfl)
  have hgLower := hgint a.2 ha2 (Or.inl le_rfl)
  have hfRight := hfint d.1 hd1 (Or.inr hb1d1)
  have hfLeft := hfint c.1 hc1 (Or.inl hc1a1)
  have s1a := intervalIntegral.integral_add_adjacent_intervals
    (hgUpper c.1 a.1 le_rfl hc1a1 ha1d1) (hgUpper a.1 b.1 hc1a1 ha1b1 hb1d1)
  have s1b := intervalIntegral.integral_add_adjacent_intervals
    (hgUpper c.1 b.1 le_rfl hc1b1 hb1d1) (hgUpper b.1 d.1 hb1c1 hb1d1 le_rfl)
  have s2a := intervalIntegral.integral_add_adjacent_intervals
    (hgLower c.1 a.1 le_rfl hc1a1 ha1d1) (hgLower a.1 b.1 hc1a1 ha1b1 hb1d1)
  have s2b := intervalIntegral.integral_add_adjacent_intervals
    (hgLower c.1 b.1 le_rfl hc1b1 hb1d1) (hgLower b.1 d.1 hb1c1 hb1d1 le_rfl)
  have s3a := intervalIntegral.integral_add_adjacent_intervals
    (hfRight c.2 a.2 le_rfl hc2a2 ha2d2) (hfRight a.2 b.2 hc2a2 ha2b2 hb2d2)
  have s3b := intervalIntegral.integral_add_adjacent_intervals
    (hfRight c.2 b.2 le_rfl hc2b2 hb2d2) (hfRight b.2 d.2 hb2c2 hb2d2 le_rfl)
  have s4a := intervalIntegral.integral_add_adjacent_intervals
    (hfLeft c.2 a.2 le_rfl hc2a2 ha2d2) (hfLeft a.2 b.2 hc2a2 ha2b2 hb2d2)
  have s4b := intervalIntegral.integral_add_adjacent_intervals
    (hfLeft c.2 b.2 le_rfl hc2b2 hb2d2) (hfLeft b.2 d.2 hb2c2 hb2d2 le_rfl)
  -- The four strip identities say the total boundary flux of each strip
  -- vanishes; the eight adjacent-interval identities decompose the far-field
  -- edges into the strip edges.
  linear_combination (norm := abel_nf) -hTop - hBottom - hLeft - hRight + s1a + s1b - s2a - s2b
    + s3a + s3b - s4a - s4b

/-- **Wall force equals far-field force.** For a momentum flux `(f, g)` that is
continuous on the closed outer rectangle with corners `c ≤ d`, differentiable
with integrable divergence in its interior, and divergence-free in the fluid
region between the outer rectangle and the closed inner rectangle with corners
`a ≤ b`, the boundary integral of the flux around the inner rectangle equals
the boundary integral around the outer rectangle. This is the analytic content
of the statement in [Musser2019Superfoil], Eq. (5), that the force integral may
be taken around *any* path enclosing the airfoil: the wall contour can be
deformed out to the far field through a divergence-free fluid. -/
theorem flux_wall_eq_far_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : ℝ × ℝ → E} {f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E} {c d a b : ℝ × ℝ}
    (h1 : c.1 < a.1) (h2 : a.1 < b.1) (h3 : b.1 < d.1)
    (h4 : c.2 < a.2) (h5 : a.2 < b.2) (h6 : b.2 < d.2)
    (Hcf : ContinuousOn f (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2))
    (Hcg : ContinuousOn g (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2))
    (Hdf : ∀ x ∈ Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2, HasFDerivAt f (f' x) x)
    (Hdg : ∀ x ∈ Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2, HasFDerivAt g (g' x) x)
    (Hi : MeasureTheory.IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1))
      (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2) MeasureTheory.volume)
    (hdiv : ∀ x ∈ (Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2) \
        (Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2), f' x (1, 0) + g' x (0, 1) = 0) :
    (((∫ x in a.1..b.1, g (x, b.2)) - ∫ x in a.1..b.1, g (x, a.2)) +
        ∫ y in a.2..b.2, f (b.1, y)) - ∫ y in a.2..b.2, f (a.1, y) =
      (((∫ x in c.1..d.1, g (x, d.2)) - ∫ x in c.1..d.1, g (x, c.2)) +
        ∫ y in c.2..d.2, f (d.1, y)) - ∫ y in c.2..d.2, f (c.1, y) :=
  flux_wall_eq_far_field_on_shell h1 h2 h3 h4 h5 h6 (Hcf.mono Set.sdiff_subset)
    (Hcg.mono Set.sdiff_subset) (fun x hx => Hdf x hx.1) (fun x hx => Hdg x hx.1)
    (Hi.mono_set Set.sdiff_subset) hdiv

/-- **Path independence of the Eq. (5) contour force.** If the columns of a
stress tensor are continuous on the closed far-field rectangle, `C¹` with
integrable divergence in its interior, and the momentum flux of each force
component is divergence-free in the fluid region between the wall rectangle
`a, b` and the far-field rectangle `c, d`, then the force on the airfoil
computed on the wall equals the force computed in the far field. The
divergence-free premise encodes steady momentum conservation of the Madelung
equations outside the airfoil. -/
theorem stress_force_wall_eq_far_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ × ℝ → Fin 2 → Fin 2 → E} {Tf Tg : ℝ × ℝ → ℝ × ℝ →L[ℝ] E}
    {c d a b : ℝ × ℝ} {k : Fin 2}
    (h1 : c.1 < a.1) (h2 : a.1 < b.1) (h3 : b.1 < d.1)
    (h4 : c.2 < a.2) (h5 : a.2 < b.2) (h6 : b.2 < d.2)
    (Hcf : ContinuousOn (fun x => T x (0 : Fin 2) k) (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2))
    (Hcg : ContinuousOn (fun x => T x (1 : Fin 2) k) (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2))
    (Hdf : ∀ x ∈ Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2,
      HasFDerivAt (fun y => T y (0 : Fin 2) k) (Tf x) x)
    (Hdg : ∀ x ∈ Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2,
      HasFDerivAt (fun y => T y (1 : Fin 2) k) (Tg x) x)
    (Hi : MeasureTheory.IntegrableOn (fun x => Tf x (1, 0) + Tg x (0, 1))
      (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2) MeasureTheory.volume)
    (hdiv : ∀ x ∈ (Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2) \
        (Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2), Tf x (1, 0) + Tg x (0, 1) = 0) :
    rectangleForce T k a b = rectangleForce T k c d :=
  flux_wall_eq_far_field h1 h2 h3 h4 h5 h6 Hcf Hcg Hdf Hdg Hi hdiv

/-- **Impulse form of the contour force.** When the far-field contour force is
carried by an advected point vortex of circulation `-Γ_bound` moving with
streamwise speed `U` (hypothesis `hfar`: the far-field force is the derivative
of the vortex impulse along the trajectory), the wall force on the airfoil
equals exactly the ideal Kutta--Joukowski lift `-ρ U Γ_bound` of the locked
impulse module. This composes the path independence of the Eq. (5) integral
with `Qatlib.Papers.SuperfoilLift19.LiftForce.impulse_derivative_lift`. -/
theorem wall_force_eq_ideal_lift
    {T : ℝ × ℝ → Fin 2 → Fin 2 → ℝ} {Tf Tg : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ}
    {c d a b : ℝ × ℝ} {k : Fin 2}
    (h1 : c.1 < a.1) (h2 : a.1 < b.1) (h3 : b.1 < d.1)
    (h4 : c.2 < a.2) (h5 : a.2 < b.2) (h6 : b.2 < d.2)
    (Hcf : ContinuousOn (fun x => T x (0 : Fin 2) k) (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2))
    (Hcg : ContinuousOn (fun x => T x (1 : Fin 2) k) (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2))
    (Hdf : ∀ x ∈ Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2,
      HasFDerivAt (fun y => T y (0 : Fin 2) k) (Tf x) x)
    (Hdg : ∀ x ∈ Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2,
      HasFDerivAt (fun y => T y (1 : Fin 2) k) (Tg x) x)
    (Hi : MeasureTheory.IntegrableOn (fun x => Tf x (1, 0) + Tg x (0, 1))
      (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2) MeasureTheory.volume)
    (hdiv : ∀ x ∈ (Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2) \
        (Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2), Tf x (1, 0) + Tg x (0, 1) = 0)
    (density boundCirculation speed t : ℝ) (position : ℝ → ℝ)
    (hpos : HasDerivAt position speed t)
    (hfar : rectangleForce T k c d =
      deriv (fun s => vortexImpulse density (-boundCirculation) (position s)) t) :
    rectangleForce T k a b = -idealLift density speed boundCirculation := by
  rw [stress_force_wall_eq_far_field h1 h2 h3 h4 h5 h6 Hcf Hcg Hdf Hdg Hi hdiv, hfar,
    impulse_derivative_lift density boundCirculation t speed position hpos]

/-- The stress-to-vortex bridge has a nondegenerate form when the density,
streamwise speed, and bound circulation are all nonzero.  In that regime the
far-field impulse derivative supplies both the exact Kutta--Joukowski value
and a nonzero wall-force witness. -/
theorem wall_force_eq_ideal_lift_nonzero
    {T : ℝ × ℝ → Fin 2 → Fin 2 → ℝ} {Tf Tg : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ}
    {c d a b : ℝ × ℝ} {k : Fin 2}
    (h1 : c.1 < a.1) (h2 : a.1 < b.1) (h3 : b.1 < d.1)
    (h4 : c.2 < a.2) (h5 : a.2 < b.2) (h6 : b.2 < d.2)
    (Hcf : ContinuousOn (fun x => T x (0 : Fin 2) k) (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2))
    (Hcg : ContinuousOn (fun x => T x (1 : Fin 2) k) (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2))
    (Hdf : ∀ x ∈ Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2,
      HasFDerivAt (fun y => T y (0 : Fin 2) k) (Tf x) x)
    (Hdg : ∀ x ∈ Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2,
      HasFDerivAt (fun y => T y (1 : Fin 2) k) (Tg x) x)
    (Hi : MeasureTheory.IntegrableOn (fun x => Tf x (1, 0) + Tg x (0, 1))
      (Set.Icc c.1 d.1 ×ˢ Set.Icc c.2 d.2) MeasureTheory.volume)
    (hdiv : ∀ x ∈ (Set.Ioo c.1 d.1 ×ˢ Set.Ioo c.2 d.2) \
        (Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2), Tf x (1, 0) + Tg x (0, 1) = 0)
    {density speed boundCirculation t : ℝ} {position : ℝ → ℝ}
    (hdensity : density ≠ 0) (hspeed : speed ≠ 0)
    (hcirculation : boundCirculation ≠ 0)
    (hpos : HasDerivAt position speed t)
    (hfar : rectangleForce T k c d =
      deriv (fun s => vortexImpulse density (-boundCirculation) (position s)) t) :
    rectangleForce T k a b = -idealLift density speed boundCirculation ∧
      rectangleForce T k a b ≠ 0 := by
  have hforce := wall_force_eq_ideal_lift h1 h2 h3 h4 h5 h6 Hcf Hcg Hdf Hdg Hi hdiv
    density boundCirculation speed t position hpos hfar
  refine ⟨hforce, ?_⟩
  rw [hforce]
  unfold idealLift
  have hdenNeg : -density ≠ 0 := neg_ne_zero.mpr hdensity
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hdenNeg hspeed) hcirculation)

/-- **Necessity of the divergence-free premise.** For the linear field with
`f (x, y) = x` and `g = 0`, whose divergence is the constant `1`, the contour
force on the inner unit square is `1` (its area) while the contour force on the
outer square `[-1, 2]²` is `9` (its area): without momentum conservation in
the fluid region the Eq. (5) integral is not path independent. -/
theorem flux_counterexample_of_nonzero_divergence :
    rectangleForce (fun x j _ => x.1 * (1 - (j.val : ℝ))) (1 : Fin 2)
        (0, 0) (1, 1) = 1 ∧
      rectangleForce (fun x j _ => x.1 * (1 - (j.val : ℝ))) (1 : Fin 2)
        (-1, -1) (2, 2) = 9 := by
  constructor
  · unfold rectangleForce
    simp only [Fin.val_one, Fin.val_zero, Nat.cast_one, Nat.cast_zero, sub_self, sub_zero,
      mul_one, mul_zero, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    norm_num
  · unfold rectangleForce
    simp only [Fin.val_one, Fin.val_zero, Nat.cast_one, Nat.cast_zero, sub_self, sub_zero,
      mul_one, mul_zero, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    norm_num

end Qatlib.Papers.SuperfoilLift19.LiftForce
