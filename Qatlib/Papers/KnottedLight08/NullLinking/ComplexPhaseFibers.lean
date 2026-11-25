/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Complex.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Projective Hopf fibers as phase circles

[IrvineBouwmeester2008KnottedLight], pp. 717–718,
[DOI](https://doi.org/10.1038/nphys1056).
The homogeneous coordinate of a nonzero complex pair identifies a projective
point even where its affine ratio has a pole. Restricted to the unit
three-sphere, each fiber is exactly the orbit of simultaneous multiplication
by a unit complex number.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

/-- The projective fiber through a complex pair, restricted to the unit
three-sphere. The cross-product equation is homogeneous in both pairs. -/
def unitHopfFiber (p : ℂ × ℂ) : Set (ℂ × ℂ) :=
  {q | Complex.normSq q.1 + Complex.normSq q.2 = 1 ∧ q.1 * p.2 = q.2 * p.1}

/-- Simultaneous multiplication of both coordinates by a complex phase. -/
def phaseOrbit (p : ℂ × ℂ) (u : ℂ) : ℂ × ℂ := (u * p.1, u * p.2)

/-- Two unit pairs represent the same projective point exactly when they
differ by simultaneous multiplication by a unit complex number. This
includes the fiber with zero second coordinate. -/
theorem mem_unitHopfFiber_iff (p q : ℂ × ℂ)
    (hp : Complex.normSq p.1 + Complex.normSq p.2 = 1) :
    q ∈ unitHopfFiber p ↔ ∃ u : ℂ, Complex.normSq u = 1 ∧ phaseOrbit p u = q := by
  constructor
  · rintro ⟨hq, hcross⟩
    have hm : ∃ u : ℂ, phaseOrbit p u = q := by
      by_cases h₁ : p.1 = 0
      · have h₂ : p.2 ≠ 0 := by
          intro hz
          simp [h₁, hz] at hp
        have hq₁ : q.1 = 0 := by
          apply (mul_eq_zero.mp ?_).resolve_right h₂
          simpa [h₁] using hcross
        refine ⟨q.2 / p.2, Prod.ext ?_ ?_⟩
        · simp [phaseOrbit, h₁, hq₁]
        · exact div_mul_cancel₀ _ h₂
      · refine ⟨q.1 / p.1, Prod.ext (div_mul_cancel₀ _ h₁) ?_⟩
        change (q.1 / p.1) * p.2 = q.2
        rw [div_mul_eq_mul_div, div_eq_iff h₁]
        exact hcross
    obtain ⟨u, hu⟩ := hm
    refine ⟨u, ?_, hu⟩
    rw [← hu] at hq
    simpa only [phaseOrbit, Complex.normSq_mul, ← mul_add, hp, mul_one] using hq
  · rintro ⟨u, hu, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [phaseOrbit, Complex.normSq_mul, hu, one_mul, hp]
    · change (u * p.1) * p.2 = (u * p.2) * p.1
      ring

/-- For a unit pair, the phase parametrization is injective. -/
theorem phaseOrbit_injective (p : ℂ × ℂ)
    (hp : Complex.normSq p.1 + Complex.normSq p.2 = 1) :
    Function.Injective (phaseOrbit p) := by
  intro u v h
  by_cases h₁ : p.1 = 0
  · have h₂ : p.2 ≠ 0 := by
      intro hz
      simp [h₁, hz] at hp
    exact mul_right_cancel₀ h₂ (congrArg Prod.snd h)
  · exact mul_right_cancel₀ h₁ (congrArg Prod.fst h)

/-- The entire projective fiber of a unit pair is the continuous injective
image of the complex unit circle. -/
theorem unitHopfFiber_eq_phase_image (p : ℂ × ℂ)
    (hp : Complex.normSq p.1 + Complex.normSq p.2 = 1) :
    unitHopfFiber p = phaseOrbit p '' Metric.sphere 0 1 := by
  ext q
  rw [mem_unitHopfFiber_iff p q hp]
  have hunit (u : ℂ) : Complex.normSq u = 1 ↔ u ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [Complex.normSq_eq_norm_sq, Metric.mem_sphere, dist_zero_right]
    constructor
    · intro h
      nlinarith [norm_nonneg u]
    · intro h
      rw [h, one_pow]
  simp only [Set.mem_image, hunit]

/-- Every Hopf fiber in the unit three-sphere is compact, including the
projective fiber at infinity in either affine chart. -/
theorem unitHopfFiber_isCompact (p : ℂ × ℂ)
    (hp : Complex.normSq p.1 + Complex.normSq p.2 = 1) :
    IsCompact (unitHopfFiber p) := by
  rw [unitHopfFiber_eq_phase_image p hp]
  exact (isCompact_sphere 0 1).image
    ((continuous_id.mul continuous_const).prodMk (continuous_id.mul continuous_const))

/-- Each unit Hopf fiber is closed in the complex coordinate space. -/
theorem unitHopfFiber_isClosed (p : ℂ × ℂ)
    (hp : Complex.normSq p.1 + Complex.normSq p.2 = 1) :
    IsClosed (unitHopfFiber p) :=
  (unitHopfFiber_isCompact p hp).isClosed

end Qatlib.Papers.KnottedLight08.NullLinking
