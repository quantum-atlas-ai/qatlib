/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Grid-level relativistic energy relation (Eqs. (81)–(82))

Source: J. Yepez, *Quantum lattice gas model of Dirac particles in 1+1 dimensions*,
arXiv:1307.3595v1 (2013), Sec. IV B, Eqs. (80)–(82).

The paper derives the lattice momentum ansatz (Eq. (80))

  `p_z c τ / ℏ = √(1 - (m c² τ / ℏ)²) · sin(ℓ k_z)`,

squares it to obtain (Eq. (81))

  `p² c² = [ℏ²/τ² - (m c²)²] · sin²(ℓ k_z)`,

and then adds `(m c²)²` to both sides to reach the *novel grid-level form* of the
relativistic energy relation (Eq. (82)).  Eq. (82) as printed in the text reads
`E² = (ℏ²/τ²) sin² ℓk_z + mc² cos² ℓk_z`; the second term must be `(m c²)² cos² ℓk_z`
(otherwise (81) + `(m c²)²` does not reproduce it, and the dimensions do not match).
We formalize the dimensionally correct identity and record the typographical
discrepancy in the module header above.

All results here are fully proved real algebra.
-/

set_option autoImplicit false

namespace Qatlib.Papers.DiracLatGas13.MainResults

noncomputable section

/-- **Eq. (81).** After squaring the lattice-momentum ansatz (80), the momentum is
`p² c² = [ℏ²/τ² - (m c²)²] sin²(ℓ k_z)`. -/
def GridMomentumSq (p m c ℏ τ ℓ k : ℝ) : Prop :=
  p ^ 2 * c ^ 2 = (ℏ ^ 2 / τ ^ 2 - (m * c ^ 2) ^ 2) * Real.sin (ℓ * k) ^ 2

/-- **Eq. (82).** The grid-level form of the relativistic energy relation,
`E² = (ℏ²/τ²) sin²(ℓ k_z) + (m c²)² cos²(ℓ k_z)`. (The printed paper drops the
square on `mc²` in the cosine term; see the module header.) -/
def GridEnergySq (E m c ℏ τ ℓ k : ℝ) : Prop :=
  E ^ 2 = ℏ ^ 2 / τ ^ 2 * Real.sin (ℓ * k) ^ 2
    + (m * c ^ 2) ^ 2 * Real.cos (ℓ * k) ^ 2

/-- **Eqs. (81) ⟹ (82).** Adding `(m c²)²` to both sides of the squared momentum
relation (81), and using `sin² + cos² = 1`, gives the grid-level energy relation.
This is the content of the passage between (81) and (82) on p. 13. -/
theorem gridEnergy_of_momentum
    (p E m c ℏ τ ℓ k : ℝ)
    (h81 : GridMomentumSq p m c ℏ τ ℓ k)
    (hE : E ^ 2 = p ^ 2 * c ^ 2 + (m * c ^ 2) ^ 2) :
    GridEnergySq E m c ℏ τ ℓ k := by
  have htrig : Real.sin (ℓ * k) ^ 2 + Real.cos (ℓ * k) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (ℓ * k)
  unfold GridMomentumSq at h81
  unfold GridEnergySq
  nlinarith [h81, hE, htrig]

/-- **Eq. (81) from the ansatz (80).** Squaring the lattice-momentum ansatz and
multiplying by `ℏ²/τ²` recovers (81), assuming the square root is real
(`0 ≤ 1 - (m c² τ / ℏ)²`). -/
theorem momentumSq_of_ansatz
    (p m c ℏ τ ℓ k : ℝ) (hτ : τ ≠ 0) (hℏ : ℏ ≠ 0)
    (hpos : 0 ≤ 1 - (m * c ^ 2 * τ / ℏ) ^ 2)
    (h80 : p * c * τ / ℏ
      = Real.sqrt (1 - (m * c ^ 2 * τ / ℏ) ^ 2) * Real.sin (ℓ * k)) :
    GridMomentumSq p m c ℏ τ ℓ k := by
  unfold GridMomentumSq
  have hsq : (p * c * τ / ℏ) ^ 2
      = (1 - (m * c ^ 2 * τ / ℏ) ^ 2) * Real.sin (ℓ * k) ^ 2 := by
    rw [h80, mul_pow, Real.sq_sqrt hpos]
  have key : (p * c * τ / ℏ) ^ 2 * (ℏ ^ 2 / τ ^ 2)
      = (1 - (m * c ^ 2 * τ / ℏ) ^ 2) * Real.sin (ℓ * k) ^ 2 * (ℏ ^ 2 / τ ^ 2) := by
    rw [hsq]
  have hcoef : (p * c * τ / ℏ) ^ 2 * (ℏ ^ 2 / τ ^ 2) = p ^ 2 * c ^ 2 := by
    field_simp <;> ring
  have hrhs : (1 - (m * c ^ 2 * τ / ℏ) ^ 2) * Real.sin (ℓ * k) ^ 2 * (ℏ ^ 2 / τ ^ 2)
      = (ℏ ^ 2 / τ ^ 2 - (m * c ^ 2) ^ 2) * Real.sin (ℓ * k) ^ 2 := by
    field_simp <;> ring
  rw [← hcoef, key, hrhs]

end

end Qatlib.Papers.DiracLatGas13.MainResults
