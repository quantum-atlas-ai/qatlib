/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BivarHidPoly13.MainResults.HiddenPolyModel
import Mathlib.Tactic.LinearCombination

set_option backward.isDefEq.respectTransparency false

/-!
# BivarHidPoly13 — Theorem 1 (c001)

Fixed source: arXiv:1305.1543v2 (9 Oct 2013), Theorem 1, p.2–3, with the
proof route of Section 2.1 (p.3–6) and Section 2.3 (p.8).

Theorem 1 (p.2–3). *Let `D` be a constant and let `f(x) = Σ_{s=1}^{D} ν_s x^s ∈
F[x]`. Then there is a quantum algorithm which, given `O(1)` states of the form
`Σ_{x∈F} |w + f(x)⟩|x⟩` for various and unknown `w ∈ F`, determines the hidden
coefficients `ν_1, …, ν_D` efficiently.*

The paper's route (Section 2.1) is **phase linearization**: apply the field QFT
to a level-set superposition, sample `y`, take three such states `(y_1,y_2,y_3)`,
append a uniform register `x`, shift the three registers by `-δ_i x`, and choose
`δ_1,δ_2,δ_3` with `y_1δ_1^2 + y_2δ_2^2 + y_3δ_3^2 = 0` so that the composed
exponent becomes **linear** in `x`.  Measuring the first three registers yields
a linear constraint `g = ν c + μ d` on the coefficients; two such constraints
with `c_1d_2 ≠ c_2d_1` determine `(ν,μ)`.

Formalized here:

* `phaseLinearization_expansion` — the algebraic identity behind the `Q = 0`
  elimination (Section 2.1, p.5, the displayed equations after line 235);
* `phaseLinearization_linear_in_x` — with `Q = 0` the exponent is affine in `x`;
* `twoConstraints_determine` — two independent linear constraints determine the
  two unknowns (Section 2.1, p.6; Section 2.4, Eq. (7));
* `theorem1_recovery` — the Theorem 1 conclusion at the level of the exact
  mathematical kernel: the level-set data determine and yield `ν`.

Modeled residue (not discharged here): the quantum circuit that obtains the
sampled `y_i`, finds the nontrivial `δ`-solution in `polylog(|F|)` time
(Las Vegas, [6]/[7]), and runs the QFT; the "efficiently" claim needs the gate
model of `UniformBqp.FiniteGateWord`.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset

namespace Qatlib.Papers.BivarHidPoly13.MainResults

section PhaseLinearization

variable {F : Type*} [Field F]

/-- Section 2.1, p.5: the composed exponent `e'(x_1,x_2,x_3)` after the shift
`x_i ↦ x_i + δ_i x` equals `ν a + μ b + (ν c + μ d) x + μ Q x²` with

`a = y_1x_1 + y_2x_2 + y_3x_3`, `b = y_1x_1² + y_2x_2² + y_3x_3²`,
`c = y_1δ_1 + y_2δ_2 + y_3δ_3`, `d = 2(y_1δ_1x_1 + y_2δ_2x_2 + y_3δ_3x_3)`,
`Q = y_1δ_1² + y_2δ_2² + y_3δ_3²`.

This is the expansion of the source display
`e'(x_1,x_2,x_3) = e(x_1+δ_1x, x_2+δ_2x, x_3+δ_3x)`. -/
theorem phaseLinearization_expansion (ν μ : F)
    (y₁ y₂ y₃ δ₁ δ₂ δ₃ x₁ x₂ x₃ x : F) :
    ν * (y₁ * (x₁ + δ₁ * x) + y₂ * (x₂ + δ₂ * x) + y₃ * (x₃ + δ₃ * x))
        + μ * (y₁ * (x₁ + δ₁ * x) ^ 2 + y₂ * (x₂ + δ₂ * x) ^ 2
               + y₃ * (x₃ + δ₃ * x) ^ 2)
      = ν * (y₁ * x₁ + y₂ * x₂ + y₃ * x₃)
        + μ * (y₁ * x₁ ^ 2 + y₂ * x₂ ^ 2 + y₃ * x₃ ^ 2)
        + (ν * (y₁ * δ₁ + y₂ * δ₂ + y₃ * δ₃)
            + μ * (2 * (y₁ * δ₁ * x₁ + y₂ * δ₂ * x₂ + y₃ * δ₃ * x₃))) * x
        + μ * (y₁ * δ₁ ^ 2 + y₂ * δ₂ ^ 2 + y₃ * δ₃ ^ 2) * x ^ 2 := by
  ring

/-- **The `Q = 0` elimination.**  If the phase-linearization solution satisfies
`y_1δ_1^2 + y_2δ_2^2 + y_3δ_3^2 = 0` (Section 2.1, p.5), the composed exponent
has no `x²` term, hence is affine in `x` for every `x_1,x_2,x_3`: this is what
makes the inverse QFT return a single linear combination `ν c + μ d`. -/
theorem phaseLinearization_linear_in_x (ν μ : F)
    (y₁ y₂ y₃ δ₁ δ₂ δ₃ x₁ x₂ x₃ : F)
    (hQ : y₁ * δ₁ ^ 2 + y₂ * δ₂ ^ 2 + y₃ * δ₃ ^ 2 = 0) :
    ∀ x : F,
      ν * (y₁ * (x₁ + δ₁ * x) + y₂ * (x₂ + δ₂ * x) + y₃ * (x₃ + δ₃ * x))
          + μ * (y₁ * (x₁ + δ₁ * x) ^ 2 + y₂ * (x₂ + δ₂ * x) ^ 2
                 + y₃ * (x₃ + δ₃ * x) ^ 2)
        = ν * (y₁ * x₁ + y₂ * x₂ + y₃ * x₃)
          + μ * (y₁ * x₁ ^ 2 + y₂ * x₂ ^ 2 + y₃ * x₃ ^ 2)
          + (ν * (y₁ * δ₁ + y₂ * δ₂ + y₃ * δ₃)
              + μ * (2 * (y₁ * δ₁ * x₁ + y₂ * δ₂ * x₂ + y₃ * δ₃ * x₃))) * x := by
  intro x
  have h := phaseLinearization_expansion ν μ y₁ y₂ y₃ δ₁ δ₂ δ₃ x₁ x₂ x₃ x
  rw [h, hQ]
  ring

/-- Section 2.1, p.6: two linear constraints `g_i = ν c_i + μ d_i` (`i = 1,2`)
associate a unique pair `(ν, μ)` when the coefficient determinant
`c_1 d_2 - c_2 d_1` is nonzero.  These are the constraints obtained from the
inverse QFT after phase linearization. -/
theorem twoConstraints_determine {ν μ ν' μ' c₁ c₂ d₁ d₂ g₁ g₂ : F}
    (hdet : c₁ * d₂ - c₂ * d₁ ≠ 0)
    (h1 : ν * c₁ + μ * d₁ = g₁) (h1' : ν' * c₁ + μ' * d₁ = g₁)
    (h2 : ν * c₂ + μ * d₂ = g₂) (h2' : ν' * c₂ + μ' * d₂ = g₂) :
    ν = ν' ∧ μ = μ' := by
  have e1 : (ν - ν') * c₁ + (μ - μ') * d₁ = 0 := by
    linear_combination h1 - h1'
  have e2 : (ν - ν') * c₂ + (μ - μ') * d₂ = 0 := by
    linear_combination h2 - h2'
  have hν : (ν - ν') * (c₁ * d₂ - c₂ * d₁) = 0 := by
    linear_combination e1 * d₂ - e2 * d₁
  have hμ : (μ - μ') * (d₁ * c₂ - d₂ * c₁) = 0 := by
    linear_combination e1 * c₂ - e2 * c₁
  have hν0 : ν - ν' = 0 := by
    rcases mul_eq_zero.mp hν with h | h
    · exact h
    · exact absurd h hdet
  have hμ0 : μ - μ' = 0 := by
    rcases mul_eq_zero.mp hμ with h | h
    · exact h
    · apply absurd h
      intro hc
      apply hdet
      linear_combination -hc
  exact ⟨sub_eq_zero.mp hν0, sub_eq_zero.mp hμ0⟩

end PhaseLinearization

variable {F : Type*} [Field F]

/-- **Theorem 1 (c001).**  Given a level-set superposition
`Σ_x |w + f(x)⟩|x⟩` of the hidden polynomial `f(x) = Σ_{s=1}^{D} ν_s x^s`
(with zero constant term), the coefficients `ν_1, …, ν_D` are determined:
there is a recovery map from the amplitude pattern of the state that returns
`ν` on every promised instance.  The hypothesis `D < |F|` is the paper's
standing constant-degree regime and makes the polynomial identifiable.

Fixed arXiv:1305.1543v2, Theorem 1, p.2–3. -/
theorem theorem1_recovery [Fintype F] [DecidableEq F]
    (D : ℕ) (hD : D < Fintype.card F) :
    ∃ recover : (F → F) → (Fin D → F),
      ∀ (ν : Fin D → F) (w : F),
        recover (levelSetAmplitude (hiddenPoly D ν) w) = ν :=
  ⟨recoverFromLevelSet D, recoverFromLevelSet_spec D hD⟩

end Qatlib.Papers.BivarHidPoly13.MainResults
