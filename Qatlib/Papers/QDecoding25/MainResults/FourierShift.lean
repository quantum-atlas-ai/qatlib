/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.Fourier.ZMod

set_option backward.isDefEq.respectTransparency false

/-! Fourier shift duality for
"The Quantum Decoding Problem: Tight Achievability Bounds and
Application to Regev's Reduction" (arXiv:2509.24796v2, 2025).

Lemma 3 of the paper: for the code state
`|ψ_c⟩ = ∑_e f(e)|c + e⟩` (a translate of the error amplitude
function `f` by the codeword `c`), the Fourier transform satisfies
`ψ̂_c(y) = f̂(y)·χ_c(y)` — translation becomes character modulation.

Here `G = (Fin n → ZMod q)` carries the standard additive character
`χ_y(x) = stdAddChar (∑ i, y i * x i)` (for prime `q` the absolute
trace in the paper's Eq. is the identity), and the paper's transform
`f̂(y) = q^{-n/2} ∑_x χ_y(x) f(x)` is realized as `qdft`.

- `chi_add_right` : `χ_y(a + b) = χ_y(a)·χ_y(b)`.
- `chi_comm` : symmetry `χ_y(x) = χ_x(y)`.
- `qdft_shift` : **Lemma 3**, `qdft (f ∘ (· − c)) y = χ_c(y) · qdft f y`.

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false

namespace Qatlib.Papers.QDecoding25.MainResults.FourierShift

variable {q n : ℕ} [NeZero q]

/-- The standard additive character `χ_y(x)` on `G = (Fin n → ZMod q)`,
matching the paper's `e^{2iπ·tr(x·y)/p}` (for prime `q`, `tr = id`). -/
noncomputable def chi (y x : Fin n → ZMod q) : ℂ :=
  ZMod.stdAddChar (∑ i, y i * x i)

/-- Additivity in the second argument: `χ_y(a + b) = χ_y(a) * χ_y(b)`. -/
theorem chi_add_right (y a b : Fin n → ZMod q) :
    chi y (a + b) = chi y a * chi y b := by
  simp only [chi, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  exact AddChar.map_add_eq_mul _ _ _

/-- Symmetry of the character: `χ_y(x) = χ_x(y)`. -/
theorem chi_comm (y x : Fin n → ZMod q) : chi y x = chi x y := by
  simp only [chi]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm (y i) (x i)

/-- The paper's Fourier transform
`f̂(y) = q^{-n/2} ∑_x χ_y(x) f(x)`. -/
noncomputable def qdft (f : (Fin n → ZMod q) → ℂ) (y : Fin n → ZMod q) : ℂ :=
  (Real.sqrt ((q : ℝ) ^ n))⁻¹ * ∑ x, chi y x * f x

/-- **Lemma 3 (Eq. (7)), translation–modulation duality**: the Fourier
transform of the translate `ψ_c(x) = f(x − c)` (the code state of the
paper) is the modulated transform `f̂(y)·χ_c(y)`. -/
theorem qdft_shift (f : (Fin n → ZMod q) → ℂ) (c y : Fin n → ZMod q) :
    qdft (fun x => f (x - c)) y = qdft f y * chi c y := by
  have h1 : ∑ x, chi y x * f (x - c) = ∑ w, chi y (w + c) * f w :=
    Fintype.sum_equiv (Equiv.subRight c) _ _
      (fun x => by simp only [Equiv.subRight_apply, sub_add_cancel])
  have hterm : ∀ w, chi y (w + c) * f w = chi y c * (chi y w * f w) := by
    intro w
    rw [chi_add_right y w c]
    ring
  rw [qdft, qdft, h1, Finset.sum_congr rfl (fun w _ => hterm w), ← Finset.mul_sum,
    chi_comm c y]
  ring

end Qatlib.Papers.QDecoding25.MainResults.FourierShift
