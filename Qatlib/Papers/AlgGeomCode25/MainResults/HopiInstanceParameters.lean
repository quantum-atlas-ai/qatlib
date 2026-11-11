/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# HOPI instance parameters (Hermitian codes)

Source: `arXiv:2510.06603v1`, Andi Gu and Stephen P. Jordan, "Algebraic Geometry
Codes and Decoded Quantum Interferometry", Section 4 (page 11).

The paper fixes the Hermitian construction with parameter `t`: the block length is
`n = q^3`, the alphabet is `𝔽_{q^2}`, the genus is `g = q(q-1)/2`, and the dual of
the Hermitian code `C_t` is the Hermitian code with parameter
`t' = n + 2g - 2 - t`, whose minimum distance `d^⊥` is the decoding radius input of
Theorem 1. Decoding is assumed to correct `ℓ = ⌊(d^⊥ - 1)/2⌋` errors, and the paper
uses the guarantee `d^⊥ ≥ t + 2 - 2g` for a Hermitian code `C_t`.

This module formalizes only that arithmetic of the parameters. It contains no
statement about the codes themselves, about `L_t`, or about decoders; those are not
rebuilt here, and the block length, genus and dual-distance guarantee are taken as
the paper's own hypotheses.
-/

set_option autoImplicit false

namespace Qatlib.Papers.AlgGeomCode25.MainResults

/-- The number of constraints of a HOPI instance: `n = q^3` (Section 4, page 11). -/
def blockLength (q : ℕ) : ℕ := q ^ 3

/-- Genus of the Hermitian curve over `𝔽_{q^2}`: `g = q(q-1)/2` (Section 4, page 11). -/
def hermitianGenus (q : ℕ) : ℕ := q * (q - 1) / 2

/-- The genus relation used by the paper: `2g = q(q-1)`. -/
theorem two_mul_hermitianGenus (q : ℕ) : 2 * hermitianGenus q = q * (q - 1) := by
  unfold hermitianGenus
  have h2 : 2 ∣ q * (q - 1) := by
    rcases Nat.even_or_odd q with hq | ⟨k, hk⟩
    · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp hq) (q - 1)
    · exact Dvd.dvd.mul_left ⟨k, by omega⟩ q
  exact Nat.mul_div_cancel' h2

/-- The dual Hermitian code parameter `t' = n + 2g - 2 - t` (Section 4, page 11). -/
def dualParameter (n g t : ℕ) : ℕ := n + 2 * g - 2 - t

/-- Duality of Hermitian codes is an involution on the parameter, on the range where
the paper's formula is meaningful: `t' = n + 2g - 2 - t` maps back to `t`. -/
theorem dualParameter_involutive {n g t : ℕ} (ht : t ≤ n + 2 * g - 2) :
    dualParameter n g (dualParameter n g t) = t := by
  unfold dualParameter
  omega

/-- The dual parameter in the explicit form quoted in Theorem 5 of the appendix:
`t' = q^3 + q(q-1) - 2 - t` for the Hermitian instance. -/
theorem dualParameter_eq_explicit (q t : ℕ) :
    dualParameter (blockLength q) (hermitianGenus q) t
      = blockLength q + q * (q - 1) - 2 - t := by
  unfold dualParameter blockLength
  have := two_mul_hermitianGenus q
  omega

/-- The decoding radius `ℓ = ⌊(d - 1)/2⌋` attached to a code of minimum distance `d`
(Section 4, page 11). -/
def decodingRadius (d : ℕ) : ℕ := (d - 1) / 2

/-- The decoding radius never exceeds the minimum distance. -/
theorem decodingRadius_le_self (d : ℕ) : decodingRadius d ≤ d := by
  unfold decodingRadius
  have := Nat.div_le_self (d - 1) 2
  omega

/-- The decoding radius is at most half the minimum distance. -/
theorem two_mul_decodingRadius_le (d : ℕ) : 2 * decodingRadius d ≤ d := by
  unfold decodingRadius
  have := Nat.div_mul_le_self (d - 1) 2
  omega

/-- The paper's decoding guarantee `2ℓ + 1 ≤ d^⊥`: a decoder at the floor radius
corrects `ℓ` errors with one unit of distance to spare whenever `d^⊥ ≥ 1`. -/
theorem two_mul_decodingRadius_add_one_le {d : ℕ} (hd : 1 ≤ d) :
    2 * decodingRadius d + 1 ≤ d := by
  unfold decodingRadius
  have := Nat.div_mul_le_self (d - 1) 2
  omega

/-- The decoding radius is monotone in the minimum distance. -/
theorem decodingRadius_monotone {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    decodingRadius d₁ ≤ decodingRadius d₂ := by
  unfold decodingRadius
  exact Nat.div_le_div_right (Nat.sub_le_sub_right h 1)

/-- The dual-distance guarantee `d^⊥ ≥ t + 2 - 2g` of a Hermitian code `C_t` yields the
explicit decoding radius `⌊(t + 1 - 2g)/2⌋`; this is the "recall that for a Hermitian
code `C_t`, `d^⊥ ≥ t + 2 - 2g`" step of Theorem 1. The statement holds for every `t`,
`g`, `d` because natural-number subtraction is truncated. -/
theorem decodingRadius_ge_of_dualDistance {t g d : ℕ}
    (hd : t + 2 - 2 * g ≤ d) : (t + 1 - 2 * g) / 2 ≤ decodingRadius d := by
  unfold decodingRadius
  apply Nat.div_le_div_right
  omega

end Qatlib.Papers.AlgGeomCode25.MainResults
