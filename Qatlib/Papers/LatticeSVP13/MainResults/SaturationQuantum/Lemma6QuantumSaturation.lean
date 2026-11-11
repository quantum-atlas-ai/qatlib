/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatticeSVP13.MainResults.ExponentCore.PaperConstants

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 6: quantum complexity of the Pujol--Stehlé saturation algorithm

Laarhoven--Mosca--van de Pol, fixed arXiv:1301.6176v1 (25 Jan 2013), Appendix B, p. 17.

In the quantum setting the three phases of Algorithm 2 cost (Appendix B, p. 17):

* generating `T`: `Õ(N₁max · |T|) = 2 ^ ((c_g + 3c_t/2) n + o(n))`,
* generating `S`: `Õ(√N₂ · |T|) = 2 ^ ((c_g + c_b/2 + c_t/2) n + o(n))`,
* searching `S` for close pairs: `Õ(√|S|²) = 2 ^ ((c_g + c_b/2) n + o(n))`,

and the space is `O(|T| + |S|) = 2 ^ (max(c_t, c_g + c_b/2) n + o(n))`.

> **Lemma 6.** Let `ξ > ½` and `R > 2ξ`, and suppose `μ > λ₁(L)`.  Then, with the
> constants of Equations (2)–(5) and probability at least `1/16`, Algorithm 2 returns a
> lattice vector `s ∈ L \ {0}` with `‖s‖ < μ` on a quantum computer in time at most
> `2 ^ (t̃ n + o(n))` and space at most `2 ^ (s̃ n + o(n))`, where
> `t̃ = max(c_g + 3c_t/2, c_g + c_b/2 + c_t/2, c_g + c_b/2)` and
> `s̃ = max(c_t, c_g + c_b/2)`.  (Equation (7).)

The success guarantee (`probability at least 1/16`, `returns s ∈ L \ {0}` with
`‖s‖ < μ`) is the correctness input from Pujol--Stehlé [44, Lemma 3], carried as an
assumption of the lemma; this file proves the complexity conclusion of Lemma 6 — that
the sequential sum of the three phase costs has leading exponent `t̃` and that the space
cost has exponent `s̃` — from the per-phase exponents above.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.LatticeSVP13.MainResults.SaturationQuantum

open Qatlib.Papers.LatticeSVP13.MainResults.ExponentCore

/-- **Lemma 6** (arXiv:1301.6176v1, p. 17, Equation (7)).  Given exponents for the three
quantum phases (`hTgen`, `hSgen`, `hSsearch`) and for the space cost (`hSpace`), the
total time `Tgen + Sgen + Ssearch` (sequential) has exponent `t̃` and the space has
exponent `s̃`.

`hξ`, `hR` are the paper's range assumptions `ξ > ½`, `R > 2ξ` (which make `c_t` and
`c_g` well defined).  `hTime` fixes the total time to the sequential sum of the three
phase costs. -/
theorem lemma6_quantum_saturation
    (ξ R : ℝ) (hξ : 1 / 2 < ξ) (hR : 2 * ξ < R)
    (Tgen Sgen Ssearch time space : ℕ → ℝ)
    (hTgen : HasLog2Exponent (fun n => Real.logb 2 (Tgen n)) (cG ξ + 3 * cT ξ R / 2))
    (hSgen : HasLog2Exponent (fun n => Real.logb 2 (Sgen n))
      (cG ξ + cB R / 2 + cT ξ R / 2))
    (hSsearch : HasLog2Exponent (fun n => Real.logb 2 (Ssearch n)) (cG ξ + cB R / 2))
    (hSpace : HasLog2Exponent (fun n => Real.logb 2 (space n))
      (quantumSpaceExponent (cB R) (cT ξ R) (cG ξ)))
    (hTime : ∀ n, time n = Tgen n + Sgen n + Ssearch n)
    (hpTgen : ∀ n, 0 < Tgen n) (hpSgen : ∀ n, 0 < Sgen n) (hpSsearch : ∀ n, 0 < Ssearch n) :
    HasLog2Exponent (fun n => Real.logb 2 (time n))
        (quantumTimeExponent (cB R) (cT ξ R) (cG ξ)) ∧
    HasLog2Exponent (fun n => Real.logb 2 (space n))
        (quantumSpaceExponent (cB R) (cT ξ R) (cG ξ)) := by
  constructor
  · -- Total time = (Tgen + Sgen) + Ssearch; repeatedly use `log₂ (a+b) ≤ 1 + max …`.
    have h12 : HasLog2Exponent (fun n => Real.logb 2 (Tgen n + Sgen n))
        (max (cG ξ + 3 * cT ξ R / 2) (cG ξ + cB R / 2 + cT ξ R / 2)) := by
      have hsup := hTgen.sup hSgen
      have hshift := hsup.add_const 1
      refine hshift.of_le (fun n => ?_)
      have h := logb_two_sum_le (hpTgen n) (hpSgen n)
      linarith
    have h123 : HasLog2Exponent
        (fun n => Real.logb 2 ((Tgen n + Sgen n) + Ssearch n))
        (quantumTimeExponent (cB R) (cT ξ R) (cG ξ)) := by
      have hsup := h12.sup hSsearch
      have hshift := hsup.add_const 1
      have hle := hshift.of_le
        (f := fun n => Real.logb 2 ((Tgen n + Sgen n) + Ssearch n)) (fun n => by
        have h := logb_two_sum_le (a := Tgen n + Sgen n) (b := Ssearch n)
          (by linarith [hpTgen n, hpSgen n]) (hpSsearch n)
        linarith)
      simpa only [quantumTimeExponent] using hle
    exact h123.congr (fun n => by rw [hTime n])
  · exact hSpace

end Qatlib.Papers.LatticeSVP13.MainResults.SaturationQuantum
