/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Encoding

/-!
# Fixed-parameter Jones hardness reduction

The structure `BraidEncoding` records a polynomial crossing bound and an additive approximation
to circuit amplitudes. Given this encoding and the Jones-value scaling relation,
`theorem31_reduction` transfers the circuit gap to the Jones promise problem in the setting of
[AharonovArad2011].

## Main statements

* `theorem31_reduction`: an encoding error at most `1 / 20` yields BQP hardness.
* `theorem31_bqpHard`: the fixed-parameter statement with the paper's restriction on `k`.
* `theorem31_scale_pos`: positivity of the Jones normalization factor for `k > 4`.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults

open Model

/-- A circuit-to-braid encoding with a polynomial crossing bound, a nonnegative error budget,
and amplitudes approximating those of the input circuits. -/
structure BraidEncoding (n : ℕ) where

  amp : BraidWord n → ℝ

  enc : CircuitGap → BraidWord n

  degree : ℕ

  constant : ℕ

  eps : ℝ

  eps_nonneg : 0 ≤ eps

  size_bound : ∀ C : CircuitGap, (enc C).numCrossings ≤ constant * (C.size + 1) ^ degree

  amp_close : ∀ C : CircuitGap, |amp (enc C) - C.amplitude| ≤ eps

/-- A braid encoding with error at most `1 / 20` yields BQP hardness of the Jones promise
problem when the scale is positive and Jones magnitudes equal scaled encoding amplitudes
[AharonovArad2011, Theorem 3.1][AharonovArad2011]. -/
theorem theorem31_reduction (k n : ℕ) (hk : 4 < k) (V : JonesValue n)
    (E : BraidEncoding n) (hΔ : 0 < deltaScale k n)
    (hscale : ∀ b : BraidWord n, ‖V b‖ = deltaScale k n * E.amp b)
    (heps : E.eps ≤ 1 / 20) :
    BQPHard (jonesPromise n V (deltaScale k n)) := by
  refine ⟨{ map := E.enc, degree := E.degree, constant := E.constant,
            size_bound := E.size_bound, maps_yes := ?_, maps_no := ?_ }⟩
  · intro C _ hC
    have hclose := E.amp_close C
    have hamp : E.amp (E.enc C) ≤ 1 / 10 := by
      have h1 : E.amp (E.enc C) ≤ C.amplitude + E.eps := by
        have := (abs_le.mp hclose).2
        linarith
      have h2 : C.amplitude ≤ 1 / 20 := hC
      linarith
    refine ⟨hΔ, ?_⟩
    show ‖V (E.enc C)‖ ≤ deltaScale k n / 10
    rw [hscale (E.enc C)]
    have hstep := mul_le_mul_of_nonneg_left hamp (le_of_lt hΔ)
    linarith
  · intro C _ hC
    have hclose := E.amp_close C
    have hamp : 9 / 10 ≤ E.amp (E.enc C) := by
      have h1 : C.amplitude - E.eps ≤ E.amp (E.enc C) := by
        have := (abs_le.mp hclose).1
        linarith
      have h2 : (19 : ℝ) / 20 ≤ C.amplitude := hC
      linarith
    refine ⟨hΔ, ?_⟩
    show 9 * deltaScale k n / 10 ≤ ‖V (E.enc C)‖
    rw [hscale (E.enc C)]
    have hstep := mul_le_mul_of_nonneg_left hamp (le_of_lt hΔ)
    linarith

/-- The fixed-parameter BQP hardness conclusion for `k > 4` and `k ≠ 6`, assuming the braid
encoding, positive scaling relation, and error bound [AharonovArad2011, Theorem
3.1][AharonovArad2011]. -/
theorem theorem31_bqpHard (k n : ℕ) (hk : 4 < k) (_hk6 : k ≠ 6) (V : JonesValue n)
    (E : BraidEncoding n) (hΔ : 0 < deltaScale k n)
    (hscale : ∀ b : BraidWord n, ‖V b‖ = deltaScale k n * E.amp b)
    (heps : E.eps ≤ 1 / 20) :
    BQPHard (jonesPromise n V (deltaScale k n)) :=
  theorem31_reduction k n hk V E hΔ hscale heps

/-- The Jones normalization factor `deltaScale k n` is positive when `k > 4`. -/
theorem theorem31_scale_pos (k n : ℕ) (hk : 4 < k) : 0 < deltaScale k n :=
  deltaScale_pos (by omega)

end Qatlib.Papers.BQPJonesPoly06.MainResults
