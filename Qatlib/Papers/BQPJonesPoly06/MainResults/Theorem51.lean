/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Theorem31

/-!
# Parameter-dependent Jones hardness reduction

The structure `BraidEncodingK` records a crossing bound polynomial in both circuit size and the
parameter `k`. Its conversion `BraidEncodingK.toEncoding` absorbs the parameter factor into the
constant, allowing the fixed-parameter reduction to yield the hardness statements associated
with Theorem 5.1 of [AharonovArad2011].

## Main statements

* `BraidEncodingK.toEncoding`: converts a parameter-dependent encoding to `BraidEncoding`.
* `theorem51_bqpHard`: gives Jones promise hardness at a polynomially bounded choice `k = p n`.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults

open Model

/-- A circuit-to-braid encoding whose crossing bound is polynomial in `(C.size + 1) * (k + 1)`
and whose amplitudes approximate circuit amplitudes within a nonnegative error budget. -/
structure BraidEncodingK (n : ℕ) (k : ℕ) where

  amp : BraidWord n → ℝ

  enc : CircuitGap → BraidWord n

  degree : ℕ

  constant : ℕ

  eps : ℝ

  eps_nonneg : 0 ≤ eps

  size_bound : ∀ C : CircuitGap,
    (enc C).numCrossings ≤ constant * ((C.size + 1) * (k + 1)) ^ degree

  amp_close : ∀ C : CircuitGap, |amp (enc C) - C.amplitude| ≤ eps

/-- Converts a parameter-dependent braid encoding to `BraidEncoding` by absorbing `(k + 1) ^
E.degree` into its size-bound constant [AharonovArad2011]. -/
def BraidEncodingK.toEncoding {n k : ℕ} (E : BraidEncodingK n k) : BraidEncoding n where
  amp := E.amp
  enc := E.enc
  degree := E.degree
  constant := E.constant * (k + 1) ^ E.degree
  eps := E.eps
  eps_nonneg := E.eps_nonneg
  size_bound := by
    intro C
    have h := E.size_bound C
    rw [mul_pow] at h
    calc (E.enc C).numCrossings
        ≤ E.constant * ((C.size + 1) ^ E.degree * (k + 1) ^ E.degree) := h
      _ = E.constant * (k + 1) ^ E.degree * (C.size + 1) ^ E.degree := by ring
  amp_close := E.amp_close

/-- A parameter-dependent encoding with error at most `1 / 20` yields BQP hardness under the
positive Jones scaling relation [AharonovArad2011, Theorem 5.1][AharonovArad2011]. -/
theorem theorem51_reduction (k n : ℕ) (hk : 4 < k) (V : JonesValue n)
    (E : BraidEncodingK n k) (hΔ : 0 < deltaScale k n)
    (hscale : ∀ b : BraidWord n, ‖V b‖ = deltaScale k n * E.amp b)
    (heps : E.eps ≤ 1 / 20) :
    BQPHard (jonesPromise n V (deltaScale k n)) :=
  theorem31_reduction k n hk V E.toEncoding hΔ hscale heps

/-- For a polynomially bounded parameter `p` with values greater than four and different from
six, the supplied encoding and scaling data yield Jones promise BQP hardness at `p n`
[AharonovArad2011, Theorem 5.1][AharonovArad2011]. -/
theorem theorem51_bqpHard (p : ℕ → ℕ) (_hp : PolyBound p) (n : ℕ)
    (hk4 : ∀ l, 4 < p l) (hk6 : ∀ l, p l ≠ 6) (V : JonesValue n)
    (E : BraidEncodingK n (p n)) (hΔ : 0 < deltaScale (p n) n)
    (hscale : ∀ b : BraidWord n, ‖V b‖ = deltaScale (p n) n * E.amp b)
    (heps : E.eps ≤ 1 / 20) :
    BQPHard (jonesPromise n V (deltaScale (p n) n)) :=
  theorem51_reduction (p n) n (hk4 n) V E hΔ hscale heps

/-- The Jones normalization factor at `p n` is positive when every value of `p` is greater than
four. -/
theorem theorem51_scale_pos (p : ℕ → ℕ) (n : ℕ) (hk4 : ∀ l, 4 < p l) :
    0 < deltaScale (p n) n :=
  deltaScale_pos (by have := hk4 n; omega)

end Qatlib.Papers.BQPJonesPoly06.MainResults
