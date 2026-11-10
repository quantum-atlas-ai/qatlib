/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Theorem31
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults

open Model

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

theorem theorem51_reduction (k n : ℕ) (hk : 4 < k) (V : JonesValue n)
    (E : BraidEncodingK n k) (hΔ : 0 < deltaScale k n)
    (hscale : ∀ b : BraidWord n, ‖V b‖ = deltaScale k n * E.amp b)
    (heps : E.eps ≤ 1 / 20) :
    BQPHard (jonesPromise n V (deltaScale k n)) :=
  theorem31_reduction k n hk V E.toEncoding hΔ hscale heps

theorem theorem51_bqpHard (p : ℕ → ℕ) (_hp : PolyBound p) (n : ℕ)
    (hk4 : ∀ l, 4 < p l) (hk6 : ∀ l, p l ≠ 6) (V : JonesValue n)
    (E : BraidEncodingK n (p n)) (hΔ : 0 < deltaScale (p n) n)
    (hscale : ∀ b : BraidWord n, ‖V b‖ = deltaScale (p n) n * E.amp b)
    (heps : E.eps ≤ 1 / 20) :
    BQPHard (jonesPromise n V (deltaScale (p n) n)) :=
  theorem51_reduction (p n) n (hk4 n) V E hΔ hscale heps

theorem theorem51_scale_pos (p : ℕ → ℕ) (n : ℕ) (hk4 : ∀ l, 4 < p l) :
    0 < deltaScale (p n) n :=
  deltaScale_pos (by have := hk4 n; omega)

end Qatlib.Papers.BQPJonesPoly06.MainResults
