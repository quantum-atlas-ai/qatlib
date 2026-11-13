/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Reduction

/-!
# Multiplicative Jones promises from additive promises

This module constructs a size-bounded reduction from the additive Jones promise to the
multiplicative promise by choosing scale `Δ / 10`. For positive `Δ` and multiplicative factor `1
< c ≤ 9`, it transfers the model’s `SharpPHard` predicate to the multiplicative problem. See
[AharonovArad2011].

## Main statements

* `addToMulReduction`: constructs the reduction between the two promises.
* `corollary11_sharpPHard_of_additive`: transfers hardness for a positive scale.
* `corollary11_sharpPHard_of_additive_at`: specializes the scale to `deltaScale`.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults

open Model

/-- For positive `Δ` and `1 < c ≤ 9`, there exists a size-bounded reduction from the additive
Jones promise to the multiplicative Jones promise. See [Aharonov and Arad, Corollary
1.1][AharonovArad2011]. -/
theorem addToMulReduction (n : ℕ) (V : JonesValue n) (Δ : ℝ) (hΔ : 0 < Δ)
    (c : ℝ) (hc1 : 1 < c) (hc9 : c ≤ 9) :
    Nonempty (PolyReduction (jonesPromise n V Δ) (mulJonesPromise n V c)) := by
  refine ⟨{ map := fun b => ⟨b, Δ / 10⟩
            degree := 1
            constant := 1
            size_bound := ?_
            maps_yes := ?_
            maps_no := ?_ }⟩
  · intro b
    show b.numCrossings ≤ 1 * (b.numCrossings + 1) ^ 1
    simp
  · intro b _ hy
    exact ⟨⟨hc1, by linarith⟩, hy⟩
  · intro b _ hn
    refine ⟨⟨hc1, by linarith⟩, ?_⟩
    show c * (Δ / 10) ≤ ‖V b‖
    have hstep : c * (Δ / 10) ≤ 9 * (Δ / 10) :=
      mul_le_mul_of_nonneg_right hc9 (by linarith)
    have hrewrite : 9 * (Δ / 10) = 9 * Δ / 10 := by ring
    have hn' : 9 * Δ / 10 ≤ ‖V b‖ := hn
    linarith [hstep, hrewrite, hn']

/-- If the additive Jones promise satisfies `SharpPHard`, then so does the multiplicative Jones
promise for positive scale and `1 < c ≤ 9`. See [Aharonov and Arad, Corollary
1.1][AharonovArad2011]. -/
theorem corollary11_sharpPHard_of_additive (n : ℕ) (V : JonesValue n) (Δ : ℝ)
    (hΔ : 0 < Δ) (c : ℝ) (hc1 : 1 < c) (hc9 : c ≤ 9)
    (hAdd : SharpPHard (jonesPromise n V Δ)) :
    SharpPHard (mulJonesPromise n V c) :=
  hAdd.elim fun r =>
    (addToMulReduction n V Δ hΔ c hc1 hc9).elim fun s => ⟨r.comp s⟩

/-- Transfer `SharpPHard` from the additive Jones promise at scale `deltaScale (p n) n` to the
multiplicative promise when `p` is everywhere greater than four and `1 < c ≤ 9`. See
[Aharonov and Arad, Corollary 1.1][AharonovArad2011]. -/
theorem corollary11_sharpPHard_of_additive_at (p : ℕ → ℕ) (n : ℕ)
    (hk4 : ∀ l, 4 < p l) (V : JonesValue n) (c : ℝ) (hc1 : 1 < c) (hc9 : c ≤ 9)
    (hAdd : SharpPHard (jonesPromise n V (deltaScale (p n) n))) :
    SharpPHard (mulJonesPromise n V c) :=
  corollary11_sharpPHard_of_additive n V (deltaScale (p n) n)
    (deltaScale_pos (by have := hk4 n; omega)) c hc1 hc9 hAdd

end Qatlib.Papers.BQPJonesPoly06.MainResults
