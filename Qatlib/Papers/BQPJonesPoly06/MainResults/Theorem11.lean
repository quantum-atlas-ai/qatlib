/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Theorem51
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults

open Model

theorem theorem11_bqpComplete (p : ℕ → ℕ) (hp : PolyBound p) (n : ℕ)
    (hk4 : ∀ l, 4 < p l) (hk6 : ∀ l, p l ≠ 6) (V : JonesValue n)
    (E : BraidEncodingK n (p n))
    (hscale : ∀ b : BraidWord n, ‖V b‖ = deltaScale (p n) n * E.amp b)
    (heps : E.eps ≤ 1 / 20)
    (hAJL : InBQP (jonesPromise n V (deltaScale (p n) n))) :
    BQPComplete (jonesPromise n V (deltaScale (p n) n)) :=
  ⟨theorem51_bqpHard p hp n hk4 hk6 V E (theorem51_scale_pos p n hk4) hscale heps,
    hAJL⟩

theorem theorem11_bqpHard (p : ℕ → ℕ) (hp : PolyBound p) (n : ℕ)
    (hk4 : ∀ l, 4 < p l) (hk6 : ∀ l, p l ≠ 6) (V : JonesValue n)
    (E : BraidEncodingK n (p n))
    (hscale : ∀ b : BraidWord n, ‖V b‖ = deltaScale (p n) n * E.amp b)
    (heps : E.eps ≤ 1 / 20) :
    BQPHard (jonesPromise n V (deltaScale (p n) n)) :=
  theorem51_bqpHard p hp n hk4 hk6 V E (theorem51_scale_pos p n hk4) hscale heps

end Qatlib.Papers.BQPJonesPoly06.MainResults
