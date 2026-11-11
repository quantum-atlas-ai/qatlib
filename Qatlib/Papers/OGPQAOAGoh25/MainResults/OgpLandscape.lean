/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-! OGP landscape lemmas for
"The Overlap Gap Property limits limit swapping in the QAOA"
(arXiv:2404.06087v6, 2025, Mark Goh).

- `OgpBand` is the abstract Overlap Gap Property of a spin-glass-type
  energy landscape: two solutions whose distance lies in the forbidden
  band `[δ₁, δ₂]` cannot both have energy strictly above the OGP level
  `ηOGP`.
- `ogp_forbids_two_far_optima` (Corollary 4.2.2, deterministic core)
  draws the direct consequence used throughout the paper: any two
  solutions with energy above `ηOGP` must avoid the forbidden band, i.e.
  they are either clustered (distance `< δ₁`) or nearly antipodal
  (distance `> δ₂`). This is the logical step behind "if the OGP exists,
  limit swapping is sub-optimal": an algorithm achieving
  `ηOPT > ηOGP + ε` cannot couple two independent runs into the band.
- `limit_swap_suboptimal` packages the same content as the impossibility
  statement of Corollary 4.2.2: two outputs of the swapped-limit
  algorithm, both above `ηOGP` and at band distance, contradict the OGP.

The random-instance asymptotics (n → ∞, w.h.p. overlap concentration of
local algorithms at distance n/2, the Guerra-interpolation inputs) are
not formalized here; see the PR work log.

No axiom, no `admit`, no `native_decide`. -/
set_option autoImplicit false

namespace Qatlib.Papers.OGPQAOAGoh25.MainResults.OgpLandscape

variable {X : Type} (dist : X → X → ℝ) (F : X → ℝ) (δ₁ δ₂ ηOGP : ℝ)

/-- **Overlap Gap Property, abstract band form**: any two solutions at
distance in the forbidden band `[δ₁, δ₂]` have at least one of their
energies at most `ηOGP`. -/
def OgpBand : Prop :=
  ∀ x y : X, δ₁ ≤ dist x y → dist x y ≤ δ₂ → min (F x) (F y) ≤ ηOGP

/-- **Corollary 4.2.2, deterministic core**: under the OGP band
property, two solutions with energy strictly above `ηOGP` cannot lie at
a band distance — they are either clustered (distance `< δ₁`) or far
(distance `> δ₂`). -/
theorem ogp_forbids_two_far_optima (h : OgpBand dist F δ₁ δ₂ ηOGP)
    (x y : X) (hx : ηOGP < F x) (hy : ηOGP < F y) :
    dist x y < δ₁ ∨ δ₂ < dist x y := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hlo, hhi⟩ := hcon
  exact absurd (h x y hlo hhi) (not_le.mpr (lt_min hx hy))

/-- **Corollary 4.2.2, impossibility form**: if the swapped-limit
algorithm produced two solutions `x`, `y` both with energy above the OGP
level `ηOGP` and at a distance inside the forbidden band, the OGP band
property would be violated — hence limit swapping cannot reach the
optimum `ηOPT > ηOGP` when the OGP holds. -/
theorem limit_swap_suboptimal (h : OgpBand dist F δ₁ δ₂ ηOGP)
    (x y : X) (hx : ηOGP < F x) (hy : ηOGP < F y)
    (hlo : δ₁ ≤ dist x y) (hhi : dist x y ≤ δ₂) : False :=
  absurd (h x y hlo hhi) (not_le.mpr (lt_min hx hy))

end Qatlib.Papers.OGPQAOAGoh25.MainResults.OgpLandscape
