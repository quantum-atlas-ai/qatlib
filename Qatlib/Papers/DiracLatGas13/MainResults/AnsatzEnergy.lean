/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DiracLatGas13.MainResults.RelativisticEnergy

@[expose] public section

/-!
# Energy of the lattice momentum ansatz

Compose Eqs. (80) and (81) of arXiv:1307.3595v1 to obtain the grid-level
energy. The mass term in the cosine contribution is squared, as follows
from the squared momentum and the relativistic energy relation.
-/

set_option autoImplicit false

open Qatlib.Papers.DiracLatGas13.MainResults

namespace Qatlib.Papers.DiracLatGas13.MainResults

/-- The lattice momentum ansatz implies the corrected squared energy relation. -/
theorem gridEnergy_of_ansatz (p E m c ℏ τ ℓ k : ℝ)
    (hτ : τ ≠ 0) (hℏ : ℏ ≠ 0) (hpos : 0 ≤ 1 - (m * c ^ 2 * τ / ℏ) ^ 2)
    (h80 : p * c * τ / ℏ =
      Real.sqrt (1 - (m * c ^ 2 * τ / ℏ) ^ 2) * Real.sin (ℓ * k))
    (hE : E ^ 2 = p ^ 2 * c ^ 2 + (m * c ^ 2) ^ 2) :
    GridEnergySq E m c ℏ τ ℓ k :=
  gridEnergy_of_momentum p E m c ℏ τ ℓ k
    (momentumSq_of_ansatz p m c ℏ τ ℓ k hτ hℏ hpos h80) hE

end Qatlib.Papers.DiracLatGas13.MainResults
