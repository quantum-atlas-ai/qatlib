/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamLCUSim12.TaylorBounds.DefectOrder

@[expose] public section

/-!
# Trotter/Suzuki first slice: the multiproduct defect-order bound, restated for the
paper line

The first auditable slice of the AdiabaticEvol00 line: the
multiproduct defect-order bound of the existing TaylorBounds analysis, restated
under this paper line's namespace so the slice's dependency is one theorem, not a
diffuse file. The bound is reused as proved; this slice does not construct a
Suzuki commutator schedule, does not evaluate a concrete exponent set, and does not
turn the remainder into a gate count.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Papers.HamLCUSim12.TaylorBounds.DefectOrder

namespace Qatlib.Papers.AdiabaticEvol00.TrotterSlice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The multiproduct order bound, restated: moment conditions plus node-defect
bounds give the defect-order estimate for the multiproduct combination. -/
theorem trotterDefectBound (k χ : ℕ) (C : Fin (k + 1) → ℝ) (ℓ : Fin (k + 1) → ℝ)
    (hmom₁ : ∑ q, C q = 1)
    (hmom : ∀ j : ℕ, j < k → (∑ q, C q / ℓ q ^ (2 * χ + 2 * j)) = 0)
    (U : ℝ → E) (W : Fin (k + 1) → ℝ → E) (D : ℕ → E) (B lam : ℝ)
    (hd : ∀ q : Fin (k + 1),
      ‖W q lam - U lam - ∑ j : Fin k, ((lam ^ (2 * χ + 1 + 2 * (j : ℕ))) /
        (ℓ q ^ (2 * χ + 2 * (j : ℕ)))) • (D (j : ℕ))‖ ≤
        B * lam ^ (2 * (χ + k) + 1)) :
    ‖(∑ q, C q • W q lam) - U lam‖ ≤ (∑ q, |C q|) * B * lam ^ (2 * (χ + k) + 1) :=
  multiproduct_order_at k χ C ℓ hmom₁ hmom U W D B lam hd

end Qatlib.Papers.AdiabaticEvol00.TrotterSlice
