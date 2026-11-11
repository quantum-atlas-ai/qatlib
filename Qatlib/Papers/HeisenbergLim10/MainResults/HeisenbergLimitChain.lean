/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Heisenberg limit chain, Eqs. (2), (3), (6), (7), (8)

Source: Zwierz, Pérez-Delgado, Kok, *General optimality of the Heisenberg limit
for quantum metrology*, fixed arXiv:1004.3944 (2010), p. 3.

The paper's proof of the Heisenberg limit is a three-step real-analytic chain:

* Eq. (2) — the (quantum) Cramér–Rao bound `(δφ)² ≥ 1 / (T F(φ))`, quoted from
  Braunstein–Caves [3, 5];
* Eq. (3) — the statistical distance `s` obeys `(ds/dφ)² = F(φ)`;
* Eq. (6) — the Wootters-distance speed bound `ds/dφ ≤ |⟨H⟩|`, proved from the
  Schrödinger equation for `|ψ(φ)⟩ = exp(-i φ H)|ψ(0)⟩`.

Composing these gives Eq. (7),
`(δφ)² ≥ (1/T) (ds/dφ)⁻² ≥ 1/(T |⟨H⟩|²)`, and for a single-shot experiment
`T = 1` Eq. (8), `δφ ≥ 1/|⟨H⟩|`.

This module fixes the real-analytic skeleton: the Cramér–Rao bound is used as
the paper's external premise (`hcr`), and the paper's own chain (inverse
antitonicity of the squared speed followed by the square root) is proved in
full.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.HeisenbergLim10.MainResults

/-- Fixed arXiv:1004.3944, Eq. (7), p. 3.  From the Cramér–Rao premise
`(δφ)² ≥ (1/T)(ds/dφ)⁻²` and the Wootters speed bound `ds/dφ ≤ |⟨H⟩|` (Eq. (6)),
the mean squared error satisfies the Heisenberg bound `(δφ)² ≥ 1/(T |⟨H⟩|²)`.

`dsdφ` is the derivative `ds/dφ` of the statistical distance, `H` is the
positive absolute resource count `|⟨H⟩|`, and `T` is the number of repetitions.
The inverse comparison step is the paper's `(ds/dφ)⁻² ≥ |⟨H⟩|⁻²`, valid because
`ds/dφ > 0`. -/
theorem cramerRao_heisenberg_chain
    (δφ dsdφ H T : ℝ) (hT : 0 < T) (hds : 0 < dsdφ) (hH : 0 < H)
    (hdsH : dsdφ ≤ H)
    (hcr : (1 / T) * (dsdφ ^ 2)⁻¹ ≤ δφ ^ 2) :
    1 / (T * H ^ 2) ≤ δφ ^ 2 := by
  -- Squaring preserves the nonnegative speed bound `ds/dφ ≤ H`.
  have hsq : dsdφ ^ 2 ≤ H ^ 2 := by nlinarith
  -- Inversion reverses the order because both squared speeds are positive.
  have hinv : (H ^ 2)⁻¹ ≤ (dsdφ ^ 2)⁻¹ := inv_anti₀ (by positivity) hsq
  have hTpos : (0 : ℝ) < 1 / T := by positivity
  have hmul : (1 / T) * (H ^ 2)⁻¹ ≤ (1 / T) * (dsdφ ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_left hinv (le_of_lt hTpos)
  calc
    1 / (T * H ^ 2) = (1 / T) * (H ^ 2)⁻¹ := by field_simp
    _ ≤ (1 / T) * (dsdφ ^ 2)⁻¹ := hmul
    _ ≤ δφ ^ 2 := hcr

/-- Fixed arXiv:1004.3944, Eq. (8), p. 3.  In the single-shot regime `T = 1`,
the Heisenberg bound on the mean squared error yields the error bound
`δφ ≥ 1/|⟨H⟩|`.

The hypothesis `hbound` is the `T = 1` instance of Eq. (7), and `hδ` records that
`δφ` is a (nonnegative) error.  The proof takes square roots of both sides, as
in passing from Eq. (7) to Eq. (8). -/
theorem heisenberg_limit_single_shot
    (δφ H : ℝ) (hδ : 0 ≤ δφ) (hH : 0 < H)
    (hbound : 1 / H ^ 2 ≤ δφ ^ 2) :
    1 / H ≤ δφ := by
  have hsqrt : Real.sqrt (1 / H ^ 2) ≤ Real.sqrt (δφ ^ 2) :=
    Real.sqrt_le_sqrt hbound
  have hleft : Real.sqrt (1 / H ^ 2) = 1 / H := by
    rw [show (1 : ℝ) / H ^ 2 = (1 / H) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have hright : Real.sqrt (δφ ^ 2) = δφ := Real.sqrt_sq hδ
  linarith

/-- Fixed arXiv:1004.3944, Eqs. (7) and (8), p. 3, in one step.

Combining the chain with the single-shot specialization: the Cramér–Rao premise
`(δφ)² ≥ (1/T)(ds/dφ)⁻²`, the Wootters speed bound `ds/dφ ≤ |⟨H⟩|`, and `T = 1`
give `δφ ≥ 1/|⟨H⟩|`, the Heisenberg limit used as the paper's main lower bound. -/
theorem heisenberg_limit_T_one
    (δφ dsdφ H : ℝ) (hδ : 0 ≤ δφ) (hds : 0 < dsdφ) (hH : 0 < H)
    (hdsH : dsdφ ≤ H)
    (hcr : (1 / (1 : ℝ)) * (dsdφ ^ 2)⁻¹ ≤ δφ ^ 2) :
    1 / H ≤ δφ := by
  have hchain : 1 / ((1 : ℝ) * H ^ 2) ≤ δφ ^ 2 :=
    cramerRao_heisenberg_chain δφ dsdφ H 1 (by norm_num) hds hH hdsH hcr
  have hbound : 1 / H ^ 2 ≤ δφ ^ 2 := by simpa using hchain
  exact heisenberg_limit_single_shot δφ H hδ hH hbound

end Qatlib.Papers.HeisenbergLim10.MainResults
