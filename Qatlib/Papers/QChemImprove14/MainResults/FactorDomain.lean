/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QChemImprove14.MainResults.TrotterCorrection

@[expose] public section


/-! # Domain checks for the inherited correction-factor model

The source's positive time step does not force positive frequency gaps. These
identities diagnose the literal inherited formula; they do not refute the
paper's perturbative argument or supply a corrected Hamiltonian simulator.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QChemImprove14.MainResults.FactorDomain

open Qatlib.Papers.QChemImprove14.MainResults

/-- The literal square-root quotient uses Lean's zero-denominator convention. -/
theorem factorAtZero : trotterFactor 0 = 0 := by
  simp [trotterFactor]

/-- Equal frequencies erase the coefficient in the inherited literal model. -/
theorem equalGap (t δ ω : ℝ) : correctedT t δ ω ω = 0 := by
  simp [correctedT, factorAtZero]

/-- The literal correction factor is odd, so a positive-time premise is insufficient. -/
theorem factorOdd (x : ℝ) : trotterFactor (-x) = -trotterFactor x := by
  unfold trotterFactor
  rw [Real.cos_neg, Real.sin_neg, div_neg]

/-- An unrestricted claim that the literal correction is always at least one is false. -/
theorem zeroGapRefutes : ¬ (∀ x : ℝ, 1 ≤ trotterFactor x) := by
  intro h
  have hzero := h 0
  rw [factorAtZero] at hzero
  norm_num at hzero

end Qatlib.Papers.QChemImprove14.MainResults.FactorDomain
