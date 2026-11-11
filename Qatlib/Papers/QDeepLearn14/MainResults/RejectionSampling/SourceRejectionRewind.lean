/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Rejection-sampling success probability (Lemma 2)

Source: "Quantum Deep Learning", arXiv:1412.3489v2, Lemma 2, p.10 (eqs. A5-A9).

The paper prepares a coherent analogue of the Gibbs state by preparing the
mean-field state `|ψ_Q⟩`, annotating each configuration with
`P(v,h) = e^{-E(v,h)}/(κ Z_Q Q(v,h))` (eq. A6), controlled-rotating an ancilla
(eq. A7) and post-selecting the ancilla on `1`. The probability of post-selection
is the squared normalization constant in (A8), namely

  `P(1 | κ, Z_Q) = Z / (κ Z_Q)`   (eq. A9),

and the clamped case gives `Z_x / (κ_x Z_{x,Q})`.

We model only the arithmetic of (A9): the success probability is a valid
probability in `[0,1]` (guaranteed by the Lemma-1 bound `Z ≤ κ Z_Q`), and it is
the square of the amplitude `√(Z/(κ Z_Q))` fixed by (A8). The quantum circuit is
the paper's granted primitive and is not re-modelled.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDeepLearn14.MainResults.RejectionSampling

/-- Success probability `Z/(κ Z_Q)` of the rejection-sampling preparation
(arXiv:1412.3489 eq. A9). -/
def successProbability (Z κ ZQ : ℝ) : ℝ := Z / (κ * ZQ)

/-- The success amplitude `√(Z/(κ Z_Q))` is the normalization constant in
eq. A8; its square is the post-selection probability of eq. A9. -/
theorem successProbability_sq_amplitude
    (Z κ ZQ : ℝ) (hZ : 0 ≤ Z) (hκZQ : 0 ≤ κ * ZQ) :
    Real.sqrt (successProbability Z κ ZQ) ^ 2 = successProbability Z κ ZQ := by
  unfold successProbability
  exact Real.sq_sqrt (div_nonneg hZ hκZQ)

/-- **Lemma 2 (generic form)** of arXiv:1412.3489 (p.10): when the Lemma-1 bound
`Z ≤ κ Z_Q` holds, the success probability `Z/(κ Z_Q)` is a valid probability,
`0 ≤ Z/(κ Z_Q) ≤ 1`, and equals the square of the amplitude `√(Z/(κ Z_Q))`. -/
theorem lemma2_successProbability
    (Z κ ZQ : ℝ) (hZpos : 0 < Z) (hκ : 0 < κ) (hZQ : 0 < ZQ)
    (hZκZQ : Z ≤ κ * ZQ) :
    0 ≤ successProbability Z κ ZQ ∧ successProbability Z κ ZQ ≤ 1 ∧
      Real.sqrt (successProbability Z κ ZQ) ^ 2 = successProbability Z κ ZQ := by
  have hκZQpos : 0 < κ * ZQ := mul_pos hκ hZQ
  refine ⟨?_, ?_, successProbability_sq_amplitude Z κ ZQ hZpos.le hκZQpos.le⟩
  · unfold successProbability
    exact div_nonneg hZpos.le hκZQpos.le
  · unfold successProbability
    exact (div_le_one hκZQpos).mpr hZκZQ

/-- **Lemma 2, clamped case** (arXiv:1412.3489 p.10): with the visible units
clamped to a training configuration `x`, the success probability is
`Z_x / (κ_x Z_{x,Q})`, again a valid probability under the analogous Lemma-1
bound `Z_x ≤ κ_x Z_{x,Q}`. -/
theorem lemma2_clampedSuccessProbability
    (Zx κx ZxQ : ℝ) (hZxpos : 0 < Zx) (hκx : 0 < κx) (hZxQ : 0 < ZxQ)
    (hle : Zx ≤ κx * ZxQ) :
    0 ≤ successProbability Zx κx ZxQ ∧ successProbability Zx κx ZxQ ≤ 1 := by
  have := lemma2_successProbability Zx κx ZxQ hZxpos hκx hZxQ hle
  exact ⟨this.1, this.2.1⟩

end Qatlib.Papers.QDeepLearn14.MainResults.RejectionSampling
