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
# Relaxed rejection-sampling fidelity bound (Lemma 3)

Source: "Quantum Deep Learning", arXiv:1412.3489v2, Lemma 3, p.12
(eqs. A12-A15).

If the clean promise `κ Q(v,h) ≥ e^{-E(v,h)}/Z_Q` is relaxed so that it holds only
on a good set while on the bad set `κ Q(v,h) < e^{-E(v,h)}/Z_Q`, with the total
bad excess mass bounded by

  `∑_{(v,h) ∈ bad} (e^{-E(v,h)} - Z_Q κ Q(v,h)) ≤ ε Z`   (hypothesis of Lemma 3),

then the preparation has success probability at least `Z(1-ε)/(κ Z_Q)`
(eq. A13) and fidelity at least `1-ε` with the target Gibbs state (eqs. A14, A15).

We model `Z` (true partition), `κ Z_Q` (the rescaled mean-field partition) and
`badExcess = ∑_{bad}(e^{-E} - Z_Q κ Q)` as positive reals. The success
probability (A13) is `(Z - badExcess)/(κ Z_Q)` and the squared fidelity (A14) is
`(Z - badExcess)/Z`; both estimates are proved from the bad-mass bound.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDeepLearn14.MainResults.RejectionSampling

/-- Success probability of the relaxed preparation (arXiv:1412.3489 eq. A13):
`(Z - badExcess)/(κ Z_Q)`. -/
def relaxedSuccessProbability (Z κ ZQ badExcess : ℝ) : ℝ :=
  (Z - badExcess) / (κ * ZQ)

/-- Squared fidelity with the target Gibbs state (arXiv:1412.3489 eq. A14):
`(Z - badExcess)/Z`. -/
def relaxedFidelitySq (Z badExcess : ℝ) : ℝ := (Z - badExcess) / Z

/-- **Lemma 3** of arXiv:1412.3489 (p.12). Assume `0 ≤ ε ≤ 1`, the bad excess mass
satisfies `badExcess ≤ ε Z` with `0 ≤ badExcess`, and the Lemma-1 bound
`Z ≤ κ Z_Q`. Then:
* the success probability is at least `Z(1-ε)/(κ Z_Q)` (eq. A13),
* it is a valid probability `≤ 1`,
* the fidelity `√((Z - badExcess)/Z)` is at least `1 - ε` (eqs. A14-A15). -/
theorem lemma3_fidelityProbability
    (Z κ ZQ badExcess ε : ℝ) (hZpos : 0 < Z) (hκ : 0 < κ) (hZQ : 0 < ZQ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hbad0 : 0 ≤ badExcess) (hbad : badExcess ≤ ε * Z)
    (hZle : Z ≤ κ * ZQ) :
    Z * (1 - ε) / (κ * ZQ) ≤ relaxedSuccessProbability Z κ ZQ badExcess ∧
      relaxedSuccessProbability Z κ ZQ badExcess ≤ 1 ∧
      (1 - ε) ≤ Real.sqrt (relaxedFidelitySq Z badExcess) := by
  have hκZQpos : 0 < κ * ZQ := mul_pos hκ hZQ
  -- Success probability lower bound (A13).
  have hsucc : Z * (1 - ε) / (κ * ZQ) ≤ relaxedSuccessProbability Z κ ZQ badExcess := by
    unfold relaxedSuccessProbability
    rw [div_le_div_iff₀ hκZQpos hκZQpos]
    nlinarith [hbad]
  -- Validity: success probability ≤ 1.
  have hupper : relaxedSuccessProbability Z κ ZQ badExcess ≤ 1 := by
    unfold relaxedSuccessProbability
    rw [div_le_one hκZQpos]
    nlinarith [hZle, hbad0]
  refine ⟨hsucc, hupper, ?_⟩
  -- Squared fidelity ≥ 1 - ε, from the bad-mass bound.
  have hfidSq : (1 - ε) ≤ relaxedFidelitySq Z badExcess := by
    unfold relaxedFidelitySq
    rw [le_div_iff₀ hZpos]
    nlinarith [hbad]
  -- sqrt is monotone, and x ≤ sqrt x for x ∈ [0,1].
  have hnonneg : 0 ≤ 1 - ε := by linarith
  have hsqrt_mono : Real.sqrt (1 - ε) ≤ Real.sqrt (relaxedFidelitySq Z badExcess) :=
    Real.sqrt_le_sqrt hfidSq
  have hself : (1 - ε) ≤ Real.sqrt (1 - ε) := by
    rw [Real.le_sqrt hnonneg hnonneg]
    nlinarith [hε0, hε1]
  exact le_trans hself hsqrt_mono

end Qatlib.Papers.QDeepLearn14.MainResults.RejectionSampling
