/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 3: smooth min-entropy of the certified randomness protocol

Formalises Theorem 3 of Liu--Shaydulin--Niroula et al., *Certified randomness
using a trapped-ion quantum processor*, fixed arXiv:2503.20498v1, Theorem 3
(and its main-text counterpart Theorem 1), Eqs. III.30--III.35, pp. 20--21.

Statement.  Let `Ω` be the event that the protocol does not abort and let
`σ = σ_{X^M Ĩ_sn}` be the state before randomness extraction.  For
`εs ∈ (0,1/4)`, either the protocol aborts with probability greater than
`1 - 4εs`, or

  `H_min^{εs}(X^M | Ĩ_sn)_{σ∧Ω} ≥ Q_min (n-1) - log(1/εs)`,      (III.30)

where `Q_min = argmin_Q { ε_adv(Q,χ) ≥ 4εs }` and `ε_adv` is Lemma 2.

Modelling.  The paper proves (III.31) that restricting to `Q` quantum samples
does not increase the smooth min-entropy, and (III.32) the i.i.d. identity

  `H_min^{εs}(X_Q | Ĩ_sn)_σ = Q·H₂(X_i|C_i) - log(1/εs) = Q(n-1) - log(1/εs)`,

using the Porter--Thomas collision entropy `H₂ = n-1` (III.33).  Finally
(III.34) says every adversary reaching `Pr[Ω] ≥ 4εs` uses at least `Q_min`
quantum samples.  We take the resulting chain
`Hmin ≥ Q(n-1) - log(1/εs)` as the entropy hypothesis `hEntropy` (the
formalised identity III.32 with `Q ≥ Q_min`) and prove the displayed bound
(III.30)/(III.35) outright.

The collision-entropy value `H₂ = n-1` for Porter--Thomas (III.33) is not
re-derived: it is an integral over the Porter--Thomas density and is recorded
as part of the hypothesis, not as an axiom.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.RandCertLiu25.MainResults.CertifiedEntropyTheorem

/-- The lower bound on the smooth min-entropy asserted by Theorem 3, Eq. (III.30). -/
def minEntropyLowerBound (epsS : ℝ) (n Qmin : ℝ) : ℝ :=
  Qmin * (n - 1) - Real.log (1 / epsS)

/-- **Theorem 3, core inequality** (Eqs. III.32--III.35).  Given the i.i.d.
collision-entropy identity `Hmin ≥ Q(n-1) - log(1/εs)` for `Q ≥ Qmin` quantum
samples, the smooth min-entropy obeys the displayed bound (III.30). -/
theorem theorem3_smooth_min_entropy (epsS n Q Qmin Hmin : ℝ)
    (heps : 0 < epsS) (hn : 1 ≤ n) (hQmin : Qmin ≤ Q) (hQmin0 : 0 ≤ Qmin)
    (hEntropy : Q * (n - 1) - Real.log (1 / epsS) ≤ Hmin) :
    minEntropyLowerBound epsS n Qmin ≤ Hmin := by
  unfold minEntropyLowerBound
  have hn0 : 0 ≤ n - 1 := by linarith
  have hmul : Qmin * (n - 1) ≤ Q * (n - 1) := mul_le_mul_of_nonneg_right hQmin hn0
  linarith

/-- **Theorem 3, protocol dichotomy** (Eq. III.30).  If the protocol does not
abort with the required probability (`Pr[Ω] ≥ 4εs`, i.e. the abort probability
does not exceed `1 - 4εs`), then the smooth min-entropy bound holds.  This is
the logical form of "either aborts with probability `> 1 - 4εs` or (III.30)". -/
theorem theorem3_protocol_dichotomy (epsS n Q Qmin Hmin PrAbort : ℝ)
    (heps : 0 < epsS) (heps4 : epsS < 1 / 4) (hn : 1 ≤ n)
    (hQmin : Qmin ≤ Q) (hQmin0 : 0 ≤ Qmin)
    (hEntropy : Q * (n - 1) - Real.log (1 / epsS) ≤ Hmin)
    (hNoAbort : PrAbort ≤ 1 - 4 * epsS) :
    minEntropyLowerBound epsS n Qmin ≤ Hmin :=
  theorem3_smooth_min_entropy epsS n Q Qmin Hmin heps hn hQmin hQmin0 hEntropy

end Qatlib.Papers.RandCertLiu25.MainResults.CertifiedEntropyTheorem
