/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RandCertLiu25.MainResults.EventProbabilityTools
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 2: the restricted adversary's XEB passing probability

Formalises Lemma 2 of Liu--Shaydulin--Niroula et al., *Certified randomness
using a trapped-ion quantum processor*, fixed arXiv:2503.20498v1, Lemma 2 and
Eqs. III.19--III.29, p. 20.

Statement.  Let `Ω` be the event that an adversary with classical computational
power `A` and `Q` perfect-fidelity quantum samples out of `M` passes the XEB
test with threshold `χ`.  Then

  `Pr[Ω] ≤ ε_adv(Q,χ) = ε1 + ε2`,     (III.29)

with the Chernoff term
`ε1 = exp(-δ² Φ_A / 3)` and the Gamma/hypergeometric term
`ε2 = 1 - Σ_{l=0}^{m} Γ̃(m+l, m(χ+1)) · [hypergeometric weight]`.

We formalise the final conditioning/union step (III.21--III.28):

  `Pr[Ω] ≤ Pr[L > Lmax] + Pr[XEB ≥ χ | L ≤ Lmax] ≤ ε1 + ε2`,

on a finite probability space.  `L` is the number of Porter--Thomas samples,
`Lmax` the threshold below which only `l ≤ Lmax` (hence at most `Lmax`)
Porter--Thomas bitstrings occur, `pass` is `XEB ≥ χ`, and `leq` is `L ≤ Lmax`.
The hypothesis `hCond` is the paper's `Pr[XEB ≥ χ | L = l] ≤ Pr[XEB ≥ χ | Lmax]`
bound (III.26--III.28) in unconditional form; `hLeq` is the Chernoff bound
`Pr[L > Lmax] ≤ ε1` (III.18) and `hPass` the Gamma tail bound `≤ ε2` (III.20).

The Chernoff and incomplete-Gamma tail estimates themselves are not re-derived
here; they are recorded as the hypotheses `hLeq` and `hPass`, not as axioms.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.RandCertLiu25.MainResults.AdversaryXebBound

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.RandCertLiu25.MainResults.EventProbabilityTools

/-- `ε_adv(Q,χ) = ε1 + ε2` (Eq. III.29). -/
def epsAdversary (eps1 eps2 : ℝ) : ℝ := eps1 + eps2

/-- **Lemma 2, conditioning step** (Eqs. III.24--III.28): the passing
probability is at most the mass of `L > Lmax` plus the mass of passing while
`L ≤ Lmax`. -/
theorem lemma2_pass_split {X : Type*} [Fintype X] [DecidableEq X] (P : FinDist X)
    (L : ℕ) (pass leq : (Fin L → X) → Prop) [DecidablePred pass] [DecidablePred leq] :
    P.probEvent pass ≤ P.probEvent (fun ω => ¬ leq ω) +
      P.probEvent (fun ω => pass ω ∧ leq ω) := by
  classical
  rw [probEvent_and_compl P pass leq]
  have hmono : P.probEvent (fun ω => pass ω ∧ ¬ leq ω) ≤ P.probEvent (fun ω => ¬ leq ω) :=
    probEvent_mono P (fun ω h => h.2)
  linarith

/-- **Lemma 2** (Eqs. III.25--III.29).  If `Pr[L > Lmax] ≤ ε1` and
`Pr[XEB ≥ χ ∧ L ≤ Lmax] ≤ ε2·Pr[L ≤ Lmax]`, then the adversary's passing
probability is at most `ε_adv(Q,χ) = ε1 + ε2`. -/
theorem lemma2_adversary_pass_probability {X : Type*} [Fintype X] [DecidableEq X]
    (P : FinDist X) (L : ℕ) (pass leq : (Fin L → X) → Prop)
    [DecidablePred pass] [DecidablePred leq]
    (eps1 eps2 : ℝ) (heps2 : 0 ≤ eps2)
    (hLeq : P.probEvent (fun ω => ¬ leq ω) ≤ eps1)
    (hCond : P.probEvent (fun ω => pass ω ∧ leq ω) ≤
      eps2 * P.probEvent leq) :
    P.probEvent pass ≤ epsAdversary eps1 eps2 := by
  classical
  have hsplit := lemma2_pass_split P L pass leq
  have hmass : P.probEvent leq ≤ 1 := probEvent_le_one P leq
  have hcond' : P.probEvent (fun ω => pass ω ∧ leq ω) ≤ eps2 := by
    calc P.probEvent (fun ω => pass ω ∧ leq ω) ≤ eps2 * P.probEvent leq := hCond
      _ ≤ eps2 * 1 := mul_le_mul_of_nonneg_left hmass heps2
      _ = eps2 := mul_one eps2
  unfold epsAdversary
  linarith

end Qatlib.Papers.RandCertLiu25.MainResults.AdversaryXebBound
