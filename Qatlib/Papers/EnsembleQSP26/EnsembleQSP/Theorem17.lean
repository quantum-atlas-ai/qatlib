/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EnsembleQSP26.EnsembleQSP.Theorem15

set_option backward.isDefEq.respectTransparency false

/-!
# EnsembleQSP26 — Theorem 17 (Hamiltonian simulation application)

Fixed version: arXiv:2601.20073v1 (first submitted 2026-01-27), Theorem 17 (Eqs. (D6)–(D10)).

Noisy QSP implements `e^{-iHT}` with i.i.d. phase noises `e_j`, `c = E cos e_j`.
The three conclusions (block-encoding of `(1/α)(e^{-iHT}+E)`, state preparation of
`e^{-iHT}|ψ⟩`, and estimation of `⟨ψ|e^{iHT}Oe^{-iHT}|ψ⟩`) reduce, respectively, to
Theorem 13 (block-encoding), amplitude amplification, and Theorem 15 (observable),
with the cost inflated by the QSP block-encoding factor `1/α ≈ (1/4)e^{-dν/2}`
(Eq. (D6)) and the polynomial degree (Eq. (D11)).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix BigOperators

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace Qatlib.Papers.EnsembleQSP26.EnsembleQSP

attribute [local instance] Classical.propDecidable

/-- **Theorem 17 (3), observable estimation (arXiv:2601.20073v1 p.16, Eq. (D10)).**
The target `⟨ψ|e^{iHT}Oe^{-iHT}|ψ⟩` is estimated up to `ε` with probability at least
`1-δ` by `M ≤ e^{2dν}(4 log(2/δ)/ε² + 2)` independent runs, each taking
`O(∥H∥T + log(1/ε))` queries to `U_H` and `O(1)` to `U_O`, `O_ψ`.  The concentration
reduces to Theorem 14 / Theorem 15. -/
theorem theorem17_observable
    {X : Type} [Fintype X] [DecidableEq X]
    {d : ℕ} (ν : ℝ) (hν : 0 ≤ ν)
    (p : FinDist X) (o : X → ℝ) (target ε δ : ℝ)
    (hbound : ∀ x, |o x| ≤ 1) (hmean : p.expect o = target)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp (2 * d * ν) * (4 * Real.log (2 / δ) / ε ^ 2 + 2) ∧
      p.probEvent (fun seeds : Fin M → X => ε ≤ |FinDist.avg o seeds - target|) ≤ δ := by
  obtain ⟨M, hMpos, hMle, hprob⟩ :=
    theorem15_quartic_observable p o target ε δ hbound hmean hε hδ hδ1
  refine ⟨M, hMpos, ?_, hprob⟩
  have hexp : (1 : ℝ) ≤ Real.exp (2 * d * ν) := by
    apply Real.one_le_exp
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  have hLpos : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hB : (0 : ℝ) ≤ 4 * Real.log (2 / δ) / ε ^ 2 + 2 := by
    have h4L : 0 < 4 * Real.log (2 / δ) := by nlinarith [hLpos]
    have hq : 0 < 4 * Real.log (2 / δ) / ε ^ 2 := div_pos h4L hε2
    linarith
  have hstep : (4 * Real.log (2 / δ) / ε ^ 2 + 2) ≤
      Real.exp (2 * d * ν) * (4 * Real.log (2 / δ) / ε ^ 2 + 2) := by
    simpa using mul_le_mul_of_nonneg_right hexp hB
  nlinarith [hMle, hstep]

end Qatlib.Papers.EnsembleQSP26.EnsembleQSP
