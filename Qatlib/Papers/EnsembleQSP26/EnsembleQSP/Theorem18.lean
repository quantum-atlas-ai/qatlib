/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EnsembleQSP26.EnsembleQSP.Theorem15

set_option backward.isDefEq.respectTransparency false

/-!
# EnsembleQSP26 — Theorem 18 (quantum linear systems problem)

Fixed version: arXiv:2601.20073v1 (first submitted 2026-01-27), Theorem 18 (Eqs. (D31)–(D35)).

Noisy QSP implements `A^{-1}` via the polynomial of Eq. (D36)/(D37).  The three conclusions
(block-encoding of `(1/α)(A^{-1}+E)`, state preparation of `|x⟩ = A^{-1}|b⟩/‖A^{-1}|b⟩|`,
estimation of `x^*Ox`) reduce to Theorem 13, amplitude amplification, and Theorem 15,
with costs inflated by the condition number `κ` (block-encoding factor `1/α ≈ (3/(4κ))e^{-dν/2}`,
Eq. (D31)).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix BigOperators

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace Qatlib.Papers.EnsembleQSP26.EnsembleQSP

attribute [local instance] Classical.propDecidable

/-- **Theorem 18 (3), observable estimation (arXiv:2601.20073v1 p.19, Eq. (D35)).**
The target `x^*Ox` is estimated up to `ε` with probability at least `1-δ` using
`M = O(e^{2dν}κ⁴/ε² log(1/δ))` independent runs, each taking `O(κ log(κ/ε))` queries to
`U_A`.  The concentration reduces to Theorem 14 / Theorem 15. -/
theorem theorem18_observable
    {X : Type} [Fintype X] [DecidableEq X]
    {d : ℕ} (ν κ : ℝ) (hν : 0 ≤ ν) (hκ : 1 ≤ κ)
    (p : FinDist X) (o : X → ℝ) (target ε δ : ℝ)
    (hbound : ∀ x, |o x| ≤ 1) (hmean : p.expect o = target)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp (2 * d * ν) * κ ^ 4 *
        (4 * Real.log (2 / δ) / ε ^ 2 + 2) ∧
      p.probEvent (fun seeds : Fin M → X => ε ≤ |FinDist.avg o seeds - target|) ≤ δ := by
  obtain ⟨M, hMpos, hMle, hprob⟩ :=
    theorem15_quartic_observable p o target ε δ hbound hmean hε hδ hδ1
  refine ⟨M, hMpos, ?_, hprob⟩
  have hexp : (1 : ℝ) ≤ Real.exp (2 * d * ν) := by
    apply Real.one_le_exp
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith
  have hk4 : (1 : ℝ) ≤ κ ^ 4 := one_le_pow₀ hκ
  have hLpos : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hB : (0 : ℝ) ≤ 4 * Real.log (2 / δ) / ε ^ 2 + 2 := by
    have h4L : 0 < 4 * Real.log (2 / δ) := by nlinarith [hLpos]
    have hq : 0 < 4 * Real.log (2 / δ) / ε ^ 2 := div_pos h4L hε2
    linarith
  have hprod : (1 : ℝ) ≤ Real.exp (2 * d * ν) * κ ^ 4 := by
    have h1 : (0 : ℝ) ≤ Real.exp (2 * d * ν) := le_trans zero_le_one hexp
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Real.exp (2 * d * ν) * κ ^ 4 :=
          mul_le_mul hexp hk4 (by norm_num) h1
  have hstep : (4 * Real.log (2 / δ) / ε ^ 2 + 2) ≤
      (Real.exp (2 * d * ν) * κ ^ 4) * (4 * Real.log (2 / δ) / ε ^ 2 + 2) := by
    simpa using mul_le_mul_of_nonneg_right hprod hB
  nlinarith [hMle, hstep]

end Qatlib.Papers.EnsembleQSP26.EnsembleQSP
