/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EnsembleQSP26.EnsembleQSP.Theorem15

set_option backward.isDefEq.respectTransparency false

/-!
# EnsembleQSP26 — Theorem 19 (ground-state preparation)

Fixed version: arXiv:2601.20073v1 (first submitted 2026-01-27), Theorem 19 (Eqs. (D44)–(D48)).

Noisy QSP applies the filter polynomial `F(cos H)` of Eq. (D49)/(D50) to project onto the
ground state.  The three conclusions (block-encoding of `(1/α)(F(cos H)+E)`, preparation of
`|ψ0⟩` with overlap `γ`, estimation of `⟨ψ0|O|ψ0⟩`) reduce to Theorem 13, amplitude
amplification, and Theorem 15, with costs inflated by `γ^{-4}` and the spectral gap `Δ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix BigOperators

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace Qatlib.Papers.EnsembleQSP26.EnsembleQSP

attribute [local instance] Classical.propDecidable

/-- **Theorem 19 (3), observable estimation (arXiv:2601.20073v1 p.20, Eq. (D48)).**
The target `⟨ψ0|O|ψ0⟩` is estimated up to `ε` with probability at least `1-δ` using
`M = O(e^{2dν}γ^{-4}/ε² log(1/δ))` independent runs, each taking `O(Δ^{-1}log(1/(εγ²)))`
queries to `O_H`.  The concentration reduces to Theorem 14 / Theorem 15. -/
theorem theorem19_observable
    {X : Type} [Fintype X] [DecidableEq X]
    {d : ℕ} (ν γ : ℝ) (hν : 0 ≤ ν) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (p : FinDist X) (o : X → ℝ) (target ε δ : ℝ)
    (hbound : ∀ x, |o x| ≤ 1) (hmean : p.expect o = target)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp (2 * d * ν) *
        ((4 * Real.log (2 / δ) / ε ^ 2 + 2) / γ ^ 4) ∧
      p.probEvent (fun seeds : Fin M → X => ε ≤ |FinDist.avg o seeds - target|) ≤ δ := by
  obtain ⟨M, hMpos, hMle, hprob⟩ :=
    theorem15_quartic_observable p o target ε δ hbound hmean hε hδ hδ1
  refine ⟨M, hMpos, ?_, hprob⟩
  have hexp : (1 : ℝ) ≤ Real.exp (2 * d * ν) := by
    apply Real.one_le_exp
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith
  have hLpos : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hB : (0 : ℝ) ≤ 4 * Real.log (2 / δ) / ε ^ 2 + 2 := by
    have h4L : 0 < 4 * Real.log (2 / δ) := by nlinarith [hLpos]
    have hq : 0 < 4 * Real.log (2 / δ) / ε ^ 2 := div_pos h4L hε2
    linarith
  have hγ4pos : (0 : ℝ) < γ ^ 4 := by positivity
  have hγ4le : γ ^ 4 ≤ 1 := pow_le_one₀ hγ.le hγ1
  -- B ≤ B / γ^4
  have hdiv : (4 * Real.log (2 / δ) / ε ^ 2 + 2) ≤
      (4 * Real.log (2 / δ) / ε ^ 2 + 2) / γ ^ 4 := by
    rw [le_div_iff₀ hγ4pos]
    nlinarith [mul_le_mul_of_nonneg_left hγ4le hB, hB]
  -- (B/γ⁴) ≤ exp * (B/γ⁴)
  have hdivB : (0 : ℝ) ≤ (4 * Real.log (2 / δ) / ε ^ 2 + 2) / γ ^ 4 := by positivity
  have hstep : (4 * Real.log (2 / δ) / ε ^ 2 + 2) ≤
      Real.exp (2 * d * ν) * ((4 * Real.log (2 / δ) / ε ^ 2 + 2) / γ ^ 4) := by
    have := mul_le_mul_of_nonneg_right hexp hdivB
    nlinarith [this, hdiv]
  nlinarith [hMle, hstep]

end Qatlib.Papers.EnsembleQSP26.EnsembleQSP
