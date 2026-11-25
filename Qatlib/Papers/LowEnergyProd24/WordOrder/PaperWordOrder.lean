/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LowEnergyProd24.CenterTransport.PhysicalWord
public import Qatlib.Concepts.TrotterFormula.GeneralOrder.GeneralTrotterOrderConsumers
public import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterDefectAlgebra
public import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.Centering

@[expose] public section

/-!
# The ordered product word at the general word-order theorem

Fixed paper version: arXiv:2402.10362v1 (K. Hejazi, M. Shokrian Zini, J. M. Arrazola,
11 pages), [arXiv:2402.10362v1](https://arxiv.org/abs/2402.10362v1).

Source: p. 2, Eq. (2), the ordered product `W(s) = e^{-i H_m s} ⋯ e^{-i H_1 s}` of the paper's
grouped stages, and p. 7, Eq. (22), the statement that the local error of `W(s)` is of order
`s ^ (p + 1)` once the generator coefficients below degree `p` cancel.

`Qatlib.Concepts.TrotterFormula.GeneralOrder.general_trotter_word_order` proves the local order
`p + 1` of an arbitrary finite ordered exponential word whose series coefficients
`Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzukiSeries` match those of `exp (t • H)` through
degree `p`.  This module transports that theorem to the paper's word: the two bridge lemmas
`approximate_eq_suzukiExponentialWord` and `evolve_eq_exp_totalGenerator` identify the paper's
`approximate`/`evolve` with the generic word and exponential, `paper_word_order_of_series_matching`
states Eq. (22) for the paper's word under the coefficient matching hypothesis, and
`paper_word_order_one` discharges that hypothesis at order one directly from the paper's
`lowerOrderCancellation` predicate, using
`Qatlib.Concepts.TrotterFormula.GeneralOrder.pf_word_series_one` and
`Qatlib.Foundations.MatrixAlgebra.CommutatorExp.generatorCoefficient_zero`.

Boundary: `lowerOrderCancellation` constrains the *generator* coefficients
`physicalCoefficient h stages n` below degree `p`, whereas `general_trotter_word_order` consumes
matching of the *word* coefficients `suzukiSeries` below degree `p`.  The two predicates agree
through degree one, which is what `paper_word_order_one` proves; for `2 ≤ p` the implication is
the coefficient recurrence of the word's logarithmic derivative and is not proved here, so the
Eq. (22) statement for general `p` is conditional on `hmatch`.  No statement about the leakage
exponent or about the small-step hypothesis `2 J k d (timeBudget stages) s < 1` is made; the
statements below are local in `t` and carry no positivity hypothesis on `J`, `k`, `d`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.LowEnergyProd24.WordOrder

open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.CenterTransport
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff

variable {N R M k d : ℕ} {J : ℝ}

/-- The list-ordered product of matrix exponentials agrees with the generic coefficient-series
word `suzukiExponentialWord` used by the general word-order theorem. -/
theorem word_eq_suzukiExponentialWord {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (t : ℝ) :
    word xs t = suzukiExponentialWord xs t := by
  induction xs with
  | nil => simp [word, suzukiExponentialWord]
  | cons X xs ih => simp [word, suzukiExponentialWord, ih]

/-- The paper's ordered product word `approximate h stages t` is the generic exponential word of
the mapped stage generators. -/
theorem approximate_eq_suzukiExponentialWord (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (t : ℝ) :
    approximate h stages t = suzukiExponentialWord (stages.map (stageGenerator h)) t :=
  word_eq_suzukiExponentialWord _ t

/-- The paper's exact evolution `evolve h.total t` is the exponential of `t` times the total
generator `-i H` of Eq. (2). -/
theorem evolve_eq_exp_totalGenerator (h : PhysicalHamiltonian N R M k d J) (t : ℝ) :
    evolve h.total t = NormedSpace.exp (t • totalGenerator h) := by
  rw [evolve]
  congr 1
  ext i j
  simp only [totalGenerator, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  ring

/-- Eq. (22) for the paper's word: if the word coefficients through degree `p` match those of
`exp (t • totalGenerator h)`, then the ordered product `approximate h stages` differs from the
exact evolution `evolve h.total` by `O (t ^ (p + 1))` near zero. -/
theorem paper_word_order_of_series_matching (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (p : ℕ)
    (hmatch : ∀ n : ℕ, n ≤ p →
      suzukiSeries (stages.map (stageGenerator h)) n =
        ((n.factorial : ℝ)⁻¹) • totalGenerator h ^ n) :
    trotterOrder (fun t => approximate h stages t - evolve h.total t) (p + 1) := by
  have hg := general_trotter_word_order (stages.map (stageGenerator h)) (totalGenerator h) p hmatch
  simpa only [approximate_eq_suzukiExponentialWord, evolve_eq_exp_totalGenerator] using hg

/-- At order one the paper's generator cancellation implies the series matching consumed by the
general word-order theorem: the degree-zero and degree-one word coefficients of the stage
generators are the total generator, and the coefficients of degree at least two are free. -/
theorem series_matching_one (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (horder : lowerOrderCancellation h stages 1) :
    ∀ n : ℕ, n ≤ 1 →
      suzukiSeries (stages.map (stageGenerator h)) n =
        ((n.factorial : ℝ)⁻¹) • totalGenerator h ^ n := by
  intro n hn
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · simp
  · rw [pf_word_series_one]
    have h0 := horder 0 (by norm_num)
    rw [physicalCoefficient, generatorCoefficient_zero] at h0
    simpa using h0

/-- Eq. (22) at order one: lower-order cancellation through degree one gives local error
`O (t ^ 2)` for the paper's ordered product word. -/
theorem paper_word_order_one (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (horder : lowerOrderCancellation h stages 1) :
    trotterOrder (fun t => approximate h stages t - evolve h.total t) 2 :=
  paper_word_order_of_series_matching h stages 1 (series_matching_one h stages horder)

end Qatlib.Papers.LowEnergyProd24.WordOrder
