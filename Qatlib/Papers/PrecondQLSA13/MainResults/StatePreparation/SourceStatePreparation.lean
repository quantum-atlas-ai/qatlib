/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# StatePreparation — source interface for the generic-state preparation of PrecondQLSA13

Clader--Jacobs--Sprouse, *Preconditioned quantum linear system algorithm*,
fixed arXiv:1301.2340v4 (2013-05-07). Source location: p. 2, Eqs. (5)--(7).

Eq. (7) prepares three registers plus one ancilla in the branch state

  `|Psi> = 1/sqrt(N) Σ_j e^{i φ_j} |j> ( sqrt(1 - C_b^2 b_j^2) |0>_a + C_b b_j |1>_a )`

and the paper identifies it with the state `|b_T> = cos φ_b |b~>|0>_a + sin φ_b |b>|1>_a`
of Eq. (5), where

  `sin^2 φ_b = C_b^2/N Σ_j b_j^2`,  `cos^2 φ_b = 1/N Σ_j (1 - C_b^2 b_j^2)`,

  `|b~> = 1/(sqrt(N) cos φ_b) Σ_j sqrt(1 - C_b^2 b_j^2) e^{i φ_j} |j>`,

  `|b>   = C_b/(sqrt(N) sin φ_b) Σ_j b_j e^{i φ_j} |j>`.

This module records the amplitude algebra behind that identification on a finite
index set `Fin N`: the total branch weight is one, the two branch weights are
exactly the paper's `sin^2 φ_b`/`cos^2 φ_b`, and the conditioned amplitudes are
exactly the normalised `|b>` and `|b~>` amplitudes. Unit-modulus complex phases
`e^{i φ_j}` multiply probabilities by one.

Boundary: this is the amplitude-level state-preparation algebra. Oracle
efficiency of computing `b_j`, `φ_j` is the algorithmic premise of the paper and
is not formalised here; the statement assumes the oracle outputs are given.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.PrecondQLSA13.MainResults.StatePreparation

/-- Eq. (7): the total weight of the `|1>_a` branch,
`sin^2 φ_b = C_b^2/N · Σ_j b_j^2`. -/
def successWeight (N : ℕ) (Cb : ℝ) (b : Fin N → ℝ) : ℝ :=
  Cb ^ 2 / (N : ℝ) * ∑ j, (b j) ^ 2

/-- Eq. (7): the total weight of the `|0>_a` branch,
`cos^2 φ_b = 1/N · Σ_j (1 - C_b^2 b_j^2)`. -/
def failWeight (N : ℕ) (Cb : ℝ) (b : Fin N → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ j, (1 - Cb ^ 2 * (b j) ^ 2)

/-- Eq. (7), first register amplitude of the `|1>_a` branch:
`1/sqrt(N) · C_b b_j`. -/
def oneBranchWeight (N : ℕ) (Cb : ℝ) (b : Fin N → ℝ) (j : Fin N) : ℝ :=
  (1 / (N : ℝ)) * (Cb * b j) ^ 2

/-- Eq. (7), first register amplitude of the `|0>_a` branch:
`1/sqrt(N) · sqrt(1 - C_b^2 b_j^2)`. -/
def zeroBranchWeight (N : ℕ) (Cb : ℝ) (b : Fin N → ℝ) (j : Fin N) : ℝ :=
  (1 / (N : ℝ)) * (1 - Cb ^ 2 * (b j) ^ 2)

/-- Fixed arXiv:1301.2340v4, Eq. (7), p. 2: the two branch weights sum to one,
so Eq. (7) is a normalised two-branch state. This is the algebraic content of
"State (7) is exactly the state (5)". -/
theorem successWeight_add_failWeight {N : ℕ} (hN : 0 < N)
    (Cb : ℝ) (b : Fin N → ℝ) :
    successWeight N Cb b + failWeight N Cb b = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hN)
  unfold successWeight failWeight
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  rw [← Finset.mul_sum]
  field_simp
  ring

/-- Fixed arXiv:1301.2340v4, Eq. (7), p. 2: `sin^2 φ_b` is nonnegative
(assuming `C_b` is a real normalisation constant). -/
theorem successWeight_nonneg {N : ℕ} (Cb : ℝ) (b : Fin N → ℝ)
    (hCb : 0 ≤ Cb) (hN : 0 ≤ (N : ℝ)) :
    0 ≤ successWeight N Cb b := by
  unfold successWeight
  have hsum : 0 ≤ ∑ j : Fin N, (b j) ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg (b j))
  have hcoef : 0 ≤ Cb ^ 2 / (N : ℝ) := by positivity
  exact mul_nonneg hcoef hsum

/-- Fixed arXiv:1301.2340v4, Eq. (7), p. 2: the rotation-existence hypothesis
`|C_b b_j| ≤ 1` makes every `1 - C_b^2 b_j^2` nonnegative, hence so is
`cos^2 φ_b`. -/
theorem failWeight_nonneg {N : ℕ} (Cb : ℝ) (b : Fin N → ℝ)
    (hbound : ∀ j, |Cb * b j| ≤ 1) (hN : 0 ≤ (N : ℝ)) :
    0 ≤ failWeight N Cb b := by
  unfold failWeight
  have hterm : ∀ j : Fin N, 0 ≤ 1 - Cb ^ 2 * (b j) ^ 2 := by
    intro j
    have hsq : (Cb * b j) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]
      exact hbound j
    have hsq' : Cb ^ 2 * (b j) ^ 2 = (Cb * b j) ^ 2 := by ring
    nlinarith
  have hsum : 0 ≤ ∑ j : Fin N, (1 - Cb ^ 2 * (b j) ^ 2) :=
    Finset.sum_nonneg (fun j _ => hterm j)
  have hcoef : 0 ≤ 1 / (N : ℝ) := by positivity
  exact mul_nonneg hcoef hsum

/-- Fixed arXiv:1301.2340v4, Eq. (7), p. 2: summing the `|1>_a` register weights
over `j` gives `sin^2 φ_b`. -/
theorem oneBranchWeight_sum_eq_successWeight {N : ℕ} (Cb : ℝ) (b : Fin N → ℝ) :
    (∑ j : Fin N, oneBranchWeight N Cb b j) = successWeight N Cb b := by
  unfold oneBranchWeight successWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Fixed arXiv:1301.2340v4, Eq. (7), p. 2: summing the `|0>_a` register weights
over `j` gives `cos^2 φ_b`. -/
theorem zeroBranchWeight_sum_eq_failWeight {N : ℕ} (Cb : ℝ) (b : Fin N → ℝ) :
    (∑ j : Fin N, zeroBranchWeight N Cb b j) = failWeight N Cb b := by
  unfold zeroBranchWeight failWeight
  rw [Finset.mul_sum]

/-- Fixed arXiv:1301.2340v4, Eq. (7), p. 2: conditioned on the ancilla being
`|1>_a`, the register-`j` probability is exactly the squared amplitude of
`|b> = C_b/(sqrt N sin φ_b) Σ_j b_j e^{i φ_j}|j>`, with
`sin φ_b = sqrt (sin^2 φ_b)`. -/
theorem conditioned_one_amplitude_sq {N : ℕ} (hN : 0 < N)
    (Cb : ℝ) (b : Fin N → ℝ) (j : Fin N)
    (hs : 0 ≤ successWeight N Cb b) :
    oneBranchWeight N Cb b j / successWeight N Cb b =
      (Cb * b j / (Real.sqrt (N : ℝ) * Real.sqrt (successWeight N Cb b))) ^ 2 := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hden : (Real.sqrt (N : ℝ) * Real.sqrt (successWeight N Cb b)) ^ 2
      = (N : ℝ) * successWeight N Cb b := by
    rw [mul_pow, Real.sq_sqrt hNpos.le, Real.sq_sqrt hs]
  unfold oneBranchWeight
  rw [div_pow, hden]
  by_cases hs0 : successWeight N Cb b = 0
  · simp [hs0]
  · field_simp [hs0]

/-- Fixed arXiv:1301.2340v4, Eq. (7), p. 2: conditioned on the ancilla being
`|0>_a`, the register-`j` probability is exactly the squared amplitude of
`|b~> = 1/(sqrt N cos φ_b) Σ_j sqrt(1 - C_b^2 b_j^2) e^{i φ_j}|j>`, with
`cos φ_b = sqrt (cos^2 φ_b)`. -/
theorem conditioned_zero_amplitude_sq {N : ℕ} (hN : 0 < N)
    (Cb : ℝ) (b : Fin N → ℝ) (j : Fin N)
    (hz : 0 ≤ 1 - Cb ^ 2 * (b j) ^ 2)
    (hf : 0 ≤ failWeight N Cb b) :
    zeroBranchWeight N Cb b j / failWeight N Cb b =
      (Real.sqrt (1 - Cb ^ 2 * (b j) ^ 2) /
        (Real.sqrt (N : ℝ) * Real.sqrt (failWeight N Cb b))) ^ 2 := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hden : (Real.sqrt (N : ℝ) * Real.sqrt (failWeight N Cb b)) ^ 2
      = (N : ℝ) * failWeight N Cb b := by
    rw [mul_pow, Real.sq_sqrt hNpos.le, Real.sq_sqrt hf]
  unfold zeroBranchWeight
  rw [div_pow, hden, Real.sq_sqrt hz]
  by_cases hf0 : failWeight N Cb b = 0
  · simp [hf0]
  · field_simp [hf0]

/-- Fixed arXiv:1301.2340v4, Eq. (7), p. 2: the oracle phases `e^{i φ_j}` enter
only through unit-modulus factors, so they leave the branch weights unchanged.
`phase j` is the complex phase and `hphase` records `|e^{i φ_j}|^2 = 1`. -/
theorem phase_preserves_weight {N : ℕ} (phase : Fin N → ℂ) {r : ℝ} {j : Fin N}
    (hphase : Complex.normSq (phase j) = 1) :
    Complex.normSq (phase j * (r : ℂ)) = r ^ 2 := by
  rw [Complex.normSq_mul, hphase, Complex.normSq_ofReal, one_mul]
  ring

end Qatlib.Papers.PrecondQLSA13.MainResults.StatePreparation
