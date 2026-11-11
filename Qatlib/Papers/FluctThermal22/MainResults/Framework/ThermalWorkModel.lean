/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixExpTrace.ExpPerturbation
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Fluctuation-theorem work model for `FluctThermal22`

Fixed source: arXiv:2203.08882 (accepted in Quantum 2022-08-22),
"Quantum algorithms from fluctuation theorems: Thermal-state preparation".

This module builds the *mathematical objects* that all of the paper's
statements are phrased in:

* the Gibbs state `ρ(β,H) = e^{-βH}/tr(e^{-βH})` and its partition function,
* the two-time measurement work probability `p_{m,n}` of Eq. (12) / Eq. (27),
  built from Boltzmann weights and the squared overlaps `|⟨φ_{1,n}|U|φ_{0,m}⟩|²`,
* the grouped work distribution `P(w)` and the left tail `Σ_{w<w_l} …`,
* the free-energy difference `ΔA(β) = -(1/β) log(Z1/Z0)` of Thm. 1.6.

All objects are finite sums over an index type `ι` (the system dimension), so
every statement below is a concrete, checkable real-valued identity or
inequality; no measure theory or infinite-dimensional Hilbert space is used.
The convention `V n m = ⟨φ_{1,n}|U|φ_{0,m}⟩` is the paper's overlap matrix.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace Qatlib.Papers.FluctThermal22.MainResults.Framework

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Eigenvalue-level objects -/

/-- Boltzmann weight `e^{-β ε_i}`.  (Paper Eq. (13), (23).) -/
def boltzmannWeight (β : ℝ) (ε : ι → ℝ) (i : ι) : ℝ := Real.exp (-β * ε i)

/-- Partition function computed from an eigenvalue list, `Z = Σ_i e^{-β ε_i}`.
(Paper Eq. (2), (15).) -/
def eigenPartition (β : ℝ) (ε : ι → ℝ) : ℝ := ∑ i, boltzmannWeight β ε i

/-- The work value `w_{m,n} = ε_{1,n} - ε_{0,m}`.  (Paper Sec. 2.2, below Eq. (25).) -/
def workValue (ε0 ε1 : ι → ℝ) (m n : ι) : ℝ := ε1 n - ε0 m

/-- The joint two-time probability `p_{m,n} = P(ε_{1,n}|ε_{0,m}) P_0(ε_{0,m})`
with `P(ε_{1,n}|ε_{0,m}) = |⟨φ_{1,n}|U|φ_{0,m}⟩|²` and the Boltzmann marginal.
Here `V n m` is the overlap `⟨φ_{1,n}|U|φ_{0,m}⟩`.  (Paper Eq. (26), (27).) -/
def twoTimeProb (β : ℝ) (ε0 : ι → ℝ) (V : Matrix ι ι ℂ) (m n : ι) : ℝ :=
  boltzmannWeight β ε0 m / eigenPartition β ε0 * Complex.normSq (V n m)

/-! ## Matrix-level objects -/

/-- The Gibbs/thermal state `ρ(β,H) = e^{-βH} / tr(e^{-βH})`.  (Paper Eq. (2).) -/
def gibbsState (β : ℝ) (H : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (((Matrix.trace (NormedSpace.exp ((-(β : ℝ)) • H))).re : ℂ)⁻¹) •
    NormedSpace.exp ((-(β : ℝ)) • H)

/-- The partition function `Z(β,H) = tr(e^{-βH})`, read as the real part of the
trace (which is real for Hermitian `H`).  (Paper Eq. (2).) -/
def partitionFun (β : ℝ) (H : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (NormedSpace.exp ((-(β : ℝ)) • H))).re

/-- The free-energy difference `ΔA(β) = -(1/β) log(Z1/Z0)`.  (Paper Thm. 1.2/1.6.) -/
def freeEnergyDiff (β : ℝ) (Z0 Z1 : ℝ) : ℝ := -(1 / β) * Real.log (Z1 / Z0)

/-! ## Work distribution, tails, and the cutoff functional of Eq. (4) -/

/-- The left tail `Σ_{w<w_l} P(w)`.  Since `P(w)` groups pairs with equal work,
this equals the double sum over pairs with `w_{m,n} < w_l`.  (Paper Eq. (12).) -/
def workTail (β wl : ℝ) (ε0 ε1 : ι → ℝ) (V : Matrix ι ι ℂ) : ℝ :=
  ∑ m, ∑ n, if workValue ε0 ε1 m n < wl then twoTimeProb β ε0 V m n else 0

/-- The exponentially-weighted left tail `Σ_{w<w_l} P(w) e^{-βw}`. -/
def workTailWeighted (β wl : ℝ) (ε0 ε1 : ι → ℝ) (V : Matrix ι ι ℂ) : ℝ :=
  ∑ m, ∑ n, if workValue ε0 ε1 m n < wl then
    twoTimeProb β ε0 V m n * Real.exp (-β * workValue ε0 ε1 m n) else 0

/-- The full weighted work sum `Σ_w P(w) e^{-βw}`, whose value is `Z1/Z0` by the
Jarzynski equality `jarzynski` below.  (Paper Eq. (13)–(16).) -/
def fullWorkWeight (β : ℝ) (ε0 ε1 : ι → ℝ) (V : Matrix ι ι ℂ) : ℝ :=
  ∑ m, ∑ n, twoTimeProb β ε0 V m n * Real.exp (-β * workValue ε0 ε1 m n)

/-- The left-hand side of the work-cutoff condition Eq. (4):
`Σ_{w<w_l} P(w) e^{-β(w-ΔA)}`. -/
def cutoffSum (β wl : ℝ) (ε0 ε1 : ι → ℝ) (V : Matrix ι ι ℂ) (ΔA : ℝ) : ℝ :=
  ∑ m, ∑ n, if workValue ε0 ε1 m n < wl then
    twoTimeProb β ε0 V m n *
      Real.exp (-β * (workValue ε0 ε1 m n - ΔA)) else 0

/-! ## Elementary positivity and the diagonal (`U = 1`) specialisation -/

/-- Boltzmann weights are strictly positive. -/
theorem boltzmannWeight_pos (β : ℝ) (ε : ι → ℝ) (i : ι) :
    0 < boltzmannWeight β ε i := Real.exp_pos _

/-- A joint two-time probability is nonnegative. -/
theorem twoTimeProb_nonneg [Nonempty ι] (β : ℝ) (ε0 : ι → ℝ) (V : Matrix ι ι ℂ)
    (m n : ι) : 0 ≤ twoTimeProb β ε0 V m n := by
  unfold twoTimeProb
  have hZ : 0 < eigenPartition β ε0 := by
    unfold eigenPartition
    exact Finset.sum_pos (fun i _ => boltzmannWeight_pos β ε0 i) Finset.univ_nonempty
  have h1 : 0 ≤ boltzmannWeight β ε0 m / eigenPartition β ε0 :=
    div_nonneg (boltzmannWeight_pos β ε0 m).le hZ.le
  exact mul_nonneg h1 (Complex.normSq_nonneg _)

/-- For the trivial driving unitary `U = 1`, the overlap matrix is the identity
and the joint probability is diagonal, with the Boltzmann weight on the
diagonal.  (Paper Thm. 1.4, `U = 1l`.) -/
theorem twoTimeProb_identity (β : ℝ) (ε0 : ι → ℝ) (m n : ι) :
    twoTimeProb β ε0 (1 : Matrix ι ι ℂ) m n =
      if n = m then boltzmannWeight β ε0 m / eigenPartition β ε0 else 0 := by
  unfold twoTimeProb
  rw [Matrix.one_apply]
  by_cases h : n = m
  · rw [if_pos h, if_pos h]
    simp
  · rw [if_neg h, if_neg h]
    simp


/-- **Jarzynski equality** (paper Eq. (13)–(16), page 10):
`Σ_w P(w) e^{-βw} = Z1/Z0`, for any overlap matrix `V` whose rows are
orthonormal (`U` unitary).  This is the fluctuation-theorem identity that
underlies every cutoff statement. -/
theorem jarzynski [Nonempty ι] (β : ℝ) (ε0 ε1 : ι → ℝ) (V : Matrix ι ι ℂ)
    (hV : ∀ n, ∑ m, Complex.normSq (V n m) = 1) :
    fullWorkWeight β ε0 ε1 V = eigenPartition β ε1 / eigenPartition β ε0 := by
  have hZne : eigenPartition β ε0 ≠ 0 := by
    unfold eigenPartition
    exact ne_of_gt (Finset.sum_pos (fun i _ => boltzmannWeight_pos β ε0 i) Finset.univ_nonempty)
  have hterm : ∀ m n,
      twoTimeProb β ε0 V m n * Real.exp (-β * workValue ε0 ε1 m n)
        = (eigenPartition β ε0)⁻¹ *
            (Real.exp (-β * ε1 n) * Complex.normSq (V n m)) := by
    intro m n
    unfold twoTimeProb workValue boltzmannWeight
    rw [show Real.exp (-β * (ε1 n - ε0 m))
          = Real.exp (-β * ε1 n) * Real.exp (β * ε0 m) by
        rw [← Real.exp_add]; congr 1; ring]
    have hB : Real.exp (β * ε0 m) = (Real.exp (-β * ε0 m))⁻¹ := by
      have h := Real.exp_neg (-(β * ε0 m))
      simpa using h
    rw [hB]
    have h1 : Real.exp (-β * ε0 m) ≠ 0 := Real.exp_ne_zero _
    field_simp
  unfold fullWorkWeight
  rw [Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => hterm m n))]
  calc
    ∑ m, ∑ n, (eigenPartition β ε0)⁻¹ * (Real.exp (-β * ε1 n) * Complex.normSq (V n m))
        = ∑ n, ∑ m, (eigenPartition β ε0)⁻¹ * (Real.exp (-β * ε1 n) * Complex.normSq (V n m)) :=
          Finset.sum_comm
    _ = ∑ n, (eigenPartition β ε0)⁻¹ * Real.exp (-β * ε1 n) * ∑ m, Complex.normSq (V n m) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          ring
    _ = ∑ n, (eigenPartition β ε0)⁻¹ * Real.exp (-β * ε1 n) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [hV n, mul_one]
    _ = eigenPartition β ε1 / eigenPartition β ε0 := by
          rw [div_eq_mul_inv, mul_comm]
          unfold eigenPartition boltzmannWeight
          rw [Finset.mul_sum]

end Qatlib.Papers.FluctThermal22.MainResults.Framework
