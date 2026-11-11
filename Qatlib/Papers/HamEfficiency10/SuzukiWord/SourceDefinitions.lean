/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.MatrixExponentialApproximation
import Qatlib.Concepts.TrotterFormula.SuzukiFourth.SuzukiFourthOrder
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# HamEfficiency10 — source model for Suzuki splitting bounds

Fixed paper version: arXiv:1005.1318 (2010),
"On the Efficiency of Quantum Algorithms for Hamiltonian Simulation".
Plain text: `prove/assets/1005.1318.txt`;
PDF: `prove/assets/1005.1318.pdf`.

The paper studies Suzuki's recursive splitting `S_{2k}` for
`exp(-i(H_1 + ... + H_m)Δt)` and its exponential cost.  This file gives the
paper-layer model.  Hamiltonians are honest finite-dimensional Hermitian
matrices and the evolution is the actual Banach-algebra exponential
`QuantumAlgorithm.Papers.HamSimQSP17.Achievability.hamiltonianEvolution`
(L2 operator norm), so no numerical sampling or abstract operator algebra is
introduced.

`S_{2k}` is represented through the coefficient form of Eq. (5): a word of
`2K+1` exponentials whose real coefficients are the paper's `s_j` and `z_j`.
Lemma 1 only ever uses the two normalizations `∑ s_j = ∑ z_j = 1` and the mass
bound `∑|s_j| + ∑|z_j| ≤ c_k` (Eq. (6)); those are the fields of
`TwoTermSchedule`.  For the many-term word the corresponding coefficient data
are Eq. (30)–(31) of the Appendix.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.HamEfficiency10.SuzukiWord

open Qatlib.Concepts.QspSimulation.Achievability (hamiltonianEvolution)

/-- Paper Eq. (6), p. 5: the two-term Suzuki mass constant
`c_k = (8/3)·(5/3)^{k-1}`.  The paper uses `k ≥ 1`; the definition also makes
sense at `k = 0`. -/
noncomputable def scalingConstant (k : ℕ) : ℝ :=
  (8 / 3 : ℝ) * (5 / 3 : ℝ) ^ (k - 1)

/-- Paper Eq. (30), p. 13 (Appendix): the many-term mass constant
`d_k = m·(4/3)^k·(5/3)^{k-1}`. -/
noncomputable def manyTermScalingConstant (m k : ℕ) : ℝ :=
  (m : ℝ) * (4 / 3 : ℝ) ^ k * (5 / 3 : ℝ) ^ (k - 1)

/-- `c_k` is strictly positive. -/
theorem scalingConstant_pos (k : ℕ) : 0 < scalingConstant k := by
  unfold scalingConstant
  positivity

/-- `d_k` is strictly positive for a nonempty number of terms. -/
theorem manyTermScalingConstant_pos {m k : ℕ} (hm : 0 < m) :
    0 < manyTermScalingConstant m k := by
  unfold manyTermScalingConstant
  have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  positivity

/-- The two-term Suzuki word of Eq. (5), p. 4.  It contains `2K+1` factors,
in the paper's left-to-right order
`e^{-iH₁s₀Δt} e^{-iH₂z₁Δt} e^{-iH₁s₁Δt} ⋯ e^{-iH₂z_KΔt} e^{-iH₁s_KΔt}`. -/
noncomputable def twoTermWord {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) :
    (K : ℕ) → (Fin K → ℝ) → (Fin (K + 1) → ℝ) → ℝ → Matrix I I ℂ
  | 0, _, s, dt => hamiltonianEvolution A (s 0 * dt)
  | K + 1, z, s, dt =>
      hamiltonianEvolution A (s 0 * dt) * hamiltonianEvolution B (z 0 * dt) *
        twoTermWord A B K (fun j => z j.succ) (fun j => s j.succ) dt

/-- The coefficient data of the `S_{2k}` construction used in Lemma 1
(Eq. (5)–(6), pp. 4–5): `K = 5^{k-1}` blocks with coefficient families
`z₁, …, z_K` and `s₀, …, s_K` satisfying the two normalizations and the mass
bound `σ_k ≤ c_k`.  Lemma 1's proof only uses these three facts. -/
structure TwoTermSchedule (k : ℕ) where
  /-- The `z` coefficients of the `H₂` factors. -/
  z : Fin (5 ^ (k - 1)) → ℝ
  /-- The `s` coefficients of the `H₁` factors. -/
  s : Fin (5 ^ (k - 1) + 1) → ℝ
  /-- Eq. (5): the `z` coefficients sum to one. -/
  sum_z : (∑ j, z j) = 1
  /-- Eq. (5): the `s` coefficients sum to one. -/
  sum_s : (∑ j, s j) = 1
  /-- Eq. (6): the total mass `σ_k` is at most `c_k`. -/
  mass_le : (∑ j, |s j|) + (∑ j, |z j|) ≤ scalingConstant k

/-- An arbitrary product word over a list of `(coefficient, generator)` pairs,
used for the many-term Suzuki word of Section III. -/
noncomputable def manyTermWord {I : Type*} [Fintype I] [DecidableEq I]
    {m : ℕ} (H : Fin m → Matrix I I ℂ) (w : List (ℝ × Fin m)) (dt : ℝ) :
    Matrix I I ℂ :=
  (w.map (fun p => hamiltonianEvolution (H p.2) (p.1 * dt))).prod

/-- Coefficient data for the many-term `S_{2k}` of Section III.
Besides the mass bound Eq. (31), each generator's coefficients sum to one
(the second display after Eq. (30), p. 13). -/
structure ManyTermSchedule (m k : ℕ) where
  /-- The ordered list of `(coefficient, generator index)` pairs. -/
  word : List (ℝ × Fin m)
  /-- Eq. (31): the total coefficient mass is at most `d_k`. -/
  mass_le : (word.map (fun p => |p.1|)).sum ≤ manyTermScalingConstant m k
  /-- Coefficient normalisation for every generator. -/
  sum_one : ∀ j : Fin m, ((word.filter (fun p => p.2 = j)).map (fun p => p.1)).sum = 1

/-- The subinterval length parameter `M` of Theorem 1's proof (p. 8):
`(8et‖H₂‖/ε)^{1/(2k)} · 2e·c_k/(2k+1)`. -/
noncomputable def theorem1SubM {I : Type*} [Fintype I] [DecidableEq I]
    (_A B : Matrix I I ℂ) (k : ℕ) (t ε : ℝ) : ℝ :=
  (8 * Real.exp 1 * t * ‖B‖ / ε) ^ (1 / (2 * (k : ℝ))) *
    (2 * Real.exp 1 * scalingConstant k / (2 * (k : ℝ) + 1))

/-- Number of subintervals used by the Theorem 1 algorithm
(`⌈M‖H₁‖t⌉`, with the `M‖H₁‖t < 1` case collapsed to one subinterval). -/
noncomputable def theorem1Subintervals {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (k : ℕ) (t ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (theorem1SubM A B k t ε * ‖A‖ * t))

/-- The paper's closed-form bracket in Theorem 1, Eq. (23), p. 8. -/
noncomputable def theorem1BoundArg {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (k : ℕ) (t ε : ℝ) : ℝ :=
  ‖A‖ * t * (8 * Real.exp 1 * t * ‖B‖ / ε) ^ (1 / (2 * (k : ℝ))) *
    (8 * Real.exp 1 / 3) * (5 / 3 : ℝ) ^ (k - 1)

/-- The subinterval parameter `M` of Theorem 2's proof (p. 10):
`(4emt‖H₂‖/ε)^{1/(2k)} · 2e·d_k/(2k+1)`.  `A1`/`A2` are the largest and
second-largest generators `H₁`/`H₂`. -/
noncomputable def theorem2SubM {I : Type*} [Fintype I] [DecidableEq I]
    (_A1 A2 : Matrix I I ℂ) (m k : ℕ) (t ε : ℝ) : ℝ :=
  (4 * (m : ℝ) * Real.exp 1 * t * ‖A2‖ / ε) ^ (1 / (2 * (k : ℝ))) *
    (2 * Real.exp 1 * manyTermScalingConstant m k / (2 * (k : ℝ) + 1))

/-- Number of subintervals used by the Theorem 2 algorithm. -/
noncomputable def theorem2Subintervals {I : Type*} [Fintype I] [DecidableEq I]
    (A1 A2 : Matrix I I ℂ) (m k : ℕ) (t ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (theorem2SubM A1 A2 m k t ε * ‖A1‖ * t))

/-- The paper's closed-form bracket in Theorem 2, Eq. (23) analogue, p. 10. -/
noncomputable def theorem2BoundArg {I : Type*} [Fintype I] [DecidableEq I]
    (A1 A2 : Matrix I I ℂ) (m k : ℕ) (t ε : ℝ) : ℝ :=
  ‖A1‖ * t * (4 * (m : ℝ) * Real.exp 1 * t * ‖A2‖ / ε) ^
      (1 / (2 * (k : ℝ))) * (4 * (m : ℝ) * Real.exp 1 / 3) * (5 / 3 : ℝ) ^ (k - 1)

end Qatlib.Papers.HamEfficiency10.SuzukiWord
