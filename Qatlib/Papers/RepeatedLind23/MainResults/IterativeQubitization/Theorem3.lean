/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RepeatedLind23.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# RepeatedLind23 c004 — Theorem 3 (Iterative Qubitization Complexity)

Fixed source: arXiv:2312.05371 (2023-12-08 posting), Theorem 3, Eq. (45) on
page 14, proof Eqs. (46)–(51) on pages 14–15.

The repeated-interaction map is implemented by Qubitization/QSVT, applying the
QSVT query bound of Eq. (48) to each of the `κ = mν` applications of the
`m`-interaction composite map (Eq. (14)) at interaction time `τ = t/ν`. The
per-map coefficient `1`-norm is Eq. (50),

`α_n = √(ν/t)·α_{I_n} + (1/m)(α₀ + ω_n)`,

so the total query count to the prepare/select oracles `P` (Eq. 40) and `S`
(Eq. 41) is

`q_PS ∈ O( max_n ((α₀ + mω_n)t + α_{I_n}·m·√(νt) + mν·log(1/ε)/log log(1/ε)) )`
(Eq. 45 / Eq. 51).

This file states Eq. (45) about the query-count model assembled from the frozen
QSVT per-step count, with the cited QSVT query bound (Refs. [34,35], Eq. (48))
entering through the explicit count `iterativeQubitizationCount` of
`SourceModel.lean`, and proves the final re-assembly step of the paper (Eqs.
(50)–(51)) in full.
-/

set_option autoImplicit false
noncomputable section

open Matrix Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open Qatlib.Papers.RepeatedLind23.MainResults
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Kronecker

namespace Qatlib.Papers.RepeatedLind23.MainResults.IterativeQubitization

/-- Eq. (45) / Eq. (51) right-hand side, as a function of the paper's data:
`max_n ((α₀ + mω_n)t + α_{I_n}·m·√(νt) + mν·log(1/ε)/log log(1/ε))`. -/
def theorem3QueryBound {m : ℕ} (hm : 0 < m) (α0 αI ω : Fin m → ℝ) (ν : ℕ)
    (t ε : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin m)).sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    (fun n =>
      (α0 n + (m : ℝ) * ω n) * t
        + αI n * (m : ℝ) * Real.sqrt ((ν : ℝ) * t)
        + (m : ℝ) * (ν : ℝ) * qsvtLogFactor ε)

/-- **Theorem 3** (Iterative Qubitization Complexity), arXiv:2312.05371,
Theorem 3 / Eq. (45), p. 14 (Eq. (51) in the proof).

For every number `m ≥ 1` of bath subsystems, every coefficient `1`-norms
`α₀, α_{I_n}, ω_n` (`ω_n ≥ 0`), every iteration count `ν > 0`, total time `t > 0`
and target error `ε > 0`, the query count `q_PS` to both oracles `P` (Eq. 40) and
`S` (Eq. 41), assembled as `κ = mν` applications of the per-step QSVT bound
Eq. (48) with the coefficient norms Eq. (50), is `O(max_n ((α₀ + mω_n)t +
α_{I_n}m√(νt) + mν log(1/ε)/log log(1/ε)))`, with a universal constant `C`.

The query count is the explicit `iterativeQubitizationCount` of
`SourceModel.lean`; the only external input is the QSVT query bound Eq. (48) of
Refs. [34,35], which is exactly how the paper proves Eq. (45). The proof below
formalises the re-assembly of Eqs. (50)–(51): the identity
`mν·√(ν/t)·(t/ν) = m√(νt)` and the pointwise comparison of the per-map count
with the final budget. -/
theorem theorem3_iterative_qubitization_complexity :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (hm : 0 < m) (α0 αI ω : Fin m → ℝ) (ν : ℕ) (t ε : ℝ),
        0 < t → 0 < ν → 0 < ε →
        (∀ n, 0 ≤ ω n) →
        iterativeQubitizationCount hm α0 αI ω ν t ε ≤
          C * theorem3QueryBound hm α0 αI ω ν t ε := by
  refine ⟨1, one_pos, ?_⟩
  intro m hm α0 αI ω ν t ε ht hν hε hω
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hν0 : (0 : ℝ) < (ν : ℝ) := by exact_mod_cast hν
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hM : (0 : ℝ) ≤ (m : ℝ) * (ν : ℝ) := le_of_lt (mul_pos hm0 hν0)
  -- The key identity of Eq. (50)–(51): `mν · √(ν/t) · (t/ν) = m·√(νt)`.
  have hsqrt : (m : ℝ) * (ν : ℝ) * (Real.sqrt ((ν : ℝ) / t) * (t / (ν : ℝ)))
      = (m : ℝ) * Real.sqrt ((ν : ℝ) * t) := by
    have hνt_nonneg : (0 : ℝ) ≤ (ν : ℝ) := le_of_lt hν0
    have ht_nonneg : (0 : ℝ) ≤ t := le_of_lt ht
    have hL : (0 : ℝ) ≤ (m : ℝ) * (ν : ℝ) *
        (Real.sqrt ((ν : ℝ) / t) * (t / (ν : ℝ))) := by positivity
    have hR : (0 : ℝ) ≤ (m : ℝ) * Real.sqrt ((ν : ℝ) * t) := by positivity
    refine (sq_eq_sq₀ hL hR).mp ?_
    have h1 : Real.sqrt ((ν : ℝ) / t) ^ 2 = (ν : ℝ) / t :=
      Real.sq_sqrt (div_nonneg hνt_nonneg ht_nonneg)
    have h2 : Real.sqrt ((ν : ℝ) * t) ^ 2 = (ν : ℝ) * t :=
      Real.sq_sqrt (mul_nonneg hνt_nonneg ht_nonneg)
    calc
      ((m : ℝ) * (ν : ℝ) * (Real.sqrt ((ν : ℝ) / t) * (t / (ν : ℝ)))) ^ 2
          = (m : ℝ) ^ 2 * (ν : ℝ) ^ 2 * (Real.sqrt ((ν : ℝ) / t)) ^ 2
              * (t / (ν : ℝ)) ^ 2 := by ring
      _ = (m : ℝ) ^ 2 * (ν : ℝ) ^ 2 * ((ν : ℝ) / t) * (t / (ν : ℝ)) ^ 2 := by
        rw [h1]
      _ = (m : ℝ) ^ 2 * ((ν : ℝ) * t) := by
        field_simp
      _ = (m : ℝ) ^ 2 * (Real.sqrt ((ν : ℝ) * t)) ^ 2 := by rw [h2]
      _ = ((m : ℝ) * Real.sqrt ((ν : ℝ) * t)) ^ 2 := by ring
  -- Pointwise comparison of the per-map budget with the final Eq. (45) bound.
  have key : ∀ n : Fin m,
      (m : ℝ) * (ν : ℝ) *
          (stepAlphaNorm (α0 n) (αI n) (ω n) m ν t * (t / (ν : ℝ)) + qsvtLogFactor ε)
        ≤ (α0 n + (m : ℝ) * ω n) * t
            + αI n * (m : ℝ) * Real.sqrt ((ν : ℝ) * t)
            + (m : ℝ) * (ν : ℝ) * qsvtLogFactor ε := by
    intro n
    have hB : (m : ℝ) * (ν : ℝ) * ((1 / (m : ℝ)) * (α0 n + ω n) * (t / (ν : ℝ)))
        = t * (α0 n + ω n) := by
      field_simp
    have hexp : (m : ℝ) * (ν : ℝ) *
          (stepAlphaNorm (α0 n) (αI n) (ω n) m ν t * (t / (ν : ℝ)) + qsvtLogFactor ε)
        = (m : ℝ) * (ν : ℝ) * (Real.sqrt ((ν : ℝ) / t) * αI n * (t / (ν : ℝ)))
          + (m : ℝ) * (ν : ℝ) * ((1 / (m : ℝ)) * (α0 n + ω n) * (t / (ν : ℝ)))
          + (m : ℝ) * (ν : ℝ) * qsvtLogFactor ε := by
      unfold stepAlphaNorm
      ring
    rw [hexp]
    have hA' : (m : ℝ) * (ν : ℝ) * (Real.sqrt ((ν : ℝ) / t) * αI n * (t / (ν : ℝ)))
        = (m : ℝ) * Real.sqrt ((ν : ℝ) * t) * αI n := by
      rw [show (m : ℝ) * (ν : ℝ) * (Real.sqrt ((ν : ℝ) / t) * αI n * (t / (ν : ℝ)))
          = ((m : ℝ) * (ν : ℝ) * (Real.sqrt ((ν : ℝ) / t) * (t / (ν : ℝ)))) * αI n
            by ring]
      rw [hsqrt]
    rw [hA', hB]
    have h1 : t * (α0 n + ω n) ≤ (α0 n + (m : ℝ) * ω n) * t := by
      rw [mul_comm (α0 n + (m : ℝ) * ω n) t]
      exact mul_le_mul_of_nonneg_left (by nlinarith [hω n, hm1]) (le_of_lt ht)
    have h2 : (m : ℝ) * Real.sqrt ((ν : ℝ) * t) * αI n
        = αI n * (m : ℝ) * Real.sqrt ((ν : ℝ) * t) := by ring
    linarith [h1, h2]
  -- Reassemble `q_PS = mν · max_n step_n` and apply the pointwise bound.
  have hsup : (m : ℝ) * (ν : ℝ) *
        (Finset.univ : Finset (Fin m)).sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
          (fun n => stepAlphaNorm (α0 n) (αI n) (ω n) m ν t * (t / (ν : ℝ))
            + qsvtLogFactor ε)
      = (Finset.univ : Finset (Fin m)).sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
          (fun n => (m : ℝ) * (ν : ℝ) *
            (stepAlphaNorm (α0 n) (αI n) (ω n) m ν t * (t / (ν : ℝ))
              + qsvtLogFactor ε)) :=
    Finset.mul₀_sup' hM _ _ _
  unfold iterativeQubitizationCount qubitizationStepQueries theorem3QueryBound
  rw [hsup]
  apply Finset.sup'_le
  intro n _
  exact le_trans (key n) (by
    simpa using (Finset.le_sup' (f := fun n =>
      (α0 n + (m : ℝ) * ω n) * t
        + αI n * (m : ℝ) * Real.sqrt ((ν : ℝ) * t)
        + (m : ℝ) * (ν : ℝ) * qsvtLogFactor ε) (Finset.mem_univ n)))

/-- The per-map coefficient `1`-norm of Eq. (50) is nonnegative whenever the
coefficient norms are nonnegative and `m, ν ≥ 1`, `t > 0`. -/
theorem stepAlphaNorm_nonneg (α0 αI ω : ℝ) (m ν : ℕ) (t : ℝ)
    (hα0 : 0 ≤ α0) (hαI : 0 ≤ αI) (hω : 0 ≤ ω) (hm : 0 < m) (_ht : 0 < t) :
    0 ≤ stepAlphaNorm α0 αI ω m ν t := by
  unfold stepAlphaNorm
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hs : 0 ≤ Real.sqrt ((ν : ℝ) / t) := Real.sqrt_nonneg _
  have h1 : 0 ≤ Real.sqrt ((ν : ℝ) / t) * αI := mul_nonneg hs hαI
  have h2 : 0 ≤ (1 / (m : ℝ)) * (α0 + ω) :=
    mul_nonneg (le_of_lt (one_div_pos.mpr hm0)) (add_nonneg hα0 hω)
  linarith

end Qatlib.Papers.RepeatedLind23.MainResults.IterativeQubitization
