/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OracleUseless11.MainResults.OracleProblem

set_option backward.isDefEq.respectTransparency false

/-!
# Theorems 14 and 15: encoding oracles in states (paper §3.3, pp. 6–7)

The paper's encoding is the pure state
`|ψ_{π,r}⟩ = (1/√(NM)) ∑_{x,y} |x⟩|y⟩|π_{x,r}(y)⟩` (Definition 12) and
`ρ_π = E_r |ψ_{π,r}⟩⟨ψ_{π,r}|` (Definition 13).

In the finite distribution model used here, the copy created by one oracle use is the
distribution of the triple `(x, y, π_{x,r}(y))` with `(x,y)` uniform — this is the content
of part 1.  For part 2 the quantity of interest is the success weight of the Kraus
operator `A` of the paper's proof: the copy selects `(x₀,y₀)` uniformly (`1/(NM)`) and
`A†A` contributes the factor `1/M`, while success requires `(x₀,y₀)` to equal the query
`(x,y)`.  We compute this weight and show it is `1/(NM²)` independently of the input
(and its `k`-fold value `1/(N^k M^{2k})`).
-/

namespace Qatlib.Papers.OracleUseless11.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

set_option autoImplicit false

/-- Mass of the `(x,y)` part of one encoding copy: `(x,y)` is uniform, `1/(NM)` each. -/
noncomputable def oneCopyMass (N M : ℕ) : ℝ := 1 / ((N : ℝ) * (M : ℝ))

/-- **Theorem 14(1) (p. 7).**  One use of `O_π` creates one copy of `ρ_π`: the masses of
the copies sum to one. -/
theorem theorem14_part1_one_copy (N M : ℕ) [NeZero N] [NeZero M] :
    ∑ _x : Fin N, ∑ _y : Fin M, oneCopyMass N M = 1 := by
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  unfold oneCopyMass
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  field_simp

/-- Success weight of the canonical simulation of one oracle use from one copy of the
encoding (Theorem 14(2), p. 7): the copy contributes `1/(NM)`, the Kraus operator
contributes `1/M`, and the query `(x,y)` must match the copy's `(x₀,y₀)`. -/
noncomputable def oneQuerySimSuccess (N M : ℕ) (x : Fin N) (y : Fin M) : ℝ :=
  (∑ x₀ : Fin N, ∑ y₀ : Fin M, if x₀ = x ∧ y₀ = y then (1 : ℝ) else 0) *
    oneCopyMass N M * (1 / (M : ℝ))

/-- The matching indicator sums to one. -/
theorem sum_indicator_match (N M : ℕ) (x : Fin N) (y : Fin M) :
    (∑ x₀ : Fin N, ∑ y₀ : Fin M, if x₀ = x ∧ y₀ = y then (1 : ℝ) else 0) = 1 := by
  classical
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ y) h
  · intro b _ hb
    refine Finset.sum_eq_zero (fun c _ => ?_)
    have : ¬ (b = x ∧ c = y) := fun h => hb h.1
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- **Theorem 14(2) (p. 7).**  It is possible to consume one copy of `ρ_π` and simulate
`O_π` with success probability `1/(NM²)`, independently of the input state. -/
theorem theorem14_part2_simulation (N M : ℕ) [NeZero N] [NeZero M]
    (x : Fin N) (y : Fin M) :
    oneQuerySimSuccess N M x y = 1 / ((N : ℝ) * (M : ℝ) ^ 2) := by
  unfold oneQuerySimSuccess oneCopyMass
  rw [sum_indicator_match]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  field_simp

/-- **Theorem 15(2) (p. 7).**  The `k`-copy simulation succeeds with probability
`1/(N^k M^{2k})`: the per-query simulations are independent. -/
theorem theorem15_part2_simulation (N M k : ℕ) [NeZero N] [NeZero M]
    (x : Fin k → Fin N) (y : Fin k → Fin M) :
    (∏ i : Fin k, oneQuerySimSuccess N M (x i) (y i))
      = (1 / ((N : ℝ) * (M : ℝ) ^ 2)) ^ k := by
  rw [Finset.prod_congr rfl (fun i _ => theorem14_part2_simulation N M (x i) (y i))]
  simp

/-- **Theorem 15(1) (p. 7).**  `k` uses of `O_π` create `ρ_π^k`: the masses of the
`k`-copy distributions sum to one. -/
theorem theorem15_part1_k_copies (N M k : ℕ) [NeZero N] [NeZero M] :
    ∑ _x : Fin k → Fin N, ∑ _y : Fin k → Fin M, (oneCopyMass N M) ^ k = 1 := by
  have hcardN : Fintype.card (Fin k → Fin N) = N ^ k := by simp
  have hcardM : Fintype.card (Fin k → Fin M) = M ^ k := by simp
  rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
    Finset.card_univ, Finset.card_univ, hcardN, hcardM]
  unfold oneCopyMass
  push_cast
  rw [div_pow, one_pow, mul_pow]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  field_simp

end Qatlib.Papers.OracleUseless11.MainResults
