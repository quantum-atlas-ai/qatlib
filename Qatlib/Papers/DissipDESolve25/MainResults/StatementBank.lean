/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DissipDESolve25.MainResults.PrepLemmas
public import Qatlib.Concepts.BlockEncoding.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Statement bank for
"Quantum Differential Equation Solvers with Low State Preparation Cost:
Eliminating the Time Dependence in Dissipative Equations"
(arXiv:2508.15170v1, 2025).

This file records faithful `Prop` statements for the claims whose full
formalisation meets substantive obstacles. Two claims are proved in this
block (`PrepLemmas.lean`): Lemma 7 (`norm_normalized_sub_le`) and
Lemma 9 (`tail_truncation_error`, with an explicit-constant
sufficient condition), together with the per-time Duhamel norm core of
`history_state_squared_norm_sum_bound_statement` (Result 3, `history_norm_bound`).

The remaining claims are recorded as abstract statements:
- (Theorem 5, robust amplitude amplification) is stated through the
  shared `BlockEncoding` interface; the `m + 1` ancilla growth and the
  `O(α/(δ‖Ξ‖)·log(α/(‖Ξ‖εa)))` controlled-`U` query count are omitted
  because the shared interface deliberately does not model circuit
  synthesis or query bounds, and no robust amplitude-amplification
  construction exists in Mathlib or in this repository.
- (Theorem 6, one-step propagator, Eq. (30)) is stated as the
  product-comparison shape `∏ α̃ ≤ C·∏ ‖𝒯 e^{∫ A}‖`; the concrete constant
  comes from the LCHS/LCU discretization ledger together with the
  `O(α_A T log(1/εa))` query bound, which needs the full compiled-query
  machinery.
- (Result 2 specialization) is the `O(log³(1/ε))` query-complexity
  shape over an abstract query model.
- (Result 3 specialization) adds the history-state normalization
  aggregation `∑‖u(kh)‖² ≤ M·B²` on top of the proved per-time bound,
  which is what makes the history-state preparation cost explicit.

-/
set_option autoImplicit false

open scoped BigOperators
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.BlockEncoding

namespace Qatlib.Papers.DissipDESolve25.MainResults

/-! ## Claim statements -/

/-- **(Theorem 5, robust amplitude amplification)**: given an
`(α, εori)` block encoding of `Ξ` between isometric frames and robustness
parameters `δ, εa ∈ (0, 1)`, there exist a carrier `H'` (the `m + 1`
ancilla-extended workspace, whose dimension bookkeeping is abstracted
away) and an `(α', εa‖Ξ‖ + εori + εa·εori)` block encoding of `Ξ` with
`α' ≤ ‖Ξ‖/(1 − δ)`. The `O(α/(δ‖Ξ‖)·log(α/(‖Ξ‖εa)))` controlled-`U`
query count is not asserted; see the file docstring. -/
def robust_block_encoding_amplification_statement {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
    [DecidableEq H] [DecidableEq I] [DecidableEq O]
    (Ξ : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (α εori δ εa : ℝ) : Prop :=
  0 < δ → δ < 1 → 0 < εa → εa < 1 →
    BlockEncoding Ξ U L R α εori →
      ∃ (H' : Type) (_instH' : Fintype H') (_decH' : DecidableEq H')
        (U' : Matrix H' H' ℂ) (L' : Matrix H' O ℂ) (R' : Matrix H' I ℂ) (α' : ℝ),
        α' ≤ ‖Ξ‖ / (1 - δ) ∧
        BlockEncoding Ξ U' L' R' α' (εa * ‖Ξ‖ + εori + εa * εori)

/-- **(Theorem 6, Eq. (30), product shape)**: for the one-step
propagator discretization with LCU block-encoding normalizations
`alpha ℓ > 0` and propagator norms `prop ℓ > 0` (the abstracted
`‖𝒯 e^{∫_{t_ℓ}^{t_{ℓ+1}} A}‖`), the product of the normalizations is at
most a constant multiple of the product of the propagator norms. The
concrete constant and the `O(α_A T log(1/εa))` query ledger are part of
the LCHS compilation and are not asserted here. -/
def propagator_normalization_product_bound_statement {n : ℕ} (alpha prop : Fin n → ℝ) : Prop :=
  (∀ ℓ, 0 < prop ℓ) → (∀ ℓ, 0 < alpha ℓ) →
    ∃ C : ℝ, 0 < C ∧ ∏ ℓ, alpha ℓ ≤ C * ∏ ℓ, prop ℓ

/-- **(Result 2 specialization)**: the total number of queries of the
dissipative solver is at most `C·log³(1/ε)` for all target precisions
`ε ∈ (0, 1/2]`, over an abstract query model `queries`. -/
def dissipative_final_state_log_cubed_query_bound_statement (C : ℝ) (queries : ℝ → ℝ) : Prop :=
  0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
    queries ε ≤ C * (Real.log (1 / ε)) ^ 3

/-- **(Result 3 specialization, history-state normalization)**: if
every time slice satisfies the Duhamel norm bound `‖u(kh)‖ ≤ B` (proved
per time in `PrepLemmas.history_norm_bound` with
`B = ‖u₀‖ + ∫₀ᵗ‖b‖`), then the squared masses of the history state
aggregate as `∑_k ‖u(kh)‖² ≤ M·B²` with `M` time slices; this is the
normalization factor that makes the history-state preparation cost
explicit in Result 3. -/
def history_state_squared_norm_sum_bound_statement {ι : Type} [Fintype ι] {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (u : ι → E) (B : ℝ) : Prop :=
  (∀ k, ‖u k‖ ≤ B) → ∑ k, ‖u k‖ ^ 2 ≤ Fintype.card ι * B ^ 2

end Qatlib.Papers.DissipDESolve25.MainResults
