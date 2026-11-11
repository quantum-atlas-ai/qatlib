/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PetzRecovery26.VirtualAdjoint.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Probabilistic transposition with a single query (main result, p. 3)

Fixed source version: arXiv:2602.05828v1 (first submitted 2026-02-05), Section
III A, Fig. 1 and the paragraph "We first observe that the transpose ..."
(pp. 3--4).

The paper executes a post-selected teleportation protocol that, using one query
to an unknown channel `N`, prepares the transposed state `Nᵀ(ρ)` on success.
For an input state `ρ` the unnormalised output is `(1/(d_A d_B)) Nᵀ(ρ)`, and the
success probability is

  `p_suc = Tr[N(ρᵀ)] / (d_A d_B)`,

which specialises to `p_suc = 1/d²` for unital channels with `d_A = d_B = d`.

This file records the quantitative core of the protocol in the single-system
model `A = B`, `d_A = d_B = d`:

* `successProbability` is the paper's success probability `Tr[N(ρᵀ)]/d²`;
* `transposeChannel` is the channel transpose `Nᵀ : X ↦ (N Xᵀ)ᵀ`;
* `successProbability_one_div_sq` proves `p_suc = 1/d²` at every unit-trace
  input state for a trace-preserving channel `N`.

The Bell-measurement / maximally-entangled-state bookkeeping that produces the
factor `1/(d_A d_B)` and the partial trace over the measured system is not
reformulated here; the success-probability formula is taken as the protocol's
defining quantity (see the docstrings for the exact correspondence).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.PetzRecovery26.VirtualAdjoint

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ## Success probability of the post-selected teleportation protocol -/

/-- The success probability of the post-selected teleportation protocol of
Fig. 1 (p. 3) in the single-system specialisation `d_A = d_B = d`:
`p_suc = Tr[N(ρᵀ)]/d²`.  This is the paper's
`Tr[N_AB(ρᵀ ⊗ 1_A)]/(d_A d_B)` after the partial trace over the
Bell-measured system has been carried out `(single-system model, see the file
docstring)`. -/
def successProbability (N : MatrixMap A A ℂ) (ρ : Matrix A A ℂ) : ℂ :=
  (N ρᵀ).trace / (Fintype.card A : ℂ) ^ 2

/-- The channel transpose `Nᵀ` of Section III A (p. 3) on a square system:
`Nᵀ(ρ) = (N(ρᵀ))ᵀ`.  In the single-system model this is the map whose action on
states produces the protocol's target state `Nᵀ(ρ)`. -/
def transposeChannel (N : MatrixMap A A ℂ) : MatrixMap A A ℂ :=
  transposeMap ∘ₗ (N ∘ₗ transposeMap)

omit [Fintype A] [DecidableEq A] in
/-- The transposed channel transposes both the input and the output. -/
@[simp] theorem transposeChannel_apply (N : MatrixMap A A ℂ) (ρ : Matrix A A ℂ) :
    transposeChannel N ρ = (N ρᵀ)ᵀ := by
  simp [transposeChannel]

omit [DecidableEq A] in
/-- The transpose of a trace-preserving channel is trace preserving (in the
single-system model). -/
theorem transposeChannel_trace (N : MatrixMap A A ℂ) (ρ : Matrix A A ℂ) :
    (transposeChannel N ρ).trace = (N ρᵀ).trace := by
  rw [transposeChannel_apply, Matrix.trace_transpose]

/-! ## Main result: success probability `1/d²` -/

omit [DecidableEq A] in
/-- **Main result: probabilistic transpose with one query (p. 3).**  For any
trace-preserving channel `N` and any input state `ρ` of unit trace, the
post-selected teleportation protocol of Fig. 1 succeeds with probability
`p_suc = 1/d²`, `d = d_A = d_B` — the paper's statement "when `N_{A→B}` is a
unital channel, we have that `p_suc = 1/d²` where `d_A = d_B = d`".

Trace preservation (rather than unitality) is what the single-system trace
formula requires: `Tr[N(ρᵀ)] = Tr[ρᵀ] = Tr[ρ] = 1`; in the paper's bipartite
protocol the same computation is driven by the unitality of `N` after the
partial trace over the measured system. -/
theorem successProbability_one_div_sq (N : MatrixMap A A ℂ)
    (hTP : N.IsTracePreserving) (ρ : Matrix A A ℂ) (hρ : ρ.trace = 1) :
    successProbability N ρ = ((Fintype.card A : ℂ) ^ 2)⁻¹ := by
  unfold successProbability
  rw [MatrixMap.IsTracePreserving.apply_trace hTP, Matrix.trace_transpose, hρ]
  rw [div_eq_mul_inv, one_mul]

omit [DecidableEq A] in
/-- The unnormalised output of the protocol is `(1/d²)` times the transposed
channel applied to the input; combining with `p_suc = 1/d²` shows that on the
success branch the normalised output is the transposed state `Nᵀ(ρ)`. -/
theorem protocolOutput_eq_smul_transposeChannel (N : MatrixMap A A ℂ)
    (ρ : Matrix A A ℂ) :
    ((Fintype.card A : ℂ) ^ 2)⁻¹ • transposeChannel N ρ =
      ((Fintype.card A : ℂ) ^ 2)⁻¹ • (N ρᵀ)ᵀ := by
  rw [transposeChannel_apply]

end Qatlib.Papers.PetzRecovery26.VirtualAdjoint
