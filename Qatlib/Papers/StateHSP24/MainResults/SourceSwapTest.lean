/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.Entanglement
import Qatlib.Concepts.MbqcFlow.FlowDecision.QuadraticTraceDistance

set_option backward.isDefEq.respectTransparency false

/-!
# StateHSP24 — the SWAP test (Proposition 3, Proposition 4, Corollary 3)

Bouland–Giurgica-Tiron–Wright, fixed arXiv:2410.12706v1, Section 2.

* **Proposition 3** (SWAP test, projector version): with
  `Π_SWAP = ½ (I + SWAP)`, the swap-test circuit implements the projective
  measurement `{Π_SWAP, I - Π_SWAP}`.
* **Proposition 4** (purity formula): `Tr(SWAP · ρ^{⊗2}) = Tr(ρ²)`.
* **Corollary 3**: the acceptance probability on `ρ^{⊗2}` is
  `½ + ½ Tr(ρ²)`.

The circuit is expanded explicitly: the ancilla starts in `|+⟩`, the controlled
swap is applied and the ancilla is Hadamarded, so the two ancilla outcomes carry
the projectors `Π_SWAP` and `I - Π_SWAP`.  The trace identities are proved at the
level of the actual matrices; no spectral decomposition or positivity assumption
is used for Proposition 4.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.StateHSP24.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision
open scoped BigOperators ComplexOrder

/-! ## The swap operator and the swap projector -/

/-- The **SWAP** operator on two `d`-dimensional registers:
`SWAP |i⟩ ⊗ |j⟩ = |j⟩ ⊗ |i⟩` (Definition 9 of the paper). -/
def swapOp (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

/-- Entry form of `SWAP`: the only nonzero entries swap the two indices. -/
theorem swapOp_apply (d : ℕ) (i j k l : Fin d) :
    swapOp d (i, j) (k, l) = if i = l ∧ j = k then 1 else 0 := rfl

/-- The action of `SWAP` on a two-register state: `(SWAP ψ)(i,j) = ψ(j,i)`. -/
theorem swapOp_mulVec_apply (d : ℕ) (ψ : QState (Fin d × Fin d)) (i j : Fin d) :
    (swapOp d *ᵥ ψ) (i, j) = ψ (j, i) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp [swapOp]
    · intro y _ hy
      by_cases h : i = y
      · exact absurd h.symm hy
      · simp [swapOp, h]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · intro x _ hx
    by_cases h : j = x
    · exact absurd h.symm hx
    · simp [swapOp, h]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- `SWAP` is an involution. -/
theorem swapOp_mul_self (d : ℕ) : swapOp d * swapOp d = 1 := by
  classical
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp only [swapOp, Matrix.one_apply, Prod.mk.injEq]
      by_cases h : i = k ∧ j = l
      · obtain ⟨rfl, rfl⟩ := h
        simp
      · have h' : ¬(j = l ∧ i = k) := fun hh => h ⟨hh.2, hh.1⟩
        rw [if_neg h', if_neg h]
        simp
    · intro y _ hy
      by_cases h : i = y
      · exact absurd h.symm hy
      · simp [swapOp, h]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · intro x _ hx
    by_cases h : j = x
    · exact absurd h.symm hx
    · simp [swapOp, h]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- `SWAP` is self-adjoint (it is a real permutation matrix). -/
theorem swapOp_conjTranspose (d : ℕ) : (swapOp d)ᴴ = swapOp d := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  simp only [Matrix.conjTranspose_apply, swapOp]
  by_cases h : k = j ∧ l = i
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, if_true, star_one]
  · have h' : ¬(i = l ∧ j = k) := by
      rintro ⟨rfl, rfl⟩
      exact h ⟨rfl, rfl⟩
    rw [if_neg h, if_neg h', star_zero]

/-- The projector `Π_SWAP = ½ (I_AB + SWAP_AB)` onto the symmetric subspace. -/
def swapProjector (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (1 / 2 : ℂ) • (1 + swapOp d)

/-- The complement `I - Π_SWAP = ½ (I - SWAP)` is the antisymmetric projector. -/
theorem one_sub_swapProjector (d : ℕ) :
    (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - swapProjector d =
      (1 / 2 : ℂ) • (1 - swapOp d) := by
  ext p q
  simp only [swapProjector, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.one_apply]
  by_cases h : p = q
  · subst h
    simp
    ring
  · simp [h]

/-- `Π_SWAP` is idempotent. -/
theorem swapProjector_mul_self (d : ℕ) : swapProjector d * swapProjector d = swapProjector d := by
  have h : (1 + swapOp d) * (1 + swapOp d) = (2 : ℂ) • (1 + swapOp d) := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, swapOp_mul_self]
    module
  rw [swapProjector, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, smul_smul]
  norm_num

/-- `Π_SWAP` is self-adjoint, hence an orthogonal projector. -/
theorem swapProjector_conjTranspose (d : ℕ) : (swapProjector d)ᴴ = swapProjector d := by
  rw [swapProjector, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, swapOp_conjTranspose]
  norm_num

/-! ## Proposition 4: the purity formula -/

/-- The trace of a Kronecker product factors: `Tr(A ⊗ B) = Tr(A) Tr(B)`. -/
theorem trace_tensorGate (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) :
    (TensorGate A B).trace = A.trace * B.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, tensorGate_apply]
  rw [Finset.sum_mul_sum]

/-- **Proposition 4** (purity formula), entrywise form: for arbitrary matrices `A`, `B`,
`Tr(SWAP · (A ⊗ B)) = Tr(A B)`.  In particular, with `A = B = ρ` this is
`Tr(SWAP · ρ^{⊗2}) = Tr(ρ²)`; no positivity of `ρ` is required. -/
theorem trace_swapOp_tensorGate (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) :
    (swapOp d * TensorGate A B).trace = (A * B).trace := by
  classical
  rw [Matrix.trace, Fintype.sum_prod_type]
  have hleft : ∀ i j : Fin d,
      (swapOp d * TensorGate A B) (i, j) (i, j) = A j i * B i j := by
    intro i j
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single i]
      · simp [swapOp, tensorGate_apply]
      · intro y _ hy
        by_cases h : i = y
        · exact absurd h.symm hy
        · simp [swapOp, h]
      · intro h
        exact absurd (Finset.mem_univ i) h
    · intro x _ hx
      by_cases h : j = x
      · exact absurd h.symm hx
      · simp [swapOp, h]
    · intro h
      exact absurd (Finset.mem_univ j) h
  simp only [Matrix.diag_apply, hleft]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]

/-- **Proposition 4** (purity formula) of the paper: for any square matrix `ρ`,
`Tr(SWAP · ρ^{⊗2}) = Tr(ρ²)`. -/
theorem proposition4_swap_trace_purity (d : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (swapOp d * TensorGate ρ ρ).trace = (ρ * ρ).trace :=
  trace_swapOp_tensorGate d ρ ρ

/-- The **acceptance trace** `Tr(Π_SWAP · ρ^{⊗2})` of the swap test. -/
def swapTestTrace (d : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  (swapProjector d * TensorGate ρ ρ).trace

/-- **Corollary 3**: for a density matrix (`Tr ρ = 1`) the swap test accepts with
probability `½ + ½ Tr(ρ²)`.  This is the trace of `Π_SWAP` against the two-copy
state, computed from Proposition 4. -/
theorem corollary3_swapTest_acceptance (d : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (htr : ρ.trace = 1) :
    swapTestTrace d ρ = (1 / 2 : ℂ) + (1 / 2 : ℂ) * (ρ * ρ).trace := by
  rw [swapTestTrace, swapProjector, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul,
    Matrix.trace_smul, Matrix.trace_add, trace_tensorGate,
    proposition4_swap_trace_purity, htr]
  ring

/-! ## Proposition 3: the circuit realises the projective measurement -/

/-- The state after the swap-test circuit (ancilla appended in `|+⟩`, controlled
`SWAP`, Hadamard on the ancilla) applied to a two-register state `ψ`.  The first
index is the ancilla outcome and the second the two-register state. -/
def swapTestState (d : ℕ) (ψ : QState (Fin d × Fin d)) : QState (Fin 2 × (Fin d × Fin d)) :=
  fun p => if p.1 = 0 then (ψ p.2 + (swapOp d *ᵥ ψ) p.2) / 2
           else (ψ p.2 - (swapOp d *ᵥ ψ) p.2) / 2

/-- The ancilla-`0` branch of the swap-test circuit is the projection by `Π_SWAP`. -/
theorem swapTestState_accept_amplitude (d : ℕ) (ψ : QState (Fin d × Fin d))
    (p : Fin d × Fin d) :
    swapTestState d ψ (0, p) = (swapProjector d *ᵥ ψ) p := by
  show (ψ p + (swapOp d *ᵥ ψ) p) / 2 = (swapProjector d *ᵥ ψ) p
  simp only [swapProjector, Matrix.smul_mulVec,
    Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The ancilla-`1` branch of the swap-test circuit is the projection by `I - Π_SWAP`. -/
theorem swapTestState_reject_amplitude (d : ℕ) (ψ : QState (Fin d × Fin d))
    (p : Fin d × Fin d) :
    swapTestState d ψ (1, p) = (((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) -
      swapProjector d) *ᵥ ψ) p := by
  show (ψ p - (swapOp d *ᵥ ψ) p) / 2 =
    (((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - swapProjector d) *ᵥ ψ) p
  simp only [one_sub_swapProjector, Matrix.smul_mulVec,
    Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Proposition 3** (SWAP test, projector version): the ancilla is measured in
the computational basis and the two outcomes have effects `Π_SWAP` and
`I - Π_SWAP`, both of which are orthogonal projectors.  Consequently the swap
test implements the projective measurement `{Π_SWAP, I - Π_SWAP}`. -/
theorem proposition3_swapTest_projective (d : ℕ) :
    swapProjector d * swapProjector d = swapProjector d ∧
      (swapProjector d)ᴴ = swapProjector d ∧
      (1 - swapProjector d) * (1 - swapProjector d) = 1 - swapProjector d ∧
      (1 - swapProjector d)ᴴ = 1 - swapProjector d ∧
      (∀ (ψ : QState (Fin d × Fin d)) (p : Fin d × Fin d),
        swapTestState d ψ (0, p) = (swapProjector d *ᵥ ψ) p) := by
  refine ⟨swapProjector_mul_self d, swapProjector_conjTranspose d, ?_, ?_,
    swapTestState_accept_amplitude d⟩
  · have h := swapProjector_mul_self d
    calc (1 - swapProjector d) * (1 - swapProjector d)
        = 1 - swapProjector d - swapProjector d +
            swapProjector d * swapProjector d := by noncomm_ring
      _ = 1 - swapProjector d := by rw [h]; noncomm_ring
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, swapProjector_conjTranspose]

end Qatlib.Papers.StateHSP24.MainResults
