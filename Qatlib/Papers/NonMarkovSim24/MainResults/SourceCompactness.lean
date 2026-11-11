/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonMarkovSim24.MainResults.DQMEModel
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# c002 — Compactness of the bosonic DQME-SQ Hilbert space vs. pseudomode theory

Paper: arXiv:2401.17255v4, Sec. II A p. 3 and Appendix A, Eq. (A2), (A7).

Claim (c002): the bosonic DQME-SQ fully captures the non-Markovian open quantum
dynamics, without any approximation, in a smaller Hilbert space
`H_S ⊗ H_S* ⊗ H_D` than the pseudomode theory's
`H_S ⊗ H_S* ⊗ H_D ⊗ H_D*`.

Appendix A (Eq. (A2), (A7)) shows exactly how the DQME-SQ RDT is recovered from
the pseudomode density operator: trace out the pseudomode modes
`H_D ⊗ H_D*` and re-expand in the dissipaton occupation basis of a single copy
of `H_D`.  The quantitative content of "smaller", with no approximation, is the
strict dimension inequality formalized here: the DQME-SQ carrier is a proper
subspace of the pseudomode carrier obtained by tensoring with one copy of `H_D`
instead of `H_D ⊗ H_D*`.

We model a single dissipaton mode with `N` levels, so `dim H_D = N` and
`dim (H_D ⊗ H_D*) = N²`.  The inequality holds for every `N ≥ 2` (a bosonic
mode has infinitely many levels; `N` is any nontrivial truncation) and every
nonempty system space (`d_S ≥ 1`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NonMarkovSim24.MainResults

/-- Dimension of the DQME-SQ carrier `H_S ⊗ H_S* ⊗ H_D` (Eq. (9a)), with
`dim H_S = d_S` and `dim H_D = N` for a truncated dissipaton mode. -/
def dqmeCarrierDim (dS N : ℕ) : ℕ :=
  Module.finrank ℂ
    (TensorProduct ℂ (TensorProduct ℂ (Fin dS → ℂ) (Module.Dual ℂ (Fin dS → ℂ)))
      (Fin N → ℂ))

/-- Dimension of the pseudomode-theory carrier `H_S ⊗ H_S* ⊗ H_D ⊗ H_D*`
(Sec. II A, p. 3; Eq. (A1)). -/
def pseudomodeCarrierDim (dS N : ℕ) : ℕ :=
  Module.finrank ℂ
    (TensorProduct ℂ (TensorProduct ℂ (Fin dS → ℂ) (Module.Dual ℂ (Fin dS → ℂ)))
      (TensorProduct ℂ (Fin N → ℂ) (Module.Dual ℂ (Fin N → ℂ))))

/-- **c002: compactness of the bosonic DQME-SQ.**  For a nontrivial dissipaton
mode (`2 ≤ N`) and a nonempty system space (`1 ≤ d_S`), the DQME-SQ Hilbert
space of Eq. (4)/(9a) is strictly smaller than the pseudomode Hilbert space
`H_S ⊗ H_S* ⊗ H_D ⊗ H_D*` of Eq. (A1).  Together with the exact recovery of
Eq. (A2)/(A7) this expresses "smaller Hilbert space, without any
approximation". -/
theorem dqmeCarrierDim_eq (dS N : ℕ) : dqmeCarrierDim dS N = dS * dS * N := by
  unfold dqmeCarrierDim
  rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct]
  simp [Subspace.dual_finrank_eq]

/-- The pseudomode carrier has dimension `d_S² · N²`. -/
theorem pseudomodeCarrierDim_eq (dS N : ℕ) :
    pseudomodeCarrierDim dS N = dS * dS * (N * N) := by
  unfold pseudomodeCarrierDim
  rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct, Module.finrank_tensorProduct]
  simp [Subspace.dual_finrank_eq]

/-- The `dqme_hilbert_space_compact` result for the NonMarkovSim24 paper model. -/
theorem dqme_hilbert_space_compact (dS N : ℕ) (hdS : 1 ≤ dS) (hN : 2 ≤ N) :
    dqmeCarrierDim dS N < pseudomodeCarrierDim dS N := by
  rw [dqmeCarrierDim_eq, pseudomodeCarrierDim_eq]
  have hNN : N < N * N := lt_mul_self (by omega)
  have hpos : 0 < dS * dS := by positivity
  exact Nat.mul_lt_mul_of_pos_left hNN hpos

end Qatlib.Papers.NonMarkovSim24.MainResults
