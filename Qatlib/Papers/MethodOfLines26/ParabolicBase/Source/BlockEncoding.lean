/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MethodOfLines26.ParabolicBase.Source.Model
public import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
public import Qatlib.Concepts.SignalPrimitive.MainResults.Theorem1Simulation

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# arXiv:2606.03407v1 — block-encodings and the quoted complexity theorems

Fixed version: **arXiv:2606.03407v1**.

* **Lemma 9** (§4.3, PDF p.26): a block-encoding `U_v ∈ (α_v, m_v, ε_v)BE(M₀)`
  of the homogeneous solution operator `M₀ = P⁻¹ e^{−T Ã} P`, with
  `α_v = O(cond(P))` and `m_v = O(log(T‖L‖₂) + log(cond(P)/ε_v) + max_l n_l +
  ⌈log n_l⌉ + log d + Σ_{l∈S₁∪S₂} n_l)` qubits and the stated gate complexity.
* **Lemma 10** (§4.3, PDF p.28): a block-encoding
  `U_b ∈ (α_b, m_b, ε_b)BE(SEL_M)` of the inhomogeneous-term selection
  operator, with the analogous normalisation, qubit and gate counts.
* **Lemma 23** (Appendix D, PDF p.63): the tensor product of two block
  encodings is a block-encoding of the tensor product operator, with
  normalisation `α₁α₂` and error `α₂ε₁ + α₁ε₂ + ε₁ε₂`.
* **Theorem 1** (§2.2, PDF p.10, quoted from [6, Cor. 60]): QSVT Hamiltonian
  simulation with `Θ(α|t| + log(1/ε)/log(e + log(1/ε)/(α|t|)))` queries.
* **Theorem 2** (§2.3, PDF p.11, quoted from [9, Thm 4]): the optimal-LCHS
  block-encoding of `U_s(t)` with `α = O(1)` and `O(log R/h)` ancillas.

The abstract block-encoding predicate is `IsApproxBlockEncoding` below, a
thin error-parameterised wrapper around the Frozen exact predicate
`Qatlib.Concepts.BlockEncoding.StateBlockEncoding.IsBlockEncoding`
(the Frozen predicate has no error parameter, so the paper's `ε` is carried by
the local definition).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.MethodOfLines26.ParabolicBase.Source
open Qatlib.Papers.MethodOfLines26.ParabolicBase.Source

open Matrix
open scoped BigOperators
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

/-- Approximate block-encoding `U ∈ (α, m, ε)BE(A)`: `U` is unitary and its
`j₀`-corner is `α⁻¹ • A` up to operator-norm error `ε`.  This is the paper's
`(α, m, ε)BE(·)` predicate (the ancilla count `m` is tracked separately in
the statements, since it is a resource parameter, not part of the matrix). -/
def IsApproxBlockEncoding {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I]
    (U : Matrix (J × I) (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ)
    (α ε : ℝ) : Prop :=
  U ∈ Matrix.unitaryGroup (J × I) ℂ ∧ 0 < α ∧
    ‖BlockCorner U j₀ - (((α⁻¹ : ℝ) : ℂ) • A)‖ ≤ ε

/-- **Lemma 23, exact form** (arXiv:2606.03407v1, Appendix D, PDF p.63),
reusing the Frozen theorem
`Qatlib.Concepts.BlockEncoding.StateBlockEncoding.blockEncoding_tensor`.
For exact (`ε = 0`) block-encodings `U ∈ (α₁, m₁)BE(A)` and
`V ∈ (α₂, m₂)BE(B)`, the reindexed tensor product is a block-encoding of
`A ⊗ B` with normalisation `α₁α₂`. -/
theorem lemma23_tensor_block_encoding_exact
    {J I K L : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    {U : Matrix (J × I) (J × I) ℂ} {j₀ : J} {A : Matrix I I ℂ} {α : ℝ}
    (hU : IsBlockEncoding U j₀ A α)
    {V : Matrix (K × L) (K × L) ℂ} {k₀ : K} {B : Matrix L L ℂ} {β : ℝ}
    (hV : IsBlockEncoding V k₀ B β) :
    IsBlockEncoding (Matrix.reindex tensorBlockEquiv tensorBlockEquiv
        (Qatlib.Foundations.PureStateMath.TensorGate U V))
      (j₀, k₀) (Qatlib.Foundations.PureStateMath.TensorGate A B)
      (α * β) :=
  blockEncoding_tensor hU hV

/-- **Lemma 23, error ledger** (arXiv:2606.03407v1, Appendix D, PDF p.63):
the accumulated error of the tensor construction is
`(α₁ + ε₁)(α₂ + ε₂) − α₁α₂ = α₂ε₁ + α₁ε₂ + ε₁ε₂`. -/
theorem lemma23_tensor_error_ledger (α₁ α₂ ε₁ ε₂ : ℝ) :
    α₂ * ε₁ + α₁ * ε₂ + ε₁ * ε₂ = (α₁ + ε₁) * (α₂ + ε₂) - α₁ * α₂ := by
  ring

end Qatlib.Papers.MethodOfLines26.ParabolicBase.Source
