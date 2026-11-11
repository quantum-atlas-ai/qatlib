/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatrixProd07.MainResults.Defs
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

/-!
# MatrixProd07 — sequential generation of MPS (Theorems 13, 14)

Fixed arXiv:quant-ph/0608197v2, Section 5.

* Theorem 13 (p.19–20, sequential generation with ancilla): the three ancilla
  schemes (probabilistic stochastic operations; deterministic unitary
  interactions with decoupling; deterministic transition schemes for `d = 2`)
  generate exactly the OBC-MPS states of maximal bond dimension `D`.
* Theorem 14 (p.20, sequential generation without ancilla): the deterministic
  and probabilistic two-site unitary schemes generate exactly the OBC-MPS states
  of bond dimension `≤ d`.

The two gauges (`∑ A A† = 1`, `∑ A† A = 1`) model the stochastic-operation and
unitary-interaction normalisations of the sequential schemes.

Note on *statement records*: below, declarations whose name starts with `theorem`,
`proposition` or `corollary` but which are `def`s record the paper's formal statement
(a `Prop`) only. They carry no proof and claim no coverage; only genuine `theorem`s
are proved. This keeps the module proof-complete while preserving the precise
statements of the paper for future work.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatrixProd07.MainResults.SequentialGeneration

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Papers.MatrixProd07.MainResults
open Matrix
open scoped BigOperators ComplexConjugate

/-- Amplitude vectors on `n` sites of local dimension `d`. -/
abbrev Ket (n d : ℕ) := (Fin n → Fin d) → ℂ

/-- `ψ` has an OBC-MPS representation of bond dimension `≤ D`. -/
def MaxBondLE {n d : ℕ} (D : ℕ) (ψ : Ket n d) : Prop :=
  ∃ (D' : ℕ) (_ : NeZero D') (A : Fin n → Fin d → BM D'),
    D' ≤ D ∧ IsMpsRepresentation A ψ

/-- Scheme 1 (probabilistic, p.19): arbitrary stochastic operations, i.e. Kraus
families with `∑ A† A = 1`. -/
def ProbabilisticSequential {n d : ℕ} (D : ℕ) (ψ : Ket n d) : Prop :=
  ∃ (D' : ℕ) (_ : NeZero D') (A : Fin n → Fin d → BM D'),
    D' ≤ D ∧ IsMpsRepresentation A ψ ∧ ∀ m : Fin n, (∑ x : Fin d, (A m x)ᴴ * A m x) = 1

/-- Scheme 2 (deterministic, p.19): unitary interactions, i.e. isometries with
`∑ A A† = 1` and a decoupled ancillary system at the end. -/
def DeterministicSequential {n d : ℕ} (D : ℕ) (ψ : Ket n d) : Prop :=
  ∃ (D' : ℕ) (_ : NeZero D') (A : Fin n → Fin d → BM D'),
    D' ≤ D ∧ IsMpsRepresentation A ψ ∧ ∀ m : Fin n, (∑ x : Fin d, A m x * (A m x)ᴴ) = 1

/-- Scheme 3 (deterministic transition, `d = 2`, p.20): the fixed two-level
transition interaction with arbitrary ancilla unitaries; same isometry gauge as
scheme 2 (both classes coincide with the OBC-MPS states). -/
def DeterministicTransitionSequential {n d : ℕ} (D : ℕ) (ψ : Ket n d) : Prop :=
  ∃ (D' : ℕ) (_ : NeZero D') (A : Fin n → Fin d → BM D'),
    D' ≤ D ∧ IsMpsRepresentation A ψ ∧ ∀ m : Fin n, (∑ x : Fin d, A m x * (A m x)ᴴ) = 1

/-- **Theorem 13** (p.19–20, sequential generation with ancilla): the three
ancilla schemes generate exactly the OBC-MPS states of maximal bond dimension
`D`.

原文证明路线（[13]）：三个方向的包含中，"MPS ⟹ 方案"用逐次 SVD 把任意 MPS
重新规范化为等距/随机 Kraus 链（determinism 通过在每步把 ancilla 与站点交换
实现，最后一步仅剩交换）；"方案 ⟹ MPS"由式 (21) 直接读出振幅为 MPS。
当前 Lean 缺口：MPS 的等距规范化（把任意 `IsMpsRepresentation` 换成满足
`∑ A†A = 1` 的同振幅族）未形式化。候选复用：`g2_clause2`（左规范形）、
`Matrix.mul_eq_one_comm`。下一步：先证右规范形存在性，再逐方案构造。 -/
def theorem13_ancilla_schemes  {n d D : ℕ} (ψ : Ket n d) : Prop :=
  (ProbabilisticSequential D ψ ↔ MaxBondLE D ψ) ∧
      (DeterministicSequential D ψ ↔ MaxBondLE D ψ) ∧
      (DeterministicTransitionSequential D ψ ↔ MaxBondLE D ψ)
/-- Deterministic generation without ancilla: two-site unitary interactions,
bond dimension `≤ d`. -/
def NoAncillaDeterministic {n d : ℕ} (ψ : Ket n d) : Prop :=
  ∃ (D' : ℕ) (_ : NeZero D') (A : Fin n → Fin d → BM D'),
    D' ≤ d ∧ IsMpsRepresentation A ψ ∧ ∀ m : Fin n, (∑ x : Fin d, A m x * (A m x)ᴴ) = 1

/-- Probabilistic generation without ancilla: stochastic two-site operations,
bond dimension `≤ d`. -/
def NoAncillaProbabilistic {n d : ℕ} (ψ : Ket n d) : Prop :=
  ∃ (D' : ℕ) (_ : NeZero D') (A : Fin n → Fin d → BM D'),
    D' ≤ d ∧ IsMpsRepresentation A ψ ∧ ∀ m : Fin n, (∑ x : Fin d, (A m x)ᴴ * A m x) = 1

/-- **Theorem 14** (p.20, sequential generation without ancilla): both the
deterministic and the probabilistic two-site schemes generate exactly the OBC-MPS
states of bond dimension `≤ d`.

原文证明路线：给定两站点操作 `U^{[k]}`，令 `A^{[k]}_{i,α,β} = ⟨i,β|U^{[k]}|α,0⟩`；
`k=1` 时 `A^{[1]}` 为向量；最后一步 `U^{[N-1]}` 对 `(i|α,j)` 做 SVD 使 `A^{[N]}`
为向量，故键维 `D ≤ d`。反过来用 Thm.13 的确定性构造，把站点 `k+1` 当作第 `k`
步的 ancilla，再做相邻交换。当前 Lean 缺口：两站点操作到 MPS 矩阵的读出与
`D ≤ d` 的 SVD 界（`Matrix.rank_le_width` 可复用）尚未形式化。 -/
def theorem14_no_ancilla  {n d : ℕ} (ψ : Ket n d) : Prop :=
  (NoAncillaDeterministic ψ ↔ MaxBondLE d ψ) ∧
      (NoAncillaProbabilistic ψ ↔ MaxBondLE d ψ)
end Qatlib.Papers.MatrixProd07.MainResults.SequentialGeneration
