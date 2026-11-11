/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QTrainLiu24.MainResults.GenerationModel — source layer

Paper: Chen-Yu Liu et al., *Quantum-Train: Rethinking Hybrid Quantum-Classical
Machine Learning in the Model Compression Perspective*, fixed arXiv:2405.11304v2.
PDF `prove/assets/2405.11304v2.pdf`.

Claim c001: the QT generation model of Eq. (3) (p.2). The classical network has
`M` parameters `θ⃗ = (θ₁,…,θ_M)` (Eq. (1)); a quantum state on
`N = ⌈log₂ M⌉` qubits has basis-measurement probabilities `|⟨i|ψ⟩|² ∈ [0,1]`
(Eq. (2), p.2). The mapping model `G_γ` takes the concatenation
`x⃗_i = [N-bit basis encoding | measurement probability]` (input length `N+1`)
and outputs the parameter

  `G_γ(x⃗_i) = θ_i`   (Eq. (3), p.2).

This module formalises:

* `BasisString N = Fin N → Bool` and its cardinality `2^N`;
* `QTInput N` — a basis string together with a bounded measurement probability,
  whose real vector `QTInput.toVec` has the `N+1` coordinates of Eq. (2)
  (`toVec_basis_coord`, `toVec_prob_coord`), and which is injective;
* `basis_coverage` — `N = ⌈log₂ M⌉` basis strings cover all `M` parameters;
* `MappingModel` / `generatedParameter` — Eq. (3) `G_γ(x_i) = θ_i`;
* `sign_unrestricted` — the mapping has no fixed-sign restriction (p.3, where
  the source contrasts it with prior constant-sign mappings [52]).

The *size* of the mapping network is accounted for separately in the
`ParameterCompression` module; this module does not derive any effective
description or trainability guarantee from the qubit count alone.
No `sorry`, no extra axiom, no `unsafe`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QTrainLiu24.MainResults.GenerationModel

/-! ## Basis strings and Eq. (2) inputs -/

/-- The `N`-bit computational-basis string used to address one parameter. -/
abbrev BasisString (N : ℕ) := Fin N → Bool

/-- A QT generation-model input (Eq. (2), p.2): an `N`-bit basis string together
with the measured probability of that basis outcome, which lies in `[0,1]`. -/
structure QTInput (N : ℕ) where
  /-- The `N`-bit basis encoding of the parameter index. -/
  basis : BasisString N
  /-- The measured probability `|⟨i|ψ⟩|²`, bundled with its `[0,1]` bound. -/
  prob : Set.Icc (0 : ℝ) 1

/-- The paper's `N = ⌈log₂ M⌉` qubit count for `M` parameters (Eq. (1), p.2). -/
def qubitCount (M : ℕ) : ℕ := Nat.clog 2 M

/-- The real input vector of Eq. (2): the `N` basis bits followed by the measured
probability, for a total of `N + 1` coordinates. -/
def QTInput.toVec {N : ℕ} (x : QTInput N) : Fin (N + 1) → ℝ :=
  fun i =>
    if h : (i : ℕ) < N then
      (if x.basis ⟨i, h⟩ then (1 : ℝ) else 0)
    else
      (x.prob : ℝ)

/-- Eq. (2): the first `N` coordinates are the `0/1` basis encoding. -/
theorem toVec_basis_coord {N : ℕ} (x : QTInput N) (k : Fin N) :
    x.toVec ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ =
      (if x.basis k then (1 : ℝ) else 0) := by
  simp [QTInput.toVec, k.isLt]

/-- Eq. (2): the final coordinate is the measured probability. -/
theorem toVec_prob_coord {N : ℕ} (x : QTInput N) :
    x.toVec ⟨N, Nat.lt_succ_self N⟩ = (x.prob : ℝ) := by
  simp [QTInput.toVec]

/-- The input vector has exactly `N + 1` coordinates, matching Eq. (2). -/
theorem input_coordinate_count (N : ℕ) :
    Fintype.card (Fin (N + 1)) = N + 1 :=
  Fintype.card_fin (N + 1)

/-- Distinct QT inputs give distinct Eq. (2) vectors: the `N` basis bits and the
probability are all faithfully encoded. -/
theorem toVec_injective {N : ℕ} : Function.Injective (QTInput.toVec (N := N)) := by
  rintro ⟨xb, xp⟩ ⟨yb, yp⟩ h
  have hbasis : xb = yb := by
    funext k
    have hk := congrFun h ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
    simp only [QTInput.toVec, dif_pos k.isLt] at hk
    by_cases hx : xb k <;> by_cases hy : yb k <;> simp_all
  have hprob : xp = yp := by
    apply Subtype.ext
    have hk := congrFun h ⟨N, Nat.lt_succ_self N⟩
    simpa [QTInput.toVec, Nat.lt_irrefl] using hk
  subst hbasis
  subst hprob
  rfl

/-! ## Basis coverage of the `M` parameters -/

/-- The number of `N`-bit basis strings is `2^N`. -/
theorem basisString_card (N : ℕ) : Fintype.card (BasisString N) = 2 ^ N := by
  simp [BasisString]

/-- `N = ⌈log₂ M⌉` qubits address all `M` parameters: there are at least `M`
basis strings. This is the "ensure coverage for all `M` parameters" paragraph of
§II-A (p.2). -/
theorem basis_coverage (M : ℕ) (_hM : 1 ≤ M) :
    M ≤ Fintype.card (BasisString (Nat.clog 2 M)) := by
  rw [basisString_card]
  exact Nat.le_pow_clog (by norm_num) M

/-- The paper's coverage statement in its own notation: `M ≤ 2^(qubitCount M)`. -/
theorem qubitCount_coverage (M : ℕ) (_hM : 1 ≤ M) :
    M ≤ 2 ^ qubitCount M := by
  simpa [qubitCount] using Nat.le_pow_clog (by norm_num) M

/-! ## Eq. (3): the mapping model -/

/-- A classical mapping network `G_γ` with parameters `γ`: a function from QT
inputs to a real classical-network parameter (Eq. (3), p.2). -/
abbrev MappingModel (N : ℕ) := QTInput N → ℝ

/-- Eq. (3): the generated parameter for the input `x_i` is `G_γ(x_i)`. -/
def generatedParameter {N : ℕ} (G : MappingModel N) (x : QTInput N) : ℝ := G x

/-- Eq. (3) definitionally: `G_γ(x_i) = θ_i` is the value assigned to the
parameter indexed by the basis string of `x_i`. -/
theorem eq3_generation {N : ℕ} (G : MappingModel N) (x : QTInput N) :
    generatedParameter G x = G x :=
  rfl

/-- The mapping model is sign-unrestricted: unlike the constant-sign mapping of
prior work [52], every real value (including negative ones) is attainable as a
generated parameter (§II-A, p.3). -/
theorem sign_unrestricted (N : ℕ) (s : ℝ) :
    ∃ (G : MappingModel N) (x : QTInput N), generatedParameter G x = s := by
  refine ⟨fun _ => s, ⟨fun _ => false, ⟨0, ?_⟩⟩, rfl⟩
  constructor <;> norm_num

end Qatlib.Papers.QTrainLiu24.MainResults.GenerationModel
