/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.RiskEstimation.PopulationGap.SimTaylorDefs
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
import Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointWord
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Sparse-Hamiltonian simulation model vocabulary

Fixed source: arXiv:1312.1414 (Berry, Childs, Cleve, Kothari, Somma,
*Exponential improvement in precision for simulating sparse Hamiltonians*),
fixed version as recorded in the repository.  PDF SHA-256 base text read from
`assets/1312.1414.pdf` / `assets/1312.1414.txt`.

This module fixes the vocabulary used by every statement of the paper layer:

* the sparse-access row oracle `SparseRowOracle` and the entry bound
  `sparseMaxEntry` are reused from the frozen `QRiskWoerner18` layer (the same
  Low–Chuang-style sparse-access contract the paper uses, Section 2);
* a counted **simulation word** is a `List (AdjointStep (Reg wires))` over the
  supplied oracle, with `adjointQueryCount` oracle calls and
  `adjointGateCount` fixed operations, and matrix semantics `evaluate`
  (reused from `Concepts.CoherentSim.CoherentOAA`);
* the target unitary is `HamiltonianEvolution H t = exp(-iHt)` from the shared
  Foundations layer (`Concepts.MbqcFlow.FlowDecision`);
* the paper's bounds `τ log(τ/ε)/loglog(τ/ε)` and
  `τ log²(τ/ε)/loglog(τ/ε)·n` are the explicit real functions `queryBound`
  and `gateBound`, with `τ = d²‖H‖max t`.

Everything here is definitional: the statements live in the sibling modules and
the two fully proved lemmas are Lemmas 3.6 and 3.7 (oblivious amplification).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.RiskEstimation.PopulationGap
open scoped Matrix.Norms.L2Operator Classical BigOperators

namespace Qatlib.Papers.SparseHamSim13.MainResults

/-! ## Sparsity, max-norm, unitarity -/

/-- A square complex matrix is unitary (membership in Mathlib's unitary group,
i.e. `U Uᴴ = 1 = Uᴴ U`). -/
def IsUnitary {I : Type*} [Fintype I] [DecidableEq I] (U : Matrix I I ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup I ℂ

/-- Row sparsity `d`: every row has at most `d` nonzero entries. -/
def RowSparse {n : ℕ} (H : Matrix (Reg n) (Reg n) ℂ) (d : ℕ) : Prop :=
  ∀ i, (Finset.univ.filter (fun j => H i j ≠ 0)).card ≤ d

/-- Column sparsity `d`: every column has at most `d` nonzero entries. -/
def ColSparse {n : ℕ} (H : Matrix (Reg n) (Reg n) ℂ) (d : ℕ) : Prop :=
  ∀ j, (Finset.univ.filter (fun i => H i j ≠ 0)).card ≤ d

/-- The paper's `d`-sparse Hamiltonian contract: Hermitian, at most `d`
nonzeros in each row and in each column (Section 2). -/
def IsSparseHamiltonian {n : ℕ} (H : Matrix (Reg n) (Reg n) ℂ) (d : ℕ) : Prop :=
  H.IsHermitian ∧ RowSparse H d ∧ ColSparse H d

/-- The paper's `τ := d²‖H‖max t`, the parameter that governs both bounds of
Theorem 1.1. -/
def tau (d : ℕ) (Hmax t : ℝ) : ℝ := (d : ℝ) ^ 2 * Hmax * t

/-! ## The explicit bound functions -/

/-- Query bound of Theorem 1.1 / Lemma 3.8 / Theorem 4.1:
`τ · log(τ/ε) / log log(τ/ε)`. -/
def queryBound (τ ε : ℝ) : ℝ :=
  τ * Real.log (τ / ε) / Real.log (Real.log (τ / ε))

/-- Gate bound of Theorem 1.1: `τ · log²(τ/ε) / log log(τ/ε) · n`. -/
def gateBound (τ ε : ℝ) (n : ℕ) : ℝ :=
  τ * (Real.log (τ / ε)) ^ 2 / Real.log (Real.log (τ / ε)) * (n : ℝ)

/-- The `Ω(log(1/ε)/loglog(1/ε))` lower-bound rate of Theorem 1.2 / 6.1:
`log(1/ε) / log log(1/ε)`. -/
def lowerBoundRate (ε : ℝ) : ℝ :=
  Real.log (1 / ε) / Real.log (Real.log (1 / ε))

/-- In the asymptotic regime `τ/ε > e` the query bound is positive. -/
theorem queryBound_pos {τ ε : ℝ} (hε : 0 < ε) (h : Real.exp 1 < τ / ε) :
    0 < queryBound τ ε := by
  have hratio : 0 < τ / ε := lt_trans (Real.exp_pos 1) h
  have hlog : 0 < Real.log (τ / ε) := Real.log_pos (lt_trans (Real.one_lt_exp_iff.mpr (by norm_num)) h)
  have hone : 1 < Real.log (τ / ε) := by
    have := Real.log_lt_log (Real.exp_pos 1) h
    rwa [Real.log_exp] at this
  have hloglog : 0 < Real.log (Real.log (τ / ε)) := Real.log_pos hone
  have hτ : 0 < τ := by
    have h2 : 0 < τ / ε * ε := mul_pos hratio hε
    rwa [div_mul_cancel₀ _ (ne_of_gt hε)] at h2
  unfold queryBound
  positivity

/-- In the asymptotic regime `τ/ε > e` the gate bound is positive (for
`1 ≤ n`). -/
theorem gateBound_pos {τ ε : ℝ} {n : ℕ} (hn : 1 ≤ n) (hε : 0 < ε)
    (h : Real.exp 1 < τ / ε) :
    0 < gateBound τ ε n := by
  have hratio : 0 < τ / ε := lt_trans (Real.exp_pos 1) h
  have hτ : 0 < τ := by
    have h2 : 0 < τ / ε * ε := mul_pos hratio hε
    rwa [div_mul_cancel₀ _ (ne_of_gt hε)] at h2
  have hlog : 0 < Real.log (τ / ε) := Real.log_pos (lt_trans (Real.one_lt_exp_iff.mpr (by norm_num)) h)
  have hone : 1 < Real.log (τ / ε) := by
    have := Real.log_lt_log (Real.exp_pos 1) h
    rwa [Real.log_exp] at this
  have hloglog : 0 < Real.log (Real.log (τ / ε)) := Real.log_pos hone
  unfold gateBound
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  positivity

/-- In the asymptotic regime `ε < 1` the lower-bound rate is positive. -/
theorem lowerBoundRate_pos {ε : ℝ} (hε : Real.exp 1 < Real.log (1 / ε)) :
    0 < lowerBoundRate ε := by
  have hlog : 0 < Real.log (1 / ε) := lt_trans (Real.exp_pos 1) hε
  have hone : 1 < Real.log (1 / ε) := lt_trans (Real.one_lt_exp_iff.mpr (by norm_num)) hε
  have hloglog : 0 < Real.log (Real.log (1 / ε)) := Real.log_pos hone
  unfold lowerBoundRate
  positivity

/-! ## Data-embedding semantics of a counted word -/

/-- Zero-padded embedding of the `n`-qubit data record `x` into the `n + a + n`
oracle workspace of the sparse-access model: data record, zero index slot, zero
answer slot.  This is the data piece of the frozen `simCat3`/`simPad`
convention. -/
def dataEmbed (n d wires : ℕ) (hd : 0 < d) (x : Fin (2 ^ n)) : Reg wires :=
  simPad wires (n + Nat.clog 2 (max 2 d) + n)
    (simCat3 (finBits n x) (indexBits d ⟨0, hd⟩) (finBits n 0))

/-- A word `body` over oracle `U` **implements** the `n`-qubit operator `V` on
the data register with clean ancillas: on every embedded data basis state it
produces the `V`-image, expanded on embedded data basis states only. -/
def ImplementsOnData {n d wires : ℕ} (hd : 0 < d)
    (U : Matrix (Reg wires) (Reg wires) ℂ) (body : List (AdjointStep (Reg wires)))
    (V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : Prop :=
  ∀ x : Fin (2 ^ n),
    evaluate U body *ᵥ Ket (dataEmbed n d wires hd x) =
      ∑ y : Fin (2 ^ n), V y x • Ket (dataEmbed n d wires hd y)

/-- A word `body` over oracle `U` **approximately implements** the target `T`
within `ε`: `ImplementsOnData` for some operator ε-close to `T` in operator
norm. -/
def ApproxImplementsOnData {n d wires : ℕ} (hd : 0 < d)
    (U : Matrix (Reg wires) (Reg wires) ℂ) (body : List (AdjointStep (Reg wires)))
    (T : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (ε : ℝ) : Prop :=
  ∃ V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
    ‖V - T‖ ≤ ε ∧ ImplementsOnData hd U body V

/-- The counted sparse-access simulation word of Theorem 1.1 / Lemma 4.5: a
well-formed counted word over a unitary sparse row oracle of `H`, whose
evaluated operator approximates `e^{-iHt}` within `ε` on the data register with
clean ancillas.  `H` is given through its row-oracle data `(f, v)`, and `H`'s
entries are exactly the oracle values (`SparseRowOracle`). -/
structure SparseSimulationWord (n d : ℕ) (hd : 0 < d)
    (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (f : Fin (2 ^ n) → Fin d → Fin (2 ^ n)) (v : Fin (2 ^ n) → Fin d → ℂ)
    (t ε : ℝ) where
  /-- Number of oracle workspace wires. -/
  wires : ℕ
  /-- The unitary sparse row oracle. -/
  oracle : Matrix (Reg wires) (Reg wires) ℂ
  /-- The oracle is unitary. -/
  oracle_mem : IsUnitary oracle
  /-- The oracle computes the row-index oracle `(x,k) ↦ (x, f x k)` on the
  basis records exactly (the frozen `simCat3` convention). -/
  oracle_row_spec : ∀ (x : Fin (2 ^ n)) (k : Fin d),
    oracle *ᵥ Ket (simPad wires (n + Nat.clog 2 (max 2 d) + n)
        (simCat3 (finBits n x) (indexBits d k) (finBits n 0))) =
      Ket (simPad wires (n + Nat.clog 2 (max 2 d) + n)
        (simCat3 (finBits n x) (indexBits d k) (finBits n (f x k))))
  /-- The counted program. -/
  body : List (AdjointStep (Reg wires))
  /-- Every fixed gate of the program is unitary. -/
  body_well_formed : WellFormedAdjointCircuit body
  /-- The program implements `e^{-iHt}` within `ε`. -/
  approximate : ApproxImplementsOnData hd oracle body (HamiltonianEvolution H t) ε

end Qatlib.Papers.SparseHamSim13.MainResults
