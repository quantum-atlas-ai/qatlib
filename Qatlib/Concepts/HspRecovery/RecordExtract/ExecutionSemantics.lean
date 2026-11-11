/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Ext
import Mathlib.Tactic.SplitIfs
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Finite quantum machine and circuit semantics

This module represents a finite quantum machine by a unitary step matrix and relates repeated
matrix evolution to circuit execution and measurement probabilities. It uses the
finite-dimensional unitary circuit framework described in [NielsenChuang2010].

A cyclic program counter embeds a finite gate sequence into repeated applications of one step
matrix. `circuit_run_semantics` identifies each prefix of that evolution with the corresponding
circuit prefix, while the counting lemmas give exact gate and query counts.

## Main statements

* `qtm_run_semantics`: equality of repeated-step states and measurement probabilities.
* `cyclicStep_unitary`: unitarity of the cyclic simulation step.
* `circuit_run_semantics_full`: simulation of the complete gate circuit.
* `stepCount_cyclicSimulation`: exact counts for a circuit prefix.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib
open Qatlib
open Qatlib

namespace Qatlib.Concepts.HspRecovery.RecordExtract

open Matrix

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A finite quantum machine specified by a complex step matrix and a proof that the matrix is
unitary. -/
structure QTMachine (C : Type*) [Fintype C] [DecidableEq C] where

  step : Matrix C C ℂ

  wellFormed : step ∈ Matrix.unitaryGroup C ℂ

/-- The state after applying the machine's step matrix `k` times to the basis state at `c₀`. -/
noncomputable def QTMState {C : Type*} [Fintype C] [DecidableEq C] (M : QTMachine C)
    (k : ℕ) (c₀ : C) : QState C :=
  (M.step ^ k) *ᵥ Ket c₀

/-- Running a circuit that repeats a single gate `k` times equals multiplying the input state by
the `k`th power of its matrix. -/
theorem run_repeatCircuit_gate (U : Matrix I I ℂ) (k : ℕ) (ψ : QState I) :
    Run 1 (RepeatCircuit [Step.gate U] k) ψ = (U ^ k) *ᵥ ψ := by
  induction k generalizing ψ with
  | zero => simp [Run, RepeatCircuit, pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    rw [RepeatCircuit, run_append, run_gate, ih, run_nil]
    simp only [ApplyGate]
    rw [Matrix.mulVec_mulVec, pow_succ]

/-- Repeating a machine's step gate gives `QTMState` and therefore the same measurement
probability on every specified finite set. -/
theorem qtm_run_semantics {C : Type*} [Fintype C] [DecidableEq C] (M : QTMachine C)
    (k : ℕ) (c₀ : C) (S : Finset C) :
    Run 1 (RepeatCircuit [Step.gate M.step] k) (Ket c₀) = QTMState M k c₀ ∧
    MeasureProb (Run 1 (RepeatCircuit [Step.gate M.step] k) (Ket c₀)) S
      = MeasureProb (QTMState M k c₀) S := by
  refine ⟨?_, ?_⟩
  · exact run_repeatCircuit_gate M.step k (Ket c₀)
  · exact congrArg (fun φ => MeasureProb φ S) (run_repeatCircuit_gate M.step k (Ket c₀))

/-- A simulation of `k` machine steps by repeated gates uses zero oracle queries and exactly `k`
gates. -/
theorem queryCount_qtmSimulation {C : Type*} [Fintype C] [DecidableEq C]
    (M : QTMachine C) (k : ℕ) :
    QueryCount (RepeatCircuit [Step.gate M.step] k) = 0 ∧
    GateCount (RepeatCircuit [Step.gate M.step] k) = k := by
  constructor
  · rw [queryCount_repeatCircuit]
    simp [QueryCount]
  · simpa using gateCount_repeatCircuit [Step.gate M.step] k

end Qatlib.Concepts.HspRecovery.RecordExtract

namespace Qatlib.Concepts.HspRecovery.RecordExtract

open Matrix

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A cyclic simulation configuration consists of a program counter in `Fin (2 * n + 1)` and a
data-register value. -/
@[reducible] def CyclicConfig (n : ℕ) (I : Type*) := Fin (2 * n + 1) × I

/-- Embed a data state at program-counter position `m`, assigning zero amplitude to all other
positions. -/
def cyclicFiberState (n : ℕ) (m : ℕ) (ψ : QState I) : QState (CyclicConfig n I) :=
  fun c => if c.1.val = m then ψ c.2 else 0

/-- The circuit formed by the first `k` matrices of a gate sequence, given a proof that `k ≤ n`. -/
def circuitPrefix {n : ℕ} (gates : Fin n → Matrix I I ℂ) : (k : ℕ) → k ≤ n → Circuit I
  | 0, _ => []
  | k + 1, h =>
    circuitPrefix gates k (Nat.le_of_succ_le h) ++ [Step.gate (gates ⟨k, Nat.lt_of_succ_le h⟩)]

/-- The complete circuit associated with a finite sequence of gate matrices. -/
def gateCircuit {n : ℕ} (gates : Fin n → Matrix I I ℂ) : Circuit I :=
  circuitPrefix gates n (le_refl n)

/-- The permutation matrix associated with an injective self-map of a finite type is unitary. -/
theorem permMatrix_unitary_of_injective {C : Type*} [Fintype C] [DecidableEq C] {σ : C → C}
    (hσ : Function.Injective σ) : permMatrix σ ∈ Matrix.unitaryGroup C ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, permMatrix, Matrix.of_apply,
    Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Finset.sum_eq_single (σ i) (fun k _ hk => by simp [hk])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = σ i
    · by_cases hkj : k = σ j
      · exact (hij (hσ (hki.symm.trans hkj))).elim
      · rw [if_neg hkj]
        simp
    · rw [if_neg hki]
      simp

/-- The permutation matrix that increments the cyclic program counter and preserves the data
register. -/
noncomputable def cyclicPcStep (n : ℕ) : Matrix (CyclicConfig n I) (CyclicConfig n I) ℂ :=
  permMatrix fun c : CyclicConfig n I => (c.1 + 1, c.2)

/-- Incrementing the cyclic program counter while preserving the data register is injective. -/
theorem cyclicPcSucc_injective (n : ℕ) :
    Function.Injective (fun c : CyclicConfig n I => (c.1 + 1, c.2)) := by
  rintro ⟨p, i⟩ ⟨q, j⟩ h
  have h' : (p + 1, i) = (q + 1, j) := h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h'
  exact Prod.ext (add_right_cancel h1) h2

/-- The cyclic program-counter increment matrix is unitary. -/
theorem cyclicPcStep_unitary (n : ℕ) :
    cyclicPcStep n ∈ Matrix.unitaryGroup (CyclicConfig n I) ℂ :=
  permMatrix_unitary_of_injective (cyclicPcSucc_injective n)

/-- Every program-counter fiber gate is unitary when all matrices in the input gate sequence are
unitary. -/
theorem cyclicFiberGate_unitary {n : ℕ} (gates : Fin n → Matrix I I ℂ)
    (hU : ∀ k, gates k ∈ Matrix.unitaryGroup I ℂ) (p : Fin (2 * n + 1)) :
    cyclicFiberGate gates p ∈ Matrix.unitaryGroup I ℂ := by
  unfold cyclicFiberGate
  split_ifs with h1 h2
  · exact hU _
  · exact conjTranspose_mem_unitaryGroup (hU _)
  · exact Submonoid.one_mem _

/-- The block diagonal matrix applying `cyclicFiberGate` separately at each program-counter
position. -/
noncomputable def cyclicGateStep {n : ℕ} (gates : Fin n → Matrix I I ℂ) :
    Matrix (CyclicConfig n I) (CyclicConfig n I) ℂ :=
  Matrix.of fun (p, i) (q, j) => if p = q then cyclicFiberGate gates p i j else 0

/-- A cyclic gate-step entry is the corresponding fiber-gate entry when the program counters
agree, and zero otherwise. -/
theorem cyclicGateStep_apply {n : ℕ} (gates : Fin n → Matrix I I ℂ)
    (p q : Fin (2 * n + 1)) (i j : I) :
    cyclicGateStep gates (p, i) (q, j)
      = if p = q then cyclicFiberGate gates p i j else 0 := rfl

/-- The block diagonal cyclic gate step is unitary when the input gate matrices are unitary. -/
theorem cyclicGateStep_unitary {n : ℕ} (gates : Fin n → Matrix I I ℂ)
    (hU : ∀ k, gates k ∈ Matrix.unitaryGroup I ℂ) :
    cyclicGateStep gates ∈ Matrix.unitaryGroup (CyclicConfig n I) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext ⟨p, i⟩ ⟨q, j⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]
  by_cases hpq : p = q
  · subst q
    rw [Finset.sum_eq_single p
      (fun r _ hr => Finset.sum_eq_zero fun l _ => by
        rw [Matrix.conjTranspose_apply, cyclicGateStep_apply, cyclicGateStep_apply,
          if_neg hr, if_neg hr]
        simp)
      (fun h => absurd (Finset.mem_univ _) h)]
    have hFp : (cyclicFiberGate gates p)ᴴ * cyclicFiberGate gates p = 1 := by
      have h := (Matrix.mem_unitaryGroup_iff').mp (cyclicFiberGate_unitary gates hU p)
      rwa [Matrix.star_eq_conjTranspose] at h
    have hsum : (∑ l : I, (cyclicGateStep gates)ᴴ (p, i) (p, l)
          * cyclicGateStep gates (p, l) (p, j))
        = ((cyclicFiberGate gates p)ᴴ * cyclicFiberGate gates p) i j := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cyclicGateStep_apply,
        if_true]
    rw [hsum, hFp, Matrix.one_apply]
    simp
  · rw [if_neg (show (p, i) ≠ (q, j) from fun h => hpq (Prod.ext_iff.mp h).1)]
    apply Finset.sum_eq_zero
    intro r _
    apply Finset.sum_eq_zero
    intro l _
    by_cases hrp : r = p
    · subst r
      rw [cyclicGateStep_apply, if_neg hpq, mul_zero]
    · rw [Matrix.conjTranspose_apply, cyclicGateStep_apply, if_neg hrp]
      simp

/-- Applying the cyclic gate step to a valid counter fiber applies its fiber gate to the data
state without changing the counter. -/
theorem cyclicGateStep_mulVec_fiber {n : ℕ} (gates : Fin n → Matrix I I ℂ)
    (m : ℕ) (hmM : m < 2 * n + 1) (χ : QState I) :
    cyclicGateStep gates *ᵥ cyclicFiberState n m χ
      = cyclicFiberState n m (cyclicFiberGate gates ⟨m, hmM⟩ *ᵥ χ) := by
  funext x
  obtain ⟨q, j⟩ := x
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, cyclicGateStep_apply,
    cyclicFiberState]
  by_cases hq : q.val = m
  · have hqm : q = ⟨m, hmM⟩ := Fin.ext hq
    subst hqm
    rw [if_pos hq]
    rw [Finset.sum_eq_single ⟨m, hmM⟩
      (fun r _ hr => Finset.sum_eq_zero fun l _ => by
        rw [if_neg (show (⟨m, hmM⟩ : Fin (2 * n + 1)) ≠ r from fun h => hr h.symm), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    apply Finset.sum_congr rfl
    intro l _
    rw [if_pos rfl, if_pos hq]
  · rw [if_neg hq]
    apply Finset.sum_eq_zero
    intro r _
    apply Finset.sum_eq_zero
    intro l _
    by_cases hqr : q = r
    · subst r
      rw [if_neg hq, mul_zero]
    · rw [if_neg hqr, zero_mul]

/-- Applying the cyclic counter step moves a state to the next cyclic counter fiber and
preserves its data state. -/
theorem cyclicPcStep_mulVec_fiber (n : ℕ) (m : ℕ) (hmM : m < 2 * n + 1) (χ : QState I) :
    cyclicPcStep n *ᵥ cyclicFiberState n m χ
      = cyclicFiberState n ((⟨m, hmM⟩ : Fin (2 * n + 1)) + 1).val χ := by
  funext x
  obtain ⟨q, j⟩ := x
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, cyclicPcStep, permMatrix,
    Matrix.of_apply, cyclicFiberState]
  by_cases hq : q.val = ((⟨m, hmM⟩ : Fin (2 * n + 1)) + 1).val
  · have hqs : q = ⟨m, hmM⟩ + 1 := Fin.ext hq
    rw [if_pos hq]
    rw [Finset.sum_eq_single ⟨m, hmM⟩
      (fun r _ hr => Finset.sum_eq_zero fun l _ => by
        by_cases hrm : r.val = m
        · exact absurd (Fin.ext hrm) hr
        · rw [if_neg hrm, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [Finset.sum_eq_single j
      (fun l _ hl => by
        rw [if_neg (show (q, j) ≠ (⟨m, hmM⟩ + 1, l) from
          fun h => hl (Prod.ext_iff.mp h).2.symm), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp [hqs]
  · rw [if_neg hq]
    apply Finset.sum_eq_zero
    intro r _
    apply Finset.sum_eq_zero
    intro l _
    by_cases hrm : r.val = m
    · have hr' : r = ⟨m, hmM⟩ := Fin.ext hrm
      subst hr'
      rw [if_neg (show (q, j) ≠ (⟨m, hmM⟩ + 1, l) from
        fun h => hq (congrArg Fin.val (Prod.ext_iff.mp h).1)), zero_mul]
    · rw [if_neg hrm, mul_zero]

/-- The cyclic simulation step first applies the counter-dependent gate and then increments the
program counter. -/
noncomputable def cyclicStep {n : ℕ} (gates : Fin n → Matrix I I ℂ) :
    Matrix (CyclicConfig n I) (CyclicConfig n I) ℂ :=
  cyclicPcStep n * cyclicGateStep gates

/-- The cyclic simulation step is unitary when all input gate matrices are unitary. -/
theorem cyclicStep_unitary {n : ℕ} (gates : Fin n → Matrix I I ℂ)
    (hU : ∀ k, gates k ∈ Matrix.unitaryGroup I ℂ) :
    cyclicStep gates ∈ Matrix.unitaryGroup (CyclicConfig n I) ℂ :=
  Submonoid.mul_mem _ (cyclicPcStep_unitary n) (cyclicGateStep_unitary gates hU)

/-- Before the end of the forward gate sequence, one cyclic step applies the gate at the current
counter and advances that counter. -/
theorem cyclicStep_mulVec_fiber {n : ℕ} (gates : Fin n → Matrix I I ℂ) (m : ℕ)
    (hm : m < n) (hmM : m < 2 * n + 1) (χ : QState I) :
    cyclicStep gates *ᵥ cyclicFiberState n m χ
      = cyclicFiberState n ((⟨m, hmM⟩ : Fin (2 * n + 1)) + 1).val (gates ⟨m, hm⟩ *ᵥ χ) := by
  rw [cyclicStep, ← Matrix.mulVec_mulVec, cyclicGateStep_mulVec_fiber gates m hmM χ,
    cyclicPcStep_mulVec_fiber n m hmM, cyclicFiberGate_of_lt gates m hm hmM]

/-- The finite quantum machine whose unitary step is the cyclic simulation of the given unitary
gate sequence. -/
noncomputable def cyclicMachine {n : ℕ} (gates : Fin n → Matrix I I ℂ)
    (hU : ∀ k, gates k ∈ Matrix.unitaryGroup I ℂ) : QTMachine (CyclicConfig n I) where
  step := cyclicStep gates
  wellFormed := cyclicStep_unitary gates hU

/-- For `k ≤ n`, applying the cyclic step `k` times from counter zero yields the circuit-prefix
output at counter `k`. -/
theorem cyclicStep_pow_mulVec_fiber {n : ℕ} (gates : Fin n → Matrix I I ℂ) (ψ : QState I) :
    ∀ (k : ℕ) (hk : k ≤ n),
      (cyclicStep gates) ^ k *ᵥ cyclicFiberState n 0 ψ
        = cyclicFiberState n k (Run 1 (circuitPrefix gates k hk) ψ) := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [pow_zero, Matrix.one_mulVec, show circuitPrefix gates 0 hk = [] from rfl, run_nil]
  | succ k ih =>
    intro hk
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    have hkn : k < n := Nat.lt_of_succ_le hk
    have hkM : k < 2 * n + 1 := by omega
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih hk',
      cyclicStep_mulVec_fiber gates k hkn hkM (Run 1 (circuitPrefix gates k hk') ψ)]
    have hval : ((⟨k, hkM⟩ : Fin (2 * n + 1)) + 1).val = k + 1 := by
      have h1 : (1 : Fin (2 * n + 1)).val = 1 := by
        haveI : NeZero (2 * n + 1) := ⟨by omega⟩
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by omega)
      have hlt : (⟨k, hkM⟩ : Fin (2 * n + 1)).val + (1 : Fin (2 * n + 1)).val < 2 * n + 1 := by
        rw [h1]
        show k + 1 < 2 * n + 1
        omega
      rw [Fin.val_add_eq_of_add_lt hlt, h1]
    rw [hval]
    have hrun : gates ⟨k, hkn⟩ *ᵥ (Run 1 (circuitPrefix gates k hk') ψ)
        = Run 1 (circuitPrefix gates (k + 1) hk) ψ := by
      rw [show circuitPrefix gates (k + 1) hk
          = circuitPrefix gates k hk' ++ [Step.gate (gates ⟨k, hkn⟩)] from rfl,
        run_append, run_gate, run_nil]
      rfl
    rw [hrun]

/-- After `k ≤ n` steps, the cyclic machine's state is the output of the first `k` circuit gates
embedded at counter `k`. -/
theorem circuit_run_semantics {n : ℕ} (gates : Fin n → Matrix I I ℂ)
    (hU : ∀ k, gates k ∈ Matrix.unitaryGroup I ℂ) (ψ : QState I) (k : ℕ) (hk : k ≤ n) :
    (cyclicMachine gates hU).step ^ k *ᵥ cyclicFiberState n 0 ψ
      = cyclicFiberState n k (Run 1 (circuitPrefix gates k hk) ψ) :=
  cyclicStep_pow_mulVec_fiber gates ψ k hk

/-- After `n` steps, the cyclic machine's state is the complete gate-circuit output embedded at
counter `n`. -/
theorem circuit_run_semantics_full {n : ℕ} (gates : Fin n → Matrix I I ℂ)
    (hU : ∀ k, gates k ∈ Matrix.unitaryGroup I ℂ) (ψ : QState I) :
    (cyclicMachine gates hU).step ^ n *ᵥ cyclicFiberState n 0 ψ
      = cyclicFiberState n n (Run 1 (gateCircuit gates) ψ) :=
  cyclicStep_pow_mulVec_fiber gates ψ n (le_refl n)

/-- A circuit prefix of length `k` uses zero oracle queries and has gate count and total size
both equal to `k`. -/
theorem stepCount_cyclicSimulation {n : ℕ} (gates : Fin n → Matrix I I ℂ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      QueryCount (circuitPrefix gates k hk) = 0 ∧
        GateCount (circuitPrefix gates k hk) = k ∧ Size (circuitPrefix gates k hk) = k := by
  intro k
  induction k with
  | zero => intro hk; exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨hq, hg, hs⟩ := ih (Nat.le_of_succ_le hk)
    have hdef : circuitPrefix gates (k + 1) hk
        = circuitPrefix gates k (Nat.le_of_succ_le hk) ++
            [Step.gate (gates ⟨k, Nat.lt_of_succ_le hk⟩)] := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hdef, queryCount_append, hq, queryCount_gate, queryCount_nil]
    · rw [hdef, gateCount_append, hg, gateCount_gate, gateCount_nil]
    · rw [hdef, size_append, hs, size_cons, size_nil]

end Qatlib.Concepts.HspRecovery.RecordExtract
