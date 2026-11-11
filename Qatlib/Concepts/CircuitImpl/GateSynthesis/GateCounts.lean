/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.GateSynthesis.GateCountsDefs
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.GateVocabulary.LocalReflectionGates

/-!
# Gate-count bounds and live-wire semantics

This module bounds the two-level counts and primitive-operation budgets used in the Section 8
synthesis arithmetic [BarencoEtAl1995]. It also records a density result for the complement of a
fixed-wire KAK circuit range and, under a Hausdorff-dimension hypothesis on the unitary target,
the existence of a unitary outside that range.

The `LiveState` interpreter tracks a Boolean register and a list of live wires through dynamic
operations. For programs whose extracted gate words contain valid X and CNOT codes, its register
updates agree with the quantum circuit action on computational basis states.

## Main statements

* `clause14_primitive_budget_bounds`: explicit lower and upper bounds proportional to `4 ^ n * n
  ^ 3`.
* `clause14_unitary_target_outside`: a unitary outside the fixed-wire circuit range under the
  stated dimension assumptions.
* `walkGoal_live_wire_quantum_semantics`: agreement between the classical register interpreter
  and quantum basis-state execution.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.CircuitImpl.GateSynthesis

open Matrix
open Qatlib
open scoped Classical BigOperators ENNReal

/-- For `n ≥ 1`, the two-level counts satisfy the stated bounds and the unitary and
special-unitary parameter counts at dimension `2 ^ n` are `4 ^ n` and `4 ^ n - 1`. -/
theorem clause14_section8_count_ledger (n : ℕ) (hn : 1 ≤ n) :
    4 ^ n ≤ 4 * reckTwoLevelLower n ∧
    reckTwoLevelLower n ≤ section8TwoLevelCount n ∧
    section8TwoLevelCount n ≤ 4 ^ n ∧
    unitaryParamCount (2 ^ n) = 4 ^ n ∧
    suParamCount (2 ^ n) = 4 ^ n - 1 := by
  obtain ⟨h1, h2, h3⟩ := section8TwoLevelCount_bounds n hn
  exact ⟨h1, h2, h3, unitaryParamCount_two_pow n, suParamCount_two_pow n⟩

/-- The cube of a natural number equals its product with itself three times. -/
theorem pow_three (n : ℕ) : n ^ 3 = n * n * n := by
  rw [Nat.pow_succ, Nat.pow_two]

/-- A natural number at least one is at most its square. -/
theorem le_mul_self (n : ℕ) (hn : 1 ≤ n) : n ≤ n * n := by
  have h2 : (1 : ℕ) ≤ n := hn
  have h3 : n * 1 ≤ n * n :=
    Nat.mul_le_mul (n₁ := n) (m₁ := 1) (n₂ := n) (m₂ := n) (Nat.le_refl n) h2
  exact Nat.le_trans (Nat.le_of_eq (Nat.mul_one n).symm) h3

/-- For `n ≥ 1`, the primitive budget lies between `12 * 4 ^ n * n ^ 3` and `7498 * 4 ^ n * n ^
3`. -/
theorem clause14_primitive_budget_bounds (n : ℕ) (hn : 1 ≤ n) :
    12 * 4 ^ n * n ^ 3 ≤ section8PrimitiveBudget n ∧
    section8PrimitiveBudget n ≤ 7498 * 4 ^ n * n ^ 3 := by
  have hcost_lo : 48 * n ^ 3 ≤ section8InstructionCost n := by
    have h1 : n ≤ 2 * n - 1 := by omega
    have h2 : 48 * n * n ≤ 48 * n * n + 2 * n + 3699 := by omega
    have hmul : n * (48 * n * n) ≤ (2 * n - 1) * (48 * n * n + 2 * n + 3699) :=
      Nat.mul_le_mul h1 h2
    calc 48 * n ^ 3 = n * (48 * n * n) := by rw [pow_three]; ring
      _ ≤ (2 * n - 1) * (48 * n * n + 2 * n + 3699) := hmul
      _ = section8InstructionCost n := rfl
  have hcost_hi : section8InstructionCost n ≤ 7498 * n ^ 3 := by
    have hnn : n ≤ n * n := le_mul_self n hn
    have h1 : 2 * n - 1 ≤ 2 * n := by omega
    have h2 : 48 * n * n + 2 * n + 3699 ≤ 3749 * n * n := by
      have ha : 2 * n ≤ 2 * n * n := by
        have h4 : 2 * n ≤ 2 * (n * n) :=
          Nat.mul_le_mul (n₁ := 2) (m₁ := n) (n₂ := 2) (m₂ := n * n) (Nat.le_refl 2) hnn
        calc 2 * n ≤ 2 * (n * n) := h4
          _ = 2 * n * n := by ring
      have hb : 3699 ≤ 3699 * n * n := by
        have h5 : (1 : ℕ) ≤ n * n := Nat.le_trans (by omega) hnn
        have h4 : 3699 * 1 ≤ 3699 * (n * n) :=
          Nat.mul_le_mul (n₁ := 3699) (m₁ := 1) (n₂ := 3699) (m₂ := n * n)
            (Nat.le_refl 3699) h5
        calc 3699 = 3699 * 1 := by ring
          _ ≤ 3699 * (n * n) := h4
          _ = 3699 * n * n := by ring
      calc 48 * n * n + 2 * n + 3699 ≤ 48 * n * n + 2 * n * n + 3699 * n * n :=
            Nat.add_le_add (Nat.add_le_add (by omega) ha) hb
        _ = 3749 * n * n := by ring
    have hmul : (2 * n - 1) * (48 * n * n + 2 * n + 3699) ≤ 2 * n * (3749 * n * n) :=
      Nat.mul_le_mul h1 h2
    calc section8InstructionCost n = (2 * n - 1) * (48 * n * n + 2 * n + 3699) := rfl
      _ ≤ 2 * n * (3749 * n * n) := hmul
      _ = 7498 * n ^ 3 := by rw [pow_three]; ring
  have hcnt : 4 ^ n ≤ 4 * section8TwoLevelCount n := by
    obtain ⟨h1, h2, _⟩ := section8TwoLevelCount_bounds n hn
    exact Nat.le_trans h1 (Nat.mul_le_mul_left 4 h2)
  have hcnt' : section8TwoLevelCount n ≤ 4 ^ n := by
    obtain ⟨_, _, h3⟩ := section8TwoLevelCount_bounds n hn
    exact h3
  have hlow : 4 ^ n * (48 * n ^ 3) ≤ 4 * section8PrimitiveBudget n := by
    have hA : 4 ^ n * (48 * n ^ 3) ≤ 4 * section8TwoLevelCount n * (48 * n ^ 3) :=
      Nat.mul_le_mul_right _ hcnt
    have hB : 4 * section8TwoLevelCount n * (48 * n ^ 3)
        ≤ 4 * section8TwoLevelCount n * section8InstructionCost n :=
      Nat.mul_le_mul_left _ hcost_lo
    have hC : 4 * section8TwoLevelCount n * section8InstructionCost n
        = 4 * section8PrimitiveBudget n := by
      unfold section8PrimitiveBudget
      ring
    exact hA.trans (hB.trans_eq hC)
  have hlow' : 4 * (12 * 4 ^ n * n ^ 3) ≤ 4 * section8PrimitiveBudget n := by
    have heq : 4 ^ n * (48 * n ^ 3) = 4 * (12 * 4 ^ n * n ^ 3) := by ring
    rw [← heq]
    exact hlow
  have hupp : section8PrimitiveBudget n ≤ 4 ^ n * (7498 * n ^ 3) := by
    have hA : section8TwoLevelCount n * section8InstructionCost n
        ≤ 4 ^ n * section8InstructionCost n := Nat.mul_le_mul_right _ hcnt'
    have hB : 4 ^ n * section8InstructionCost n ≤ 4 ^ n * (7498 * n ^ 3) :=
      Nat.mul_le_mul_left _ hcost_hi
    have hC : section8TwoLevelCount n * section8InstructionCost n
        = section8PrimitiveBudget n := by
      unfold section8PrimitiveBudget
      ring
    exact hC ▸ hA.trans hB
  refine ⟨Nat.le_of_mul_le_mul_left hlow' (by omega : (0 : ℕ) < 4), ?_⟩
  have heq : 4 ^ n * (7498 * n ^ 3) = 7498 * 4 ^ n * n ^ 3 := by ring
  rw [← heq]
  exact hupp

/-- The threshold inequality against `4 ^ n` is equivalent to the same inequality against the
unitary parameter count at dimension `2 ^ n`. -/
theorem clause14_threshold_equals_chart (n r : ℕ) :
    9 * r + 3 * n + 1 < 4 ^ n ↔ 9 * r + 3 * n + 1 < unitaryParamCount (2 ^ n) := by
  rw [unitaryParamCount_two_pow]

/-- The set of unitary complex matrices on the `n`-qubit computational basis. -/
def unitaryTarget {n : ℕ} : Set ((Fin n → Fin 2) → (Fin n → Fin 2) → ℂ) :=
  {M | M ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ}

/-- The complement of the fixed-wire KAK circuit range is dense in the ambient matrix space when
`15 * wires.length + 3 * n + 1 < 2 * 4 ^ n`. -/
theorem clause14_reachable_complement_dense {n : ℕ} (wires : List (Fin n × Fin n))
    (hlen : 15 * wires.length + 3 * n + 1 < 2 * 4 ^ n) :
    Dense (Set.range (kakCircuitFullFn wires)).compl := by
  refine dense_compl_of_dimH_lt_finrank ?_
  have h1 := barenco_kakFullForm_dimH_le wires
  have h2 : ((15 * wires.length + 3 * n + 1 : ℕ) : ℝ≥0∞)
      < ((2 * 4 ^ n : ℕ) : ℝ≥0∞) := Nat.cast_lt.2 hlen
  rw [qubitOperatorSpace_finrank]
  exact lt_of_le_of_lt h1 h2

/-- A unitary lies outside the fixed-wire KAK circuit range when the target has Hausdorff
dimension at least `4 ^ n` and `15 * wires.length + 3 * n + 1 < 4 ^ n`. -/
theorem clause14_unitary_target_outside {n : ℕ} (wires : List (Fin n × Fin n))
    (hdim : ((4 ^ n : ℕ) : ℝ≥0∞) ≤ dimH (unitaryTarget (n := n)))
    (hlen : 15 * wires.length + 3 * n + 1 < 4 ^ n) :
    ∃ V, V ∈ unitaryTarget (n := n) ∧ V ∉ Set.range (kakCircuitFullFn wires) := by
  obtain ⟨V, hV, hout⟩ :=
    barenco_existential_target_outside_full wires (unitaryTarget (n := n)) hdim
      (Nat.cast_lt.2 hlen)
  exact ⟨V, hV, hout⟩

/-- A Boolean register together with the list of wire indices currently recorded as live. -/
structure LiveState (N : ℕ) where

  bits : Reg N

  live : List ℕ

/-- The bit at wire `w` when `w < N`, and `none` when the wire is outside the register. -/
def liveBit {N : ℕ} (x : Reg N) (w : ℕ) : Option Bool :=
  if h : w < N then some (x ⟨w, h⟩) else none

/-- The Boolean-register action of X and CNOT codes, leaving the register unchanged for
unsupported codes or invalid wire choices. -/
def classicalAct {N : ℕ} (g : FiniteGateCode) (x : Reg N) : Reg N :=
  match g with
  | .x w =>
      if h : w < N then Function.update x ⟨w, h⟩ (!x ⟨w, h⟩) else x
  | .cx c t =>
      if hc : c < N then
        if ht : t < N then
          if c ≠ t then
            Function.update x ⟨t, ht⟩ (x ⟨t, ht⟩ ^^ x ⟨c, hc⟩)
          else x
        else x
      else x
  | _ => x

/-- The predicate selecting X codes on an in-range wire and CNOT codes on distinct in-range
control and target wires. -/
def classicalCodeOk (N : ℕ) : FiniteGateCode → Prop
  | .x w => w < N
  | .cx c t => c < N ∧ t < N ∧ c ≠ t
  | _ => False

/-- The predicate asserting that every code in a gate list satisfies `classicalCodeOk N`. -/
def classicalWord (N : ℕ) : List FiniteGateCode → Prop
  | [] => True
  | g :: gs => classicalCodeOk N g ∧ classicalWord N gs

/-- A nonempty classical gate word has a valid head code and a classical tail. -/
theorem classicalWord_head {N : ℕ} {g : FiniteGateCode} {gs : List FiniteGateCode}
    (hg : classicalWord N (g :: gs)) :
    classicalCodeOk N g ∧ classicalWord N gs := by
  simpa only [classicalWord] using! hg

/-- The tail of a nonempty classical gate word is classical. -/
theorem classicalWord_tail {N : ℕ} {g : FiniteGateCode} {gs : List FiniteGateCode}
    (hg : classicalWord N (g :: gs)) : classicalWord N gs :=
  (classicalWord_head hg).2

/-- One step of dynamic live-wire bookkeeping, including register updates for supported fixed
classical gates. -/
def liveStep {N : ℕ} (base : ℕ) (st : LiveState N) (op : DynOp) : LiveState N :=
  match op with
  | .alloc w =>
      if base ≤ w ∧ w ∉ st.live then ⟨st.bits, w :: st.live⟩ else st
  | .releaseClean w =>
      if base ≤ w ∧ w ∈ st.live ∧ liveBit st.bits w = some false then
        ⟨st.bits, st.live.erase w⟩
      else st
  | .releaseDirty w =>
      if base ≤ w ∧ w ∈ st.live then ⟨st.bits, st.live.erase w⟩ else st
  | .resetWire _ => st
  | .uncomputeWire _ => st
  | .fixedGate g => ⟨classicalAct g st.bits, st.live⟩
  | .oracleQuery _ => st

/-- The final live state obtained by folding `liveStep base` over the dynamic operation list. -/
def liveRun {N : ℕ} (base : ℕ) (ops : List DynOp) (st : LiveState N) : LiveState N :=
  ops.foldl (liveStep base) st

/-- The list of live states reached after each operation, excluding the initial state. -/
def liveTrace {N : ℕ} (base : ℕ) (ops : List DynOp) (st : LiveState N) : List (LiveState N) :=
  (ops.scanl (liveStep base) st).tail

/-- The maximum live-list length among the initial state and all states visited during the
operation list. -/
def livePeakLive {N : ℕ} (base : ℕ) (ops : List DynOp) (st : LiveState N) : ℕ :=
  (liveTrace base ops st).foldl (fun m s => max m s.live.length) st.live.length

/-- The maximum of the live-list length minus `base`, using natural-number subtraction, over the
initial and visited states. -/
def livePeakWorkspace {N : ℕ} (base : ℕ) (ops : List DynOp) (st : LiveState N) : ℕ :=
  (liveTrace base ops st).foldl (fun m s => max m (s.live.length - base)) (st.live.length - base)

/-- Applying a Pauli X gate on an in-range wire flips that bit of a computational basis state. -/
theorem applyGate_pauliX_ket {N : ℕ} (w : ℕ) (hw : w < N) (x : Reg N) :
    ApplyGate (wireGate N ⟨w, hw⟩ PauliX) (Ket x) =
      Ket (Function.update x ⟨w, hw⟩ (!x ⟨w, hw⟩)) := by
  rw [applyGate_wireGate_ket]
  by_cases hx : x ⟨w, hw⟩ = true
  · have h1 : PauliX false true = 1 := by
      simp [PauliX, Qatlib.Foundations.PureStateMath.permMatrix, Matrix.of_apply]
    have h2 : PauliX true true = 0 := by
      simp [PauliX, Qatlib.Foundations.PureStateMath.permMatrix, Matrix.of_apply]
    simp only [hx, h1, h2, one_smul, zero_smul, Bool.not_true]
    funext i
    simp
  · have hxf : x ⟨w, hw⟩ = false := Bool.eq_false_of_not_eq_true hx
    have h1 : PauliX false false = 0 := by
      simp [PauliX, Qatlib.Foundations.PureStateMath.permMatrix, Matrix.of_apply]
    have h2 : PauliX true false = 1 := by
      simp [PauliX, Qatlib.Foundations.PureStateMath.permMatrix, Matrix.of_apply]
    simp only [hxf, h1, h2, one_smul, zero_smul, Bool.not_false]
    funext i
    simp

/-- A valid classical gate code sends a computational basis ket to the ket of its `classicalAct`
register update. -/
theorem applyGate_classical_code {N : ℕ} (g : FiniteGateCode) (x : Reg N)
    (hg : classicalWord N [g]) :
    ApplyGate (finiteCodeMatrix N g) (Ket x) = Ket (classicalAct g x) := by
  cases g with
  | h w => exact False.elim (classicalWord_head hg).1
  | x w =>
      have hw : w < N := (classicalWord_head hg).1
      have hmat : finiteCodeMatrix N (.x w) = wireGate N ⟨w, hw⟩ PauliX := by
        simp [finiteCodeMatrix, hw]
      rw [hmat]
      have hclassical : classicalAct (.x w) x
          = Function.update x ⟨w, hw⟩ (!x ⟨w, hw⟩) := by
        simp [classicalAct, hw]
      rw [hclassical]
      exact applyGate_pauliX_ket w hw x
  | t w => exact False.elim (classicalWord_head hg).1
  | tdg w => exact False.elim (classicalWord_head hg).1
  | cx c t =>
      have hconj : c < N ∧ t < N ∧ c ≠ t := (classicalWord_head hg).1
      have hc : c < N := hconj.1
      have ht : t < N := hconj.2.1
      have hne : c ≠ t := hconj.2.2
      have hmat : finiteCodeMatrix N (.cx c t) = cnotGate N ⟨c, hc⟩ ⟨t, ht⟩ := by
        simp [finiteCodeMatrix, hc, ht, hne]
      rw [hmat]
      have hclassical : classicalAct (.cx c t) x
          = Function.update x ⟨t, ht⟩ (x ⟨t, ht⟩ ^^ x ⟨c, hc⟩) := by
        simp [classicalAct, hc, ht, hne]
      rw [hclassical]
      exact applyGate_cnotGate_ket N ⟨c, hc⟩ ⟨t, ht⟩ (by simpa using! hne) x

/-- For a dynamic program with a valid classical extracted gate word, quantum execution on a
basis ket agrees with the register component of `liveRun`. -/
theorem walkGoal_live_wire_quantum_semantics {N : ℕ} (base : ℕ) (ops : List DynOp)
    (x : Reg N) (live : List ℕ) (hclassical : classicalWord N (opsGates ops)) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (finiteCodeCircuit N (opsGates ops)) (Ket x) =
      Ket (liveRun base ops ⟨x, live⟩).bits := by
  induction ops generalizing x live with
  | nil =>
      simp [liveRun, opsGates, finiteCodeCircuit]
  | cons op rest ih =>
      cases op with
      | fixedGate g =>
          have hgt : classicalWord N (g :: opsGates rest) := by
            simpa only [opsGates] using! hclassical
          have hsingle : classicalWord N [g] := by
            have hh := (classicalWord_head hgt).1
            simp only [classicalWord]
            exact ⟨hh, trivial⟩
          rw [show opsGates (.fixedGate g :: rest) = g :: opsGates rest from rfl]
          rw [show finiteCodeCircuit N (g :: opsGates rest)
              = Step.gate (finiteCodeMatrix N g) :: finiteCodeCircuit N (opsGates rest) from rfl]
          rw [show Run 1 (Step.gate (finiteCodeMatrix N g) :: finiteCodeCircuit N (opsGates rest))
                (Ket x) = Run 1 (finiteCodeCircuit N (opsGates rest))
                  (ApplyGate (finiteCodeMatrix N g) (Ket x)) from rfl]
          rw [applyGate_classical_code g x hsingle]
          rw [show liveRun base (.fixedGate g :: rest) ⟨x, live⟩
              = liveRun base rest (liveStep base ⟨x, live⟩ (.fixedGate g)) from rfl]
          rw [show liveStep base ⟨x, live⟩ (.fixedGate g) = ⟨classicalAct g x, live⟩ from rfl]
          exact ih (classicalAct g x) live (classicalWord_tail hgt)
      | alloc w =>
          have hgt : classicalWord N (opsGates rest) := by
            simpa only [opsGates] using! hclassical
          rw [show opsGates (.alloc w :: rest) = opsGates rest from rfl]
          rw [show liveRun base (.alloc w :: rest) ⟨x, live⟩
              = liveRun base rest (liveStep base ⟨x, live⟩ (.alloc w)) from rfl]
          by_cases hb : base ≤ w ∧ w ∉ live
          · rw [show liveStep base ⟨x, live⟩ (.alloc w) = ⟨x, w :: live⟩ from by
                simp only [liveStep, if_pos hb]]
            exact ih x (w :: live) hgt
          · rw [show liveStep base ⟨x, live⟩ (.alloc w) = ⟨x, live⟩ from by
                simp only [liveStep, if_neg hb]]
            exact ih x live hgt
      | releaseClean w =>
          have hgt : classicalWord N (opsGates rest) := by
            simpa only [opsGates] using! hclassical
          rw [show opsGates (.releaseClean w :: rest) = opsGates rest from rfl]
          rw [show liveRun base (.releaseClean w :: rest) ⟨x, live⟩
              = liveRun base rest (liveStep base ⟨x, live⟩ (.releaseClean w)) from rfl]
          by_cases hb : base ≤ w ∧ w ∈ live ∧ liveBit x w = some false
          · rw [show liveStep base ⟨x, live⟩ (.releaseClean w) = ⟨x, live.erase w⟩ from by
                simp only [liveStep, if_pos hb]]
            exact ih x (live.erase w) hgt
          · rw [show liveStep base ⟨x, live⟩ (.releaseClean w) = ⟨x, live⟩ from by
                simp only [liveStep, if_neg hb]]
            exact ih x live hgt
      | releaseDirty w =>
          have hgt : classicalWord N (opsGates rest) := by
            simpa only [opsGates] using! hclassical
          rw [show opsGates (.releaseDirty w :: rest) = opsGates rest from rfl]
          rw [show liveRun base (.releaseDirty w :: rest) ⟨x, live⟩
              = liveRun base rest (liveStep base ⟨x, live⟩ (.releaseDirty w)) from rfl]
          by_cases hb : base ≤ w ∧ w ∈ live
          · rw [show liveStep base ⟨x, live⟩ (.releaseDirty w) = ⟨x, live.erase w⟩ from by
                simp only [liveStep, if_pos hb]]
            exact ih x (live.erase w) hgt
          · rw [show liveStep base ⟨x, live⟩ (.releaseDirty w) = ⟨x, live⟩ from by
                simp only [liveStep, if_neg hb]]
            exact ih x live hgt
      | resetWire w =>
          have hgt : classicalWord N (opsGates rest) := by
            simpa only [opsGates] using! hclassical
          rw [show opsGates (.resetWire w :: rest) = opsGates rest from rfl]
          rw [show liveRun base (.resetWire w :: rest) ⟨x, live⟩
              = liveRun base rest (liveStep base ⟨x, live⟩ (.resetWire w)) from rfl]
          rw [show liveStep base ⟨x, live⟩ (.resetWire w) = ⟨x, live⟩ from rfl]
          exact ih x live hgt
      | uncomputeWire w =>
          have hgt : classicalWord N (opsGates rest) := by
            simpa only [opsGates] using! hclassical
          rw [show opsGates (.uncomputeWire w :: rest) = opsGates rest from rfl]
          rw [show liveRun base (.uncomputeWire w :: rest) ⟨x, live⟩
              = liveRun base rest (liveStep base ⟨x, live⟩ (.uncomputeWire w)) from rfl]
          rw [show liveStep base ⟨x, live⟩ (.uncomputeWire w) = ⟨x, live⟩ from rfl]
          exact ih x live hgt
      | oracleQuery ws =>
          have hgt : classicalWord N (opsGates rest) := by
            simpa only [opsGates] using! hclassical
          rw [show opsGates (.oracleQuery ws :: rest) = opsGates rest from rfl]
          rw [show liveRun base (.oracleQuery ws :: rest) ⟨x, live⟩
              = liveRun base rest (liveStep base ⟨x, live⟩ (.oracleQuery ws)) from rfl]
          rw [show liveStep base ⟨x, live⟩ (.oracleQuery ws) = ⟨x, live⟩ from rfl]
          exact ih x live hgt

end Qatlib.Concepts.CircuitImpl.GateSynthesis

end
