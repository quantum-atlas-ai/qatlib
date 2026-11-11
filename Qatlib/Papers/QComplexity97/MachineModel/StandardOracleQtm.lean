/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QComplexity97.MachineModel.StandardOracleQtmDefs

/-!
# An explicit local oracle machine and its charges

The module verifies the five local well-formedness conditions for `oracleMachine` and equips it
with an answer function through `nativeOracle`. It evaluates the query row and shows that other
rows agree with the underlying local machine.

Each charged request records three access types and a fixed tariff sum. Under the explicit
intermediate mass bound, the accumulated slot bill is at most the step count times this sum,
while `copyProgram` preserves the oracle log. See [BernsteinVazirani1997].

## Main statements

* `nativeOracle_queryRow`: evaluates and normalizes the answer row.
* `nativeOracle_bill_le`: bounds the slot bill under the stated mass and tariff hypotheses.
* `clause3_complete`: collects local conditions and charging identities.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Papers.QComplexity97.MachineDefs.StandardOracleQtm

set_option autoImplicit false

namespace Qatlib.Papers.QComplexity97.MachineDefs
namespace StandardOracleQtm

open Matrix

/-- The full finite oracle state set consists of `read`, `ask`, `end`, and `halt`. -/
theorem oracleState_univ : (Finset.univ : Finset OracleState) =
    ({OracleState.read, OracleState.ask, OracleState.end, OracleState.halt} : Finset OracleState) := by
  decide

/-- The full finite oracle symbol set consists of `bit0`, `bit1`, and `blank`. -/
theorem oracleSymbol_univ : (Finset.univ : Finset OracleSymbol) =
    ({OracleSymbol.bit0, OracleSymbol.bit1, OracleSymbol.blank} : Finset OracleSymbol) := by
  decide

/-- The full finite move set consists of left, stay, and right moves. -/
theorem oracleMove_univ : (Finset.univ : Finset QtmMove) =
    ({QtmMove.left, QtmMove.stay, QtmMove.right} : Finset QtmMove) := by
  decide

/-- Distinct source state-symbol pairs pass the disjoint-support test `oracleDisjointCheck`. -/
theorem oracleSupport_disjoint : ∀ (v1 v2 : OracleState × OracleSymbol), v1 ≠ v2 →
    oracleDisjointCheck v1 v2 = true := by
  decide

/-- The amplitude `oracleMachineStep` is zero outside its specified support list. -/
theorem oracleStep_eq_zero_off {q : OracleState} {a : OracleSymbol} {d : QtmMove}
    {q' : OracleState} {b : OracleSymbol} (h : (d, q', b) ∉ oracleSupport q a) :
    oracleMachineStep q a d q' b = 0 := by
  simp [oracleMachineStep, h]

/-- Each row of `oracleMachineStep` has total squared amplitude one. -/
theorem oracleMachine_wf_norm : ∀ (q : OracleState) (a : OracleSymbol),
    ∑ q' : OracleState, ∑ b : OracleSymbol, ∑ d : QtmMove,
      ‖oracleMachineStep q a d q' b‖ ^ 2 = 1 := by
  intro q a
  rw [oracleState_univ, oracleSymbol_univ, oracleMove_univ]
  cases q <;> cases a <;> simp [oracleMachineStep, oracleSupport]

/-- Transition rows of `oracleMachineStep` at distinct source state-symbol pairs are orthogonal. -/
theorem oracleMachine_wf_sameCell : ∀ (q₁ : OracleState) (a₁ : OracleSymbol)
    (q₂ : OracleState) (a₂ : OracleSymbol), (q₁, a₁) ≠ (q₂, a₂) →
      ∑ q' : OracleState, ∑ b : OracleSymbol, ∑ d : QtmMove,
        star (oracleMachineStep q₁ a₁ d q' b) * oracleMachineStep q₂ a₂ d q' b = 0 := by
  intro q₁ a₁ q₂ a₂ hne
  have hdis : ∀ slot ∈ oracleSupportOf (q₁, a₁), slot ∉ oracleSupportOf (q₂, a₂) := by
    have h := oracleSupport_disjoint (q₁, a₁) (q₂, a₂) hne
    unfold oracleDisjointCheck at h
    rw [List.all_eq_true] at h
    intro slot hslot
    have h' := h slot hslot
    simp at h'
    exact h'
  have hterm : ∀ (q' : OracleState) (b : OracleSymbol) (d : QtmMove),
      star (oracleMachineStep q₁ a₁ d q' b) * oracleMachineStep q₂ a₂ d q' b = 0 := by
    intro q' b d
    by_cases hm₁ : (d, q', b) ∈ oracleSupportOf (q₁, a₁)
    · have hnot : (d, q', b) ∉ oracleSupportOf (q₂, a₂) := hdis (d, q', b) hm₁
      rw [oracleStep_eq_zero_off hnot]
      simp
    · rw [oracleStep_eq_zero_off hm₁]
      simp
  refine Finset.sum_eq_zero fun q' _ => ?_
  refine Finset.sum_eq_zero fun b _ => ?_
  exact Finset.sum_eq_zero fun d _ => hterm q' b d

/-- The right-moving and stay-moving transition rows have zero overlap in the stated local
condition. -/
theorem oracleMachine_wf_rightStay : ∀ (q₁ : OracleState) (a₁ : OracleSymbol)
    (q₂ : OracleState) (a₂ : OracleSymbol) (c d : OracleSymbol),
    ∑ q' : OracleState, oracleMachineStep q₁ a₁ QtmMove.right q' c *
      star (oracleMachineStep q₂ a₂ QtmMove.stay q' d) = 0 := by
  intro q₁ a₁ q₂ a₂ c d
  refine Finset.sum_eq_zero fun q' _ => ?_
  cases q₂ <;> cases a₂ <;> simp [oracleMachineStep, oracleSupport]

/-- The stay-moving and left-moving transition rows have zero overlap in the stated local
condition. -/
theorem oracleMachine_wf_stayLeft : ∀ (q₁ : OracleState) (a₁ : OracleSymbol)
    (q₂ : OracleState) (a₂ : OracleSymbol) (c d : OracleSymbol),
    ∑ q' : OracleState, oracleMachineStep q₁ a₁ QtmMove.stay q' c *
      star (oracleMachineStep q₂ a₂ QtmMove.left q' d) = 0 := by
  intro q₁ a₁ q₂ a₂ c d
  refine Finset.sum_eq_zero fun q' _ => ?_
  cases q₁ <;> cases a₁ <;> simp [oracleMachineStep, oracleSupport]

/-- The right-moving and left-moving transition rows have zero overlap in the stated local
condition. -/
theorem oracleMachine_wf_rightLeft : ∀ (q₁ : OracleState) (a₁ : OracleSymbol)
    (q₂ : OracleState) (a₂ : OracleSymbol) (c d : OracleSymbol),
    ∑ q' : OracleState, oracleMachineStep q₁ a₁ QtmMove.right q' c *
      star (oracleMachineStep q₂ a₂ QtmMove.left q' d) = 0 := by
  intro q₁ a₁ q₂ a₂ c d
  refine Finset.sum_eq_zero fun q' _ => ?_
  cases q₂ <;> cases a₂ <;> simp [oracleMachineStep, oracleSupport]

/-- The local QTM with start state `read`, blank symbol `blank`, and the verified transition
rule `oracleMachineStep`. -/
noncomputable def oracleMachine : LocalQTM OracleState OracleSymbol where
  blank := OracleSymbol.blank
  start := OracleState.read
  step := oracleMachineStep
  wf_norm := oracleMachine_wf_norm
  wf_sameCell := oracleMachine_wf_sameCell
  wf_rightStay := oracleMachine_wf_rightStay
  wf_stayLeft := oracleMachine_wf_stayLeft
  wf_rightLeft := oracleMachine_wf_rightLeft

/-- The oracle QTM formed from `oracleMachine` by designating `ask` as the query state and using
the answer function `ans`. -/
noncomputable def nativeOracle (ans : OracleSymbol → OracleSymbol) :
    OracleQTM OracleState OracleSymbol :=
  toOracleQTM oracleMachine OracleState.ask ans

/-- In state `ask`, the oracle transition has amplitude one exactly for a stay move retaining
`ask` and writing `ans a`, and zero otherwise; this row has squared amplitude sum one. -/
theorem nativeOracle_queryRow (ans : OracleSymbol → OracleSymbol) (a : OracleSymbol) :
    (∀ d q' b, oracleDelta (nativeOracle ans) OracleState.ask a d q' b
        = if d = QtmMove.stay ∧ q' = OracleState.ask ∧ b = ans a then 1 else 0) ∧
      (∑ d : QtmMove, ∑ q' : OracleState, ∑ b : OracleSymbol,
        ‖oracleDelta (nativeOracle ans) OracleState.ask a d q' b‖ ^ 2 = 1) :=
  toOracleQTM_queryRow oracleMachine OracleState.ask ans a

/-- At every state other than `ask`, the oracle transition agrees with `oracleMachineStep`. -/
theorem nativeOracle_nonQuery_eq (ans : OracleSymbol → OracleSymbol) (q : OracleState)
    (a : OracleSymbol) (hq : q ≠ OracleState.ask) (d : QtmMove) (q' : OracleState)
    (b : OracleSymbol) :
    oracleDelta (nativeOracle ans) q a d q' b = oracleMachineStep q a d q' b :=
  toOracleQTM_nonQuery_eq oracleMachine OracleState.ask ans q a hq d q' b

/-- The charge for a request records input access, label comparison, and record access in that
order. -/
theorem nativeOracle_charge_accesses
    (r : OracleRequest OracleState OracleSymbol) :
    (oracleCharge r).accesses = [.inputAccess, .labelCompare, .recordAccess] := rfl

/-- The fee for a charged request is `t.inputFee + t.labelFee + t.recordFee`. -/
theorem nativeOracle_charge_fee (t : OracleTariff) (r : OracleRequest OracleState OracleSymbol) :
    (oracleCharge r).fee t = t.inputFee + t.labelFee + t.recordFee := rfl

/-- Repeating a charged request `k` times has bill `k * (t.inputFee + t.labelFee +
t.recordFee)`. -/
theorem nativeOracle_bill_repeat (t : OracleTariff) (r : OracleRequest OracleState OracleSymbol)
    (k : ℕ) :
    oracleBillRepeat t (oracleCharge r) k = k * (t.inputFee + t.labelFee + t.recordFee) := rfl

/-- At every time strictly before `steps`, the total Born mass of the specified oracle window
evolution is at most one. -/
def NativeOracleUnitMass (w m steps : ℕ) (ans : OracleSymbol → OracleSymbol)
    (x : Fin m → OracleSymbol) : Prop :=
  ∀ j : ℕ, j < steps →
    ∑ c : WindowCfg w OracleState OracleSymbol,
      BornProb ((oracleWindowStep (t := w) (nativeOracle ans)) ^ j *ᵥ
        Ket (initWindowCfg (t := w) (nativeOracle ans).machine m x)) c ≤ 1

/-- With nonnegative component fees and the stated intermediate unit-mass bound, the oracle slot
bill is at most `steps * (t.inputFee + t.labelFee + t.recordFee)`. -/
theorem nativeOracle_bill_le {w : ℕ} (ans : OracleSymbol → OracleSymbol) (m steps : ℕ)
    (x : Fin m → OracleSymbol) (t : OracleTariff)
    (hfees : 0 ≤ t.inputFee ∧ 0 ≤ t.labelFee ∧ 0 ≤ t.recordFee)
    (hmass : NativeOracleUnitMass w m steps ans x) :
    oracleSlotBill (w := w) (nativeOracle ans) m steps x t
      ≤ steps * (t.inputFee + t.labelFee + t.recordFee) := by
  have hmass' := oracleQueryMass_le_steps_of_unitMass (w := w) (nativeOracle ans) m steps x hmass
  have htotal : 0 ≤ t.total := by
    unfold OracleTariff.total
    linarith [hfees.1, hfees.2.1, hfees.2.2]
  have hbill : oracleSlotBill (w := w) (nativeOracle ans) m steps x t
      = oracleQueryMass (w := w) (nativeOracle ans) m steps x * t.total := rfl
  rw [hbill]
  have hmul : oracleQueryMass (w := w) (nativeOracle ans) m steps x * t.total
      ≤ steps * t.total := by
    exact mul_le_mul_of_nonneg_right hmass' htotal
  have heq : steps * t.total = steps * (t.inputFee + t.labelFee + t.recordFee) := rfl
  rw [heq] at hmul
  exact hmul

set_option maxHeartbeats 800000 in

/-- Running `copyProgram` for any number of steps preserves the oracle log. -/
theorem nativeOracle_copy_not_charged (O : ℕ → List Bool → Bool) (k : ℕ)
    (s : Qatlib.Foundations.ClockedOracle.StackProgram.State) :
    (Qatlib.Foundations.ClockedOracle.StackProgram.run copyProgram O k s).log = s.log :=
  copyProgram_log O k s

/-- Starting from `[true, false]`, the displayed `copyProgram` run finishes with address
`[false, true]`, the halted flag set, and tick count `3 * [true, false].length + 2`. -/
theorem nativeOracle_copy_instance :
    (Qatlib.Foundations.ClockedOracle.StackProgram.run copyProgram (fun _ _ => false) (3 * [true, false].length + 2)
        (Qatlib.Foundations.ClockedOracle.StackProgram.init [true, false])).address = [false, true] ∧
      (Qatlib.Foundations.ClockedOracle.StackProgram.run copyProgram (fun _ _ => false) (3 * [true, false].length + 2)
        (Qatlib.Foundations.ClockedOracle.StackProgram.init [true, false])).halted = true ∧
      (Qatlib.Foundations.ClockedOracle.StackProgram.run copyProgram (fun _ _ => false) (3 * [true, false].length + 2)
        (Qatlib.Foundations.ClockedOracle.StackProgram.init [true, false])).ticks = 3 * [true, false].length + 2 := by
  have h := copyProgram_run [true, false] (fun _ _ => false)
    (Qatlib.Foundations.ClockedOracle.StackProgram.init [true, false]) [] rfl rfl rfl rfl
  rw [h]
  simp [Qatlib.Foundations.ClockedOracle.StackProgram.init, List.reverse_cons, List.append_nil]

/-- The explicit oracle machine satisfies the five local conditions and the stated access-list,
fee, repetition, and conditional slot-bill formulas; copying preserves the oracle log. -/
theorem clause3_complete :
    LocalQTMFiveConditions oracleMachine ∧
    (∀ (r : OracleRequest OracleState OracleSymbol),
      (oracleCharge r).accesses = [.inputAccess, .labelCompare, .recordAccess] ∧
        ∀ (t : OracleTariff), (oracleCharge r).fee t = t.inputFee + t.labelFee + t.recordFee) ∧
    (∀ (t : OracleTariff) (r : OracleRequest OracleState OracleSymbol) (k : ℕ),
      oracleBillRepeat t (oracleCharge r) k = k * (t.inputFee + t.labelFee + t.recordFee)) ∧
    (∀ (w m steps : ℕ) (ans : OracleSymbol → OracleSymbol) (x : Fin m → OracleSymbol)
      (t : OracleTariff),
      0 ≤ t.inputFee → 0 ≤ t.labelFee → 0 ≤ t.recordFee →
      NativeOracleUnitMass w m steps ans x →
      oracleSlotBill (w := w) (nativeOracle ans) m steps x t
        ≤ steps * (t.inputFee + t.labelFee + t.recordFee)) ∧
    (∀ (O : ℕ → List Bool → Bool) (k : ℕ) (s : Qatlib.Foundations.ClockedOracle.StackProgram.State),
      (Qatlib.Foundations.ClockedOracle.StackProgram.run copyProgram O k s).log = s.log) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨oracleMachine.wf_norm, oracleMachine.wf_sameCell, oracleMachine.wf_rightStay,
      oracleMachine.wf_stayLeft, oracleMachine.wf_rightLeft⟩
  · intro r
    refine ⟨nativeOracle_charge_accesses r, ?_⟩
    intro t
    exact nativeOracle_charge_fee t r
  · intro t r k
    exact nativeOracle_bill_repeat t r k
  · intro w m steps ans x t h1 h2 h3 hmass
    exact nativeOracle_bill_le ans m steps x t ⟨h1, h2, h3⟩ hmass
  · intro O k s
    exact nativeOracle_copy_not_charged O k s

end StandardOracleQtm
end Qatlib.Papers.QComplexity97.MachineDefs
