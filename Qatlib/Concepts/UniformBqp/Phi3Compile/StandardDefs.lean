/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.StandardModelDefs
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity

/-!
# Circuit specifications and QTM light-cone obstructions

This module introduces auxiliary circuit and machine specifications, including a Hadamard, T,
and controlled-NOT language and a polynomial clock requirement. It develops head light-cone
bounds for Boolean-tape QTM evolution.

The light-cone arguments refute `HeadStaySimulationSpec` and the local `DLambdaCorrespondence`
specification using a distant input bit. These results describe the precise resource constraints
of the stated specifications.

For background, see [BernsteinVazirani1997].

## Main statements

* `evolve_headCone`: evolved amplitudes vanish outside the head light cone.
* `clause1_headStaySimulationSpec_lightCone_false`: refutation of the head-stay specification.
* `clause2_dLambdaCorrespondence_lightCone_false`: refutation of the stated circuit
  correspondence.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false

namespace Qatlib.Concepts.UniformBqp.Phi3Compile

open Matrix Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.UniformBqp.Phi3Compile

/-- The existence of a unitary circuit with zero queries and at most `2 * t * steps` gates that
exactly reproduces the embedded window evolution and its configuration Born probabilities. -/
private def WindowSimulatesSteps {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) (n steps t : ℕ) : Prop :=
  ∃ C : Circuit (WReg t Q A),
    IsUnitaryCircuit C ∧ QueryCount C = 0 ∧ GateCount C ≤ 2 * t * steps ∧
      ∀ x : Fin n → A, ∀ cfg : WindowCfg t Q A,
        Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) C
            (Ket (windowEncode (initWindowCfg (t := t) M n x)))
          = windowEmbed ((windowStep (t := t) M) ^ steps *ᵥ
              Ket (initWindowCfg (t := t) M n x)) ∧
        BornProb (Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) C
            (Ket (windowEncode (initWindowCfg (t := t) M n x)))) (windowEncode cfg)
          = BornProb ((windowStep (t := t) M) ^ steps *ᵥ
              Ket (initWindowCfg (t := t) M n x)) cfg

/-- The specification that each positive polynomial budget has a tape clock that halts within
that budget and has no halting run with budget below the input length. -/
private def TimeConstructibleBudget : Prop :=
  ∀ c k : ℕ, 1 ≤ c → 1 ≤ k →
    ∃ (q : ℕ) (Clock : Turing.TM0.Machine (Option Bool) (Fin (q + 1))),
      (∀ x : List Bool,
        ∃ (s : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q + 1))),
          s ≤ c * x.length ^ k + c ∧
            TM0HaltRun Clock s (Turing.TM0.init (x.map some)) = some cfg ∧
            Turing.TM0.step Clock cfg = none) ∧
      (∀ (s : ℕ) (x : List Bool), s < x.length →
          TM0HaltRun Clock s (Turing.TM0.init (x.map some)) = none)

/-- The finite-register gate syntax with Hadamard, T, and controlled-NOT operations. -/
private inductive DLambdaOp (n : ℕ) where
  | hGate : Fin n → DLambdaOp n
  | tGate : Fin n → DLambdaOp n
  | cnot : Fin n → Fin n → DLambdaOp n

/-- The validity condition requiring distinct control and target wires for controlled-NOT; the
single-wire operations are always valid. -/
private def ValidDLambdaOp : ∀ {n : ℕ}, DLambdaOp n → Prop
  | _, .cnot i j => i ≠ j
  | _, _ => True

/-- The matrix interpretation of the Hadamard, T, and controlled-NOT gate syntax. -/
private noncomputable def dLambdaGateMatrix {n : ℕ} :
    DLambdaOp n → Matrix (Reg n) (Reg n) ℂ
  | .hGate i =>
    Matrix.of fun y x =>
      if (∀ k : Fin n, (k : ℕ) ≠ (i : ℕ) → y k = x k) then
        (if x i ∧ y i then (-1 : ℂ) else 1) / Real.sqrt 2
      else 0
  | .tGate i =>
    Matrix.of fun y x =>
      if ∀ k : Fin n, y k = x k then
        (if x i then Complex.exp (Complex.I * Real.pi / 4) else 1)
      else 0
  | .cnot i j =>
    Matrix.of fun y x =>
      if y = Function.update x j (Bool.xor (x j) (x i)) then 1 else 0

/-- Converts a list of gate operations into the circuit consisting of their matrix
interpretations. -/
private noncomputable def dLambdaCircuit {n : ℕ} (ops : List (DLambdaOp n)) :
    Circuit (Reg n) :=
  ops.map (fun op => Step.gate (dLambdaGateMatrix op))

/-- Encodes an operation using a Boolean tag and binary wire indices. -/
private def dLambdaOpEnc {n : ℕ} : DLambdaOp n → List Bool
  | .hGate i => false :: false :: i.val.bits
  | .tGate i => false :: true :: i.val.bits
  | .cnot i j => true :: (i.val.bits ++ [false] ++ j.val.bits)

/-- Encodes an operation list by concatenating the individual operation encodings. -/
private def dLambdaOpsEnc {n : ℕ} (ops : List (DLambdaOp n)) : List Bool :=
  ops.flatMap dLambdaOpEnc

/-- The conjunction of circuit unitarity and count guarantees, an acceptance-preserving local
QTM simulation with the specified polynomial bounds, and polynomial tape emission of circuit
sizes. -/
private def DLambdaCorrespondence : Prop :=
  (∀ (n : ℕ) (ops : List (DLambdaOp n)), (∀ op ∈ ops, ValidDLambdaOp op) →
      IsUnitaryCircuit (dLambdaCircuit ops) ∧
        GateCount (dLambdaCircuit ops) = ops.length ∧
        QueryCount (dLambdaCircuit ops) = 0) ∧
    (∀ (n : ℕ) (ops : List (DLambdaOp n)), (∀ op ∈ ops, ValidDLambdaOp op) →
        ∀ (hn : 0 < n),
      ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (qacc : Q) (M : LocalQTM Q Bool)
          (w t : ℕ),
        0 < w ∧ 0 < t ∧ n ≤ w ∧ w ≤ (n + ops.length + 2) ^ 6 ∧
          t ≤ (ops.length + 2) ^ 6 ∧ LocalQTMFiveConditions M ∧
          ∀ x : Reg n,
            (∑ c ∈ Finset.univ.filter (fun c => c.state = qacc),
                BornProb ((windowStep (t := w) M) ^ t *ᵥ
                  Ket (initWindowCfg (t := w) M n x)) c)
            = AcceptProb (Run (1 : Matrix (Reg n) (Reg n) ℂ) (dLambdaCircuit ops)
                (Ket x)) hn) ∧
    (∃ (q c d : ℕ) (emitter : Turing.TM0.Machine (Option Bool) (Fin (q + 1))),
        ∀ (n : ℕ) (ops : List (DLambdaOp n)),
          TM0EmitsPoly emitter c d (n.bits ++ [false] ++ dLambdaOpsEnc ops)
            ((Size (dLambdaCircuit ops)).bits ++ [false]))

/-- The oracle query mass multiplied by the sum of the query, computation, and routing tariffs. -/
private noncomputable def oracleTariffBill {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] {w : ℕ} (O : OracleQTM Q A) (m steps : ℕ)
    (x : Fin m → A) (qf cf rf : ℝ) : ℝ :=
  oracleQueryMass (w := w) O m steps x * (qf + cf + rf)

section LightCone

/-- Flips the Boolean tape symbol at a chosen cell while preserving the head and internal state. -/
private def flipCfg {Q : Type} {w : ℕ} (j₀ : Fin (2 * w + 1)) (c : WindowCfg w Q Bool) :
    WindowCfg w Q Bool where
  head := c.head
  state := c.state
  tape := fun j => if j = j₀ then !c.tape j else c.tape j

/-- Flipping the same configuration cell twice returns the original configuration. -/
private theorem flipCfg_involutive {Q : Type} {w : ℕ} (j₀ : Fin (2 * w + 1))
    (c : WindowCfg w Q Bool) : flipCfg j₀ (flipCfg j₀ c) = c := by
  have htp : (flipCfg j₀ (flipCfg j₀ c)).tape = c.tape := by
    funext j
    by_cases hj : j = j₀ <;> simp [flipCfg, hj]
  cases c
  simp only [flipCfg, WindowCfg.mk.injEq]
  exact ⟨trivial, trivial, htp⟩

/-- Flipping a fixed tape cell is a bijection on window configurations. -/
private theorem flipCfg_bijective {Q : Type} {w : ℕ} (j₀ : Fin (2 * w + 1)) :
    Function.Bijective (flipCfg (Q := Q) (w := w) j₀) := by
  constructor
  · intro a b hab
    have h := congrArg (flipCfg j₀) hab
    rw [flipCfg_involutive, flipCfg_involutive] at h
    exact h
  · intro b
    exact ⟨flipCfg j₀ b, flipCfg_involutive j₀ b⟩

/-- Flipping a tape cell preserves the internal state of the configuration. -/
private theorem flipCfg_state {Q : Type} {w : ℕ} (j₀ : Fin (2 * w + 1))
    (c : WindowCfg w Q Bool) : (flipCfg j₀ c).state = c.state := rfl

/-- A successful head move changes the cell index by at most one. -/
private theorem moveCell_dist {w : ℕ} (d : QtmMove) (h h' : Fin (2 * w + 1))
    (hm : moveCell d h = some h') : h'.val ≤ h.val + 1 ∧ h.val ≤ h'.val + 1 := by
  cases d with
  | left =>
    simp only [moveCell] at hm
    split at hm
    · exact absurd hm (by simp)
    · rw [Option.some.injEq] at hm
      obtain rfl := hm
      show h.val - 1 ≤ h.val + 1 ∧ h.val ≤ h.val - 1 + 1
      omega
  | stay =>
    rw [moveCell, Option.some.injEq] at hm
    obtain rfl := hm
    omega
  | right =>
    simp only [moveCell] at hm
    split at hm
    · exact absurd hm (by simp)
    · rw [Option.some.injEq] at hm
      obtain rfl := hm
      show h.val + 1 ≤ h.val + 1 ∧ h.val ≤ h.val + 1 + 1
      omega

/-- A window transition has zero amplitude when its source and target heads are at least two
cells apart. -/
private theorem windowStep_zero_of_far {Q : Type} [Fintype Q] [DecidableEq Q] {w : ℕ}
    (M : LocalQTM Q Bool) (c d : WindowCfg w Q Bool)
    (hfar : d.head.val + 2 ≤ c.head.val ∨ c.head.val + 2 ≤ d.head.val) :
    windowStep (t := w) M c d = 0 := by
  simp only [windowStep, Matrix.of_apply]
  refine Finset.sum_eq_zero ?_
  intro dd _
  refine Finset.sum_eq_zero ?_
  intro q' _
  refine Finset.sum_eq_zero ?_
  intro b _
  rw [if_neg]
  intro hcond
  rcases hcond with ⟨hmove, -⟩
  obtain ⟨h1, h2⟩ := moveCell_dist dd d.head c.head hmove
  omega

/-- Evolution from a configuration with centered head has zero amplitude outside the head light
cone of radius equal to the step count. -/
private theorem evolve_headCone {Q : Type} [Fintype Q] [DecidableEq Q] {w : ℕ}
    (M : LocalQTM Q Bool) (i : WindowCfg w Q Bool) (hi : i.head.val = w) :
    ∀ (t : ℕ) (c : WindowCfg w Q Bool),
      ¬(w ≤ c.head.val + t ∧ c.head.val ≤ w + t) →
      ((windowStep (t := w) M) ^ t *ᵥ Ket i) c = 0 := by
  intro t
  induction t with
  | zero =>
    intro c hc
    rw [pow_zero, Matrix.one_mulVec]
    by_cases hci : c = i
    · rw [hci, hi] at hc
      simp at hc
    · simp [Ket, hci]
  | succ t ih =>
    intro c hc
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    have hsum : (((windowStep (t := w) M) *ᵥ
        ((windowStep (t := w) M) ^ t *ᵥ Ket i)) c) =
        ∑ d : WindowCfg w Q Bool,
          windowStep (t := w) M c d * ((windowStep (t := w) M) ^ t *ᵥ Ket i) d := by
      simp [Matrix.mulVec, dotProduct]
    rw [hsum]
    refine Finset.sum_eq_zero ?_
    intro d _
    by_cases hcone : (w ≤ d.head.val + t ∧ d.head.val ≤ w + t)
    · have hzero : windowStep (t := w) M c d = 0 := by
        refine windowStep_zero_of_far M c d ?_
        have h1 : d.head.val ≤ w + t := hcone.2
        have h2 : w ≤ d.head.val + t := hcone.1
        omega
      rw [hzero, zero_mul]
    · rw [ih d hcone, mul_zero]

/-- Flipping a cell away from the source head can be transferred between the source and target
of a window transition without changing its amplitude. -/
private theorem windowStep_flip {Q : Type} [Fintype Q] [DecidableEq Q] {w : ℕ}
    (M : LocalQTM Q Bool) (j₀ : Fin (2 * w + 1)) (c e : WindowCfg w Q Bool)
    (hj : e.head ≠ j₀) :
    windowStep (t := w) M c (flipCfg j₀ e) = windowStep (t := w) M (flipCfg j₀ c) e := by
  have tapeImp : ∀ (b : Bool),
      (∀ j : Fin (2 * w + 1),
          c.tape j = if j = e.head then b else (if j = j₀ then !e.tape j else e.tape j)) →
      ∀ j : Fin (2 * w + 1),
        (if j = j₀ then !c.tape j else c.tape j) = if j = e.head then b else e.tape j := by
    intro b h1 j
    by_cases hjj : j = j₀
    · have hne : ¬(j₀ = e.head) := fun hh => hj hh.symm
      have h1j := h1 j₀
      rw [if_pos rfl, if_neg hne] at h1j
      subst hjj
      rw [if_pos rfl, if_neg hne, h1j]
      simp
    · rw [if_neg hjj]
      have h1j := h1 j
      rw [if_neg hjj] at h1j
      exact h1j
  have tapeImp' : ∀ (b : Bool),
      (∀ j : Fin (2 * w + 1),
          (if j = j₀ then !c.tape j else c.tape j) = if j = e.head then b else e.tape j) →
      ∀ j : Fin (2 * w + 1),
        c.tape j = if j = e.head then b else (if j = j₀ then !e.tape j else e.tape j) := by
    intro b h2 j
    by_cases hjj : j = j₀
    · have hne : ¬(j₀ = e.head) := fun hh => hj hh.symm
      have h2j := h2 j₀
      rw [if_pos rfl, if_neg hne] at h2j
      subst hjj
      rw [if_pos rfl, ← h2j]
      simp [hne]
    · rw [if_neg hjj]
      have h2j := h2 j
      rw [if_neg hjj] at h2j
      exact h2j
  simp only [windowStep, Matrix.of_apply]
  simp only [flipCfg]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun q' _ =>
    Finset.sum_congr rfl fun b _ => ?_
  by_cases hmove : moveCell d e.head = some c.head ∧ c.state = q' ∧
      ∀ j : Fin (2 * w + 1),
        c.tape j = if j = e.head then b else (if j = j₀ then !e.tape j else e.tape j)
  · have hcond2 : moveCell d e.head = some c.head ∧ c.state = q' ∧
        ∀ j : Fin (2 * w + 1),
          (if j = j₀ then !c.tape j else c.tape j) = if j = e.head then b else e.tape j :=
      ⟨hmove.1, hmove.2.1, tapeImp b hmove.2.2⟩
    rw [if_pos hmove, if_pos hcond2]
    by_cases hh : e.head = j₀
    · exact absurd hh hj
    · rw [if_neg hh]
  · have hcond2 : ¬(moveCell d e.head = some c.head ∧ c.state = q' ∧
        ∀ j : Fin (2 * w + 1),
          (if j = j₀ then !c.tape j else c.tape j) = if j = e.head then b else e.tape j) :=
      fun hcond => hmove ⟨hcond.1, hcond.2.1, tapeImp' b hcond.2.2⟩
    rw [if_neg hmove, if_neg hcond2]

/-- Before a distant flipped cell can be reached, the two evolutions have equal amplitudes at
configurations related by that flip. -/
private theorem evolve_flip {Q : Type} [Fintype Q] [DecidableEq Q] {w : ℕ}
    (M : LocalQTM Q Bool) (j₀ : Fin (2 * w + 1)) (i i' : WindowCfg w Q Bool)
    (hflip : flipCfg j₀ i = i') (hi : i.head.val = w) :
    ∀ (t : ℕ), t < j₀.val - w →
      ∀ c : WindowCfg w Q Bool,
        ((windowStep (t := w) M) ^ t *ᵥ Ket i) c
          = ((windowStep (t := w) M) ^ t *ᵥ Ket i') (flipCfg j₀ c) := by
  have hi' : i'.head.val = w := by
    rw [← hflip]
    exact hi
  intro t
  induction t with
  | zero =>
    intro _ c
    rw [pow_zero, Matrix.one_mulVec, Matrix.one_mulVec]
    by_cases hc : c = i
    · subst hc
      rw [hflip]
      simp [Ket]
    · have hne : flipCfg j₀ c ≠ i' := by
        intro h
        have h2 := congrArg (flipCfg j₀) h
        rw [flipCfg_involutive, ← hflip, flipCfg_involutive] at h2
        exact hc h2
      simp [Ket, hc, hne]
  | succ t ih =>
    intro ht c
    have htS : t < j₀.val - w := by omega
    rw [pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hsumL : ((windowStep (t := w) M) *ᵥ
        ((windowStep (t := w) M) ^ t *ᵥ Ket i)) c =
        ∑ d : WindowCfg w Q Bool,
          windowStep (t := w) M c d * ((windowStep (t := w) M) ^ t *ᵥ Ket i) d := by
      simp [Matrix.mulVec, dotProduct]
    have hsumR : ((windowStep (t := w) M) *ᵥ
        ((windowStep (t := w) M) ^ t *ᵥ Ket i')) (flipCfg j₀ c) =
        ∑ e : WindowCfg w Q Bool,
          windowStep (t := w) M (flipCfg j₀ c) e * ((windowStep (t := w) M) ^ t *ᵥ Ket i') e := by
      simp [Matrix.mulVec, dotProduct]
    rw [hsumL, hsumR]
    rw [Finset.sum_congr rfl (fun d _ => by rw [ih htS d])]
    have hreindex : (∑ d : WindowCfg w Q Bool,
          windowStep (t := w) M c d * ((windowStep (t := w) M) ^ t *ᵥ Ket i') (flipCfg j₀ d))
        = (∑ e : WindowCfg w Q Bool,
          windowStep (t := w) M c (flipCfg j₀ e)
            * ((windowStep (t := w) M) ^ t *ᵥ Ket i') e) :=
      Finset.sum_bijective (flipCfg j₀) (flipCfg_bijective j₀)
        (fun _ => iff_of_true (Finset.mem_univ _) (Finset.mem_univ _))
        (fun d _ => by rw [flipCfg_involutive])
    rw [hreindex]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases hj : e.head = j₀
    · have hzero : ((windowStep (t := w) M) ^ t *ᵥ Ket i') e = 0 := by
        refine evolve_headCone M i' hi' t e ?_
        rw [hj]
        omega
      rw [hzero, mul_zero, mul_zero]
    · rw [windowStep_flip M j₀ c e hj]

/-- Flipping an initially distant tape cell does not change acceptance mass before the head can
reach that cell. -/
private theorem acceptMass_lightCone {Q : Type} [Fintype Q] [DecidableEq Q] {w : ℕ}
    (M : LocalQTM Q Bool) (qacc : Q) (j₀ : Fin (2 * w + 1)) (i i' : WindowCfg w Q Bool)
    (hflip : flipCfg j₀ i = i') (hi : i.head.val = w) (t : ℕ) (ht : t < j₀.val - w) :
    (∑ c ∈ Finset.univ.filter (fun c => c.state = qacc),
        BornProb ((windowStep (t := w) M) ^ t *ᵥ Ket i) c)
      = (∑ c ∈ Finset.univ.filter (fun c => c.state = qacc),
        BornProb ((windowStep (t := w) M) ^ t *ᵥ Ket i') c) := by
  have hconj := evolve_flip M j₀ i i' hflip hi t ht
  refine Finset.sum_bijective (flipCfg j₀) (flipCfg_bijective j₀) ?_ ?_
  · intro c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, flipCfg_state]
  · intro c _
    simp only [BornProb]
    rw [hconj c]

end LightCone

/-- The all-false Boolean input on 730 wires. -/
private def zeroInput : Reg 730 := fun _ => false

/-- The 730-bit input whose only true bit is at index 729. -/
private def farInput : Reg 730 := fun i => if i = ⟨729, by omega⟩ then true else false

/-- Every bit of `zeroInput` is false. -/
private theorem zeroInput_eq (i : Fin 730) : zeroInput i = false := rfl

/-- The bit of `farInput` at index 729 is true. -/
private theorem farInput_self : farInput ⟨729, by omega⟩ = true := by
  rw [farInput]
  exact if_pos rfl

/-- Every bit of `farInput` away from index 729 is false. -/
private theorem farInput_ne {i : Fin 730} (h : i ≠ ⟨729, by omega⟩) : farInput i = false := by
  rw [farInput, if_neg h]

/-- The register transformation that toggles wire zero under the control of wire 729. -/
private def cnotPerm : Reg 730 → Reg 730 :=
  fun y => Function.update y ⟨0, by omega⟩ (Bool.xor (y ⟨0, by omega⟩) (y ⟨729, by omega⟩))

/-- Applying the distant controlled-NOT register transformation twice returns the original
register. -/
private theorem cnotPerm_involutive : Function.Involutive cnotPerm := by
  intro y
  have hcancel : ∀ a b : Bool, Bool.xor (Bool.xor a b) b = a := by
    intro a b; cases a <;> cases b <;> rfl
  funext j
  by_cases hj : j = ⟨0, by omega⟩
  · subst hj
    have h729 : (cnotPerm y) ⟨729, by omega⟩ = y ⟨729, by omega⟩ := by
      show (Function.update y ⟨0, by omega⟩ _) ⟨729, by omega⟩ = y ⟨729, by omega⟩
      exact Function.update_of_ne (by decide) _ _
    show Bool.xor ((cnotPerm y) ⟨0, by omega⟩) ((cnotPerm y) ⟨729, by omega⟩)
        = y ⟨0, by omega⟩
    rw [h729]
    show Bool.xor (Bool.xor (y ⟨0, by omega⟩) (y ⟨729, by omega⟩)) (y ⟨729, by omega⟩)
        = y ⟨0, by omega⟩
    exact hcancel _ _
  · have h0 : (cnotPerm (cnotPerm y)) j = (cnotPerm y) j := by
      show (Function.update (cnotPerm y) ⟨0, by omega⟩ _) j = (cnotPerm y) j
      exact Function.update_of_ne hj _ _
    have h1 : (cnotPerm y) j = y j := by
      show (Function.update y ⟨0, by omega⟩ _) j = y j
      exact Function.update_of_ne hj _ _
    rw [h0, h1]

/-- A basis ket has zero Born probability at a distinct basis register. -/
private theorem bornProb_ket_ne {n : ℕ} {z y : Reg n} (h : y ≠ z) : BornProb (Ket z) y = 0 := by
  show ‖(if y = z then (1 : ℂ) else 0)‖ ^ 2 = 0
  rw [if_neg h]
  simp

/-- A basis ket has Born probability one at its own basis register. -/
private theorem bornProb_ket_self {n : ℕ} (z : Reg n) : BornProb (Ket z) z = 1 := by
  show ‖(if z = z then (1 : ℂ) else 0)‖ ^ 2 = 1
  rw [if_pos rfl]
  simp

/-- Running the permutation matrix of an involutive register map on a basis ket gives the ket of
its image. -/
private theorem run_permKet {n : ℕ} (σ : Reg n → Reg n) (_hσ : Function.Involutive σ)
    (x : Reg n) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) [Step.gate (permMatrix σ)] (Ket x) = Ket (σ x) := by
  have hstep : ApplyGate (permMatrix σ) (Ket x) = Ket (σ x) := by
    funext y
    have hsum : (permMatrix σ *ᵥ Ket x) y
        = ∑ j : Reg n, permMatrix σ y j * Ket x j := by
      simp [Matrix.mulVec, dotProduct]
    have hket : Ket (σ x) y = (if y = σ x then (1 : ℂ) else 0) := rfl
    have hperm : permMatrix σ y x = (if y = σ x then (1 : ℂ) else 0) := rfl
    have hself : Ket x x = (1 : ℂ) := by
      show (if x = x then (1 : ℂ) else 0) = 1
      exact if_pos rfl
    show (permMatrix σ *ᵥ Ket x) y = Ket (σ x) y
    rw [hsum, hket]
    rw [Finset.sum_eq_single x (fun j _ hj => by
        have hk : Ket x j = 0 := by
          show (if j = x then (1 : ℂ) else 0) = 0
          rw [if_neg hj]
        rw [hk, mul_zero])
      (fun h => absurd (Finset.mem_univ x) h)]
    rw [hperm, hself]
    by_cases hy : y = σ x
    · rw [if_pos hy, mul_one]
    · rw [if_neg hy]
      norm_num
  exact hstep

set_option maxRecDepth 20000 in

/-- The acceptance probability of a basis ket is one exactly when its first bit is true, and is
zero otherwise. -/
private theorem acceptProb_ket {n : ℕ} (hn : 0 < n) (z : Reg n) :
    AcceptProb (Ket z) hn = (if z ⟨0, hn⟩ = true then (1 : ℝ) else 0) := by
  unfold AcceptProb MeasureProb
  by_cases hz : z ⟨0, hn⟩ = true
  · have hmem : z ∈ Finset.univ.filter (fun x : Reg n => x ⟨0, hn⟩ = true) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hz
    rw [Finset.sum_eq_single z (fun _ _ hye => bornProb_ket_ne hye)
      (fun h => absurd hmem h), if_pos hz]
    exact bornProb_ket_self z
  · have hnm : z ∉ Finset.univ.filter (fun x : Reg n => x ⟨0, hn⟩ = true) := by
      intro h
      exact hz (Finset.mem_filter.mp h).2
    rw [if_neg hz]
    exact Finset.sum_eq_zero fun y hy => bornProb_ket_ne (by
      intro e
      subst e
      exact hnm hy)

/-- The initialized tape for `farInput` is obtained from that for `zeroInput` by flipping the
cell at offset 730 from the window center. -/
private theorem initTape_eq_flip {w : ℕ} (blank : Bool) (j₀ : Fin (2 * w + 1))
    (hj0val : j₀.val = w + 730) :
    ∀ j : Fin (2 * w + 1),
      (if h : w < j.val ∧ j.val ≤ w + 730 then farInput ⟨j.val - w - 1, by omega⟩ else blank)
        = (if j = j₀ then
            !(if h : w < j.val ∧ j.val ≤ w + 730 then
                zeroInput ⟨j.val - w - 1, by omega⟩ else blank)
          else
            (if h : w < j.val ∧ j.val ≤ w + 730 then
                zeroInput ⟨j.val - w - 1, by omega⟩ else blank)) := by
  intro j
  by_cases hj : j = j₀
  · have hjv : j.val = w + 730 := (congrArg Fin.val hj).trans hj0val
    rw [if_pos hj]
    have hreg : w < j.val ∧ j.val ≤ w + 730 := ⟨by omega, by omega⟩
    rw [dif_pos hreg, dif_pos hreg]
    have hfar : farInput ⟨j.val - w - 1, by omega⟩ = true := by
      have hidx : (⟨j.val - w - 1, by omega⟩ : Fin 730) = ⟨729, by omega⟩ :=
        Fin.ext (show j.val - w - 1 = 729 by omega)
      rw [hidx, farInput_self]
    rw [hfar, zeroInput_eq]
    rfl
  · have hjv : j.val ≠ w + 730 := fun h => hj (Fin.ext (h.trans hj0val.symm))
    by_cases hreg : w < j.val ∧ j.val ≤ w + 730
    · rw [dif_pos hreg, if_neg hj, dif_pos hreg]
      have hne : ¬(j.val - w - 1 = 729) := by omega
      have hfar : farInput ⟨j.val - w - 1, by omega⟩ = false := by
        rw [farInput, if_neg (fun h => hne (congrArg Fin.val h))]
      rw [hfar, zeroInput_eq]
    · rw [dif_neg hreg, if_neg hj, dif_neg hreg]

/-- The head-stay simulation specification is false, as witnessed by the distant-bit light-cone
obstruction. -/
theorem clause1_headStaySimulationSpec_lightCone_false : ¬ HeadStaySimulationSpec := by
  intro hspec
  have hunit : IsUnitaryCircuit [Step.gate (permMatrix cnotPerm)] :=
    (isUnitaryCircuit_gate (permMatrix cnotPerm) []).mpr
      ⟨permMatrix_unitary cnotPerm_involutive, isUnitaryCircuit_nil⟩
  obtain ⟨Q, _hf, _hd, qacc, M, w, t, _hw0, _ht0, hnw, htbound, _hfive, hsim⟩ :=
    hspec 730 [Step.gate (permMatrix cnotPerm)] (by norm_num) hunit
  have hsize : Size [Step.gate (permMatrix cnotPerm)] = 1 := rfl
  have ht729 : t ≤ 729 := by
    have h := htbound
    rw [hsize] at h
    norm_num at h
    exact h
  have hj0lt : w + 730 < 2 * w + 1 := by omega
  obtain ⟨j₀, hj0val⟩ : ∃ j₀ : Fin (2 * w + 1), j₀.val = w + 730 :=
    ⟨⟨w + 730, hj0lt⟩, rfl⟩
  have hi : (initWindowCfg (t := w) M 730 zeroInput).head.val = w := rfl
  have hflip : flipCfg j₀ (initWindowCfg (t := w) M 730 zeroInput)
      = initWindowCfg (t := w) M 730 farInput := by
    simp only [flipCfg, initWindowCfg, WindowCfg.mk.injEq]
    refine ⟨trivial, trivial, funext fun j => (initTape_eq_flip M.blank j₀ hj0val j).symm⟩
  have hfar : t < j₀.val - w := by
    rw [hj0val]
    omega
  have hx0 := hsim zeroInput
  have hx1 := hsim farInput
  rw [run_permKet cnotPerm cnotPerm_involutive zeroInput,
    acceptProb_ket (by norm_num : 0 < 730) (cnotPerm zeroInput)] at hx0
  rw [run_permKet cnotPerm cnotPerm_involutive farInput,
    acceptProb_ket (by norm_num : 0 < 730) (cnotPerm farInput)] at hx1
  have h0 : cnotPerm zeroInput ⟨0, by omega⟩ = false := rfl
  have hne0 : (⟨0, by omega⟩ : Fin 730) ≠ ⟨729, by omega⟩ := by
    intro h
    have hval : (0 : ℕ) = 729 := congrArg Fin.val h
    omega
  have h1 : cnotPerm farInput ⟨0, by omega⟩ = true := by
    show Bool.xor (farInput ⟨0, by omega⟩) (farInput ⟨729, by omega⟩) = true
    rw [farInput_ne hne0, farInput_self]
    rfl
  rw [h0, if_neg (by simp)] at hx0
  rw [h1, if_pos rfl] at hx1
  have hlc := acceptMass_lightCone M qacc j₀
    (initWindowCfg (t := w) M 730 zeroInput) (initWindowCfg (t := w) M 730 farInput)
    hflip hi t hfar
  rw [hx0, hx1] at hlc
  exact absurd hlc (by norm_num)

set_option maxRecDepth 20000 in

/-- A single controlled-NOT operation maps a basis ket to the ket obtained by toggling the
target by the control bit. -/
private theorem run_dLambdaCnot (i j : Fin 730) (x : Reg 730) :
    Run (1 : Matrix (Reg 730) (Reg 730) ℂ) (dLambdaCircuit [DLambdaOp.cnot i j]) (Ket x)
      = Ket (Function.update x j (Bool.xor (x j) (x i))) := by
  have hstep : ApplyGate (dLambdaGateMatrix (DLambdaOp.cnot i j)) (Ket x)
      = Ket (Function.update x j (Bool.xor (x j) (x i))) := by
    funext y
    have hsum : (dLambdaGateMatrix (DLambdaOp.cnot i j) *ᵥ Ket x) y
        = ∑ x' : Reg 730, dLambdaGateMatrix (DLambdaOp.cnot i j) y x' * Ket x x' := by
      simp [Matrix.mulVec, dotProduct]
    have hket : Ket (Function.update x j (Bool.xor (x j) (x i))) y
        = (if y = Function.update x j (Bool.xor (x j) (x i)) then (1 : ℂ) else 0) := rfl
    show (dLambdaGateMatrix (DLambdaOp.cnot i j) *ᵥ Ket x) y
        = Ket (Function.update x j (Bool.xor (x j) (x i))) y
    rw [hsum, hket]
    rw [Finset.sum_eq_single x (fun x' _ hx' => by
        have hk : Ket x x' = 0 := by
          show (if x' = x then (1 : ℂ) else 0) = 0
          rw [if_neg hx']
        rw [hk, mul_zero])
      (fun h => absurd (Finset.mem_univ x) h)]
    show (if y = Function.update x j (Bool.xor (x j) (x i)) then (1 : ℂ) else 0)
        * (if x = x then (1 : ℂ) else 0)
        = (if y = Function.update x j (Bool.xor (x j) (x i)) then (1 : ℂ) else 0)
    rw [if_pos rfl, mul_one]
  exact hstep

/-- The stated `DLambdaCorrespondence` specification is false because its time bound cannot
support the distant controlled-NOT acceptance behavior. -/
theorem clause2_dLambdaCorrespondence_lightCone_false : ¬ DLambdaCorrespondence := by
  intro hcorr
  obtain ⟨_h1, h2, _h3⟩ := hcorr
  have hne0 : (⟨0, by omega⟩ : Fin 730) ≠ ⟨729, by omega⟩ := by
    intro h
    have hval : (0 : ℕ) = 729 := congrArg Fin.val h
    omega
  have hvalid : ∀ op ∈ ([DLambdaOp.cnot ⟨729, by omega⟩ ⟨0, by omega⟩] :
      List (DLambdaOp 730)), ValidDLambdaOp op := by
    intro op hop
    simp only [List.mem_singleton] at hop
    subst hop
    exact hne0.symm
  obtain ⟨Q, _hf, _hd, qacc, M, w, t, _hw0, _ht0, hnw, _hwbd, htbound, _hfive, hsim⟩ :=
    h2 730 [DLambdaOp.cnot ⟨729, by omega⟩ ⟨0, by omega⟩] hvalid (by norm_num)
  have hlen : ([DLambdaOp.cnot ⟨729, by omega⟩ ⟨0, by omega⟩] : List (DLambdaOp 730)).length
      = 1 := rfl
  have ht729 : t ≤ 729 := by
    have h := htbound
    rw [hlen] at h
    norm_num at h
    exact h
  have hj0lt : w + 730 < 2 * w + 1 := by omega
  obtain ⟨j₀, hj0val⟩ : ∃ j₀ : Fin (2 * w + 1), j₀.val = w + 730 :=
    ⟨⟨w + 730, hj0lt⟩, rfl⟩
  have hi : (initWindowCfg (t := w) M 730 zeroInput).head.val = w := rfl
  have hflip : flipCfg j₀ (initWindowCfg (t := w) M 730 zeroInput)
      = initWindowCfg (t := w) M 730 farInput := by
    simp only [flipCfg, initWindowCfg, WindowCfg.mk.injEq]
    exact ⟨trivial, trivial, funext fun j => (initTape_eq_flip M.blank j₀ hj0val j).symm⟩
  have hfar : t < j₀.val - w := by
    rw [hj0val]
    omega
  have hx0 := hsim zeroInput
  have hx1 := hsim farInput
  rw [run_dLambdaCnot ⟨729, by omega⟩ ⟨0, by omega⟩ zeroInput,
    acceptProb_ket (by norm_num : 0 < 730)] at hx0
  rw [run_dLambdaCnot ⟨729, by omega⟩ ⟨0, by omega⟩ farInput,
    acceptProb_ket (by norm_num : 0 < 730)] at hx1
  have h0 : Function.update zeroInput ⟨0, by omega⟩
      (Bool.xor (zeroInput ⟨0, by omega⟩) (zeroInput ⟨729, by omega⟩)) ⟨0, by omega⟩
      = false := rfl
  have h1 : Function.update farInput ⟨0, by omega⟩
      (Bool.xor (farInput ⟨0, by omega⟩) (farInput ⟨729, by omega⟩)) ⟨0, by omega⟩
      = true := by
    show (if (⟨0, by omega⟩ : Fin 730) = ⟨0, by omega⟩ then
        Bool.xor (farInput ⟨0, by omega⟩) (farInput ⟨729, by omega⟩) else
        farInput ⟨0, by omega⟩) = true
    rw [if_pos rfl, farInput_ne hne0, farInput_self]
    rfl
  rw [h0, if_neg (by simp)] at hx0
  rw [h1, if_pos rfl] at hx1
  have hlc := acceptMass_lightCone M qacc j₀
    (initWindowCfg (t := w) M 730 zeroInput) (initWindowCfg (t := w) M 730 farInput)
    hflip hi t hfar
  rw [hx0, hx1] at hlc
  exact absurd hlc (by norm_num)

end Qatlib.Concepts.UniformBqp.Phi3Compile
