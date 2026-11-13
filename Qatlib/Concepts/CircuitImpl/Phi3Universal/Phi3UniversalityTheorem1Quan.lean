/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.Phi3Universal.Phi3UniversalityTheorem1Stat
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis

/-!
# Exact universality of three-wire gates

This module proves a quantitative form of the three-wire universality theorem in [Yao1993] by
translating legal reflection-gate tables into three-wire gates on a register with three added
wires. One-wire gates and controlled-NOT gates are embedded using unused selected wires,
preserving the compiled circuit and its gate count in the synthesis framework of
[BarencoEtAl1995].

## Main statements

* `phi3UniversalityTheorem1`: every unitary on `n ≥ 1` qubits has an exact, query-free
  three-wire implementation on the embedded register, with at most `768*(n+1)^3*4^n` gates.

## References

* [Yao, Theorem 1][Yao1993]
* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CircuitImpl.Phi3Universal

open Matrix
noncomputable section

/-- Agreement off three distinct wires together with agreement on the last two selected wires is
equivalent to agreement off the first selected wire. -/
private theorem phi3Off_local {n : ℕ} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (x y : Reg n) :
    ((∀ k : Fin n, (∀ q : Fin 3, w q ≠ k) → x k = y k) ∧
      (∀ q : Fin 3, q ≠ 0 → x (w q) = y (w q))) ↔
      (∀ k : Fin n, k ≠ w 0 → x k = y k) := by
  constructor
  · rintro ⟨hoff, hlocal⟩ k hk
    by_cases hr : k ∈ Set.range w
    · obtain ⟨q, rfl⟩ := hr
      exact hlocal q (fun h => hk (congrArg w h))
    · exact hoff k (fun q hq => hr ⟨q, hq⟩)
  · intro h
    constructor
    · intro k hk
      exact h k (Ne.symm (hk 0))
    · intro q hq
      exact h (w q) (hw.ne hq)

/-- Embedding a one-wire unitary as a three-wire gate gives its direct action on the first
selected ambient wire. -/
private theorem phi3One_matrix {n : ℕ} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    phi3GateMatrix (⟨w, hw, wireGate 3 0 U, wireGate_unitary 3 0 U hU⟩ : Phi3Gate n) =
      wireGate n (w 0) U := by
  classical
  ext x y
  simp only [phi3GateMatrix, Matrix.of_apply, wireGate_apply]
  rw [← ite_and]
  simp only [phi3Off_local w hw]

/-- For distinct selected wires, agreement off them and a local update on the second wire are
equivalent to the corresponding ambient register update. -/
private theorem phi3Off_update {n : ℕ} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (x y : Reg n) (v : Bool) :
    ((∀ k : Fin n, (∀ q : Fin 3, w q ≠ k) → x k = y k) ∧
      (fun q => x (w q)) = Function.update (fun q => y (w q)) (1 : Fin 3) v) ↔
      x = Function.update y (w 1) v := by
  have hu : (fun q => Function.update y (w 1) v (w q)) =
      Function.update (fun q => y (w q)) (1 : Fin 3) v :=
    Function.update_comp_eq_of_injective' y hw 1 v
  constructor
  · rintro ⟨hoff, hlocal⟩
    funext k
    by_cases hr : k ∈ Set.range w
    · obtain ⟨q, rfl⟩ := hr
      exact (congrFun hlocal q).trans (congrFun hu q).symm
    · rw [Function.update_of_ne (fun h => hr ⟨1, h.symm⟩)]
      exact hoff k (fun q hq => hr ⟨q, hq⟩)
  · intro h
    constructor
    · intro k hk
      rw [h, Function.update_of_ne (Ne.symm (hk 1))]
    · rw [h]
      exact hu

/-- Embedding the local controlled-NOT as a three-wire gate gives controlled-NOT on the first
two selected ambient wires. -/
private theorem phi3Cnot_matrix {n : ℕ} (w : Fin 3 → Fin n) (hw : Function.Injective w) :
    phi3GateMatrix (⟨w, hw, cnotGate 3 0 1,
      cnotGate_unitary 3 0 1 (by decide)⟩ : Phi3Gate n) = cnotGate n (w 0) (w 1) := by
  classical
  ext x y
  simp only [phi3GateMatrix, cnotGate, permMatrix, Matrix.of_apply]
  rw [← ite_and]
  simp only [phi3Off_update w hw]

/-- The map selecting three ambient wires in the order `a`, `b`, `c`. -/
private def threeWires {n : ℕ} (a b c : Fin n) : Fin 3 → Fin n := ![a, b, c]

/-- Three pairwise distinct ambient wires define an injective `threeWires` selection. -/
private theorem threeWires_injective {n : ℕ} (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Function.Injective (threeWires a b c) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [threeWires]

/-- The additional wire at index `n` in an `(n+3)`-wire register. -/
private def dummyZero (n : ℕ) : Fin (n + 3) := ⟨n, by omega⟩
/-- The additional wire at index `n+1` in an `(n+3)`-wire register. -/
private def dummyOne (n : ℕ) : Fin (n + 3) := ⟨n + 1, by omega⟩

/-- A prefix data wire differs from the additional wire `dummyZero`. -/
private theorem data_ne_dummyZero {n : ℕ} (w : Fin n) :
    knownPrefixWires n 3 w ≠ dummyZero n := by
  intro h
  have hv := congrArg Fin.val h
  change w.val = n at hv
  omega

/-- A prefix data wire differs from the additional wire `dummyOne`. -/
private theorem data_ne_dummyOne {n : ℕ} (w : Fin n) :
    knownPrefixWires n 3 w ≠ dummyOne n := by
  intro h
  have hv := congrArg Fin.val h
  change w.val = n + 1 at hv
  omega

/-- Translates a legal reflection gate into a three-wire unitary gate after adding three ambient
wires. -/
private def phi3Translate {n : ℕ} (g : ReflectionGate n) (hg : reflectionGateLegal g) : Phi3Gate (n + 3) :=
  match g with
  | .inl (w, U) =>
    { wires := threeWires (knownPrefixWires n 3 w) (dummyZero n) (dummyOne n)
      wires_inj := threeWires_injective _ _ _ (data_ne_dummyZero w) (data_ne_dummyOne w)
        (by intro h; have hv := congrArg Fin.val h; change n = n + 1 at hv; omega)
      localMatrix := wireGate 3 0 U
      localMatrix_unitary := wireGate_unitary 3 0 U hg }
  | .inr (c, t) =>
    { wires := threeWires (knownPrefixWires n 3 c) (knownPrefixWires n 3 t) (dummyZero n)
      wires_inj := threeWires_injective _ _ _ ((knownPrefixWires n 3).injective.ne hg)
        (data_ne_dummyZero c) (data_ne_dummyZero t)
      localMatrix := cnotGate 3 0 1
      localMatrix_unitary := cnotGate_unitary 3 0 1 (by decide) }

/-- The translated three-wire matrix equals the original reflection-gate matrix mapped onto the
prefix data wires. -/
private theorem phi3Translate_matrix {n : ℕ} (g : ReflectionGate n) (hg : reflectionGateLegal g) :
    phi3GateMatrix (phi3Translate g hg) = reflectionGateMatrix (knownWireGateMap (knownPrefixWires n 3) g) := by
  rcases g with ⟨w, U⟩ | ⟨c, t⟩
  · have h := phi3One_matrix (phi3Translate (.inl (w, U)) hg).wires
      (phi3Translate (.inl (w, U)) hg).wires_inj U hg
    simpa only [phi3Translate, threeWires, Matrix.cons_val_zero, knownWireGateMap,
      reflectionGateMatrix] using! h
  · have h := phi3Cnot_matrix (phi3Translate (.inr (c, t)) hg).wires
      (phi3Translate (.inr (c, t)) hg).wires_inj
    simpa only [phi3Translate, threeWires, Matrix.cons_val_zero, Matrix.cons_val_one,
      knownWireGateMap, reflectionGateMatrix] using! h

/-- A legal reflection-gate list translates to a three-wire gate list of the same length with
exactly the mapped compiled circuit. -/
private theorem phi3Translate_list {n : ℕ} (gs : List (ReflectionGate n)) (hgs : reflectionLegal gs) :
    ∃ ts : List (Phi3Gate (n + 3)), ts.length = gs.length ∧
      phi3Compile ts = reflectionCompile (gs.map (knownWireGateMap (knownPrefixWires n 3))) := by
  induction gs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons g gs ih =>
    have hg := hgs g List.mem_cons_self
    obtain ⟨ts, hlen, hcompile⟩ := ih (fun t ht => hgs t (List.mem_cons_of_mem _ ht))
    refine ⟨phi3Translate g hg :: ts, by simpa using! hlen, ?_⟩
    simp only [phi3Compile, List.map_cons, reflectionCompile]
    rw [phi3Translate_matrix]
    exact congrArg (List.cons _) hcompile

/-- Every unitary on `n ≥ 1` qubits has an exact query-free three-wire implementation on the
embedding with three added wires and at most `768*(n+1)^3*4^n` gates. This is a quantitative
form of [Yao, Theorem 1][Yao1993]. -/
theorem phi3UniversalityTheorem1 : Phi3UniversalityTheorem1 := by
  intro n hn U hU
  obtain ⟨gs, hgs, hlen, _, _, hrun⟩ := known_unitary_no_work_actual_local_synthesis n hn U hU
  obtain ⟨ts, htlen, htcompile⟩ := phi3Translate_list gs hgs
  obtain ⟨hq, hg⟩ := phi3Compile_count ts
  refine ⟨ts, isUnitaryCircuit_phi3Compile ts, hq, hg, htlen.le.trans hlen, ?_⟩
  intro psi
  rw [htcompile, knownWireProgram_embed (knownPrefixWires n 3) gs hgs, hrun]

end

end Qatlib.Concepts.CircuitImpl.Phi3Universal
