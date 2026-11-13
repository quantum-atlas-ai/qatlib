/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermal.FiniteThermalSelect
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermal.FiniteThermalComparator

/-!
# Native interval predicates and conditional operations

This module lifts multiply controlled X, masked controls, comparisons, and interval tests to
`ThermalNativeStep` programs and proves that their lowering recovers the corresponding finite
words. Legality and inverse semantics then transfer to the native interval program.

The programs `thermalNativeIntervalSelectY` and `thermalNativeIntervalPhase` compute an interval
predicate into a false flag, apply a signed signal flip or a fourth-root phase, and uncompute
the predicate. Basis and coherent semantics specify the exact signs and restoration of the flag
and workspace, using standard reversible circuit methods [NielsenChuang2010].

## Main statements

* `thermalNativeInterval_lower`: native interval lowering equals `thermalIntervalWord`.
* `thermalNativeIntervalSelectY_basis`: gives the interval-conditioned signal flip and sign.
* `thermalNativeIntervalPhase_coherent`: multiplies amplitudes in the interval by the selected
  phase.
* `thermalNativeIntervalPhase_cost`: counts both interval computations and the flag phase.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
open Qatlib Matrix
open scoped BigOperators

/-- Lowering a concatenation of native programs equals concatenating their lowered finite words. -/
private theorem native_append {n : ℕ} (gs hs : List (ThermalNativeStep n)) :
    thermalNativeProgram (gs++hs)=thermalNativeProgram gs++thermalNativeProgram hs := by
  simp [thermalNativeProgram,List.flatMap_append]

/-- The native recursive multiply controlled X program, retaining Toffoli instructions until
lowering and emitting an illegal self-CNOT when workspace is insufficient. -/
def thermalNativeMultiX {n : ℕ} (cs : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) : List (ThermalNativeStep n) :=
  match cs,ws with
  | [],_ => [.fixed (.x t.val)]
  | [a],_ => [.fixed (.cx a.val t.val)]
  | [a,b],_ => [.ccx a b t]
  | a::b::c::rest,w::work =>
      [.ccx a b w] ++ thermalNativeMultiX (w::c::rest) t work ++ [.ccx a b w]
  | _,[] => [.fixed (.cx t.val t.val)]
termination_by cs.length

/-- Lowering the native multiply controlled X program gives exactly `thermalMultiX`. -/
theorem thermalNativeMultiX_lower {n : ℕ} (cs : List (Fin n)) (t : Fin n) (ws : List (Fin n)) :
    thermalNativeProgram (thermalNativeMultiX cs t ws)=thermalMultiX cs t ws := by
  fun_induction thermalNativeMultiX cs t ws
  all_goals simp_all [thermalMultiX,thermalNativeProgram,thermalNativeLower]

/-- The native program containing a fixed X instruction for each wire in the list. -/
def thermalNativeXMask {n : ℕ} (ms : List (Fin n)) : List (ThermalNativeStep n) :=
  ms.map (fun w => .fixed (.x w.val))

/-- Lowering the native X mask gives exactly `thermalXMask`. -/
private theorem mask_lower {n : ℕ} (ms : List (Fin n)) :
    thermalNativeProgram (thermalNativeXMask ms)=thermalXMask ms := by
  induction ms with
  | nil => rfl
  | cons w ms ih =>
    simpa [thermalNativeXMask,thermalNativeProgram,thermalXMask,thermalNativeLower] using!
      congrArg (List.cons (.x w.val)) ih

/-- The native program consisting of an X mask, a multiply controlled X program, and the
reversed X mask. -/
def thermalNativeMaskedX {n : ℕ} (cs zeros : List (Fin n)) (t : Fin n) (ws : List (Fin n)) :=
  thermalNativeXMask zeros ++ thermalNativeMultiX cs t ws ++ thermalNativeXMask zeros.reverse

/-- Lowering the native masked controlled X program gives exactly `thermalMaskedX`. -/
theorem thermalNativeMaskedX_lower {n : ℕ} (cs zeros : List (Fin n)) (t : Fin n) (ws : List (Fin n)) :
    thermalNativeProgram (thermalNativeMaskedX cs zeros t ws)=thermalMaskedX cs zeros t ws := by
  simp only [thermalNativeMaskedX,native_append,mask_lower,thermalNativeMultiX_lower,
    thermalMaskedX,thermalXMask_adjoint]

/-- The recursive native comparison program that accumulates masked prefix tests into target
`t`. -/
def thermalNativeLess {n : ℕ} (pre zs : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) : List (Fin n × Bool) → List (ThermalNativeStep n)
  | [] => []
  | (w,b)::rest =>
      (if b then thermalNativeMaskedX (pre++[w]) (zs++[w]) t ws else []) ++
      thermalNativeLess (pre++[w]) (if b then zs else zs++[w]) t ws rest

/-- Lowering the native recursive comparison gives exactly `thermalLessWord`. -/
theorem thermalNativeLess_lower {n : ℕ} (pre zs : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) (ps : List (Fin n × Bool)) :
    thermalNativeProgram (thermalNativeLess pre zs t ws ps)=thermalLessWord pre zs t ws ps := by
  induction ps generalizing pre zs with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨w,b⟩
    cases b with
    | false => exact ih (pre++[w]) (zs++[w])
    | true =>
      change thermalNativeProgram (thermalNativeMaskedX (pre++[w]) (zs++[w]) t ws ++
        thermalNativeLess (pre++[w]) zs t ws ps)=_
      rw [native_append,thermalNativeMaskedX_lower,ih]
      rfl

/-- The native comparator, using a fixed X instruction when `full` is true and otherwise the
empty-prefix native comparison program. -/
def thermalNativeComparator {n : ℕ} (full : Bool) (ps : List (Fin n × Bool))
    (t : Fin n) (ws : List (Fin n)) : List (ThermalNativeStep n) :=
  if full then [.fixed (.x t.val)] else thermalNativeLess [] [] t ws ps

/-- Lowering the native comparator gives exactly `thermalComparatorWord`. -/
theorem thermalNativeComparator_lower {n : ℕ} (full : Bool) (ps : List (Fin n × Bool))
    (t : Fin n) (ws : List (Fin n)) :
    thermalNativeProgram (thermalNativeComparator full ps t ws)=thermalComparatorWord full ps t ws := by
  cases full with
  | false => exact thermalNativeLess_lower [] [] t ws ps
  | true => rfl

/-- The native program concatenating upper-threshold and lower-threshold comparators on the same
target. -/
def thermalNativeInterval {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (t : Fin n) (ws : List (Fin n)) :=
  thermalNativeComparator hiFull hi t ws ++ thermalNativeComparator loFull lo t ws

/-- Lowering the native interval program gives exactly `thermalIntervalWord`. -/
theorem thermalNativeInterval_lower {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (t : Fin n) (ws : List (Fin n)) :
    thermalNativeProgram (thermalNativeInterval loFull lo hiFull hi t ws)=
      thermalIntervalWord loFull lo hiFull hi t ws := by
  simp [thermalNativeInterval,native_append,thermalNativeComparator_lower,thermalIntervalWord]

/-- A native instruction is legal if its lowered finite word is legal. -/
theorem thermalNative_step_legal_of_lower {n : ℕ} (g : ThermalNativeStep n)
    (h : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalNativeLower g)=true) : thermalNativeLegal g := by
  cases g with
  | fixed g => simpa [thermalNativeLower,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal] using! h
  | z _ | s _ | sdg _ => trivial
  | ccx a b t =>
    change a≠b ∧ a≠t ∧ b≠t
    constructor
    · intro he; subst b
      simp [thermalNativeLower,thermalToffoliWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal] at h
    constructor
    · intro he; subst t
      simp [thermalNativeLower,thermalToffoliWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal] at h
    · intro he; subst t
      simp [thermalNativeLower,thermalToffoliWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal] at h

/-- If a lowered native program is a legal finite word, every instruction of the native program
is legal. -/
theorem thermalNative_program_legal_of_lower {n : ℕ} (gs : List (ThermalNativeStep n))
    (h : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalNativeProgram gs)=true) :
    ∀ g∈gs,thermalNativeLegal g := by
  intro g hg
  apply thermalNative_step_legal_of_lower g
  simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,List.all_eq_true] at h ⊢
  intro code hcode
  exact h code (List.mem_flatMap.mpr ⟨g,hg,hcode⟩)

/-- Every instruction in the native interval program is legal when the threshold lists use the
same data wires, the listed data, flag, and workspace wires are distinct, and workspace is
sufficient. -/
theorem thermalNativeInterval_legal {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (t : Fin n) (ws : List (Fin n))
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hn : (hi.map Prod.fst++t::ws).Nodup)
    (hlen : hi.length ≤ ws.length+2) :
    ∀ g∈thermalNativeInterval loFull lo hiFull hi t ws,thermalNativeLegal g := by
  apply thermalNative_program_legal_of_lower
  rw [thermalNativeInterval_lower]
  exact thermalIntervalWord_legal loFull lo hiFull hi t ws hwires hn hlen

/-- For matching data wires, distinct listed wires, and sufficient workspace, lowering the
native inverse of the interval program gives the matrix of the adjoint finite interval word. -/
theorem thermalNativeInterval_inverse_matrix {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (t : Fin n) (ws : List (Fin n))
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hn : (hi.map Prod.fst++t::ws).Nodup)
    (hlen : hi.length ≤ ws.length+2) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram
      (thermalNativeInverse (thermalNativeInterval loFull lo hiFull hi t ws)))=
      Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalIntervalWord loFull lo hiFull hi t ws)) := by
  rw [thermalNative_program_inverse_matrix _
    (thermalNativeInterval_legal loFull lo hiFull hi t ws hwires hn hlen),thermalNativeInterval_lower]

/-- For matching distinct data wires, sufficient clean workspace, and ordered cutoffs, the
lowered native interval inverse toggles only `t` by the half-open interval membership test. -/
theorem thermalNativeInterval_inverse_basis {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (t : Fin n) (ws : List (Fin n))
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hn : (hi.map Prod.fst++t::ws).Nodup)
    (hlen : hi.length ≤ ws.length+2) (horder : thermalCutoff loFull lo ≤ thermalCutoff hiFull hi)
    (x : Qatlib.Foundations.PureStateMath.Reg n) (hc : ∀ w∈ws,x w=false) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram
      (thermalNativeInverse (thermalNativeInterval loFull lo hiFull hi t ws))))
      (Qatlib.Foundations.PureStateMath.Ket x)=Qatlib.Foundations.PureStateMath.Ket (Function.update x t
        (x t ^^ decide (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun p => x p.1)) ∧
          thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi))) := by
  rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run,
    thermalNativeInterval_inverse_matrix loFull lo hiFull hi t ws hwires hn hlen,
    ← Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run]
  exact thermalIntervalWord_adjoint loFull lo hiFull hi t ws hwires hn hlen horder x hc

/-- The native program that computes the interval predicate into `flag`, applies
`thermalSelectYSteps` to flag and signal, and runs the native interval inverse. -/
def thermalNativeIntervalSelectY {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (flag signal : Fin n) (ws : List (Fin n)) :=
  thermalNativeInterval loFull lo hiFull hi flag ws ++ thermalSelectYSteps flag signal ++
    thermalNativeInverse (thermalNativeInterval loFull lo hiFull hi flag ws)

/-- Updating a wire outside the listed data wires leaves the extracted data bits unchanged. -/
private theorem data_update {n : ℕ} (ps : List (Fin n × Bool)) (w : Fin n)
    (hne : w∉ps.map Prod.fst) (x : Qatlib.Foundations.PureStateMath.Reg n) (b : Bool) :
    ps.map (fun p => Function.update x w b p.1)=ps.map (fun p => x p.1) := by
  apply List.map_congr_left
  intro p hp
  have hw : p.1≠w := by
    intro h
    exact hne (List.mem_map.mpr ⟨p,hp,h⟩)
  exact Function.update_of_ne hw _ _

/-- Running a finite code circuit commutes with complex scalar multiplication of its input. -/
private theorem native_run_smul {n : ℕ} (gs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode) (a : ℂ) (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n)) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n gs) (a • psi)=
      a • Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n gs) psi := by
  simp only [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run,Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionApplyGate_smul]

/-- For matching data wires, distinct data, flag, workspace, and signal wires, sufficient false
workspace, ordered cutoffs, and an initially false flag, the program flips the signal
exactly on the interval. It contributes sign minus one exactly when the interval predicate
and the original signal bit are both true, restoring all other bits. -/
theorem thermalNativeIntervalSelectY_basis {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (flag signal : Fin n) (ws : List (Fin n))
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hn : (hi.map Prod.fst++flag::ws).Nodup)
    (hlen : hi.length ≤ ws.length+2) (horder : thermalCutoff loFull lo ≤ thermalCutoff hiFull hi)
    (hs : signal∉hi.map Prod.fst++flag::ws)
    (x : Qatlib.Foundations.PureStateMath.Reg n) (hc : ∀ w∈ws,x w=false) (hflag : x flag=false) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram
      (thermalNativeIntervalSelectY loFull lo hiFull hi flag signal ws)))
      (Qatlib.Foundations.PureStateMath.Ket x)=
      (if decide (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun p => x p.1)) ∧
          thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi) && x signal
        then (-1:ℂ) else 1) • Qatlib.Foundations.PureStateMath.Ket (Function.update x signal
        (x signal ^^ decide (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun p => x p.1)) ∧
          thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi))) := by
  have hsf : signal≠flag := by intro he; apply hs; simp [he]
  have hfs : flag≠signal := hsf.symm
  have hfdata : flag∉hi.map Prod.fst := by
    intro hf
    exact (List.disjoint_left.mp hn.disjoint) hf (by simp)
  have hfws : flag∉ws := (List.nodup_cons.mp hn.of_append_right).1
  have hsdata : signal∉hi.map Prod.fst := fun h => hs (List.mem_append_left _ h)
  have hsws : signal∉ws := by intro h; apply hs; simp [h]
  let hit := decide (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun p => x p.1)) ∧
    thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi)
  let y := Function.update x flag hit
  let z := Function.update y signal (x signal ^^ hit)
  have hzc : ∀ w∈ws,z w=false := by
    intro w hw
    have hwf : w≠flag := fun h => hfws (h ▸ hw)
    have hws : w≠signal := fun h => hsws (h ▸ hw)
    simpa only [z,y,Function.update_of_ne hws,Function.update_of_ne hwf] using! hc w hw
  have hdata : hi.map (fun p => z p.1)=hi.map (fun p => x p.1) := by
    dsimp only [z,y]
    rw [data_update hi signal hsdata,data_update hi flag hfdata]
  have hu : Function.update z flag (z flag ^^ hit)=Function.update x signal (x signal ^^ hit) := by
    funext w
    by_cases hwf : w=flag
    · subst w
      simp [z,y,hfs,hflag]
    · by_cases hws : w=signal
      · subst w
        simp [z,y,hsf]
      · simp [z,y,Function.update_of_ne hwf,Function.update_of_ne hws]
  have ha := thermalIntervalWord_numeric loFull lo hiFull hi flag ws hwires hn hlen horder x hc
  simp only [hflag,Bool.false_xor] at ha
  change Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ)
    (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalIntervalWord loFull lo hiFull hi flag ws))
    (Qatlib.Foundations.PureStateMath.Ket x)=Qatlib.Foundations.PureStateMath.Ket y at ha
  have hb := thermalSelectY_basis flag signal hfs y
  have hc' := thermalNativeInterval_inverse_basis loFull lo hiFull hi flag ws
    hwires hn hlen horder z hzc
  rw [hdata] at hc'
  change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram
    (thermalNativeInverse (thermalNativeInterval loFull lo hiFull hi flag ws))))
    (Qatlib.Foundations.PureStateMath.Ket z)=Qatlib.Foundations.PureStateMath.Ket (Function.update z flag (z flag ^^ hit)) at hc'
  rw [hu] at hc'
  simp only [y,Function.update_self,Function.update_of_ne hsf] at hb
  change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalSelectYWord flag signal)) (Qatlib.Foundations.PureStateMath.Ket y)=
    (if hit && x signal then (-1:ℂ) else 1) • Qatlib.Foundations.PureStateMath.Ket z at hb
  simp only [thermalNativeIntervalSelectY,native_append,thermalNativeInterval_lower,
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_append,Qatlib.Foundations.QueryWordCore.Circuit.run_append]
  change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram
    (thermalNativeInverse (thermalNativeInterval loFull lo hiFull hi flag ws))))
    (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalSelectYWord flag signal))
      (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalIntervalWord loFull lo hiFull hi flag ws))
        (Qatlib.Foundations.PureStateMath.Ket x)))=_
  rw [ha,hb,native_run_smul,hc']

/-- For matching data wires, distinct listed data, flag, and workspace wires, sufficient
workspace, and distinct flag and signal, every instruction of `thermalNativeIntervalSelectY`
is legal. -/
theorem thermalNativeIntervalSelectY_legal {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (flag signal : Fin n) (ws : List (Fin n))
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hn : (hi.map Prod.fst++flag::ws).Nodup)
    (hlen : hi.length ≤ ws.length+2) (hfs : flag≠signal) :
    ∀ g∈thermalNativeIntervalSelectY loFull lo hiFull hi flag signal ws,thermalNativeLegal g := by
  have hl := thermalNativeInterval_legal loFull lo hiFull hi flag ws hwires hn hlen
  intro g hg
  simp only [thermalNativeIntervalSelectY,List.mem_append] at hg
  rcases hg with (hg|hg)|hg
  · exact hl g hg
  · exact thermalSelectY_legal flag signal hfs g hg
  · exact thermalNative_inverse_legal _ hl g hg

/-- The lowered interval-select program has zero queries and gate count twice that of
`thermalIntervalWord` plus seven. -/
theorem thermalNativeIntervalSelectY_cost {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (flag signal : Fin n) (ws : List (Fin n)) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram
      (thermalNativeIntervalSelectY loFull lo hiFull hi flag signal ws)))=
      2*Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalIntervalWord loFull lo hiFull hi flag ws))+7 ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram
      (thermalNativeIntervalSelectY loFull lo hiFull hi flag signal ws)))=0 := by
  constructor
  · simp only [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).2,thermalNativeIntervalSelectY,native_append,
      List.length_append,thermalNative_program_inverse_length,thermalNativeInterval_lower]
    have hs : (thermalNativeProgram (thermalSelectYSteps flag signal)).length=7 := rfl
    rw [hs]
    omega
  · exact (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).1

/-- For matching data wires, distinct data, flag, workspace, and signal wires, sufficient
workspace, and ordered cutoffs, the program applies the interval-conditioned signal flip to
states supported on false flag and workspace. Each basis component gains sign minus one
exactly when its interval predicate and original signal bit are both true. -/
theorem thermalNativeIntervalSelectY_coherent {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (flag signal : Fin n) (ws : List (Fin n))
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hn : (hi.map Prod.fst++flag::ws).Nodup)
    (hlen : hi.length ≤ ws.length+2) (horder : thermalCutoff loFull lo ≤ thermalCutoff hiFull hi)
    (hs : signal∉hi.map Prod.fst++flag::ws) (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n))
    (hc : ∀ x : Qatlib.Foundations.PureStateMath.Reg n, (¬(x flag=false ∧ ∀ w∈ws,x w=false)) → psi x=0) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram
      (thermalNativeIntervalSelectY loFull lo hiFull hi flag signal ws))) psi =
      ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • ((if decide (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun p => x p.1)) ∧
          thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi) && x signal
        then (-1:ℂ) else 1) • Qatlib.Foundations.PureStateMath.Ket (Function.update x signal
        (x signal ^^ decide (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun p => x p.1)) ∧
          thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi)))) := by
  have he : psi = ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket x := by
    funext z
    simp [Qatlib.Foundations.PureStateMath.Ket,Finset.sum_apply]
  rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run]
  conv_lhs => rw [he]
  simp only [Qatlib.Foundations.PureStateMath.ApplyGate,Matrix.mulVec_sum,Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hcx : x flag=false ∧ ∀ w∈ws,x w=false
  · have hb := thermalNativeIntervalSelectY_basis loFull lo hiFull hi flag signal ws
      hwires hn hlen horder hs x hcx.2 hcx.1
    rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run] at hb
    exact congrArg (fun v => psi x • v) hb
  · simp only [hc x hcx,zero_smul]

/-- The native program that computes the interval predicate into `flag`, applies the selected
flag phase, and runs the native interval inverse. -/
def thermalNativeIntervalPhase {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (flag : Fin n) (ws : List (Fin n)) (phase : Fin 4) :=
  thermalNativeInterval loFull lo hiFull hi flag ws ++ thermalFlagPhaseSteps phase flag ++
    thermalNativeInverse (thermalNativeInterval loFull lo hiFull hi flag ws)

/-- For matching data wires, distinct listed wires, sufficient false workspace, ordered cutoffs,
and an initially false flag, the interval-phase program multiplies `Ket x` by
`thermalFlagPhaseValue phase` inside the half-open interval and by one outside it. -/
theorem thermalNativeIntervalPhase_basis {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (flag : Fin n) (ws : List (Fin n)) (phase : Fin 4)
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hn : (hi.map Prod.fst++flag::ws).Nodup)
    (hlen : hi.length ≤ ws.length+2) (horder : thermalCutoff loFull lo ≤ thermalCutoff hiFull hi)
    (x : Qatlib.Foundations.PureStateMath.Reg n) (hc : ∀ w∈ws,x w=false) (hflag : x flag=false) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram
      (thermalNativeIntervalPhase loFull lo hiFull hi flag ws phase))) (Qatlib.Foundations.PureStateMath.Ket x)=
      (if decide (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun p => x p.1)) ∧
          thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi)
        then thermalFlagPhaseValue phase else 1) • Qatlib.Foundations.PureStateMath.Ket x := by
  let hit := decide (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun p => x p.1)) ∧
    thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi)
  let y := Function.update x flag hit
  have hfdata : flag∉hi.map Prod.fst := by
    intro hf
    exact (List.disjoint_left.mp hn.disjoint) hf (by simp)
  have hfws : flag∉ws := (List.nodup_cons.mp hn.of_append_right).1
  have hyc : ∀ w∈ws,y w=false := by
    intro w hw
    have hwf : w≠flag := fun h => hfws (h ▸ hw)
    simpa only [y,Function.update_of_ne hwf] using! hc w hw
  have ha := thermalIntervalWord_numeric loFull lo hiFull hi flag ws hwires hn hlen horder x hc
  simp only [hflag,Bool.false_xor] at ha
  change Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ)
    (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalIntervalWord loFull lo hiFull hi flag ws))
    (Qatlib.Foundations.PureStateMath.Ket x)=Qatlib.Foundations.PureStateMath.Ket y at ha
  have hb := thermalFlagPhase_basis phase flag y
  have hc' :=
      thermalNativeInterval_inverse_basis loFull lo hiFull hi flag ws hwires hn hlen horder y hyc
  rw [show hi.map (fun p => y p.1)=hi.map (fun p => x p.1) from data_update hi flag hfdata x hit] at hc'
  have hu : Function.update y flag (y flag ^^ hit)=x := by
    simp only [y,Function.update_self,Bool.xor_self,Function.update_idem]
    exact Function.update_eq_self_iff.mpr hflag.symm
  change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram
    (thermalNativeInverse (thermalNativeInterval loFull lo hiFull hi flag ws))))
    (Qatlib.Foundations.PureStateMath.Ket y)=Qatlib.Foundations.PureStateMath.Ket (Function.update y flag (y flag ^^ hit)) at hc'
  rw [hu] at hc'
  simp only [thermalNativeIntervalPhase,native_append,thermalNativeInterval_lower,
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_append,Qatlib.Foundations.QueryWordCore.Circuit.run_append]
  change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram
    (thermalNativeInverse (thermalNativeInterval loFull lo hiFull hi flag ws))))
    (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalFlagPhaseWord phase flag))
      (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalIntervalWord loFull lo hiFull hi flag ws))
        (Qatlib.Foundations.PureStateMath.Ket x)))=_
  rw [ha,hb,native_run_smul,hc']
  simp only [y,Function.update_self]
  rfl

/-- For matching data wires, distinct data, flag, and workspace wires, and sufficient workspace,
every instruction of the native interval-phase program is legal. -/
theorem thermalNativeIntervalPhase_legal {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (flag : Fin n) (ws : List (Fin n)) (phase : Fin 4)
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hn : (hi.map Prod.fst++flag::ws).Nodup)
    (hlen : hi.length ≤ ws.length+2) :
    ∀ g∈thermalNativeIntervalPhase loFull lo hiFull hi flag ws phase,thermalNativeLegal g := by
  have hl := thermalNativeInterval_legal loFull lo hiFull hi flag ws hwires hn hlen
  intro g hg
  simp only [thermalNativeIntervalPhase,List.mem_append] at hg
  rcases hg with (hg|hg)|hg
  · exact hl g hg
  · exact thermalFlagPhase_legal phase flag g hg
  · exact thermalNative_inverse_legal _ hl g hg

/-- For matching data wires, distinct listed wires, sufficient workspace, and ordered cutoffs,
the interval-phase program multiplies each amplitude inside the half-open interval by
`thermalFlagPhaseValue phase`, leaving other amplitudes unchanged, on states supported on
false flag and workspace. -/
theorem thermalNativeIntervalPhase_coherent {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (flag : Fin n) (ws : List (Fin n)) (phase : Fin 4)
    (hwires : lo.map Prod.fst=hi.map Prod.fst) (hn : (hi.map Prod.fst++flag::ws).Nodup)
    (hlen : hi.length ≤ ws.length+2) (horder : thermalCutoff loFull lo ≤ thermalCutoff hiFull hi)
    (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n)) (hc : ∀ x : Qatlib.Foundations.PureStateMath.Reg n, (¬(x flag=false ∧ ∀ w∈ws,x w=false)) → psi x=0) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram
      (thermalNativeIntervalPhase loFull lo hiFull hi flag ws phase))) psi =
      fun x => (if decide (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun p => x p.1)) ∧
          thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi)
        then thermalFlagPhaseValue phase else 1)*psi x := by
  have he : psi = ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket x := by
    funext z
    simp [Qatlib.Foundations.PureStateMath.Ket,Finset.sum_apply]
  rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run]
  conv_lhs => rw [he]
  simp only [Qatlib.Foundations.PureStateMath.ApplyGate,Matrix.mulVec_sum,Matrix.mulVec_smul]
  have ht : (∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x •
      ((Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram
        (thermalNativeIntervalPhase loFull lo hiFull hi flag ws phase))) *ᵥ Qatlib.Foundations.PureStateMath.Ket x)) =
      ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • ((if decide
        (thermalCutoff loFull lo ≤ thermalBitValue (hi.map (fun p => x p.1)) ∧
          thermalBitValue (hi.map (fun p => x p.1)) < thermalCutoff hiFull hi)
        then thermalFlagPhaseValue phase else 1) • Qatlib.Foundations.PureStateMath.Ket x) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hcx : x flag=false ∧ ∀ w∈ws,x w=false
    · have hb := thermalNativeIntervalPhase_basis loFull lo hiFull hi flag ws phase
        hwires hn hlen horder x hcx.2 hcx.1
      rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run] at hb
      exact congrArg (fun v => psi x • v) hb
    · simp only [hc x hcx,zero_smul]
  rw [ht]
  funext x
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Qatlib.Foundations.PureStateMath.Ket]
  simp [mul_comm]

/-- The lowered interval-phase program has zero queries and gate count twice that of the
interval word plus zero, four, or two for phase indices zero, two, or either remaining
index, respectively. -/
theorem thermalNativeIntervalPhase_cost {n : ℕ} (loFull : Bool) (lo : List (Fin n × Bool))
    (hiFull : Bool) (hi : List (Fin n × Bool)) (flag : Fin n) (ws : List (Fin n)) (phase : Fin 4) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram
      (thermalNativeIntervalPhase loFull lo hiFull hi flag ws phase)))=
      2*Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalIntervalWord loFull lo hiFull hi flag ws))+
        (if phase.val=0 then 0 else if phase.val=2 then 4 else 2) ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram
      (thermalNativeIntervalPhase loFull lo hiFull hi flag ws phase)))=0 := by
  constructor
  · simp only [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).2,thermalNativeIntervalPhase,native_append,
      List.length_append,thermalNative_program_inverse_length,thermalNativeInterval_lower]
    have hs := (thermalFlagPhase_cost phase flag).1
    rw [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).2] at hs
    change (thermalNativeProgram (thermalFlagPhaseSteps phase flag)).length=_ at hs
    rw [hs]
    omega
  · exact (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).1

end Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
