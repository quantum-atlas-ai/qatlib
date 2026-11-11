/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Rotate
import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabulary
import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SimpRw

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Measurement Gate Semantics

Measurement Gate Semantics constructions and identities for Spinor Sampling.
-/


set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit

/-- Constructors for Bit Gate in the measurement gate semantics model. -/
inductive BitGate (W : Type*) where
  | cx (control target : W)
  | ccx (a b target : W)

/-- Constructors for Native Gate in the measurement gate semantics model. -/
inductive NativeGate (W : Type*) where
  | h (target : W)
  | t (target : W)
  | tdg (target : W)
  | cx (control target : W)

/-- Actual chronological fifteen-opcode table, with no Toffoli primitive left. -/
def toffoliWord {W : Type*} (a b t : W) : List (NativeGate W) :=
  [.h t, .cx b t, .tdg t, .cx a t, .t t, .cx b t, .tdg t, .cx a t,
    .t b, .t t, .h t, .cx a b, .t a, .tdg b, .cx a b]

/-- Construction for native One in the measurement gate semantics model. -/
def nativeOne {W : Type*} : BitGate W → List (NativeGate W)
  | .cx c t => [.cx c t]
  | .ccx a b t => toffoliWord a b t

/-- Construction for native Word in the measurement gate semantics model. -/
def nativeWord {W : Type*} (gs : List (BitGate W)) : List (NativeGate W) :=
  gs.flatMap nativeOne

/-- Construction for act in the measurement gate semantics model. -/
def act {W : Type*} [DecidableEq W] (g : BitGate W) (x : W → Bool) : W → Bool :=
  match g with
  | .cx c t => Function.update x t (x t ^^ x c)
  | .ccx a b t => Function.update x t (x t ^^ (x a && x b))

/-- Construction for run in the measurement gate semantics model. -/
def run {W : Type*} [DecidableEq W] (gs : List (BitGate W)) (x : W → Bool) : W → Bool :=
  gs.foldl (fun z g => act g z) x

/-- Recursive spelling of the same compute/target/uncompute ladder as _multi_x. -/
def multiX {W : Type*} (controls : List W) (t : W) (work : List W) : List (BitGate W) :=
  match controls, work with
  | [a], _ => [.cx a t]
  | [a,b], _ => [.ccx a b t]
  | a::b::c::rest, w::ws =>
      [.ccx a b w] ++ multiX (w::c::rest) t ws ++ [.ccx a b w]
  | _, _ => []
termination_by work.length

/-- Complete original `all_update_not_mem` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
private theorem all_update_not_mem {W : Type*} [DecidableEq W]
    (l : List W) (x : W → Bool) (w : W) (v : Bool) (hw : w ∉ l) :
    l.all (Function.update x w v) = l.all x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mem_cons, not_or] at hw
    simp only [List.all_cons, Function.update_of_ne (Ne.symm hw.1), ih hw.2]

/-- Complete original `multiX_basis` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem multiX_basis {W : Type*} [DecidableEq W] (cs : List W) (t : W)
    (ws : List W) (x : W → Bool) (hpos : 0 < cs.length)
    (hsize : cs.length ≤ ws.length+2) (hn : (cs ++ t::ws).Nodup)
    (hclean : ∀ w ∈ ws, x w=false) :
    run (multiX cs t ws) x = Function.update x t (x t ^^ cs.all x) := by
  induction ws generalizing cs x with
  | nil =>
    match cs with
    | [] => simp at hpos
    | [a] => simp [multiX, run, act]
    | [a,b] => simp [multiX, run, act]
    | a::b::c::rest => simp at hsize
  | cons w ws ih =>
    match cs with
    | [] => simp at hpos
    | [a] => simp [multiX, run, act]
    | [a,b] => simp [multiX, run, act]
    | a::b::c::rest =>
      have ha := (List.nodup_cons.mp hn).1
      have hb := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
      have hshort := hn.tail.tail
      have hrec : ((w::c::rest) ++ t::ws).Nodup := by
        have h := (List.nodup_middle (l₁ := (c::rest) ++ [t]) (a := w) (l₂ := ws)).mp
          (by simpa only [List.cons_append, List.tail_cons, List.nil_append, List.append_assoc, List.singleton_append] using hshort)
        simpa only [List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] using h
      have hw := (List.nodup_cons.mp hrec).1
      have hat : a ≠ t := by intro h; exact ha (by simp [h])
      have hbt : b ≠ t := by intro h; exact hb (by simp [h])
      have haw : a ≠ w := by intro h; exact ha (by simp [h])
      have hbw : b ≠ w := by intro h; exact hb (by simp [h])
      have hwt : w ≠ t := by intro h; exact hw (by simp [h])
      have hwc : w ∉ c::rest := by intro h; exact hw (List.mem_append_left _ h)
      let y := act (.ccx a b w) x
      have hy (v : W) (hv : v ∈ ws) : y v=false := by
        have hvw : v ≠ w := by intro h; exact hw (by simp [← h,hv])
        simpa only [y, act, Function.update_of_ne hvw] using hclean v (by simp [hv])
      have hall : (w::c::rest).all y=(a::b::c::rest).all x := by
        change (y w && (c::rest).all y) = _
        rw [show y w=(x a && x b) by simp [y,act,hclean w (by simp)]]
        rw [show (c::rest).all y=(c::rest).all x from
          all_update_not_mem (c::rest) x w _ hwc]
        simp only [List.all_cons, Bool.and_assoc]
      rw [multiX]
      simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change act (.ccx a b w) (run (multiX (w::c::rest) t ws) y) = _
      rw [ih (w::c::rest) y (by simp) (by simp only [List.length_cons] at hsize ⊢; omega) hrec hy]
      rw [hall]
      funext v
      by_cases hvt : v=t
      · subst v
        simp [act, y, Function.update_of_ne hwt.symm]
      · by_cases hvw : v=w
        · subst v
          simp [act, y, Function.update_of_ne hwt, Function.update_of_ne hat,
            Function.update_of_ne hbt, Function.update_of_ne haw,
            Function.update_of_ne hbw, hclean w (by simp)]
        · simp [act, y, Function.update_of_ne hvt, Function.update_of_ne hvw]

/-- Construction for legal in the measurement gate semantics model. -/
def legal {W : Type*} : BitGate W → Prop
  | .cx c t => c ≠ t
  | .ccx a b t => a ≠ b ∧ a ≠ t ∧ b ≠ t

/-- Complete original `multiX_legal` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem multiX_legal {W : Type*} (cs : List W) (t : W) (ws : List W)
    (hn : (cs ++ t::ws).Nodup) : ∀ g ∈ multiX cs t ws, legal g := by
  induction ws generalizing cs with
  | nil =>
    match cs with
    | [a] => simpa [multiX, legal] using (List.nodup_cons.mp hn).1
    | [a,b] =>
      have ha := (List.nodup_cons.mp hn).1
      have hb := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
      simpa [multiX, legal, and_assoc] using And.intro ha hb
    | [] => simp [multiX]
    | a::b::c::rest => simp [multiX]
  | cons w ws ih =>
    match cs with
    | [] => simp [multiX]
    | [a] =>
      have ha := (List.nodup_cons.mp hn).1
      intro g hg
      simp only [multiX, List.mem_singleton] at hg
      subst g
      exact fun h => ha (by simp [h])
    | [a,b] =>
      have ha := (List.nodup_cons.mp hn).1
      have hb := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
      intro g hg
      simp only [multiX, List.mem_singleton] at hg
      subst g
      exact ⟨fun h => ha (by simp [h]), fun h => ha (by simp [h]),
        fun h => hb (by simp [h])⟩
    | a::b::c::rest =>
      have ha := (List.nodup_cons.mp hn).1
      have hb := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
      have hrec : ((w::c::rest) ++ t::ws).Nodup := by
        have h := (List.nodup_middle (l₁ := (c::rest) ++ [t]) (a := w) (l₂ := ws)).mp
          (by simpa only [List.cons_append, List.tail_cons, List.nil_append, List.append_assoc, List.singleton_append] using hn.tail.tail)
        simpa only [List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] using h
      have hab : a ≠ b := by intro h; exact ha (by simp [h])
      have haw : a ≠ w := by intro h; exact ha (by simp [h])
      have hbw : b ≠ w := by intro h; exact hb (by simp [h])
      intro g hg
      simp only [multiX, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (h | h) | h
      · subst g; exact ⟨hab,haw,hbw⟩
      · exact ih (w::c::rest) hrec g h
      · subst g; exact ⟨hab,haw,hbw⟩

/-- Complete original `multiX_length` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem multiX_length {W : Type*} (cs : List W) (t : W) (ws : List W)
    (hpos : 0 < cs.length) (hsize : cs.length ≤ ws.length+2) :
    (multiX cs t ws).length = if cs.length=1 then 1 else 2*cs.length-3 := by
  induction ws generalizing cs with
  | nil =>
    match cs with
    | [] => simp at hpos
    | [a] => simp [multiX]
    | [a,b] => simp [multiX]
    | a::b::c::rest => simp at hsize
  | cons w ws ih =>
    match cs with
    | [] => simp at hpos
    | [a] => simp [multiX]
    | [a,b] => simp [multiX]
    | a::b::c::rest =>
      rw [multiX, List.length_append, List.length_append,
        ih (w::c::rest) (by simp) (by simp only [List.length_cons] at hsize ⊢; omega)]
      simp only [List.length_cons, List.length_nil] at *
      split_ifs <;> omega

end Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit

namespace Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib
open scoped BigOperators

/-- Construction for compile One in the measurement gate semantics model. -/
noncomputable def compileOne {n : ℕ} : BitGate (Fin n) → List (ReflectionGate n)
  | .cx c t => [.inr (c,t)]
  | .ccx a b t => toffoliLocalSteps a b t

/-- Construction for compile Bits in the measurement gate semantics model. -/
noncomputable def compileBits {n : ℕ} (gs : List (BitGate (Fin n))) :
    List (ReflectionGate n) := gs.flatMap compileOne

/-- Construction for native Matrix in the measurement gate semantics model. -/
noncomputable def nativeMatrix {n : ℕ} : NativeGate (Fin n) → ReflectionGate n
  | .h w => .inl (w,Hadamard)
  | .t w => .inl (w,tGate)
  | .tdg w => .inl (w,tGateAdj)
  | .cx c t => .inr (c,t)

/-- Complete original `native_toffoli_table` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem native_toffoli_table {n : ℕ} (a b t : Fin n) :
    (toffoliWord a b t).map nativeMatrix = toffoliLocalSteps a b t := rfl

/-- Complete original `native_word_compile` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem native_word_compile {n : ℕ} (gs : List (BitGate (Fin n))) :
    (nativeWord gs).map nativeMatrix = compileBits gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [nativeWord, List.flatMap_cons, List.map_append, compileBits] at *
    rw [ih]
    cases g <;> rfl

/-- Complete original `compile_one_exact` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem compile_one_exact {n : ℕ} (g : BitGate (Fin n)) (hg : legal g) (x : Reg n) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (reflectionCompile (compileOne g)) (Ket x) =
      Ket (act g x) := by
  cases g with
  | cx c t =>
    simpa [compileOne, reflectionCompile, reflectionGateMatrix, act] using
      applyGate_cnotGate_ket n c t hg x
  | ccx a b t => exact (local_toffoli_fifteen_exact n a b t hg.1 hg.2.1 hg.2.2).2.2 x

/-- Complete original `compile_append` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
private theorem compile_append {n : ℕ} (gs hs : List (ReflectionGate n)) :
    reflectionCompile (gs ++ hs) = reflectionCompile gs ++ reflectionCompile hs :=
  List.map_append

/-- Complete original `compile_bits_exact` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem compile_bits_exact {n : ℕ} (gs : List (BitGate (Fin n)))
    (hg : ∀ g ∈ gs, legal g) (x : Reg n) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (reflectionCompile (compileBits gs)) (Ket x) =
      Ket (run gs x) := by
  induction gs generalizing x with
  | nil => simp [compileBits, reflectionCompile, run]
  | cons g gs ih =>
    have hhead := hg g (by simp)
    have htail : ∀ h ∈ gs, legal h := fun h hh => hg h (by simp [hh])
    simp only [compileBits, List.flatMap_cons, compile_append, run_append]
    rw [compile_one_exact g hhead]
    exact ih htail (act g x)

/-- Complete original `compiled_multiX_clean_ket` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem compiled_multiX_clean_ket {n : ℕ} (cs : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) (x : Reg n) (hpos : 0 < cs.length)
    (hsize : cs.length ≤ ws.length+2) (hn : (cs ++ t::ws).Nodup)
    (hclean : ∀ w ∈ ws, x w=false) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (reflectionCompile (compileBits (multiX cs t ws))) (Ket x) =
      Ket (Function.update x t (x t ^^ cs.all x)) := by
  rw [compile_bits_exact _ (multiX_legal cs t ws hn), multiX_basis cs t ws x hpos hsize hn hclean]

-- Full complex linearity, including relative phases, on the clean-work subspace.
/-- Complete original `compiled_multiX_clean_superposition` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem compiled_multiX_clean_superposition {n : ℕ} {J : Type*} [Fintype J]
    (cs : List (Fin n)) (t : Fin n) (ws : List (Fin n))
    (x : J → Reg n) (φ : J → ℂ) (hpos : 0 < cs.length)
    (hsize : cs.length ≤ ws.length+2) (hn : (cs ++ t::ws).Nodup)
    (hclean : ∀ j w, w ∈ ws → x j w=false) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (reflectionCompile (compileBits (multiX cs t ws))) (∑ j, φ j • Ket (x j)) =
      ∑ j, φ j • Ket (Function.update (x j) t (x j t ^^ cs.all (x j))) := by
  rw [run_reflectionCompile]
  change Matrix.mulVec (reflectionProgramMatrix (compileBits (multiX cs t ws))) (∑ j, φ j • Ket (x j)) = _
  rw [Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mulVec_smul]
  change φ j • ApplyGate (reflectionProgramMatrix (compileBits (multiX cs t ws))) (Ket (x j)) = _
  rw [← run_reflectionCompile, compiled_multiX_clean_ket cs t ws (x j) hpos hsize hn (hclean j)]

/-- Complete original `compile_bits_legal` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem compile_bits_legal {n : ℕ} (gs : List (BitGate (Fin n)))
    (hg : ∀ g ∈ gs, legal g) : reflectionLegal (compileBits gs) := by
  intro g h
  obtain ⟨b,hb,hmem⟩ := List.mem_flatMap.mp h
  have hlegal := hg b hb
  cases b with
  | cx c t =>
    simp only [compileOne, List.mem_singleton] at hmem
    subst g
    exact hlegal
  | ccx a b t => exact toffoliLocalSteps_legal a b t hlegal.1 hlegal.2.1 hlegal.2.2 g hmem

/-- Complete original `compiled_multiX_gate_count` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem compiled_multiX_gate_count {n : ℕ} (cs : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) (hpos : 0 < cs.length) (hsize : cs.length ≤ ws.length+2) :
    (compileBits (multiX cs t ws)).length =
      if cs.length=1 then 1 else 15*(2*cs.length-3) := by
  induction ws generalizing cs with
  | nil =>
    match cs with
    | [] => simp at hpos
    | [a] => simp [multiX, compileBits, compileOne]
    | [a,b] => simp [multiX, compileBits, compileOne, toffoliLocalSteps_length]
    | a::b::c::rest => simp at hsize
  | cons w ws ih =>
    match cs with
    | [] => simp at hpos
    | [a] => simp [multiX, compileBits, compileOne]
    | [a,b] => simp [multiX, compileBits, compileOne, toffoliLocalSteps_length]
    | a::b::c::rest =>
      have hword : compileBits (multiX (a::b::c::rest) t (w::ws)) =
          toffoliLocalSteps a b w ++ compileBits (multiX (w::c::rest) t ws) ++ toffoliLocalSteps a b w := by
        rw [multiX]
        simp [compileBits, compileOne, List.flatMap_append]
      rw [hword, List.length_append, List.length_append, toffoliLocalSteps_length,
        ih (w::c::rest) (by simp) (by simp only [List.length_cons] at hsize ⊢; omega)]
      simp only [List.length_cons]
      split_ifs <;> omega

/-- Complete original `compiled_multiX_semantics_and_cost` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem compiled_multiX_semantics_and_cost {n : ℕ} (cs : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) (hpos : 0 < cs.length) (hsize : cs.length ≤ ws.length+2)
    (hn : (cs ++ t::ws).Nodup) :
    let gates := compileBits (multiX cs t ws)
    let program := reflectionCompile gates
    reflectionLegal gates ∧ QueryCount program=0 ∧
      GateCount program=(if cs.length=1 then 1 else 15*(2*cs.length-3)) ∧
      ∀ x : Reg n, (∀ w ∈ ws, x w=false) →
        Run (1 : Matrix (Reg n) (Reg n) ℂ) program (Ket x) =
          Ket (Function.update x t (x t ^^ cs.all x)) := by
  refine ⟨compile_bits_legal _ (multiX_legal cs t ws hn), queryCount_reflectionCompile _, ?_, ?_⟩
  · rw [gateCount_reflectionCompile, compiled_multiX_gate_count cs t ws hpos hsize]
  · exact fun x hclean => compiled_multiX_clean_ket cs t ws x hpos hsize hn hclean

/-- Complete original `native_multiX_gate_count` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem native_multiX_gate_count {n : ℕ} (cs : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) (hpos : 0 < cs.length) (hsize : cs.length ≤ ws.length+2) :
    (nativeWord (multiX cs t ws)).length =
      if cs.length=1 then 1 else 15*(2*cs.length-3) := by
  calc
    _ = ((nativeWord (multiX cs t ws)).map nativeMatrix).length := (List.length_map _).symm
    _ = _ := by rw [native_word_compile, compiled_multiX_gate_count cs t ws hpos hsize]

/-- Complete original `native_multiX_clean_superposition` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem native_multiX_clean_superposition {n : ℕ} {J : Type*} [Fintype J]
    (cs : List (Fin n)) (t : Fin n) (ws : List (Fin n))
    (x : J → Reg n) (φ : J → ℂ) (hpos : 0 < cs.length)
    (hsize : cs.length ≤ ws.length+2) (hn : (cs ++ t::ws).Nodup)
    (hclean : ∀ j w, w ∈ ws → x j w=false) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (reflectionCompile ((nativeWord (multiX cs t ws)).map nativeMatrix))
      (∑ j, φ j • Ket (x j)) =
      ∑ j, φ j • Ket (Function.update (x j) t (x j t ^^ cs.all (x j))) := by
  rw [native_word_compile]
  exact compiled_multiX_clean_superposition cs t ws x φ hpos hsize hn hclean

end Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit

#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.multiX_basis
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.multiX_legal
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.multiX_length
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.native_toffoli_table
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.native_word_compile
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.compile_one_exact
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.compile_bits_exact
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.compiled_multiX_clean_ket
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.compiled_multiX_clean_superposition
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.compile_bits_legal
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.compiled_multiX_gate_count
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.compiled_multiX_semantics_and_cost
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.native_multiX_gate_count
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.native_multiX_clean_superposition


namespace Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit

/-- Construction for increment Aux in the measurement gate semantics model. -/
def incrementAux {W : Type*} (lower axis work : List W) : List (BitGate W) :=
  match axis with
  | [] => []
  | a::rest => incrementAux (lower++[a]) rest work ++ multiX lower a work
termination_by axis.length

/-- Construction for increment Word in the measurement gate semantics model. -/
def incrementWord {W : Type*} (control : W) (axis work : List W) : List (BitGate W) :=
  incrementAux [control] axis work

/-- Construction for axis Increment in the measurement gate semantics model. -/
def axisIncrement {W : Type*} [DecidableEq W] (carry : Bool) (axis : List W)
    (x : W → Bool) : W → Bool :=
  match axis with
  | [] => x
  | a::rest => Function.update (axisIncrement (carry && x a) rest x) a (x a ^^ carry)

/-- Complete original `axis_increment_off` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem axis_increment_off {W : Type*} [DecidableEq W] (carry : Bool)
    (axis : List W) (x : W → Bool) (v : W) (hv : v ∉ axis) :
    axisIncrement carry axis x v=x v := by
  induction axis generalizing carry with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.mem_cons, not_or] at hv
    simp only [axisIncrement, Function.update_of_ne hv.1, ih _ hv.2]

/-- Construction for ripple in the measurement gate semantics model. -/
def ripple (carry : Bool) : List Bool → List Bool
  | [] => []
  | b::bs => (b ^^ carry)::ripple (carry && b) bs

/-- Construction for axis Value in the measurement gate semantics model. -/
def axisValue : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*axisValue bs

/-- Complete original `ripple_length` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem ripple_length (bits : List Bool) (carry : Bool) :
    (ripple carry bits).length=bits.length := by
  induction bits generalizing carry with
  | nil => rfl
  | cons b bs ih => simp only [ripple, List.length_cons, ih]

/-- Complete original `axis_value_bound` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem axis_value_bound (bits : List Bool) : axisValue bits < 2^bits.length := by
  induction bits with
  | nil => decide
  | cons b bs ih =>
    cases b <;> simp only [axisValue, Bool.toNat_false, Bool.toNat_true,
      List.length_cons, Nat.pow_succ] <;> omega

/-- Complete original `ripple_with_overflow` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem ripple_with_overflow (bits : List Bool) (carry : Bool) :
    axisValue (ripple carry bits)+2^bits.length*(carry && bits.all id).toNat =
      axisValue bits+carry.toNat := by
  induction bits generalizing carry with
  | nil => cases carry <;> rfl
  | cons b bs ih =>
    have hh := ih (carry && b)
    cases b <;> cases carry <;>
      simp only [ripple, axisValue, List.length_cons, Nat.pow_succ, List.all_cons,
        Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true,
        Bool.xor_false, Bool.xor_true, Bool.toNat_false, Bool.toNat_true,
        Bool.not_false, Bool.not_true, id_eq, Nat.mul_zero, Nat.add_zero,
        Nat.zero_add] at hh ⊢ <;> first | omega | ((try ring_nf at hh); (try ring_nf); omega)

/-- Complete original `ripple_value` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem ripple_value (bits : List Bool) (carry : Bool) :
    axisValue (ripple carry bits)=(axisValue bits+carry.toNat) % 2^bits.length := by
  have h := congrArg (fun k => k % 2^bits.length) (ripple_with_overflow bits carry)
  have hlt : axisValue (ripple carry bits) < 2^bits.length := by
    simpa only [ripple_length] using axis_value_bound (ripple carry bits)
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt] at h
  exact h

/-- Complete original `axis_increment_bits` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem axis_increment_bits {W : Type*} [DecidableEq W] (carry : Bool)
    (axis : List W) (x : W → Bool) (hn : axis.Nodup) :
    axis.map (axisIncrement carry axis x)=ripple carry (axis.map x) := by
  induction axis generalizing carry with
  | nil => rfl
  | cons a rest ih =>
    have ha := (List.nodup_cons.mp hn).1
    have hr := (List.nodup_cons.mp hn).2
    simp only [axisIncrement, List.map_cons, ripple, Function.update_self]
    congr 1
    rw [← ih (carry && x a) hr]
    apply List.map_congr_left
    intro v hv
    have hva : v ≠ a := by intro h; subst v; exact ha hv
    exact Function.update_of_ne hva _ _

/-- Complete original `increment_aux_basis` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem increment_aux_basis {W : Type*} [DecidableEq W]
    (lower axis ws : List W) (x : W → Bool) (hpos : 0 < lower.length)
    (hsize : lower.length+axis.length ≤ ws.length+3)
    (hn : (lower++(axis++ws)).Nodup) (hclean : ∀ w ∈ ws, x w=false) :
    run (incrementAux lower axis ws) x=axisIncrement (lower.all x) axis x := by
  induction axis generalizing lower with
  | nil => simp [incrementAux, run, axisIncrement]
  | cons a rest ih =>
    have htail : run (incrementAux (lower++[a]) rest ws) x =
        axisIncrement ((lower++[a]).all x) rest x := by
      apply ih
      · simp only [List.length_append, List.length_singleton]; omega
      · simp only [List.length_append, List.length_cons, List.length_nil] at hsize ⊢
        omega
      · simpa only [List.nil_append, List.append_assoc, List.singleton_append, List.cons_append] using hn
    have hnow : (lower++a::ws).Nodup := by
      apply List.Nodup.sublist _ hn
      exact (List.Sublist.cons_cons a (List.sublist_append_right rest ws)).append_left lower
    have hndtail : (a::rest++ws).Nodup := hn.of_append_right
    have hrestws : (rest++ws).Nodup := hndtail.tail
    have han : a ∉ rest := by
      intro h
      exact (List.nodup_cons.mp hndtail).1 (List.mem_append_left _ h)
    let y := axisIncrement ((lower++[a]).all x) rest x
    have hpres (v : W) (hv : v ∈ lower) : y v=x v := by
      apply axis_increment_off
      intro hvr
      exact List.disjoint_left.mp hn.disjoint hv (List.mem_cons_of_mem a (List.mem_append_left _ hvr))
    have hyclean (w : W) (hw : w ∈ ws) : y w=false := by
      rw [show y w=x w from axis_increment_off _ _ _ _ (by
        intro hwr
        exact List.disjoint_left.mp hrestws.disjoint hwr hw)]
      exact hclean w hw
    have hya : y a=x a := axis_increment_off _ _ _ _ han
    have hall : lower.all y=lower.all x := by
      have hm := List.map_congr_left hpres
      have he := congrArg (fun l : List Bool => l.all id) hm
      simpa only [List.all_map, Function.comp_def, id_eq] using he
    rw [incrementAux]
    simp only [run, List.foldl_append]
    change run (multiX lower a ws) (run (incrementAux (lower++[a]) rest ws) x) = _
    rw [htail, multiX_basis lower a ws y hpos (by
      simp only [List.length_cons] at hsize; omega) hnow hyclean]
    rw [hya, hall]
    simp only [y, axisIncrement, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

/-- Complete original `increment_word_value` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem increment_word_value {W : Type*} [DecidableEq W]
    (control : W) (axis ws : List W) (x : W → Bool)
    (hsize : axis.length ≤ ws.length+2) (hn : (control::(axis++ws)).Nodup)
    (hclean : ∀ w ∈ ws, x w=false) :
    axisValue (axis.map (run (incrementWord control axis ws) x)) =
      (axisValue (axis.map x)+(x control).toNat) % 2^axis.length := by
  rw [incrementWord, increment_aux_basis [control] axis ws x (by simp)
    (by simp only [List.length_cons, List.length_nil]; omega) hn hclean]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  have haxisws : (axis++ws).Nodup := hn.tail
  rw [axis_increment_bits _ _ _ haxisws.of_append_left, ripple_value, List.length_map]

/-- Complete original `increment_word_basis` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem increment_word_basis {W : Type*} [DecidableEq W]
    (control : W) (axis ws : List W) (x : W → Bool)
    (hsize : axis.length ≤ ws.length+2) (hn : (control::(axis++ws)).Nodup)
    (hclean : ∀ w ∈ ws, x w=false) :
    run (incrementWord control axis ws) x=axisIncrement (x control) axis x := by
  simpa only [incrementWord, List.all_cons, List.all_nil, Bool.and_true] using
    increment_aux_basis [control] axis ws x (by simp)
      (by simp only [List.length_cons, List.length_nil]; omega) hn hclean

/-- Complete original `increment_aux_legal` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem increment_aux_legal {W : Type*} (lower axis ws : List W)
    (hn : (lower++(axis++ws)).Nodup) : ∀ g ∈ incrementAux lower axis ws, legal g := by
  induction axis generalizing lower with
  | nil => simp [incrementAux]
  | cons a rest ih =>
    have htail : ((lower++[a])++(rest++ws)).Nodup := by
      simpa only [List.nil_append, List.append_assoc, List.singleton_append, List.cons_append] using hn
    have hnow : (lower++a::ws).Nodup := by
      apply List.Nodup.sublist _ hn
      exact (List.Sublist.cons_cons a (List.sublist_append_right rest ws)).append_left lower
    intro g hg
    rw [incrementAux, List.mem_append] at hg
    rcases hg with h | h
    · exact ih (lower++[a]) htail g h
    · exact multiX_legal lower a ws hnow g h

/-- Complete original `act_involutive` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem act_involutive {W : Type*} [DecidableEq W] (g : BitGate W) (hg : legal g) :
    Function.Involutive (act g) := by
  intro x
  cases g with
  | cx c t =>
    funext v
    by_cases hv : v=t
    · subst v; simp [act, Function.update_of_ne hg]
    · simp [act, Function.update_of_ne hv]
  | ccx a b t =>
    funext v
    by_cases hv : v=t
    · subst v
      simp [act, Function.update_of_ne hg.2.1, Function.update_of_ne hg.2.2]
    · simp [act, Function.update_of_ne hv]

/-- Complete original `run_reverse_cancel` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem run_reverse_cancel {W : Type*} [DecidableEq W] (gs : List (BitGate W))
    (hg : ∀ g ∈ gs, legal g) (x : W → Bool) : run gs.reverse (run gs x)=x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    have htail : ∀ h ∈ gs, legal h := fun h hh => hg h (by simp [hh])
    rw [List.reverse_cons]
    simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change act g (run gs.reverse (run gs (act g x)))=x
    rw [ih htail]
    exact act_involutive g (hg g (by simp)) x

/-- Complete original `run_cancel_reverse` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem run_cancel_reverse {W : Type*} [DecidableEq W] (gs : List (BitGate W))
    (hg : ∀ g ∈ gs, legal g) (x : W → Bool) : run gs (run gs.reverse x)=x := by
  have hr : ∀ g ∈ gs.reverse, legal g := by simpa only [List.mem_reverse] using hg
  simpa only [List.reverse_reverse] using run_reverse_cancel gs.reverse hr x

end Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit


namespace Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib
open scoped BigOperators

/-- Complete original `native_word_superposition` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
private theorem native_word_superposition {n : ℕ} {J : Type*} [Fintype J]
    (gs : List (BitGate (Fin n))) (hg : ∀ g ∈ gs, legal g)
    (x : J → Reg n) (φ : J → ℂ) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (reflectionCompile ((nativeWord gs).map nativeMatrix)) (∑ j, φ j • Ket (x j)) =
      ∑ j, φ j • Ket (run gs (x j)) := by
  rw [native_word_compile, run_reflectionCompile]
  change Matrix.mulVec (reflectionProgramMatrix (compileBits gs)) (∑ j, φ j • Ket (x j)) = _
  rw [Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mulVec_smul]
  change φ j • ApplyGate (reflectionProgramMatrix (compileBits gs)) (Ket (x j)) = _
  rw [← run_reflectionCompile, compile_bits_exact gs hg]

/-- Complete original `native_increment_clean_ket` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem native_increment_clean_ket {n : ℕ} (control : Fin n)
    (axis ws : List (Fin n)) (x : Reg n) (hsize : axis.length ≤ ws.length+2)
    (hn : (control::(axis++ws)).Nodup) (hclean : ∀ w ∈ ws, x w=false) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (reflectionCompile ((nativeWord (incrementWord control axis ws)).map nativeMatrix)) (Ket x) =
      Ket (axisIncrement (x control) axis x) := by
  rw [native_word_compile, compile_bits_exact (incrementWord control axis ws) (increment_aux_legal [control] axis ws hn)]
  exact congrArg Ket (increment_word_basis control axis ws x hsize hn hclean)

/-- Complete original `native_increment_clean_superposition` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem native_increment_clean_superposition {n : ℕ} {J : Type*} [Fintype J]
    (control : Fin n) (axis ws : List (Fin n)) (x : J → Reg n) (φ : J → ℂ)
    (hsize : axis.length ≤ ws.length+2) (hn : (control::(axis++ws)).Nodup)
    (hclean : ∀ j w, w ∈ ws → x j w=false) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (reflectionCompile ((nativeWord (incrementWord control axis ws)).map nativeMatrix))
      (∑ j, φ j • Ket (x j)) =
      ∑ j, φ j • Ket (axisIncrement (x j control) axis (x j)) := by
  rw [native_word_superposition (incrementWord control axis ws) (increment_aux_legal [control] axis ws hn)]
  apply Finset.sum_congr rfl
  intro j _
  rw [increment_word_basis control axis ws (x j) hsize hn (hclean j)]

/-- Complete original `native_word_reverse_cancel` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem native_word_reverse_cancel {n : ℕ} {J : Type*} [Fintype J]
    (gs : List (BitGate (Fin n))) (hg : ∀ g ∈ gs, legal g)
    (x : J → Reg n) (φ : J → ℂ) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (reflectionCompile ((nativeWord gs.reverse).map nativeMatrix))
      (Run (1 : Matrix (Reg n) (Reg n) ℂ)
        (reflectionCompile ((nativeWord gs).map nativeMatrix)) (∑ j, φ j • Ket (x j))) =
      ∑ j, φ j • Ket (x j) := by
  have hr : ∀ g ∈ gs.reverse, legal g := by simpa only [List.mem_reverse] using hg
  rw [native_word_superposition gs hg, native_word_superposition gs.reverse hr]
  simp_rw [run_reverse_cancel gs hg]

/-- Complete original `native_increment_semantics_and_cost` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem native_increment_semantics_and_cost {n : ℕ} (control : Fin n)
    (axis ws : List (Fin n)) (hsize : axis.length ≤ ws.length+2)
    (hn : (control::(axis++ws)).Nodup) :
    let word := nativeWord (incrementWord control axis ws)
    let gates := word.map nativeMatrix
    let program := reflectionCompile gates
    reflectionLegal gates ∧ QueryCount program=0 ∧ GateCount program=word.length ∧
      ∀ x : Reg n, (∀ w ∈ ws, x w=false) →
        Run (1 : Matrix (Reg n) (Reg n) ℂ) program (Ket x) =
          Ket (axisIncrement (x control) axis x) := by
  dsimp only
  rw [native_word_compile]
  refine ⟨compile_bits_legal _ (increment_aux_legal [control] axis ws hn),
    queryCount_reflectionCompile _, ?_, ?_⟩
  · rw [gateCount_reflectionCompile, ← native_word_compile, List.length_map]
  · intro x hclean
    simpa only [native_word_compile] using native_increment_clean_ket control axis ws x hsize hn hclean

end Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit

#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.axis_increment_off
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.ripple_length
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.axis_value_bound
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.ripple_with_overflow
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.ripple_value
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.axis_increment_bits
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.increment_aux_basis
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.increment_word_value
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.increment_word_basis
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.increment_aux_legal
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.act_involutive
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.run_reverse_cancel
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.run_cancel_reverse
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.native_increment_clean_ket
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.native_increment_clean_superposition
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.native_word_reverse_cancel
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.native_increment_semantics_and_cost


namespace Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib

/-- Complete original `axis_value_injective` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem axis_value_injective (a b : List Bool) (hlen : a.length=b.length)
    (hv : axisValue a=axisValue b) : a=b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons q qs => simp at hlen
  | cons p ps ih =>
    cases b with
    | nil => simp at hlen
    | cons q qs =>
      have ht : ps.length=qs.length := by simpa only [List.length_cons, Nat.succ_inj] using hlen
      cases p <;> cases q <;>
        simp only [axisValue, Bool.toNat_false, Bool.toNat_true] at hv <;>
        first | omega | (congr 1; exact ih qs ht (by omega))

/-- Executable low-endian decoder, independent of the library's other bit order. -/
def littleAddress (r : ℕ) (x : Reg r) : Fin (2^r) :=
  ⟨axisValue (List.ofFn x), by simpa only [List.length_ofFn] using axis_value_bound (List.ofFn x)⟩

/-- Complete original `little_address_injective` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem little_address_injective (r : ℕ) : Function.Injective (littleAddress r) := by
  intro x y h
  apply List.ofFn_injective
  apply axis_value_injective
  · simp only [List.length_ofFn]
  · exact congrArg Fin.val h

/-- Construction for little Endian Equiv in the measurement gate semantics model. -/
noncomputable def littleEndianEquiv (r : ℕ) : Reg r ≃ Fin (2^r) :=
  Equiv.ofBijective (littleAddress r) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨little_address_injective r, by simp only [card_reg, Fintype.card_fin]⟩)

/-- Complete original `little_endian_equiv_apply` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
@[simp] theorem little_endian_equiv_apply (r : ℕ) (x : Reg r) :
    littleEndianEquiv r x=littleAddress r x := rfl

/-- Construction for register Width in the measurement gate semantics model. -/
def registerWidth (d r : ℕ) : ℕ := d*r+2+(r-2)

/-- Construction for axis Wire in the measurement gate semantics model. -/
def axisWire (d r : ℕ) (j : Fin d) (i : Fin r) : Fin (registerWidth d r) :=
  ⟨(finProdFinEquiv (j,i)).val, by
    have hi := (finProdFinEquiv (j,i)).isLt
    unfold registerWidth
    omega⟩

/-- Construction for test Wire in the measurement gate semantics model. -/
def testWire (d r : ℕ) : Fin (registerWidth d r) := ⟨d*r+1, by unfold registerWidth; omega⟩

/-- Construction for spin Wire in the measurement gate semantics model. -/
def spinWire (d r : ℕ) : Fin (registerWidth d r) := ⟨d*r, by unfold registerWidth; omega⟩

/-- Construction for work Wire in the measurement gate semantics model. -/
def workWire (d r : ℕ) (i : Fin (r-2)) : Fin (registerWidth d r) :=
  ⟨d*r+2+i.val, by have hi := i.isLt; unfold registerWidth; omega⟩

/-- Construction for axis Wires in the measurement gate semantics model. -/
def axisWires (d r : ℕ) (j : Fin d) : List (Fin (registerWidth d r)) :=
  List.ofFn (axisWire d r j)

/-- Construction for work Wires in the measurement gate semantics model. -/
def workWires (d r : ℕ) : List (Fin (registerWidth d r)) := List.ofFn (workWire d r)

/-- Complete original `axis_wire_val` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem axis_wire_val (d r : ℕ) (j : Fin d) (i : Fin r) :
    (axisWire d r j i).val=j.val*r+i.val := by
  change i.val+r*j.val=j.val*r+i.val
  ac_rfl

/-- Complete original `axis_wire_lt_positions` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem axis_wire_lt_positions (d r : ℕ) (j : Fin d) (i : Fin r) :
    (axisWire d r j i).val < d*r := (finProdFinEquiv (j,i)).isLt

/-- Complete original `axis_wire_pair_injective` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem axis_wire_pair_injective (d r : ℕ) :
    Function.Injective (fun p : Fin d × Fin r => axisWire d r p.1 p.2) := by
  intro x y h
  apply finProdFinEquiv.injective
  apply Fin.ext
  exact congrArg (fun z : Fin (registerWidth d r) => z.val) h

/-- Complete original `axis_wires_nodup` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem axis_wires_nodup (d r : ℕ) (j : Fin d) : (axisWires d r j).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i k h
  exact congrArg Prod.snd (@axis_wire_pair_injective d r (j,i) (j,k) h)

/-- Complete original `work_wires_nodup` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem work_wires_nodup (d r : ℕ) : (workWires d r).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i k h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change d*r+2+i.val=d*r+2+k.val at hv
  omega

/-- Complete original `axis_work_disjoint` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem axis_work_disjoint (d r : ℕ) (j : Fin d) :
    List.Disjoint (axisWires d r j) (workWires d r) := by
  rw [List.disjoint_left]
  intro v hv hw
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hv
  obtain ⟨k,hk⟩ := List.mem_ofFn.mp hw
  have hlt := axis_wire_lt_positions d r j i
  have he := congrArg Fin.val (hi.trans hk.symm)
  change (axisWire d r j i).val=d*r+2+k.val at he
  omega

/-- Complete original `layout_wires_nodup` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem layout_wires_nodup (d r : ℕ) (j : Fin d) :
    (testWire d r :: (axisWires d r j ++ workWires d r)).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro h
    rw [List.mem_append] at h
    rcases h with h | h
    · obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
      have hlt := axis_wire_lt_positions d r j i
      have he := congrArg Fin.val hi
      change (axisWire d r j i).val=d*r+1 at he
      omega
    · obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
      have he := congrArg Fin.val hi
      change d*r+2+i.val=d*r+1 at he
      omega
  · exact (axis_wires_nodup d r j).append (work_wires_nodup d r) (axis_work_disjoint d r j)

/-- Complete original `layout_work_sufficient` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem layout_work_sufficient (d r : ℕ) (j : Fin d) :
    (axisWires d r j).length ≤ (workWires d r).length+2 := by
  simp only [axisWires, workWires, List.length_ofFn]
  omega

/-- Construction for spatial Increment Word in the measurement gate semantics model. -/
def spatialIncrementWord (d r : ℕ) (j : Fin d) : List (BitGate (Fin (registerWidth d r))) :=
  incrementWord (testWire d r) (axisWires d r j) (workWires d r)

/-- Construction for site Address in the measurement gate semantics model. -/
def siteAddress (d r : ℕ) (x : Reg (registerWidth d r)) (j : Fin d) : Fin (2^r) :=
  littleAddress r (fun i => x (axisWire d r j i))

/-- Complete original `other_axis_wire_not_mem` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem other_axis_wire_not_mem (d r : ℕ) (j k : Fin d) (hkj : k ≠ j) (i : Fin r) :
    axisWire d r k i ∉ axisWires d r j := by
  intro h
  obtain ⟨l,hl⟩ := List.mem_ofFn.mp h
  have hp := @axis_wire_pair_injective d r (j,l) (k,i) hl
  exact hkj (congrArg Prod.fst hp).symm

/-- Complete original `spatial_increment_address` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem spatial_increment_address (d r : ℕ) (j k : Fin d) (x : Reg (registerWidth d r))
    (hclean : ∀ w ∈ workWires d r, x w=false) :
    (siteAddress d r (run (spatialIncrementWord d r j) x) k).val =
      if k=j then ((siteAddress d r x k).val+(x (testWire d r)).toNat) % 2^r
      else (siteAddress d r x k).val := by
  by_cases hk : k=j
  · subst k
    rw [ite_eq_left rfl]
    simpa only [axisWires, List.length_ofFn, List.map_ofFn, siteAddress, littleAddress,
      spatialIncrementWord, Function.comp_def] using
      increment_word_value (testWire d r) (axisWires d r j) (workWires d r) x
        (layout_work_sufficient d r j) (layout_wires_nodup d r j) hclean
  · rw [ite_eq_right hk]
    have hb (i : Fin r) : run (spatialIncrementWord d r j) x (axisWire d r k i)=x (axisWire d r k i) := by
      rw [spatialIncrementWord, increment_word_basis _ _ _ _ (layout_work_sufficient d r j)
        (layout_wires_nodup d r j) hclean]
      exact axis_increment_off _ _ _ _ (other_axis_wire_not_mem d r j k hk i)
    have he : (fun i => run (spatialIncrementWord d r j) x (axisWire d r k i)) =
        (fun i => x (axisWire d r k i)) := funext hb
    exact congrArg (fun b => (littleAddress r b).val) he

/-- Complete original `spatial_increment_off` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem spatial_increment_off (d r : ℕ) (j : Fin d) (x : Reg (registerWidth d r))
    (hclean : ∀ w ∈ workWires d r, x w=false) (v : Fin (registerWidth d r))
    (hv : v ∉ axisWires d r j) : run (spatialIncrementWord d r j) x v=x v := by
  rw [spatialIncrementWord, increment_word_basis _ _ _ _ (layout_work_sufficient d r j)
    (layout_wires_nodup d r j) hclean]
  exact axis_increment_off _ _ _ _ hv

/-- Complete original `spin_wire_not_axis` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem spin_wire_not_axis (d r : ℕ) (j : Fin d) : spinWire d r ∉ axisWires d r j := by
  intro h
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
  have hlt := axis_wire_lt_positions d r j i
  have he := congrArg Fin.val hi
  change (axisWire d r j i).val=d*r at he
  omega

/-- Complete original `test_wire_not_axis` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem test_wire_not_axis (d r : ℕ) (j : Fin d) : testWire d r ∉ axisWires d r j := by
  intro h
  exact (List.nodup_cons.mp (layout_wires_nodup d r j)).1 (List.mem_append_left _ h)

/-- Complete original `work_wire_not_axis` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem work_wire_not_axis (d r : ℕ) (j : Fin d) (i : Fin (r-2)) :
    workWire d r i ∉ axisWires d r j := by
  exact List.disjoint_right.mp (axis_work_disjoint d r j) (List.mem_ofFn.mpr ⟨i,rfl⟩)

/-- Construction for decoded Neighbor in the measurement gate semantics model. -/
def decodedNeighbor (d r : ℕ) (j : Fin d) :
    (Fin d → Fin (2^r)) ≃ (Fin d → Fin (2^r)) :=
  Equiv.piCongrRight (fun k => if k=j then finRotate (2^r) else Equiv.refl (Fin (2^r)))

/-- Complete original `decoded_neighbor_coordinate` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem decoded_neighbor_coordinate (d r : ℕ) (j k : Fin d) (s : Fin d → Fin (2^r)) :
    (decodedNeighbor d r j s k).val = if k=j then ((s k).val+1) % 2^r else (s k).val := by
  by_cases hk : k=j
  · change ((if k=j then finRotate (2^r) else Equiv.refl (Fin (2^r))) (s k)).val = _
    rw [ite_eq_left hk, ite_eq_left hk, finRotate_apply, Fin.val_add]
    change ((s k).val+1 % 2^r) % 2^r=((s k).val+1) % 2^r
    exact Nat.add_mod_mod _ _ _
  · simp [decodedNeighbor, Equiv.piCongrRight, hk]

/-- Complete original `spatial_increment_site` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem spatial_increment_site (d r : ℕ) (j : Fin d) (x : Reg (registerWidth d r))
    (hclean : ∀ w ∈ workWires d r, x w=false) :
    siteAddress d r (run (spatialIncrementWord d r j) x) =
      if x (testWire d r) then decodedNeighbor d r j (siteAddress d r x) else siteAddress d r x := by
  cases hc : x (testWire d r)
  · simp only [Bool.false_eq_true, ite_false]
    funext k
    apply Fin.ext
    rw [spatial_increment_address d r j k x hclean]
    simp [hc, Nat.mod_eq_of_lt (siteAddress d r x k).isLt]
  · simp only [ite_true]
    funext k
    apply Fin.ext
    rw [spatial_increment_address d r j k x hclean, decoded_neighbor_coordinate]
    simp only [hc, Bool.toNat_true]

/-- Abbreviation for Layout Data in the measurement gate semantics model. -/
abbrev LayoutData (d r : ℕ) := (Fin d → Fin (2^r)) × Bool × Bool × Reg (r-2)

/-- Construction for decode Layout in the measurement gate semantics model. -/
def decodeLayout (d r : ℕ) (x : Reg (registerWidth d r)) : LayoutData d r :=
  (siteAddress d r x, x (spinWire d r), x (testWire d r), fun i => x (workWire d r i))

/-- Complete original `layout_readout_injective` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem layout_readout_injective (d r : ℕ) (x y : Reg (registerWidth d r))
    (hs : siteAddress d r x=siteAddress d r y)
    (hspin : x (spinWire d r)=y (spinWire d r)) (htest : x (testWire d r)=y (testWire d r))
    (hw : ∀ i, x (workWire d r i)=y (workWire d r i)) : x=y := by
  funext v
  by_cases hp : v.val < d*r
  · let q : Fin (d*r) := ⟨v.val,hp⟩
    let p : Fin d × Fin r := finProdFinEquiv.symm q
    have hwire : axisWire d r p.1 p.2=v := by
      apply Fin.ext
      exact congrArg (fun z : Fin (d*r) => z.val) (finProdFinEquiv.apply_symm_apply q)
    have hb : (fun i => x (axisWire d r p.1 i))=(fun i => y (axisWire d r p.1 i)) :=
      little_address_injective r (congrFun hs p.1)
    simpa only [hwire] using congrFun hb p.2
  · by_cases hsp : v.val=d*r
    · have hv : v=spinWire d r := Fin.ext hsp
      simpa only [hv] using hspin
    · by_cases ht : v.val=d*r+1
      · have hv : v=testWire d r := Fin.ext ht
        simpa only [hv] using htest
      · have hvlt := v.isLt
        have hwi : v.val-(d*r+2) < r-2 := by unfold registerWidth at hvlt; omega
        let i : Fin (r-2) := ⟨v.val-(d*r+2),hwi⟩
        have hwire : workWire d r i=v := by
          apply Fin.ext
          change d*r+2+(v.val-(d*r+2))=v.val
          omega
        simpa only [hwire] using hw i

/-- Complete original `decode_layout_injective` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem decode_layout_injective (d r : ℕ) : Function.Injective (decodeLayout d r) := by
  intro x y h
  apply layout_readout_injective d r x y
  · exact congrArg Prod.fst h
  · exact congrArg (fun z => z.2.1) h
  · exact congrArg (fun z => z.2.2.1) h
  · intro i
    exact congrArg (fun z => z.2.2.2 i) h

/-- Complete original `layout_card_eq` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem layout_card_eq (d r : ℕ) : Fintype.card (Reg (registerWidth d r))=Fintype.card (LayoutData d r) := by
  simp only [LayoutData, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  simp only [registerWidth, Nat.pow_add, ← Nat.pow_mul]
  rw [Nat.mul_comm r d]
  ring

/-- Construction for layout Equiv in the measurement gate semantics model. -/
noncomputable def layoutEquiv (d r : ℕ) : Reg (registerWidth d r) ≃ LayoutData d r :=
  Equiv.ofBijective (decodeLayout d r) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨decode_layout_injective d r,layout_card_eq d r⟩)

/-- Complete original `layout_equiv_apply` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
@[simp] theorem layout_equiv_apply (d r : ℕ) (x : Reg (registerWidth d r)) :
    layoutEquiv d r x=decodeLayout d r x := rfl

/-- Complete original `spatial_increment_layout` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem spatial_increment_layout (d r : ℕ) (j : Fin d) (x : Reg (registerWidth d r))
    (hclean : ∀ w ∈ workWires d r, x w=false) :
    decodeLayout d r (run (spatialIncrementWord d r j) x) =
      (if x (testWire d r) then decodedNeighbor d r j (siteAddress d r x) else siteAddress d r x,
       x (spinWire d r), x (testWire d r), fun i => x (workWire d r i)) := by
  apply Prod.ext
  · exact spatial_increment_site d r j x hclean
  · apply Prod.ext
    · exact spatial_increment_off d r j x hclean _ (spin_wire_not_axis d r j)
    · apply Prod.ext
      · exact spatial_increment_off d r j x hclean _ (test_wire_not_axis d r j)
      · funext i
        exact spatial_increment_off d r j x hclean _ (work_wire_not_axis d r j i)

/-- Construction for encode Clean in the measurement gate semantics model. -/
noncomputable def encodeClean (d r : ℕ) (s : Fin d → Fin (2^r)) (spin test : Bool) :
    Reg (registerWidth d r) := (layoutEquiv d r).symm (s,spin,test,fun _ => false)

/-- Complete original `decode_encode_clean` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem decode_encode_clean (d r : ℕ) (s : Fin d → Fin (2^r)) (spin test : Bool) :
    decodeLayout d r (encodeClean d r s spin test)=(s,spin,test,fun _ => false) :=
  (layoutEquiv d r).apply_symm_apply _

/-- Complete original `encode_clean_site` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
@[simp] theorem encode_clean_site (d r : ℕ) (s : Fin d → Fin (2^r)) (spin test : Bool) :
    siteAddress d r (encodeClean d r s spin test)=s :=
  congrArg Prod.fst (decode_encode_clean d r s spin test)

/-- Complete original `encode_clean_spin` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
@[simp] theorem encode_clean_spin (d r : ℕ) (s : Fin d → Fin (2^r)) (spin test : Bool) :
    encodeClean d r s spin test (spinWire d r)=spin :=
  congrArg (fun z : LayoutData d r => z.2.1) (decode_encode_clean d r s spin test)

/-- Complete original `encode_clean_test` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
@[simp] theorem encode_clean_test (d r : ℕ) (s : Fin d → Fin (2^r)) (spin test : Bool) :
    encodeClean d r s spin test (testWire d r)=test :=
  congrArg (fun z : LayoutData d r => z.2.2.1) (decode_encode_clean d r s spin test)

/-- Complete original `encode_clean_work` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
@[simp] theorem encode_clean_work (d r : ℕ) (s : Fin d → Fin (2^r)) (spin test : Bool)
    (i : Fin (r-2)) : encodeClean d r s spin test (workWire d r i)=false :=
  congrArg (fun z : LayoutData d r => z.2.2.2 i) (decode_encode_clean d r s spin test)

/-- Complete original `encoded_work_clean` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem encoded_work_clean (d r : ℕ) (s : Fin d → Fin (2^r)) (spin test : Bool) :
    ∀ w ∈ workWires d r, encodeClean d r s spin test w=false := by
  intro w hw
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hw
  simpa only [hi] using encode_clean_work d r s spin test i

/-- Complete original `spatial_increment_encoded_basis` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem spatial_increment_encoded_basis (d r : ℕ) (j : Fin d)
    (s : Fin d → Fin (2^r)) (spin test : Bool) :
    run (spatialIncrementWord d r j) (encodeClean d r s spin test) =
      encodeClean d r (if test then decodedNeighbor d r j s else s) spin test := by
  apply decode_layout_injective d r
  rw [spatial_increment_layout d r j _ (encoded_work_clean d r s spin test), decode_encode_clean]
  simp only [encode_clean_site, encode_clean_spin, encode_clean_test, encode_clean_work]

/-- Complete original `spatial_reverse_encoded_basis` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem spatial_reverse_encoded_basis (d r : ℕ) (j : Fin d)
    (s : Fin d → Fin (2^r)) (spin test : Bool) :
    run (spatialIncrementWord d r j).reverse (encodeClean d r s spin test) =
      encodeClean d r (if test then (decodedNeighbor d r j).symm s else s) spin test := by
  let pre := if test then (decodedNeighbor d r j).symm s else s
  have hf : run (spatialIncrementWord d r j) (encodeClean d r pre spin test)=encodeClean d r s spin test := by
    rw [spatial_increment_encoded_basis]
    cases test <;> simp [pre]
  have hg : ∀ g ∈ spatialIncrementWord d r j, legal g :=
    increment_aux_legal [testWire d r] (axisWires d r j) (workWires d r) (layout_wires_nodup d r j)
  have hh := run_reverse_cancel (spatialIncrementWord d r j) hg (encodeClean d r pre spin test)
  rw [hf] at hh
  exact hh

open scoped BigOperators

/-- Complete original `native_spatial_increment_encoded_ket` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem native_spatial_increment_encoded_ket (d r : ℕ) (j : Fin d)
    (s : Fin d → Fin (2^r)) (spin test : Bool) :
    Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
      (reflectionCompile ((nativeWord (spatialIncrementWord d r j)).map nativeMatrix))
      (Ket (encodeClean d r s spin test)) =
      Ket (encodeClean d r (if test then decodedNeighbor d r j s else s) spin test) := by
  have hg : ∀ g ∈ spatialIncrementWord d r j, legal g :=
    increment_aux_legal [testWire d r] (axisWires d r j) (workWires d r) (layout_wires_nodup d r j)
  rw [native_word_compile, compile_bits_exact (spatialIncrementWord d r j) hg,
    spatial_increment_encoded_basis]

/-- Complete original `native_spatial_increment_encoded_superposition` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem native_spatial_increment_encoded_superposition {J : Type*} [Fintype J]
    (d r : ℕ) (j : Fin d) (s : J → Fin d → Fin (2^r)) (spin test : J → Bool) (φ : J → ℂ) :
    Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
      (reflectionCompile ((nativeWord (spatialIncrementWord d r j)).map nativeMatrix))
      (∑ i, φ i • Ket (encodeClean d r (s i) (spin i) (test i))) =
      ∑ i, φ i • Ket (encodeClean d r (if test i then decodedNeighbor d r j (s i) else s i) (spin i) (test i)) := by
  have hg : ∀ g ∈ spatialIncrementWord d r j, legal g :=
    increment_aux_legal [testWire d r] (axisWires d r j) (workWires d r) (layout_wires_nodup d r j)
  rw [native_word_superposition (spatialIncrementWord d r j) hg]
  simp_rw [spatial_increment_encoded_basis]

/-- Complete original `native_spatial_reverse_encoded_superposition` guarantee for `MeasurementGateSemantics`; all source hypotheses and output obligations are retained. -/
theorem native_spatial_reverse_encoded_superposition {J : Type*} [Fintype J]
    (d r : ℕ) (j : Fin d) (s : J → Fin d → Fin (2^r)) (spin test : J → Bool) (φ : J → ℂ) :
    Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
      (reflectionCompile ((nativeWord (spatialIncrementWord d r j).reverse).map nativeMatrix))
      (∑ i, φ i • Ket (encodeClean d r (s i) (spin i) (test i))) =
      ∑ i, φ i • Ket (encodeClean d r (if test i then (decodedNeighbor d r j).symm (s i) else s i) (spin i) (test i)) := by
  have hg : ∀ g ∈ (spatialIncrementWord d r j).reverse, legal g := by
    simpa only [spatialIncrementWord, incrementWord, List.mem_reverse] using
      increment_aux_legal [testWire d r] (axisWires d r j) (workWires d r) (layout_wires_nodup d r j)
  rw [native_word_superposition (spatialIncrementWord d r j).reverse hg]
  simp_rw [spatial_reverse_encoded_basis]

end Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit

#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.axis_value_injective
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.little_address_injective
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.little_endian_equiv_apply
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.axis_wire_val
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.axis_wire_lt_positions
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.axis_wire_pair_injective
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.axis_wires_nodup
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.work_wires_nodup
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.axis_work_disjoint
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.layout_wires_nodup
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.layout_work_sufficient
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.other_axis_wire_not_mem
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.spatial_increment_address
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.spatial_increment_off
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.spin_wire_not_axis
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.test_wire_not_axis
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.work_wire_not_axis
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.decoded_neighbor_coordinate
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.spatial_increment_site
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.layout_readout_injective
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.decode_layout_injective
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.layout_card_eq
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.layout_equiv_apply
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.spatial_increment_layout
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.decode_encode_clean
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.encode_clean_site
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.encode_clean_spin
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.encode_clean_test
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.encode_clean_work
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.encoded_work_clean
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.spatial_increment_encoded_basis
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.spatial_reverse_encoded_basis
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.native_spatial_increment_encoded_ket
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.native_spatial_increment_encoded_superposition
#print axioms Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit.native_spatial_reverse_encoded_superposition
