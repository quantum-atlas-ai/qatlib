/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs
import Lean
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

open Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp

open Turing

def modelParseUnaryField : List Bool → Option (ℕ × List Bool) := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs.parseUnaryField").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

def modelParseGateCodeFields : (tag : ℕ) → (bits : List Bool) → Option (FiniteGateCode × List Bool) := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs.parseGateCodeFields").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

def modelParseGateCodeListFuel : ℕ → List Bool → Option (List FiniteGateCode) := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs.parseGateCodeListFuel").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

def modelRunUntilHaltWithin : {k : ℕ} → (machine : Turing.TM0.Machine (Option Bool) (Fin (k + 1))) → ℕ → Turing.TM0.Cfg (Option Bool) (Fin (k + 1)) → Option (Turing.TM0.Cfg (Option Bool) (Fin (k + 1))) := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs.runUntilHaltWithin").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

def modelReadOutputUntilBlank : ℕ → Turing.ListBlank (Option Bool) → Option (List Bool) := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs.readOutputUntilBlank").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

def modelClockMachine : Turing.TM0.Machine (Option Bool) (Fin 1) := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs.uniformBqpClockMachine").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

def modelWordPrinterMachine : (bs : List Bool) → Turing.TM0.Machine (Option Bool) (Fin (3 * bs.length + 1)) := by
  run_tac do
    let moduleName :=
        ("_private.Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs").splitOn "."
    let root := Lean.Name.mkNum (moduleName.foldl (init := Lean.Name.anonymous) Lean.Name.mkStr) 0
    let name :=
        ("Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs.uniformBqpWordPrinterMachine").splitOn "."
    let constant := name.foldl (init := root) Lean.Name.mkStr
    Lean.Elab.Tactic.closeMainGoal Lean.Name.anonymous (Lean.mkConst constant)

noncomputable def modelDecode (bits : List Bool) : Option (ℕ × List FiniteGateCode) := do
  let (q, rest) ← modelParseUnaryField bits
  let gs ← modelParseGateCodeListFuel rest.length rest
  pure (q, gs)

theorem modelDecode_eq : modelDecode = decodeUniformBqpWord := rfl

@[simp] theorem modelParseUnaryField_nil :
    modelParseUnaryField [] = none := rfl

@[simp] theorem modelParseUnaryField_cons_false (rest : List Bool) :
    modelParseUnaryField (false :: rest) = some (0, rest) := rfl

@[simp] theorem modelParseUnaryField_cons_true (rest : List Bool) :
    modelParseUnaryField (true :: rest) =
      (modelParseUnaryField rest).map fun (k, tail) => (k + 1, tail) := rfl

theorem encodeUnaryField_succ (k : ℕ) :
    encodeUnaryField (k + 1) = true :: encodeUnaryField k := rfl

theorem encodeUnaryField_zero : encodeUnaryField 0 = [false] := rfl

theorem encodeUnaryField_length (k : ℕ) : (encodeUnaryField k).length = k + 1 := by
  simp [encodeUnaryField]

theorem modelParseUnaryField_encode (k : ℕ) (rest : List Bool) :
    modelParseUnaryField (encodeUnaryField k ++ rest) = some (k, rest) := by
  induction k with
  | zero => simp [encodeUnaryField_zero]
  | succ k ih => simp [encodeUnaryField_succ, ih]

theorem modelParseUnaryField_eq_some {bits : List Bool} {k : ℕ} {rest : List Bool}
    (h : modelParseUnaryField bits = some (k, rest)) :
    bits = encodeUnaryField k ++ rest := by
  induction bits generalizing k rest with
  | nil => simp [modelParseUnaryField_nil] at h
  | cons b bits ih =>
    cases b with
    | false =>
      simp [modelParseUnaryField_cons_false] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | true =>
      rw [modelParseUnaryField_cons_true] at h
      cases hm : modelParseUnaryField bits with
      | none => simp [hm] at h
      | some p =>
        obtain ⟨w, t⟩ := p
        simp [hm] at h
        obtain ⟨h1, h2⟩ := h
        subst h1
        subst h2
        have hi : bits = encodeUnaryField w ++ t := ih hm
        simp [encodeUnaryField_succ, hi, List.cons_append]

theorem modelParseUnaryField_eq_some_iff {bits : List Bool} {k : ℕ} {rest : List Bool} :
    modelParseUnaryField bits = some (k, rest) ↔ bits = encodeUnaryField k ++ rest :=
  ⟨modelParseUnaryField_eq_some, fun h => by
    rw [h]
    exact modelParseUnaryField_encode k rest⟩

def gateTag : FiniteGateCode → ℕ
  | .h _ => 0
  | .x _ => 1
  | .t _ => 2
  | .tdg _ => 3
  | .cx _ _ => 4

def gateWireFields : FiniteGateCode → List Bool
  | .h w => encodeUnaryField w
  | .x w => encodeUnaryField w
  | .t w => encodeUnaryField w
  | .tdg w => encodeUnaryField w
  | .cx c t => encodeUnaryField c ++ encodeUnaryField t

theorem encodeFiniteGateCode_eq (g : FiniteGateCode) :
    encodeFiniteGateCode g = encodeUnaryField (gateTag g) ++ gateWireFields g := by
  cases g <;> rfl

noncomputable def modelParseGateCodeFieldsBody : ℕ → List Bool → Option (FiniteGateCode × List Bool) :=
  fun tag bits =>
    if tag = 0 then
      (modelParseUnaryField bits).bind fun (w, rest) => some (FiniteGateCode.h w, rest)
    else if tag = 1 then
      (modelParseUnaryField bits).bind fun (w, rest) => some (FiniteGateCode.x w, rest)
    else if tag = 2 then
      (modelParseUnaryField bits).bind fun (w, rest) => some (FiniteGateCode.t w, rest)
    else if tag = 3 then
      (modelParseUnaryField bits).bind fun (w, rest) => some (FiniteGateCode.tdg w, rest)
    else if tag = 4 then
      (modelParseUnaryField bits).bind fun (c, rest) =>
        (modelParseUnaryField rest).bind fun (t, tail) => some (FiniteGateCode.cx c t, tail)
    else none

theorem modelParseGateCodeFields_eq_body :
    modelParseGateCodeFields = modelParseGateCodeFieldsBody := rfl

@[simp] theorem modelParseGateCodeFields_zero (bits : List Bool) :
    modelParseGateCodeFields 0 bits =
      (modelParseUnaryField bits).bind fun (w, rest) => some (FiniteGateCode.h w, rest) := rfl

@[simp] theorem modelParseGateCodeFields_one (bits : List Bool) :
    modelParseGateCodeFields 1 bits =
      (modelParseUnaryField bits).bind fun (w, rest) => some (FiniteGateCode.x w, rest) := rfl

@[simp] theorem modelParseGateCodeFields_two (bits : List Bool) :
    modelParseGateCodeFields 2 bits =
      (modelParseUnaryField bits).bind fun (w, rest) => some (FiniteGateCode.t w, rest) := rfl

@[simp] theorem modelParseGateCodeFields_three (bits : List Bool) :
    modelParseGateCodeFields 3 bits =
      (modelParseUnaryField bits).bind fun (w, rest) => some (FiniteGateCode.tdg w, rest) := rfl

@[simp] theorem modelParseGateCodeFields_four (bits : List Bool) :
    modelParseGateCodeFields 4 bits =
      (modelParseUnaryField bits).bind fun (c, rest) =>
        (modelParseUnaryField rest).bind fun (t, tail) => some (FiniteGateCode.cx c t, tail) := rfl

theorem modelParseGateCodeFields_encode (g : FiniteGateCode) (rest : List Bool) :
    modelParseGateCodeFields (gateTag g) (gateWireFields g ++ rest) = some (g, rest) := by
  cases g with
  | h w => simp [gateTag, gateWireFields, modelParseUnaryField_encode]
  | x w => simp [gateTag, gateWireFields, modelParseUnaryField_encode]
  | t w => simp [gateTag, gateWireFields, modelParseUnaryField_encode]
  | tdg w => simp [gateTag, gateWireFields, modelParseUnaryField_encode]
  | cx c t => simp [gateTag, gateWireFields, modelParseUnaryField_encode]

theorem modelParseGateCodeFields_eq_some {tag : ℕ} {bits : List Bool}
    {g : FiniteGateCode} {tail : List Bool}
    (h : modelParseGateCodeFields tag bits = some (g, tail)) :
    gateTag g = tag ∧ bits = gateWireFields g ++ tail := by
  by_cases h0 : tag = 0
  · subst h0
    rw [modelParseGateCodeFields_zero] at h
    cases hm : modelParseUnaryField bits with
    | none => simp [hm] at h
    | some p =>
      obtain ⟨w, t⟩ := p
      simp [hm] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      have hi := modelParseUnaryField_eq_some hm
      simp [gateTag, gateWireFields, hi]
  · by_cases h1 : tag = 1
    · subst h1
      rw [modelParseGateCodeFields_one] at h
      cases hm : modelParseUnaryField bits with
      | none => simp [hm] at h
      | some p =>
        obtain ⟨w, t⟩ := p
        simp [hm] at h
        obtain ⟨h1, h2⟩ := h
        subst h1
        subst h2
        have hi := modelParseUnaryField_eq_some hm
        simp [gateTag, gateWireFields, hi]
    · by_cases h2 : tag = 2
      · subst h2
        rw [modelParseGateCodeFields_two] at h
        cases hm : modelParseUnaryField bits with
        | none => simp [hm] at h
        | some p =>
          obtain ⟨w, t⟩ := p
          simp [hm] at h
          obtain ⟨h1, h2⟩ := h
          subst h1
          subst h2
          have hi := modelParseUnaryField_eq_some hm
          simp [gateTag, gateWireFields, hi]
      · by_cases h3 : tag = 3
        · subst h3
          rw [modelParseGateCodeFields_three] at h
          cases hm : modelParseUnaryField bits with
          | none => simp [hm] at h
          | some p =>
            obtain ⟨w, t⟩ := p
            simp [hm] at h
            obtain ⟨h1, h2⟩ := h
            subst h1
            subst h2
            have hi := modelParseUnaryField_eq_some hm
            simp [gateTag, gateWireFields, hi]
        · by_cases h4 : tag = 4
          · subst h4
            rw [modelParseGateCodeFields_four] at h
            cases hm : modelParseUnaryField bits with
            | none => simp [hm] at h
            | some p =>
              obtain ⟨c, t0⟩ := p
              simp [hm] at h
              cases hm2 : modelParseUnaryField t0 with
              | none => simp [hm2] at h
              | some p2 =>
                obtain ⟨w, t⟩ := p2
                simp [hm2] at h
                obtain ⟨h1, h2⟩ := h
                subst h1
                subst h2
                have hi := modelParseUnaryField_eq_some hm
                have hi2 := modelParseUnaryField_eq_some hm2
                simp [gateTag, gateWireFields, hi, hi2, List.append_assoc]
          · rw [modelParseGateCodeFields_eq_body] at h
            unfold modelParseGateCodeFieldsBody at h
            simp [h0, h1, h2, h3, h4] at h

@[simp] theorem modelParseGateCodeListFuel_zero_nil :
    modelParseGateCodeListFuel 0 [] = some [] := rfl

@[simp] theorem modelParseGateCodeListFuel_zero_cons (b : Bool) (rest : List Bool) :
    modelParseGateCodeListFuel 0 (b :: rest) = none := rfl

@[simp] theorem modelParseGateCodeListFuel_succ_nil (fuel : ℕ) :
    modelParseGateCodeListFuel (fuel + 1) [] = some [] := rfl

@[simp] theorem modelParseGateCodeListFuel_succ_cons (fuel : ℕ) (b : Bool) (bits : List Bool) :
    modelParseGateCodeListFuel (fuel + 1) (b :: bits) =
      (modelParseUnaryField (b :: bits)).bind fun (tag, rest) =>
        (modelParseGateCodeFields tag rest).bind fun (g, tail) =>
          (modelParseGateCodeListFuel fuel tail).bind fun gs => some (g :: gs) := rfl

theorem encodeFiniteGateCode_ne_nil (g : FiniteGateCode) : encodeFiniteGateCode g ≠ [] := by
  have h2 : (encodeFiniteGateCode g).length = gateTag g + 1 + (gateWireFields g).length := by
    rw [encodeFiniteGateCode_eq, List.length_append, encodeUnaryField_length]
  intro hc
  have hlen' : (encodeFiniteGateCode g).length = (0 : ℕ) := by
    rw [hc]
    rfl
  omega

theorem encodeFiniteGateCode_append_ne_nil (g : FiniteGateCode) (rest : List Bool) :
    encodeFiniteGateCode g ++ rest ≠ [] := by
  have h2 : (encodeFiniteGateCode g).length = gateTag g + 1 + (gateWireFields g).length := by
    rw [encodeFiniteGateCode_eq, List.length_append, encodeUnaryField_length]
  intro hc
  have hlen' : (encodeFiniteGateCode g ++ rest).length = (0 : ℕ) := by
    rw [hc]
    rfl
  rw [List.length_append] at hlen'
  omega

theorem length_le_flatMap_encodeFiniteGateCode (gs : List FiniteGateCode) :
    gs.length ≤ (gs.flatMap encodeFiniteGateCode).length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have h1 : 1 ≤ (encodeFiniteGateCode g).length := by
      cases g <;> simp [encodeFiniteGateCode, encodeUnaryField, List.length_append,
        List.length_replicate]
    have hlen0 : (g :: gs).length = gs.length + 1 := rfl
    simp only [List.flatMap_cons, List.length_append]
    omega

theorem modelParseGateCodeListFuel_succ_ne_nil (fuel : ℕ) (bits : List Bool)
    (hbits : bits ≠ []) :
    modelParseGateCodeListFuel (fuel + 1) bits =
      (modelParseUnaryField bits).bind fun (tag, rest) =>
        (modelParseGateCodeFields tag rest).bind fun (g, tail) =>
          (modelParseGateCodeListFuel fuel tail).bind fun gs => some (g :: gs) := by
  cases bits with
  | nil => exact absurd rfl hbits
  | cons b bits => rfl

theorem modelParseGateCodeListFuel_encode (fuel : ℕ) (gs : List FiniteGateCode)
    (hfuel : gs.length ≤ fuel) :
    modelParseGateCodeListFuel fuel (gs.flatMap encodeFiniteGateCode) = some gs := by
  induction gs generalizing fuel with
  | nil =>
    cases fuel with
    | zero => rfl
    | succ fuel => rfl
  | cons g gs ih =>
    cases fuel with
    | zero =>
      have hlen0 : (g :: gs).length = gs.length + 1 := rfl
      omega
    | succ fuel =>
      have hlen : gs.length ≤ fuel := by
        have hlen0 : (g :: gs).length = gs.length + 1 := rfl
        omega
      simp only [List.flatMap_cons]
      rw [modelParseGateCodeListFuel_succ_ne_nil fuel
        (encodeFiniteGateCode g ++ gs.flatMap encodeFiniteGateCode)
        (encodeFiniteGateCode_append_ne_nil g _)]
      have hp : modelParseUnaryField
          (encodeFiniteGateCode g ++ gs.flatMap encodeFiniteGateCode) =
          some (gateTag g, gateWireFields g ++ gs.flatMap encodeFiniteGateCode) := by
        rw [encodeFiniteGateCode_eq, List.append_assoc, modelParseUnaryField_encode]
      rw [hp]
      simp only [Option.bind_some]
      have hf2 : modelParseGateCodeFields (gateTag g)
          (gateWireFields g ++ gs.flatMap encodeFiniteGateCode) =
          some (g, gs.flatMap encodeFiniteGateCode) :=
        modelParseGateCodeFields_encode g _
      rw [hf2]
      simp only [Option.bind_some]
      rw [ih fuel hlen]
      simp

theorem modelParseGateCodeListFuel_eq_some {fuel : ℕ} {bits : List Bool}
    {gs : List FiniteGateCode} (h : modelParseGateCodeListFuel fuel bits = some gs) :
    bits = gs.flatMap encodeFiniteGateCode := by
  induction fuel generalizing bits gs with
  | zero =>
    cases bits with
    | nil =>
      simp at h
      subst h
      rfl
    | cons b bits => simp at h
  | succ fuel ih =>
    cases bits with
    | nil =>
      simp at h
      subst h
      rfl
    | cons b bits =>
      simp only [modelParseGateCodeListFuel_succ_cons] at h
      cases hm : modelParseUnaryField (b :: bits) with
      | none => simp [hm] at h
      | some p =>
        obtain ⟨tag, rest⟩ := p
        simp [hm] at h
        cases hm2 : modelParseGateCodeFields tag rest with
        | none => simp [hm2] at h
        | some p2 =>
          obtain ⟨g, tail⟩ := p2
          simp [hm2] at h
          cases hm3 : modelParseGateCodeListFuel fuel tail with
          | none => simp [hm3] at h
          | some gs' =>
            simp [hm3] at h
            subst h
            obtain ⟨htag, hrest⟩ := modelParseGateCodeFields_eq_some hm2
            have hp' := modelParseUnaryField_eq_some hm
            have htail := ih hm3
            rw [hp']
            subst hrest
            subst htail
            subst htag
            simp [List.flatMap_cons, encodeFiniteGateCode_eq, List.append_assoc]

theorem modelDecode_encode (q : ℕ) (gs : List FiniteGateCode) :
    modelDecode (encodeUniformBqpWord q gs) = some (q, gs) := by
  unfold modelDecode encodeUniformBqpWord
  have hp := modelParseUnaryField_encode q (gs.flatMap encodeFiniteGateCode)
  have hl := modelParseGateCodeListFuel_encode (gs.flatMap encodeFiniteGateCode).length gs
    (length_le_flatMap_encodeFiniteGateCode gs)
  rw [hp]
  show (modelParseGateCodeListFuel (gs.flatMap encodeFiniteGateCode).length
      (gs.flatMap encodeFiniteGateCode)).bind (fun a => some (q, a)) = some (q, gs)
  rw [hl]
  rfl

theorem modelDecode_eq_some {bits : List Bool} {q : ℕ} {gs : List FiniteGateCode}
    (h : modelDecode bits = some (q, gs)) : bits = encodeUniformBqpWord q gs := by
  unfold modelDecode at h
  cases hm : modelParseUnaryField bits with
  | none => simp [hm] at h
  | some p =>
    obtain ⟨q', rest⟩ := p
    simp [hm] at h
    cases hm2 : modelParseGateCodeListFuel rest.length rest with
    | none => simp [hm2] at h
    | some gs' =>
      simp [hm2] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      have hp' := modelParseUnaryField_eq_some hm
      have hgs' := modelParseGateCodeListFuel_eq_some hm2
      subst hp'
      subst hgs'
      rfl

theorem decode_encodeUniformBqpWord (q : ℕ) (gs : List FiniteGateCode) :
    decodeUniformBqpWord (encodeUniformBqpWord q gs) = some (q, gs) :=
  modelDecode_encode q gs

theorem decodeUniformBqpWord_eq_some {bits : List Bool} {q : ℕ} {gs : List FiniteGateCode}
    (h : decodeUniformBqpWord bits = some (q, gs)) : bits = encodeUniformBqpWord q gs :=
  modelDecode_eq_some h

theorem encodeUniformBqpWord_length_of_decode {bits : List Bool} {q : ℕ}
    {gs : List FiniteGateCode} (h : decodeUniformBqpWord bits = some (q, gs)) :
    (encodeUniformBqpWord q gs).length = bits.length := by
  rw [decodeUniformBqpWord_eq_some h]

@[simp] theorem modelRunUntilHaltWithin_zero {k : ℕ}
    (m : TM0.Machine (Option Bool) (Fin (k + 1))) (cfg : TM0.Cfg (Option Bool) (Fin (k + 1))) :
    modelRunUntilHaltWithin m 0 cfg =
      if TM0.step m cfg = none then some cfg else none := rfl

@[simp] theorem modelRunUntilHaltWithin_succ {k : ℕ}
    (m : TM0.Machine (Option Bool) (Fin (k + 1))) (fuel : ℕ)
    (cfg : TM0.Cfg (Option Bool) (Fin (k + 1))) :
    modelRunUntilHaltWithin m (fuel + 1) cfg =
      match TM0.step m cfg with
      | none => some cfg
      | some next => modelRunUntilHaltWithin m fuel next := rfl

@[simp] theorem modelReadOutputUntilBlank_zero (tape : ListBlank (Option Bool)) :
    modelReadOutputUntilBlank 0 tape = if tape.nth 0 = none then some [] else none := rfl

@[simp] theorem modelReadOutputUntilBlank_succ (fuel : ℕ) (tape : ListBlank (Option Bool)) :
    modelReadOutputUntilBlank (fuel + 1) tape =
      match tape.nth 0 with
      | none => some []
      | some bit => (modelReadOutputUntilBlank fuel tape.tail).map (bit :: ·) := rfl

def iterStep {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (cfg : TM0.Cfg (Option Bool) (Fin (k + 1))) :
    ℕ → Option (TM0.Cfg (Option Bool) (Fin (k + 1)))
  | 0 => some cfg
  | t + 1 => (iterStep m cfg t).bind (TM0.step m)

theorem iterStep_succ {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (cfg : TM0.Cfg (Option Bool) (Fin (k + 1))) (t : ℕ) :
    iterStep m cfg (t + 1) = (iterStep m cfg t).bind (TM0.step m) := rfl

theorem iterStep_one {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (cfg : TM0.Cfg (Option Bool) (Fin (k + 1))) :
    iterStep m cfg 1 = TM0.step m cfg := rfl

theorem iterStep_succ_of_step {k : ℕ} {m : TM0.Machine (Option Bool) (Fin (k + 1))}
    {cfg0 next : TM0.Cfg (Option Bool) (Fin (k + 1))} {t : ℕ}
    (hstep : TM0.step m cfg0 = some next) :
    iterStep m cfg0 (t + 1) = iterStep m next t := by
  induction t with
  | zero =>
    show (iterStep m cfg0 0).bind (TM0.step m) = iterStep m next 0
    simp [iterStep, hstep]
  | succ t ih =>
    show (iterStep m cfg0 (t + 1)).bind (TM0.step m) = iterStep m next (t + 1)
    rw [ih, iterStep_succ]

theorem exists_of_ne_none {α : Type} {o : Option α} (h : o ≠ none) : ∃ a, o = some a := by
  cases o with
  | none => exact absurd rfl h
  | some a => exact ⟨a, rfl⟩

theorem iterStep_eq_none_of_step_eq_none {k : ℕ} {m : TM0.Machine (Option Bool) (Fin (k + 1))}
    {cfg0 : TM0.Cfg (Option Bool) (Fin (k + 1))} {t : ℕ}
    (h : TM0.step m cfg0 = none) :
    iterStep m cfg0 (t + 1) = none := by
  induction t with
  | zero => simp [iterStep, h]
  | succ t ih => rw [iterStep_succ, ih]; simp

theorem modelRunUntilHaltWithin_eq_some_iff {k : ℕ}
    {m : TM0.Machine (Option Bool) (Fin (k + 1))} {fuel : ℕ}
    {cfg0 cfgf : TM0.Cfg (Option Bool) (Fin (k + 1))} :
    modelRunUntilHaltWithin m fuel cfg0 = some cfgf ↔
      ∃ t ≤ fuel, iterStep m cfg0 t = some cfgf ∧ TM0.step m cfgf = none := by
  induction fuel generalizing cfg0 with
  | zero =>
    constructor
    · intro h
      by_cases hstop : TM0.step m cfg0 = none
      · simp [hstop] at h
        subst h
        exact ⟨0, by omega, rfl, hstop⟩
      · simp [hstop] at h
    · intro h
      obtain ⟨t, ht, hcfg, hstop⟩ := h
      have ht0 : t = 0 := by omega
      subst ht0
      have hcfg2 : some cfg0 = some cfgf := hcfg
      have hp : cfg0 = cfgf := Option.some.inj hcfg2
      subst hp
      simp [hstop]
  | succ fuel ih =>
    constructor
    · intro h
      by_cases hstop : TM0.step m cfg0 = none
      · simp [hstop] at h
        subst h
        exact ⟨0, by omega, rfl, hstop⟩
      · obtain ⟨next, hnext⟩ := exists_of_ne_none hstop
        simp [hnext] at h
        obtain ⟨t, ht, hcfg, hstop'⟩ := ih.mp h
        refine ⟨t + 1, by omega, ?_, hstop'⟩
        rw [iterStep_succ_of_step hnext]
        exact hcfg
    · intro h
      obtain ⟨t, ht, hcfg, hstop⟩ := h
      cases t with
      | zero =>
        have hcfg2 : some cfg0 = some cfgf := hcfg
        have hp : cfg0 = cfgf := Option.some.inj hcfg2
        subst hp
        simp [hstop]
      | succ t =>
        by_cases hstop0 : TM0.step m cfg0 = none
        · rw [iterStep_eq_none_of_step_eq_none hstop0] at hcfg
          simp at hcfg
        · obtain ⟨next, hnext⟩ := exists_of_ne_none hstop0
          have hcfg' : iterStep m next t = some cfgf := by
            rw [← iterStep_succ_of_step hnext]
            exact hcfg
          have hle : t ≤ fuel := by omega
          simp [hnext]
          exact ih.mpr ⟨t, hle, hcfg', hstop⟩

theorem modelReadOutputUntilBlank_eq_some_iff {B : ℕ} {tape : ListBlank (Option Bool)}
    {w : List Bool} :
    modelReadOutputUntilBlank B tape = some w ↔
      w.length ≤ B ∧ tape.nth w.length = none ∧
        ∀ i : ℕ, i < w.length → tape.nth i = some (w.getD i false) := by
  induction B generalizing tape w with
  | zero =>
    rw [modelReadOutputUntilBlank_zero]
    constructor
    · intro h
      by_cases hblank : tape.nth 0 = none
      · rw [if_pos hblank] at h
        have hw : w = [] := Option.some.inj h.symm
        subst hw
        refine ⟨by simp, ?_, ?_⟩
        · simpa using! hblank
        · intro i hi
          simp at hi
      · rw [if_neg hblank] at h
        simp at h
    · intro h
      obtain ⟨hlen, hblank, hcells⟩ := h
      have hw : w = [] := by
        cases w with
        | nil => rfl
        | cons b w' =>
          exfalso
          have : (b :: w').length = w'.length + 1 := rfl
          omega
      subst hw
      have hblank0 : tape.nth 0 = none := by simpa using! hblank
      rw [if_pos hblank0]
  | succ B ih =>
    rw [modelReadOutputUntilBlank_succ]
    constructor
    · intro h
      by_cases hblank : tape.nth 0 = none
      · rw [hblank] at h
        simp at h
        subst h
        refine ⟨by simp, ?_, ?_⟩
        · simpa using! hblank
        · intro i hi
          simp at hi
      · obtain ⟨bit, hbit⟩ := exists_of_ne_none hblank
        rw [hbit] at h
        simp at h
        cases hm : modelReadOutputUntilBlank B tape.tail with
        | none => rw [hm] at h; simp at h
        | some w' =>
          rw [hm] at h
          obtain ⟨a, ha1, ha2⟩ := h
          have haw : a = w' := Option.some.inj ha1.symm
          subst a
          have hw : w = bit :: w' := ha2.symm
          subst hw
          obtain ⟨hlen, hblank', hcells⟩ := ih.mp hm
          have hlen1 : (bit :: w').length = w'.length + 1 := rfl
          refine ⟨by omega, ?_, ?_⟩
          · rw [hlen1, ListBlank.nth_succ]
            simpa [Nat.add_comm] using! hblank'
          · intro i hi
            cases i with
            | zero => simpa using! hbit
            | succ i =>
              have hi' : i < w'.length := by omega
              rw [ListBlank.nth_succ]
              simpa [Nat.add_comm] using! hcells i hi'
    · intro h
      obtain ⟨hlen, hblank, hcells⟩ := h
      by_cases hblank0 : tape.nth 0 = none
      · have hw : w = [] := by
          cases w with
          | nil => rfl
          | cons b w' =>
            exfalso
            have := hcells 0 (by simp)
            rw [hblank0] at this
            simp at this
        subst hw
        rw [hblank0]
      · obtain ⟨bit, hbit⟩ := exists_of_ne_none hblank0
        have hcons : ∃ w', w = bit :: w' := by
          cases w with
          | nil =>
            exfalso
            have hblank' : tape.nth 0 = none := by simpa using! hblank
            exact hblank0 hblank'
          | cons b w' =>
            have hb : b = bit := by
              have h0 := hcells 0 (by simp)
              simp [hbit] at h0
              exact h0.symm
            subst hb
            exact ⟨w', rfl⟩
        obtain ⟨w', rfl⟩ := hcons
        have hlen1 : (bit :: w').length = w'.length + 1 := rfl
        have hlen' : w'.length ≤ B := by omega
        have hblank' : tape.tail.nth w'.length = none := by
          rw [hlen1, ListBlank.nth_succ] at hblank
          simpa [Nat.add_comm] using! hblank
        have hcells' : ∀ i < w'.length, tape.tail.nth i = some (w'.getD i false) := by
          intro i hi
          have hi' : i + 1 < (bit :: w').length := by omega
          have := hcells (i + 1) hi'
          rw [ListBlank.nth_succ] at this
          simpa [Nat.add_comm] using! this
        rw [hbit, ih.mpr ⟨hlen', hblank', hcells'⟩]
        rfl

noncomputable def modelGeneratedAt (g : UniformBqpGenerator) (n : ℕ) :
    Option (ℕ × List FiniteGateCode) :=
  (modelRunUntilHaltWithin g.machine (uniformBqpTimeBound g n)
    (TM0.init (uniformBqpUnaryInput n))).bind fun cfg =>
      (modelReadOutputUntilBlank (n + uniformBqpTimeBound g n + 1) cfg.Tape.right₀).bind
        decodeUniformBqpWord

theorem modelGeneratedAt_eq : modelGeneratedAt = uniformBqpGeneratedAt := rfl

theorem modelGeneratedAt_of_run {g : UniformBqpGenerator} {n : ℕ} {t : ℕ}
    {cfg : TM0.Cfg (Option Bool) (Fin (g.controlBound + 1))}
    (ht : t ≤ uniformBqpTimeBound g n)
    (hcfg : iterStep g.machine (TM0.init (uniformBqpUnaryInput n)) t = some cfg)
    (hstop : TM0.step g.machine cfg = none)
    (q : ℕ) (gs : List FiniteGateCode)
    (hread : modelReadOutputUntilBlank (n + uniformBqpTimeBound g n + 1) cfg.Tape.right₀
      = some (encodeUniformBqpWord q gs)) :
    modelGeneratedAt g n = some (q, gs) := by
  unfold modelGeneratedAt
  rw [modelRunUntilHaltWithin_eq_some_iff.mpr ⟨t, ht, hcfg, hstop⟩]
  simp only [Option.bind_some]
  rw [hread]
  exact decode_encodeUniformBqpWord q gs

theorem generatorValid_implies_generatorWellformed {g : UniformBqpGenerator}
    (h : uniformBqpGeneratorValid g) : generatorWellformed g := by
  intro n q gs hg
  obtain ⟨q', gs', hg', _, hlegal, _⟩ := h n
  have heq : (q', gs') = (q, gs) := Option.some.inj (hg'.symm.trans hg)
  obtain ⟨rfl, rfl⟩ := heq
  exact hlegal

theorem generatorValid_implies_generatorClocked {g : UniformBqpGenerator}
    (h : uniformBqpGeneratorValid g) : generatorClocked g := by
  refine ⟨g.timeCoefficient, g.timeDegree, fun n => ?_⟩
  obtain ⟨q, gs, _, ⟨t, ht, hhalts⟩, _⟩ := h n
  exact ⟨t, ht, hhalts⟩

theorem generatorClocked_implies_generatorHaltsEffectively {g : UniformBqpGenerator}
    (h : generatorClocked g) : generatorHaltsEffectively g := by
  intro n
  obtain ⟨c, d, h⟩ := h
  obtain ⟨t, _, hhalts⟩ := h n
  exact ⟨t, hhalts⟩

theorem diverging_step_ne_none :
    ∀ cfg : TM0.Cfg (Option Bool) (Fin 1),
      TM0.step uniformBqpDivergingGenerator.machine cfg ≠ none := by
  intro cfg
  cases cfg with
  | mk q T => simp [uniformBqpDivergingGenerator, TM0.step]

theorem diverging_run_none (fuel : ℕ) :
    ∀ cfg : TM0.Cfg (Option Bool) (Fin 1),
      modelRunUntilHaltWithin uniformBqpDivergingGenerator.machine fuel cfg = none := by
  induction fuel with
  | zero =>
    intro cfg
    simp [diverging_step_ne_none cfg]
  | succ fuel ih =>
    intro cfg
    cases hs : TM0.step uniformBqpDivergingGenerator.machine cfg with
    | none => exact absurd hs (diverging_step_ne_none cfg)
    | some next =>
      rw [modelRunUntilHaltWithin_succ, hs]
      exact ih next

theorem diverging_modelGeneratedAt_none (n : ℕ) :
    modelGeneratedAt uniformBqpDivergingGenerator n = none := by
  unfold modelGeneratedAt
  rw [diverging_run_none]
  rfl

theorem diverging_generatedAt_none (n : ℕ) :
    uniformBqpGeneratedAt uniformBqpDivergingGenerator n = none :=
  diverging_modelGeneratedAt_none n

theorem diverging_generatedTotal_zero :
    uniformBqpGeneratedTotal uniformBqpDivergingGenerator 0 = (0, []) := by
  simp [uniformBqpGeneratedTotal, diverging_generatedAt_none]

theorem generatorValid_native_to_standard {g : UniformBqpGenerator}
    (h : uniformBqpGeneratorValid g) :
    ∃ W : StandardWordFamily, nativeRealizes g W ∧ standardFamilyLegal W ∧
      ∃ cW dW cS dS : ℕ, standardFamilyBounded cW dW cS dS W := by
  refine ⟨uniformBqpGeneratedTotal g, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨q, gs, hg, _⟩ := h n
    have htot : uniformBqpGeneratedTotal g n = (q, gs) := by
      simp [uniformBqpGeneratedTotal, hg]
    rw [htot]
    exact hg
  · intro n
    obtain ⟨q, gs, hg, _, hlegal, _⟩ := h n
    have htot : uniformBqpGeneratedTotal g n = (q, gs) := by
      simp [uniformBqpGeneratedTotal, hg]
    rw [htot]
    exact hlegal
  · refine ⟨g.wordCoefficient, g.wordDegree, g.spaceCoefficient, g.spaceDegree, ?_⟩
    intro n
    obtain ⟨q, gs, hg, _, _, hlen, hq, _⟩ := h n
    have htot : uniformBqpGeneratedTotal g n = (q, gs) := by
      simp [uniformBqpGeneratedTotal, hg]
    rw [htot]
    exact ⟨hlen, hq⟩

theorem generatorValid_per_length_ledgers {g : UniformBqpGenerator}
    (h : uniformBqpGeneratorValid g) :
    ∀ n : ℕ, ∃ (q : ℕ) (gs : List FiniteGateCode),
      uniformBqpGeneratedAt g n = some (q, gs) ∧
        finiteWordLegal q gs = true ∧
        QueryCount (finiteCodeCircuit q gs) = 0 ∧
        GateCount (finiteCodeCircuit q gs) = gs.length ∧
        gs.length ≤ uniformBqpWordBound g n ∧
        q ≤ uniformBqpSpaceBound g n ∧
        (encodeUniformBqpWord q gs).length ≤ n + uniformBqpTimeBound g n ∧
        ∀ x : Reg q,
          Normalized (uniformBqpRun q gs x) ∧
            0 ≤ uniformBqpAcceptProb q gs x ∧ uniformBqpAcceptProb q gs x ≤ 1 := by
  intro n
  obtain ⟨q, gs, hg, _, hlegal, hlen, hq, henc⟩ := h n
  refine ⟨q, gs, hg, hlegal, ?_, ?_, hlen, hq, henc, ?_⟩
  · exact (finiteCodeCircuit_counts q gs).1
  · exact (finiteCodeCircuit_counts q gs).2
  · intro x
    have hu := ((finite_gate_description_rejection_unitarity_and_counts q gs).2 hlegal).1
    have hn : Normalized (uniformBqpRun q gs x) := by
      unfold uniformBqpRun
      exact normalized_run (1 : Matrix (Reg q) (Reg q) ℂ)
        (Matrix.unitaryGroup (Reg q) ℂ).one_mem _ hu (normalized_ket x)
    exact ⟨hn, measureProb_nonneg _ _, measureProb_le_one hn _⟩

theorem inv_sqrt2_eq : ((Real.sqrt 2 : ℂ))⁻¹ = (Real.sqrt 2 : ℂ) / 2 := by
  have h : ((Real.sqrt 2 : ℂ)) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← pow_two, sqrt2_sq]
  have hne : ((Real.sqrt 2 : ℂ)) ≠ 0 := by
    intro hc
    have h0 : ((Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ)) = 0 := by rw [hc, mul_zero]
    rw [h] at h0
    norm_num at h0
  rw [eq_div_iff (by norm_num : (2:ℂ) ≠ 0)]
  calc ((Real.sqrt 2 : ℂ))⁻¹ * 2
      = ((Real.sqrt 2 : ℂ))⁻¹ * (((Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ))) := by rw [h]
    _ = (((Real.sqrt 2 : ℂ))⁻¹ * (Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ)) := by ring
    _ = (1 : ℂ) * ((Real.sqrt 2 : ℂ)) := by rw [inv_mul_cancel₀ hne]
    _ = (Real.sqrt 2 : ℂ) := by rw [one_mul]

theorem finiteDigitVal_zero : finiteDigitVal ⟨0, 0, false, 0⟩ = 0 := by
  simp [finiteDigitVal]

theorem finiteDigitVal_one : finiteDigitVal ⟨1, 0, false, 0⟩ = 1 := by
  simp [finiteDigitVal]

theorem finiteDigitVal_neg_one : finiteDigitVal ⟨-1, 0, false, 0⟩ = -1 := by
  simp [finiteDigitVal]

theorem finiteDigitVal_inv_sqrt2 : finiteDigitVal ⟨1, 0, true, 1⟩ = ((Real.sqrt 2 : ℂ))⁻¹ := by
  simp [finiteDigitVal, inv_sqrt2_eq]

theorem finiteDigitVal_neg_inv_sqrt2 :
    finiteDigitVal ⟨-1, 0, true, 1⟩ = -((Real.sqrt 2 : ℂ))⁻¹ := by
  simp [finiteDigitVal, inv_sqrt2_eq]
  ring

theorem finiteDigitVal_phase_quarter :
    finiteDigitVal ⟨1, 1, true, 1⟩ = Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) := by
  rw [Complex.exp_ofReal_mul_I, Real.cos_pi_div_four, Real.sin_pi_div_four]
  simp [finiteDigitVal]
  ring

theorem finiteDigitVal_phase_quarter_neg :
    finiteDigitVal ⟨1, -1, true, 1⟩ =
      Complex.exp (Complex.ofReal (-(Real.pi / 4)) * Complex.I) := by
  rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  simp [finiteDigitVal]
  ring

theorem permMatrix_entry_finiteDigit {I : Type} [Fintype I] [DecidableEq I]
    (σ : I → I) (i j : I) :
    (∃ r : FiniteDigitAmplitude, finiteDigitVal r = permMatrix σ i j) := by
  rw [permMatrix]
  simp only [Matrix.of_apply]
  split_ifs with hif
  · exact ⟨⟨1, 0, false, 0⟩, finiteDigitVal_one⟩
  · exact ⟨⟨0, 0, false, 0⟩, finiteDigitVal_zero⟩

theorem hadamard_apply_finiteDigit (a b : Bool) :
    ∃ r : FiniteDigitAmplitude, finiteDigitVal r = Hadamard a b := by
  rcases a with - | - <;> rcases b with - | -
  · refine ⟨⟨1, 0, true, 1⟩, by simp [Hadamard, finiteDigitVal, inv_sqrt2_eq]⟩
  · refine ⟨⟨1, 0, true, 1⟩, by simp [Hadamard, finiteDigitVal, inv_sqrt2_eq]⟩
  · refine ⟨⟨1, 0, true, 1⟩, by simp [Hadamard, finiteDigitVal, inv_sqrt2_eq]⟩
  · refine ⟨⟨-1, 0, true, 1⟩, by simp [Hadamard, finiteDigitVal, inv_sqrt2_eq, neg_div]⟩

theorem tGate_apply_finiteDigit (a b : Bool) :
    ∃ r : FiniteDigitAmplitude, finiteDigitVal r = tGate a b := by
  by_cases hab : a = b
  · subst hab
    cases a with
    | false =>
      refine ⟨⟨1, 0, false, 0⟩, ?_⟩
      simp [tGate, Rz, finiteDigitVal]
    | true =>
      refine ⟨⟨1, 1, true, 1⟩, ?_⟩
      simp [tGate, Rz, finiteDigitVal_phase_quarter]
  · refine ⟨⟨0, 0, false, 0⟩, ?_⟩
    simp [tGate, Rz, finiteDigitVal, hab]

theorem tGateAdj_apply_finiteDigit (a b : Bool) :
    ∃ r : FiniteDigitAmplitude, finiteDigitVal r = tGateAdj a b := by
  by_cases hab : a = b
  · subst hab
    cases a with
    | false =>
      refine ⟨⟨1, 0, false, 0⟩, ?_⟩
      simp [tGateAdj, Rz, finiteDigitVal]
    | true =>
      refine ⟨⟨1, -1, true, 1⟩, ?_⟩
      simp [tGateAdj, Rz, finiteDigitVal_phase_quarter_neg]
  · refine ⟨⟨0, 0, false, 0⟩, ?_⟩
    simp [tGateAdj, Rz, finiteDigitVal, hab]

theorem finiteCodeMatrix_entry_finiteDigit (q : ℕ) (g : FiniteGateCode)
    (hg : finiteCodeLegal q g = true) (i j : Reg q) :
    ∃ r : FiniteDigitAmplitude, finiteDigitVal r = finiteCodeMatrix q g i j := by
  cases g with
  | h w =>
    have hw : w < q := by simpa [finiteCodeLegal] using! hg
    simp only [finiteCodeMatrix, dif_pos hw]
    rw [wireGate_apply]
    split_ifs with hsupp
    · exact hadamard_apply_finiteDigit (i ⟨w, hw⟩) (j ⟨w, hw⟩)
    · exact ⟨⟨0, 0, false, 0⟩, finiteDigitVal_zero⟩
  | x w =>
    have hw : w < q := by simpa [finiteCodeLegal] using! hg
    simp only [finiteCodeMatrix, dif_pos hw]
    rw [wireGate_apply]
    split_ifs with hsupp
    · simpa [PauliX] using! permMatrix_entry_finiteDigit Bool.not (i ⟨w, hw⟩) (j ⟨w, hw⟩)
    · exact ⟨⟨0, 0, false, 0⟩, finiteDigitVal_zero⟩
  | t w =>
    have hw : w < q := by simpa [finiteCodeLegal] using! hg
    simp only [finiteCodeMatrix, dif_pos hw]
    rw [wireGate_apply]
    split_ifs with hsupp
    · exact tGate_apply_finiteDigit (i ⟨w, hw⟩) (j ⟨w, hw⟩)
    · exact ⟨⟨0, 0, false, 0⟩, finiteDigitVal_zero⟩
  | tdg w =>
    have hw : w < q := by simpa [finiteCodeLegal] using! hg
    simp only [finiteCodeMatrix, dif_pos hw]
    rw [wireGate_apply]
    split_ifs with hsupp
    · exact tGateAdj_apply_finiteDigit (i ⟨w, hw⟩) (j ⟨w, hw⟩)
    · exact ⟨⟨0, 0, false, 0⟩, finiteDigitVal_zero⟩
  | cx c t =>
    have hw : c < q ∧ t < q ∧ c ≠ t := by simpa [finiteCodeLegal] using! hg
    have hct : (⟨c, hw.1⟩ : Fin q) ≠ ⟨t, hw.2.1⟩ := fun hh => hw.2.2 (congrArg Fin.val hh)
    simp only [finiteCodeMatrix, dif_pos hw]
    simpa [cnotGate] using! permMatrix_entry_finiteDigit
      (fun x : Reg q => Function.update x ⟨t, hw.2.1⟩ (x ⟨t, hw.2.1⟩ ^^ x ⟨c, hw.1⟩)) i j

theorem finiteDigitBackendPremise_of_legal {q : ℕ} {gs : List FiniteGateCode}
    (h : finiteWordLegal q gs = true) : finiteDigitBackendPremise (q, gs) := by
  refine ⟨h, ?_⟩
  intro g hg i j
  exact finiteCodeMatrix_entry_finiteDigit q g ((List.all_eq_true.mp h) g hg) i j

theorem div_sub_eq_sub_div {x y N : ℝ} (h : N ≠ 0) : x / N - y = (x - y * N) / N := by
  have key : y * N / N = y := by
    rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ h, mul_one]
  rw [sub_div, key]

theorem hasDyadicDigit_of_complex (lam : ℕ) (z : ℂ) : HasDyadicDigit lam z := by
  set N : ℝ := ((2 ^ lam : ℕ) : ℝ)
  have hNpos : 0 < N := by
    show 0 < ((2 ^ lam : ℕ) : ℝ)
    positivity
  have hN2 : N = (2 : ℝ) ^ (lam : ℤ) := by
    show ((2 ^ lam : ℕ) : ℝ) = _
    push_cast
    exact (zpow_ofNat (2 : ℝ) lam).symm
  have hz : (2 : ℝ) ^ (-(lam : ℤ)) = 1 / N := by
    rw [zpow_neg, hN2, one_div]
  refine ⟨⟨Int.ceil (z.re * N), Int.ceil (z.im * N)⟩, ?_, ?_⟩
  · have h3 : |(Int.ceil (z.re * N) : ℝ) - z.re * N| < 1 := by
      have h1 : z.re * N ≤ (Int.ceil (z.re * N) : ℝ) := Int.le_ceil _
      have h2 : (Int.ceil (z.re * N) : ℝ) < z.re * N + 1 := Int.ceil_lt_add_one _
      rw [abs_lt]
      constructor <;> linarith
    have h4 : (Int.ceil (z.re * N) : ℝ) / N - z.re =
        ((Int.ceil (z.re * N) : ℝ) - z.re * N) / N :=
      div_sub_eq_sub_div (ne_of_gt hNpos)
    rw [h4, abs_div, abs_of_pos hNpos, hz]
    rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
    exact (mul_le_mul_of_nonneg_right (le_of_lt h3)
      (inv_nonneg.mpr (le_of_lt hNpos))).trans (by simp)
  · have h3 : |(Int.ceil (z.im * N) : ℝ) - z.im * N| < 1 := by
      have h1 : z.im * N ≤ (Int.ceil (z.im * N) : ℝ) := Int.le_ceil _
      have h2 : (Int.ceil (z.im * N) : ℝ) < z.im * N + 1 := Int.ceil_lt_add_one _
      rw [abs_lt]
      constructor <;> linarith
    have h4 : (Int.ceil (z.im * N) : ℝ) / N - z.im =
        ((Int.ceil (z.im * N) : ℝ) - z.im * N) / N :=
      div_sub_eq_sub_div (ne_of_gt hNpos)
    rw [h4, abs_div, abs_of_pos hNpos, hz]
    rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
    exact (mul_le_mul_of_nonneg_right (le_of_lt h3)
      (inv_nonneg.mpr (le_of_lt hNpos))).trans (by simp)

theorem dyadicBackendPremise_of_legal {q : ℕ} {gs : List FiniteGateCode}
    (h : finiteWordLegal q gs = true) (lam : ℕ) : dyadicBackendPremise lam (q, gs) := by
  refine ⟨h, ?_⟩
  intro g hg i j
  exact hasDyadicDigit_of_complex lam (finiteCodeMatrix q g i j)

theorem tape_ext {Γ : Type} [Inhabited Γ] {T₁ T₂ : Turing.Tape Γ}
    (h : ∀ i : ℤ, T₁.nth i = T₂.nth i) : T₁ = T₂ := by
  obtain ⟨a₁, l₁, r₁⟩ := T₁
  obtain ⟨a₂, l₂, r₂⟩ := T₂
  have ha : a₁ = a₂ := by simpa using! h 0
  have hl : l₁ = l₂ := by
    refine Turing.ListBlank.ext (fun n => ?_)
    exact h (Int.negSucc n)
  have hr : r₁ = r₂ := by
    refine Turing.ListBlank.ext (fun n => ?_)
    exact h (n + 1 : ℕ)
  rw [ha, hl, hr]

theorem init_nth {Γ : Type} [Inhabited Γ] (l : List Γ) (x : ℤ) :
    (Turing.Tape.mk₁ l).nth x = if x < 0 then default else l.getI x.toNat := by
  cases x with
  | ofNat n =>
    have h := Turing.Tape.mk'_nth_nat (Γ := Γ)
      (Turing.ListBlank.mk ([] : List Γ)) (Turing.ListBlank.mk l) n
    have h2 : (Turing.Tape.mk₁ l).nth (Int.ofNat n)
        = (Turing.Tape.mk' (Turing.ListBlank.mk ([] : List Γ))
          (Turing.ListBlank.mk l)).nth (n : ℤ) := rfl
    rw [h2, h, Turing.ListBlank.nth_mk]
    simp [Int.toNat_natCast]
  | negSucc n =>
    show (Turing.Tape.mk' (Turing.ListBlank.mk ([] : List Γ))
      (Turing.ListBlank.mk l)).nth (Int.negSucc n) = _
    have hlt : (Int.negSucc n < 0) := Int.negSucc_lt_zero n
    simp [hlt]
    rfl

theorem tm0_step_none_iff {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (cfg : TM0.Cfg (Option Bool) (Fin (k + 1))) :
    TM0.step m cfg = none ↔ m cfg.q cfg.Tape.head = none := by
  obtain ⟨q, T⟩ := cfg
  simp [TM0.step]

theorem tm0_step_eq_some' {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (cfg : TM0.Cfg (Option Bool) (Fin (k + 1))) (q' : Fin (k + 1))
    (st : TM0.Stmt (Option Bool)) (h : m cfg.q cfg.Tape.head = some (q', st)) :
    TM0.step m cfg = some ⟨q', match st with
      | TM0.Stmt.move d => cfg.Tape.move d
      | TM0.Stmt.write b => cfg.Tape.write b⟩ := by
  obtain ⟨q, T⟩ := cfg
  cases st with
  | move d => simp [TM0.step, h]
  | write b => simp [TM0.step, h]

theorem iterStep_add {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1))) :
    ∀ (a b : ℕ) (cfg : TM0.Cfg (Option Bool) (Fin (k + 1))),
      iterStep m cfg (a + b) = (iterStep m cfg a).bind (fun cfg' => iterStep m cfg' b) := by
  intro a b
  induction b with
  | zero =>
    intro cfg
    simp [iterStep]
  | succ b ih =>
    intro cfg
    show (iterStep m cfg (a + b)).bind (TM0.step m) =
      (iterStep m cfg a).bind (fun cfg' => iterStep m cfg' (b + 1))
    rw [ih]
    show ((iterStep m cfg a).bind (fun cfg' => iterStep m cfg' b)).bind (TM0.step m) =
      (iterStep m cfg a).bind (fun cfg' => (iterStep m cfg' b).bind (TM0.step m))
    exact Option.bind_assoc _ _ _

theorem iterStep_add1 {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (a : ℕ) (cfg : TM0.Cfg (Option Bool) (Fin (k + 1))) :
    iterStep m cfg (a + 1) = (iterStep m cfg a).bind (TM0.step m) := by
  rw [iterStep_add]
  rfl

theorem iterStep_init_eq_bitMachineAfter {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (l : List (Option Bool)) (t : ℕ) :
    iterStep m (TM0.init l) t = BitMachineAfter m l t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iterStep_succ, ih]; rfl

theorem modelReadOutputUntilBlank_mono {B₁ B₂ : ℕ} (hB : B₁ ≤ B₂)
    (tape : Turing.ListBlank (Option Bool)) (w : List Bool)
    (h : modelReadOutputUntilBlank B₁ tape = some w) :
    modelReadOutputUntilBlank B₂ tape = some w := by
  obtain ⟨hlen, hblank, hcells⟩ := modelReadOutputUntilBlank_eq_some_iff.mp h
  exact modelReadOutputUntilBlank_eq_some_iff.mpr ⟨by omega, hblank, hcells⟩

theorem bitMachineAfter_succ_of_halts' {k : ℕ} {m : TM0.Machine (Option Bool) (Fin (k + 1))}
    {l : List (Option Bool)} {t : ℕ} (h : BitMachineHaltsAt m l t) :
    BitMachineAfter m l (t + 1) = none := by
  obtain ⟨final, hrun, hstop⟩ := h
  show (BitMachineAfter m l t).bind (TM0.step m) = none
  rw [hrun]
  exact hstop

theorem bitMachineAfter_none_of_lt {k : ℕ} {m : TM0.Machine (Option Bool) (Fin (k + 1))}
    {l : List (Option Bool)} {t t' : ℕ} (h : BitMachineHaltsAt m l t) (ht : t < t') :
    BitMachineAfter m l t' = none := by
  induction t' with
  | zero => exact absurd (by omega : t < 0) (by omega)
  | succ t' ih =>
    by_cases heq : t' = t
    · subst heq
      exact bitMachineAfter_succ_of_halts' h
    · have hlt : t < t' := by omega
      show (BitMachineAfter m l t').bind (TM0.step m) = none
      rw [ih hlt]
      rfl

theorem unaryInput_getI_of_lt (n t : ℕ) (ht : t < n) :
    (uniformBqpUnaryInput n).getI t = some true := by
  unfold uniformBqpUnaryInput
  rw [List.getI_eq_getElem (List.replicate n (some true))
    (by simp [ht] : t < (List.replicate n (some true)).length)]
  simp

theorem unaryInput_getI_of_le (n t : ℕ) (ht : n ≤ t) :
    (uniformBqpUnaryInput n).getI t = (none : Option Bool) := by
  unfold uniformBqpUnaryInput
  rw [List.getI_eq_default (List.replicate n (some true))
    (by simp [ht] : (List.replicate n (some true)).length ≤ t)]
  rfl

theorem modelClockMachine_apply (q : Fin 1) (a : Option Bool) :
    modelClockMachine q a = if a = none then none
      else some ⟨default, TM0.Stmt.move Turing.Dir.right⟩ := rfl

theorem clock_machine_eq : uniformBqpClockGenerator.machine = modelClockMachine := rfl

theorem clock_step (cfg : TM0.Cfg (Option Bool) (Fin 1)) :
    TM0.step uniformBqpClockGenerator.machine cfg =
      if cfg.Tape.head = none then none
      else some ⟨default, cfg.Tape.move Turing.Dir.right⟩ := by
  obtain ⟨q, T⟩ := cfg
  rw [clock_machine_eq]
  by_cases hT : T.head = none
  · rw [if_pos hT]
    refine (tm0_step_none_iff modelClockMachine ⟨q, T⟩).mpr ?_
    rw [modelClockMachine_apply]
    simp [hT]
  · rw [if_neg hT]
    have happ : modelClockMachine q T.head
        = some ⟨default, TM0.Stmt.move Turing.Dir.right⟩ := by
      rw [modelClockMachine_apply]
      simp [hT]
    exact tm0_step_eq_some' modelClockMachine ⟨q, T⟩ default
      (TM0.Stmt.move Turing.Dir.right) happ

theorem clock_head_of_lt (n t : ℕ) (ht : t < n) :
    ((Turing.Tape.move Turing.Dir.right)^[t]
      (Turing.Tape.mk₁ (uniformBqpUnaryInput n))).head = some true := by
  have h1 := Turing.Tape.move_right_n_head (Turing.Tape.mk₁ (uniformBqpUnaryInput n)) t
  rw [h1, init_nth]
  simp only [if_neg (by omega : ¬((t : ℤ) < 0)), Int.toNat_natCast]
  exact unaryInput_getI_of_lt n t ht

theorem clock_head_none (n : ℕ) :
    ((Turing.Tape.move Turing.Dir.right)^[n]
      (Turing.Tape.mk₁ (uniformBqpUnaryInput n))).head = none := by
  have h1 := Turing.Tape.move_right_n_head (Turing.Tape.mk₁ (uniformBqpUnaryInput n)) n
  rw [h1, init_nth]
  simp only [if_neg (by omega : ¬((n : ℤ) < 0)), Int.toNat_natCast]
  exact unaryInput_getI_of_le n n le_rfl

theorem clock_after_of_le (n t : ℕ) (ht : t ≤ n) :
    BitMachineAfter uniformBqpClockGenerator.machine (uniformBqpUnaryInput n) t
      = some ⟨default,
        (Turing.Tape.move Turing.Dir.right)^[t] (Turing.Tape.mk₁ (uniformBqpUnaryInput n))⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hcfg := ih (by omega : t ≤ n)
    have hstep : TM0.step uniformBqpClockGenerator.machine
        (⟨default, (Turing.Tape.move Turing.Dir.right)^[t]
          (Turing.Tape.mk₁ (uniformBqpUnaryInput n))⟩ : TM0.Cfg (Option Bool) (Fin 1))
        = some ⟨default, (Turing.Tape.move Turing.Dir.right)^[t + 1]
          (Turing.Tape.mk₁ (uniformBqpUnaryInput n))⟩ := by
      have hhead : ((Turing.Tape.move Turing.Dir.right)^[t]
          (Turing.Tape.mk₁ (uniformBqpUnaryInput n))).head = some true :=
        clock_head_of_lt n t (by omega)
      rw [clock_step, hhead]
      simp only [Option.some_ne_none, if_false]
      rw [← Function.iterate_succ_apply' (Turing.Tape.move Turing.Dir.right) t
        (Turing.Tape.mk₁ (uniformBqpUnaryInput n))]
    show (BitMachineAfter uniformBqpClockGenerator.machine (uniformBqpUnaryInput n) t).bind
      (TM0.step uniformBqpClockGenerator.machine) = _
    rw [hcfg]
    exact hstep

theorem clock_haltsAt (n : ℕ) :
    BitMachineHaltsAt uniformBqpClockGenerator.machine (uniformBqpUnaryInput n) n := by
  refine ⟨⟨default, (Turing.Tape.move Turing.Dir.right)^[n]
    (Turing.Tape.mk₁ (uniformBqpUnaryInput n))⟩, clock_after_of_le n n le_rfl, ?_⟩
  rw [clock_step, clock_head_none]
  simp

theorem clock_after_of_gt (n t : ℕ) (ht : n < t) :
    BitMachineAfter uniformBqpClockGenerator.machine (uniformBqpUnaryInput n) t = none :=
  bitMachineAfter_none_of_lt (clock_haltsAt n) ht

theorem clock_haltsAt_iff (n t : ℕ) :
    BitMachineHaltsAt uniformBqpClockGenerator.machine (uniformBqpUnaryInput n) t ↔ t = n := by
  constructor
  · intro h
    by_cases heq : t = n
    · exact heq
    · exfalso
      obtain ⟨final, hrun, hstop⟩ := h
      by_cases hlt : t < n
      · have hcfg := clock_after_of_le n t (Nat.le_of_lt hlt)
        rw [hcfg] at hrun
        have hfeq : final = ⟨default, (Turing.Tape.move Turing.Dir.right)^[t]
            (Turing.Tape.mk₁ (uniformBqpUnaryInput n))⟩ := Option.some.inj hrun.symm
        rw [hfeq] at hstop
        rw [clock_step] at hstop
        rw [clock_head_of_lt n t hlt] at hstop
        simp at hstop
      · rw [clock_after_of_gt n t (by omega)] at hrun
        exact absurd hrun (by simp)
  · rintro rfl
    exact clock_haltsAt _

theorem clock_generatedAt_none (n : ℕ) :
    uniformBqpGeneratedAt uniformBqpClockGenerator n = none := by
  rw [← modelGeneratedAt_eq]
  unfold modelGeneratedAt
  have hfuel : n ≤ uniformBqpTimeBound uniformBqpClockGenerator n := by
    simp [uniformBqpTimeBound, uniformBqpPolynomial, uniformBqpClockGenerator]
    try simp
  have hrun : modelRunUntilHaltWithin uniformBqpClockGenerator.machine
      (uniformBqpTimeBound uniformBqpClockGenerator n)
      (TM0.init (uniformBqpUnaryInput n)) = some
        ⟨default, (Turing.Tape.move Turing.Dir.right)^[n]
          (Turing.Tape.mk₁ (uniformBqpUnaryInput n))⟩ :=
    modelRunUntilHaltWithin_eq_some_iff.mpr
      ⟨n, hfuel, by rw [iterStep_init_eq_bitMachineAfter]; exact clock_after_of_le n n le_rfl,
        by rw [clock_step, clock_head_none]; simp⟩
  rw [hrun]
  simp only [Option.bind_some]
  have hread : modelReadOutputUntilBlank
      (n + uniformBqpTimeBound uniformBqpClockGenerator n + 1)
      (⟨default, (Turing.Tape.move Turing.Dir.right)^[n]
        (Turing.Tape.mk₁ (uniformBqpUnaryInput n))⟩ : TM0.Cfg (Option Bool) (Fin 1)).Tape.right₀
      = some [] := by
    refine modelReadOutputUntilBlank_eq_some_iff.mpr ⟨by simp, ?_, ?_⟩
    · rw [Turing.Tape.right₀_nth]
      exact clock_head_none n
    · intro i hi
      simp at hi
  rw [hread]
  simp only [Option.bind_some]
  show decodeUniformBqpWord [] = none
  rfl

theorem clock_wellformed : generatorWellformed uniformBqpClockGenerator := by
  intro n q gs hg
  rw [clock_generatedAt_none] at hg
  simp at hg

def printerContent (n w : ℕ) (bs : List Bool) (x : ℤ) : Option Bool :=
  if x < 0 then none
  else if x < n then some true
  else if x < n + w then some (bs.getD (x.toNat - n) false)
  else none

theorem printerContent_neg {n w : ℕ} {bs : List Bool} {x : ℤ} (hx : x < 0) :
    printerContent n w bs x = none := by
  unfold printerContent
  rw [if_pos hx]

theorem printerContent_input {n w : ℕ} {bs : List Bool} {x : ℤ} (hx : 0 ≤ x) (hxn : x < n) :
    printerContent n w bs x = some true := by
  unfold printerContent
  rw [if_neg (by omega : ¬x < 0), if_pos hxn]

theorem printerContent_written {n w : ℕ} {bs : List Bool} {x : ℤ} (hxn : n ≤ x)
    (hxw : x < n + w) : printerContent n w bs x = some (bs.getD (x.toNat - n) false) := by
  unfold printerContent
  rw [if_neg (by omega : ¬x < 0), if_neg (by omega : ¬x < n), if_pos hxw]

theorem printerContent_blank {n w : ℕ} {bs : List Bool} {x : ℤ} (hxw : n + w ≤ x) :
    printerContent n w bs x = none := by
  unfold printerContent
  rw [if_neg (by omega : ¬x < 0), if_neg (by omega : ¬x < n), if_neg (by omega : ¬x < n + w)]

theorem modelWordPrinterMachine_apply (bs : List Bool) :
    ∀ (q : Fin (3 * bs.length + 1)) (a : Option Bool),
      modelWordPrinterMachine bs q a =
        if h0 : q.val = 0 ∧ a = none ∧ 1 ≤ bs.length then
          some ⟨⟨1, by omega⟩, TM0.Stmt.write (some (bs.getD 0 false))⟩
        else if q.val = 0 ∧ a = none then
          none
        else if q.val = 0 then
          some ⟨⟨0, by omega⟩, TM0.Stmt.move Turing.Dir.right⟩
        else if h2 : 2 ≤ q.val ∧ q.val % 2 = 0 ∧ q.val ≤ 2 * bs.length - 2 then
          some ⟨⟨q.val + 1, by omega⟩, TM0.Stmt.write (some (bs.getD (q.val / 2) false))⟩
        else if h3 : q.val % 2 = 1 ∧ q.val ≤ 2 * bs.length - 3 then
          some ⟨⟨q.val + 1, by omega⟩, TM0.Stmt.move Turing.Dir.right⟩
        else if h4 : 1 ≤ q.val ∧ 2 * bs.length - 1 ≤ q.val ∧ q.val ≤ 3 * bs.length - 3 then
          some ⟨⟨q.val + 1, by omega⟩, TM0.Stmt.move Turing.Dir.left⟩
        else none := fun _ _ => rfl

theorem wordPrinter_machine_eq (q : ℕ) (gs : List FiniteGateCode) :
    (uniformBqpWordPrinter q gs).machine
      = modelWordPrinterMachine (encodeUniformBqpWord q gs) := rfl

theorem modelWordPrinterMachine_halt (bs : List Bool) (q : Fin (3 * bs.length + 1))
    (a : Option Bool)
    (h0 : ¬q.val = 0)
    (h4 : ¬(2 ≤ q.val ∧ q.val % 2 = 0 ∧ q.val ≤ 2 * bs.length - 2))
    (h5 : ¬(q.val % 2 = 1 ∧ q.val ≤ 2 * bs.length - 3))
    (h6 : ¬(1 ≤ q.val ∧ 2 * bs.length - 1 ≤ q.val ∧ q.val ≤ 3 * bs.length - 3)) :
    modelWordPrinterMachine bs q a = none := by
  rw [modelWordPrinterMachine_apply]
  split_ifs <;> first | rfl | grind

theorem modelWordPrinterMachine_left (bs : List Bool) (q : Fin (3 * bs.length + 1))
    (a : Option Bool)
    (h0 : ¬q.val = 0)
    (h4 : ¬(2 ≤ q.val ∧ q.val % 2 = 0 ∧ q.val ≤ 2 * bs.length - 2))
    (h5 : ¬(q.val % 2 = 1 ∧ q.val ≤ 2 * bs.length - 3))
    (h6 : 1 ≤ q.val ∧ 2 * bs.length - 1 ≤ q.val ∧ q.val ≤ 3 * bs.length - 3) :
    modelWordPrinterMachine bs q a
      = some ⟨⟨q.val + 1, by omega⟩, TM0.Stmt.move Turing.Dir.left⟩ := by
  rw [modelWordPrinterMachine_apply]
  split_ifs <;> first | rfl | grind

theorem wordPrinter_timeBound_eq (q : ℕ) (gs : List FiniteGateCode) (n : ℕ) :
    uniformBqpTimeBound (uniformBqpWordPrinter q gs) n
      = (3 * (encodeUniformBqpWord q gs).length + 2) * (n + 1) := by
  simp [uniformBqpTimeBound, uniformBqpPolynomial, uniformBqpWordPrinter]

theorem encodeUniformBqpWord_length_pos (q : ℕ) (gs : List FiniteGateCode) :
    0 < (encodeUniformBqpWord q gs).length := by
  unfold encodeUniformBqpWord
  rw [List.length_append, encodeUnaryField_length]
  omega

theorem printer_step_scan {bs : List Bool} {n k : ℕ} (hk : k < n)
    (cfg : TM0.Cfg (Option Bool) (Fin (3 * bs.length + 1)))
    (hq : cfg.q.val = 0)
    (hcontent : ∀ i : ℤ, cfg.Tape.nth i = printerContent n 0 bs ((k : ℤ) + i)) :
    ∃ cfg' : TM0.Cfg (Option Bool) (Fin (3 * bs.length + 1)),
      TM0.step (modelWordPrinterMachine bs) cfg = some cfg' ∧
        cfg'.q.val = 0 ∧
        ∀ i : ℤ, cfg'.Tape.nth i = printerContent n 0 bs (((k + 1 : ℕ) : ℤ) + i) := by
  have hhead : cfg.Tape.head = some true := by
    have h0 : cfg.Tape.nth (0 : ℤ) = cfg.Tape.head := Turing.Tape.nth_zero _
    rw [← h0, hcontent]
    simp only [Int.add_zero]
    exact printerContent_input (by omega) (by omega)
  have happ : modelWordPrinterMachine bs cfg.q cfg.Tape.head
      = some ⟨⟨0, by omega⟩, TM0.Stmt.move Turing.Dir.right⟩ := by
    simp [modelWordPrinterMachine_apply, hq, hhead]
  refine ⟨⟨⟨0, by omega⟩, cfg.Tape.move Turing.Dir.right⟩, ?_, rfl, ?_⟩
  · exact tm0_step_eq_some' (modelWordPrinterMachine bs) cfg ⟨0, by omega⟩
      (TM0.Stmt.move Turing.Dir.right) happ
  · intro i
    rw [Turing.Tape.move_right_nth, hcontent]
    congr 1
    omega

theorem printer_scan_reach (bs : List Bool) (n : ℕ) : ∀ k ≤ n,
    ∃ cfg : TM0.Cfg (Option Bool) (Fin (3 * bs.length + 1)),
      BitMachineAfter (modelWordPrinterMachine bs) (uniformBqpUnaryInput n) k = some cfg ∧
        cfg.q.val = 0 ∧
        ∀ i : ℤ, cfg.Tape.nth i = printerContent n 0 bs ((k : ℤ) + i) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨TM0.init (uniformBqpUnaryInput n), rfl, rfl, ?_⟩
    intro i
    show (Turing.Tape.mk₁ (uniformBqpUnaryInput n)).nth i = _
    rw [init_nth]
    by_cases hi : i < 0
    · rw [if_pos hi, printerContent_neg (by omega : ((0 : ℕ) : ℤ) + i < 0)]
      rfl
    · rw [if_neg hi]
      by_cases hik : i < n
      · rw [printerContent_input (by omega) (by omega)]
        unfold uniformBqpUnaryInput
        rw [List.getI_eq_getElem (List.replicate n (some true))
          (by rw [List.length_replicate]; omega)]
        simp
      · rw [printerContent_blank (by omega)]
        unfold uniformBqpUnaryInput
        rw [List.getI_eq_default (List.replicate n (some true))
          (by rw [List.length_replicate]; omega)]
        rfl
  | succ k ih =>
    intro hk
    obtain ⟨cfg, hr, hq, hcontent⟩ := ih (by omega)
    obtain ⟨cfg', hs, hq', hcontent'⟩ := printer_step_scan (by omega : k < n) cfg hq hcontent
    refine ⟨cfg', ?_, hq', hcontent'⟩
    show (BitMachineAfter (modelWordPrinterMachine bs) (uniformBqpUnaryInput n) k).bind
      (TM0.step (modelWordPrinterMachine bs)) = _
    rw [hr]
    exact hs

theorem printerContent_succ (n w : ℕ) (bs : List Bool) (x : ℤ) :
    printerContent n (w + 1) bs x =
      if x = (n : ℤ) + w then some (bs.getD w false) else printerContent n w bs x := by
  have hidx : ((n : ℤ) + w).toNat - n = w := by
    have h : ((n : ℤ) + w).toNat = n + w := by
      rw [Int.toNat_add (Int.natCast_nonneg n) (Int.natCast_nonneg w),
        Int.toNat_natCast, Int.toNat_natCast]
    omega
  by_cases h0 : x < 0
  · rw [printerContent_neg h0, if_neg (by omega), printerContent_neg h0]
  by_cases h1 : x < n
  · rw [printerContent_input (by omega) h1, if_neg (by omega),
      printerContent_input (by omega) h1]
  by_cases h2 : x = (n : ℤ) + w
  · rw [if_pos h2]
    have h3 : printerContent n (w + 1) bs x = some (bs.getD (x.toNat - n) false) :=
      printerContent_written (by omega) (by omega)
    rw [h3, h2, hidx]
  by_cases h3 : x < n + w
  · rw [if_neg h2]
    have h4 : printerContent n (w + 1) bs x = some (bs.getD (x.toNat - n) false) :=
      printerContent_written (by omega) (by omega)
    have h5 : printerContent n w bs x = some (bs.getD (x.toNat - n) false) :=
      printerContent_written (by omega) h3
    rw [h4, h5]
  · rw [if_neg h2, printerContent_blank (by omega), printerContent_blank (by omega)]

theorem printer_step_first_write {bs : List Bool} {n : ℕ} (hL : 1 ≤ bs.length)
    (cfg : TM0.Cfg (Option Bool) (Fin (3 * bs.length + 1)))
    (hq : cfg.q.val = 0)
    (hcontent : ∀ i : ℤ, cfg.Tape.nth i = printerContent n 0 bs (((n : ℕ) : ℤ) + i)) :
    ∃ cfg' : TM0.Cfg (Option Bool) (Fin (3 * bs.length + 1)),
      TM0.step (modelWordPrinterMachine bs) cfg = some cfg' ∧
        cfg'.q.val = 1 ∧
        ∀ i : ℤ, cfg'.Tape.nth i = printerContent n 1 bs (((n : ℕ) : ℤ) + i) := by
  have hhead : cfg.Tape.head = none := by
    have h0 : cfg.Tape.nth (0 : ℤ) = cfg.Tape.head := Turing.Tape.nth_zero _
    rw [← h0, hcontent, Int.add_zero]
    exact printerContent_blank (by omega)
  have happ : modelWordPrinterMachine bs cfg.q cfg.Tape.head
      = some ⟨⟨1, by omega⟩, TM0.Stmt.write (some (bs.getD 0 false))⟩ := by
    simp [modelWordPrinterMachine_apply, hq, hhead, hL]
  refine ⟨⟨⟨1, by omega⟩, cfg.Tape.write (some (bs.getD 0 false))⟩, ?_, rfl, ?_⟩
  · exact tm0_step_eq_some' (modelWordPrinterMachine bs) cfg ⟨1, by omega⟩
      (TM0.Stmt.write (some (bs.getD 0 false))) happ
  · intro i
    rw [Turing.Tape.write_nth]
    by_cases hi : i = 0
    · subst hi
      rw [if_pos rfl, Int.add_zero]
      have h4 : printerContent n 1 bs ((n : ℤ)) = some (bs.getD 0 false) := by
        have h5 := printerContent_written (n := n) (w := 1) (bs := bs)
          (x := (n : ℤ)) (by omega) (by omega)
        rw [h5]
        simp
      exact h4.symm
    · rw [if_neg hi, hcontent]
      rw [printerContent_succ n 0 bs (↑n + i)]
      rw [if_neg (by omega)]

theorem printer_step_move_right {bs : List Bool} {n j : ℕ}
    (hj : j + 1 < bs.length)
    (cfg : TM0.Cfg (Option Bool) (Fin (3 * bs.length + 1)))
    (hq : cfg.q.val = 2 * j + 1)
    (hcontent : ∀ i : ℤ, cfg.Tape.nth i = printerContent n (j + 1) bs
      (((n + j : ℕ) : ℤ) + i)) :
    ∃ cfg' : TM0.Cfg (Option Bool) (Fin (3 * bs.length + 1)),
      TM0.step (modelWordPrinterMachine bs) cfg = some cfg' ∧
        cfg'.q.val = 2 * j + 2 ∧
        ∀ i : ℤ, cfg'.Tape.nth i = printerContent n (j + 1) bs
          (((n + j + 1 : ℕ) : ℤ) + i) := by
  have hhead : cfg.Tape.head = some (bs.getD j false) := by
    have h0 : cfg.Tape.nth (0 : ℤ) = cfg.Tape.head := Turing.Tape.nth_zero _
    rw [← h0, hcontent, Int.add_zero]
    have h5 := printerContent_written (n := n) (w := j + 1) (bs := bs)
      (x := ((n + j : ℕ) : ℤ)) (by omega) (by omega)
    rw [h5]
    have h6 : (((n + j : ℕ) : ℤ).toNat - n) = j := by
      rw [Int.toNat_natCast]
      omega
    rw [h6]
  have happ : modelWordPrinterMachine bs cfg.q cfg.Tape.head
      = some ⟨⟨2 * j + 2, by omega⟩, TM0.Stmt.move Turing.Dir.right⟩ := by
    have h1 : 2 * j + 1 ≠ 0 := by omega
    have h2 : (2 * j + 1) % 2 = 1 := by omega
    have h3 : 2 * j + 1 ≤ 2 * bs.length - 3 := by omega
    simp [modelWordPrinterMachine_apply, hq, hhead, h2, h3]
  refine ⟨⟨⟨2 * j + 2, by omega⟩, cfg.Tape.move Turing.Dir.right⟩, ?_, rfl, ?_⟩
  · exact tm0_step_eq_some' (modelWordPrinterMachine bs) cfg ⟨2 * j + 2, by omega⟩
      (TM0.Stmt.move Turing.Dir.right) happ
  · intro i
    rw [Turing.Tape.move_right_nth, hcontent]
    congr 1
    omega

theorem printer_step_write {bs : List Bool} {n j : ℕ}
    (hj : j < bs.length) (hj0 : 0 < j)
    (cfg : TM0.Cfg (Option Bool) (Fin (3 * bs.length + 1)))
    (hq : cfg.q.val = 2 * j)
    (hcontent : ∀ i : ℤ, cfg.Tape.nth i = printerContent n j bs
      (((n + j : ℕ) : ℤ) + i)) :
    ∃ cfg' : TM0.Cfg (Option Bool) (Fin (3 * bs.length + 1)),
      TM0.step (modelWordPrinterMachine bs) cfg = some cfg' ∧
        cfg'.q.val = 2 * j + 1 ∧
        ∀ i : ℤ, cfg'.Tape.nth i = printerContent n (j + 1) bs
          (((n + j : ℕ) : ℤ) + i) := by
  have hhead : cfg.Tape.head = none := by
    have h0 : cfg.Tape.nth (0 : ℤ) = cfg.Tape.head := Turing.Tape.nth_zero _
    rw [← h0, hcontent, Int.add_zero]
    exact printerContent_blank (by omega)
  have happ : modelWordPrinterMachine bs cfg.q cfg.Tape.head
      = some ⟨⟨2 * j + 1, by omega⟩, TM0.Stmt.write (some (bs.getD j false))⟩ := by
    have h1 : 2 * j ≠ 0 := by omega
    have h2 : 2 ≤ 2 * j := by omega
    have h3 : (2 * j) % 2 = 0 := by omega
    have h4 : 2 * j ≤ 2 * bs.length - 2 := by omega
    have h5 : 2 * j / 2 = j := by omega
    simp [modelWordPrinterMachine_apply, hq, hhead, h1, h2, h3, h4, h5]
  refine ⟨⟨⟨2 * j + 1, by omega⟩, cfg.Tape.write (some (bs.getD j false))⟩, ?_, rfl, ?_⟩
  · exact tm0_step_eq_some' (modelWordPrinterMachine bs) cfg ⟨2 * j + 1, by omega⟩
      (TM0.Stmt.write (some (bs.getD j false))) happ
  · intro i
    rw [Turing.Tape.write_nth]
    by_cases hi : i = 0
    · subst hi
      rw [if_pos rfl, Int.add_zero]
      have h6 : printerContent n (j + 1) bs (↑(n + j)) = some (bs.getD j false) := by
        have h7 := printerContent_written (n := n) (w := j + 1) (bs := bs)
          (x := ((n + j : ℕ) : ℤ)) (by omega) (by omega)
        rw [h7]
        have h8 : (((n + j : ℕ) : ℤ).toNat - n) = j := by
          rw [Int.toNat_natCast]
          omega
        rw [h8]
      exact h6.symm
    · rw [if_neg hi, hcontent]
      rw [printerContent_succ n j bs (↑(n + j) + i)]
      rw [if_neg (by omega)]

theorem printer_step_left {bs : List Bool} {n r : ℕ}
    (hr : r + 2 < bs.length + 1) (_hr' : r + 1 ≤ bs.length - 1)
    (cfg : TM0.Cfg (Option Bool) (Fin (3 * bs.length + 1)))
    (hq : cfg.q.val = 2 * bs.length - 1 + r)
    (hcontent : ∀ i : ℤ, cfg.Tape.nth i = printerContent n bs.length bs
      (((n + bs.length - 1 - r : ℕ) : ℤ) + i)) :
    ∃ cfg' : TM0.Cfg (Option Bool) (Fin (3 * bs.length + 1)),
      TM0.step (modelWordPrinterMachine bs) cfg = some cfg' ∧
        cfg'.q.val = 2 * bs.length - 1 + (r + 1) ∧
        ∀ i : ℤ, cfg'.Tape.nth i = printerContent n bs.length bs
          (((n + bs.length - 1 - (r + 1) : ℕ) : ℤ) + i) := by
  have hhead : cfg.Tape.head = some (bs.getD (bs.length - 1 - r) false) := by
    have h0 : cfg.Tape.nth (0 : ℤ) = cfg.Tape.head := Turing.Tape.nth_zero _
    rw [← h0, hcontent, Int.add_zero]
    have h5 := printerContent_written (n := n) (w := bs.length) (bs := bs)
      (x := ((n + bs.length - 1 - r : ℕ) : ℤ)) (by omega) (by omega)
    rw [h5]
    have h6 : (((n + bs.length - 1 - r : ℕ) : ℤ).toNat - n) = bs.length - 1 - r := by
      rw [Int.toNat_natCast]
      omega
    rw [h6]
  have happ : modelWordPrinterMachine bs cfg.q cfg.Tape.head
      = some ⟨⟨2 * bs.length - 1 + (r + 1), by omega⟩, TM0.Stmt.move Turing.Dir.left⟩ := by
    have hle : 1 ≤ cfg.q.val ∧ 2 * bs.length - 1 ≤ cfg.q.val ∧ cfg.q.val ≤ 3 * bs.length - 3 := by
      rw [hq]
      exact ⟨by omega, by omega, by omega⟩
    simpa [hq] using! modelWordPrinterMachine_left bs cfg.q cfg.Tape.head
      (by omega) (by rintro ⟨_, h, _⟩; omega) (by rintro ⟨_, h⟩; omega) hle
  refine ⟨⟨⟨2 * bs.length - 1 + (r + 1), by omega⟩, cfg.Tape.move Turing.Dir.left⟩, ?_, rfl, ?_⟩
  · exact tm0_step_eq_some' (modelWordPrinterMachine bs) cfg
      ⟨2 * bs.length - 1 + (r + 1), by omega⟩ (TM0.Stmt.move Turing.Dir.left) happ
  · intro i
    rw [Turing.Tape.move_left_nth, hcontent]
    congr 1
    omega

theorem printer_write_reach (bs : List Bool) (n : ℕ) (hL : 1 ≤ bs.length) : ∀ j ≤ bs.length - 1,
    (∃ cfg : TM0.Cfg (Option Bool) (Fin (3 * bs.length + 1)),
      BitMachineAfter (modelWordPrinterMachine bs) (uniformBqpUnaryInput n) (n + 1 + 2 * j)
        = some cfg ∧
        cfg.q.val = 2 * j + 1 ∧
        ∀ i : ℤ, cfg.Tape.nth i = printerContent n (j + 1) bs (↑(n + j) + i)) ∧
    (j < bs.length - 1 →
      ∃ cfg : TM0.Cfg (Option Bool) (Fin (3 * bs.length + 1)),
        BitMachineAfter (modelWordPrinterMachine bs) (uniformBqpUnaryInput n) (n + 2 + 2 * j)
          = some cfg ∧
          cfg.q.val = 2 * j + 2 ∧
          ∀ i : ℤ, cfg.Tape.nth i = printerContent n (j + 1) bs (↑(n + j + 1) + i)) := by
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨cfg0, hr0, hq0, hc0⟩ := printer_scan_reach bs n n le_rfl
    obtain ⟨cfg1, hs1, hq1, hc1⟩ := printer_step_first_write hL cfg0 hq0 hc0
    have hrA : BitMachineAfter (modelWordPrinterMachine bs) (uniformBqpUnaryInput n)
        (n + 1 + 2 * 0) = some cfg1 := by
      show (BitMachineAfter (modelWordPrinterMachine bs) (uniformBqpUnaryInput n) n).bind
        (TM0.step (modelWordPrinterMachine bs)) = _
      rw [hr0]
      exact hs1
    refine ⟨⟨cfg1, hrA, hq1, hc1⟩, ?_⟩
    · intro hj
      obtain ⟨cfg2, hs2, hq2, hc2⟩ :=
        printer_step_move_right (by omega : 0 + 1 < bs.length) cfg1 hq1 hc1
      refine ⟨cfg2, ?_, hq2, hc2⟩
      have htimeB : n + 2 + 2 * 0 = n + 1 + 2 * 0 + 1 := by omega
      rw [htimeB]
      show (BitMachineAfter (modelWordPrinterMachine bs) (uniformBqpUnaryInput n)
        (n + 1 + 2 * 0)).bind (TM0.step (modelWordPrinterMachine bs)) = _
      rw [hrA]
      exact hs2
  | succ j ih =>
    intro hj
    have ih' := ih (by omega)
    obtain ⟨cfgB, hrB, hqB, hcB⟩ := ih'.2 (by omega : j < bs.length - 1)
    have hwrite : j + 1 < bs.length := by omega
    have hpos : 0 < j + 1 := by omega
    obtain ⟨cfgA, hsA, hqA, hcA⟩ := printer_step_write hwrite hpos cfgB hqB hcB
    have htimeA : n + 1 + 2 * (j + 1) = n + 2 + 2 * j + 1 := by omega
    have hrA : BitMachineAfter (modelWordPrinterMachine bs) (uniformBqpUnaryInput n)
        (n + 1 + 2 * (j + 1)) = some cfgA := by
      rw [htimeA]
      show (BitMachineAfter (modelWordPrinterMachine bs) (uniformBqpUnaryInput n)
        (n + 2 + 2 * j)).bind (TM0.step (modelWordPrinterMachine bs)) = _
      rw [hrB]
      exact hsA
    refine ⟨⟨cfgA, hrA, hqA, hcA⟩, ?_⟩
    · intro hj2
      obtain ⟨cfgB', hsB, hqB', hcB'⟩ :=
        printer_step_move_right (by omega : j + 1 + 1 < bs.length) cfgA hqA hcA
      refine ⟨cfgB', ?_, hqB', hcB'⟩
      have htimeB : n + 2 + 2 * (j + 1) = n + 1 + 2 * (j + 1) + 1 := by omega
      rw [htimeB]
      show (BitMachineAfter (modelWordPrinterMachine bs) (uniformBqpUnaryInput n)
        (n + 1 + 2 * (j + 1))).bind (TM0.step (modelWordPrinterMachine bs)) = _
      rw [hrA]
      exact hsB

theorem printer_left_reach (bs : List Bool) (n : ℕ) (hL : 1 ≤ bs.length) :
    ∀ r ≤ bs.length - 1,
      ∃ cfg : TM0.Cfg (Option Bool) (Fin (3 * bs.length + 1)),
        BitMachineAfter (modelWordPrinterMachine bs) (uniformBqpUnaryInput n)
          (n + 2 * bs.length - 1 + r) = some cfg ∧
          cfg.q.val = 2 * bs.length - 1 + r ∧
          ∀ i : ℤ, cfg.Tape.nth i =
            printerContent n bs.length bs (↑(n + bs.length - 1 - r) + i) := by
  intro r
  induction r with
  | zero =>
    intro _
    obtain ⟨cfgA, hrA, hqA, hcA⟩ := (printer_write_reach bs n hL (bs.length - 1) le_rfl).1
    have htime : n + 2 * bs.length - 1 + 0 = n + 1 + 2 * (bs.length - 1) := by omega
    refine ⟨cfgA, ?_, ?_, ?_⟩
    · rw [htime]
      exact hrA
    · rw [hqA]
      omega
    · intro i
      rw [hcA]
      have h1 : bs.length - 1 + 1 = bs.length := by omega
      have h2 : n + (bs.length - 1) = n + bs.length - 1 - 0 := by omega
      rw [h1, h2]
  | succ r ih =>
    intro hr
    obtain ⟨cfg, hr0, hq0, hc0⟩ := ih (by omega)
    have hleft : r + 2 < bs.length + 1 := by omega
    have hleft' : r + 1 ≤ bs.length - 1 := by omega
    obtain ⟨cfg', hs, hq', hc'⟩ := printer_step_left hleft hleft' cfg hq0 hc0
    refine ⟨cfg', ?_, hq', hc'⟩
    have htime : n + 2 * bs.length - 1 + (r + 1) = n + 2 * bs.length - 1 + r + 1 := by omega
    rw [htime]
    show (BitMachineAfter (modelWordPrinterMachine bs) (uniformBqpUnaryInput n)
      (n + 2 * bs.length - 1 + r)).bind (TM0.step (modelWordPrinterMachine bs)) = _
    rw [hr0]
    exact hs

theorem printer_haltsAt (bs : List Bool) (n : ℕ) (hL : 1 ≤ bs.length) :
    BitMachineHaltsAt (modelWordPrinterMachine bs) (uniformBqpUnaryInput n)
      (n + 3 * bs.length - 2) := by
  obtain ⟨cfg, hr, hq, hc⟩ := printer_left_reach bs n hL (bs.length - 1) le_rfl
  have htime : n + 2 * bs.length - 1 + (bs.length - 1) = n + 3 * bs.length - 2 := by omega
  refine ⟨cfg, ?_, ?_⟩
  · rw [← htime]
    exact hr
  · rw [tm0_step_none_iff]
    exact modelWordPrinterMachine_halt bs cfg.q cfg.Tape.head
      (by rw [hq]; omega)
      (by rw [hq]; rintro ⟨_, _, h⟩; omega)
      (by rw [hq]; rintro ⟨_, h⟩; omega)
      (by rw [hq]; rintro ⟨_, _, h⟩; omega)

theorem printerContent_at_halt (n : ℕ) (bs : List Bool) (i : ℕ) :
    printerContent n bs.length bs (↑n + (i : ℤ)) =
      if i < bs.length then some (bs.getD i false) else none := by
  by_cases hi : i < bs.length
  · rw [if_pos hi]
    have h := printerContent_written (n := n) (w := bs.length) (bs := bs)
      (x := (↑n + (i : ℤ))) (by omega) (by omega)
    rw [h]
    congr 1
    have h2 : (↑n + (i : ℤ)).toNat - n = i := by
      rw [Int.toNat_add (Int.natCast_nonneg n) (Int.natCast_nonneg i),
        Int.toNat_natCast, Int.toNat_natCast]
      omega
    rw [h2]
  · rw [if_neg hi, printerContent_blank (by omega)]

theorem printer_final_nth (bs : List Bool) (n : ℕ) (hL : 1 ≤ bs.length) :
    ∃ cfg : TM0.Cfg (Option Bool) (Fin (3 * bs.length + 1)),
      BitMachineAfter (modelWordPrinterMachine bs) (uniformBqpUnaryInput n)
        (n + 3 * bs.length - 2) = some cfg ∧
        TM0.step (modelWordPrinterMachine bs) cfg = none ∧
        (∀ i : ℕ, i < bs.length → cfg.Tape.right₀.nth i = some (bs.getD i false)) ∧
        cfg.Tape.right₀.nth bs.length = none := by
  obtain ⟨cfg, hr, hq, hc⟩ := printer_left_reach bs n hL (bs.length - 1) le_rfl
  have htime : n + 2 * bs.length - 1 + (bs.length - 1) = n + 3 * bs.length - 2 := by omega
  have hpos : n + bs.length - 1 - (bs.length - 1) = n := by omega
  refine ⟨cfg, ?_, ?_, ?_, ?_⟩
  · rw [← htime]; exact hr
  · rw [tm0_step_none_iff]
    exact modelWordPrinterMachine_halt bs cfg.q cfg.Tape.head
      (by rw [hq]; omega)
      (by rw [hq]; rintro ⟨_, _, h⟩; omega)
      (by rw [hq]; rintro ⟨_, h⟩; omega)
      (by rw [hq]; rintro ⟨_, _, h⟩; omega)
  · intro i hi
    rw [Turing.Tape.right₀_nth, hc, hpos, printerContent_at_halt]
    rw [if_pos hi]
  · rw [Turing.Tape.right₀_nth, hc, hpos, printerContent_at_halt]
    rw [if_neg (by omega)]

theorem printer_time_bound (q : ℕ) (gs : List FiniteGateCode) (n : ℕ) :
    n + 3 * (encodeUniformBqpWord q gs).length - 2
      ≤ uniformBqpTimeBound (uniformBqpWordPrinter q gs) n := by
  rw [wordPrinter_timeBound_eq]
  have h1 : (3 * (encodeUniformBqpWord q gs).length + 2) * (n + 1)
      = 3 * (encodeUniformBqpWord q gs).length * n + 2 * n
        + 3 * (encodeUniformBqpWord q gs).length + 2 := by ring
  rw [h1]
  omega

theorem printer_generatedAt (q : ℕ) (gs : List FiniteGateCode) (n : ℕ) :
    uniformBqpGeneratedAt (uniformBqpWordPrinter q gs) n = some (q, gs) := by
  have hL : 1 ≤ (encodeUniformBqpWord q gs).length := encodeUniformBqpWord_length_pos q gs
  obtain ⟨cfg, hr, hstop, hcells, hblank⟩ := printer_final_nth (encodeUniformBqpWord q gs) n hL
  have hcfg : iterStep (uniformBqpWordPrinter q gs).machine
      (TM0.init (uniformBqpUnaryInput n)) (n + 3 * (encodeUniformBqpWord q gs).length - 2)
      = some cfg := by
    rw [iterStep_init_eq_bitMachineAfter]
    exact hr
  have hread : modelReadOutputUntilBlank
      (n + uniformBqpTimeBound (uniformBqpWordPrinter q gs) n + 1)
      cfg.Tape.right₀ = some (encodeUniformBqpWord q gs) := by
    refine modelReadOutputUntilBlank_eq_some_iff.mpr ⟨?_, hblank, ?_⟩
    · rw [wordPrinter_timeBound_eq]
      have h1 : (3 * (encodeUniformBqpWord q gs).length + 2) * (n + 1)
          = 3 * (encodeUniformBqpWord q gs).length * n + 2 * n
            + 3 * (encodeUniformBqpWord q gs).length + 2 := by ring
      rw [h1]
      omega
    · intro i hi
      exact hcells i hi
  exact modelGeneratedAt_of_run (printer_time_bound q gs n) hcfg hstop q gs hread

theorem printer_valid (q : ℕ) (gs : List FiniteGateCode)
    (hlegal : finiteWordLegal q gs = true) :
    uniformBqpGeneratorValid (uniformBqpWordPrinter q gs) := by
  intro n
  refine ⟨q, gs, printer_generatedAt q gs n, ?_, hlegal, ?_, ?_, ?_⟩
  · exact ⟨n + 3 * (encodeUniformBqpWord q gs).length - 2, printer_time_bound q gs n,
      printer_haltsAt (encodeUniformBqpWord q gs) n (encodeUniformBqpWord_length_pos q gs)⟩
  · have h1 : gs.length ≤ (encodeUniformBqpWord q gs).length := by
      unfold encodeUniformBqpWord
      rw [List.length_append, encodeUnaryField_length]
      have h2 := length_le_flatMap_encodeFiniteGateCode gs
      omega
    simp [uniformBqpWordBound, uniformBqpPolynomial, uniformBqpWordPrinter]
    have h2 : ((encodeUniformBqpWord q gs).length + 1) * (n + 1)
        = (encodeUniformBqpWord q gs).length * n + (encodeUniformBqpWord q gs).length
          + n + 1 := by ring
    rw [h2]
    omega
  · simp [uniformBqpSpaceBound, uniformBqpPolynomial, uniformBqpWordPrinter]
    have h2 : (q + 1) * (n + 1) = q * n + q + n + 1 := by ring
    rw [h2]
    omega
  · rw [wordPrinter_timeBound_eq]
    have h1 : (3 * (encodeUniformBqpWord q gs).length + 2) * (n + 1)
        = 3 * (encodeUniformBqpWord q gs).length * n + 2 * n
          + 3 * (encodeUniformBqpWord q gs).length + 2 := by ring
    rw [h1]
    omega

theorem padWire_zero (k w : ℕ) : Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.padWire 0 k w = w + k := by
  unfold Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.padWire
  rw [if_neg (by omega : ¬w < 0)]

theorem finiteCodeLegal_of_le {q q' : ℕ} {g : FiniteGateCode} (hle : q ≤ q')
    (hg : finiteCodeLegal q g = true) : finiteCodeLegal q' g = true := by
  cases g with
  | h w =>
    have hw : w < q := by simpa [finiteCodeLegal] using! hg
    have hw' : w < q' := lt_of_lt_of_le hw hle
    simpa [finiteCodeLegal] using! hw'
  | x w =>
    have hw : w < q := by simpa [finiteCodeLegal] using! hg
    have hw' : w < q' := lt_of_lt_of_le hw hle
    simpa [finiteCodeLegal] using! hw'
  | t w =>
    have hw : w < q := by simpa [finiteCodeLegal] using! hg
    have hw' : w < q' := lt_of_lt_of_le hw hle
    simpa [finiteCodeLegal] using! hw'
  | tdg w =>
    have hw : w < q := by simpa [finiteCodeLegal] using! hg
    have hw' : w < q' := lt_of_lt_of_le hw hle
    simpa [finiteCodeLegal] using! hw'
  | cx c t =>
    have hw : c < q ∧ t < q ∧ c ≠ t := by simpa [finiteCodeLegal] using! hg
    have hw' : c < q' ∧ t < q' ∧ c ≠ t :=
      ⟨lt_of_lt_of_le hw.1 hle, lt_of_lt_of_le hw.2.1 hle, hw.2.2⟩
    simpa [finiteCodeLegal] using! hw'

theorem padFiniteCode_legal {q : ℕ} {g : FiniteGateCode}
    (h : finiteCodeLegal q g = true) :
    finiteCodeLegal (2 * q) (Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.padFiniteCode 0 q g) = true := by
  cases g with
  | h w =>
    have hw : w < q := by simpa [finiteCodeLegal] using! h
    simp [finiteCodeLegal,
        Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.padFiniteCode, padWire_zero]; omega
  | x w =>
    have hw : w < q := by simpa [finiteCodeLegal] using! h
    simp [finiteCodeLegal,
        Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.padFiniteCode, padWire_zero]; omega
  | t w =>
    have hw : w < q := by simpa [finiteCodeLegal] using! h
    simp [finiteCodeLegal,
        Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.padFiniteCode, padWire_zero]; omega
  | tdg w =>
    have hw : w < q := by simpa [finiteCodeLegal] using! h
    simp [finiteCodeLegal,
        Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.padFiniteCode, padWire_zero]; omega
  | cx c t =>
    have hw : c < q ∧ t < q ∧ c ≠ t := by simpa [finiteCodeLegal] using! h
    simp [finiteCodeLegal,
        Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.padFiniteCode, padWire_zero]; omega

theorem duplicateWord_legal (q : ℕ) (gs : List FiniteGateCode)
    (h : finiteWordLegal q gs = true) :
    finiteWordLegal (duplicateWord q gs).1 (duplicateWord q gs).2 = true := by
  show finiteWordLegal (2 * q)
      (gs ++ gs.map (Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.padFiniteCode 0 q)) = true
  have hall : gs.all (finiteCodeLegal q) = true := h
  simp only [finiteWordLegal, List.all_append, Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, ?_⟩
  · intro x hx
    exact finiteCodeLegal_of_le (by omega : q ≤ 2 * q) (List.all_eq_true.mp hall x hx)
  · intro x hx
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hx
    exact padFiniteCode_legal (List.all_eq_true.mp hall g0 hg0)

theorem duplicateWord_counts (q : ℕ) (gs : List FiniteGateCode) :
    QueryCount (finiteCodeCircuit (duplicateWord q gs).1 (duplicateWord q gs).2) = 0 ∧
      GateCount (finiteCodeCircuit (duplicateWord q gs).1 (duplicateWord q gs).2) = 2 * gs.length := by
  show QueryCount (finiteCodeCircuit (2 * q) (gs ++ gs.map (Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.padFiniteCode 0 q))) = 0 ∧
    GateCount (finiteCodeCircuit (2 * q) (gs ++ gs.map (Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs.padFiniteCode 0 q))) = 2 * gs.length
  refine ⟨(finiteCodeCircuit_counts _ _).1, ?_⟩
  rw [(finiteCodeCircuit_counts _ _).2]
  simp only [List.length_append, List.length_map]
  omega

theorem duplicateWord_printer_generatedAt (q : ℕ) (gs : List FiniteGateCode) (n : ℕ) :
    uniformBqpGeneratedAt
      (uniformBqpWordPrinter (duplicateWord q gs).1 (duplicateWord q gs).2) n =
      some (duplicateWord q gs) :=
  printer_generatedAt (duplicateWord q gs).1 (duplicateWord q gs).2 n

theorem duplicateWord_printer_valid (q : ℕ) (gs : List FiniteGateCode)
    (h : finiteWordLegal q gs = true) :
    uniformBqpGeneratorValid
      (uniformBqpWordPrinter (duplicateWord q gs).1 (duplicateWord q gs).2) :=
  printer_valid (duplicateWord q gs).1 (duplicateWord q gs).2 (duplicateWord_legal q gs h)

theorem option_bind_eq_some' {α β : Type} {o : Option α} {f : α → Option β} {b : β} :
    o.bind f = some b ↔ ∃ a, o = some a ∧ f a = some b := by
  cases o with
  | none => simp
  | some a => simp

theorem wellformed_generatedTotal_legal {g : UniformBqpGenerator} (h : generatorWellformed g) :
    ∀ n : ℕ, finiteWordLegal (uniformBqpGeneratedTotal g n).1
      (uniformBqpGeneratedTotal g n).2 = true := by
  intro n
  cases hs : uniformBqpGeneratedAt g n with
  | none =>
    have htot : uniformBqpGeneratedTotal g n = (0, []) := by
      simp [uniformBqpGeneratedTotal, hs]
    rw [htot]
    rfl
  | some w =>
    obtain ⟨q, gs⟩ := w
    have htot : uniformBqpGeneratedTotal g n = (q, gs) := by
      simp [uniformBqpGeneratedTotal, hs]
    rw [htot]
    exact h n q gs hs

theorem generatedTotal_bit_bound (g : UniformBqpGenerator) (n : ℕ) :
    (uniformBqpGeneratedTotal g n).2.length ≤ n + uniformBqpTimeBound g n + 1 ∧
      (uniformBqpGeneratedTotal g n).1 ≤ n + uniformBqpTimeBound g n + 1 := by
  cases hs : uniformBqpGeneratedAt g n with
  | none =>
    have htot : uniformBqpGeneratedTotal g n = (0, []) := by
      simp [uniformBqpGeneratedTotal, hs]
    rw [htot]
    simp
  | some w =>
    obtain ⟨q, gs⟩ := w
    have htot : uniformBqpGeneratedTotal g n = (q, gs) := by
      simp [uniformBqpGeneratedTotal, hs]
    rw [htot]
    show gs.length ≤ n + uniformBqpTimeBound g n + 1 ∧ q ≤ n + uniformBqpTimeBound g n + 1
    have hs' : modelGeneratedAt g n = some (q, gs) := by
      rw [modelGeneratedAt_eq]
      exact hs
    unfold modelGeneratedAt at hs'
    obtain ⟨cfg, hrun, hrest⟩ := option_bind_eq_some'.mp hs'
    obtain ⟨bits, hread, hdec⟩ := option_bind_eq_some'.mp hrest
    have hbits : bits = encodeUniformBqpWord q gs := decodeUniformBqpWord_eq_some hdec
    obtain ⟨hlen, _, _⟩ := modelReadOutputUntilBlank_eq_some_iff.mp hread
    have h1 : q ≤ bits.length := by
      rw [hbits]
      unfold encodeUniformBqpWord
      rw [List.length_append, encodeUnaryField_length]
      omega
    have h2 : gs.length ≤ bits.length := by
      rw [hbits]
      unfold encodeUniformBqpWord
      rw [List.length_append, encodeUnaryField_length]
      have h3 := length_le_flatMap_encodeFiniteGateCode gs
      omega
    omega

theorem poly_encode_bound (tc td n : ℕ) :
    n + tc * (n + 1) ^ td + 1 ≤ uniformBqpPolynomial (tc + 1) (td + 1) n := by
  unfold uniformBqpPolynomial
  rw [pow_succ]
  rcases Nat.eq_zero_or_pos td with h0 | hpos
  · subst h0
    simp only [pow_zero, mul_one, one_mul]
    have h2 : (tc + 1) * (n + 1) = tc * n + tc + n + 1 := by ring
    rw [h2]
    have h3 : 0 ≤ tc * n := Nat.zero_le _
    omega
  · have h3 : n + 1 ≤ (n + 1) ^ td :=
      le_self_pow (by omega : 1 ≤ n + 1) (by omega : td ≠ 0)
    have hnorm : (tc + 1) * ((n + 1) ^ td * (n + 1))
        = (tc * (n + 1) ^ td) * (n + 1) + (n + 1) ^ td * (n + 1) := by ring
    rw [hnorm]
    have hA : tc * (n + 1) ^ td ≤ (tc * (n + 1) ^ td) * (n + 1) := by
      have h1 : (tc * (n + 1) ^ td) * 1 ≤ (tc * (n + 1) ^ td) * (n + 1) :=
        Nat.mul_le_mul (le_refl _) (by omega : 1 ≤ n + 1)
      simpa using! h1
    have hB : n + 1 ≤ (n + 1) ^ td * (n + 1) := by
      have h1 : (n + 1) * 1 ≤ (n + 1) ^ td * (n + 1) :=
        Nat.mul_le_mul h3 (by omega : 1 ≤ n + 1)
      simpa using! h1
    omega

theorem generatedTotal_poly_bounds (g : UniformBqpGenerator) :
    ∃ cW dW cS dS : ℕ, ∀ n : ℕ,
      (uniformBqpGeneratedTotal g n).2.length ≤ uniformBqpPolynomial cW dW n ∧
        (uniformBqpGeneratedTotal g n).1 ≤ uniformBqpPolynomial cS dS n := by
  refine ⟨g.timeCoefficient + 1, g.timeDegree + 1, g.timeCoefficient + 1, g.timeDegree + 1, ?_⟩
  intro n
  obtain ⟨h2, h1⟩ := generatedTotal_bit_bound g n
  have h3 : n + uniformBqpTimeBound g n + 1 = n + g.timeCoefficient * (n + 1) ^ g.timeDegree + 1 := by
    rfl
  have h4 := poly_encode_bound g.timeCoefficient g.timeDegree n
  rw [h3] at h1 h2
  exact ⟨h2.trans h4, h1.trans h4⟩

theorem clocked_bitTm {g : UniformBqpGenerator} (h : generatorClocked g) :
    bitTmBackendPremise g := by
  refine ⟨generatorClocked_implies_generatorHaltsEffectively h, ?_⟩
  refine ⟨g.timeCoefficient + 1, g.timeDegree + 1, ?_⟩
  intro n
  obtain ⟨_, h1⟩ := generatedTotal_bit_bound g n
  cases hs : uniformBqpGeneratedAt g n with
  | none =>
    have htot : uniformBqpGeneratedTotal g n = (0, []) := by
      simp [uniformBqpGeneratedTotal, hs]
    rw [htot]
    show (encodeUniformBqpWord 0 []).length ≤ _
    have h5 : (encodeUniformBqpWord 0 []).length = 1 := rfl
    rw [h5]
    show (1 : ℕ) ≤ (g.timeCoefficient + 1) * (n + 1) ^ (g.timeDegree + 1)
    have hp : (1 : ℕ) ≤ (n + 1) ^ (g.timeDegree + 1) := by
      have hpos : 0 < (n + 1) ^ (g.timeDegree + 1) :=
        pow_pos (by omega : 0 < n + 1) (g.timeDegree + 1)
      omega
    have hq : (1 : ℕ) ≤ g.timeCoefficient + 1 := by omega
    simpa using! Nat.mul_le_mul hq hp
  | some w =>
    obtain ⟨q, gs⟩ := w
    have htot : uniformBqpGeneratedTotal g n = (q, gs) := by
      simp [uniformBqpGeneratedTotal, hs]
    rw [htot]
    show (encodeUniformBqpWord q gs).length ≤
      uniformBqpPolynomial (g.timeCoefficient + 1) (g.timeDegree + 1) n
    have hs' : modelGeneratedAt g n = some (q, gs) := by
      rw [modelGeneratedAt_eq]
      exact hs
    unfold modelGeneratedAt at hs'
    obtain ⟨cfg, hrun, hrest⟩ := option_bind_eq_some'.mp hs'
    obtain ⟨bits, hread, hdec⟩ := option_bind_eq_some'.mp hrest
    have hbits : bits = encodeUniformBqpWord q gs := decodeUniformBqpWord_eq_some hdec
    obtain ⟨hlen, _, _⟩ := modelReadOutputUntilBlank_eq_some_iff.mp hread
    have h7 : (encodeUniformBqpWord q gs).length ≤
        n + uniformBqpPolynomial g.timeCoefficient g.timeDegree n + 1 := by
      rw [← hbits]
      exact hlen
    have h6 : n + uniformBqpPolynomial g.timeCoefficient g.timeDegree n + 1
        ≤ uniformBqpPolynomial (g.timeCoefficient + 1) (g.timeDegree + 1) n :=
      poly_encode_bound g.timeCoefficient g.timeDegree n
    omega

def nfAIdx : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

def nfAOfIdx : ℕ → Option Bool
  | 0 => none
  | 1 => some false
  | _ => some true

theorem nfAIdx_lt (a : Option Bool) : nfAIdx a < 3 := by
  cases a with
  | none => decide
  | some b => cases b <;> decide

theorem nfAOfIdx_nfAIdx (a : Option Bool) : nfAOfIdx (nfAIdx a) = a := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl

theorem nfAIdx_nfAOfIdx {i : ℕ} (hi : i < 3) : nfAIdx (nfAOfIdx i) = i := by
  interval_cases i <;> rfl

def nfBound (k : ℕ) : ℕ := 4 * (k + 1) - 1

theorem nfBound_add_one (k : ℕ) : nfBound k + 1 = 4 * (k + 1) := by
  unfold nfBound
  omega

def nfEnterVal (k : ℕ) (q : Fin (k + 1)) : ℕ := q.val

def nfActVal (k : ℕ) (q : Fin (k + 1)) (a : Option Bool) : ℕ := (k + 1) + 3 * q.val + nfAIdx a

theorem nfEnterVal_lt (k : ℕ) (q : Fin (k + 1)) : nfEnterVal k q < nfBound k + 1 := by
  unfold nfEnterVal
  rw [nfBound_add_one]
  have hq := q.isLt
  omega

theorem nfActVal_lt (k : ℕ) (q : Fin (k + 1)) (a : Option Bool) :
    nfActVal k q a < nfBound k + 1 := by
  unfold nfActVal
  rw [nfBound_add_one]
  have hq := q.isLt
  have ha := nfAIdx_lt a
  omega

theorem nfActVal_div (k : ℕ) (q : Fin (k + 1)) (a : Option Bool) :
    (nfActVal k q a - (k + 1)) / 3 = q.val := by
  unfold nfActVal
  have ha := nfAIdx_lt a
  omega

theorem nfActVal_mod (k : ℕ) (q : Fin (k + 1)) (a : Option Bool) :
    (nfActVal k q a - (k + 1)) % 3 = nfAIdx a := by
  unfold nfActVal
  have ha := nfAIdx_lt a
  omega

def nfEnter {k : ℕ} (q : Fin (k + 1)) : Fin (nfBound k + 1) :=
  ⟨nfEnterVal k q, nfEnterVal_lt k q⟩

def nfAct {k : ℕ} (q : Fin (k + 1)) (a : Option Bool) : Fin (nfBound k + 1) :=
  ⟨nfActVal k q a, nfActVal_lt k q a⟩

def nfDecQ (k : ℕ) (s : Fin (nfBound k + 1)) : Fin (k + 1) :=
  ⟨(s.val - (k + 1)) / 3, by
    have h1 : s.val < 4 * (k + 1) := by rw [← nfBound_add_one]; exact s.isLt
    exact Nat.div_lt_of_lt_mul (by omega)⟩

def nfDecA (k : ℕ) (s : Fin (nfBound k + 1)) : Option Bool :=
  nfAOfIdx ((s.val - (k + 1)) % 3)

theorem nfDecQ_nfAct (k : ℕ) (q : Fin (k + 1)) (a : Option Bool) :
    nfDecQ k (nfAct q a) = q := by
  apply Fin.eq_of_val_eq
  simp only [nfDecQ, nfAct]
  exact nfActVal_div k q a

theorem nfDecA_nfAct (k : ℕ) (q : Fin (k + 1)) (a : Option Bool) :
    nfDecA k (nfAct q a) = a := by
  have h1 : (nfAct q a).val = nfActVal k q a := rfl
  unfold nfDecA
  rw [h1, nfActVal_mod]
  exact nfAOfIdx_nfAIdx a

def nfMachine {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1))) :
    TM0.Machine (Option Bool) (Fin (nfBound k + 1)) := fun s a =>
  if hs : s.val < k + 1 then
    (m ⟨s.val, hs⟩ a).map fun _ => ⟨nfAct ⟨s.val, hs⟩ a, TM0.Stmt.write a⟩
  else if a = nfDecA k s then
    (m (nfDecQ k s) (nfDecA k s)).map fun p => ⟨nfEnter p.1, p.2⟩
  else
    some ⟨nfEnter (nfDecQ k s), TM0.Stmt.write a⟩

theorem nfMachine_enter_eq {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (q : Fin (k + 1)) (a : Option Bool) :
    nfMachine m (nfEnter q) a =
      (m q a).map fun _ => ⟨nfAct q a, TM0.Stmt.write a⟩ := by
  unfold nfMachine
  have hcond : (nfEnter q).val < k + 1 := q.isLt
  rw [dif_pos hcond]
  have heq : (⟨(nfEnter q).val, hcond⟩ : Fin (k + 1)) = q := Fin.eq_of_val_eq rfl
  rw [heq]

theorem nfMachine_act_match_eq {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (q : Fin (k + 1)) (a : Option Bool) :
    nfMachine m (nfAct q a) a = (m q a).map fun p => ⟨nfEnter p.1, p.2⟩ := by
  unfold nfMachine
  have hcond : ¬(nfAct q a).val < k + 1 := by
    have hq := q.isLt
    have ha := nfAIdx_lt a
    have hval : (nfAct q a).val = nfActVal k q a := rfl
    rw [hval]
    unfold nfActVal
    omega
  have hiff : a = nfDecA k (nfAct q a) := by rw [nfDecA_nfAct]
  rw [dif_neg hcond, if_pos hiff, nfDecQ_nfAct, nfDecA_nfAct]

theorem nfMachine_act_mismatch_eq {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (q : Fin (k + 1)) (a b : Option Bool) (hab : b ≠ a) :
    nfMachine m (nfAct q a) b = some ⟨nfEnter q, TM0.Stmt.write b⟩ := by
  unfold nfMachine
  have hcond : ¬(nfAct q a).val < k + 1 := by
    have hq := q.isLt
    have ha := nfAIdx_lt a
    have hval : (nfAct q a).val = nfActVal k q a := rfl
    rw [hval]
    unfold nfActVal
    omega
  have hiff : b ≠ nfDecA k (nfAct q a) := by
    rw [nfDecA_nfAct]
    exact hab
  rw [dif_neg hcond, if_neg hiff, nfDecQ_nfAct]

theorem nfMachine_unidirectional {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1))) :
    tm0Unidirectional (nfMachine m) := by
  intro s a b r s' ha hb hra hsb
  obtain ⟨d₁, hd₁⟩ := hra
  obtain ⟨d₂, hd₂⟩ := hsb
  by_cases hs : s.val < k + 1
  · have ha' : nfMachine m s a =
        (m ⟨s.val, hs⟩ a).map fun _ => ⟨nfAct ⟨s.val, hs⟩ a, TM0.Stmt.write a⟩ := by
      unfold nfMachine
      rw [dif_pos hs]
    rw [ha'] at ha
    cases hm : m ⟨s.val, hs⟩ a with
    | none => simp [hm] at ha
    | some p =>
      simp [hm] at ha
      obtain rfl := ha.symm
      simp at hd₁
  · by_cases haa : a = nfDecA k s
    · by_cases hbb : b = nfDecA k s
      · have ha' : nfMachine m s a =
            (m (nfDecQ k s) (nfDecA k s)).map fun p => ⟨nfEnter p.1, p.2⟩ := by
          unfold nfMachine
          rw [dif_neg hs, if_pos haa]
        have hb' : nfMachine m s b =
            (m (nfDecQ k s) (nfDecA k s)).map fun p => ⟨nfEnter p.1, p.2⟩ := by
          unfold nfMachine
          rw [dif_neg hs, if_pos hbb]
        rw [ha'] at ha
        rw [hb'] at hb
        cases hm : m (nfDecQ k s) (nfDecA k s) with
        | none => simp [hm] at ha
        | some p =>
          simp [hm] at ha
          simp [hm] at hb
          obtain rfl := ha.symm
          obtain rfl := hb.symm
          rfl
      · have hb' : nfMachine m s b = some ⟨nfEnter (nfDecQ k s), TM0.Stmt.write b⟩ := by
          unfold nfMachine
          rw [dif_neg hs, if_neg hbb]
        rw [hb'] at hb
        simp at hb
        obtain rfl := hb.symm
        simp at hd₂
    · have ha' : nfMachine m s a = some ⟨nfEnter (nfDecQ k s), TM0.Stmt.write a⟩ := by
        unfold nfMachine
        rw [dif_neg hs, if_neg haa]
      rw [ha'] at ha
      simp at ha
      obtain rfl := ha.symm
      simp at hd₁

def nfEmbed {k : ℕ} (c : TM0.Cfg (Option Bool) (Fin (k + 1))) :
    TM0.Cfg (Option Bool) (Fin (nfBound k + 1)) := ⟨nfEnter c.q, c.Tape⟩

def nfMid {k : ℕ} (c : TM0.Cfg (Option Bool) (Fin (k + 1))) :
    TM0.Cfg (Option Bool) (Fin (nfBound k + 1)) := ⟨nfAct c.q c.Tape.head, c.Tape⟩

theorem nf_step_embed {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (c : TM0.Cfg (Option Bool) (Fin (k + 1))) :
    TM0.step (nfMachine m) (nfEmbed c) = (TM0.step m c).map fun _ => nfMid c := by
  obtain ⟨q, T⟩ := c
  cases h : m q T.head with
  | none =>
    simp [TM0.step, nfEmbed, nfMid, nfMachine_enter_eq, h]
  | some p =>
    obtain ⟨q', st⟩ := p
    simp [TM0.step, nfEmbed, nfMid, nfMachine_enter_eq, h, Tape.write_self]

theorem nf_step_mid {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (c : TM0.Cfg (Option Bool) (Fin (k + 1))) :
    TM0.step (nfMachine m) (nfMid c) = (TM0.step m c).map nfEmbed := by
  obtain ⟨q, T⟩ := c
  cases h : m q T.head with
  | none =>
    simp [TM0.step, nfMid, nfMachine_act_match_eq, h]
  | some p =>
    obtain ⟨q', st⟩ := p
    simp [TM0.step, nfEmbed, nfMid, nfMachine_act_match_eq, h]

theorem nf_step_embed_none_iff {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (c : TM0.Cfg (Option Bool) (Fin (k + 1))) :
    TM0.step (nfMachine m) (nfEmbed c) = none ↔ TM0.step m c = none := by
  rw [nf_step_embed]
  cases TM0.step m c <;> simp

theorem nf_step_mid_ne_none {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (c : TM0.Cfg (Option Bool) (Fin (k + 1))) (hc : TM0.step m c ≠ none) :
    TM0.step (nfMachine m) (nfMid c) ≠ none := by
  rw [nf_step_mid]
  cases h : TM0.step m c with
  | none => exact absurd h hc
  | some ct => simp

theorem nf_embed_init {k : ℕ} (l : List (Option Bool)) :
    nfEmbed (TM0.init l : TM0.Cfg (Option Bool) (Fin (k + 1)))
      = (TM0.init l : TM0.Cfg (Option Bool) (Fin (nfBound k + 1))) :=
  rfl

theorem nf_iterStep_two {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (c : TM0.Cfg (Option Bool) (Fin (k + 1))) :
    iterStep (nfMachine m) (nfEmbed c) 2 = (TM0.step m c).map nfEmbed := by
  rw [iterStep_add1, iterStep_one, nf_step_embed]
  cases hc : TM0.step m c with
  | none => simp
  | some ct => simp [nf_step_mid, hc]

theorem nf_iterStep_even {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (c : TM0.Cfg (Option Bool) (Fin (k + 1))) (t : ℕ) :
    iterStep (nfMachine m) (nfEmbed c) (2 * t) = (iterStep m c t).map nfEmbed := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h2 : 2 * (t + 1) = 2 * t + 2 := by omega
    rw [h2, iterStep_add, ih, iterStep_succ]
    cases hc : iterStep m c t with
    | none => simp
    | some ct => simp [nf_iterStep_two]

theorem nf_iterStep_odd {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (c : TM0.Cfg (Option Bool) (Fin (k + 1))) (t : ℕ) :
    iterStep (nfMachine m) (nfEmbed c) (2 * t + 1) =
      (iterStep m c t).bind fun ct => (TM0.step m ct).map fun _ => nfMid ct := by
  rw [iterStep_add, nf_iterStep_even]
  simp only [iterStep_one]
  cases hc : iterStep m c t with
  | none => simp
  | some ct => simp [nf_step_embed]

theorem nf_bitMachineAfter_even {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (l : List (Option Bool)) (t : ℕ) :
    BitMachineAfter (nfMachine m) l (2 * t) = (BitMachineAfter m l t).map nfEmbed := by
  rw [← iterStep_init_eq_bitMachineAfter (nfMachine m) l (2 * t),
    ← iterStep_init_eq_bitMachineAfter m l t]
  rw [← nf_embed_init (k := k) l]
  exact nf_iterStep_even m (TM0.init l) t

theorem nf_haltsAt_iff {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (l : List (Option Bool)) (t : ℕ) :
    BitMachineHaltsAt (nfMachine m) l (2 * t) ↔ BitMachineHaltsAt m l t := by
  constructor
  · intro h
    obtain ⟨final, hrun, hstop⟩ := h
    rw [nf_bitMachineAfter_even] at hrun
    cases hc : BitMachineAfter m l t with
    | none => simp [hc] at hrun
    | some ct =>
      simp only [hc, Option.map_some] at hrun
      have hfin : final = nfEmbed ct := (Option.some.inj hrun).symm
      subst hfin
      rw [nf_step_embed_none_iff] at hstop
      exact ⟨ct, hc, hstop⟩
  · intro h
    obtain ⟨ct, hrun, hstop⟩ := h
    refine ⟨nfEmbed ct, ?_, ?_⟩
    · simp [nf_bitMachineAfter_even, hrun]
    · exact (nf_step_embed_none_iff m ct).mpr hstop

theorem nf_iterStep_halts {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (c : TM0.Cfg (Option Bool) (Fin (k + 1))) {t' : ℕ}
    {cfg' : TM0.Cfg (Option Bool) (Fin (nfBound k + 1))}
    (hrun : iterStep (nfMachine m) (nfEmbed c) t' = some cfg')
    (hstop : TM0.step (nfMachine m) cfg' = none) :
    ∃ t ct, t' = 2 * t ∧ iterStep m c t = some ct ∧ cfg' = nfEmbed ct ∧
      TM0.step m ct = none := by
  rcases Nat.even_or_odd t' with heven | hodd
  · obtain ⟨t, ht⟩ := heven
    have hte : t' = 2 * t := by omega
    subst hte
    rw [nf_iterStep_even] at hrun
    cases hc : iterStep m c t with
    | none => simp [hc] at hrun
    | some ct =>
      simp only [hc, Option.map_some] at hrun
      have hcfg : cfg' = nfEmbed ct := (Option.some.inj hrun).symm
      subst hcfg
      rw [nf_step_embed_none_iff] at hstop
      exact ⟨t, ct, rfl, hc, rfl, hstop⟩
  · obtain ⟨t, ht⟩ := hodd
    have hte : t' = 2 * t + 1 := by omega
    subst hte
    rw [nf_iterStep_odd] at hrun
    cases hc : iterStep m c t with
    | none => simp [hc] at hrun
    | some ct =>
      simp only [hc, Option.bind_some] at hrun
      cases hs : TM0.step m ct with
      | none => simp [hs] at hrun
      | some ct' =>
        simp only [hs, Option.map_some] at hrun
        have hcfg : cfg' = nfMid ct := (Option.some.inj hrun).symm
        subst hcfg
        rw [nf_step_mid, hs] at hstop
        simp at hstop

theorem nf_runUntilHaltWithin {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1)))
    (l : List (Option Bool)) (F : ℕ) :
    modelRunUntilHaltWithin (nfMachine m) (2 * F) (TM0.init l) =
      (modelRunUntilHaltWithin m F (TM0.init l)).map nfEmbed := by
  cases hc : modelRunUntilHaltWithin m F (TM0.init l) with
  | some ct =>
    obtain ⟨t, hle, hrunm, hstopm⟩ := modelRunUntilHaltWithin_eq_some_iff.mp hc
    refine (modelRunUntilHaltWithin_eq_some_iff
      (m := nfMachine m) (fuel := 2 * F) (cfg0 := TM0.init l)
      (cfgf := nfEmbed ct)).mpr ⟨2 * t, by omega, ?_, ?_⟩
    · rw [← nf_embed_init (k := k) l, nf_iterStep_even, hrunm]
      simp
    · exact (nf_step_embed_none_iff m ct).mpr hstopm
  | none =>
    cases h : modelRunUntilHaltWithin (nfMachine m) (2 * F) (TM0.init l) with
    | none => rfl
    | some cfg' =>
      obtain ⟨t', hle, hrun, hstop⟩ := modelRunUntilHaltWithin_eq_some_iff.mp h
      rw [← nf_embed_init (k := k) l] at hrun
      obtain ⟨t, ct, hte, hrunm, hcfg, hstopm⟩ := nf_iterStep_halts m (TM0.init l) hrun hstop
      have hle' : t ≤ F := by omega
      have hctr : modelRunUntilHaltWithin m F (TM0.init l) = some ct :=
        modelRunUntilHaltWithin_eq_some_iff.mpr ⟨t, hle', hrunm, hstopm⟩
      rw [hctr] at hc
      simp at hc

theorem blank_bound {k : ℕ} (m : TM0.Machine (Option Bool) (Fin (k + 1))) (n : ℕ) :
    ∀ (t : ℕ) (cfg : TM0.Cfg (Option Bool) (Fin (k + 1))),
      BitMachineAfter m (uniformBqpUnaryInput n) t = some cfg →
      ∀ i : ℕ, n + t ≤ i → cfg.Tape.nth (i : ℤ) = none := by
  intro t
  induction t with
  | zero =>
    intro cfg h i hi
    have hcfg : cfg = TM0.init (uniformBqpUnaryInput n) := Option.some.inj h.symm
    subst hcfg
    show (Turing.Tape.mk₁ (uniformBqpUnaryInput n)).nth (i : ℤ) = none
    rw [init_nth (uniformBqpUnaryInput n) (i : ℤ)]
    have hi0 : ¬((i : ℤ) < 0) := by omega
    rw [if_neg hi0, Int.toNat_natCast]
    exact unaryInput_getI_of_le n i hi
  | succ t ih =>
    intro cfg h i hi
    have hbind : (BitMachineAfter m (uniformBqpUnaryInput n) t).bind (TM0.step m)
        = some cfg := h
    obtain ⟨cfg_t, hprev, hstep⟩ := option_bind_eq_some'.mp hbind
    have hblankT : ∀ j : ℕ, n + t ≤ j → cfg_t.Tape.nth (j : ℤ) = none := ih cfg_t hprev
    cases hm : m cfg_t.q cfg_t.Tape.head with
    | none =>
      have hstop : TM0.step m cfg_t = none := (tm0_step_none_iff m cfg_t).mpr hm
      rw [hstop] at hstep
      simp at hstep
    | some p =>
      obtain ⟨q', st⟩ := p
      cases st with
      | move d =>
        cases d with
        | left =>
          have hstep2 : TM0.step m cfg_t = some ⟨q', cfg_t.Tape.move Turing.Dir.left⟩ := by
            simp [TM0.step, hm]
          rw [hstep2] at hstep
          have hcfg : ⟨q', cfg_t.Tape.move Turing.Dir.left⟩ = cfg := Option.some.inj hstep
          subst hcfg
          show (cfg_t.Tape.move Turing.Dir.left).nth (i : ℤ) = none
          rw [Turing.Tape.move_left_nth]
          have hcast : ((i : ℤ) - 1) = ((i - 1 : ℕ) : ℤ) := by omega
          rw [hcast]
          exact hblankT (i - 1) (by omega)
        | right =>
          have hstep2 : TM0.step m cfg_t = some ⟨q', cfg_t.Tape.move Turing.Dir.right⟩ := by
            simp [TM0.step, hm]
          rw [hstep2] at hstep
          have hcfg : ⟨q', cfg_t.Tape.move Turing.Dir.right⟩ = cfg := Option.some.inj hstep
          subst hcfg
          show (cfg_t.Tape.move Turing.Dir.right).nth (i : ℤ) = none
          rw [Turing.Tape.move_right_nth]
          have hcast : ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) := by omega
          rw [hcast]
          exact hblankT (i + 1) (by omega)
      | write b =>
        have hstep2 : TM0.step m cfg_t = some ⟨q', cfg_t.Tape.write b⟩ := by
          simp [TM0.step, hm]
        rw [hstep2] at hstep
        have hcfg : ⟨q', cfg_t.Tape.write b⟩ = cfg := Option.some.inj hstep
        subst hcfg
        show (cfg_t.Tape.write b).nth (i : ℤ) = none
        rw [Turing.Tape.write_nth]
        have hi0 : ¬((i : ℤ) = 0) := by omega
        rw [if_neg hi0]
        exact hblankT i (by omega)

theorem modelReadOutputUntilBlank_exists_of_blank {N : ℕ}
    {tape : Turing.ListBlank (Option Bool)}
    (hblank : ∀ i : ℕ, N ≤ i → tape.nth i = none) :
    ∃ w, modelReadOutputUntilBlank N tape = some w := by
  induction N generalizing tape with
  | zero =>
    refine ⟨[], ?_⟩
    rw [modelReadOutputUntilBlank_zero]
    have h0 : tape.nth 0 = none := hblank 0 (by omega)
    rw [if_pos h0]
  | succ N ih =>
    cases hb : tape.nth 0 with
    | none =>
      refine ⟨[], ?_⟩
      rw [modelReadOutputUntilBlank_succ, hb]
    | some b =>
      have htail : ∀ i : ℕ, N ≤ i → tape.tail.nth i = none := by
        intro j hj
        have h1 := hblank (j + 1) (by omega)
        rw [← ListBlank.nth_succ]
        exact h1
      obtain ⟨w, hw⟩ := ih htail
      refine ⟨b :: w, ?_⟩
      rw [modelReadOutputUntilBlank_succ, hb, hw]
      rfl

theorem modelReadOutputUntilBlank_eq_of_blank_bound {N : ℕ}
    {tape : Turing.ListBlank (Option Bool)}
    (hblank : ∀ i : ℕ, N ≤ i → tape.nth i = none) :
    ∀ B₁ B₂ : ℕ, N ≤ B₁ → N ≤ B₂ →
      modelReadOutputUntilBlank B₁ tape = modelReadOutputUntilBlank B₂ tape := by
  obtain ⟨w, hw⟩ := modelReadOutputUntilBlank_exists_of_blank (N := N) hblank
  intro B₁ B₂ h1 h2
  rw [modelReadOutputUntilBlank_mono (B₁ := N) (B₂ := B₁) h1 tape w hw,
    modelReadOutputUntilBlank_mono (B₁ := N) (B₂ := B₂) h2 tape w hw]

def nfGen (g : UniformBqpGenerator) : UniformBqpGenerator where
  controlBound := nfBound g.controlBound
  machine := nfMachine g.machine
  timeCoefficient := 2 * g.timeCoefficient
  timeDegree := g.timeDegree
  wordCoefficient := g.wordCoefficient
  wordDegree := g.wordDegree
  spaceCoefficient := g.spaceCoefficient
  spaceDegree := g.spaceDegree

theorem nfGen_timeBound (g : UniformBqpGenerator) (n : ℕ) :
    uniformBqpTimeBound (nfGen g) n = 2 * uniformBqpTimeBound g n := by
  simp [uniformBqpTimeBound, uniformBqpPolynomial, nfGen, Nat.mul_assoc]

theorem nfGen_machine (g : UniformBqpGenerator) :
    (nfGen g).machine = nfMachine g.machine :=
  rfl

theorem nfGen_runUntilHaltWithin (g : UniformBqpGenerator) (n : ℕ) :
    modelRunUntilHaltWithin (nfGen g).machine (uniformBqpTimeBound (nfGen g) n)
        (TM0.init (uniformBqpUnaryInput n)) =
      (modelRunUntilHaltWithin g.machine (uniformBqpTimeBound g n)
        (TM0.init (uniformBqpUnaryInput n))).map nfEmbed := by
  rw [nfGen_machine, nfGen_timeBound]
  exact nf_runUntilHaltWithin g.machine (uniformBqpUnaryInput n) (uniformBqpTimeBound g n)

theorem nf_generatedAt (g : UniformBqpGenerator) (n : ℕ) :
    uniformBqpGeneratedAt (nfGen g) n = uniformBqpGeneratedAt g n := by
  show modelGeneratedAt (nfGen g) n = modelGeneratedAt g n
  unfold modelGeneratedAt
  rw [nfGen_runUntilHaltWithin g n, nfGen_timeBound]
  cases hc : modelRunUntilHaltWithin g.machine (uniformBqpTimeBound g n)
      (TM0.init (uniformBqpUnaryInput n)) with
  | none => simp
  | some cfg =>
    obtain ⟨t, hle, hrun, hstop⟩ := modelRunUntilHaltWithin_eq_some_iff.mp hc
    rw [iterStep_init_eq_bitMachineAfter] at hrun
    have hblank : ∀ i : ℕ, n + t ≤ i → cfg.Tape.nth (i : ℤ) = none :=
      blank_bound g.machine n t cfg hrun
    have hblank' : ∀ i : ℕ, n + t ≤ i → cfg.Tape.right₀.nth i = none := by
      intro i hi
      rw [Turing.Tape.right₀_nth]
      exact hblank i hi
    have hread : modelReadOutputUntilBlank (n + 2 * uniformBqpTimeBound g n + 1)
          (nfEmbed cfg).Tape.right₀
        = modelReadOutputUntilBlank (n + uniformBqpTimeBound g n + 1) cfg.Tape.right₀ := by
      have h1 : (nfEmbed cfg).Tape.right₀ = cfg.Tape.right₀ := rfl
      rw [h1]
      exact modelReadOutputUntilBlank_eq_of_blank_bound hblank'
        (n + 2 * uniformBqpTimeBound g n + 1) (n + uniformBqpTimeBound g n + 1)
        (by omega) (by omega)
    show (modelReadOutputUntilBlank (n + 2 * uniformBqpTimeBound g n + 1)
        (nfEmbed cfg).Tape.right₀).bind decodeUniformBqpWord =
      (modelReadOutputUntilBlank (n + uniformBqpTimeBound g n + 1) cfg.Tape.right₀).bind
        decodeUniformBqpWord
    rw [hread]

theorem nfGen_normalForm (g : UniformBqpGenerator) : generatorNormalForm (nfGen g) :=
  nfMachine_unidirectional g.machine

theorem nfGen_wellformed {g : UniformBqpGenerator} (hg : generatorWellformed g) :
    generatorWellformed (nfGen g) := by
  intro n q gs hgen
  rw [nf_generatedAt g n] at hgen
  exact hg n q gs hgen

theorem nfGen_clocked {g : UniformBqpGenerator} (h : generatorClocked g) :
    generatorClocked (nfGen g) := by
  obtain ⟨c, d, hc⟩ := h
  refine ⟨2 * c, d, ?_⟩
  intro n
  obtain ⟨t, ht, hhalts⟩ := hc n
  refine ⟨2 * t, ?_, (nf_haltsAt_iff g.machine (uniformBqpUnaryInput n) t).mpr hhalts⟩
  have h2 : 2 * t ≤ 2 * uniformBqpPolynomial c d n := Nat.mul_le_mul_left 2 ht
  have h3 : uniformBqpPolynomial (2 * c) d n = 2 * uniformBqpPolynomial c d n := by
    simp [uniformBqpPolynomial, Nat.mul_assoc]
  rw [h3]
  exact h2

theorem generatorWellformed_normalForm {g : UniformBqpGenerator}
    (hg : generatorWellformed g) :
    ∃ g' : UniformBqpGenerator, generatorNormalForm g' ∧ generatorWellformed g' ∧
      (∀ n : ℕ, uniformBqpGeneratedAt g' n = uniformBqpGeneratedAt g n) ∧
      (generatorClocked g → generatorClocked g') := by
  refine ⟨nfGen g, nfGen_normalForm g, nfGen_wellformed hg, ?_, ?_⟩
  · intro n
    exact nf_generatedAt g n
  · intro hc
    exact nfGen_clocked hc

theorem clause17 :

  (∀ g : UniformBqpGenerator, uniformBqpGeneratorValid g → generatorWellformed g) ∧

  (∀ g : UniformBqpGenerator, uniformBqpGeneratorValid g → generatorClocked g) ∧

  (∀ g : UniformBqpGenerator, generatorClocked g → generatorHaltsEffectively g) ∧

  (∀ g : UniformBqpGenerator, generatorWellformed g →
    ∃ g' : UniformBqpGenerator, generatorNormalForm g' ∧ generatorWellformed g' ∧
      (∀ n : ℕ, uniformBqpGeneratedAt g' n = uniformBqpGeneratedAt g n) ∧
      (generatorClocked g → generatorClocked g')) ∧

  (generatorWellformed uniformBqpClockGenerator ∧
    (∀ n : ℕ, BitMachineHaltsAt uniformBqpClockGenerator.machine
      (uniformBqpUnaryInput n) n) ∧
      (∀ (n t : ℕ), BitMachineHaltsAt uniformBqpClockGenerator.machine
        (uniformBqpUnaryInput n) t → t = n)) ∧

  (∀ (q : ℕ) (gs : List FiniteGateCode), finiteWordLegal q gs = true →
    finiteWordLegal (duplicateWord q gs).1 (duplicateWord q gs).2 = true ∧
      QueryCount (finiteCodeCircuit (duplicateWord q gs).1 (duplicateWord q gs).2) = 0 ∧
      GateCount (finiteCodeCircuit (duplicateWord q gs).1 (duplicateWord q gs).2) =
        2 * gs.length ∧
      uniformBqpGeneratorValid
        (uniformBqpWordPrinter (duplicateWord q gs).1 (duplicateWord q gs).2) ∧
      (∀ n : ℕ, uniformBqpGeneratedAt
        (uniformBqpWordPrinter (duplicateWord q gs).1 (duplicateWord q gs).2) n =
        some (duplicateWord q gs))) ∧

  (∀ g : UniformBqpGenerator, generatorWellformed g →
    ∀ n : ℕ, finiteWordLegal (uniformBqpGeneratedTotal g n).1
      (uniformBqpGeneratedTotal g n).2 = true) ∧

  (∀ g : UniformBqpGenerator, generatorClocked g →
    ∃ cW dW cS dS : ℕ, ∀ n : ℕ,
      (uniformBqpGeneratedTotal g n).2.length ≤ uniformBqpPolynomial cW dW n ∧
        (uniformBqpGeneratedTotal g n).1 ≤ uniformBqpPolynomial cS dS n) ∧

  (∀ (lam : ℕ) (g : UniformBqpGenerator), generatorWellformed g →
    ∀ n : ℕ, dyadicBackendPremise lam (uniformBqpGeneratedTotal g n)) ∧

  (∀ g : UniformBqpGenerator, generatorWellformed g →
    ∀ n : ℕ, finiteDigitBackendPremise (uniformBqpGeneratedTotal g n)) ∧

  (∀ g : UniformBqpGenerator, generatorClocked g → bitTmBackendPremise g) :=
  ⟨fun _g h => generatorValid_implies_generatorWellformed h,
    fun _g h => generatorValid_implies_generatorClocked h,
    fun _g h => generatorClocked_implies_generatorHaltsEffectively h,
    fun _g h => generatorWellformed_normalForm h,
    ⟨clock_wellformed, clock_haltsAt, fun n t h => (clock_haltsAt_iff n t).mp h⟩,
    fun q gs h => ⟨duplicateWord_legal q gs h, (duplicateWord_counts q gs).1,
      (duplicateWord_counts q gs).2, duplicateWord_printer_valid q gs h,
      fun n => duplicateWord_printer_generatedAt q gs n⟩,
    fun _g h n => wellformed_generatedTotal_legal h n,
    fun _g _ => generatedTotal_poly_bounds _g,
    fun lam _g h n => dyadicBackendPremise_of_legal (wellformed_generatedTotal_legal h n) lam,
    fun _g h n => finiteDigitBackendPremise_of_legal (wellformed_generatedTotal_legal h n),
    fun _g h => clocked_bitTm h⟩

theorem clause16_roundTrip :
    ∀ (q : ℕ) (gs : List FiniteGateCode),
      decodeUniformBqpWord (encodeUniformBqpWord q gs) = some (q, gs) :=
  fun q gs => decode_encodeUniformBqpWord q gs

theorem clause16_nativeToStandard :
    ∀ g : UniformBqpGenerator, uniformBqpGeneratorValid g →
      ∃ W : StandardWordFamily, nativeRealizes g W ∧ standardFamilyLegal W ∧
        ∃ cW dW cS dS : ℕ, standardFamilyBounded cW dW cS dS W :=
  fun _g h => generatorValid_native_to_standard h

theorem clause16_perLengthLedgers :
    ∀ g : UniformBqpGenerator, uniformBqpGeneratorValid g →
      ∀ n : ℕ, ∃ (q : ℕ) (gs : List FiniteGateCode),
        uniformBqpGeneratedAt g n = some (q, gs) ∧
          finiteWordLegal q gs = true ∧
          QueryCount (finiteCodeCircuit q gs) = 0 ∧
          GateCount (finiteCodeCircuit q gs) = gs.length ∧
          gs.length ≤ uniformBqpWordBound g n ∧
          q ≤ uniformBqpSpaceBound g n ∧
          (encodeUniformBqpWord q gs).length ≤ n + uniformBqpTimeBound g n ∧
          ∀ x : Reg q,
            Normalized (uniformBqpRun q gs x) ∧
              0 ≤ uniformBqpAcceptProb q gs x ∧ uniformBqpAcceptProb q gs x ≤ 1 :=
  fun _g h => generatorValid_per_length_ledgers h

theorem clause16_printer_time_bound (q : ℕ) (gs : List FiniteGateCode) (n : ℕ) :
    uniformBqpTimeBound (uniformBqpWordPrinter q gs) n ≤
      (4 * (encodeUniformBqpWord q gs).length + 4) * (n + 1) := by
  rw [wordPrinter_timeBound_eq]
  have h : 3 * (encodeUniformBqpWord q gs).length + 2
      ≤ 4 * (encodeUniformBqpWord q gs).length + 4 := by omega
  exact Nat.mul_le_mul h (le_refl (n + 1))

theorem clause16_standardToNative :
    ∀ (q : ℕ) (gs : List FiniteGateCode), finiteWordLegal q gs = true →
      uniformBqpGeneratorValid (uniformBqpWordPrinter q gs) ∧
        (∀ n : ℕ, uniformBqpGeneratedAt (uniformBqpWordPrinter q gs) n = some (q, gs)) ∧
        (∀ n : ℕ, uniformBqpTimeBound (uniformBqpWordPrinter q gs) n ≤
          (4 * (encodeUniformBqpWord q gs).length + 4) * (n + 1)) :=
  fun q gs h => ⟨printer_valid q gs h, fun n => printer_generatedAt q gs n,
    fun n => clause16_printer_time_bound q gs n⟩

theorem diverging_not_valid : ¬ uniformBqpGeneratorValid uniformBqpDivergingGenerator := by
  intro h
  obtain ⟨q, gs, hg, _⟩ := h 0
  rw [diverging_generatedAt_none] at hg
  simp at hg

theorem clause16_boundary :
    ¬ uniformBqpGeneratorValid uniformBqpDivergingGenerator ∧
      uniformBqpGeneratedTotal uniformBqpDivergingGenerator 0 = (0, []) :=
  ⟨diverging_not_valid, diverging_generatedTotal_zero⟩

end Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp
