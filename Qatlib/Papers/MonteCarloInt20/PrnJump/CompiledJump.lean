/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.SharedLayout
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore
open scoped Classical ENNReal
namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled
open Qatlib.Papers.MonteCarloInt20.PrnJump.Lcg
open Qatlib.Papers.MonteCarloInt20.PrnJump.NativeArithmetic
open Qatlib.Papers.MonteCarloInt20.PrnJump.Shared
open Qatlib.Papers.MonteCarloInt20.PrnJump.Affine

abbrev width (n k : ℕ) := ((n+1)+k)+max (mulScratch (n+1) k) (addScratch (n+1) k)+((n+1)+k)

def frame {n k : ℕ} (bits : Reg k) (x : ZMod (2^n)) : Reg (width n k) :=
  booleanDAGInput ((n+1)+k) (commonScratch (n+1) k) ((n+1)+k)
    (Fin.append (encode n x) bits) (fun _ => false)

theorem mul_basis {n k : ℕ} (q : Fin k) (a : (ZMod (2^n))ˣ) (x : ZMod (2^n)) (bits : Reg k) :
    Run 1 (reflectionCompile (commonMul (n+1) k q (encode n (a:ZMod (2^n))) (modulusBits n)))
      (Ket (frame bits x)) = Ket (frame bits (if bits q then (a:ZMod (2^n))*x else x)) := by
  have hc : (booleanWordLSBValue (n+1) (encode n (a:ZMod (2^n)))).Coprime
      (booleanWordLSBValue (n+1) (modulusBits n)) := by
    rw [encode_value,modulus_value]
    exact ZMod.val_coe_unit_coprime a
  have h :=
      common_mul_basis (n+1) k q (encode n (a:ZMod (2^n))) (modulusBits n) (encode n x) bits hc
  simp only [native_mul_value] at h
  by_cases hb : bits q = true
  · simpa only [frame,hb,ite_true] using! h
  · have hb' : bits q = false := Bool.eq_false_iff.mpr hb
    simpa only [frame,hb',Bool.false_eq_true,ite_false] using! h

theorem add_basis {n k : ℕ} (q : Fin k) (c x : ZMod (2^n)) (bits : Reg k) :
    Run 1 (reflectionCompile (commonAdd (n+1) k q (encode n c) (modulusBits n)))
      (Ket (frame bits x)) = Ket (frame bits (if bits q then x+c else x)) := by
  have h := common_add_basis (n+1) k q (encode n c) (modulusBits n) (encode n x) bits
  simp only [native_add_value] at h
  by_cases hb : bits q = true
  · simpa only [frame,hb,ite_true] using! h
  · have hb' : bits q = false := Bool.eq_false_iff.mpr hb
    simpa only [frame,hb',Bool.false_eq_true,ite_false] using! h

noncomputable def rung {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) (q : Fin k) :
    List (ReflectionGate (width n k)) :=
  commonMul (n+1) k q (encode n ((powerPair n a c q.val).1:ZMod (2^n))) (modulusBits n) ++
  commonAdd (n+1) k q (encode n (powerPair n a c q.val).2) (modulusBits n)

theorem rung_basis {n k : ℕ} (a : (ZMod (2^n))ˣ) (c x : ZMod (2^n)) (q : Fin k) (bits : Reg k) :
    Run 1 (reflectionCompile (rung a c q)) (Ket (frame bits x)) =
      Ket (frame bits (if bits q then lcg (a:ZMod (2^n)) c x (2^q.val) else x)) := by
  have hp : reflectionCompile (rung a c q) =
      reflectionCompile (commonMul (n+1) k q (encode n ((powerPair n a c q.val).1:ZMod (2^n))) (modulusBits n)) ++
      reflectionCompile (commonAdd (n+1) k q (encode n (powerPair n a c q.val).2) (modulusBits n)) :=
    List.map_append
  have hr := run_append (I := Reg (width n k)) (1 : Matrix (Reg (width n k)) (Reg (width n k)) ℂ)
    (reflectionCompile (commonMul (n+1) k q (encode n ((powerPair n a c q.val).1:ZMod (2^n))) (modulusBits n)))
    (reflectionCompile (commonAdd (n+1) k q (encode n (powerPair n a c q.val).2) (modulusBits n)))
    (Ket (frame bits x))
  rw [hp,hr,mul_basis,add_basis]
  by_cases hb : bits q = true
  · simp only [hb,ite_true,powerPair_apply]
  · have hb' : bits q = false := Bool.eq_false_iff.mpr hb
    simp only [hb',Bool.false_eq_true,ite_false]

noncomputable def nativeWord {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) (qs : List (Fin k)) :
    List (ReflectionGate (width n k)) := qs.flatMap (rung a c)

theorem native_basis {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n))
    (qs : List (Fin k)) (bits : Reg k) (x : ZMod (2^n)) :
    Run 1 (reflectionCompile (nativeWord a c qs)) (Ket (frame bits x)) =
      Ket (frame bits (lcg (a:ZMod (2^n)) c x (exponent qs bits))) := by
  induction qs generalizing x with
  | nil => simp [nativeWord,reflectionCompile,exponent,lcg,run_nil]
  | cons q qs ih =>
    change Run 1 (reflectionCompile (rung a c q ++ nativeWord a c qs)) _ = _
    rw [reflectionCompile_append,run_append,rung_basis]
    cases h : bits q
    · simpa [exponent,h] using! ih x
    · rw [ih]
      simp only [exponent,List.map_cons,List.sum_cons,h,if_true,lcg_restart]

theorem full_native_basis {n k : ℕ} (a : (ZMod (2^n))ˣ) (c x : ZMod (2^n)) (bits : Reg k) :
    Run 1 (reflectionCompile (nativeWord a c (List.ofFn (fun q : Fin k => q)))) (Ket (frame bits x)) =
      Ket (frame bits (lcg (a:ZMod (2^n)) c x (booleanWordLSBValue k bits))) := by
  simpa only [exponent_all] using! native_basis a c (List.ofFn (fun q : Fin k => q)) bits x

theorem strided_native_basis (n s d : ℕ) (hd : 0<d) (a : (ZMod (2^n))ˣ) (c x : ZMod (2^n))
    (j : Fin (2^s)) (i : Fin (2^d+1)) :
    let bits := Bits.ofNat (s+d+1) (strided (2^d) j i)
    Run 1 (reflectionCompile (nativeWord a c (List.ofFn (fun q : Fin (s+d+1) => q)))) (Ket (frame bits x)) =
      Ket (frame bits (lcg (a:ZMod (2^n)) c x (strided (2^d) j i))) := by
  (try dsimp only)
  rw [full_native_basis,Bits.ofNat_value,Nat.mod_eq_of_lt (strided_bit_bound s d hd j i)]

def rungBound (n k : ℕ) := 6660*(n+1)^2+5770*(n+1)+370*k+2400

theorem rung_resources {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) (q : Fin k) :
    reflectionLegal (rung a c q) ∧ (rung a c q).length ≤ rungBound n k := by
  let aa := encode n ((powerPair n a c q.val).1:ZMod (2^n))
  let cc := encode n (powerPair n a c q.val).2
  have hm := Qatlib.Papers.MonteCarloInt20.PrnJump.Shared.mul_resources (n+1) k q aa (modulusBits n)
  have ha := Qatlib.Papers.MonteCarloInt20.PrnJump.Shared.add_resources (n+1) k q cc (modulusBits n)
  have hmp := padded_resources (Nat.le_max_left (mulScratch (n+1) k) (addScratch (n+1) k)) _ hm.1
  have hap := padded_resources (Nat.le_max_right (mulScratch (n+1) k) (addScratch (n+1) k)) _ ha.1
  refine ⟨(reflectionLegal_append _ _).mpr ⟨hmp.1,hap.1⟩,?_⟩
  change (commonMul (n+1) k q aa (modulusBits n) ++ commonAdd (n+1) k q cc (modulusBits n)).length ≤ _
  rw [List.length_append]
  change (paddedWord _ _).length+(paddedWord _ _).length ≤ _
  rw [hmp.2.1,hap.2.1]
  dsimp only [rungBound]
  omega

theorem native_resources {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) (qs : List (Fin k)) :
    reflectionLegal (nativeWord a c qs) ∧
    (nativeWord a c qs).length ≤ qs.length*rungBound n k ∧
    QueryCount (reflectionCompile (nativeWord a c qs)) = 0 ∧
    GateCount (reflectionCompile (nativeWord a c qs)) = (nativeWord a c qs).length := by
  have h : reflectionLegal (nativeWord a c qs) ∧ (nativeWord a c qs).length ≤ qs.length*rungBound n k := by
    induction qs with
    | nil => exact ⟨by intro g hg; simp [nativeWord] at hg,by simp [nativeWord]⟩
    | cons q qs ih =>
      have hr := rung_resources a c q
      refine ⟨(reflectionLegal_append _ _).mpr ⟨hr.1,ih.1⟩,?_⟩
      change (rung a c q ++ nativeWord a c qs).length ≤ (qs.length+1)*rungBound n k
      rw [List.length_append,Nat.add_mul,Nat.one_mul]
      omega
  exact ⟨h.1,h.2,queryCount_reflectionCompile _,gateCount_reflectionCompile _⟩

theorem native_unitary {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) (qs : List (Fin k)) :
    IsUnitaryCircuit (reflectionCompile (nativeWord a c qs)) :=
  (local_reflection_gate_support_unitarity_counts _ _ (native_resources a c qs).1).1

theorem native_inverse {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) (qs : List (Fin k)) :
    reflectionProgramMatrix (reflectionAdjoint (nativeWord a c qs))*reflectionProgramMatrix (nativeWord a c qs)=1 ∧
    (reflectionAdjoint (nativeWord a c qs)).length = (nativeWord a c qs).length := by
  refine ⟨?_,reflectionAdjoint_length _⟩
  rw [reflectionAdjoint_matrix _ (native_resources a c qs).1]
  exact Matrix.mem_unitaryGroup_iff'.mp
      (reflectionProgramMatrix_unitary _ (native_resources a c qs).1)
end Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled
