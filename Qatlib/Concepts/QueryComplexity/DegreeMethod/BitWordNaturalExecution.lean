/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.CheckedNat
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec

private theorem unary_exact (n : ℕ) (rest markers output : Bits) (v : Local) :
    Stacks.stackRun program (n+1)
      ⟨some .unary,v,Parsing.triple
        (List.replicate n true ++ false::rest) markers output⟩ =
      some ⟨some .field,(false,none),
        Parsing.triple rest (List.replicate n true ++ markers) output⟩ := by
  induction n generalizing markers v with
  | zero => simpa using unary_stop rest markers output v
  | succ n ih =>
    have hh := ih (true::markers) (false,some true)
    rw [show n+1+1=1+(n+1) by omega,Stacks.run_add]
    simp only [List.replicate_succ,List.cons_append,unary_step,Option.bind_some]
    simpa only [Parsing.marker_cons] using hh

private theorem field_exact (bits rest output : Bits) (v : Local) :
    Stacks.stackRun program (bits.length+1)
      ⟨some .field,v,Parsing.triple
        (bits++rest) (List.replicate bits.length true) output⟩ =
      some (fieldFinish bits.length (bits++rest) output v.2) := by
  induction bits generalizing output v with
  | nil =>
    rcases v with ⟨flag,last⟩
    cases last with
    | none => simp [Stacks.stackRun,TM2.step,program,TM2.stepAux,fieldFinish]
    | some b =>
      cases b <;> simp [Stacks.stackRun,TM2.step,program,TM2.stepAux,fieldFinish]
  | cons bit bits ih =>
    have hh := ih (bit::output) (true,some bit)
    rw [show (bit::bits).length+1=1+(bits.length+1) by simp only [List.length_cons]; omega,
      Stacks.run_add]
    simp only [List.length_cons,List.replicate_succ,List.cons_append,
      field_step,Option.bind_some,fieldFinish]
    exact hh

theorem canonical_execution_exact (n : ℕ) (rest output : Bits) (v : Local) :
    Stacks.stackRun program (2*n.bits.length+3)
      ⟨some .unary,v,Parsing.triple (natBits n++rest) [] output⟩ =
      some ⟨none,(true,lastField n.bits none),
        Parsing.triple rest [] (n.bits.reverse++output)⟩ := by
  have hu := unary_exact n.bits.length (n.bits++rest) [] output v
  have hinput : natBits n++rest =
      List.replicate n.bits.length true ++ false::(n.bits++rest) := by
    simp [natBits,List.append_assoc]
  rw [← hinput] at hu
  simp only [List.append_nil] at hu
  have hf := field_exact n.bits rest output (false,none)
  have hlast : lastField n.bits none ≠ some false := by
    rw [lastField_none]
    exact (canonical_iff n.bits).mp (by rw [binaryValue_bits])
  rw [field_data] at hf
  simp only [if_pos hlast] at hf
  have ha : Stacks.stackRun program 1
      ⟨some .accept,(false,lastField n.bits none),
        Parsing.triple rest [] (n.bits.reverse++output)⟩ =
      some ⟨none,(true,lastField n.bits none),
        Parsing.triple rest [] (n.bits.reverse++output)⟩ := by
    rfl
  rw [show 2*n.bits.length+3 = (n.bits.length+1)+(n.bits.length+1)+1 by omega,
    Stacks.run_add,Stacks.run_add,hu,Option.bind_some,hf,Option.bind_some,ha]

end Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.NatReadEmit
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatReadEmit
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec

theorem canonical_execution_exact (n : ℕ) (tail out : Bits) (v : Local) :
    Stacks.stackRun program (7*n.bits.length+10)
      ⟨some (.read .unary),v,store (natBits n++tail) [] [] [] [] out⟩ =
      some ⟨none,((true,CheckedNat.lastField n.bits none),none),
        store tail [] [] n.bits [] ((natBits n).reverse++out)⟩ := by
  have hchecked :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.canonical_execution_exact n tail [] v.1
  simp only [List.append_nil] at hchecked
  obtain ⟨hR,_⟩ := StackCall.execution readCode Label.read (.transfer 0)
    Prod.fst (fun v s => (s,v.2))
    (readFrame [] [] out) (readFrame_at [] [] out) (readFrame_update [] [] out)
    (fun _ _ => rfl) (fun _ _ _ => rfl) CheckedNat.program program
    (fun _ => rfl) v (2*n.bits.length+3) _ _ hchecked
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,
    Option.getD_none,readFrame,Parsing.triple_zero,Parsing.triple_one,
    Parsing.triple_two] at hR
  let v₁ : Local := ((true,CheckedNat.lastField n.bits none),v.2)
  let v₂ : Local := (v₁.1,none)
  have hT := (transfer_call n tail out v₁).1
  have hE := (emit_call n tail out v₂).1
  have hD : Stacks.stackRun program 1
      ⟨some .done,v₂,store tail [] [] n.bits [] ((natBits n).reverse++out)⟩ =
      some ⟨none,((true,CheckedNat.lastField n.bits none),none),
        store tail [] [] n.bits [] ((natBits n).reverse++out)⟩ := by rfl
  rw [show 7*n.bits.length+10 =
      ((2*n.bits.length+3)+(n.bits.length+1))+(4*n.bits.length+5)+1 by omega,
    Stacks.run_add,Stacks.run_add,Stacks.run_add,hR,Option.bind_some,
    hT,Option.bind_some,hE,Option.bind_some,hD]

end Qatlib.Concepts.QueryComplexity.DegreeMethod.NatReadEmit
