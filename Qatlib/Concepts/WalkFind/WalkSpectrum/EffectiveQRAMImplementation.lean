/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
import Qatlib.Concepts.WalkFind.QRAMModel.QRAMImplementation

/-!
# From effective descriptions to QRAM implementation bounds

This module compares source instruction bit costs with the lengths of their explicit
descriptions. The estimates bound both the total bit cost and the instruction count by sums of
squared description lengths.

`qRAMImplementation_of_effective` uses these comparisons to derive `QRAMImplementationContract`
from `EffectiveQRAMImplementationContract` for the collision-search implementation model
[Ambainis2007ElementDistinctness].

## Main statements

* `natDescription_length`: the exact length of a natural-number description.
* `sourceWord_description_budget`: bit and instruction bounds from descriptions.
* `qRAMImplementation_of_effective`: passage from the effective contract to the QRAM contract.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.WalkFind.SearchAlgorithm

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkFind.WalkSpectrum
open scoped Classical BigOperators

/-- The description of `n` has length `2*Nat.clog 2 (n+1)+1`. -/
theorem natDescription_length (n : ℕ) : (natDescription n).length = 2*Nat.clog 2 (n+1)+1 := by
  simp [natDescription]
  omega

/-- The bit cost of a source instruction is at most the length of its explicit description. -/
theorem codeBits_le_description_length (g : SourceCode) : codeBits g ≤ (sourceDescription g).length := by
  cases g with
  | query => simp [codeBits,sourceDescription,natDescription_length,Nat.clog]
  | qram a aw t m ml =>
    simp only [codeBits,sourceDescription,List.length_append,natDescription_length]
    norm_num
    omega
  | «local» g =>
    have hc2 : Nat.clog 2 2 = 1 := by decide
    have hc3 : Nat.clog 2 3 = 2 := by decide
    have hc4 : Nat.clog 2 4 = 2 := by decide
    cases g <;> simp only [codeBits,sourceDescription,gateDescription,List.length_append,natDescription_length,hc2,hc3,hc4] <;>
      norm_num <;> omega

/-- Both the total instruction bit cost and the number of instructions are bounded by the sum of
squared description lengths. -/
theorem sourceWord_description_budget (cs : List SourceCode) :
    (cs.map codeBits).sum ≤ (cs.map (fun g => (sourceDescription g).length^2)).sum ∧
    cs.length ≤ (cs.map (fun g => (sourceDescription g).length^2)).sum := by
  have hlen (g : SourceCode) : 1 ≤ (sourceDescription g).length := by
    cases g <;> simp only [sourceDescription,List.length_append,natDescription_length] <;> omega
  have hsq (g : SourceCode) : (sourceDescription g).length ≤ (sourceDescription g).length^2 := by
    nlinarith [sq_nonneg ((sourceDescription g).length : ℤ)]
  induction cs with
  | nil => simp
  | cons g cs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    constructor
    · exact Nat.add_le_add ((codeBits_le_description_length g).trans (hsq g)) ih.1
    · have hg := (hlen g).trans (hsq g)
      omega

/-- An effective QRAM implementation satisfying its description and execution bounds also
satisfies `QRAMImplementationContract`. -/
theorem qRAMImplementation_of_effective (heffective : EffectiveQRAMImplementationContract) :
    QRAMImplementationContract := by
  intro k hk
  obtain ⟨C,c,seeds,words,hC,hrest⟩ := heffective k hk
  refine ⟨C,c,hC,?_⟩
  intro N M precision _ hN hM hp
  obtain ⟨sb,w,program,hmem,hseed,hprogram,hcorrect⟩ := hrest N M precision hN hM hp
  have hseedbound : (sb : ℝ) ≤ C*(dataBits N M+precision)^c := by
    obtain ⟨steps,_,hsteps⟩ := hseed
    have hs : (sb : ℝ) ≤ (steps+sb : ℕ) := by exact_mod_cast (Nat.le_add_left sb steps)
    exact hs.trans (by simpa only [Nat.cast_add] using! hsteps)
  refine ⟨sb,w,program,hmem,hseedbound,?_,?_,?_⟩
  · intro x
    exact (hcorrect x).1
  · intro s
    obtain ⟨hlegal,hu,hquery,steps,_,hclock⟩ := hprogram s
    have hlen : ((program s).length : ℝ) ≤
        (steps+sb+((program s).map (fun g => (sourceDescription g).length^2)).sum+(program s).length : ℕ) := by
      exact_mod_cast (Nat.le_add_left (program s).length _)
    have hbits := (sourceWord_description_budget (program s)).1
    have hsum : (((program s).map codeBits).sum : ℝ) ≤
        (steps+sb+((program s).map (fun g => (sourceDescription g).length^2)).sum+(program s).length : ℕ) := by
      exact_mod_cast (show ((program s).map codeBits).sum ≤ _ by omega)
    exact ⟨hlegal,hu,hquery,hlen.trans (by simpa only [Nat.cast_add] using! hclock),
      hsum.trans (by simpa only [Nat.cast_add] using! hclock)⟩
  · intro x
    exact (hcorrect x).2

end Qatlib.Concepts.WalkFind.WalkSpectrum
