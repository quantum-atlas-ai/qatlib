/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionRejection
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionBounds

/-!
# Uniform machine bounds for checked division

This module bounds the statement size, stack execution length, and encoded output length of the
rational division program. It then compiles the stack program to a single finite TM0 machine
with quartic time and quadratic space bounds in `size`, uniformly over signs and operand words.

The theorem `uniform_checked_division_machine` includes both successful cross products and the
failure word selected by the parsed validity flag. The finite machine complexity framework has
background in [KitaevShenVyalyi2002].

## Main statements

* `successSteps_bound`: bounds successful stack execution by `128 * size ^ 2`.
* `uniform_bounded_runs`: transfers suitably bounded stack runs to one TM0 machine.
* `uniform_checked_division_machine`: gives uniform time and space bounds for both outcomes.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatListFind
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.PairZip
open Qatlib.Concepts.RawChannelWord.CptpWordBound
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionOutput
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionMachine
open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib

/-- Embedding a stack statement as a subroutine call preserves its `stackNodes` count. -/
theorem call_nodes {K J Λ Λ' σ ρ : Type} [DecidableEq K] [DecidableEq J]
    (sc : K → J) (lc : Λ → Λ') (ret : Λ') (get : ρ → σ) (put : ρ → σ → ρ)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    stackNodes (StackCall.stmt sc lc ret get put q)=stackNodes q := by
  induction q <;> simp_all only [StackCall.stmt,stackNodes]

/-- Every statement in the multiplication program has at most five stack nodes. -/
theorem mul_program_nodes : ∀l,stackNodes (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program l)≤5 := by
  intro l
  cases l with
  | multiply k =>
    rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,call_nodes]
    cases k <;> norm_num [mulProgram,stackNodes]
  | parse => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,stackNodes]
  | payload => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,stackNodes]
  | multiplier => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,stackNodes]
  | clear => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,stackNodes]
  | output => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,stackNodes]

/-- The maximum stack node count of the division program is at most five. -/
theorem division_program_nodes : programNodes Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program≤5 := by
  apply Finset.sup_le
  intro l _
  cases l with
  | first k =>
    rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,call_nodes]
    exact mul_program_nodes k
  | second k =>
    rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,call_nodes]
    exact mul_program_nodes k
  | invalid p =>
    simp only [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]
    split_ifs <;> norm_num [stackNodes]
  | signA => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]
  | signB => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]
  | parse p => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]
  | payload p => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]
  | last => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]
  | test => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]
  | loadC => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]
  | frameA => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]
  | saveNumerator => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]
  | loadB => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]
  | frameD => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]
  | startOutput => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]
  | numerator => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]
  | reverseDenominator => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]
  | denominator => norm_num [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,stackNodes]

/-- The division program's sweep factor is at most `61`. -/
theorem division_sweepFactor : sweepFactor Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program≤61 := by
  have h := division_program_nodes
  have hh := Nat.mul_le_mul h (Nat.succ_le_succ h)
  dsimp only [sweepFactor]
  nlinarith

/-- The division input size parameter, equal to one plus the sum of the four operand word
lengths. -/
def size (A D B C : Bits) : ℕ := 1+A.length+D.length+B.length+C.length

/-- The multiplication stack step count is at most `32 * (1 + x.length + y.length) ^ 2`. -/
theorem mul_sourceSteps_bound (x y : Bits) :
    sourceSteps x y≤32*(1+x.length+y.length)^2 := by
  let L := 1+x.length+y.length
  have hL : 1≤L := by dsimp [L]; omega
  have hL2 : L≤L^2 := by nlinarith [Nat.mul_le_mul_left L hL]
  have ha := mulAcc_length x y y.length
  have ht := mulTotalTicks_le x y y.length
  have hy : y.length≤L := by dsimp [L]; omega
  have hb : 4*x.length+4*y.length+8≤8*L := by dsimp [L]; omega
  have ht' : mulTotalTicks x y y.length≤8*L^2 := by
    calc _≤y.length*(4*x.length+4*y.length+8) := ht
         _≤L*(8*L) := Nat.mul_le_mul hy hb
         _=8*L^2 := by ring
  have hs : sourceSteps x y ≤ mulTotalTicks x y y.length+6*L := by
    dsimp [sourceSteps,L]; omega
  change sourceSteps x y≤32*L^2
  nlinarith

/-- The successful division stack step count is at most `128 * (size A D B C) ^ 2`. -/
theorem successSteps_bound (A D B C : Bits) :
    successSteps A D B C≤128*(size A D B C)^2 := by
  let L := size A D B C
  have hL : 1≤L := by dsimp [L,size]; omega
  have hL2 : L≤L^2 := by nlinarith [Nat.mul_le_mul_left L hL]
  have hN := mulAcc_length A C C.length
  have hE := mulAcc_length D B B.length
  have hAC : 1+A.length+C.length≤L := by dsimp [L,size]; omega
  have hDB : 1+D.length+B.length≤L := by dsimp [L,size]; omega
  have hcall1 : sourceSteps A C≤32*L^2 :=
    (mul_sourceSteps_bound A C).trans
      (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left hAC 2))
  have hcall2 : sourceSteps D B≤32*L^2 :=
    (mul_sourceSteps_bound D B).trans
      (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left hDB 2))
  have hrest : successSteps A D B C ≤ sourceSteps A C+sourceSteps D B+32*L := by
    dsimp [successSteps,readerSteps,outputSteps,L,size]
    omega
  change successSteps A D B C≤128*L^2
  nlinarith

/-- The division input encoding has length `2 * A.length + 2 * D.length + 2 * B.length +
C.length + 5`. -/
theorem input_length (sa sb : Bool) (A D B C : Bits) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C).length=2*A.length+2*D.length+2*B.length+C.length+5 := by
  simp only [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input,List.length_reverse,List.length_cons,List.length_append,frame_length]
  omega

/-- The successful division output encoding has length `2 * N.length + E.length + 3`. -/
theorem output_length (sa sb : Bool) (N E : Bits) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.output sa sb N E).length=2*N.length+E.length+3 := by
  simp only [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.output,List.length_cons,List.length_append,frame_length]
  omega

/-- The initial division configuration's maximum stack height is bounded by the encoded input
length. -/
theorem initialHeight_bound (sa sb : Bool) (A D B C : Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight ((TM2.init (Sum.inr (4 : Fin 5) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot)
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C).reverse : TM2.Cfg (fun _ : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot => Bool) Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Label Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local).stk)≤
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C).length := by
  apply Finset.sup_le
  intro k _
  by_cases hk : k=Sum.inr (4 : Fin 5)
  · subst k
    simp only [TM2.init,Function.update_self,List.length_reverse,le_refl]
  · simp only [TM2.init,Function.update_of_ne hk,List.length_nil]
    omega

/-- There is a single finite TM0 machine that realizes every clean halted division stack run
with at most `128 * size ^ 2` steps and `1 + out.length ≤ 4 * size`. A uniform positive
constant bounds its time by that constant times `size ^ 4` and its space by that constant
times `size ^ 2`. -/
theorem uniform_bounded_runs :
    ∃ (q : ℕ) (M : TM0.Machine (Option Bool) (Fin (q+1))) (C₀ : ℕ),0<C₀ ∧
      ∀ (sa sb : Bool) (A D B C out : Bits) (n : ℕ),
        n ≤ 128*(size A D B C)^2 →
        1+out.length ≤ 4*size A D B C →
        stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program n
          (TM2.init (Sum.inr (4 : Fin 5) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot) (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C).reverse) =
            some ⟨none,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.init,Function.update (fun _ => []) (Sum.inr (1 : Fin 5) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot) out.reverse⟩ →
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C) out
          (C₀*(size A D B C)^4) (C₀*(size A D B C)^2) := by
  obtain ⟨q,M,D₀,hD₀,hM⟩ := raw_compiler_separate Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program
    (Sum.inr (4 : Fin 5) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot) (Sum.inr (1 : Fin 5) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot)
  let C₀ := D₀*6000000
  refine ⟨q,M,C₀,by dsimp [C₀]; positivity,?_⟩
  intro sa sb A D B C out n hn ho hrun
  let L := size A D B C
  let first : TM2.Cfg (fun _ : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot => Bool) Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Label Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local :=
    TM2.init (Sum.inr (4 : Fin 5) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot) (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C).reverse
  have hL : 1≤L := by dsimp [L,size]; omega
  have hL2 : L≤L^2 := by nlinarith [Nat.mul_le_mul_left L hL]
  have hL24 : L^2≤L^4 := by
    have hh : 1≤L^2 := by simpa using! Nat.pow_le_pow_left hL 2
    calc L^2=L^2*1 := by ring
         _≤L^2*L^2 := Nat.mul_le_mul_left _ hh
         _=L^4 := by ring
  have hi : 1+(Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C).length≤6*L := by
    rw [input_length]
    dsimp [L,size]; omega
  have hH : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk≤5*L := by
    apply (initialHeight_bound sa sb A D B C).trans
    rw [input_length]
    dsimp [L,size]; omega
  have hnode := division_program_nodes
  have hsweep := division_sweepFactor
  have hna :
      n*programNodes Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program≤(128*L^2)*5 := Nat.mul_le_mul hn hnode
  have hheight : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+n*programNodes Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program+1≤646*L^2 := by
    nlinarith
  have hc : stackRunClock Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program n first≤5043968*L^4 := by
    calc
      _≤n*sweepFactor Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program*(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+n*programNodes Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program+1) :=
        runClock_le Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program n first
      _≤(128*L^2)*61*(646*L^2) :=
        Nat.mul_le_mul (Nat.mul_le_mul hn hsweep) hheight
      _=5043968*L^4 := by ring
  have hp : stackRunMaxClock Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program n first≤39406*L^2 := by
    calc
      _ ≤ sweepFactor Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program*(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+n*programNodes Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program+1) :=
        runMaxClock_le Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program n first
      _≤61*(646*L^2) := Nat.mul_le_mul hsweep hheight
      _=39406*L^2 := by ring
  have hi2 : (1+(Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C).length)^2≤36*L^2 := by
    calc _≤(6*L)^2 := Nat.pow_le_pow_left hi 2
         _=36*L^2 := by ring
  have ho2 : (1+out.length)^2≤16*L^2 := by
    calc _≤(4*L)^2 := Nat.pow_le_pow_left ho 2
         _=16*L^2 := by ring
  have ht : (1+(Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C).length)^2+stackRunClock Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program n first+
      (1+out.length)^2≤6000000*L^4 := by
    have hi4 := hi2.trans (Nat.mul_le_mul_left 36 hL24)
    have ho4 := ho2.trans (Nat.mul_le_mul_left 16 hL24)
    nlinarith
  have hspace : (1+(Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C).length)^2+stackRunMaxClock Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program n first+
      (1+out.length)^2≤6000000*L^2 := by nlinarith
  have hr :=
      hM (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C) out n Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.init hrun
  apply runs_mono hr
  · calc _≤D₀*(6000000*L^4) := Nat.mul_le_mul_left D₀ ht
         _=C₀*L^4 := by dsimp [C₀]; ring
  · calc _≤D₀*(6000000*L^2) := Nat.mul_le_mul_left D₀ hspace
         _=C₀*L^2 := by dsimp [C₀]; ring

/-- One plus the successful cross product output length is at most four times the division input
size parameter. -/
theorem success_output_bound (sa sb : Bool) (A D B C : Bits) :
    1+(Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.output sa sb (mulAcc A C C.length) (mulAcc D B B.length)).length ≤ 4*size A D B C := by
  have hN := mulAcc_length A C C.length
  have hE := mulAcc_length D B B.length
  rw [output_length]
  dsimp [size]
  omega

/-- A single finite TM0 machine produces the successful cross product encoding whenever `D`,
`B`, and `C` have positive binary values. A uniform positive constant gives quartic time and
quadratic space bounds in `size A D B C`. -/
theorem uniform_division_machine :
    ∃ (q : ℕ) (M : TM0.Machine (Option Bool) (Fin (q+1))) (C₀ : ℕ),0<C₀ ∧
      ∀ (sa sb : Bool) (A D B C : Bits),
        0<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue D →
        0<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue B →
        0<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue C →
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C)
          (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.output sa sb (mulAcc A C C.length) (mulAcc D B B.length))
          (C₀*(size A D B C)^4) (C₀*(size A D B C)^2) := by
  obtain ⟨q,M,C₀,hC₀,hM⟩ := uniform_bounded_runs
  refine ⟨q,M,C₀,hC₀,?_⟩
  intro sa sb A D B C hD hB hC
  exact hM sa sb A D B C _ _ (successSteps_bound A D B C)
    (success_output_bound sa sb A D B C) (raw_success sa sb A D B C hD hB hC)

/-- The rejecting division stack step count is at most `128 * (size A D B C) ^ 2`. -/
theorem rejectSteps_bound (A D B C : Bits) : rejectSteps A D B C ≤ 128*(size A D B C)^2 := by
  have hL : 1 ≤ size A D B C := by dsimp [size]; omega
  have hL2 : size A D B C ≤ (size A D B C)^2 := by nlinarith
  have hr : rejectSteps A D B C ≤ 16*size A D B C := by
    dsimp [rejectSteps,readerSteps,size]; omega
  nlinarith

/-- A single finite TM0 machine produces the successful cross product encoding when the parsed
validity flag is true and `[false]` otherwise. A uniform positive constant gives quartic
time and quadratic space bounds in the input size parameter. -/
theorem uniform_checked_division_machine :
    ∃ (q : ℕ) (M : TM0.Machine (Option Bool) (Fin (q+1))) (C₀ : ℕ),0<C₀ ∧
      ∀ (sa sb : Bool) (A D B C : Bits),
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.input sa sb A D B C)
          (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing.parsed sa sb A D B C).valid then
            Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.output sa sb (mulAcc A C C.length) (mulAcc D B B.length) else [false])
          (C₀*(size A D B C)^4) (C₀*(size A D B C)^2) := by
  obtain ⟨q,M,C₀,hC₀,hM⟩ := uniform_bounded_runs
  refine ⟨q,M,C₀,hC₀,?_⟩
  intro sa sb A D B C
  cases hv :
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing.parsed sa sb A D B C).valid with
  | true =>
      simp only [if_true]
      apply hM sa sb A D B C _ _ (successSteps_bound A D B C)
        (success_output_bound sa sb A D B C)
      rw [success_run sa sb A D B C hv]
      congr 2
      funext k
      cases k with
      | inl k => simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store,emptyWork]
      | inr k => fin_cases k <;> simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store]
  | false =>
      simp only [Bool.false_eq_true,if_false]
      apply hM sa sb A D B C [false] _ (rejectSteps_bound A D B C)
        (by simp only [List.length_cons,List.length_nil]; dsimp [size]; omega)
      rw [reject_run sa sb A D B C hv]
      congr 2
      funext k
      cases k with
      | inl k => simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store,emptyWork]
      | inr k => fin_cases k <;> simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store]

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionMachine
