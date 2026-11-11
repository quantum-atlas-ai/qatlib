/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionMachine

/-!
# Binary products for square-root preparation

The register-preserving multiplication `program` copies two source words, computes their
product, and writes an initially empty destination while clearing its working stacks. The
`Preprocess` program composes four such calls to form the integer numerator and denominator used
by square-root preparation.

The preprocessing outputs represent `qN * sD^2` and `qD * sN^2` under binary evaluation. The
construction supplies explicit quartic execution bounds; see [KitaevShenVyalyi2002] for the
classical computational background.

## Main statements

* `complete`: correctness and a quartic execution bound for multiplication into an empty
  destination.
* `Preprocess.result_value`: the numerical values of the two preprocessing products.
* `Preprocess.complete_bound`: a quartic bound in the combined input-word lengths.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct
open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib

/-- The eight registers used for rational square-root preprocessing. -/
abbrev Register := Fin 8
/-- Six multiplication workspace stacks together with a family of external registers. -/
abbrev SlotOf (K : Type) := Fin 6 ⊕ K
/-- The multiplication workspace and the eight preprocessing registers. -/
abbrev Slot := SlotOf Register
/-- The multiplication-local state paired with an input/output symbol register. -/
abbrev Local := MulVar × Symbol

/-- Control labels for copying factors, multiplying, moving the result, clearing workspace, and
halting. -/
inductive Label where
  | copy (which : Bool) (l : NatEmit.Label)
  | multiply (l : MulLabel)
  | move (which : Bool) (l : Fin 1)
  | clear (l : Fin 1)
  | done
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.copy false .emit⟩

/-- Replaces the multiplication-local component while preserving the symbol register. -/
def putMul (v : Local) (w : MulVar) : Local := (w,v.2)
/-- Replaces the symbol register while preserving the multiplication-local state. -/
def putIO (v : Local) (w : Symbol) : Local := (v.1,w)

section ArbitraryRegisters
variable {K : Type} [DecidableEq K]

/-- Maps a copy subroutine to a source register, its temporary stack, and the selected factor
stack. -/
def copyCode (src : K) (which : Bool) : Fin 3 → (SlotOf K)
  | 0 => .inr src
  | 1 => .inl 2
  | _ => .inl (if which then 4 else 3)

/-- Maps a transfer subroutine to the intermediate product stacks or the destination register. -/
def moveCode (dst : K) (which : Bool) : Fin 2 → (SlotOf K)
  | 0 => .inl (if which then 1 else 0)
  | _ => if which then .inr dst else .inl 1

/-- Selects the factor workspace stack cleared after multiplication. -/
def clearCode (_ : Fin 1) : (SlotOf K) := .inl 3

/-- Selects the second factor copy or the multiplication phase after a factor copy. -/
def nextCopy (which : Bool) : Label := if which then .multiply .outer else .copy true .emit
/-- Selects the next product transfer or the workspace-cleanup phase. -/
def nextMove (which : Bool) : Label := if which then .clear 0 else .move true 0

/-- The program that copies two source registers, multiplies them, writes the destination, and
clears its workspace. -/
def program (x y dst : K) : Label → TM2.Stmt (fun _ : (SlotOf K) => Bool) Label Local
  | .copy which l => StackCall.stmt (copyCode (if which then y else x) which)
      (Label.copy which) (nextCopy which) Prod.snd putIO (NatEmit.program l)
  | .multiply l => StackCall.stmt Sum.inl Label.multiply (.move false 0)
      Prod.fst putMul (mulProgram l)
  | .move which l => StackCall.stmt (moveCode dst which) (Label.move which) (nextMove which)
      Prod.snd putIO (transferProgram l)
  | .clear l => StackCall.stmt clearCode Label.clear .done Prod.snd putIO
      (Normalization.drainProgram l)
  | .done => .load (fun _ => (MulVar.init,none)) .halt

/-- Combines the six working stacks with the external register store. -/
def store (working : Fin 6 → Bits) (registers : K → Bits) : (SlotOf K) → Bits :=
  Sum.elim working registers

omit [DecidableEq K] in

/-- The stack map for copying either factor is injective. -/
theorem copyCode_injective (src : K) (which : Bool) :
    Function.Injective (copyCode src which) := by
  intro a b h
  cases which <;> fin_cases a <;> fin_cases b <;> simp [copyCode] at h ⊢

omit [DecidableEq K] in

/-- The stack map for either product transfer is injective. -/
theorem moveCode_injective (dst : K) (which : Bool) :
    Function.Injective (moveCode dst which) := by
  intro a b h
  cases which <;> fin_cases a <;> fin_cases b <;> simp [moveCode] at h ⊢

/-- Copying a factor preserves its source and prepends its reversal to the selected factor
stack, with the stated step count and quadratic clock bound. -/
theorem copy_call (x y dst : K) (which : Bool) (S : (SlotOf K) → Bits) (v : Local)
    (htmp : S (.inl 2)=[]) :
    let src := if which then y else x
    let target : (SlotOf K) := .inl (if which then 4 else 3)
    let bits := S (.inr src)
    stackRun (program x y dst) (2*bits.length+3)
      ⟨some (.copy which .emit),v,S⟩ =
      some ⟨some (nextCopy which),putIO v none,
        Function.update S target (bits.reverse++S target)⟩ ∧
    stackRunClock (program x y dst) (2*bits.length+3)
      ⟨some (.copy which .emit),v,S⟩ ≤
      25*(1+bits.length+(S target).length)^2 := by
  (try dsimp only)
  let code := copyCode (if which then y else x) which
  let bits := S (.inr (if which then y else x))
  let target : (SlotOf K) := .inl (if which then 4 else 3)
  let initial := Parsing.triple bits [] (S target)
  have hinj := copyCode_injective (if which then y else x) which
  have hsame : StackCall.frame code S initial=S := by
    apply StackCall.frame_same _ _ _ hinj
    intro i
    fin_cases i <;> simp [initial,copyCode,bits,target,htmp]
  have ht : Parsing.triple bits [] (bits.reverse++S target) =
      Function.update initial (2 : Fin 3) (bits.reverse++S target) := by
    funext i
    fin_cases i <;> simp [initial,Parsing.triple]
  have hfinal : StackCall.frame code S (Parsing.triple bits [] (bits.reverse++S target)) =
      Function.update S target (bits.reverse++S target) := by
    rw [ht,StackCall.frame_update _ _ _ hinj,hsame]
    rfl
  dsimp only [initial] at hsame
  obtain ⟨hr,hc⟩ := StackCall.execution code (Label.copy which) (nextCopy which) Prod.snd putIO
    (StackCall.frame code S) (fun data j => StackCall.frame_at _ _ data hinj j)
    (fun data j w => StackCall.frame_update _ _ data hinj j w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) NatEmit.program (program x y dst)
    (fun _ => rfl) v _ _ _ (NatEmit.copy_complete bits (S target) v.2).1
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    hsame,hfinal,putIO,Prod.mk.eta] at hr hc
  exact ⟨hr,hc.trans_le (NatEmit.copy_clock_bound bits (S target) v.2)⟩

/-- The fixed constant used in the quartic clock bound for binary multiplication. -/
noncomputable def mulClockConstant : ℕ := 10*sweepFactor mulProgram*(10*programNodes mulProgram+2)

/-- Binary multiplication has clock cost at most `mulClockConstant * (1 + a.length +
b.length)^4`. -/
theorem mul_clock_bound (a b : Bits) :
    stackRunClock mulProgram (mulTotalTicks a b b.length+2) (mulStart a b) ≤
      mulClockConstant*(1+a.length+b.length)^4 := by
  let N := 1+a.length+b.length
  have hN : 1 ≤ N := by dsimp [N]; omega
  have ha : a.length ≤ N := by dsimp [N]; omega
  have hb : b.length ≤ N := by dsimp [N]; omega
  have hInner : 4*a.length+4*b.length+8 ≤ 8*N := by dsimp [N]; omega
  have hT := Qatlib.Concepts.QueryComplexity.DegreeMethod.mulTotalTicks_le a b b.length
  have hT' := Nat.mul_le_mul hb hInner
  have hN2 : N ≤ N^2 := by nlinarith
  have hOne : 1 ≤ N^2 := by nlinarith
  have ht : mulTotalTicks a b b.length+2 ≤ 10*N^2 := by nlinarith
  have hH : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (mulStart a b).stk ≤ N := by
    apply Finset.sup_le
    intro k _
    fin_cases k <;> simp [mulStart,mulStacks,List.length_reverse] <;> omega
  have h := Qatlib.Concepts.QueryComplexity.DegreeMethod.runClock_le mulProgram
    (mulTotalTicks a b b.length+2) (mulStart a b)
  have hP := Nat.mul_le_mul_right (programNodes mulProgram) ht
  have hHeight : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (mulStart a b).stk+
      (mulTotalTicks a b b.length+2)*programNodes mulProgram+1 ≤
      (10*programNodes mulProgram+2)*N^2 := by nlinarith
  calc
    _ ≤ (mulTotalTicks a b b.length+2)*sweepFactor mulProgram*
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (mulStart a b).stk+(mulTotalTicks a b b.length+2)*programNodes mulProgram+1) := h
    _ ≤ (10*N^2)*sweepFactor mulProgram*((10*programNodes mulProgram+2)*N^2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ ht) hHeight
    _ = _ := by dsimp [mulClockConstant,N]; ring

/-- The embedded multiplication computes the product accumulator and enters result transfer
while preserving external registers, with a quartic clock bound. -/
theorem multiply_call (x y dst : K) (a b : Bits) (R : K → Bits) (v : Local) :
    stackRun (program x y dst) (mulTotalTicks a b b.length+2)
      ⟨some (.multiply .outer),putMul v MulVar.init,
        store (mulStacks [] [] [] a.reverse b.reverse []) R⟩ =
      some ⟨some (.move false 0),putMul v MulVar.init,
        store (mulStacks (mulAcc a b b.length) [] [] a.reverse [] []) R⟩ ∧
    stackRunClock (program x y dst) (mulTotalTicks a b b.length+2)
      ⟨some (.multiply .outer),putMul v MulVar.init,
        store (mulStacks [] [] [] a.reverse b.reverse []) R⟩ ≤
      mulClockConstant*(1+a.length+b.length)^4 := by
  obtain ⟨hr,hc⟩ := StackCall.execution Sum.inl Label.multiply (.move false 0) Prod.fst putMul
    (fun S => store S R) (fun _ _ => rfl)
    (fun S k w => by simpa only [store,StackCall.leftFrame] using! StackCall.leftFrame_update R S k w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) mulProgram (program x y dst) (fun _ => rfl)
    v _ _ _ (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExecution.mul_halt a b)
  simp only [StackCall.cfg,mulStart,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none] at hr hc
  exact ⟨hr,hc.trans_le (mul_clock_bound a b)⟩

/-- A product-transfer phase empties its source stack and prepends the reversed source to its
destination, with a quadratic clock bound. -/
theorem move_call (x y dst : K) (which : Bool) (S : (SlotOf K) → Bits) (v : Local) :
    let code := moveCode dst which
    let bits := S (code 0)
    let out := S (code 1)
    stackRun (program x y dst) (bits.length+1) ⟨some (.move which 0),v,S⟩ =
      some ⟨some (nextMove which),putIO v none,
        Function.update (Function.update S (code 0) []) (code 1) (bits.reverse++out)⟩ ∧
    stackRunClock (program x y dst) (bits.length+1) ⟨some (.move which 0),v,S⟩ ≤
      10*(1+bits.length+out.length)^2 := by
  (try dsimp only)
  let code := moveCode dst which
  let bits := S (code 0)
  let out := S (code 1)
  have hinj := moveCode_injective dst which
  have hsame : StackCall.frame code S (stackPair bits out)=S := by
    apply StackCall.frame_same _ _ _ hinj
    intro i
    fin_cases i <;> rfl
  have ht : stackPair [] (bits.reverse++out) =
      Function.update (Function.update (stackPair bits out) (0 : Fin 2) []) 1 (bits.reverse++out) := by
    funext i
    fin_cases i <;> rfl
  have hfinal : StackCall.frame code S (stackPair [] (bits.reverse++out)) =
      Function.update (Function.update S (code 0) []) (code 1) (bits.reverse++out) := by
    rw [ht,StackCall.frame_update _ _ _ hinj,StackCall.frame_update _ _ _ hinj,hsame]
  obtain ⟨hr,hc⟩ := StackCall.execution code (Label.move which) (nextMove which) Prod.snd putIO
    (StackCall.frame code S) (fun data j => StackCall.frame_at _ _ data hinj j)
    (fun data j w => StackCall.frame_update _ _ data hinj j w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) transferProgram (program x y dst) (fun _ => rfl)
    v _ _ _ (transfer_run bits out v.2)
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    hsame,hfinal,putIO,Prod.mk.eta] at hr hc
  refine ⟨hr,?_⟩
  rw [hc,transfer_clock]
  nlinarith

/-- The cleanup phase empties the remaining factor stack and enters the final label with a
quadratic clock bound. -/
theorem clear_call (x y dst : K) (S : (SlotOf K) → Bits) (v : Local) :
    stackRun (program x y dst) ((S (.inl 3)).length+1) ⟨some (.clear 0),v,S⟩ =
      some ⟨some .done,putIO v none,Function.update S (.inl 3) []⟩ ∧
    stackRunClock (program x y dst) ((S (.inl 3)).length+1) ⟨some (.clear 0),v,S⟩ ≤
      10*(1+(S (.inl 3)).length)^2 := by
  have hinj : Function.Injective (clearCode (K:=K)) := fun a b _ => Subsingleton.elim a b
  have hsame : StackCall.frame clearCode S (Normalization.singleStack (S (.inl 3)))=S := by
    apply StackCall.frame_same _ _ _ hinj
    intro i
    fin_cases i
    rfl
  have ht : Normalization.singleStack [] =
      Function.update (Normalization.singleStack (S (.inl 3))) (0 : Fin 1) [] := by
    funext i
    fin_cases i
    rfl
  have hfinal : StackCall.frame clearCode S (Normalization.singleStack []) =
      Function.update S (.inl 3) [] := by
    rw [ht,StackCall.frame_update _ _ _ hinj,hsame]
    rfl
  obtain ⟨hr,hc⟩ := StackCall.execution clearCode Label.clear .done Prod.snd putIO
    (StackCall.frame clearCode S) (fun data j => StackCall.frame_at _ _ data hinj j)
    (fun data j w => StackCall.frame_update _ _ data hinj j w)
    (fun _ _ => rfl) (fun _ _ _ => rfl) Normalization.drainProgram (program x y dst) (fun _ => rfl)
    v _ _ _ (Normalization.drain_run (S (.inl 3)) v.2)
  simp only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    hsame,hfinal,putIO,Prod.mk.eta] at hr hc
  refine ⟨hr,?_⟩
  rw [hc,Normalization.drain_clock]
  nlinarith

/-- Updating a working stack in the combined store updates only its working-store component. -/
theorem store_update_left (S : Fin 6 → Bits) (R : K → Bits) (i : Fin 6) (bits : Bits) :
    Function.update (store S R) (.inl i) bits=store (Function.update S i bits) R := by
  funext slot
  cases slot <;> simp [store]

/-- Updating an external register in the combined store updates only its register-store
component. -/
theorem store_update_right (S : Fin 6 → Bits) (R : K → Bits) (i : K) (bits : Bits) :
    Function.update (store S R) (.inr i) bits=store S (Function.update R i bits) := by
  funext slot
  cases slot <;> simp [store]

/-- With an empty destination, multiplication writes the product accumulator there and halts
with empty workspace within the stated quartic execution bound. -/
theorem complete (x y dst : K) (R : K → Bits) (hempty : R dst=[]) :
    Execution (program x y dst)
      ⟨some (.copy false .emit),(MulVar.init,none),store (fun _ => []) R⟩
      ⟨none,(MulVar.init,none),
        store (fun _ => []) (Function.update R dst (mulAcc (R x) (R y) (R y).length))⟩
      ((mulClockConstant+1000)*(1+(R x).length+(R y).length)^4) := by
  let a := R x
  let b := R y
  let p := mulAcc a b b.length
  let v : Local := (MulVar.init,none)
  let S0 := store (fun _ => []) R
  let S1 := Function.update S0 (.inl 3) a.reverse
  let S2 := Function.update S1 (.inl 4) b.reverse
  let S3 := store (mulStacks p [] [] a.reverse [] []) R
  let S4 := Function.update (Function.update S3 (.inl 0) []) (.inl 1) p.reverse
  let S5 := Function.update (Function.update S4 (.inl 1) []) (.inr dst) p
  let S6 := Function.update S5 (.inl 3) []
  have hS2 : S2=store (mulStacks [] [] [] a.reverse b.reverse []) R := by
    funext slot
    cases slot with
    | inl i => fin_cases i <;> rfl
    | inr i => rfl
  have hS6 : S6=store (fun _ => []) (Function.update R dst p) := by
    funext slot
    cases slot with
    | inl i => fin_cases i <;> rfl
    | inr i => simp only [S6,S5,S4,S3,store,Function.update_apply,Sum.elim_inr,Sum.inr.injEq,Sum.inr_ne_inl,↓reduceIte]
  have h00 : S0 (.inr x)=a := rfl
  have h03 : S0 (.inl 3)=[] := rfl
  have h1y : S1 (.inr y)=b := rfl
  have h14 : S1 (.inl 4)=[] := rfl
  have h0 := copy_call x y dst false S0 v rfl
  have h1 := copy_call x y dst true S1 v (by rfl)
  have e0 : Execution (program x y dst) ⟨some (.copy false .emit),v,S0⟩
      ⟨some (.copy true .emit),v,S1⟩ (25*(1+a.length)^2) := by
    refine ⟨2*a.length+3,?_,?_⟩
    · simpa only [nextCopy,Bool.false_eq_true,↓reduceIte,h00,h03,List.append_nil] using! h0.1
    · simpa only [Bool.false_eq_true,↓reduceIte,List.length_nil,Nat.add_zero] using! h0.2
  have e1 : Execution (program x y dst) ⟨some (.copy true .emit),v,S1⟩
      ⟨some (.multiply .outer),v,S2⟩ (25*(1+b.length)^2) := by
    refine ⟨2*b.length+3,?_,?_⟩
    · simpa only [nextCopy,↓reduceIte,h1y,h14,List.append_nil] using! h1.1
    · simpa only [↓reduceIte,List.length_nil,Nat.add_zero] using! h1.2
  have hM := multiply_call x y dst a b R v
  have e2 : Execution (program x y dst) ⟨some (.multiply .outer),v,S2⟩
      ⟨some (.move false 0),v,S3⟩ (mulClockConstant*(1+a.length+b.length)^4) := by
    refine ⟨mulTotalTicks a b b.length+2,?_,?_⟩
    · rw [hS2]
      exact hM.1
    · rw [hS2]
      exact hM.2
  have hA0 : S3 (.inl 0)=p := rfl
  have hA1 : S3 (.inl 1)=[] := rfl
  have hA := move_call x y dst false S3 v
  have e3 : Execution (program x y dst) ⟨some (.move false 0),v,S3⟩
      ⟨some (.move true 0),v,S4⟩ (10*(1+p.length)^2) := by
    refine ⟨p.length+1,?_,?_⟩
    · simpa only [moveCode,nextMove,Bool.false_eq_true,↓reduceIte,hA0,hA1,List.append_nil] using!
        hA.1
    · simpa only
        [moveCode,Bool.false_eq_true,↓reduceIte,hA0,hA1,List.length_nil,Nat.add_zero] using! hA.2
  have hB0 : S4 (.inl 1)=p.reverse := rfl
  have hB1 : S4 (.inr dst)=[] := hempty
  have hB := move_call x y dst true S4 v
  have e4 : Execution (program x y dst) ⟨some (.move true 0),v,S4⟩
      ⟨some (.clear 0),v,S5⟩ (10*(1+p.length)^2) := by
    refine ⟨p.length+1,?_,?_⟩
    · simpa only
        [moveCode,nextMove,↓reduceIte,hB0,hB1,List.length_reverse,List.reverse_reverse,List.append_nil] using! hB.1
    · simpa only
        [moveCode,↓reduceIte,hB0,hB1,List.length_reverse,List.length_nil,Nat.add_zero] using! hB.2
  have hC0 : S5 (.inl 3)=a.reverse := rfl
  have hC := clear_call x y dst S5 v
  have e5 : Execution (program x y dst) ⟨some (.clear 0),v,S5⟩
      ⟨some .done,v,S6⟩ (10*(1+a.length)^2) := by
    refine ⟨a.length+1,?_,?_⟩
    · simpa only [hC0,List.length_reverse] using! hC.1
    · simpa only [hC0,List.length_reverse] using! hC.2
  have e6 : Execution (program x y dst) ⟨some .done,v,S6⟩ ⟨none,v,S6⟩ 1 := by
    refine ⟨1,?_,?_⟩ <;> rfl
  have hall := (((((e0.trans e1).trans e2).trans e3).trans e4).trans e5).trans e6
  rw [hS6] at hall
  apply hall.mono
  let N := 1+a.length+b.length
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hA : 1+a.length ≤ N := by dsimp [N]; omega
  have hB : 1+b.length ≤ N := by dsimp [N]; omega
  have hp := Qatlib.Concepts.QueryComplexity.DegreeMethod.mulAcc_length a b b.length
  have hP : 1+p.length ≤ 2*N := by dsimp [p,N]; omega
  have ha2 := Nat.pow_le_pow_left hA 2
  have hb2 := Nat.pow_le_pow_left hB 2
  have hp2 := Nat.pow_le_pow_left hP 2
  have h24 : N^2 ≤ N^4 := by nlinarith [sq_nonneg ((N:ℤ)^2-1)]
  have hOne : 1 ≤ N^4 := by have h := Nat.pow_le_pow_left hN 4; simpa using! h
  change 25*(1+a.length)^2+25*(1+b.length)^2+mulClockConstant*N^4+
    10*(1+p.length)^2+10*(1+p.length)^2+10*(1+a.length)^2+1 ≤ (mulClockConstant+1000)*N^4
  nlinarith

end ArbitraryRegisters

namespace Preprocess

/-- The first source register for each of the four preprocessing multiplications. -/
def sourceX : Fin 4 → Register | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1
/-- The second source register for each of the four preprocessing multiplications. -/
def sourceY : Fin 4 → Register | 0 => 3 | 1 => 4 | 2 => 2 | _ => 6
/-- The destination register for each preprocessing multiplication. -/
def target : Fin 4 → Register | 0 => 4 | 1 => 5 | 2 => 6 | _ => 7

/-- Control labels for the four preprocessing multiplication calls and termination. -/
inductive Label where
  | call (index : Fin 4) (l : Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Label)
  | done
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.call 0 (.copy false .emit)⟩

/-- Selects the next preprocessing multiplication, or the final label after the fourth call. -/
def next (i : Fin 4) : Label :=
  if h : i.val+1<4 then .call ⟨i.val+1,h⟩ (.copy false .emit) else .done

/-- The preprocessing program that computes two squares and the two products needed for the
square-root ratio. -/
def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .call i l => StackCall.stmt id (Label.call i) (next i) id (fun _ v => v)
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.program (sourceX i) (sourceY i) (target i) l)
  | .done => .halt

/-- Updates the selected destination register with the corresponding binary product accumulator. -/
def stepR (i : Fin 4) (R : Register → Bits) : Register → Bits :=
  Function.update R (target i) (mulAcc (R (sourceX i)) (R (sourceY i)) (R (sourceY i)).length)

/-- Initializes the four rational-parameter registers and leaves the four product registers
empty. -/
def initial (qN qD sN sD : Bits) : Register → Bits
  | 0 => qN | 1 => qD | 2 => sN | 3 => sD | _ => []

/-- The binary product accumulator for the square of a word. -/
def square (bits : Bits) : Bits := mulAcc bits bits bits.length
/-- The binary product accumulator representing the numerator word times the square of the
scale-denominator word. -/
def numerator (qN sD : Bits) : Bits := mulAcc qN (square sD) (square sD).length
/-- The binary product accumulator representing the denominator word times the square of the
scale-numerator word. -/
def denominator (qD sN : Bits) : Bits := mulAcc qD (square sN) (square sN).length

/-- The final register store containing the original words, their required squares, and the two
preprocessing products. -/
def result (qN qD sN sD : Bits) : Register → Bits
  | 0 => qN | 1 => qD | 2 => sN | 3 => sD | 4 => square sD
  | 5 => numerator qN sD | 6 => square sN | _ => denominator qD sN

/-- A preprocessing multiplication updates its destination and advances to the next label with
the stated quartic execution bound, provided the destination is empty. -/
theorem call_execution (i : Fin 4) (R : Register → Bits) (hempty : R (target i)=[]) :
    Execution program
      ⟨some (.call i (.copy false .emit)),(MulVar.init,none),store (fun _ => []) R⟩
      ⟨some (next i),(MulVar.init,none),store (fun _ => []) (stepR i R)⟩
      ((mulClockConstant+1000)*(1+(R (sourceX i)).length+(R (sourceY i)).length)^4) := by
  obtain ⟨ticks,hr,hc⟩ :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.complete
      (sourceX i) (sourceY i) (target i) R hempty
  obtain ⟨hN,hNC⟩ := StackCall.execution id (Label.call i) (next i) id (fun _ v : Local => v)
    id (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.program (sourceX i) (sourceY i) (target i)) program (fun _ => rfl)
    (MulVar.init,none) _ _ _ hr
  simp only [StackCall.cfg,id_eq,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none] at hN hNC
  exact ⟨ticks,hN,hNC.trans_le hc⟩

/-- The four-call preprocessing program halts with the specified result registers and empty
workspace within the sum of the four multiplication budgets plus one. -/
theorem complete (qN qD sN sD : Bits) :
    Execution program
      ⟨some (.call 0 (.copy false .emit)),(MulVar.init,none),store (fun _ => []) (initial qN qD sN sD)⟩
      ⟨none,(MulVar.init,none),store (fun _ => []) (result qN qD sN sD)⟩
      ((mulClockConstant+1000)*((1+sD.length+sD.length)^4+
        (1+qN.length+(square sD).length)^4+(1+sN.length+sN.length)^4+
        (1+qD.length+(square sN).length)^4)+1) := by
  let R0 := initial qN qD sN sD
  let R1 := stepR 0 R0
  let R2 := stepR 1 R1
  let R3 := stepR 2 R2
  let R4 := stepR 3 R3
  have h0 := call_execution 0 R0 (by rfl)
  have h1 := call_execution 1 R1 (by rfl)
  have h2 := call_execution 2 R2 (by rfl)
  have h3 := call_execution 3 R3 (by rfl)
  have hE : R4=result qN qD sN sD := by
    funext i
    fin_cases i <;> rfl
  have hD : Execution program
      ⟨some .done,(MulVar.init,none),store (fun _ => []) R4⟩
      ⟨none,(MulVar.init,none),store (fun _ => []) R4⟩ 1 := by
    refine ⟨1,?_,?_⟩ <;> rfl
  have hall := (((h0.trans h1).trans h2).trans h3).trans hD
  rw [hE] at hall
  apply hall.mono
  change (mulClockConstant+1000)*(1+sD.length+sD.length)^4+
    (mulClockConstant+1000)*(1+qN.length+(square sD).length)^4+
    (mulClockConstant+1000)*(1+sN.length+sN.length)^4+
    (mulClockConstant+1000)*(1+qD.length+(square sN).length)^4+1 ≤ _
  exact le_of_eq (by ring)

/-- The two output product registers represent `qN * sD^2` and `qD * sN^2` under binary
evaluation. -/
theorem result_value (qN qD sN sD : Bits) :
    binaryValue (result qN qD sN sD 5) = binaryValue qN*(binaryValue sD)^2 ∧
    binaryValue (result qN qD sN sD 7) = binaryValue qD*(binaryValue sN)^2 := by
  constructor
  · change binaryValue (mulAcc qN (square sD) (square sD).length)=_
    rw [mulProgram_value]
    unfold square
    rw [mulProgram_value]
    ring
  · change binaryValue (mulAcc qD (square sN) (square sN).length)=_
    rw [mulProgram_value]
    unfold square
    rw [mulProgram_value]
    ring

/-- Preprocessing satisfies a quartic execution bound in one plus the sum of the four input-word
lengths. -/
theorem complete_bound (qN qD sN sD : Bits) :
    Execution program
      ⟨some (.call 0 (.copy false .emit)),(MulVar.init,none),store (fun _ => []) (initial qN qD sN sD)⟩
      ⟨none,(MulVar.init,none),store (fun _ => []) (result qN qD sN sD)⟩
      ((mulClockConstant+1001)*400*(1+qN.length+qD.length+sN.length+sD.length)^4) := by
  apply (complete qN qD sN sD).mono
  let N := 1+qN.length+qD.length+sN.length+sD.length
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hSD := Qatlib.Concepts.QueryComplexity.DegreeMethod.mulAcc_length sD sD sD.length
  have hSN := Qatlib.Concepts.QueryComplexity.DegreeMethod.mulAcc_length sN sN sN.length
  have h0 : 1+sD.length+sD.length ≤ 3*N := by dsimp [N]; omega
  have h1 : 1+qN.length+(square sD).length ≤ 3*N := by dsimp [N,square]; omega
  have h2 : 1+sN.length+sN.length ≤ 3*N := by dsimp [N]; omega
  have h3 : 1+qD.length+(square sN).length ≤ 3*N := by dsimp [N,square]; omega
  have hp0 := Nat.pow_le_pow_left h0 4
  have hp1 := Nat.pow_le_pow_left h1 4
  have hp2 := Nat.pow_le_pow_left h2 4
  have hp3 := Nat.pow_le_pow_left h3 4
  have hsum : (1+sD.length+sD.length)^4+(1+qN.length+(square sD).length)^4+
      (1+sN.length+sN.length)^4+(1+qD.length+(square sN).length)^4 ≤ 324*N^4 := by nlinarith
  have hmul := Nat.mul_le_mul_left (mulClockConstant+1000) hsum
  have hOne : 1 ≤ N^4 := by have h := Nat.pow_le_pow_left hN 4; simpa using! h
  change _ ≤ (mulClockConstant+1001)*400*N^4
  nlinarith

end Preprocess
end Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct
