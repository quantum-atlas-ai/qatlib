/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalGaussianProgram
import Mathlib.Data.List.GetD

/-!
# Compilation of Gaussian cache programs

This file defines `CacheOp`, a language of operations on Gaussian-code caches with a
distinguished source prefix, and `CacheRep`, its representation by five words per cache entry.
`compileCache_run` and `SqRationalMachineCost.compileCache_output` relate successful cache
evaluation to execution and decoding of compiled word programs.

The remaining results count instructions, natural-number arithmetic operations, and reads from
source fields in the compiled programs. These are properties of the compiler defined here;
[KitaevShenVyalyi2002] supplies general background on classical and quantum computation.

## Main statements

* `compileCache_run`: compiled execution represents successful cache evaluation.
* `SqRationalMachineCost.compileCache_output`: decoding the selected cache output.
* `SqRationalMachineCost.compileCache_source_fields`: exact source-field instruction counts.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002], *Classical and Quantum Computation*.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat
open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Concepts.AdversaryBounds.AdvDuality.GaussianExpression
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

namespace GaussianExpression

/-- Appending parameters preserves evaluation of a Gaussian parameter block whose five fields
already lie in the original list. -/
theorem parameter_preserved (ps tail : List ℕ) (base : ℕ) (h : base+4<ps.length) :
    (parameter base).eval (ps++tail)=(parameter base).eval ps := by
  have h0 : (ps++tail).getD base 0=ps.getD base 0 :=
    List.getD_append ps tail 0 base (by omega)
  have h1 := List.getD_append ps tail 0 (base+1) (by omega : base+1<ps.length)
  have h2 := List.getD_append ps tail 0 (base+2) (by omega : base+2<ps.length)
  have h3 := List.getD_append ps tail 0 (base+3) (by omega : base+3<ps.length)
  have h4 := List.getD_append ps tail 0 (base+4) h
  simp only [parameter,eval,Expression.eval,h0,h1,h2,h3,h4]

/-- A Gaussian parameter block starting at the original list length reads the five newly
appended natural numbers. -/
theorem parameter_appended (ps : List ℕ) (a b c d e : ℕ) :
    (parameter ps.length).eval (ps++[a,b,c,d,e])=⟨⟨a,b⟩,⟨c,d⟩,e⟩ := by
  unfold parameter eval
  simp only [Expression.eval]
  rw [List.getD_append_right ps [a,b,c,d,e] 0 ps.length (by omega),
    List.getD_append_right ps [a,b,c,d,e] 0 (ps.length+1) (by omega),
    List.getD_append_right ps [a,b,c,d,e] 0 (ps.length+2) (by omega),
    List.getD_append_right ps [a,b,c,d,e] 0 (ps.length+3) (by omega),
    List.getD_append_right ps [a,b,c,d,e] 0 (ps.length+4) (by omega)]
  simp

end GaussianExpression

/-- The word list represents the Gaussian-code cache when it has five words per entry and each
corresponding parameter block evaluates to that entry. -/
def CacheRep (ps : List Bits) (cs : List GaussianCode) : Prop :=
  ps.length=5*cs.length ∧ ∀ i,i<cs.length →
    (GaussianExpression.parameter (5*i)).eval (ps.map binaryValue)=cs.getD i GaussianCode.zero

/-- The empty word list represents the empty Gaussian-code cache. -/
theorem cacheRep_nil : CacheRep [] [] := by
  constructor
  · rfl
  · intro i h
    simp at h

/-- Appending the five words of a Gaussian expression preserves cache representation and appends
its evaluated Gaussian code. -/
theorem cacheRep_append (ps : List Bits) (cs : List GaussianCode) (e : GaussianExpression)
    (h : CacheRep ps cs) :
    CacheRep (ps++e.words ps) (cs++[e.eval (ps.map binaryValue)]) := by
  constructor
  · simp only [List.length_append,GaussianExpression.words,List.length_cons,List.length_nil,
      h.1]
    omega
  · intro i hi
    have hil : i<cs.length+1 := by simpa using! hi
    by_cases hold : i<cs.length
    · rw [List.map_append,GaussianExpression.parameter_preserved]
      · rw [h.2 i hold,List.getD_append cs _ GaussianCode.zero i hold]
      · simp only [List.length_map]
        have hl := h.1
        omega
    · have hieq : i=cs.length := by omega
      subst i
      rw [List.getD_append_right cs _ GaussianCode.zero cs.length (Nat.le_refl _)]
      simp only [Nat.sub_self,List.getD_cons_zero]
      have hl := h.1
      rw [← hl,List.map_append]
      have hp := GaussianExpression.parameter_appended (ps.map binaryValue)
        (e.realPositive.eval (ps.map binaryValue)) (e.realNegative.eval (ps.map binaryValue))
        (e.imagPositive.eval (ps.map binaryValue)) (e.imagNegative.eval (ps.map binaryValue))
        (e.denominator.eval (ps.map binaryValue))
      simpa only [List.length_map,GaussianExpression.words,List.map_cons,List.map_nil,
        Expression.word_value,GaussianExpression.eval] using! hp

/-- Encode a Gaussian code as the five words of its literal expression. -/
def encodeCode (x : GaussianCode) : List Bits := (GaussianExpression.literal x).words []
/-- Encode a Gaussian-code cache by concatenating the five-word encodings of its entries. -/
def encodeCache (cs : List GaussianCode) : List Bits := cs.flatMap encodeCode

/-- The words of a literal Gaussian expression are independent of its parameter list and equal
`encodeCode`. -/
theorem encodeCode_words (x : GaussianCode) (ps : List Bits) :
    (GaussianExpression.literal x).words ps=encodeCode x := rfl

/-- The concatenated word encoding of a Gaussian-code cache satisfies `CacheRep`. -/
theorem encodeCache_rep (cs : List GaussianCode) : CacheRep (encodeCache cs) cs := by
  induction cs using List.reverseRecOn with
  | nil => exact cacheRep_nil
  | append_singleton cs x ih =>
    have hh := cacheRep_append (encodeCache cs) cs (GaussianExpression.literal x) ih
    simpa [encodeCache,GaussianExpression.eval_literal,encodeCode_words] using! hh

/-- Operations that append a source entry, a copy, a conjugate, a sum, or a product to a
Gaussian-code cache. -/
inductive CacheOp where
  | sourceRead (index : ℕ)
  | copy (index : ℕ)
  | conjugate (index : ℕ)
  | add (left right : ℕ)
  | multiply (left right : ℕ)
  deriving DecidableEq, Repr

namespace CacheOp

/-- Validity requires source reads to lie in the source prefix and all other operands to lie in
the existing working region. A source read also requires the cache to contain the whole
source prefix. -/
def Valid (sourceCount cacheLength : ℕ) : CacheOp → Prop
  | .sourceRead i => i<sourceCount ∧ sourceCount≤cacheLength
  | .copy i | .conjugate i => sourceCount ≤ i ∧ i<cacheLength
  | .add i j | .multiply i j => (sourceCount ≤ i ∧ i<cacheLength) ∧ (sourceCount ≤ j ∧ j<cacheLength)
instance (sourceCount cacheLength : ℕ) (op : CacheOp) : Decidable (op.Valid sourceCount cacheLength) :=
  by cases op <;> unfold Valid <;> infer_instance

/-- Evaluate a cache operation using the indicated entries, with `GaussianCode.zero` as the
default for missing entries. -/
def eval (op : CacheOp) (cs : List GaussianCode) : GaussianCode :=
  match op with
  | .sourceRead i | .copy i => cs.getD i GaussianCode.zero
  | .conjugate i => (cs.getD i GaussianCode.zero).conjugate
  | .add i j => (cs.getD i GaussianCode.zero).add (cs.getD j GaussianCode.zero)
  | .multiply i j => (cs.getD i GaussianCode.zero).mul (cs.getD j GaussianCode.zero)

/-- Lower a cache operation to a Gaussian expression using five consecutive word parameters for
each cache entry. -/
def lower : CacheOp → GaussianExpression
  | .sourceRead i | .copy i => .parameter (5*i)
  | .conjugate i => (GaussianExpression.parameter (5*i)).conjugate
  | .add i j => GaussianExpression.add (.parameter (5*i)) (.parameter (5*j))
  | .multiply i j => GaussianExpression.mul (.parameter (5*i)) (.parameter (5*j))

/-- For a represented cache and a valid operation, evaluation of the lowered expression equals
evaluation of the cache operation. -/
theorem lower_eval (sourceCount : ℕ) (op : CacheOp) (ps : List Bits) (cs : List GaussianCode)
    (h : CacheRep ps cs) (hv : op.Valid sourceCount cs.length) :
    op.lower.eval (ps.map binaryValue)=op.eval cs := by
  cases op with
  | sourceRead i => exact h.2 i (hv.1.trans_le hv.2)
  | copy i => exact h.2 i hv.2
  | conjugate i =>
    rw [lower,GaussianExpression.eval_conjugate,h.2 i hv.2]
    rfl
  | add i j =>
    rw [lower,GaussianExpression.eval_add,h.2 i hv.1.2,h.2 j hv.2.2]
    rfl
  | multiply i j =>
    rw [lower,GaussianExpression.eval_mul,h.2 i hv.1.2,h.2 j hv.2.2]
    rfl

/-- Lowering and storing a source read, copy, or conjugation uses ten instructions; addition
uses 36 and multiplication uses 68. -/
theorem lower_length (op : CacheOp) :
    op.lower.append.length = match op with
      | .sourceRead _ | .copy _ | .conjugate _ => 10
      | .add _ _ => 36
      | .multiply _ _ => 68 := by
  cases op <;> rfl

/-- Count one source read for a `sourceRead` operation and zero for every other operation. -/
def sourceReads : CacheOp → ℕ | .sourceRead _ => 1 | _ => 0
/-- Count one multiplication for a `multiply` operation and zero for every other operation. -/
def multiplies : CacheOp → ℕ | .multiply _ _ => 1 | _ => 0

/-- Append the value of a valid operation to the cache, returning `none` when the operation is
invalid. -/
def step (sourceCount : ℕ) (op : CacheOp) (cs : List GaussianCode) : Option (List GaussianCode) :=
  if op.Valid sourceCount cs.length then some (cs++[op.eval cs]) else none
end CacheOp

/-- Run cache operations sequentially, appending one entry at each successful step and
propagating failure. -/
def cacheRun (sourceCount : ℕ) : List CacheOp → List GaussianCode → Option (List GaussianCode)
  | [],cs => some cs
  | op::rest,cs => (op.step sourceCount cs).bind (cacheRun sourceCount rest)

/-- Compile a cache program by concatenating the lowered append program for each operation. -/
def compileCache (p : List CacheOp) : List Instruction := p.flatMap (fun op => op.lower.append)

/-- A successful cache run can be simulated from any representing word list, ending with an
empty value stack and a representation of the final cache. -/
theorem compileCache_run (sourceCount : ℕ) (p : List CacheOp) (ps : List Bits)
    (cs cs' : List GaussianCode) (hrep : CacheRep ps cs) (hr : cacheRun sourceCount p cs=some cs') :
    ∃ ps',run (compileCache p) ⟨ps,[]⟩=some ⟨ps',[]⟩ ∧ CacheRep ps' cs' := by
  induction p generalizing ps cs with
  | nil =>
    simp only [cacheRun,Option.some.injEq] at hr
    subst cs'
    exact ⟨ps,rfl,hrep⟩
  | cons op rest ih =>
    by_cases hv : op.Valid sourceCount cs.length
    · have hrest : cacheRun sourceCount rest (cs++[op.eval cs])=some cs' := by
        simpa only [cacheRun,CacheOp.step,if_pos hv,Option.bind_some] using! hr
      have hnext := cacheRep_append ps cs op.lower hrep
      rw [CacheOp.lower_eval sourceCount op ps cs hrep hv] at hnext
      obtain ⟨ps',hR,hP⟩ := ih (ps++op.lower.words ps) (cs++[op.eval cs]) hnext hrest
      refine ⟨ps',?_,hP⟩
      simp only [compileCache,List.flatMap_cons,run_append,GaussianExpression.append_run,Option.bind_some]
      exact hR
    · simp only [cacheRun,CacheOp.step,if_neg hv,Option.bind_none,reduceCtorEq] at hr
end Qatlib.Concepts.AdversaryBounds.AdvDuality

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

/-- Compile a cache program followed by instructions that push the five words of the selected
output entry. -/
def cacheOutputProgram (p : List CacheOp) (output : ℕ) : List Instruction :=
  compileCache p++(GaussianExpression.parameter (5*output)).compile

/-- A successful cache run with an in-range output yields a compiled execution whose output
words decode to the selected final cache entry. -/
theorem compileCache_output (sourceCount : ℕ) (p : List CacheOp)
    (cs cs' : List GaussianCode) (output : ℕ) (hr : cacheRun sourceCount p cs=some cs')
    (hout : output<cs'.length) :
    ∃ ps',CacheRep ps' cs' ∧
      run (cacheOutputProgram p output) ⟨encodeCache cs,[]⟩=
        some ⟨ps',(GaussianExpression.parameter (5*output)).words ps'⟩ ∧
      decodeGaussian (valueStack ((GaussianExpression.parameter (5*output)).words ps'))=
        (cs'.getD output GaussianCode.zero,[]) := by
  obtain ⟨ps',hR,hP⟩ :=
      compileCache_run sourceCount p (encodeCache cs) cs cs' (encodeCache_rep cs) hr
  refine ⟨ps',hP,?_,?_⟩
  · rw [cacheOutputProgram,run_append,hR,Option.bind_some,GaussianExpression.compile_run]
    rfl
  · have hd := (GaussianExpression.parameter (5*output)).decode_words ps' []
    simpa only [List.append_nil,hP.2 output hout] using! hd
end Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

namespace CacheOp

/-- The lowered append program uses nine natural multiplications for cache addition, 17 for
cache multiplication, and none for the other operations. -/
theorem lower_natural_multiplies (op : CacheOp) :
    op.lower.append.count .multiply = match op with | .add _ _ => 9 | .multiply _ _ => 17 | _ => 0 := by
  cases op <;> rfl

/-- The lowered append program uses four natural additions for cache addition, 12 for cache
multiplication, and none for the other operations. -/
theorem lower_natural_adds (op : CacheOp) :
    op.lower.append.count .add = match op with | .add _ _ => 4 | .multiply _ _ => 12 | _ => 0 := by
  cases op <;> rfl

/-- The lowered append program for every cache operation contains five store instructions. -/
theorem lower_stores (op : CacheOp) : op.lower.append.count .store=5 := by
  cases op <;> rfl
end CacheOp

/-- Count source-read operations in a cache program. -/
def cacheSourceReads (p : List CacheOp) : ℕ := (p.map CacheOp.sourceReads).sum
/-- Count multiplication operations in a cache program. -/
def cacheMultiplies (p : List CacheOp) : ℕ := (p.map CacheOp.multiplies).sum

/-- Count addition operations in a cache program. -/
def cacheAdds (p : List CacheOp) : ℕ :=
  (p.map (fun op => match op with | .add _ _ => 1 | _ => 0)).sum

/-- The compiled cache program has at most 68 instructions per cache operation. -/
theorem compileCache_length_le (p : List CacheOp) : (compileCache p).length≤68*p.length := by
  induction p with
  | nil => rfl
  | cons op rest ih =>
    simp only [compileCache,List.flatMap_cons,List.length_append,List.length_cons] at ih ⊢
    have hop : op.lower.append.length≤68 := by rw [CacheOp.lower_length]; cases op <;> norm_num
    omega

/-- The compiled program contains nine natural multiplications per cache addition and 17 per
cache multiplication. -/
theorem compileCache_natural_multiplies (p : List CacheOp) :
    (compileCache p).count .multiply=9*cacheAdds p+17*cacheMultiplies p := by
  induction p with
  | nil => rfl
  | cons op rest ih =>
    simp only [compileCache,List.flatMap_cons,List.count_append] at ih ⊢
    rw [CacheOp.lower_natural_multiplies,ih]
    cases op <;> simp [cacheAdds,cacheMultiplies,CacheOp.multiplies] <;> omega

/-- The compiled program contains four natural additions per cache addition and 12 per cache
multiplication. -/
theorem compileCache_natural_adds (p : List CacheOp) :
    (compileCache p).count .add=4*cacheAdds p+12*cacheMultiplies p := by
  induction p with
  | nil => rfl
  | cons op rest ih =>
    simp only [compileCache,List.flatMap_cons,List.count_append] at ih ⊢
    rw [CacheOp.lower_natural_adds,ih]
    cases op <;> simp [cacheAdds,cacheMultiplies,CacheOp.multiplies] <;> omega

/-- A successful cache run increases the cache length by exactly the number of operations. -/
theorem cacheRun_length (sourceCount : ℕ) (p : List CacheOp) (cs cs' : List GaussianCode)
    (hr : cacheRun sourceCount p cs=some cs') : cs'.length=cs.length+p.length := by
  induction p generalizing cs with
  | nil =>
    simp only [cacheRun,Option.some.injEq] at hr
    subst cs'
    rfl
  | cons op rest ih =>
    by_cases hv : op.Valid sourceCount cs.length
    · have hrest : cacheRun sourceCount rest (cs++[op.eval cs])=some cs' := by
        simpa only [cacheRun,CacheOp.step,if_pos hv,Option.bind_some] using! hr
      have hh := ih (cs++[op.eval cs]) hrest
      simp only [List.length_append,List.length_cons,List.length_nil] at hh ⊢
      omega
    · simp only [cacheRun,CacheOp.step,if_neg hv,Option.bind_none,reduceCtorEq] at hr
end Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost

/-- Test whether an instruction reads a word parameter belonging to the first `sourceCount`
Gaussian-code entries. -/
def sourceField (sourceCount : ℕ) : Instruction → Bool
  | .parameter i => decide (i<5*sourceCount)
  | _ => false

/-- If `i < s`, all five word indices of entry `i` lie below the boundary `5 * s`. -/
private theorem below_five (i s : ℕ) (h : i<s) :
    5*i<5*s ∧ 5*i+1<5*s ∧ 5*i+2<5*s ∧ 5*i+3<5*s ∧ 5*i+4<5*s := by omega

/-- If `s ≤ i`, none of the five word indices of entry `i` lie below the boundary `5 * s`. -/
private theorem above_five (i s : ℕ) (h : s ≤ i) :
    ¬5*i<5*s ∧ ¬5*i+1<5*s ∧ ¬5*i+2<5*s ∧ ¬5*i+3<5*s ∧ ¬5*i+4<5*s := by omega

/-- The lowered append program of a valid operation reads five source fields for a source read
and no source fields otherwise. -/
theorem CacheOp.lower_source_fields (sourceCount cacheLength : ℕ) (op : CacheOp)
    (hv : op.Valid sourceCount cacheLength) :
    op.lower.append.countP (sourceField sourceCount)=5*op.sourceReads := by
  cases op with
  | sourceRead i =>
    obtain ⟨h0,h1,h2,h3,h4⟩ := below_five i sourceCount hv.1
    simp [CacheOp.lower, GaussianExpression.append, GaussianExpression.compile,
        GaussianExpression.parameter, Expression.compile, sourceField, CacheOp.sourceReads, h0, h1, h2, h3, h4]
  | copy i =>
    obtain ⟨h0,h1,h2,h3,h4⟩ := above_five i sourceCount hv.1
    simp [CacheOp.lower, GaussianExpression.append, GaussianExpression.compile,
        GaussianExpression.parameter, Expression.compile, sourceField, CacheOp.sourceReads, h0, h1, h2, h3, h4]
  | conjugate i =>
    obtain ⟨h0,h1,h2,h3,h4⟩ := above_five i sourceCount hv.1
    simp [CacheOp.lower, GaussianExpression.append, GaussianExpression.compile,
        GaussianExpression.parameter, Expression.compile, sourceField, CacheOp.sourceReads, GaussianExpression.conjugate, GaussianExpression.ofParts, GaussianExpression.real, GaussianExpression.imag, DifferenceExpression.neg, h0, h1, h2, h3, h4]
  | add i j =>
    obtain ⟨h0,h1,h2,h3,h4⟩ := above_five i sourceCount hv.1.1
    obtain ⟨g0,g1,g2,g3,g4⟩ := above_five j sourceCount hv.2.1
    simp [CacheOp.lower, GaussianExpression.append, GaussianExpression.compile,
        GaussianExpression.parameter, Expression.compile, sourceField, CacheOp.sourceReads, GaussianExpression.add, GaussianExpression.ofParts, GaussianExpression.real, GaussianExpression.imag, DifferenceExpression.add, DifferenceExpression.scale, h0, h1, h2, h3, h4, g0, g1, g2, g3, g4]
  | multiply i j =>
    obtain ⟨h0,h1,h2,h3,h4⟩ := above_five i sourceCount hv.1.1
    obtain ⟨g0,g1,g2,g3,g4⟩ := above_five j sourceCount hv.2.1
    simp [CacheOp.lower, GaussianExpression.append, GaussianExpression.compile,
        GaussianExpression.parameter, Expression.compile, sourceField, CacheOp.sourceReads, GaussianExpression.mul, GaussianExpression.ofParts, GaussianExpression.real, GaussianExpression.imag, DifferenceExpression.add, DifferenceExpression.neg, DifferenceExpression.mul, h0, h1, h2, h3, h4, g0, g1, g2, g3, g4]
end Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost

/-- For a successful cache run, the compiled program reads exactly five source fields per
source-read operation. -/
theorem compileCache_source_fields (sourceCount : ℕ) (p : List CacheOp)
    (cs cs' : List GaussianCode) (hr : cacheRun sourceCount p cs=some cs') :
    (compileCache p).countP (sourceField sourceCount)=5*cacheSourceReads p := by
  induction p generalizing cs with
  | nil => rfl
  | cons op rest ih =>
    by_cases hv : op.Valid sourceCount cs.length
    · have hrest : cacheRun sourceCount rest (cs++[op.eval cs])=some cs' := by
        simpa only [cacheRun,CacheOp.step,if_pos hv,Option.bind_some] using! hr
      simp only [compileCache,List.flatMap_cons,List.countP_append]
      change op.lower.append.countP (sourceField sourceCount)+
        (compileCache rest).countP (sourceField sourceCount)=5*cacheSourceReads (op::rest)
      rw [CacheOp.lower_source_fields sourceCount cs.length op hv,ih _ hrest]
      simp [cacheSourceReads]
      omega
    · simp only [cacheRun,CacheOp.step,if_neg hv,Option.bind_none,reduceCtorEq] at hr

/-- Compiling an output read from outside the source prefix reads no source fields. -/
theorem output_source_fields (sourceCount output : ℕ) (hout : sourceCount ≤ output) :
    (GaussianExpression.parameter (5*output)).compile.countP (sourceField sourceCount)=0 := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := above_five output sourceCount hout
  simp [GaussianExpression.compile,GaussianExpression.parameter,Expression.compile,sourceField,
    h0,h1,h2,h3,h4]

/-- For a successful cache run with output outside the source prefix, the output program reads
exactly five source fields per source-read operation. -/
theorem cacheOutput_source_fields (sourceCount : ℕ) (p : List CacheOp)
    (cs cs' : List GaussianCode) (output : ℕ) (hr : cacheRun sourceCount p cs=some cs')
    (hout : sourceCount ≤ output) :
    (cacheOutputProgram p output).countP (sourceField sourceCount)=5*cacheSourceReads p := by
  rw [cacheOutputProgram,List.countP_append,compileCache_source_fields sourceCount p cs cs' hr,
    output_source_fields sourceCount output hout,Nat.add_zero]
end Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
