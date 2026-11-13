/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineBitBounds
import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalGaussianProgram
import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalCacheProgram
import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalRowProgram
import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalRowsProgram

/-!
# Native execution costs for rational word programs

This module compiles successful rational word-program executions to finite-state Turing machines
with separate time and space bounds. `compiled_execution` supplies total and peak stack-machine
clock bounds, and `native_program_polynomial` turns a payload-width bound into polynomial native
resource bounds. The cache, row, batch, and matrix results add decoding correctness and exact
source-field instruction counts; `SqRationalMachineCost.frontier1` combines the matrix execution
statement with polynomial work and program-length bounds.

The compilation results here use the machine and encodings developed in this library. For
general background on Turing-machine computation and its resource measures, see
[KitaevShenVyalyi2002].

## Main statements

* `native_program_polynomial`: native execution with polynomial resource bounds.
* `native_cache_polynomial`: polynomial execution bounds for cache programs.
* `SqRationalMachineCost.frontier1`: matrix execution, decoding, and instruction counts.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002] *Classical and Quantum Computation*.
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

set_option autoImplicit false
set_option maxHeartbeats 2500000
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

/-- For any input and output stack slots, one finite-state native Turing machine simulates every
terminating stack-machine execution with the stated time and space bounds. Both bounds use
the execution clock budget and quadratic input and output overhead. -/
theorem native_backend
    (inputStack outputStack : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot) :
    ∃ (q : ℕ) (N : TM0.Machine Symbol (Fin (q+1))) (C : ℕ), 0 < C ∧
      ∀ (input output : Bits)
        (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) (T : ℕ),
      Execution Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program
        (TM2.init inputStack input.reverse)
        ⟨none,v,Function.update (fun _ => []) outputStack output.reverse⟩ T →
      Runs N input output
        (C*((1+input.length)^2+T+(1+output.length)^2))
        (C*((1+input.length)^2+T+(1+output.length)^2)) := by
  obtain ⟨q,N,C,hC,hN⟩ := raw_compiler_separate
    Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program inputStack outputStack
  refine ⟨q,N,C,hC,?_⟩
  intro input output v T h
  obtain ⟨steps,hr,hc⟩ := h
  have hraw := hN input output steps v hr
  apply runs_mono hraw
  · exact Nat.mul_le_mul_left C (Nat.add_le_add_right (Nat.add_le_add_left hc _) _)
  · have hp := (maxClock_le_clock
      Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program steps
      (TM2.init inputStack input.reverse)).trans hc
    exact Nat.mul_le_mul_left C (Nat.add_le_add_right (Nat.add_le_add_left hp _) _)

/-- A terminating stack-machine run has a native simulation whose time bound contains `steps *
sweepFactor M * H` and whose space bound contains `sweepFactor M * H`, with the stated
quadratic input and output overhead. -/
theorem native_backend_separate_peak
    (inputStack outputStack : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot) :
    ∃ (q : ℕ) (N : TM0.Machine Symbol (Fin (q+1))) (C : ℕ), 0 < C ∧
      ∀ (input output : Bits) (steps : ℕ)
        (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local),
      let M := Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program
      let first := TM2.init inputStack input.reverse
      let H :=
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight first.stk+steps*programNodes M+1
      stackRun M steps first =
        some ⟨none,v,Function.update (fun _ => []) outputStack output.reverse⟩ →
      Runs N input output
        (C*((1+input.length)^2+steps*sweepFactor M*H+(1+output.length)^2))
        (C*((1+input.length)^2+sweepFactor M*H+(1+output.length)^2)) := by
  obtain ⟨q,N,C,hC,hN⟩ := raw_compiler_separate
    Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program inputStack outputStack
  refine ⟨q,N,C,hC,?_⟩
  intro input output steps v
  (try dsimp only)
  intro hr
  have hraw := hN input output steps v hr
  apply runs_mono hraw
  · have ht := Qatlib.Concepts.QueryComplexity.DegreeMethod.runClock_le
      Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program steps
      (TM2.init inputStack input.reverse)
    exact Nat.mul_le_mul_left C (Nat.add_le_add_right (Nat.add_le_add_left ht _) _)
  · have hs := Qatlib.Concepts.QueryComplexity.DegreeMethod.runMaxClock_le
      Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program steps
      (TM2.init inputStack input.reverse)
    exact Nat.mul_le_mul_left C (Nat.add_le_add_right (Nat.add_le_add_left hs _) _)

/-- The total clock budget for initializing, executing, and finalizing a compiled instruction
program. -/
def compiledTime (p : List Instruction) (ps : List Bits) (s' : WordState) : ℕ :=
  bootBudget ps (programCode p)+programBudget p [] ⟨ps,[]⟩+finishBudget s'.parameters s'.values

/-- The maximum of the initialization, program-execution, and finalization clock budgets. -/
def compiledPeak (p : List Instruction) (ps : List Bits) (s' : WordState) : ℕ :=
  max (max (bootBudget ps (programCode p)) (programPeak p [] ⟨ps,[]⟩))
    (finishBudget s'.parameters s'.values)

/-- A successful word-program run from parameters and an empty value stack yields a terminating
stack-machine path with the encoded output values. Its total and peak clock budgets are
`compiledTime` and `compiledPeak`. -/
theorem compiled_execution (p : List Instruction) (ps : List Bits) (s' : WordState)
    (h : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run p ⟨ps,[]⟩=some s') :
    ∃ last,PathExecution (TM2.init (.inl .program) (inputCode ps (programCode p)).reverse)
      ⟨none,last,Function.update (fun _ => []) (.inl .output) (valueStack s'.values).reverse⟩
      (compiledTime p ps s') (compiledPeak p ps s') := by
  obtain ⟨v,h0⟩ := boot_execution ps (programCode p)
  obtain ⟨w,h1⟩ := program_execution p [] ⟨ps,[]⟩ s' v h
  simp only [List.append_nil] at h1
  obtain ⟨last,h2⟩ := finish_execution s'.parameters s'.values w
  exact ⟨last,((path_of_execution h0).trans h1).trans (path_of_execution h2)⟩

/-- A stack-machine path with total clock bound `T` and peak clock bound `P` has a uniform
native simulation with time controlled by `T` and space controlled by `P`, plus quadratic
input and output overhead. -/
theorem native_backend_path (inputStack outputStack : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Slot) :
    ∃ (q : ℕ) (N : TM0.Machine Symbol (Fin (q+1))) (C : ℕ), 0 < C ∧
      ∀ (input output : Bits) (v : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.Local) (T P : ℕ),
      PathExecution (TM2.init inputStack input.reverse)
        ⟨none,v,Function.update (fun _ => []) outputStack output.reverse⟩ T P →
      Runs N input output (C*((1+input.length)^2+T+(1+output.length)^2))
        (C*((1+input.length)^2+P+(1+output.length)^2)) := by
  obtain ⟨q,N,C,hC,hN⟩ :=
      raw_compiler_separate Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineDefs.program inputStack outputStack
  refine ⟨q,N,C,hC,?_⟩
  intro input output v T P h
  obtain ⟨steps,hr,hc,hp⟩ := h
  apply runs_mono (hN input output steps v hr)
  · exact Nat.mul_le_mul_left C (Nat.add_le_add_right (Nat.add_le_add_left hc _) _)
  · exact Nat.mul_le_mul_left C (Nat.add_le_add_right (Nat.add_le_add_left hp _) _)

/-- One finite-state native Turing machine executes every successfully evaluated encoded
instruction program. Its time and space bounds use `compiledTime` and `compiledPeak`,
respectively, together with quadratic input and output overhead. -/
theorem native_program :
    ∃ (q : ℕ) (N : TM0.Machine Symbol (Fin (q+1))) (C : ℕ), 0 < C ∧
      ∀ (p : List Instruction) (ps : List Bits) (s' : WordState),
      Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run p ⟨ps,[]⟩=some s' →
      Runs N (inputCode ps (programCode p)) (valueStack s'.values)
        (C*((1+(inputCode ps (programCode p)).length)^2+compiledTime p ps s'+
          (1+(valueStack s'.values).length)^2))
        (C*((1+(inputCode ps (programCode p)).length)^2+compiledPeak p ps s'+
          (1+(valueStack s'.values).length)^2)) := by
  obtain ⟨q,N,C,hC,hN⟩ := native_backend_path (.inl .program) (.inl .output)
  refine ⟨q,N,C,hC,?_⟩
  intro p ps s' h
  obtain ⟨last,hr⟩ := compiled_execution p ps s' h
  exact hN _ _ last _ _ hr

/-- A successful program with payload bound `B` has compiled time at most `100000000 * (p.length
+ 2) * (pathEnvelope p ps B + 1)^4` and compiled peak at most `100000000 * (pathEnvelope p
ps B + 1)^4`. Its encoded output length is at most `pathEnvelope p ps B`. -/
theorem compiled_polynomial (p : List Instruction) (ps : List Bits) (s' : WordState) (B : ℕ)
    (he : Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run p ⟨ps,[]⟩=some s') (hb : PayloadBound B p ⟨ps,[]⟩) :
    compiledTime p ps s' ≤ 100000000*(p.length+2)*(pathEnvelope p ps B+1)^4 ∧
    compiledPeak p ps s' ≤ 100000000*(pathEnvelope p ps B+1)^4 ∧
    (valueStack s'.values).length ≤ pathEnvelope p ps B := by
  let H := pathEnvelope p ps B
  have hi : (inputCode ps (programCode p)).length ≤ H := by dsimp [H,pathEnvelope]; omega
  have hc : (programCode p++[]).length ≤ H := by
    simp only [inputCode,List.length_reverse,List.length_append] at hi
    simpa only [List.append_nil] using! (show (programCode p).length ≤ H by omega)
  have hbound : BoundaryBound H p ⟨ps,[]⟩ := payload_boundary p ⟨ps,[]⟩ B (ps.length+p.length) H hb
    (by simp [wordCount]) (by dsimp [H,pathEnvelope]; omega)
  obtain ⟨hf,ht,hp⟩ := program_polynomial p [] ⟨ps,[]⟩ s' H he hc hbound
  have hboot := bootBudget_le ps (programCode p) H hi
  have hfinish := finishBudget_le s'.parameters s'.values H hf.1 hf.2
  refine ⟨?_,?_,hf.2⟩
  · unfold compiledTime
    calc
      _ ≤ 10000*(H+1)^4+p.length*(10000000*(H+1)^4)+100*(H+1)^4 :=
        Nat.add_le_add (Nat.add_le_add hboot ht) hfinish
      _ ≤ _ := by dsimp only [H]; ring_nf; omega
  · change max (max (bootBudget ps (programCode p)) (programPeak p [] ⟨ps,[]⟩))
      (finishBudget s'.parameters s'.values) ≤ 100000000*(H+1)^4
    exact max_le (max_le (by omega) (by omega)) (by omega)

/-- One finite-state native Turing machine executes every successful instruction program with a
payload bound, using time at most `C * (p.length + 2) * (pathEnvelope p ps B + 1)^4` and
space at most `C * (pathEnvelope p ps B + 1)^4` for one positive constant `C`. -/
theorem native_program_polynomial :
    ∃ (q : ℕ) (N : TM0.Machine Symbol (Fin (q+1))) (C : ℕ),0 < C ∧
      ∀ (p : List Instruction) (ps : List Bits) (s' : WordState) (B : ℕ),
      Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.run p ⟨ps,[]⟩=some s' → PayloadBound B p ⟨ps,[]⟩ →
      Runs N (inputCode ps (programCode p)) (valueStack s'.values)
        (C*(p.length+2)*(pathEnvelope p ps B+1)^4)
        (C*(pathEnvelope p ps B+1)^4) := by
  obtain ⟨q,N,C,hC,hN⟩ := native_program
  refine ⟨q,N,C*100000002,Nat.mul_pos hC (by omega),?_⟩
  intro p ps s' B he hb
  obtain ⟨ht,hp,hout⟩ := compiled_polynomial p ps s' B he hb
  let H := pathEnvelope p ps B
  have hin : (inputCode ps (programCode p)).length ≤ H := by dsimp [H,pathEnvelope]; omega
  have hlow : (H+1)^2 ≤ (H+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hi : (1+(inputCode ps (programCode p)).length)^2 ≤ (H+1)^4 :=
    (Nat.pow_le_pow_left (show 1+(inputCode ps (programCode p)).length ≤ H+1 by omega) 2).trans hlow
  have ho : (1+(valueStack s'.values).length)^2 ≤ (H+1)^4 :=
    (Nat.pow_le_pow_left (show 1+(valueStack s'.values).length ≤ H+1 by omega) 2).trans hlow
  apply runs_mono (hN p ps s' he)
  · calc
      _ ≤ C*((H+1)^4+100000000*(p.length+2)*(H+1)^4+(H+1)^4) := by gcongr
      _ ≤ _ := by dsimp only [H]; ring_nf; omega
  · calc
      _ ≤ C*((H+1)^4+100000000*(H+1)^4+(H+1)^4) := by gcongr
      _ = _ := by dsimp only [H]; ring

/-- One finite-state native Turing machine executes compiled Gaussian expressions with the
stated compiled time and peak bounds. Decoding the output yields the expression's evaluation
on the binary parameter values with an empty remainder. -/
theorem native_gaussian :
    ∃ (q : ℕ) (N : TM0.Machine Symbol (Fin (q+1))) (C : ℕ), 0 < C ∧
      ∀ (e : GaussianExpression) (ps : List Bits),
      Runs N (inputCode ps (programCode e.compile)) (valueStack (e.words ps))
        (C*((1+(inputCode ps (programCode e.compile)).length)^2+
          compiledTime e.compile ps ⟨ps,e.words ps⟩+(1+(valueStack (e.words ps)).length)^2))
        (C*((1+(inputCode ps (programCode e.compile)).length)^2+
          compiledPeak e.compile ps ⟨ps,e.words ps⟩+(1+(valueStack (e.words ps)).length)^2)) ∧
      decodeGaussian (valueStack (e.words ps))=(e.eval (ps.map binaryValue),[]) := by
  obtain ⟨q,N,C,hC,hN⟩ := native_program
  refine ⟨q,N,C,hC,?_⟩
  intro e ps
  constructor
  · apply hN
    simpa only [List.append_nil] using! e.compile_run ps []
  · simpa only [List.append_nil] using! e.decode_words ps []

/-- For valid evaluated operands, decoding the compiled product of the conjugate of `x` with `y`
gives the product of the decoded conjugate of `x` and the decoded value of `y`. -/
theorem decode_conjugate_scale (x y : GaussianExpression) (ps : List Bits)
    (hx : (x.eval (ps.map binaryValue)).Valid) (hy : (y.eval (ps.map binaryValue)).Valid) :
    (decodeGaussian (valueStack ((GaussianExpression.mul x.conjugate y).words ps))).1.decode =
      GaussianRat.mul (x.eval (ps.map binaryValue)).decode.conjugate (y.eval (ps.map binaryValue)).decode := by
  have hd := (GaussianExpression.mul x.conjugate y).decode_words ps []
  simp only [List.append_nil] at hd
  rw [hd]
  simp only [GaussianExpression.eval_mul,GaussianExpression.eval_conjugate]
  rw [GaussianCode.decode_mul _ _ (GaussianCode.conjugate_valid _ hx) hy,GaussianCode.decode_conjugate]

/-- One finite-state native Turing machine executes successful cache programs and returns the
selected cache entry when its index is valid and at least `sourceCount`, with the stated
compiled resource bounds. The output decodes with an empty remainder, and the compiled
program contains exactly `5 * cacheSourceReads p` source-field instructions. -/
theorem native_cache :
    ∃ (q : ℕ) (N : TM0.Machine Symbol (Fin (q+1))) (C : ℕ), 0 < C ∧
      ∀ (sourceCount : ℕ) (p : List CacheOp) (cs cs' : List GaussianCode) (output : ℕ),
      cacheRun sourceCount p cs=some cs' → output < cs'.length → sourceCount ≤ output →
      ∃ ps',CacheRep ps' cs' ∧
      Runs N (inputCode (encodeCache cs) (programCode (cacheOutputProgram p output)))
        (valueStack ((GaussianExpression.parameter (5*output)).words ps'))
        (C*((1+(inputCode (encodeCache cs) (programCode (cacheOutputProgram p output))).length)^2+
          compiledTime (cacheOutputProgram p output) (encodeCache cs)
            ⟨ps',(GaussianExpression.parameter (5*output)).words ps'⟩+
          (1+(valueStack ((GaussianExpression.parameter (5*output)).words ps')).length)^2))
        (C*((1+(inputCode (encodeCache cs) (programCode (cacheOutputProgram p output))).length)^2+
          compiledPeak (cacheOutputProgram p output) (encodeCache cs)
            ⟨ps',(GaussianExpression.parameter (5*output)).words ps'⟩+
          (1+(valueStack ((GaussianExpression.parameter (5*output)).words ps')).length)^2)) ∧
      decodeGaussian (valueStack ((GaussianExpression.parameter (5*output)).words ps'))=
        (cs'.getD output GaussianCode.zero,[]) ∧
      (cacheOutputProgram p output).countP (sourceField sourceCount)=5*cacheSourceReads p := by
  obtain ⟨q,N,C,hC,hN⟩ := native_program
  refine ⟨q,N,C,hC,?_⟩
  intro sourceCount p cs cs' output hr hout hsafe
  obtain ⟨ps',hP,hR,hD⟩ := compileCache_output sourceCount p cs cs' output hr hout
  exact ⟨ps',hP,hN _ _ _ hR,hD,cacheOutput_source_fields sourceCount p cs cs' output hr hsafe⟩

/-- The encoded initial cache together with the compiled cache program that emits the selected
output entry. -/
def cacheInput (p : List CacheOp) (cs : List GaussianCode) (output : ℕ) : Bits :=
  inputCode (encodeCache cs) (programCode (cacheOutputProgram p output))
/-- The encoded value stack for the Gaussian expression selecting the cache entry beginning at
parameter index `5 * output`. -/
def cacheOutput (ps' : List Bits) (output : ℕ) : Bits :=
  valueStack ((GaussianExpression.parameter (5*output)).words ps')
/-- The compiled clock budget for a cache-output program, augmented by quadratic input and
output overhead. -/
def cacheTime (p : List CacheOp) (cs : List GaussianCode) (ps' : List Bits) (output : ℕ) : ℕ :=
  (1+(cacheInput p cs output).length)^2+
    compiledTime (cacheOutputProgram p output) (encodeCache cs)
      ⟨ps',(GaussianExpression.parameter (5*output)).words ps'⟩+(1+(cacheOutput ps' output).length)^2
/-- The compiled peak clock budget for a cache-output program, augmented by quadratic input and
output overhead. -/
def cachePeak (p : List CacheOp) (cs : List GaussianCode) (ps' : List Bits) (output : ℕ) : ℕ :=
  (1+(cacheInput p cs output).length)^2+
    compiledPeak (cacheOutputProgram p output) (encodeCache cs)
      ⟨ps',(GaussianExpression.parameter (5*output)).words ps'⟩+(1+(cacheOutput ps' output).length)^2

/-- The fourth power of one plus the path envelope for the compiled cache-output program. -/
def cachePolynomialWork (p : List CacheOp) (cs : List GaussianCode) (output B : ℕ) : ℕ :=
  (pathEnvelope (cacheOutputProgram p output) (encodeCache cs) B+1)^4

/-- The polynomial work bound multiplied by two plus the length of the compiled cache-output
program. -/
def cachePolynomialTime (p : List CacheOp) (cs : List GaussianCode) (output B : ℕ) : ℕ :=
  ((cacheOutputProgram p output).length+2)*cachePolynomialWork p cs output B

/-- The cache polynomial work bound is at most `625 * (1 + (cacheInput p cs output).length)^4 *
(B + 1)^4`. -/
theorem cachePolynomialWork_bound (p : List CacheOp) (cs : List GaussianCode) (output B : ℕ) :
    cachePolynomialWork p cs output B ≤ 625*(1+(cacheInput p cs output).length)^4*(B+1)^4 := by
  unfold cachePolynomialWork
  calc
    _ ≤ (5*(1+(cacheInput p cs output).length)*(B+1))^4 :=
      Nat.pow_le_pow_left (pathEnvelope_bound (cacheOutputProgram p output) (encodeCache cs) B) 4
    _ = _ := by ring

/-- Compiling a cache program and appending output selection produces at most `68 * p.length +
5` instructions. -/
theorem cacheOutputProgram_length_le (p : List CacheOp) (output : ℕ) :
    (cacheOutputProgram p output).length ≤ 68*p.length+5 := by
  have h := compileCache_length_le p
  simp only [cacheOutputProgram,List.length_append]
  have he : (GaussianExpression.parameter (5*output)).compile.length=5 := rfl
  rw [he]
  omega

/-- For a successful cache run with an in-range output outside the source prefix and a payload
bound, one finite-state native Turing machine has time and space bounded by a uniform
constant times `cachePolynomialTime` and `cachePolynomialWork`. The selected output decodes
with an empty remainder, and the compiled program contains exactly `5 * cacheSourceReads p`
source-field instructions. -/
theorem native_cache_polynomial :
    ∃ (q : ℕ) (N : TM0.Machine Symbol (Fin (q+1))) (C : ℕ),0 < C ∧
      ∀ (sourceCount : ℕ) (p : List CacheOp) (cs cs' : List GaussianCode) (output B : ℕ),
      cacheRun sourceCount p cs=some cs' → output < cs'.length → sourceCount ≤ output →
      PayloadBound B (cacheOutputProgram p output) ⟨encodeCache cs,[]⟩ →
      ∃ ps',CacheRep ps' cs' ∧
      Runs N (cacheInput p cs output) (cacheOutput ps' output)
        (C*cachePolynomialTime p cs output B) (C*cachePolynomialWork p cs output B) ∧
      decodeGaussian (cacheOutput ps' output)=(cs'.getD output GaussianCode.zero,[]) ∧
      (cacheOutputProgram p output).countP (sourceField sourceCount)=5*cacheSourceReads p := by
  obtain ⟨q,N,C,hC,hN⟩ := native_program_polynomial
  refine ⟨q,N,C,hC,?_⟩
  intro sourceCount p cs cs' output B hr hout hsafe hb
  obtain ⟨ps',hP,hR,hD⟩ := compileCache_output sourceCount p cs cs' output hr hout
  refine ⟨ps',hP,?_,hD,cacheOutput_source_fields sourceCount p cs cs' output hr hsafe⟩
  simpa only [cacheInput,cacheOutput,cachePolynomialTime,cachePolynomialWork,Nat.mul_assoc] using!
    hN (cacheOutputProgram p output) (encodeCache cs) ⟨ps',(GaussianExpression.parameter (5*output)).words ps'⟩ B hR hb

/-- Under the stated index and validity hypotheses, one native machine executes a row plan and
returns the selected `rowRatValue` with an empty decoding remainder and the stated cache
time and peak bounds. The compiled output program contains exactly `5 * n` source-field
instructions. -/
theorem native_row :
    ∃ (q : ℕ) (N : TM0.Machine Symbol (Fin (q+1))) (C : ℕ), 0 < C ∧
      ∀ (sourceCount n source weight acc : ℕ) (cs : List GaussianCode) (choice : Option ℕ),
      source+n ≤ sourceCount → sourceCount ≤ weight → weight+n ≤ cs.length →
      sourceCount ≤ acc → acc < cs.length → (∀ z∈cs,z.Valid) →
      choice.elim True (fun j => j < n) →
      ∃ (cf : List GaussianCode) (ps' : List Bits),
      cacheRun sourceCount (rowPlan n cs.length source weight acc) cs=some cf ∧ CacheRep ps' cf ∧
      Runs N (cacheInput (rowPlan n cs.length source weight acc) cs (rowOutput n cs.length choice))
        (cacheOutput ps' (rowOutput n cs.length choice))
        (C*cacheTime (rowPlan n cs.length source weight acc) cs ps' (rowOutput n cs.length choice))
        (C*cachePeak (rowPlan n cs.length source weight acc) cs ps' (rowOutput n cs.length choice)) ∧
      (decodeGaussian (cacheOutput ps' (rowOutput n cs.length choice))).1.decode=
        rowRatValue n source weight acc (cs.map GaussianCode.decode) choice ∧
      (decodeGaussian (cacheOutput ps' (rowOutput n cs.length choice))).2=[] ∧
      (cacheOutputProgram (rowPlan n cs.length source weight acc) (rowOutput n cs.length choice)).countP
        (sourceField sourceCount)=5*n := by
  obtain ⟨q,N,C,hC,hN⟩ := native_cache
  refine ⟨q,N,C,hC,?_⟩
  intro sourceCount n source weight acc cs choice hs hw hwb ha hab hcs hc
  obtain ⟨cf,hR,hDot,hV⟩ := rowPlan_run sourceCount n source weight acc cs hs hw hwb ha hab
  have hl : cf.length=cs.length+5*n+1 := by
    have hh := cacheRun_length sourceCount (rowPlan n cs.length source weight acc) cs cf hR
    rw [rowPlan_length] at hh
    omega
  have hsafe : sourceCount ≤ rowOutput n cs.length choice := by
    cases choice <;> simp only [rowOutput] <;> omega
  have hout : rowOutput n cs.length choice < cf.length := by
    cases choice with
    | none => simp only [rowOutput]; omega
    | some j => simp only [Option.elim] at hc; simp only [rowOutput]; omega
  have hValue : cf.getD (rowOutput n cs.length choice) GaussianCode.zero=rowValue n source weight acc cs choice := by
    cases choice with
    | none => exact hDot
    | some j => exact hV j hc
  obtain ⟨ps',hP,hNative,hD,hCount⟩ := hN sourceCount (rowPlan n cs.length source weight acc) cs cf
    (rowOutput n cs.length choice) hR hout hsafe
  refine ⟨cf,ps',hR,hP,hNative,?_,?_,?_⟩
  · rw [show decodeGaussian (cacheOutput ps' (rowOutput n cs.length choice))=
        (cf.getD (rowOutput n cs.length choice) GaussianCode.zero,[]) from hD,
      hValue,rowValue_decode n source weight acc cs choice hcs]
  · rw [show decodeGaussian (cacheOutput ps' (rowOutput n cs.length choice))=
        (cf.getD (rowOutput n cs.length choice) GaussianCode.zero,[]) from hD]
  · simpa only [rowPlan_source_reads] using! hCount

/-- Composing two native runs gives a run with time bound `Ts + Ta + 1` and space bound `max Ss
Sa`. -/
theorem paid_plan {a b : ℕ}
    (P : TM0.Machine Symbol (Fin (a+1))) (N : TM0.Machine Symbol (Fin (b+1)))
    (raw middle output : Bits) (Ts Ss Ta Sa : ℕ)
    (hP : Runs P raw middle Ts Ss) (hN : Runs N middle output Ta Sa) :
    @Runs ((a+1)+b) (composeMachine (a:=a) (b:=b) P N) raw output (Ts+Ta+1) (max Ss Sa) :=
  compose_runs P N raw middle output Ts Ss Ta Sa (Ts+Ta+1) (max Ss Sa)
    hP hN (Nat.le_refl _) (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- For a successful cache run with an in-range output outside the source prefix, a native
machine preparing the cache input can be composed with a uniform cache executor, with time
bound `Ts + C * cacheTime p cs ps' output + 1` and space bound `max Ss (C * cachePeak p cs
ps' output)`. The output decodes to the selected cache entry with an empty remainder, and
the compiled program retains its exact source-field instruction count. -/
theorem paid_cache {a : ℕ} (P : TM0.Machine Symbol (Fin (a+1))) :
    ∃ (q : ℕ) (Q : TM0.Machine Symbol (Fin (q+1))) (C : ℕ), 0 < C ∧
      ∀ (sourceCount : ℕ) (p : List CacheOp) (cs cs' : List GaussianCode) (output : ℕ)
        (raw : Bits) (Ts Ss : ℕ),
      cacheRun sourceCount p cs=some cs' → output < cs'.length → sourceCount ≤ output →
      Runs P raw (cacheInput p cs output) Ts Ss →
      ∃ ps',CacheRep ps' cs' ∧
      Runs Q raw (cacheOutput ps' output) (Ts+C*cacheTime p cs ps' output+1)
        (max Ss (C*cachePeak p cs ps' output)) ∧
      decodeGaussian (cacheOutput ps' output)=(cs'.getD output GaussianCode.zero,[]) ∧
      (cacheOutputProgram p output).countP (sourceField sourceCount)=5*cacheSourceReads p := by
  obtain ⟨b,N,C,hC,hN⟩ := native_cache
  refine ⟨(a+1)+b,composeMachine (a:=a) (b:=b) P N,C,hC,?_⟩
  intro sourceCount p cs cs' output raw Ts Ss hr hout hsafe hP
  obtain ⟨ps',hRep,hNative,hDecode,hCount⟩ := hN sourceCount p cs cs' output hr hout hsafe
  exact ⟨ps',hRep,@paid_plan a b P N raw (cacheInput p cs output) (cacheOutput ps' output)
    Ts Ss (C*cacheTime p cs ps' output) (C*cachePeak p cs ps' output) hP hNative,hDecode,hCount⟩

/-- For valid row jobs, cache entries, and output choice, one native machine executes the batch
plan and returns `batchRatValue` with an empty decoding remainder and the stated cache
resource bounds. The compiled output program contains exactly `5 * n * jobs.length`
source-field instructions. -/
theorem native_batch :
    ∃ (q : ℕ) (N : TM0.Machine Symbol (Fin (q+1))) (C : ℕ),0 < C ∧
      ∀ (sourceCount n : ℕ) (jobs : List RowJob) (cs : List GaussianCode) (fallback : ℕ)
        (choice : Option (ℕ × Option ℕ)),
      (∀ k,k < jobs.length → (jobs.getD k default).Valid sourceCount n cs.length) →
      sourceCount ≤ fallback → fallback < cs.length → (∀ z∈cs,z.Valid) →
      batchChoiceValid n jobs.length choice →
      ∃ (cf : List GaussianCode) (ps' : List Bits),
      cacheRun sourceCount (batchPlan n cs.length jobs) cs=some cf ∧ CacheRep ps' cf ∧
      Runs N (cacheInput (batchPlan n cs.length jobs) cs (batchChoiceOutput n cs.length fallback choice))
        (cacheOutput ps' (batchChoiceOutput n cs.length fallback choice))
        (C*cacheTime (batchPlan n cs.length jobs) cs ps' (batchChoiceOutput n cs.length fallback choice))
        (C*cachePeak (batchPlan n cs.length jobs) cs ps' (batchChoiceOutput n cs.length fallback choice)) ∧
      (decodeGaussian (cacheOutput ps' (batchChoiceOutput n cs.length fallback choice))).1.decode=
        batchRatValue n fallback jobs (cs.map GaussianCode.decode) choice ∧
      (decodeGaussian (cacheOutput ps' (batchChoiceOutput n cs.length fallback choice))).2=[] ∧
      (cacheOutputProgram (batchPlan n cs.length jobs) (batchChoiceOutput n cs.length fallback choice)).countP
        (sourceField sourceCount)=5*n*jobs.length := by
  obtain ⟨q,N,C,hC,hN⟩ := native_cache
  refine ⟨q,N,C,hC,?_⟩
  intro sourceCount n jobs cs fallback choice hs hf hfb hcs hc
  obtain ⟨cf,hR,hV,hout,hsafe⟩ :=
      batchPlan_output sourceCount n jobs cs fallback choice hs hf hfb hc
  obtain ⟨ps',hP,hNative,hD,hCount⟩ := hN sourceCount (batchPlan n cs.length jobs) cs cf
    (batchChoiceOutput n cs.length fallback choice) hR hout hsafe
  refine ⟨cf,ps',hR,hP,hNative,?_,?_,?_⟩
  · rw [show decodeGaussian (cacheOutput ps' (batchChoiceOutput n cs.length fallback choice))=
        (cf.getD (batchChoiceOutput n cs.length fallback choice) GaussianCode.zero,[]) from hD,
      hV,batchValue_decode n fallback jobs cs choice hcs]
  · rw [show decodeGaussian (cacheOutput ps' (batchChoiceOutput n cs.length fallback choice))=
        (cf.getD (batchChoiceOutput n cs.length fallback choice) GaussianCode.zero,[]) from hD]
  · rw [batchPlan_source_reads] at hCount
    simpa only [Nat.mul_assoc] using! hCount

/-- For valid matrix inputs and output choice, one native machine executes the associated
row-job batch and returns its `batchRatValue` with an empty decoding remainder and the
stated cache resource bounds. The compiled output program contains exactly `5 * q * n * r`
source-field instructions. -/
theorem native_matrix :
    ∃ (states : ℕ) (N : TM0.Machine Symbol (Fin (states+1))) (C : ℕ),0 < C ∧
      ∀ (matrixRows n q r : ℕ) (rows : Fin q → Fin r → Fin matrixRows)
        (A : Fin matrixRows → Fin n → GaussianCode) (X : Fin q → Fin n → GaussianCode)
        (choice : Option (ℕ × Option ℕ)),
      (∀ i j,(A i j).Valid) → (∀ i j,(X i j).Valid) → batchChoiceValid n (q*r) choice →
      ∃ (cf : List GaussianCode) (ps' : List Bits),
      let cs := matrixInputs A X
      let jobs := matrixJobs matrixRows n q r rows
      let p := batchPlan n cs.length jobs
      let output := batchChoiceOutput n cs.length (matrixRows*n+q*n) choice
      cacheRun (matrixRows*n) p cs=some cf ∧ CacheRep ps' cf ∧
      Runs N (cacheInput p cs output) (cacheOutput ps' output)
        (C*cacheTime p cs ps' output) (C*cachePeak p cs ps' output) ∧
      (decodeGaussian (cacheOutput ps' output)).1.decode=
        batchRatValue n (matrixRows*n+q*n) jobs (cs.map GaussianCode.decode) choice ∧
      (decodeGaussian (cacheOutput ps' output)).2=[] ∧
      (cacheOutputProgram p output).countP (sourceField (matrixRows*n))=5*q*n*r := by
  obtain ⟨states,N,C,hC,hN⟩ := native_batch
  refine ⟨states,N,C,hC,?_⟩
  intro matrixRows n q r rows A X choice hA hX hc
  have hs : ∀ k,k < (matrixJobs matrixRows n q r rows).length →
      ((matrixJobs matrixRows n q r rows).getD k default).Valid (matrixRows*n) n (matrixInputs A X).length := by
    intro k hk
    rw [matrixInputs_length]
    exact matrixJobs_valid matrixRows n q r rows k hk
  have hf : matrixRows*n ≤ matrixRows*n+q*n := by omega
  have hfb : matrixRows*n+q*n < (matrixInputs A X).length := by rw [matrixInputs_length]; omega
  have hChoice : batchChoiceValid n (matrixJobs matrixRows n q r rows).length choice := by
    simpa only [matrixJobs_length] using! hc
  obtain ⟨cf,ps',hR,hP,hNative,hV,hTail,hCount⟩ := hN (matrixRows*n) n (matrixJobs matrixRows n q r rows)
    (matrixInputs A X) (matrixRows*n+q*n) choice hs hf hfb (matrixInputs_valid A X hA hX) hChoice
  refine ⟨cf,ps',hR,hP,hNative,hV,hTail,?_⟩
  rw [matrixJobs_length] at hCount
  exact hCount.trans (by ring)

end Qatlib.Concepts.AdversaryBounds.AdvDuality

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM Machine

/-- Under the matrix validity, output-choice, and payload-bound hypotheses, one native machine
returns the associated `batchRatValue` with polynomial time and space bounds and an empty
decoding remainder. The statement also records exact source-read, multiplication, row-build,
and source-field instruction counts, together with explicit work and compiled-program length
bounds. -/
theorem frontier1 :
    ∃ (states : ℕ) (N : TM0.Machine Symbol (Fin (states+1))) (C : ℕ),0 < C ∧
      ∀ (matrixRows n q r : ℕ) (rows : Fin q → Fin r → Fin matrixRows)
        (A : Fin matrixRows → Fin n → GaussianCode) (X : Fin q → Fin n → GaussianCode)
        (choice : Option (ℕ × Option ℕ)) (B : ℕ),
      let cs := matrixInputs A X
      let jobs := matrixJobs matrixRows n q r rows
      let p := batchPlan n cs.length jobs
      let output := batchChoiceOutput n cs.length (matrixRows*n+q*n) choice
      (∀ i j,(A i j).Valid) → (∀ i j,(X i j).Valid) → batchChoiceValid n (q*r) choice →
      PayloadBound B (cacheOutputProgram p output) ⟨encodeCache cs,[]⟩ →
      ∃ (cf : List GaussianCode) (ps' : List Bits),
      cacheRun (matrixRows*n) p cs=some cf ∧ CacheRep ps' cf ∧
      Runs N (cacheInput p cs output) (cacheOutput ps' output)
        (C*cachePolynomialTime p cs output B) (C*cachePolynomialWork p cs output B) ∧
      (decodeGaussian (cacheOutput ps' output)).1.decode=
        batchRatValue n (matrixRows*n+q*n) jobs (cs.map GaussianCode.decode) choice ∧
      (decodeGaussian (cacheOutput ps' output)).2=[] ∧
      (cacheOutputProgram p output).countP (sourceField (matrixRows*n))=5*q*n*r ∧
      cacheSourceReads p=q*n*r ∧ cacheMultiplies p=q*2*n*r ∧ cacheRowBuilds p=q*r ∧
      cachePolynomialWork p cs output B ≤ 625*(1+(cacheInput p cs output).length)^4*(B+1)^4 ∧
      (cacheOutputProgram p output).length ≤ 68*((5*n+1)*(q*r))+5 := by
  obtain ⟨states,N,C,hC,hN⟩ := native_cache_polynomial
  refine ⟨states,N,C,hC,?_⟩
  intro matrixRows n q r rows A X choice B
  (try dsimp only)
  intro hA hX hc hb
  let cs := matrixInputs A X
  let jobs := matrixJobs matrixRows n q r rows
  let p := batchPlan n cs.length jobs
  let output := batchChoiceOutput n cs.length (matrixRows*n+q*n) choice
  have hs : ∀ k,k < jobs.length → (jobs.getD k default).Valid (matrixRows*n) n cs.length := by
    intro k hk
    dsimp [cs]
    rw [matrixInputs_length]
    exact matrixJobs_valid matrixRows n q r rows k hk
  have hf : matrixRows*n ≤ matrixRows*n+q*n := by omega
  have hfb : matrixRows*n+q*n < cs.length := by dsimp [cs]; rw [matrixInputs_length]; omega
  have hChoice : batchChoiceValid n jobs.length choice := by
    simpa only [jobs,matrixJobs_length] using! hc
  obtain ⟨cf,hR,hV,hout,hsafe⟩ := batchPlan_output (matrixRows*n) n jobs cs
    (matrixRows*n+q*n) choice hs hf hfb hChoice
  obtain ⟨ps',hP,hNative,hD,hCount⟩ := hN (matrixRows*n) p cs cf output B hR hout hsafe hb
  have hvalid : ∀ z∈cs,z.Valid := matrixInputs_valid A X hA hX
  refine ⟨cf,ps',hR,hP,hNative,?_,?_,?_,matrixJobs_reads matrixRows n q r cs.length rows,
    matrixJobs_multiplies matrixRows n q r cs.length rows,matrixJobs_row_builds matrixRows n q r cs.length rows,
    cachePolynomialWork_bound p cs output B,?_⟩
  · rw [hD,hV,batchValue_decode n (matrixRows*n+q*n) jobs cs choice hvalid]
  · rw [hD]
  · rw [matrixJobs_reads] at hCount
    exact hCount.trans (by ring)
  · have hlen : p.length=(5*n+1)*(q*r) := by rw [batchPlan_length,matrixJobs_length]
    simpa only [hlen] using! cacheOutputProgram_length_le p output

end Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
