/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrtExec

/-!
# Resource bounds for certified square roots

The size measure `inputSize` controls preprocessing-word lengths, completed data width, output
length, and stack height for the raw square-root program. The execution budget is bounded by a
fixed constant times the fourth power of this size, giving the uniform Turing machine in
`uniform_raw_machine`.

The rational interface adds certified square-root intervals and a choice of precision for
absolute error at most `1 / 2^b`. These explicit machine bounds use the classical computational
setting described in [KitaevShenVyalyi2002].

## Main statements

* `executionBudget_bound`: a quartic bound on the complete source execution budget.
* `uniform_certified_sqrt`: one machine computes rational intervals of width `S / 2^k`.
* `uniform_absolute_sqrt`: one machine computes intervals of width at most `1 / 2^b`.
* `output_words_certified`: certification for arbitrary valid numerator and denominator words.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2
open Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt
open Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrtExec

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrtBounds
open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits framed)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib

/-- One plus the iteration count and the encoded raw-input length. -/
def inputSize (k : ℕ) (qN qD sN sD : Bits) : ℕ := 1+k+(input k qN qD sN sD).length

/-- The sum of the five input payload lengths is at most the encoded input length. -/
theorem input_lengths (k : ℕ) (qN qD sN sD : Bits) :
    k.bits.length+qN.length+qD.length+sN.length+sD.length ≤ (input k qN qD sN sD).length := by
  dsimp only [input,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed]
  simp only [List.length_append]
  omega

/-- The binary square word has length at most three times its input length. -/
theorem square_length (bits : Bits) : (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.square bits).length ≤ 3*bits.length := by
  have h := Qatlib.Concepts.QueryComplexity.DegreeMethod.mulAcc_length bits bits bits.length
  change (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.square bits).length≤bits.length+2*bits.length at h
  omega

/-- The preprocessed numerator word has length at most the numerator length plus six times the
scale-denominator length. -/
theorem numerator_length (qN sD : Bits) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.numerator qN sD).length ≤ qN.length+6*sD.length := by
  have hs := square_length sD
  have h := Qatlib.Concepts.QueryComplexity.DegreeMethod.mulAcc_length qN
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.square sD) (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.square sD).length
  change (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.numerator qN sD).length≤
    qN.length+2*(Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.square sD).length at h
  omega

/-- The preprocessed denominator word has length at most the denominator length plus six times
the scale-numerator length. -/
theorem denominator_length (qD sN : Bits) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.denominator qD sN).length ≤ qD.length+6*sN.length :=
  numerator_length qD sN

/-- The initial loop-data width is at most seven times the encoded input length plus two. -/
theorem data_width_bound (k : ℕ) (qN qD sN sD : Bits) :
    (data qN qD sN sD).width ≤ 7*(input k qN qD sN sD).length+2 := by
  have hI := input_lengths k qN qD sN sD
  have hP := numerator_length qN sD
  have hQ := denominator_length qD sN
  dsimp only [data,Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.Data.width]
  simp only [List.length_nil,List.length_cons]
  omega

/-- The completed loop-data width is at most twelve times `inputSize`. -/
theorem completed_width_bound (k : ℕ) (qN qD sN sD : Bits) :
    (completedData k qN qD sN sD).width ≤ 12*inputSize k qN qD sN sD := by
  have h :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.iterate_width k
      (data qN qD sN sD)
  have h0 := data_width_bound k qN qD sN sD
  dsimp only [completedData,inputSize]
  omega

/-- The encoded output length is at most nine times `inputSize`. -/
theorem output_length_bound (k : ℕ) (qN qD sN sD : Bits) :
    (output k qN qD sN sD).length ≤ 9*inputSize k qN qD sN sD := by
  have hI := input_lengths k qN qD sN sD
  have hN :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareMachine.framed_length_le sN
  have hD :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareMachine.framed_length_le sD
  have hA :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareMachine.framed_length_le
      ((completedData k qN qD sN sD).a)
  have hp := output_precision k qN qD sN sD
  change ((completedData k qN qD sN sD).a).length=k at hp
  change (framed sN++(framed sD++framed ((completedData k qN qD sN sD).a))).length ≤ _
  simp only [List.length_append]
  dsimp only [inputSize]
  omega

/-- The stack height before cleanup is at most twenty times `inputSize`. -/
theorem lastMemory_height_bound (k : ℕ) (qN qD sN sD : Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (lastMemory k qN qD sN sD) ≤ 20*inputSize k qN qD sN sD := by
  let N := inputSize k qN qD sN sD
  let d := completedData k qN qD sN sD
  have hI := input_lengths k qN qD sN sD
  have hd : d.width≤20*N := by
    have h := completed_width_bound k qN qD sN sD
    dsimp only [d,N] at *
    omega
  have hfields :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareLoop.width_fields d
  have hs := hfields.1.trans hd
  have hl := hfields.2.1.trans hd
  have hq := hfields.2.2.1.trans hd
  have hr := hfields.2.2.2.1.trans hd
  have ha := hfields.2.2.2.2.trans hd
  have hqN : qN.length≤20*N := by dsimp only [N,inputSize]; omega
  have hqD : qD.length≤20*N := by dsimp only [N,inputSize]; omega
  have hsN : sN.length≤20*N := by dsimp only [N,inputSize]; omega
  have hsD : sD.length≤20*N := by dsimp only [N,inputSize]; omega
  have hsqN : (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.square sN).length≤20*N := by
    have h := square_length sN
    dsimp only [N,inputSize]
    omega
  have hsqD : (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.square sD).length≤20*N := by
    have h := square_length sD
    dsimp only [N,inputSize]
    omega
  have hout : (output k qN qD sN sD).length≤20*N := by
    have h := output_length_bound k qN qD sN sD
    dsimp only [N]
    omega
  apply Finset.sup_le
  intro i _
  fin_cases i
  · exact Nat.zero_le (20*N)
  · exact Nat.zero_le (20*N)
  · exact Nat.zero_le (20*N)
  · exact Nat.zero_le (20*N)
  · exact Nat.zero_le (20*N)
  · exact Nat.zero_le (20*N)
  · exact Nat.zero_le (20*N)
  · exact hqN
  · exact hqD
  · exact hsN
  · exact hsD
  · exact hsqD
  · exact hr
  · exact hsqN
  · exact hq
  · exact Nat.zero_le (20*N)
  · exact hs
  · exact hl
  · exact ha
  · exact Nat.zero_le (20*N)
  · exact Nat.zero_le (20*N)
  · exact Nat.zero_le (20*N)
  · exact Nat.zero_le (20*N)
  · exact Nat.zero_le (20*N)
  · exact Nat.zero_le (20*N)
  · exact Nat.zero_le (20*N)
  · exact Nat.zero_le (20*N)
  · exact Nat.zero_le (20*N)
  · exact Nat.zero_le (20*N)
  · exact hout
  · exact Nat.zero_le (20*N)

/-- The fixed constant bounding the raw square-root execution budget by the fourth power of the
input size. -/
noncomputable def sourceConstant : ℕ :=
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.mulClockConstant+1001)*400+1000000000

/-- The total execution budget is at most `sourceConstant` times the fourth power of
`inputSize`. -/
theorem executionBudget_bound (k : ℕ) (qN qD sN sD : Bits) :
    executionBudget k qN qD sN sD ≤ sourceConstant*(inputSize k qN qD sN sD)^4 := by
  let N := inputSize k qN qD sN sD
  let I := (input k qN qD sN sD).length
  let d := completedData k qN qD sN sD
  let L := k.bits.length+(data qN qD sN sD).width+10*k+10
  have hN : 1≤N := by dsimp [N,inputSize]; omega
  have hI := input_lengths k qN qD sN sD
  have hp := numerator_length qN sD
  have hw := data_width_bound k qN qD sN sD
  have hIn : 1+I≤N := by dsimp [I,N,inputSize]; omega
  have hPre : 1+qN.length+qD.length+sN.length+sD.length≤N := by dsimp [N,inputSize]; omega
  have hLaunch : 1+(Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.numerator qN sD).length≤8*N := by
    dsimp [N,inputSize]
    omega
  have hk : k+1≤N := by dsimp [N,inputSize]; omega
  have hL : L≤12*N := by dsimp [L,N,inputSize]; omega
  have h34 : N^3≤N^4 := by have h := Nat.mul_le_mul_left (N^3) hN; nlinarith only [h]
  have h24 : N^2≤N^4 := by
    have h2 := Nat.pow_le_pow_left hN 2
    nlinarith only [h2,sq_nonneg ((N:ℤ)^2-1)]
  have hOne : 1≤N^4 := by have h := Nat.pow_le_pow_left hN 4; simpa using! h
  have hF : 60000*(1+I)^3≤60000*N^4 :=
    Nat.mul_le_mul_left 60000 ((Nat.pow_le_pow_left hIn 3).trans h34)
  have hP : (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.mulClockConstant+1001)*400*
      (1+qN.length+qD.length+sN.length+sD.length)^4 ≤
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.mulClockConstant+1001)*400*N^4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hPre 4)
  have hLaunch2 := Nat.pow_le_pow_left hLaunch 2
  have hA :
      100*(1+(Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.numerator qN sD).length)^2≤6400*N^4 := by nlinarith only [hLaunch2,h24]
  have hLoop := Nat.mul_le_mul (Nat.pow_le_pow_left hk 2) (Nat.pow_le_pow_left hL 2)
  have hB : 4000000*(k+1)^2*L^2≤576000000*N^4 := by nlinarith only [hLoop]
  have hprec : d.a.length=k := output_precision k qN qD sN sD
  have hfA :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareMachine.framed_length_le d.a
  have hfD :=
      Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareMachine.framed_length_le sD
  have he0 : 1+d.a.length≤N := by dsimp [N,inputSize]; omega
  have he1 : 1+sD.length+(framed d.a).length≤4*N := by dsimp [N,inputSize]; omega
  have he2 : 1+sN.length+(framed sD++framed d.a).length≤7*N := by
    simp only [List.length_append]
    dsimp [N,inputSize]
    omega
  have he03 := Nat.pow_le_pow_left he0 3
  have he13 := Nat.pow_le_pow_left he1 3
  have he23 := Nat.pow_le_pow_left he2 3
  have hE : 11000*((1+d.a.length)^3+(1+sD.length+(framed d.a).length)^3+
      (1+sN.length+(framed sD++framed d.a).length)^3)≤4488000*N^4 := by nlinarith only [he03,he13,he23,h34]
  have hHeight := lastMemory_height_bound k qN qD sN sD
  have hHeight' :
      1+Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
      (lastMemory k qN qD sN sD)≤21*N := by dsimp [N] at *; omega
  have hHeight2 := Nat.pow_le_pow_left hHeight' 2
  have hC :
      290*(1+Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (lastMemory k qN qD sN sD))^2≤127890*N^4 := by nlinarith only [hHeight2,h24]
  have hOut := output_length_bound k qN qD sN sD
  have hOut' : 1+(output k qN qD sN sD).length≤10*N := by dsimp [N] at *; omega
  have hOut2 := Nat.pow_le_pow_left hOut' 2
  have hO : 10*(1+(output k qN qD sN sD).length)^2+1≤1001*N^4 := by nlinarith only [hOut2,h24,hOne]
  change 60000*(1+I)^3+
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.mulClockConstant+1001)*400*(1+qN.length+qD.length+sN.length+sD.length)^4+
    100*(1+(Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.Preprocess.numerator qN sD).length)^2+
    4000000*(k+1)^2*L^2+
    11000*((1+d.a.length)^3+(1+sD.length+(framed d.a).length)^3+
      (1+sN.length+(framed sD++framed d.a).length)^3)+
    290*(1+Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (lastMemory k qN qD sN sD))^2+
    (10*(1+(output k qN qD sN sD).length)^2+1) ≤
      ((Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareProduct.mulClockConstant+1001)*400+1000000000)*N^4
  nlinarith only [hF,hP,hA,hB,hE,hC,hO,hOne]

/-- A single finite-state Turing machine computes all raw square-root outputs with time and
space bounded by a fixed positive constant times `inputSize^4`. -/
theorem uniform_raw_machine :
    ∃ (q : ℕ) (M : TM0.Machine Symbol (Fin (q+1))) (C : ℕ), 0<C ∧
      ∀ (k : ℕ) (qN qD sN sD : Bits),
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (input k qN qD sN sD) (output k qN qD sN sD)
          (C*(inputSize k qN qD sN sD)^4) (C*(inputSize k qN qD sN sD)^4) := by
  obtain ⟨q,M,D,hD,hM⟩ :=
      raw_compiler_separate Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program (30 : Slot) 30
  refine ⟨q,M,(sourceConstant+1000)*D,by positivity,?_⟩
  intro k qN qD sN sD
  obtain ⟨ticks,hr,hclock⟩ := (complete k qN qD sN sD).mono (executionBudget_bound k qN qD sN sD)
  have hraw := hM (input k qN qD sN sD) (output k qN qD sN sD) ticks default hr
  have hmax :=
      maxClock_le_clock Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program ticks (TM2.init 30 (input k qN qD sN sD).reverse)
  let N := inputSize k qN qD sN sD
  have hN : 1≤N := by dsimp [N,inputSize]; omega
  have hin : 1+(input k qN qD sN sD).length≤N := by dsimp [N,inputSize]; omega
  have hout := output_length_bound k qN qD sN sD
  have hout' : 1+(output k qN qD sN sD).length≤10*N := by dsimp [N] at *; omega
  have hin2 := Nat.pow_le_pow_left hin 2
  have hout2 := Nat.pow_le_pow_left hout' 2
  have h2 := Nat.pow_le_pow_left hN 2
  have h24 : N^2≤N^4 := by nlinarith only [h2,sq_nonneg ((N:ℤ)^2-1)]
  have hclockN : stackRunClock Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program ticks (TM2.init 30 (input k qN qD sN sD).reverse)≤
      sourceConstant*N^4 := hclock
  apply runs_mono hraw
  · have hb : (1+(input k qN qD sN sD).length)^2+
        stackRunClock Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program ticks (TM2.init 30 (input k qN qD sN sD).reverse)+
        (1+(output k qN qD sN sD).length)^2 ≤ (sourceConstant+1000)*N^4 := by
      nlinarith only [hin2,hout2,h24,hclockN,h2]
    calc
      _ ≤ D*((sourceConstant+1000)*N^4) := Nat.mul_le_mul_left D hb
      _ = _ := by dsimp only [N]; ac_rfl
  · have hb : (1+(input k qN qD sN sD).length)^2+
        stackRunMaxClock Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt.program ticks (TM2.init 30 (input k qN qD sN sD).reverse)+
        (1+(output k qN qD sN sD).length)^2 ≤ (sourceConstant+1000)*N^4 := by
      nlinarith only [hin2,hout2,h24,hclockN,hmax,h2]
    calc
      _ ≤ D*((sourceConstant+1000)*N^4) := Nat.mul_le_mul_left D hb
      _ = _ := by dsimp only [N]; ac_rfl

/-- The raw input-size measure evaluated on the canonical binary words of the rational
parameters. -/
def rationalSize (q S : ℚ) (k : ℕ) : ℕ :=
  inputSize k q.num.natAbs.bits q.den.bits S.num.natAbs.bits S.den.bits

/-- A single Turing machine computes certified rational square-root intervals for `0 ≤ q ≤ S *
S` and `S > 0`, with width `S / 2^k` and quartic time and space bounds in `rationalSize`. -/
theorem uniform_certified_sqrt :
    ∃ (states : ℕ) (M : TM0.Machine Symbol (Fin (states+1))) (C : ℕ), 0<C ∧
      ∀ (q S : ℚ) (k : ℕ), 0≤q → 0<S → q≤S*S →
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (rationalInput q S k) (rationalOutput q S k)
          (C*(rationalSize q S k)^4) (C*(rationalSize q S k)^4) ∧
        ∃ lo hi : ℚ, decode (rationalOutput q S k)=some (lo,hi) ∧
          0≤lo ∧ lo≤hi ∧ hi≤S ∧ lo^2≤q ∧ q≤hi^2 ∧ hi-lo=S/2^k := by
  obtain ⟨states,M,C,hC,hM⟩ := uniform_raw_machine
  refine ⟨states,M,C,hC,?_⟩
  intro q S k hq hS hSq
  exact ⟨hM k q.num.natAbs.bits q.den.bits S.num.natAbs.bits S.den.bits,
    rationalOutput_certified q S k hq hS hSq⟩

/-- A single Turing machine computes certified rational square-root intervals of width at most
`1 / 2^b`, using `widthPrecision S b` and quartic time and space bounds in the corresponding
`rationalSize`. -/
theorem uniform_absolute_sqrt :
    ∃ (states : ℕ) (M : TM0.Machine Symbol (Fin (states+1))) (C : ℕ), 0<C ∧
      ∀ (q S : ℚ) (b : ℕ), 0≤q → 0<S → q≤S*S →
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (rationalInput q S (widthPrecision S b))
          (rationalOutput q S (widthPrecision S b))
          (C*(rationalSize q S (widthPrecision S b))^4)
          (C*(rationalSize q S (widthPrecision S b))^4) ∧
        ∃ lo hi : ℚ, decode (rationalOutput q S (widthPrecision S b))=some (lo,hi) ∧
          0≤lo ∧ lo≤hi ∧ hi≤S ∧ lo^2≤q ∧ q≤hi^2 ∧ hi-lo≤1/2^b := by
  obtain ⟨states,M,C,hC,hM⟩ := uniform_certified_sqrt
  refine ⟨states,M,C,hC,?_⟩
  intro q S b hq hS hSq
  obtain ⟨hr,lo,hi,hdecode,h0,horder,hupper,hlo,hhi,hwidth⟩ :=
    hM q S (widthPrecision S b) hq hS hSq
  refine ⟨hr,lo,hi,hdecode,h0,horder,hupper,hlo,hhi,?_⟩
  rw [hwidth]
  exact widthPrecision_spec S hS b

/-- The rational value obtained by dividing the binary value of the numerator word by that of
the denominator word. -/
def wordValue (numerator denominator : Bits) : ℚ :=
  (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue numerator : ℚ)/(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue denominator : ℚ)

/-- With positive radicand denominator and positive scale numerator and denominator, the raw
output decodes to the corresponding `sqrtLo` and `sqrtHi` values. -/
theorem output_words_decodes (k : ℕ) (qN qD sN sD : Bits)
    (hqD : 0<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue qD)
    (hsN : 0<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue sN)
    (hsD : 0<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue sD) :
    decode (output k qN qD sN sD)=
      some (sqrtLo (wordValue qN qD) (wordValue sN sD) k,
        sqrtHi (wordValue qN qD) (wordValue sN sD) k) := by
  let P :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue qN*(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue sD)^2
  let Q :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue qD*(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue sN)^2
  let x := wordValue qN qD
  let scale := wordValue sN sD
  let a := (completedData k qN qD sN sD).a
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hqDr : (0 : ℚ)<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue qD := by
    exact_mod_cast hqD
  have hsNr : (0 : ℚ)<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue sN := by
    exact_mod_cast hsN
  have hsDr : (0 : ℚ)<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue sD := by
    exact_mod_cast hsD
  have hRatio : (P : ℚ)/(Q : ℚ)=x/(scale*scale) := by
    dsimp only [P,Q,x,scale,wordValue]
    push_cast
    field_simp [hqDr.ne',hsNr.ne',hsDr.ne']
  have ha : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue a=intBisect P Q k :=
      output_value k qN qD sN sD
  have hlen : a.length=k := output_precision k qN qD sN sD
  have hI := bisectStep_iterate_int_zero P Q hQ k
  rw [hRatio,← ha] at hI
  have hparts := (rationalSqrtBracket_pair_eq_iterate (x/(scale*scale)) k).trans hI
  have hfirst := congrArg Prod.fst hparts
  have hsecond := congrArg Prod.snd hparts
  (try dsimp only at hfirst hsecond)
  have hinterval : sqrtInterval x scale k=
      (scale*((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue a : ℚ)/2^k),
        scale*(((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue a : ℚ)+1)/2^k)) := by
    rw [sqrtInterval_eq_scale,hfirst,hsecond]
  change decode (framed sN++(framed sD++framed a))=some (sqrtLo x scale k,sqrtHi x scale k)
  rw [decode_frames _ _ _ hsD,hlen]
  change some (scale*((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue a : ℚ)/2^k),
    scale*(((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue a : ℚ)+1)/2^k))=some (sqrtLo x scale k,sqrtHi x scale k)
  rw [← hinterval]
  rfl

/-- For words representing `0 ≤ q ≤ S * S` with positive denominators and positive scale, the
output decodes to ordered endpoints in `[0, S]` whose squares enclose `q` and whose
difference is `S / 2^k`. -/
theorem output_words_certified (k : ℕ) (qN qD sN sD : Bits)
    (hqD : 0<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue qD)
    (hsN : 0<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue sN)
    (hsD : 0<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue sD)
    (hSq : wordValue qN qD≤wordValue sN sD*wordValue sN sD) :
    ∃ lo hi : ℚ, decode (output k qN qD sN sD)=some (lo,hi) ∧
      0≤lo ∧ lo≤hi ∧ hi≤wordValue sN sD ∧ lo^2≤wordValue qN qD ∧
      wordValue qN qD≤hi^2 ∧ hi-lo=wordValue sN sD/2^k := by
  have hq : (0 : ℚ)≤wordValue qN qD := by dsimp [wordValue]; positivity
  have hS : (0 : ℚ)<wordValue sN sD := by
    have hn : (0 : ℚ)<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue sN := by
      exact_mod_cast hsN
    have hd : (0 : ℚ)<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue sD := by
      exact_mod_cast hsD
    exact div_pos hn hd
  let x := wordValue qN qD
  let scale := wordValue sN sD
  refine ⟨sqrtLo x scale k,sqrtHi x scale k,output_words_decodes k qN qD sN sD hqD hsN hsD,?_⟩
  have h := sqrtInterval_certified x scale k hS hq hSq
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1⟩

end Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrtBounds
