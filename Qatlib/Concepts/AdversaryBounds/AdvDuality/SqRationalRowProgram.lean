/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalCacheProgram

/-!
# Exact Gaussian-rational row programs

`dotPlan` and `scalePlan` construct cache programs for a dot-product accumulation and for
multiplying that accumulation by conjugated source entries. `rowPlan` combines them into one row
computation, with exact output locations and operation counts.

The specifications connect encoded Gaussian arithmetic to Gaussian rationals and complex
numbers. They provide explicit arithmetic components for matrix-witness computations in the
adversary-method setting of [HoyerLeeSpalek2007].

## Main statements

* `rowPlan_run`: identifies the accumulated dot product and all conjugate-scaled outputs.
* `rowValue_decode`: relates encoded outputs to Gaussian-rational values.
* `rowRatValue_toComplex`: identifies the corresponding complex-valued row expression.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2500000

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TinyTag
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open scoped BigOperators

/-- Sequential validity of cache operations, increasing the cache length by one after each
operation. -/
def CacheWf (sourceCount : ℕ) : List CacheOp → ℕ → Prop
  | [],_ => True
  | op::rest,len => op.Valid sourceCount len ∧ CacheWf sourceCount rest (len+1)

/-- A cache program that is well formed at the initial cache length executes successfully. -/
theorem cacheRun_of_wf (sourceCount : ℕ) (p : List CacheOp) (cs : List GaussianCode)
    (hw : CacheWf sourceCount p cs.length) : ∃ cs',cacheRun sourceCount p cs=some cs' := by
  induction p generalizing cs with
  | nil => exact ⟨cs,rfl⟩
  | cons op rest ih =>
    have hv := hw.1
    have ht : CacheWf sourceCount rest (cs++[op.eval cs]).length := by
      simpa using! hw.2
    obtain ⟨cs',hr⟩ := ih (cs++[op.eval cs]) ht
    exact ⟨cs',by simpa only [cacheRun,CacheOp.step,if_pos hv,Option.bind_some] using! hr⟩

/-- Well-formedness of concatenated cache programs is equivalent to well-formedness of each part
at its corresponding cache length. -/
theorem cacheWf_append (sourceCount : ℕ) (p q : List CacheOp) (len : ℕ) :
    CacheWf sourceCount (p++q) len ↔ CacheWf sourceCount p len ∧ CacheWf sourceCount q (len+p.length) := by
  induction p generalizing len with
  | nil => simp [CacheWf]
  | cons op rest ih =>
    simp only [List.cons_append,CacheWf,ih,List.length_cons]
    have hl : (len+1)+rest.length=len+(rest.length+1) := by omega
    simp only [hl,and_assoc]

/-- A cache program that repeatedly reads a source entry, multiplies it by a weight, and adds
the product to the accumulator. -/
def dotPlan : ℕ → ℕ → ℕ → ℕ → ℕ → List CacheOp
  | 0,_,_,_,_ => []
  | n+1,base,source,weight,acc =>
      [.sourceRead source,.multiply base weight,.add acc (base+1)]++
        dotPlan n (base+3) (source+1) (weight+1) (base+2)

/-- The cache index of the final dot-product accumulator, using the original accumulator when `n
= 0`. -/
def dotOutput (n base acc : ℕ) : ℕ := if n=0 then acc else base+3*n-1

/-- A dot-product plan of length `n` contains exactly `3 * n` cache operations. -/
theorem dotPlan_length (n base source weight acc : ℕ) :
    (dotPlan n base source weight acc).length=3*n := by
  induction n generalizing base source weight acc with
  | zero => rfl
  | succ n ih => simp [dotPlan,ih]; omega

/-- The dot-product plan is well formed when its source range, weight range, and accumulator
satisfy the stated index bounds. -/
theorem dotPlan_wf (sourceCount n base source weight acc : ℕ)
    (hs : source+n ≤ sourceCount) (hw : sourceCount ≤ weight) (hwb : weight+n ≤ base)
    (ha : sourceCount ≤ acc) (hab : acc<base) :
    CacheWf sourceCount (dotPlan n base source weight acc) base := by
  induction n generalizing base source weight acc with
  | zero => trivial
  | succ n ih =>
    dsimp only [dotPlan,CacheWf]
    refine ⟨?_,?_,?_,?_⟩
    · constructor <;> omega
    · constructor <;> constructor <;> omega
    · constructor <;> constructor <;> omega
    · apply ih <;> omega

/-- The output index of a nonempty dot-product plan agrees with that of the remaining plan after
one accumulation step. -/
theorem dotOutput_succ (n base acc : ℕ) :
    dotOutput (n+1) base acc=dotOutput n (base+3) (base+2) := by
  cases n with
  | zero => simp [dotOutput]
  | succ n => simp [dotOutput]; omega

/-- A dot-product plan of length `n` performs exactly `n` source reads. -/
theorem dotPlan_source_reads (n base source weight acc : ℕ) :
    cacheSourceReads (dotPlan n base source weight acc)=n := by
  induction n generalizing base source weight acc with
  | zero => rfl
  | succ n ih =>
    have hh := ih (base+3) (source+1) (weight+1) (base+2)
    simp only [cacheSourceReads] at hh
    simp only [dotPlan,cacheSourceReads,List.map_append,List.sum_append]
    rw [hh]
    norm_num [CacheOp.sourceReads]
    omega

/-- A dot-product plan of length `n` performs exactly `n` cache multiplications. -/
theorem dotPlan_multiplies (n base source weight acc : ℕ) :
    cacheMultiplies (dotPlan n base source weight acc)=n := by
  induction n generalizing base source weight acc with
  | zero => rfl
  | succ n ih =>
    have hh := ih (base+3) (source+1) (weight+1) (base+2)
    simp only [cacheMultiplies] at hh
    simp only [dotPlan,cacheMultiplies,List.map_append,List.sum_append]
    rw [hh]
    norm_num [CacheOp.multiplies]
    omega

/-- A dot-product plan of length `n` performs exactly `n` cache additions. -/
theorem dotPlan_adds (n base source weight acc : ℕ) :
    cacheAdds (dotPlan n base source weight acc)=n := by
  induction n generalizing base source weight acc with
  | zero => rfl
  | succ n ih =>
    have hh := ih (base+3) (source+1) (weight+1) (base+2)
    simp only [cacheAdds] at hh
    simp only [dotPlan,cacheAdds,List.map_append,List.sum_append]
    rw [hh]
    simp
    omega

/-- The encoded Gaussian dot-product accumulation over consecutive source and weight entries,
starting from `acc`. -/
def dotSpec : ℕ → ℕ → ℕ → List GaussianCode → GaussianCode → GaussianCode
  | 0,_,_,_,acc => acc
  | n+1,source,weight,cs,acc => dotSpec n (source+1) (weight+1) cs
      (acc.add ((cs.getD source GaussianCode.zero).mul (cs.getD weight GaussianCode.zero)))

/-- Appending entries to the cache preserves a dot-product specification whose source and weight
ranges lie in the original cache. -/
theorem dotSpec_append (n source weight : ℕ) (cs tail : List GaussianCode) (acc : GaussianCode)
    (hs : source+n ≤ cs.length) (hw : weight+n ≤ cs.length) :
    dotSpec n source weight (cs++tail) acc=dotSpec n source weight cs acc := by
  induction n generalizing source weight acc with
  | zero => rfl
  | succ n ih =>
    simp only [dotSpec]
    rw [List.getD_append cs tail GaussianCode.zero source (by omega),
      List.getD_append cs tail GaussianCode.zero weight (by omega)]
    apply ih <;> omega

/-- Default lookup in a cache of valid Gaussian codes returns a valid code, including for an
out-of-range index. -/
private theorem code_getD_valid (cs : List GaussianCode) (h : ∀ z∈cs,z.Valid) (i : ℕ) :
    (cs.getD i GaussianCode.zero).Valid := by
  induction cs generalizing i with
  | nil => simp [List.getD,GaussianCode.Valid,GaussianCode.zero]
  | cons a cs ih =>
    cases i with
    | zero => exact h a (by simp)
    | succ i =>
      apply ih
      intro z hz
      exact h z (by simp [hz])

/-- Decoding a default lookup of a Gaussian code agrees with default lookup in the decoded
cache. -/
theorem code_decode_getD (cs : List GaussianCode) (i : ℕ) :
    (cs.getD i GaussianCode.zero).decode=(cs.map GaussianCode.decode).getD i GaussianRat.zero := by
  simp only [List.getD,List.getElem?_map]
  cases cs[i]? <;> simp [GaussianCode.zero,GaussianCode.decode,Difference.value,GaussianRat.zero]

/-- The Gaussian-rational dot-product accumulation over consecutive source and weight entries,
starting from `acc`. -/
def dotRatSpec : ℕ → ℕ → ℕ → List GaussianRat → GaussianRat → GaussianRat
  | 0,_,_,_,acc => acc
  | n+1,source,weight,cs,acc => dotRatSpec n (source+1) (weight+1) cs
      (acc.add ((cs.getD source GaussianRat.zero).mul (cs.getD weight GaussianRat.zero)))

/-- For valid cache entries and accumulator, decoding the encoded dot-product specification
gives the Gaussian-rational specification. -/
theorem dotSpec_decode (n source weight : ℕ) (cs : List GaussianCode) (acc : GaussianCode)
    (hcs : ∀ z∈cs,z.Valid) (ha : acc.Valid) :
    (dotSpec n source weight cs acc).decode=
      dotRatSpec n source weight (cs.map GaussianCode.decode) acc.decode := by
  induction n generalizing source weight acc with
  | zero => rfl
  | succ n ih =>
    have hs := code_getD_valid cs hcs source
    have hw := code_getD_valid cs hcs weight
    have hm := GaussianCode.mul_valid _ _ hs hw
    simp only [dotSpec,dotRatSpec]
    rw [ih _ _ _ (GaussianCode.add_valid _ _ ha hm),GaussianCode.decode_add _ _ ha hm,
      GaussianCode.decode_mul _ _ hs hw,code_decode_getD,code_decode_getD]

/-- Running concatenated cache programs agrees with running the first program and binding its
result into the second. -/
theorem cacheRun_append (sourceCount : ℕ) (p q : List CacheOp) (cs : List GaussianCode) :
    cacheRun sourceCount (p++q) cs=(cacheRun sourceCount p cs).bind (cacheRun sourceCount q) := by
  induction p generalizing cs with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.cons_append,cacheRun]
    cases hs : op.step sourceCount cs <;> simp [ih]

/-- A successful cache program preserves every entry of the initial cache. -/
theorem cacheRun_preserves (sourceCount : ℕ) (p : List CacheOp) (cs cs' : List GaussianCode)
    (hr : cacheRun sourceCount p cs=some cs') (i : ℕ) (hi : i<cs.length) :
    cs'.getD i GaussianCode.zero=cs.getD i GaussianCode.zero := by
  induction p generalizing cs with
  | nil =>
    simp only [cacheRun,Option.some.injEq] at hr
    subst cs'
    rfl
  | cons op rest ih =>
    by_cases hv : op.Valid sourceCount cs.length
    · have ht : cacheRun sourceCount rest (cs++[op.eval cs])=some cs' := by
        simpa only [cacheRun,CacheOp.step,if_pos hv,Option.bind_some] using! hr
      rw [ih _ ht (by simp; omega),List.getD_append cs _ _ i hi]
    · simp only [cacheRun,CacheOp.step,if_neg hv,Option.bind_none,reduceCtorEq] at hr

/-- The cache obtained by appending a source entry, its weighted product, and the updated
dot-product accumulator. -/
def dotStepState (cs : List GaussianCode) (source weight acc : ℕ) : List GaussianCode :=
  let a := cs.getD source GaussianCode.zero
  let prod := a.mul (cs.getD weight GaussianCode.zero)
  cs++[a,prod,(cs.getD acc GaussianCode.zero).add prod]

/-- Under the stated index bounds, one source-read, multiplication, and addition step produces
`dotStepState`. -/
theorem dotStep_run (sourceCount source weight acc : ℕ) (cs : List GaussianCode)
    (hs : source<sourceCount) (hsc : sourceCount ≤ cs.length)
    (hw : sourceCount ≤ weight) (hwb : weight<cs.length)
    (ha : sourceCount ≤ acc) (hab : acc<cs.length) :
    cacheRun sourceCount [.sourceRead source,.multiply cs.length weight,.add acc (cs.length+1)] cs=
      some (dotStepState cs source weight acc) := by
  let a := cs.getD source GaussianCode.zero
  let prod := a.mul (cs.getD weight GaussianCode.zero)
  let c1 := cs++[a]
  let c2 := c1++[prod]
  have h0 : CacheOp.Valid sourceCount cs.length (.sourceRead source) := ⟨hs,hsc⟩
  have h1 : CacheOp.Valid sourceCount c1.length (.multiply cs.length weight) := by
    dsimp [CacheOp.Valid,c1]
    simp only [List.length_append,List.length_cons,List.length_nil]
    exact ⟨⟨hsc,by omega⟩,⟨hw,by omega⟩⟩
  have h2 : CacheOp.Valid sourceCount c2.length (.add acc (cs.length+1)) := by
    dsimp [CacheOp.Valid,c2,c1]
    simp only [List.length_append,List.length_cons,List.length_nil]
    exact ⟨⟨ha,by omega⟩,⟨by omega,by omega⟩⟩
  have hm : CacheOp.eval (.multiply cs.length weight) c1=prod := by
    dsimp only [CacheOp.eval,c1,prod]
    rw [List.getD_append_right cs [a] GaussianCode.zero cs.length (Nat.le_refl _),
      Nat.sub_self,List.getD_cons_zero,List.getD_append cs [a] GaussianCode.zero weight hwb]
  have hc : CacheOp.eval (.add acc (cs.length+1)) c2=
      (cs.getD acc GaussianCode.zero).add prod := by
    dsimp only [CacheOp.eval,c2]
    rw [List.getD_append c1 [prod] GaussianCode.zero acc (by simp [c1]; omega),
      show cs.length+1=c1.length from by simp [c1],
      List.getD_append_right c1 [prod] GaussianCode.zero c1.length (Nat.le_refl _),
      Nat.sub_self,List.getD_cons_zero]
    rw [show c1=cs++[a] from rfl,List.getD_append cs [a] GaussianCode.zero acc hab]
  rw [cacheRun,CacheOp.step,if_pos h0,Option.bind_some]
  change cacheRun sourceCount [.multiply cs.length weight,.add acc (cs.length+1)] c1=_
  rw [cacheRun,CacheOp.step,if_pos h1,Option.bind_some,hm]
  change cacheRun sourceCount [.add acc (cs.length+1)] c2=_
  rw [cacheRun,CacheOp.step,if_pos h2,Option.bind_some,hc]
  simp [cacheRun,c2,c1,dotStepState,a,prod,List.append_assoc]

/-- Under the stated index bounds, the dot-product plan executes successfully and stores
`dotSpec` at `dotOutput`. -/
theorem dotPlan_run (sourceCount n source weight acc : ℕ) (cs : List GaussianCode)
    (hs : source+n ≤ sourceCount) (hw : sourceCount ≤ weight) (hwb : weight+n ≤ cs.length)
    (ha : sourceCount ≤ acc) (hab : acc<cs.length) :
    ∃ cs',cacheRun sourceCount (dotPlan n cs.length source weight acc) cs=some cs' ∧
      cs'.getD (dotOutput n cs.length acc) GaussianCode.zero=
        dotSpec n source weight cs (cs.getD acc GaussianCode.zero) := by
  induction n generalizing source weight acc cs with
  | zero => exact ⟨cs,rfl,rfl⟩
  | succ n ih =>
    let next := dotStepState cs source weight acc
    have hn : next.length=cs.length+3 := by simp [next,dotStepState]
    obtain ⟨cs',hR,hV⟩ := ih (source+1) (weight+1) (cs.length+2) next
      (by omega) (by omega) (by rw [hn]; omega) (by omega) (by rw [hn]; omega)
    have hR' : cacheRun sourceCount
        (dotPlan n (cs.length+3) (source+1) (weight+1) (cs.length+2)) next=some cs' := by
      simpa only [hn] using! hR
    refine ⟨cs',?_,?_⟩
    · rw [dotPlan,cacheRun_append,dotStep_run sourceCount source weight acc cs
        (by omega) (by omega) hw (by omega) ha hab,Option.bind_some]
      exact hR'
    · rw [dotOutput_succ]
      rw [hn] at hV
      rw [hV]
      have hacc : next.getD (cs.length+2) GaussianCode.zero=
          (cs.getD acc GaussianCode.zero).add
            ((cs.getD source GaussianCode.zero).mul (cs.getD weight GaussianCode.zero)) := by
        dsimp only [next,dotStepState]
        rw [List.getD_append_right cs _ GaussianCode.zero (cs.length+2) (by omega)]
        simp
      rw [hacc]
      apply dotSpec_append <;> omega

/-- The source entries copied by a successful dot-product plan occur at indices `cs.length + 3 *
j` for `j < n`. -/
theorem dotPlan_sources (sourceCount n source weight acc : ℕ) (cs cs' : List GaussianCode)
    (hs : source+n ≤ sourceCount) (hw : sourceCount ≤ weight) (hwb : weight+n ≤ cs.length)
    (ha : sourceCount ≤ acc) (hab : acc<cs.length)
    (hr : cacheRun sourceCount (dotPlan n cs.length source weight acc) cs=some cs')
    (j : ℕ) (hj : j<n) :
    cs'.getD (cs.length+3*j) GaussianCode.zero=cs.getD (source+j) GaussianCode.zero := by
  induction n generalizing source weight acc cs j with
  | zero => omega
  | succ n ih =>
    let next := dotStepState cs source weight acc
    have hn : next.length=cs.length+3 := by simp [next,dotStepState]
    rw [dotPlan,cacheRun_append,dotStep_run sourceCount source weight acc cs
      (by omega) (by omega) hw (by omega) ha hab,Option.bind_some] at hr
    have ht : cacheRun sourceCount
        (dotPlan n next.length (source+1) (weight+1) (cs.length+2)) next=some cs' := by
      simpa only [hn] using! hr
    cases j with
    | zero =>
      simp only [Nat.mul_zero,Nat.add_zero]
      rw [cacheRun_preserves sourceCount _ next cs' ht cs.length (by rw [hn]; omega)]
      dsimp only [next,dotStepState]
      rw [List.getD_append_right cs _ GaussianCode.zero cs.length (Nat.le_refl _),
        Nat.sub_self,List.getD_cons_zero]
    | succ j =>
      have hv := ih (source+1) (weight+1) (cs.length+2) next
        (by omega) (by omega) (by rw [hn]; omega) (by omega) (by rw [hn]; omega) ht j (by omega)
      have hidx : next.length+3*j=cs.length+3*(j+1) := by rw [hn]; omega
      rw [hidx] at hv
      rw [hv]
      dsimp only [next,dotStepState]
      rw [List.getD_append cs _ GaussianCode.zero (source+1+j) (by omega)]
      congr 1
      omega

/-- A cache program that conjugates every third cached source entry and multiplies it by a fixed
dot-product value. -/
def scalePlan : ℕ → ℕ → ℕ → ℕ → List CacheOp
  | 0,_,_,_ => []
  | n+1,base,sourceCache,dot => [.conjugate sourceCache,.multiply base dot]++
      scalePlan n (base+2) (sourceCache+3) dot

/-- A scaling plan of length `n` contains exactly `2 * n` cache operations. -/
theorem scalePlan_length (n base sourceCache dot : ℕ) :
    (scalePlan n base sourceCache dot).length=2*n := by
  induction n generalizing base sourceCache dot with
  | zero => rfl
  | succ n ih => simp [scalePlan,ih]; omega

/-- The scaling plan is well formed when the source-cache range and dot-product index satisfy
the stated bounds. -/
theorem scalePlan_wf (sourceCount n base sourceCache dot : ℕ)
    (hs : sourceCount ≤ sourceCache) (hsb : sourceCache+3*n ≤ base)
    (hd : sourceCount ≤ dot) (hdb : dot<base) :
    CacheWf sourceCount (scalePlan n base sourceCache dot) base := by
  induction n generalizing base sourceCache dot with
  | zero => trivial
  | succ n ih =>
    dsimp only [scalePlan,CacheWf]
    refine ⟨?_,?_,?_⟩
    · constructor <;> omega
    · constructor <;> constructor <;> omega
    · apply ih <;> omega

/-- The cache obtained by appending a conjugated source entry and its product with the selected
dot-product value. -/
def scaleStepState (cs : List GaussianCode) (sourceCache dot : ℕ) : List GaussianCode :=
  let a := (cs.getD sourceCache GaussianCode.zero).conjugate
  cs++[a,a.mul (cs.getD dot GaussianCode.zero)]

/-- Under the stated index bounds, one conjugation and multiplication step produces
`scaleStepState`. -/
theorem scaleStep_run (sourceCount sourceCache dot : ℕ) (cs : List GaussianCode)
    (hs : sourceCount ≤ sourceCache) (hsb : sourceCache<cs.length)
    (hd : sourceCount ≤ dot) (hdb : dot<cs.length) :
    cacheRun sourceCount [.conjugate sourceCache,.multiply cs.length dot] cs=
      some (scaleStepState cs sourceCache dot) := by
  let a := (cs.getD sourceCache GaussianCode.zero).conjugate
  let c1 := cs++[a]
  have h0 : CacheOp.Valid sourceCount cs.length (.conjugate sourceCache) := ⟨hs,hsb⟩
  have h1 : CacheOp.Valid sourceCount c1.length (.multiply cs.length dot) := by
    dsimp [CacheOp.Valid,c1]
    simp only [List.length_append,List.length_cons,List.length_nil]
    exact ⟨⟨by omega,by omega⟩,⟨hd,by omega⟩⟩
  have hm : CacheOp.eval (.multiply cs.length dot) c1=a.mul (cs.getD dot GaussianCode.zero) := by
    dsimp only [CacheOp.eval,c1]
    rw [List.getD_append_right cs [a] GaussianCode.zero cs.length (Nat.le_refl _),
      Nat.sub_self,List.getD_cons_zero,List.getD_append cs [a] GaussianCode.zero dot hdb]
  rw [cacheRun,CacheOp.step,if_pos h0,Option.bind_some]
  change cacheRun sourceCount [.multiply cs.length dot] c1=_
  rw [cacheRun,CacheOp.step,if_pos h1,Option.bind_some,hm]
  simp [cacheRun,c1,scaleStepState,a,List.append_assoc]

/-- Under the stated index bounds, the scaling plan executes successfully and stores each
conjugate-scaled product at its specified output index. -/
theorem scalePlan_run (sourceCount n sourceCache dot : ℕ) (cs : List GaussianCode)
    (hs : sourceCount ≤ sourceCache) (hsb : sourceCache+3*n ≤ cs.length)
    (hd : sourceCount ≤ dot) (hdb : dot<cs.length) :
    ∃ cs',cacheRun sourceCount (scalePlan n cs.length sourceCache dot) cs=some cs' ∧
      ∀ j,j<n → cs'.getD (cs.length+1+2*j) GaussianCode.zero=
        (cs.getD (sourceCache+3*j) GaussianCode.zero).conjugate.mul (cs.getD dot GaussianCode.zero) := by
  induction n generalizing sourceCache dot cs with
  | zero => exact ⟨cs,rfl,by intro j hj; omega⟩
  | succ n ih =>
    let next := scaleStepState cs sourceCache dot
    have hn : next.length=cs.length+2 := by simp [next,scaleStepState]
    obtain ⟨cs',hR,hV⟩ := ih (sourceCache+3) dot next
      (by omega) (by rw [hn]; omega) hd (by rw [hn]; omega)
    have hR' : cacheRun sourceCount (scalePlan n (cs.length+2) (sourceCache+3) dot) next=some cs' := by
      simpa only [hn] using! hR
    refine ⟨cs',?_,?_⟩
    · rw [scalePlan,cacheRun_append,scaleStep_run sourceCount sourceCache dot cs
        hs (by omega) hd hdb,Option.bind_some]
      exact hR'
    · intro j hj
      cases j with
      | zero =>
        simp only [Nat.mul_zero,Nat.add_zero]
        rw [cacheRun_preserves sourceCount _ next cs' hR (cs.length+1) (by rw [hn]; omega)]
        dsimp only [next,scaleStepState]
        rw [List.getD_append_right cs _ GaussianCode.zero (cs.length+1) (by omega)]
        simp
      | succ j =>
        have hv := hV j (by omega)
        have hi : next.length+1+2*j=cs.length+1+2*(j+1) := by rw [hn]; omega
        rw [hi] at hv
        rw [hv]
        dsimp only [next,scaleStepState]
        rw [List.getD_append cs _ GaussianCode.zero (sourceCache+3+3*j) (by omega),
          List.getD_append cs _ GaussianCode.zero dot hdb]
        congr 3
        omega

/-- An accumulator index in the mutable cache region yields a dot-product output index in that
region and below `base + 3 * n`. -/
theorem dotOutput_bounds (sourceCount n base acc : ℕ)
    (ha : sourceCount ≤ acc) (hab : acc<base) :
    sourceCount ≤ dotOutput n base acc ∧ dotOutput n base acc<base+3*n := by
  cases n with
  | zero => simpa [dotOutput] using! And.intro ha hab
  | succ n => simp [dotOutput]; omega

/-- The row program formed by a dot-product plan, a copy of its output, and a conjugate-scaling
plan. -/
def rowPlan (n base source weight acc : ℕ) : List CacheOp :=
  dotPlan n base source weight acc++[.copy (dotOutput n base acc)]++
    scalePlan n (base+3*n+1) base (base+3*n)

/-- A row plan of width `n` contains exactly `5 * n + 1` cache operations. -/
theorem rowPlan_length (n base source weight acc : ℕ) :
    (rowPlan n base source weight acc).length=5*n+1 := by
  simp only [rowPlan,List.length_append,List.length_cons,List.length_nil,dotPlan_length,scalePlan_length]
  omega

/-- Under the stated index bounds, a row plan executes successfully and stores both the
dot-product accumulation and every conjugate-scaled source product at the specified indices. -/
theorem rowPlan_run (sourceCount n source weight acc : ℕ) (cs : List GaussianCode)
    (hs : source+n ≤ sourceCount) (hw : sourceCount ≤ weight) (hwb : weight+n ≤ cs.length)
    (ha : sourceCount ≤ acc) (hab : acc<cs.length) :
    ∃ cs',cacheRun sourceCount (rowPlan n cs.length source weight acc) cs=some cs' ∧
      cs'.getD (cs.length+3*n) GaussianCode.zero=
        dotSpec n source weight cs (cs.getD acc GaussianCode.zero) ∧
      ∀ j,j<n → cs'.getD (cs.length+3*n+2+2*j) GaussianCode.zero=
        (cs.getD (source+j) GaussianCode.zero).conjugate.mul
          (dotSpec n source weight cs (cs.getD acc GaussianCode.zero)) := by
  obtain ⟨cd,hD,hV⟩ := dotPlan_run sourceCount n source weight acc cs hs hw hwb ha hab
  have hdl : cd.length=cs.length+3*n := by
    have hh := cacheRun_length sourceCount (dotPlan n cs.length source weight acc) cs cd hD
    simpa only [dotPlan_length] using! hh
  have hdBounds := dotOutput_bounds sourceCount n cs.length acc ha hab
  let ccopy := cd++[cd.getD (dotOutput n cs.length acc) GaussianCode.zero]
  have hcl : ccopy.length=cs.length+3*n+1 := by simp [ccopy,hdl]
  have hC : cacheRun sourceCount [.copy (dotOutput n cs.length acc)] cd=some ccopy := by
    have hv : CacheOp.Valid sourceCount cd.length (.copy (dotOutput n cs.length acc)) := by
      exact ⟨hdBounds.1,by rw [hdl]; exact hdBounds.2⟩
    simp only [cacheRun,CacheOp.step,if_pos hv,Option.bind_some,CacheOp.eval]
    rfl
  obtain ⟨cf,hS,hSV⟩ := scalePlan_run sourceCount n cs.length (cs.length+3*n) ccopy
    (by omega) (by rw [hcl]; omega) (by omega) (by rw [hcl]; omega)
  have hS' : cacheRun sourceCount (scalePlan n (cs.length+3*n+1) cs.length (cs.length+3*n)) ccopy=some cf := by
    simpa only [hcl] using! hS
  have hdot : ccopy.getD (cs.length+3*n) GaussianCode.zero=
      dotSpec n source weight cs (cs.getD acc GaussianCode.zero) := by
    rw [← hdl]
    dsimp only [ccopy]
    rw [List.getD_append_right cd _ GaussianCode.zero cd.length (Nat.le_refl _),
      Nat.sub_self,List.getD_cons_zero,hV]
  refine ⟨cf,?_,?_,?_⟩
  · rw [rowPlan,cacheRun_append,cacheRun_append,hD,Option.bind_some,hC,Option.bind_some,hS']
  · rw [cacheRun_preserves sourceCount _ ccopy cf hS (cs.length+3*n) (by rw [hcl]; omega),hdot]
  · intro j hj
    have hv := hSV j hj
    have hl : ccopy.length+1+2*j=cs.length+3*n+2+2*j := by rw [hcl]
    rw [hl] at hv
    rw [hv]
    have hsrc : ccopy.getD (cs.length+3*j) GaussianCode.zero=cs.getD (source+j) GaussianCode.zero := by
      rw [show ccopy=cd++[cd.getD (dotOutput n cs.length acc) GaussianCode.zero] from rfl,
        List.getD_append cd _ GaussianCode.zero (cs.length+3*j) (by rw [hdl]; omega)]
      exact dotPlan_sources sourceCount n source weight acc cs cd hs hw hwb ha hab hD j hj
    rw [hsrc,hdot]

/-- A scaling plan performs no source reads. -/
theorem scalePlan_source_reads (n base sourceCache dot : ℕ) :
    cacheSourceReads (scalePlan n base sourceCache dot)=0 := by
  induction n generalizing base sourceCache dot with
  | zero => rfl
  | succ n ih =>
    have hh := ih (base+2) (sourceCache+3) dot
    simp only [cacheSourceReads] at hh
    simp only [scalePlan,cacheSourceReads,List.map_append,List.sum_append]
    rw [hh]
    norm_num [CacheOp.sourceReads]

/-- A scaling plan of length `n` performs exactly `n` cache multiplications. -/
theorem scalePlan_multiplies (n base sourceCache dot : ℕ) :
    cacheMultiplies (scalePlan n base sourceCache dot)=n := by
  induction n generalizing base sourceCache dot with
  | zero => rfl
  | succ n ih =>
    have hh := ih (base+2) (sourceCache+3) dot
    simp only [cacheMultiplies] at hh
    simp only [scalePlan,cacheMultiplies,List.map_append,List.sum_append]
    rw [hh]
    norm_num [CacheOp.multiplies]
    omega

/-- A scaling plan performs no cache additions. -/
theorem scalePlan_adds (n base sourceCache dot : ℕ) :
    cacheAdds (scalePlan n base sourceCache dot)=0 := by
  induction n generalizing base sourceCache dot with
  | zero => rfl
  | succ n ih =>
    have hh := ih (base+2) (sourceCache+3) dot
    simp only [cacheAdds] at hh
    simp only [scalePlan,cacheAdds,List.map_append,List.sum_append]
    rw [hh]
    simp

/-- A row plan of width `n` performs exactly `n` source reads. -/
theorem rowPlan_source_reads (n base source weight acc : ℕ) :
    cacheSourceReads (rowPlan n base source weight acc)=n := by
  have hd := dotPlan_source_reads n base source weight acc
  have hs := scalePlan_source_reads n (base+3*n+1) base (base+3*n)
  simp only [cacheSourceReads] at hd hs
  simp only [rowPlan,cacheSourceReads,List.map_append,List.sum_append]
  rw [hd,hs]
  norm_num [CacheOp.sourceReads]

/-- A row plan of width `n` performs exactly `2 * n` cache multiplications. -/
theorem rowPlan_multiplies (n base source weight acc : ℕ) :
    cacheMultiplies (rowPlan n base source weight acc)=2*n := by
  have hd := dotPlan_multiplies n base source weight acc
  have hs := scalePlan_multiplies n (base+3*n+1) base (base+3*n)
  simp only [cacheMultiplies] at hd hs
  simp only [rowPlan,cacheMultiplies,List.map_append,List.sum_append]
  rw [hd,hs]
  norm_num [CacheOp.multiplies]
  omega

/-- A row plan of width `n` performs exactly `n` cache additions. -/
theorem rowPlan_adds (n base source weight acc : ℕ) :
    cacheAdds (rowPlan n base source weight acc)=n := by
  have hd := dotPlan_adds n base source weight acc
  have hs := scalePlan_adds n (base+3*n+1) base (base+3*n)
  simp only [cacheAdds] at hd hs
  simp only [rowPlan,cacheAdds,List.map_append,List.sum_append]
  rw [hd,hs]
  simp

/-- Compiling a row plan of width `n` produces exactly `43 * n` natural-number multiplication
instructions. -/
theorem rowPlan_natural_multiplies (n base source weight acc : ℕ) :
    (compileCache (rowPlan n base source weight acc)).count .multiply=43*n := by
  rw [compileCache_natural_multiplies,rowPlan_adds,rowPlan_multiplies]
  omega

/-- Compiling a row plan of width `n` produces exactly `28 * n` natural-number addition
instructions. -/
theorem rowPlan_natural_adds (n base source weight acc : ℕ) :
    (compileCache (rowPlan n base source weight acc)).count .add=28*n := by
  rw [compileCache_natural_adds,rowPlan_adds,rowPlan_multiplies]
  omega

/-- The output index for the row's dot product when the choice is `none`, or its selected
conjugate-scaled product when the choice is `some j`. -/
def rowOutput (n base : ℕ) : Option ℕ → ℕ
  | none => base+3*n
  | some j => base+3*n+2+2*j

/-- The encoded value selected from a row computation: its dot-product accumulation or a
conjugate-scaled source product. -/
def rowValue (n source weight acc : ℕ) (cs : List GaussianCode) : Option ℕ → GaussianCode
  | none => dotSpec n source weight cs (cs.getD acc GaussianCode.zero)
  | some j => (cs.getD (source+j) GaussianCode.zero).conjugate.mul
      (dotSpec n source weight cs (cs.getD acc GaussianCode.zero))

/-- The Gaussian-rational value selected from a row computation: its dot-product accumulation or
a conjugate-scaled source product. -/
def rowRatValue (n source weight acc : ℕ) (cs : List GaussianRat) : Option ℕ → GaussianRat
  | none => dotRatSpec n source weight cs (cs.getD acc GaussianRat.zero)
  | some j => (cs.getD (source+j) GaussianRat.zero).conjugate.mul
      (dotRatSpec n source weight cs (cs.getD acc GaussianRat.zero))

/-- A dot-product accumulation of valid Gaussian codes, starting from a valid accumulator, is
valid. -/
theorem dotSpec_valid (n source weight : ℕ) (cs : List GaussianCode) (acc : GaussianCode)
    (hcs : ∀ z∈cs,z.Valid) (ha : acc.Valid) : (dotSpec n source weight cs acc).Valid := by
  induction n generalizing source weight acc with
  | zero => exact ha
  | succ n ih =>
    apply ih
    exact GaussianCode.add_valid _ _ ha (GaussianCode.mul_valid _ _
      (code_getD_valid cs hcs source) (code_getD_valid cs hcs weight))

/-- For valid cache entries, decoding a selected encoded row value gives the corresponding
Gaussian-rational row value. -/
theorem rowValue_decode (n source weight acc : ℕ) (cs : List GaussianCode) (choice : Option ℕ)
    (hcs : ∀ z∈cs,z.Valid) :
    (rowValue n source weight acc cs choice).decode=
      rowRatValue n source weight acc (cs.map GaussianCode.decode) choice := by
  have ha := code_getD_valid cs hcs acc
  have hd := dotSpec_valid n source weight cs (cs.getD acc GaussianCode.zero) hcs ha
  cases choice with
  | none =>
    simp only [rowValue,rowRatValue]
    rw [dotSpec_decode _ _ _ _ _ hcs ha,code_decode_getD]
  | some j =>
    simp only [rowValue,rowRatValue]
    rw [GaussianCode.decode_mul _ _ (GaussianCode.conjugate_valid _ (code_getD_valid cs hcs (source+j))) hd,
      GaussianCode.decode_conjugate,dotSpec_decode _ _ _ _ _ hcs ha,code_decode_getD,code_decode_getD]

/-- Converting the Gaussian-rational dot-product specification to a complex number gives the
initial accumulator plus the finite sum of source-weight products. -/
theorem dotRatSpec_toComplex (n source weight : ℕ) (cs : List GaussianRat) (acc : GaussianRat) :
    (dotRatSpec n source weight cs acc).toComplex=acc.toComplex+
      ∑ j ∈ Finset.range n,(cs.getD (source+j) GaussianRat.zero).toComplex*
        (cs.getD (weight+j) GaussianRat.zero).toComplex := by
  induction n generalizing source weight acc with
  | zero => simp [dotRatSpec]
  | succ n ih =>
    rw [dotRatSpec,ih,GaussianRat.toComplex_add,GaussianRat.toComplex_mul,Finset.sum_range_succ']
    have hs : (∑ j ∈ Finset.range n,
        (cs.getD (source+1+j) GaussianRat.zero).toComplex*
          (cs.getD (weight+1+j) GaussianRat.zero).toComplex)=
        ∑ j ∈ Finset.range n,(cs.getD (source+(j+1)) GaussianRat.zero).toComplex*
          (cs.getD (weight+(j+1)) GaussianRat.zero).toComplex := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show source+1+j=source+(j+1) from by omega,
        show weight+1+j=weight+(j+1) from by omega]
    rw [hs]
    simp only [Nat.add_zero]
    rw [add_assoc]
    congr 1
    exact add_comm _ _

/-- The complex dot-product accumulation, optionally multiplied by the complex conjugate of a
selected source entry. -/
noncomputable def rowComplexValue (n source weight acc : ℕ) (cs : List GaussianRat) (choice : Option ℕ) : ℂ :=
  let dot := (cs.getD acc GaussianRat.zero).toComplex+
    ∑ j ∈ Finset.range n,(cs.getD (source+j) GaussianRat.zero).toComplex*
      (cs.getD (weight+j) GaussianRat.zero).toComplex
  match choice with
  | none => dot
  | some j => star (cs.getD (source+j) GaussianRat.zero).toComplex*dot

/-- Converting the selected Gaussian-rational row value to a complex number gives
`rowComplexValue`. -/
theorem rowRatValue_toComplex (n source weight acc : ℕ) (cs : List GaussianRat) (choice : Option ℕ) :
    (rowRatValue n source weight acc cs choice).toComplex=rowComplexValue n source weight acc cs choice := by
  cases choice with
  | none => exact dotRatSpec_toComplex n source weight cs (cs.getD acc GaussianRat.zero)
  | some j =>
    simp only [rowRatValue,rowComplexValue,GaussianRat.toComplex_mul,GaussianRat.toComplex_conjugate,
      dotRatSpec_toComplex]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
