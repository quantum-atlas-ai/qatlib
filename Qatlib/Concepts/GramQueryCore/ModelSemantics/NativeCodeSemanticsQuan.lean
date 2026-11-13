/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Logic.Equiv.Prod
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.GramQueryCore.ModelSemantics.NativeCodeSemanticsStat

/-!
# Encoding and unitary semantics of native programs

Proves injectivity of the bit encodings of rational source problems and native quantum programs.
Prefix decoders recover scalar data, public rows, and gate fields, while register arithmetic
validates the address, answer, tag, and payload layouts.

Wire splitting and lifting identify each native query with a unitary permutation on selected
wires. Together with standard circuit semantics [NielsenChuang2010], these results prove
legal-program unitarity, exact call and gate accounting, and isometry of the clean source frame.

## Main statements

* `sourceProblemBits_injective`, `sourceNativeProgramBits_injective`: establish unambiguous
  encodings.
* `sourceNativeSteps_unitary`: every legal native program evaluates to a unitary matrix.
* `sourceNativeCounts_exact`: calls and gates partition the program steps.
* `sourceNativeFrame_isometry`: a sufficiently wide register gives an isometric source frame.
* `nativeCodeSemantics`: proves the combined encoding and semantics specification.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.GramQueryCore.ModelSemantics
open Matrix
open scoped Classical BigOperators

/-- Counts the initial true bits of a Boolean list and returns the remainder after the next
false delimiter, if present. -/
def nativeReadUnary : List Bool → ℕ × List Bool
  | true::bits => let result := nativeReadUnary bits; (result.1+1,result.2)
  | false::bits => (0,bits)
  | [] => (0,[])

/-- Reads a unary length prefix and splits the remaining Boolean list into the indicated bit
block and its suffix. -/
def nativeReadNatBlock (bits : List Bool) : List Bool × List Bool :=
  let result := nativeReadUnary bits
  (result.2.take result.1,result.2.drop result.1)

/-- A unary prefix of `n` true bits followed by false decodes to `n` and leaves the appended
suffix unchanged. -/
theorem nativeReadUnary_prefix (n : ℕ) (bits : List Bool) :
    nativeReadUnary (List.replicate n true ++ false::bits) = (n,bits) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,nativeReadUnary,ih]

/-- Reading the natural-number encoding followed by a suffix recovers `n.bits` and that suffix. -/
theorem nativeReadNatBlock_prefix (n : ℕ) (suffix : List Bool) :
    nativeReadNatBlock (sourceNatBits n ++ suffix) = (n.bits,suffix) := by
  simp [sourceNatBits,nativeReadNatBlock,List.append_assoc,nativeReadUnary_prefix]

/-- Equality of two natural-number encodings with appended suffixes forces equality of both the
encoded numbers and the suffixes. -/
theorem sourceNatBits_prefix_injective {n m : ℕ} {suffix tail : List Bool}
    (h : sourceNatBits n ++ suffix = sourceNatBits m ++ tail) : n = m ∧ suffix = tail := by
  have hd := congrArg nativeReadNatBlock h
  rw [nativeReadNatBlock_prefix,nativeReadNatBlock_prefix] at hd
  have hbits := congrArg Prod.fst hd
  (try dsimp only at hbits)
  have he : n = m := Nat.eq_of_testBit_eq (fun i => by
    rw [Nat.testBit_eq_inth,Nat.testBit_eq_inth,hbits])
  exact ⟨he,congrArg Prod.snd hd⟩

/-- Every natural-number bit encoding is nonempty. -/
theorem sourceNatBits_nonempty (n : ℕ) : sourceNatBits n ≠ [] := by
  have hh : 0 < (sourceNatBits n).length := by simp [sourceNatBits]
  exact List.ne_nil_of_length_pos hh

/-- Concatenating the bit encodings of a list of natural numbers is an injective encoding of the
list. -/
theorem sourceNatBits_flatMap_injective : Function.Injective (List.flatMap sourceNatBits) := by
  intro ns
  induction ns with
  | nil =>
    intro ms he
    cases ms with
    | nil => rfl
    | cons m ms =>
      have hn := sourceNatBits_nonempty m
      simp only [List.flatMap_nil,List.flatMap_cons] at he
      have h := List.eq_nil_of_append_eq_nil he.symm
      exact False.elim (hn h.1)
  | cons n ns ih =>
    intro ms he
    cases ms with
    | nil =>
      simp only [List.flatMap_nil,List.flatMap_cons] at he
      exact False.elim (sourceNatBits_nonempty n (List.eq_nil_of_append_eq_nil he).1)
    | cons m ms =>
      simp only [List.flatMap_cons] at he
      obtain ⟨hn,ht⟩ := sourceNatBits_prefix_injective he
      subst m
      exact congrArg (List.cons n) (ih ht)

/-- Equality of two integer encodings with appended suffixes forces equality of both the
integers and the suffixes. -/
theorem sourceIntBits_prefix_injective {n m : ℤ} {suffix tail : List Bool}
    (h : sourceIntBits n ++ suffix = sourceIntBits m ++ tail) : n = m ∧ suffix = tail := by
  have hc : decide (n<0) = decide (m<0) ∧
      sourceNatBits n.natAbs ++ suffix = sourceNatBits m.natAbs ++ tail := by
    simpa only [sourceIntBits,List.cons_append,List.cons.injEq] using! h
  obtain ⟨habs,ht⟩ := sourceNatBits_prefix_injective hc.2
  refine ⟨?_,ht⟩
  cases n <;> cases m <;> simp_all <;> omega

/-- Equality of two rational encodings with appended suffixes forces equality of both the
rationals and the suffixes. -/
theorem sourceRatBits_prefix_injective {a b : ℚ} {suffix tail : List Bool}
    (h : sourceRatBits a ++ suffix = sourceRatBits b ++ tail) : a = b ∧ suffix = tail := by
  have hc : sourceIntBits a.num ++ (sourceNatBits a.den ++ suffix) =
      sourceIntBits b.num ++ (sourceNatBits b.den ++ tail) := by
    simpa only [sourceRatBits,List.append_assoc] using! h
  obtain ⟨hn,ht⟩ := sourceIntBits_prefix_injective hc
  obtain ⟨hd,he⟩ := sourceNatBits_prefix_injective ht
  exact ⟨Rat.ext hn hd,he⟩

/-- Concatenated fixed-length tables inherit unique prefix decoding from their entry encoding,
recovering both the table and the appended suffix. -/
theorem nativeEncodedTable_prefix_injective {A : Type} (encode : A → List Bool)
    (hencode : ∀ a b suffix tail, encode a ++ suffix = encode b ++ tail → a = b ∧ suffix = tail)
    (n : ℕ) (f g : Fin n → A) (suffix tail : List Bool)
    (he : (List.ofFn (fun i => encode (f i))).flatten ++ suffix =
      (List.ofFn (fun i => encode (g i))).flatten ++ tail) : f = g ∧ suffix = tail := by
  induction n generalizing suffix tail with
  | zero =>
    refine ⟨funext (fun i => Fin.elim0 i),?_⟩
    simpa using! he
  | succ n ih =>
    simp only [List.ofFn_succ,List.flatten_cons,List.append_assoc] at he
    obtain ⟨h0,ht⟩ := hencode (f 0) (g 0) _ _ he
    obtain ⟨hf,hs⟩ := ih (fun i => f i.succ) (fun i => g i.succ) _ _ ht
    refine ⟨funext (fun i => ?_),hs⟩
    exact Fin.cases h0 (fun j => congrFun hf j) i

/-- Concatenates the rational encodings of four coordinates grouped into two pairs. -/
def nativeCoordinateBits (a : (ℚ × ℚ) × (ℚ × ℚ)) : List Bool :=
  sourceRatBits a.1.1 ++ sourceRatBits a.1.2 ++ sourceRatBits a.2.1 ++ sourceRatBits a.2.2

/-- The four-coordinate encoding uniquely determines both its coordinate data and any appended
suffix. -/
theorem nativeCoordinateBits_prefix_injective
    (a b : (ℚ × ℚ) × (ℚ × ℚ)) (suffix tail : List Bool)
    (he : nativeCoordinateBits a ++ suffix = nativeCoordinateBits b ++ tail) :
    a = b ∧ suffix = tail := by
  simp only [nativeCoordinateBits,List.append_assoc] at he
  obtain ⟨h1,he⟩ := sourceRatBits_prefix_injective he
  obtain ⟨h2,he⟩ := sourceRatBits_prefix_injective he
  obtain ⟨h3,he⟩ := sourceRatBits_prefix_injective he
  obtain ⟨h4,he⟩ := sourceRatBits_prefix_injective he
  exact ⟨Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4),he⟩

/-- Encodes one public problem row by concatenating its input symbol encodings and paired start
and target rational coordinates. -/
def nativePublicRowBits {a h q : ℕ}
    (row : (Fin a → Fin (q+1)) × ((Fin h → ℚ × ℚ) × (Fin h → ℚ × ℚ))) : List Bool :=
  (List.ofFn (fun j => sourceNatBits (row.1 j).val)).flatten ++
    (List.ofFn (fun i => nativeCoordinateBits (row.2.1 i,row.2.2 i))).flatten

/-- The public row encoding uniquely determines both the row data and any appended suffix. -/
theorem nativePublicRowBits_prefix_injective {a h q : ℕ}
    (row other : (Fin a → Fin (q+1)) × ((Fin h → ℚ × ℚ) × (Fin h → ℚ × ℚ)))
    (suffix tail : List Bool)
    (he : nativePublicRowBits row ++ suffix = nativePublicRowBits other ++ tail) :
    row = other ∧ suffix = tail := by
  simp only [nativePublicRowBits,List.append_assoc] at he
  obtain ⟨hinput,he⟩ := nativeEncodedTable_prefix_injective sourceNatBits
    (fun _ _ _ _ h => sourceNatBits_prefix_injective h) a
    (fun j => (row.1 j).val) (fun j => (other.1 j).val) _ _ he
  obtain ⟨hcoord,ht⟩ := nativeEncodedTable_prefix_injective nativeCoordinateBits
    nativeCoordinateBits_prefix_injective h (fun i => (row.2.1 i,row.2.2 i))
    (fun i => (other.2.1 i,other.2.2 i)) _ _ he
  refine ⟨Prod.ext ?_ (Prod.ext ?_ ?_),ht⟩
  · funext j
    exact Fin.ext (congrFun hinput j)
  · funext i
    exact congrArg Prod.fst (congrFun hcoord i)
  · funext i
    exact congrArg Prod.snd (congrFun hcoord i)

/-- The bit encoding of rational source problems is injective. -/
theorem sourceProblemBits_injective : Function.Injective sourceProblemBits := by
  intro d e he
  cases d with
  | mk count dim addr alphabet input start target =>
    cases e with
    | mk count' dim' addr' alphabet' input' start' target' =>
      simp only [sourceProblemBits,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.append_assoc] at he
      obtain ⟨hc,he⟩ := sourceNatBits_prefix_injective he
      obtain ⟨hd,he⟩ := sourceNatBits_prefix_injective he
      obtain ⟨ha,he⟩ := sourceNatBits_prefix_injective he
      obtain ⟨hq,he⟩ := sourceNatBits_prefix_injective he
      subst count'
      subst dim'
      subst addr'
      subst alphabet'
      have he' : (List.ofFn (fun x => nativePublicRowBits (input x,(start x,target x)))).flatten ++ [] =
          (List.ofFn (fun x => nativePublicRowBits (input' x,(start' x,target' x)))).flatten ++ [] := by
        simpa only [nativePublicRowBits,nativeCoordinateBits,List.append_nil,List.append_assoc] using! he
      obtain ⟨hrows,_⟩ := nativeEncodedTable_prefix_injective nativePublicRowBits
        nativePublicRowBits_prefix_injective count (fun x => (input x,(start x,target x)))
        (fun x => (input' x,(start' x,target' x))) [] [] he'
      have hi : input = input' := funext (fun x => congrArg Prod.fst (congrFun hrows x))
      have hs : start = start' := funext (fun x => congrArg (fun r => r.2.1) (congrFun hrows x))
      have ht : target = target' := funext (fun x => congrArg (fun r => r.2.2) (congrFun hrows x))
      subst input'
      subst start'
      subst target'
      rfl

/-- Native gate and query instructions with natural-number wire indices, including Hadamard,
controlled phase, swap, and directed query instructions. -/
inductive NativeRawStep where
  | h : ℕ → NativeRawStep
  | cp : ℕ → ℕ → ℕ → Bool → NativeRawStep
  | swap : ℕ → ℕ → NativeRawStep
  | query : List ℕ → Bool → NativeRawStep

/-- Forgets the bounded wire-index types of a local QFT gate to produce a raw instruction. -/
def nativeRawLocal {w : ℕ} : LocalQFTGate w → NativeRawStep
  | .h a => .h a.val
  | .cp a b k neg => .cp a.val b.val k neg
  | .swap a b => .swap a.val b.val

/-- Forgets the bounded wire-index types of a native step, retaining its gate or directed query
data. -/
def nativeRawStep {w : ℕ} : SourceNativeStep w → NativeRawStep
  | .local g => nativeRawLocal g
  | .query ws adj => .query (ws.map Fin.val) adj

/-- Parses tagged natural-number fields into a raw instruction and its remaining fields,
returning `none` when no instruction pattern matches. -/
def nativeReadRawStep : List ℕ → Option (NativeRawStep × List ℕ)
  | 0::a::rest => some (.h a,rest)
  | 1::a::b::k::neg::rest => some (.cp a b k (decide (neg=1)),rest)
  | 2::a::b::rest => some (.swap a b,rest)
  | 3::adj::len::rest => some (.query (rest.take len) (decide (adj=1)),rest.drop len)
  | _ => none

/-- Parsing an encoded native step followed by a suffix returns its raw instruction and the
unchanged suffix. -/
theorem nativeReadRawStep_prefix {w : ℕ} (s : SourceNativeStep w) (suffix : List ℕ) :
    nativeReadRawStep (sourceNativeStepFields s ++ suffix) = some (nativeRawStep s,suffix) := by
  cases s with
  | «local» g =>
    cases g with
    | h a => rfl
    | cp a b k neg => cases neg <;> rfl
    | swap a b => rfl
  | query ws adj =>
    cases adj <;> simp [sourceNativeStepFields,nativeRawStep,nativeReadRawStep]

/-- For a fixed register width, forgetting the bounded wire-index types of a local gate is
injective. -/
theorem nativeRawLocal_injective {w : ℕ} : Function.Injective (nativeRawLocal (w:=w)) := by
  intro g g' he
  cases g <;> cases g' <;> simp_all [nativeRawLocal,Fin.ext_iff]

/-- For a fixed register width, forgetting the bounded wire-index types of a native step is
injective. -/
theorem nativeRawStep_injective {w : ℕ} : Function.Injective (nativeRawStep (w:=w)) := by
  intro s t he
  cases s with
  | «local» g =>
    cases t with
    | «local» g' => exact congrArg SourceNativeStep.local (nativeRawLocal_injective he)
    | query ws adj => cases g <;> contradiction
  | query ws adj =>
    cases t with
    | «local» g => cases g <;> contradiction
    | query ts adj' =>
      have hh : ws.map Fin.val = ts.map Fin.val ∧ adj = adj' := by
        simpa only [nativeRawStep,NativeRawStep.query.injEq] using! he
      have hws : ws = ts := List.map_injective_iff.mpr (Fin.val_injective) hh.1
      exact congrArg₂ SourceNativeStep.query hws hh.2

/-- For a fixed register width, native step fields uniquely determine both the step and an
appended field suffix. -/
theorem sourceNativeStepFields_prefix_injective {w : ℕ} (s t : SourceNativeStep w)
    (suffix tail : List ℕ)
    (he : sourceNativeStepFields s ++ suffix = sourceNativeStepFields t ++ tail) :
    s = t ∧ suffix = tail := by
  have hd := congrArg nativeReadRawStep he
  rw [nativeReadRawStep_prefix,nativeReadRawStep_prefix] at hd
  have hp := Option.some.inj hd
  exact ⟨nativeRawStep_injective (congrArg Prod.fst hp),congrArg Prod.snd hp⟩

/-- For two step lists of equal length, equality of concatenated step fields with suffixes
forces equality of the lists and suffixes. -/
theorem sourceNativeStepsFields_prefix_injective {w : ℕ} (steps other : List (SourceNativeStep w))
    (hlen : steps.length = other.length) (suffix tail : List ℕ)
    (he : steps.flatMap sourceNativeStepFields ++ suffix = other.flatMap sourceNativeStepFields ++ tail) :
    steps = other ∧ suffix = tail := by
  induction steps generalizing other suffix tail with
  | nil =>
    have ho : other = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst other
    exact ⟨rfl,he⟩
  | cons s steps ih =>
    cases other with
    | nil => simp at hlen
    | cons t other =>
      have htlen : steps.length = other.length := by simpa using! hlen
      simp only [List.flatMap_cons,List.append_assoc] at he
      obtain ⟨hs,ht⟩ := sourceNativeStepFields_prefix_injective s t _ _ he
      obtain ⟨he,hsuf⟩ := ih other htlen _ _ ht
      exact ⟨congrArg₂ List.cons hs he,hsuf⟩

/-- The bit encoding of native programs is injective. -/
theorem sourceNativeProgramBits_injective : Function.Injective sourceNativeProgramBits := by
  intro p q he
  cases p with
  | mk w steps =>
    cases q with
    | mk v other =>
      have hf := sourceNatBits_flatMap_injective he
      change w::steps.length::steps.flatMap sourceNativeStepFields =
        v::other.length::other.flatMap sourceNativeStepFields at hf
      obtain ⟨hw,hf⟩ := List.cons.inj hf
      subst v
      obtain ⟨hlen,hfields⟩ := List.cons.inj hf
      obtain ⟨hs,_⟩ :=
          sourceNativeStepsFields_prefix_injective steps other hlen [] [] (by simpa using! hfields)
      subst other
      rfl

/-- Splits a register into the ordered bits on a duplicate-free wire list and the bits on its
complementary wires. -/
def nativeWireSplit {w : ℕ} (ws : List (Fin w)) (hws : ws.Nodup) :
    Reg w ≃ Reg ws.length × ({i : Fin w // i ∉ ws} → Bool) :=
  (Equiv.piEquivPiSubtypeProd (fun i : Fin w => i ∈ ws) (fun _ => Bool)).trans
    (Equiv.prodCongr
      (Equiv.arrowCongr (List.Nodup.getEquiv ws hws).symm (Equiv.refl Bool)) (Equiv.refl _))

/-- Extends a matrix on selected wires to the full register by tensoring with the identity on
complementary wires and relabeling. -/
def nativeWireLift {w : ℕ} (ws : List (Fin w)) (hws : ws.Nodup)
    (O : Matrix (Reg ws.length) (Reg ws.length) ℂ) : Matrix (Reg w) (Reg w) ℂ :=
  relabelGate (nativeWireSplit ws hws).symm (TensorGate O 1)

/-- Lifting a unitary matrix to a duplicate-free list of wires preserves unitarity. -/
theorem nativeWireLift_unitary {w : ℕ} (ws : List (Fin w)) (hws : ws.Nodup)
    (O : Matrix (Reg ws.length) (Reg ws.length) ℂ)
    (hO : O ∈ Matrix.unitaryGroup _ ℂ) : nativeWireLift ws hws O ∈ Matrix.unitaryGroup _ ℂ :=
  (relabelGate_mem_unitaryGroup _ _).mpr (tensorGate_unitary hO (Submonoid.one_mem _))

/-- A lifted matrix entry equals the selected-wire matrix entry when the complementary bits
agree, and zero otherwise. -/
theorem nativeWireLift_apply {w : ℕ} (ws : List (Fin w)) (hws : ws.Nodup)
    (O : Matrix (Reg ws.length) (Reg ws.length) ℂ) (p t : Reg w) :
    nativeWireLift ws hws O p t =
      if ∀ i : Fin w, i ∉ ws → p i = t i then
        O (fun k => p (ws.get k)) (fun k => t (ws.get k)) else 0 := by
  have hother : (fun i : {i : Fin w // i ∉ ws} => p i.val) =
      (fun i : {i : Fin w // i ∉ ws} => t i.val) ↔ ∀ i : Fin w, i ∉ ws → p i = t i := by
    constructor
    · intro he i hi
      exact congrFun he ⟨i,hi⟩
    · intro he
      funext i
      exact he i.val i.property
  change O (fun k => p (ws.get k)) (fun k => t (ws.get k)) *
      (if (fun i : {i : Fin w // i ∉ ws} => p i.val) =
        (fun i : {i : Fin w // i ∉ ws} => t i.val) then 1 else 0) = _
  by_cases he : ∀ i : Fin w, i ∉ ws → p i = t i
  · rw [if_pos (hother.mpr he),if_pos he,mul_one]
  · rw [if_neg (fun h => he (hother.mp h)),if_neg he,mul_zero]

/-- The number represented by an `n`-bit register is strictly less than `2^n`. -/
theorem nativeRegNumber_lt {n : ℕ} (z : Reg n) : sourceRegNumber z < 2^n := by
  induction n with
  | zero => simp [sourceRegNumber]
  | succ n ih =>
    have hb := ih (fun i => z i.castSucc)
    simp only [sourceRegNumber] at hb ⊢
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.pow_succ]
    cases he : z (Fin.last n) <;> simp at hb ⊢ <;> omega

/-- Converting the low `n` bits of `v` back to a number gives `v % 2^n`. -/
theorem nativeRegNumber_bits (n v : ℕ) : sourceRegNumber (sourceRegBits n v) = v % 2^n := by
  induction n with
  | zero => simp [sourceRegNumber,Nat.mod_one]
  | succ n ih =>
    simp only [sourceRegNumber,sourceRegBits] at ih ⊢
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    simp only [Nat.pow_succ,Nat.mod_mul]
    have hmod := Nat.mod_lt (v/2^n) (by omega : 0<2)
    by_cases he : v/2^n%2=1
    · simpa [Nat.testBit_eq_decide_div_mod_eq,he] using! ih
    · have hz : v/2^n%2=0 := by omega
      simpa [Nat.testBit_eq_decide_div_mod_eq,hz] using! ih

/-- Two natural numbers below `2^n` are equal if their `n`-bit register encodings agree. -/
theorem nativeRegBits_injective_below {n a b : ℕ} (ha : a < 2^n) (hb : b < 2^n)
    (he : sourceRegBits n a = sourceRegBits n b) : a = b := by
  have hn := congrArg sourceRegNumber he
  simpa only [nativeRegNumber_bits,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using! hn

/-- Encoding the number represented by a register recovers that register. -/
theorem nativeRegBits_number {n : ℕ} (z : Reg n) : sourceRegBits n (sourceRegNumber z) = z := by
  let f : Fin (2^n) → Reg n := fun v => sourceRegBits n v.val
  have hf : Function.Injective f := by
    intro a b he
    exact Fin.ext (nativeRegBits_injective_below a.isLt b.isLt he)
  have hs : Function.Surjective f := hf.surjective_of_finite (bitVecEquiv n).symm
  obtain ⟨v,hv⟩ := hs z
  rw [← hv]
  change sourceRegBits n (sourceRegNumber (sourceRegBits n v.val)) = sourceRegBits n v.val
  rw [nativeRegNumber_bits,Nat.mod_eq_of_lt v.isLt]

/-- Converting an `n`-bit register to its represented natural number is injective. -/
theorem nativeRegNumber_injective {n : ℕ} : Function.Injective (sourceRegNumber (n:=n)) := by
  intro z t he
  have hbits := congrArg (sourceRegBits n) he
  simpa only [nativeRegBits_number] using! hbits

/-- Extracts the first `na` bits of a register split into address and answer parts. -/
def nativeAddressPart (na nb : ℕ) (z : Reg (na+nb)) : Reg na :=
  fun i => z ⟨i.val,by omega⟩

/-- Extracts the `nb` answer bits following the first `na` address bits. -/
def nativeAnswerPart (na nb : ℕ) (z : Reg (na+nb)) : Reg nb :=
  fun i => z ⟨na+i.val,by omega⟩

/-- Two packed registers are equal when their address parts and answer parts are equal. -/
theorem nativeParts_ext (na nb : ℕ) (z t : Reg (na+nb))
    (ha : nativeAddressPart na nb z = nativeAddressPart na nb t)
    (hb : nativeAnswerPart na nb z = nativeAnswerPart na nb t) : z = t := by
  funext i
  by_cases hi : i.val < na
  · exact congrFun ha ⟨i.val,hi⟩
  · have hib : i.val-na < nb := by have ht := i.isLt; omega
    have hbit := congrFun hb ⟨i.val-na,hib⟩
    simpa only [nativeAnswerPart,Nat.add_sub_of_le (by omega : na ≤ i.val)] using! hbit

/-- If `j < 2^na`, the address part of the encoding of `j + 2^na*a` is the `na`-bit encoding of
`j`. -/
theorem nativePacked_address (na nb j a : ℕ) (hj : j < 2^na) :
    nativeAddressPart na nb (sourceRegBits (na+nb) (j+2^na*a)) = sourceRegBits na j := by
  funext i
  change (j+2^na*a).testBit i.val = j.testBit i.val
  rw [Nat.add_comm,Nat.testBit_two_pow_mul_add a hj]
  simp only [i.isLt,↓reduceIte]

/-- If `j < 2^na`, the answer part of the encoding of `j + 2^na*a` is the `nb`-bit encoding of
`a`. -/
theorem nativePacked_answer (na nb j a : ℕ) (hj : j < 2^na) :
    nativeAnswerPart na nb (sourceRegBits (na+nb) (j+2^na*a)) = sourceRegBits nb a := by
  funext i
  change (j+2^na*a).testBit (na+i.val) = a.testBit i.val
  rw [Nat.add_comm,Nat.testBit_two_pow_mul_add a hj]
  simp

/-- A packed register is recovered by encoding its address number plus `2^na` times its answer
number. -/
theorem nativePacked_reconstruct (na nb : ℕ) (z : Reg (na+nb)) :
    sourceRegBits (na+nb) (sourceRegNumber (nativeAddressPart na nb z)+
      2^na*sourceRegNumber (nativeAnswerPart na nb z)) = z := by
  apply nativeParts_ext na nb
  · rw [nativePacked_address _ _ _ _ (nativeRegNumber_lt _),nativeRegBits_number]
  · rw [nativePacked_answer _ _ _ _ (nativeRegNumber_lt _),nativeRegBits_number]

/-- The problem input symbol at a valid natural-number address, extended by zero outside the
address range. -/
def nativeSymbol (d : SourceRationalProblem) (x : Fin d.count) (j : ℕ) : Fin (d.alphabet+1) :=
  if hj : j < d.addresses then d.input x ⟨j,hj⟩ else 0

/-- Adds the addressed input symbol modulo the alphabet size to valid answer codes, preserving
the address and fixing codes outside the alphabet. -/
def nativeValueAction (d : SourceRationalProblem) (x : Fin d.count)
    (z : Reg (sourceAddressBits d+sourceValueBits d)) : Reg (sourceAddressBits d+sourceValueBits d) :=
  let na := sourceAddressBits d
  let nb := sourceValueBits d
  let j := sourceRegNumber (nativeAddressPart na nb z)
  let a := sourceRegNumber (nativeAnswerPart na nb z)
  if _ha : a < d.alphabet+1 then
    sourceRegBits (na+nb) (j+2^na*((a+(nativeSymbol d x j).val)%(d.alphabet+1))) else z

/-- Subtracts the addressed input symbol modulo the alphabet size from valid answer codes and
fixes codes outside the alphabet. -/
def nativeValueUndo (d : SourceRationalProblem) (x : Fin d.count)
    (z : Reg (sourceAddressBits d+sourceValueBits d)) : Reg (sourceAddressBits d+sourceValueBits d) :=
  let na := sourceAddressBits d
  let nb := sourceValueBits d
  let j := sourceRegNumber (nativeAddressPart na nb z)
  let a := sourceRegNumber (nativeAnswerPart na nb z)
  if ha : a < d.alphabet+1 then
    sourceRegBits (na+nb) (j+2^na*((⟨a,ha⟩ : Fin (d.alphabet+1))-nativeSymbol d x j).val) else z

/-- The native value action preserves the number represented by the address register. -/
theorem nativeValueAction_address (d : SourceRationalProblem) (x : Fin d.count)
    (z : Reg (sourceAddressBits d+sourceValueBits d)) :
    sourceRegNumber (nativeAddressPart (sourceAddressBits d) (sourceValueBits d) (nativeValueAction d x z)) =
      sourceRegNumber (nativeAddressPart (sourceAddressBits d) (sourceValueBits d) z) := by
  unfold nativeValueAction
  (try dsimp only)
  split_ifs
  · rw [nativePacked_address _ _ _ _ (nativeRegNumber_lt _),nativeRegNumber_bits,
      Nat.mod_eq_of_lt (nativeRegNumber_lt _)]
  · rfl

/-- On valid answer codes, the native value action adds the addressed input symbol modulo
`d.alphabet+1`. -/
theorem nativeValueAction_answer (d : SourceRationalProblem) (x : Fin d.count)
    (z : Reg (sourceAddressBits d+sourceValueBits d))
    (ha : sourceRegNumber (nativeAnswerPart (sourceAddressBits d) (sourceValueBits d) z) < d.alphabet+1) :
    sourceRegNumber (nativeAnswerPart (sourceAddressBits d) (sourceValueBits d) (nativeValueAction d x z)) =
      (sourceRegNumber (nativeAnswerPart (sourceAddressBits d) (sourceValueBits d) z)+
        (nativeSymbol d x (sourceRegNumber (nativeAddressPart (sourceAddressBits d) (sourceValueBits d) z))).val) %
          (d.alphabet+1) := by
  unfold nativeValueAction
  (try dsimp only)
  rw [dif_pos ha,nativePacked_answer _ _ _ _ (nativeRegNumber_lt _),nativeRegNumber_bits]
  apply Nat.mod_eq_of_lt
  exact (Nat.mod_lt _ (by omega)).trans_le (Nat.le_pow_clog (by omega) _)

/-- The native value undo operation is a left inverse of the native value action. -/
theorem nativeValueUndo_leftInverse (d : SourceRationalProblem) (x : Fin d.count) :
    Function.LeftInverse (nativeValueUndo d x) (nativeValueAction d x) := by
  intro z
  let na := sourceAddressBits d
  let nb := sourceValueBits d
  let j := sourceRegNumber (nativeAddressPart na nb z)
  let a := sourceRegNumber (nativeAnswerPart na nb z)
  let v := nativeSymbol d x j
  by_cases ha : a < d.alphabet+1
  · have hn : (a+v.val)%(d.alphabet+1) < d.alphabet+1 := Nat.mod_lt _ (by omega)
    unfold nativeValueUndo
    (try dsimp only)
    rw [nativeValueAction_address,nativeValueAction_answer d x z ha]
    rw [dif_pos hn]
    have he : (⟨(a+v.val)%(d.alphabet+1),hn⟩ : Fin (d.alphabet+1)) =
        (⟨a,ha⟩ : Fin (d.alphabet+1))+v := by
      apply Fin.ext
      simp only [Fin.val_add]
    rw [he,add_sub_cancel_right]
    exact nativePacked_reconstruct na nb z
  · have he : nativeValueAction d x z = z := by simp [nativeValueAction,ha,a,na,nb]
    rw [he]
    simp [nativeValueUndo,ha,a,na,nb]

/-- The native value action is injective. -/
theorem nativeValueAction_injective (d : SourceRationalProblem) (x : Fin d.count) :
    Function.Injective (nativeValueAction d x) := (nativeValueUndo_leftInverse d x).injective

/-- The native value oracle is the permutation matrix of `nativeValueAction`. -/
theorem sourceNativeValueOracle_eq (d : SourceRationalProblem) (x : Fin d.count) :
    sourceNativeValueOracle d x = permMatrix (nativeValueAction d x) := by
  unfold sourceNativeValueOracle
  apply congrArg permMatrix
  funext z
  have hs (j : ℕ) : (nativeSymbol d x j).val =
      if hj : j < d.addresses then (d.input x ⟨j,hj⟩).val else 0 := by
    unfold nativeSymbol
    split_ifs <;> rfl
  unfold nativeValueAction
  simp only [hs]
  rfl

/-- The native value oracle is unitary. -/
theorem sourceNativeValueOracle_unitary (d : SourceRationalProblem) (x : Fin d.count) :
    sourceNativeValueOracle d x ∈ Matrix.unitaryGroup _ ℂ := by
  rw [sourceNativeValueOracle_eq]
  exact permMatrix_unitary_of_injective (nativeValueAction_injective d x)

/-- Lifts a matrix of a specified register size to a duplicate-free wire list whose length
equals that size. -/
def nativeWireLiftSized {w l : ℕ} (ws : List (Fin w)) (hws : ws.Nodup) (hlen : ws.length=l)
    (O : Matrix (Reg l) (Reg l) ℂ) : Matrix (Reg w) (Reg w) ℂ :=
  nativeWireLift ws hws
    (relabelGate (Equiv.arrowCongr (finCongr hlen.symm) (Equiv.refl Bool)) O)

/-- Lifting a unitary matrix to a wire list of matching length preserves unitarity. -/
theorem nativeWireLiftSized_unitary {w l : ℕ} (ws : List (Fin w)) (hws : ws.Nodup)
    (hlen : ws.length=l) (O : Matrix (Reg l) (Reg l) ℂ) (hO : O ∈ Matrix.unitaryGroup _ ℂ) :
    nativeWireLiftSized ws hws hlen O ∈ Matrix.unitaryGroup _ ℂ :=
  nativeWireLift_unitary _ _ _ ((relabelGate_mem_unitaryGroup _ _).mpr hO)

/-- The sized wire lift has the selected-wire matrix entries, with indices transported through
the length equality, when complementary bits agree, and zero otherwise. -/
theorem nativeWireLiftSized_apply {w l : ℕ} (ws : List (Fin w)) (hws : ws.Nodup)
    (hlen : ws.length=l) (O : Matrix (Reg l) (Reg l) ℂ) (p t : Reg w) :
    nativeWireLiftSized ws hws hlen O p t =
      if ∀ i : Fin w, i ∉ ws → p i=t i then
        O (fun k => p (ws.get (Fin.cast hlen.symm k)))
          (fun k => t (ws.get (Fin.cast hlen.symm k))) else 0 := by
  unfold nativeWireLiftSized
  rw [nativeWireLift_apply]
  split_ifs <;> rfl

/-- A forward or adjoint native query on distinct wires of the required address-and-answer width
is unitary. -/
theorem sourceNativeQuery_unitary (d : SourceRationalProblem) (x : Fin d.count) (w : ℕ)
    (ws : List (Fin w)) (adj : Bool) (hws : ws.Nodup)
    (hlen : ws.length=sourceAddressBits d+sourceValueBits d) :
    sourceNativeStepMatrix d x w (.query ws adj) ∈ Matrix.unitaryGroup _ ℂ := by
  let O := sourceNativeValueOracle d x
  have hO : O ∈ Matrix.unitaryGroup _ ℂ := sourceNativeValueOracle_unitary d x
  have hOadj : Oᴴ ∈ Matrix.unitaryGroup _ ℂ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose]
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hO
  have hQ : (if adj then Oᴴ else O) ∈ Matrix.unitaryGroup _ ℂ := by cases adj <;> simp_all
  have he : sourceNativeStepMatrix d x w (.query ws adj) =
      nativeWireLiftSized ws hws hlen (if adj then Oᴴ else O) := by
    ext p t
    rw [nativeWireLiftSized_apply]
    simp only [sourceNativeStepMatrix,dif_pos hlen,O]
  rw [he]
  exact nativeWireLiftSized_unitary _ _ _ _ hQ

/-- Every native program legal for a rational source problem evaluates to a unitary matrix on
every input. -/
theorem sourceNativeSteps_unitary (d : SourceRationalProblem) (p : SourceNativeProgram)
    (hlegal : sourceNativeLegal d p) (x : Fin d.count) :
    sourceNativeMatrix d x p ∈ Matrix.unitaryGroup _ ℂ := by
  have hsteps : ∀ s ∈ p.steps, sourceNativeStepMatrix d x p.width s ∈ Matrix.unitaryGroup _ ℂ := by
    intro s hs
    have hl := hlegal s hs
    cases s with
    | «local» g => exact localGateMatrix_unitary g
    | query ws adj => exact sourceNativeQuery_unitary d x p.width ws adj hl.1 hl.2
  have hp : ∀ gs : List (Matrix (Reg p.width) (Reg p.width) ℂ),
      (∀ M ∈ gs, M ∈ Matrix.unitaryGroup _ ℂ) → gs.prod ∈ Matrix.unitaryGroup _ ℂ := by
    intro gs
    induction gs with
    | nil => simp
    | cons M gs ih =>
      intro h
      exact Submonoid.mul_mem _ (h M List.mem_cons_self)
        (ih (fun A hA => h A (List.mem_cons_of_mem M hA)))
  apply hp
  intro M hM
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hM)
  exact hsteps s hs

/-- The oracle call count plus the gate count equals the number of native program steps. -/
theorem sourceNativeCounts_exact (p : SourceNativeProgram) :
    sourceNativeCalls p+sourceNativeGates p=p.steps.length := by
  have hh := (List.length_eq_countP_add_countP
    (fun s : SourceNativeStep p.width => match s with | .local _ => false | .query _ _ => true)
    (l:=p.steps)).symm
  unfold sourceNativeCalls sourceNativeGates
  convert! hh using 1
  congr 1
  apply congrArg (fun f : SourceNativeStep p.width → Bool => p.steps.countP f)
  funext s
  cases s <;> rfl

/-- The register index encoding a Boolean tag and payload basis element above zero address and
answer bits. -/
def nativeFrameIndex (d : SourceRationalProblem) (t : Bool × Fin d.dimension) : ℕ :=
  (if t.1 then 1 else 0)*2^(sourceAddressBits d+sourceValueBits d) +
    t.2.val*2^(sourceAddressBits d+sourceValueBits d+1)

/-- Factors the frame index as the tag-and-payload number times `2^(sourceAddressBits d +
sourceValueBits d)`. -/
theorem nativeFrameIndex_factor (d : SourceRationalProblem) (t : Bool × Fin d.dimension) :
    nativeFrameIndex d t = ((if t.1 then 1 else 0)+2*t.2.val)*
      2^(sourceAddressBits d+sourceValueBits d) := by
  unfold nativeFrameIndex
  rw [Nat.pow_succ]
  ring

/-- The frame index is below `2^w` when `w` accommodates the address, answer, tag, and payload
bits. -/
theorem nativeFrameIndex_lt (d : SourceRationalProblem) (w : ℕ)
    (hw : sourceAddressBits d+sourceValueBits d+1+sourcePayloadBits d ≤ w)
    (t : Bool × Fin d.dimension) : nativeFrameIndex d t < 2^w := by
  have ht : t.2.val < 2^sourcePayloadBits d :=
    t.2.isLt.trans_le (Nat.le_pow_clog (by omega) _)
  have hb : (if t.1 then 1 else 0 : ℕ) ≤ 1 := by cases t.1 <;> simp
  have hc : ((if t.1 then 1 else 0)+2*t.2.val : ℕ) < 2^(sourcePayloadBits d+1) := by
    rw [Nat.pow_succ]
    omega
  rw [nativeFrameIndex_factor]
  apply (Nat.mul_lt_mul_of_pos_right hc (by positivity)).trans_le
  rw [← Nat.pow_add]
  exact Nat.pow_le_pow_right (by omega) (by omega)

/-- The natural-number frame index is injective on tag and payload labels. -/
theorem nativeFrameIndex_injective (d : SourceRationalProblem) : Function.Injective (nativeFrameIndex d) := by
  intro t u he
  rw [nativeFrameIndex_factor,nativeFrameIndex_factor] at he
  have hp : 0 < 2^(sourceAddressBits d+sourceValueBits d) := by positivity
  have hc := Nat.eq_of_mul_eq_mul_right hp he
  have hb : t.1 = u.1 := by
    cases ht : t.1 <;> cases hu : u.1 <;> simp_all <;> omega
  have hv : t.2.val = u.2.val := by
    rw [hb] at hc
    omega
  exact Prod.ext hb (Fin.ext hv)

/-- For a sufficiently wide register, encoding frame indices as bit registers is injective on
tag and payload labels. -/
theorem nativeFrameBasis_injective (d : SourceRationalProblem) (w : ℕ)
    (hw : sourceAddressBits d+sourceValueBits d+1+sourcePayloadBits d ≤ w) :
    Function.Injective (fun t : Bool × Fin d.dimension => sourceRegBits w (nativeFrameIndex d t)) := by
  intro t u he
  apply nativeFrameIndex_injective d
  exact nativeRegBits_injective_below (nativeFrameIndex_lt d w hw t)
      (nativeFrameIndex_lt d w hw u) he

/-- The native source frame is an isometry when the register accommodates the address, answer,
tag, and payload bits. -/
theorem sourceNativeFrame_isometry (d : SourceRationalProblem) (w : ℕ)
    (hw : sourceAddressBits d+sourceValueBits d+1+sourcePayloadBits d ≤ w) :
    (sourceNativeFrame d w)ᴴ * sourceNativeFrame d w = 1 := by
  have hinj := nativeFrameBasis_injective d w hw
  ext t u
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply]
  change (∑ z : Reg w, star (if z=sourceRegBits w (nativeFrameIndex d t) then (1 : ℂ) else 0)*
    (if z=sourceRegBits w (nativeFrameIndex d u) then 1 else 0)) = if t=u then 1 else 0
  rw [Finset.sum_eq_single (sourceRegBits w (nativeFrameIndex d t))]
  · simp [hinj.eq_iff]
  · intro z _ hz
    simp [hz]
  · simp

/-- Proves native program and problem encoding injectivity, legal-program unitarity, exact step
accounting, and source-frame isometry under the width condition. -/
theorem nativeCodeSemantics : NativeCodeSemantics := by
  refine ⟨sourceNativeProgramBits_injective,sourceProblemBits_injective,?_⟩
  intro d p hlegal x
  exact ⟨sourceNativeSteps_unitary d p hlegal x,sourceNativeCounts_exact p,
    sourceNativeFrame_isometry d p.width⟩

end Qatlib.Concepts.GramQueryCore.ModelSemantics
