/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.BooleanSimonRecovery
import Qatlib.Concepts.WalshMoment.Forrelation.BooleanHadamardPhase
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost

/-!
# Boolean Gaussian elimination and Simon decoding

This module implements Gaussian elimination on Boolean registers using pivot rows and XOR
operations. It proves preservation of row spans, echelon invariants, and correctness of back
substitution, then constructs a linearly independent spanning list for the pivot kernel.

The decoder `decodeSimonSecret` returns the unique secret encoded by a candidate subgroup of
cardinality at most two, and returns `none` for larger candidates. Explicit operation counters
bound the elimination and kernel construction costs. See [Simon1997] for the mathematical
background.

## Main statements

* `boolean_gaussian_actual_echelon`: echelon form, row-span preservation, and an XOR-count
  bound.
* `boolean_gaussian_kernel_basis`: independence and spanning for the constructed kernel list.
* `boolean_gaussian_simon_decode_iff`: characterize a successful decoded secret.
* `boolean_gaussian_actual_operation_bound`: bound the recorded bit-operation counts.

## References

* [Simon, 1997][Simon1997]
-/

set_option warningAsError false

open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open scoped Classical

/-- Coordinatewise exclusive-or of two Boolean registers. -/
def regXor {n : ℕ} (x y : Reg n) : Reg n := fun i => x i ^^ y i

/-- Coordinatewise register XOR evaluates to Boolean exclusive-or at each index. -/
@[simp] theorem regXor_apply {n : ℕ} (x y : Reg n) (i : Fin n) :
    regXor x y i = (x i ^^ y i) := rfl

/-- The Boolean-to-`ZMod 2` equivalence sends exclusive-or to addition. -/
theorem boolZModEquiv_xor (a b : Bool) :
    boolZModEquiv (a ^^ b) = boolZModEquiv a + boolZModEquiv b := by
  cases a <;> cases b <;> decide

/-- The register equivalence sends coordinatewise XOR to vector addition over `ZMod 2`. -/
theorem regBooleanEquiv_xor {n : ℕ} (x y : Reg n) :
    regBooleanEquiv n (regXor x y) = regBooleanEquiv n x + regBooleanEquiv n y := by
  funext i
  simp only [regBooleanEquiv_apply, Pi.add_apply]
  exact boolZModEquiv_xor _ _

/-- The all-false register maps to the zero Boolean vector. -/
@[simp] theorem regBooleanEquiv_zeroStr (n : ℕ) :
    regBooleanEquiv n (ZeroStr n) = 0 := by
  funext i
  simp [ZeroStr]

/-- The equivalence from Boolean registers to Boolean vectors is injective. -/
theorem regBooleanEquiv_injective (n : ℕ) :
    Function.Injective (regBooleanEquiv n) := (regBooleanEquiv n).injective

/-- The XOR of a register with itself is the all-false register. -/
@[simp] theorem regXor_self {n : ℕ} (x : Reg n) : regXor x x = ZeroStr n := by
  funext i
  simp [ZeroStr]

/-- Register XOR is associative. -/
theorem regXor_assoc {n : ℕ} (x y z : Reg n) :
    regXor (regXor x y) z = regXor x (regXor y z) := by
  funext i
  simp

/-- Register XOR is commutative. -/
theorem regXor_comm {n : ℕ} (x y : Reg n) : regXor x y = regXor y x := by
  funext i
  simp [Bool.xor_comm]

/-- XOR with the all-false register on the right preserves a register. -/
@[simp] theorem regXor_zeroStr {n : ℕ} (x : Reg n) : regXor x (ZeroStr n) = x := by
  funext i
  simp [ZeroStr]

/-- XOR with the all-false register on the left preserves a register. -/
@[simp] theorem zeroStr_regXor {n : ℕ} (x : Reg n) : regXor (ZeroStr n) x = x := by
  funext i
  simp [ZeroStr]

/-- Subtraction of encoded Boolean registers equals the encoding of their XOR. -/
theorem regBooleanEquiv_sub {n : ℕ} (x y : Reg n) :
    regBooleanEquiv n x - regBooleanEquiv n y = regBooleanEquiv n (regXor x y) := by
  rw [regBooleanEquiv_xor]
  funext i
  cases hx : x i <;> cases hy : y i <;>
    simp only [regBooleanEquiv_apply, Pi.sub_apply, Pi.add_apply, hx, hy,
      boolZModEquiv_true, boolZModEquiv_false] <;> decide

/-- The Boolean dot product is symmetric. -/
theorem booleanDot_comm' {n : ℕ} (a x : BooleanVec n) :
    booleanDot a x = booleanDot x a := by
  simp only [booleanDot]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- The Boolean dot product is additive in its left argument. -/
theorem booleanDot_add_left {n : ℕ} (a b x : BooleanVec n) :
    booleanDot (a + b) x = booleanDot a x + booleanDot b x := by
  simp [booleanDot, add_mul, Finset.sum_add_distrib]

/-- Negating the left argument negates the Boolean dot product. -/
theorem booleanDot_neg_left {n : ℕ} (a x : BooleanVec n) :
    booleanDot (-a) x = -booleanDot a x := by
  simp [booleanDot]

/-- The Boolean dot product is additive in its right argument. -/
theorem booleanDot_add_right {n : ℕ} (a x y : BooleanVec n) :
    booleanDot a (x + y) = booleanDot a x + booleanDot a y := by
  simp [booleanDot, mul_add, Finset.sum_add_distrib]

/-- Negating the right argument negates the Boolean dot product. -/
theorem booleanDot_neg_right {n : ℕ} (a x : BooleanVec n) :
    booleanDot a (-x) = -booleanDot a x := by
  simp [booleanDot]

/-- Compute the Boolean dot product as the XOR of coordinatewise conjunctions. -/
def booleanDotBool {n : ℕ} (r x : Reg n) : Bool :=
  (List.finRange n).foldl (fun acc i => acc ^^ (r i && x i)) false

/-- The Boolean implementation of the dot product agrees with `booleanDot` after encoding in
`ZMod 2`. -/
theorem boolZModEquiv_booleanDotBool {n : ℕ} (r x : Reg n) :
    boolZModEquiv (booleanDotBool r x) =
      booleanDot (regBooleanEquiv n r) (regBooleanEquiv n x) := by
  unfold booleanDotBool
  rw [booleanDot_regBooleanEquiv]
  have hgen : ∀ (l : List (Fin n)) (b : Bool),
      boolZModEquiv (l.foldl (fun acc i => acc ^^ (r i && x i)) b) =
        boolZModEquiv b + (l.map (fun i => boolZModEquiv (r i && x i))).sum := by
    intro l b
    induction l generalizing b with
    | nil => simp
    | cons i l ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, boolZModEquiv_xor]
      ring
  rw [hgen, show (List.finRange n).map (fun i => boolZModEquiv (r i && x i)) =
      List.ofFn (fun i => boolZModEquiv (r i && x i)) by
    rw [List.ofFn_eq_map]]
  simp [List.sum_ofFn]

/-- The Boolean dot product is false exactly when the encoded vector dot product is zero. -/
theorem booleanDotBool_eq_false_iff {n : ℕ} (r x : Reg n) :
    booleanDotBool r x = false ↔
      booleanDot (regBooleanEquiv n r) (regBooleanEquiv n x) = 0 := by
  rw [← boolZModEquiv_booleanDotBool, ← boolZModEquiv_false]
  exact (boolZModEquiv.injective.eq_iff).symm

/-- A table of optional pivot rows together with XOR and bit-operation counters. -/
structure BooleanEchelonResult (n : ℕ) where
  pivots : Fin n → Option (Reg n)
  xorCount : ℕ
  bitOps : ℕ

/-- Each occupied pivot row has a true pivot bit and false bits in every earlier column. -/
def IsBooleanEchelon {n : ℕ} (piv : Fin n → Option (Reg n)) : Prop :=
  ∀ i row, piv i = some row → row i = true ∧ ∀ j, j < i → row j = false

/-- The additive subgroup generated by the encoded rows in a pivot table. -/
def booleanPivotSpan {n : ℕ} (piv : Fin n → Option (Reg n)) :
    AddSubgroup (BooleanVec n) :=
  AddSubgroup.closure {v | ∃ i row, piv i = some row ∧ v = regBooleanEquiv n row}

/-- Every occupied pivot row, encoded as a Boolean vector, belongs to the pivot span. -/
theorem mem_booleanPivotSpan_of_piv {n : ℕ} {piv : Fin n → Option (Reg n)}
    {i : Fin n} {row : Reg n} (h : piv i = some row) :
    regBooleanEquiv n row ∈ booleanPivotSpan piv :=
  AddSubgroup.subset_closure ⟨i, row, h, rfl⟩

/-- The subgroup of vectors orthogonal to every occupied pivot row. -/
def booleanPivotKernel {n : ℕ} (piv : Fin n → Option (Reg n)) :
    AddSubgroup (BooleanVec n) where
  carrier := {x | ∀ i row, piv i = some row → booleanDot (regBooleanEquiv n row) x = 0}
  zero_mem' := by
    intro i row _
    simp [booleanDot]
  add_mem' := by
    intro x y hx hy i row hrow
    rw [booleanDot_add_right, hx i row hrow, hy i row hrow, add_zero]
  neg_mem' := by
    intro x hx i row hrow
    rw [booleanDot_neg_right, hx i row hrow, neg_zero]

/-- Membership in the pivot kernel means having zero dot product with every occupied pivot row. -/
@[simp] theorem mem_booleanPivotKernel {n : ℕ} (piv : Fin n → Option (Reg n))
    (x : BooleanVec n) :
    x ∈ booleanPivotKernel piv ↔
      ∀ i row, piv i = some row → booleanDot (regBooleanEquiv n row) x = 0 :=
  Iff.rfl

/-- The additive subgroup generated by the encodings of the rows in a list. -/
def booleanRowsSpan {n : ℕ} (rows : List (Reg n)) : AddSubgroup (BooleanVec n) :=
  AddSubgroup.closure {v | ∃ r, r ∈ rows ∧ v = regBooleanEquiv n r}

/-- The encoding of any listed row belongs to the row span. -/
theorem mem_booleanRowsSpan_of_mem {n : ℕ} {rows : List (Reg n)} {r : Reg n}
    (h : r ∈ rows) :
    regBooleanEquiv n r ∈ booleanRowsSpan rows :=
  AddSubgroup.subset_closure ⟨r, h, rfl⟩

/-- The pivot kernel is the Boolean orthogonal complement of the pivot span. -/
theorem booleanPivotKernel_eq_booleanOrthogonal_span {n : ℕ}
    (piv : Fin n → Option (Reg n)) :
    booleanPivotKernel piv = booleanOrthogonal (booleanPivotSpan piv) := by
  ext x
  rw [mem_booleanPivotKernel, mem_booleanOrthogonal]
  constructor
  · intro hx a
    apply AddSubgroup.closure_induction
      (k := {v | ∃ i row, piv i = some row ∧ v = regBooleanEquiv n row})
      (p := fun y _ => booleanDot x y = 0) (x := a)
    · intro y hy
      rcases hy with ⟨i, row, hrow, rfl⟩
      rw [booleanDot_comm']
      exact hx i row hrow
    · simp [booleanDot]
    · intro y z _ _ hy0 hz0
      rw [booleanDot_add_right, hy0, hz0, add_zero]
    · intro y _ hy0
      rw [booleanDot_neg_right, hy0, neg_zero]
    · exact a.property
  · intro hx i row hrow
    rw [booleanDot_comm']
    exact hx ⟨regBooleanEquiv n row, mem_booleanPivotSpan_of_piv hrow⟩

/-- Summing a function along `List.finRange n` equals its finite sum over `Fin n`. -/
theorem listSum_finRange_map {M : Type*} [AddCommMonoid M] :
    ∀ (n : ℕ) (f : Fin n → M), ((List.finRange n).map f).sum = ∑ i, f i := by
  intro n f
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ_last, List.map_append, List.map_map, List.sum_append,
      List.map_singleton, List.sum_singleton, ih, Fin.sum_univ_castSucc]
    simp only [Function.comp_apply]

/-- Encoding an XOR fold in `ZMod 2` gives the initial encoded bit plus the sum of encoded input
bits. -/
theorem boolZModEquiv_foldl_xor {ι : Type*} (l : List ι) (g : ι → Bool) (b : Bool) :
    boolZModEquiv (l.foldl (fun acc i => acc ^^ g i) b) =
      boolZModEquiv b + (l.map (fun i => boolZModEquiv (g i))).sum := by
  induction l generalizing b with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, boolZModEquiv_xor]
    ring

/-- A position-dependent invariant preserved at each list entry holds after folding the entire
list. -/
theorem foldl_induction_position {α β : Type*} (l : List β) (f : α → β → α) :
    ∀ (init : α) (P : ℕ → α → Prop), P 0 init →
      (∀ (k : ℕ) (hk : k < l.length) (acc : α),
        P k acc → P (k + 1) (f acc l[k])) →
      P l.length (l.foldl f init) := by
  induction l with
  | nil => intro init P h0 _; exact h0
  | cons b l ih =>
    intro init P h0 hstep
    simp only [List.foldl_cons, List.length_cons]
    apply ih (f init b) (fun k acc => P (k + 1) acc)
    · have h := hstep 0 (by simp) init h0
      simpa using h
    · intro k hk acc hacc
      have h := hstep (k + 1) (by simp only [List.length_cons]; omega) acc hacc
      rwa [List.getElem_cons_succ] at h

/-- An invariant indexed by the number of processed coordinates holds after folding over
`List.finRange n`. -/
theorem foldl_finRange_induction {α : Type*} {n : ℕ} (f : α → Fin n → α) (init : α)
    (P : ℕ → α → Prop) (h0 : P 0 init)
    (hstep : ∀ (k : ℕ) (hk : k < n) (acc : α), P k acc → P (k + 1) (f acc ⟨k, hk⟩)) :
    P n ((List.finRange n).foldl f init) := by
  have h := foldl_induction_position (List.finRange n) f init P h0 (fun k hk acc hacc => by
    rw [List.length_finRange] at hk
    have hget : (List.finRange n)[k] = ⟨k, hk⟩ := by
      rw [List.getElem_finRange]
      exact Fin.ext rfl
    rw [hget]
    exact hstep k hk acc hacc)
  rwa [List.length_finRange] at h

/-- A Boolean row together with the XOR and bit-operation counts accumulated during reduction. -/
structure ReduceAccum (n : ℕ) where
  row : Reg n
  xorCount : ℕ
  bitOps : ℕ

/-- At a true coordinate with an occupied pivot, XOR the accumulator row with that pivot row and
update operation counts. -/
def booleanReduceStep {n : ℕ} (piv : Fin n → Option (Reg n)) (acc : ReduceAccum n)
    (i : Fin n) : ReduceAccum n :=
  if acc.row i then
    match piv i with
    | some p => ⟨regXor acc.row p, acc.xorCount + 1, acc.bitOps + (2 + 3 * n + n)⟩
    | none => ⟨acc.row, acc.xorCount, acc.bitOps + 2⟩
  else ⟨acc.row, acc.xorCount, acc.bitOps + 2⟩

/-- Reduce a row against all pivot columns in increasing order, starting both operation counters
at zero. -/
def booleanReduceFull {n : ℕ} (piv : Fin n → Option (Reg n)) (x : Reg n) :
    ReduceAccum n :=
  (List.finRange n).foldl (booleanReduceStep piv) ⟨x, 0, 0⟩

/-- The row component of the full pivot reduction. -/
def booleanReduceRow {n : ℕ} (piv : Fin n → Option (Reg n)) (x : Reg n) : Reg n :=
  (booleanReduceFull piv x).row

/-- For an echelon pivot table, full reduction changes the row by an element of the pivot span,
clears all pivot columns, and satisfies the stated operation bounds. -/
theorem booleanReduceFull_invariant {n : ℕ} (piv : Fin n → Option (Reg n)) (x : Reg n)
    (hech : IsBooleanEchelon piv) :
    regBooleanEquiv n (booleanReduceFull piv x).row - regBooleanEquiv n x ∈
        booleanPivotSpan piv ∧
      (∀ i row, piv i = some row → (booleanReduceFull piv x).row i = false) ∧
      (booleanReduceFull piv x).xorCount ≤ n ∧
      (booleanReduceFull piv x).bitOps ≤ n * (2 + 4 * n) := by
  have h := foldl_finRange_induction (booleanReduceStep piv)
    ⟨x, 0, 0⟩
    (fun k acc =>
      regBooleanEquiv n acc.row - regBooleanEquiv n x ∈ booleanPivotSpan piv ∧
      (∀ j row, piv j = some row → j.val < k → acc.row j = false) ∧
      acc.xorCount ≤ k ∧ acc.bitOps ≤ k * (2 + 4 * n))
    (by
      refine ⟨?_, ?_, Nat.zero_le _, Nat.zero_le _⟩
      · simp
      · intro j row hj hjk
        omega)
    (by
      intro k hk acc hacc
      obtain ⟨hspan, hbits, hxc, hbo⟩ := hacc
      unfold booleanReduceStep
      split
      · rename_i hbit
        split
        · rename_i p hp
          obtain ⟨hpi, hplow⟩ := hech ⟨k, hk⟩ p hp
          refine ⟨?_, ?_, Nat.succ_le_succ hxc, ?_⟩
          · have h1 : regBooleanEquiv n (regXor acc.row p) - regBooleanEquiv n x =
                (regBooleanEquiv n acc.row - regBooleanEquiv n x) +
                  regBooleanEquiv n p := by
              rw [regBooleanEquiv_xor]
              abel
            rw [h1]
            exact add_mem hspan (mem_booleanPivotSpan_of_piv hp)
          · intro j row hj hjk
            have hle : j.val ≤ k := Nat.lt_succ_iff.mp hjk
            by_cases hjk' : j.val < k
            · have hpj : p j = false := hplow j hjk'
              simp only [regXor_apply, hbits j row hj hjk', hpj, Bool.false_xor]
            · have hji : j = ⟨k, hk⟩ := Fin.ext (Nat.le_antisymm hle (Nat.not_lt.mp hjk'))
              subst hji
              have hrow : row = p := by
                have hpj : piv ⟨k, hk⟩ = some row := hj
                rw [hp] at hpj
                exact (Option.some.inj hpj).symm
              subst hrow
              simp [regXor_apply, hpi, hbit]
          · show acc.bitOps + (2 + 3 * n + n) ≤ (k + 1) * (2 + 4 * n)
            have hb1 : (k + 1) * (2 + 4 * n) = k * (2 + 4 * n) + (2 + 4 * n) :=
              Nat.succ_mul k _
            omega
        · rename_i hpiv
          refine ⟨hspan, ?_, hxc.trans (Nat.le_succ k), ?_⟩
          · intro j row hj hjk
            have hle : j.val ≤ k := Nat.lt_succ_iff.mp hjk
            by_cases hjk' : j.val < k
            · exact hbits j row hj hjk'
            · have hji : j = ⟨k, hk⟩ := Fin.ext (Nat.le_antisymm hle (Nat.not_lt.mp hjk'))
              subst hji
              rw [hpiv] at hj
              simp at hj
          · show acc.bitOps + 2 ≤ (k + 1) * (2 + 4 * n)
            have hb1 : (k + 1) * (2 + 4 * n) = k * (2 + 4 * n) + (2 + 4 * n) :=
              Nat.succ_mul k _
            omega
      · rename_i hbit
        refine ⟨hspan, ?_, hxc.trans (Nat.le_succ k), ?_⟩
        · intro j row hj hjk
          have hle : j.val ≤ k := Nat.lt_succ_iff.mp hjk
          by_cases hjk' : j.val < k
          · exact hbits j row hj hjk'
          · have hji : j = ⟨k, hk⟩ := Fin.ext (Nat.le_antisymm hle (Nat.not_lt.mp hjk'))
            subst hji
            have hfalse : acc.row ⟨k, hk⟩ = false := by
              cases hb : acc.row ⟨k, hk⟩ with
              | false => rfl
              | true => simp [hb] at hbit
            exact hfalse
        · show acc.bitOps + 2 ≤ (k + 1) * (2 + 4 * n)
          have hb1 : (k + 1) * (2 + 4 * n) = k * (2 + 4 * n) + (2 + 4 * n) :=
            Nat.succ_mul k _
          omega)
  obtain ⟨hspan, hbits, hxc, hbo⟩ := h
  exact ⟨hspan, fun i row hi => hbits i row hi i.isLt, hxc, hbo⟩

/-- Reduction against an echelon pivot table preserves the row modulo the pivot span and clears
every occupied pivot column. -/
theorem boolean_gaussian_reduce_invariant {n : ℕ} (piv : Fin n → Option (Reg n))
    (x : Reg n) :
    IsBooleanEchelon piv →
    regBooleanEquiv n (booleanReduceRow piv x) - regBooleanEquiv n x ∈
        booleanPivotSpan piv ∧
      (∀ i row, piv i = some row → booleanReduceRow piv x i = false) := by
  intro hech
  have h := booleanReduceFull_invariant piv x hech
  exact ⟨h.1, h.2.1⟩

/-- Retain an already found coordinate or record a true bit at the current coordinate,
increasing the scan count by one. -/
def booleanFindFirstStep {n : ℕ} (x : Reg n) (acc : Option (Fin n) × ℕ) (i : Fin n) :
    Option (Fin n) × ℕ :=
  (match acc.1 with
   | some j => some j
   | none => if x i then some i else none, acc.2 + 1)

/-- Scan a register in increasing coordinate order for its first true bit, recording the scan
count. -/
def booleanFindFirstTrue {n : ℕ} (x : Reg n) : Option (Fin n) × ℕ :=
  (List.finRange n).foldl (booleanFindFirstStep x) (none, 0)

/-- The scan returns the first true coordinate or certifies that all bits are false, and its
count equals `n`. -/
theorem booleanFindFirstTrue_sound {n : ℕ} (x : Reg n) :
    (∀ i, (booleanFindFirstTrue x).1 = some i →
        x i = true ∧ ∀ j, j < i → x j = false) ∧
      ((booleanFindFirstTrue x).1 = none → ∀ i, x i = false) ∧
      (booleanFindFirstTrue x).2 = n := by
  have h := foldl_finRange_induction (booleanFindFirstStep x)
    (none, 0)
    (fun k acc =>
      (acc.1 = none → ∀ j, j.val < k → x j = false) ∧
      (∀ j, acc.1 = some j → j.val < k ∧ x j = true ∧ ∀ l, l < j → x l = false) ∧
      acc.2 = k)
    (by
      refine ⟨fun _ j hj => by omega, fun j hj => by simp at hj, rfl⟩)
    (by
      intro k hk acc hacc
      obtain ⟨hnone, hsome, hcount⟩ := hacc
      unfold booleanFindFirstStep
      split
      · rename_i j hj
        refine ⟨fun h => by simp at h, ?_, ?_⟩
        · intro j' hj'
          cases hj'
          obtain ⟨hlt, htrue, hlow⟩ := hsome j hj
          exact ⟨Nat.lt_succ_of_lt hlt, htrue, hlow⟩
        · simp [hcount]
      · rename_i hacc1
        split
        · rename_i hxi
          refine ⟨fun h => by simp at h, ?_, ?_⟩
          · intro j' hj'
            cases hj'
            refine ⟨Nat.lt_succ_iff.mpr (Nat.le_refl k), hxi, ?_⟩
            intro l hl
            apply hnone hacc1 l
            have : l < ⟨k, hk⟩ := hl
            exact this
          · simp [hcount]
        · rename_i hxi
          refine ⟨?_, fun j hj => by simp at hj, ?_⟩
          · intro _ j hj
            have hle : j.val ≤ k := Nat.lt_succ_iff.mp hj
            by_cases hjk : j.val < k
            · exact hnone hacc1 j hjk
            · have hji : j = ⟨k, hk⟩ := Fin.ext (Nat.le_antisymm hle (Nat.not_lt.mp hjk))
              subst hji
              cases hxk : x ⟨k, hk⟩ with
              | false => rfl
              | true => simp [hxk] at hxi
          · simp [hcount])
  obtain ⟨hnone, hsome, hcount⟩ := h
  refine ⟨fun i hi => ?_, fun h j => hnone h j j.isLt, hcount⟩
  obtain ⟨-, htrue, hlow⟩ := hsome i hi
  exact ⟨htrue, hlow⟩

/-- Reduce an input row, insert a nonzero remainder at its first true coordinate, and accumulate
the reduction and insertion costs. -/
def booleanInsertRow {n : ℕ} (acc : BooleanEchelonResult n) (x : Reg n) :
    BooleanEchelonResult n :=
  match (booleanFindFirstTrue (booleanReduceFull acc.pivots x).row).1 with
  | none => ⟨acc.pivots, acc.xorCount + (booleanReduceFull acc.pivots x).xorCount,
      acc.bitOps + (booleanReduceFull acc.pivots x).bitOps +
        (booleanFindFirstTrue (booleanReduceFull acc.pivots x).row).2⟩
  | some i => ⟨Function.update acc.pivots i (some (booleanReduceFull acc.pivots x).row),
      acc.xorCount + (booleanReduceFull acc.pivots x).xorCount,
      acc.bitOps + (booleanReduceFull acc.pivots x).bitOps +
        (booleanFindFirstTrue (booleanReduceFull acc.pivots x).row).2 + n⟩

/-- Insert a list of rows into an initial pivot table with operation counters initialized to
zero. -/
def booleanEchelonContinue {n : ℕ} (piv : Fin n → Option (Reg n)) (rows : List (Reg n)) :
    BooleanEchelonResult n :=
  rows.foldl booleanInsertRow ⟨piv, 0, 0⟩

/-- Run Boolean elimination on a row list starting from an empty pivot table. -/
def booleanEchelonRun {n : ℕ} (rows : List (Reg n)) : BooleanEchelonResult n :=
  booleanEchelonContinue (fun _ => none) rows

/-- The empty pivot table satisfies the Boolean echelon condition. -/
theorem isBooleanEchelon_none {n : ℕ} :
    IsBooleanEchelon (fun _ : Fin n => none) := by
  intro i row h
  simp at h

/-- The span of an empty pivot table is the trivial subgroup. -/
theorem booleanPivotSpan_none {n : ℕ} :
    booleanPivotSpan (fun _ : Fin n => none) = ⊥ := by
  unfold booleanPivotSpan
  rw [show {v : BooleanVec n | ∃ i row, (fun _ : Fin n => none) i = some row ∧
      v = regBooleanEquiv n row} = ∅ by
    ext v
    simp]
  exact AddSubgroup.closure_empty

/-- Inserting a row into an echelon pivot table preserves the echelon condition. -/
theorem booleanInsertRow_echelon {n : ℕ} (acc : BooleanEchelonResult n) (x : Reg n)
    (hech : IsBooleanEchelon acc.pivots) :
    IsBooleanEchelon (booleanInsertRow acc x).pivots := by
  unfold booleanInsertRow
  obtain ⟨hspan, hbits, -, -⟩ := booleanReduceFull_invariant acc.pivots x hech
  obtain ⟨hsome, hnone, -⟩ := booleanFindFirstTrue_sound (booleanReduceFull acc.pivots x).row
  split
  · exact hech
  · rename_i i hi
    obtain ⟨hlead, hlow⟩ := hsome i hi
    have hnone_i : acc.pivots i = none := by
      cases hp : acc.pivots i with
      | none => rfl
      | some row =>
        have := hbits i row hp
        rw [hlead] at this
        simp at this
    intro j row hj
    simp only [Function.update_apply] at hj
    by_cases hji : j = i
    · subst hji
      rw [if_pos rfl] at hj
      cases hj
      exact ⟨hlead, fun l hl => hlow l hl⟩
    · rw [if_neg hji] at hj
      exact hech j row hj

/-- Inserting a row into an echelon pivot table adds exactly that row's span to the pivot span. -/
theorem booleanInsertRow_span {n : ℕ} (acc : BooleanEchelonResult n) (x : Reg n)
    (hech : IsBooleanEchelon acc.pivots) :
    booleanPivotSpan (booleanInsertRow acc x).pivots =
      booleanPivotSpan acc.pivots ⊔ booleanRowsSpan [x] := by
  obtain ⟨hspan, hbits, -, -⟩ := booleanReduceFull_invariant acc.pivots x hech
  obtain ⟨hsome, hnone, -⟩ := booleanFindFirstTrue_sound (booleanReduceFull acc.pivots x).row
  have hrowsSpan : booleanRowsSpan [x] = AddSubgroup.closure {regBooleanEquiv n x} := by
    unfold booleanRowsSpan
    congr 1
    ext v
    simp
  unfold booleanInsertRow
  split
  · rename_i hfind
    have hzero : (booleanReduceFull acc.pivots x).row = ZeroStr n := funext (hnone hfind)
    have hx_mem : regBooleanEquiv n x ∈ booleanPivotSpan acc.pivots := by
      have h0 : regBooleanEquiv n (booleanReduceFull acc.pivots x).row = 0 := by
        rw [hzero]
        simp
      have hneg : -regBooleanEquiv n x ∈ booleanPivotSpan acc.pivots := by
        rwa [h0, zero_sub] at hspan
      have hnn := neg_mem hneg
      rwa [neg_neg] at hnn
    have hle : booleanRowsSpan [x] ≤ booleanPivotSpan acc.pivots := by
      rw [hrowsSpan, AddSubgroup.closure_le]
      intro v hv
      simp only [Set.mem_singleton_iff] at hv
      subst hv
      exact hx_mem
    show booleanPivotSpan acc.pivots = booleanPivotSpan acc.pivots ⊔ booleanRowsSpan [x]
    rw [sup_comm, sup_of_le_right hle]
  · rename_i i hfind
    obtain ⟨hlead, -⟩ := hsome i hfind
    have hnone_i : acc.pivots i = none := by
      cases hp : acc.pivots i with
      | none => rfl
      | some row =>
        have hbit := hbits i row hp
        rw [hlead] at hbit
        simp at hbit
    have hgen : {v : BooleanVec n | ∃ j row,
        Function.update acc.pivots i (some (booleanReduceFull acc.pivots x).row) j =
          some row ∧ v = regBooleanEquiv n row} =
        {v | ∃ j row, acc.pivots j = some row ∧ v = regBooleanEquiv n row} ∪
          {regBooleanEquiv n (booleanReduceFull acc.pivots x).row} := by
      ext v
      constructor
      · rintro ⟨j, row, hj, rfl⟩
        by_cases hji : j = i
        · subst hji
          rw [Function.update_self] at hj
          cases hj
          exact Or.inr rfl
        · rw [Function.update_of_ne hji] at hj
          exact Or.inl ⟨j, row, hj, rfl⟩
      · rintro (⟨j, row, hj, rfl⟩ | rfl)
        · refine ⟨j, row, ?_, rfl⟩
          rw [Function.update_of_ne (fun hji => by
            subst hji
            rw [hnone_i] at hj
            simp at hj)]
          exact hj
        · exact ⟨i, _, Function.update_self .., rfl⟩
    show booleanPivotSpan
        (Function.update acc.pivots i (some (booleanReduceFull acc.pivots x).row)) =
      booleanPivotSpan acc.pivots ⊔ booleanRowsSpan [x]
    unfold booleanPivotSpan
    rw [hgen, AddSubgroup.closure_union, hrowsSpan]
    apply le_antisymm
    · apply sup_le le_sup_left
      rw [AddSubgroup.closure_le]
      intro v hv
      simp only [Set.mem_singleton_iff] at hv
      subst hv
      rw [show regBooleanEquiv n (booleanReduceFull acc.pivots x).row =
          regBooleanEquiv n x +
            (regBooleanEquiv n (booleanReduceFull acc.pivots x).row -
              regBooleanEquiv n x) by abel]
      exact AddSubgroup.mem_sup.mpr ⟨_, hspan, _,
        AddSubgroup.subset_closure (Set.mem_singleton _), by abel⟩
    · apply sup_le le_sup_left
      rw [AddSubgroup.closure_le]
      intro v hv
      simp only [Set.mem_singleton_iff] at hv
      subst hv
      rw [show regBooleanEquiv n x =
          regBooleanEquiv n (booleanReduceFull acc.pivots x).row -
            (regBooleanEquiv n (booleanReduceFull acc.pivots x).row -
              regBooleanEquiv n x) by abel]
      exact AddSubgroup.mem_sup.mpr ⟨_, neg_mem hspan, _,
        AddSubgroup.subset_closure (Set.mem_singleton _), by abel⟩

/-- The span of a list with a prepended row is the join of that row's span and the tail span. -/
theorem booleanRowsSpan_cons {n : ℕ} (x : Reg n) (xs : List (Reg n)) :
    booleanRowsSpan (x :: xs) = booleanRowsSpan [x] ⊔ booleanRowsSpan xs := by
  have hgen : {v : BooleanVec n | ∃ r, r ∈ x :: xs ∧ v = regBooleanEquiv n r} =
      {v | ∃ r, r ∈ [x] ∧ v = regBooleanEquiv n r} ∪
        {v | ∃ r, r ∈ xs ∧ v = regBooleanEquiv n r} := by
    ext v
    simp [List.mem_cons]
  unfold booleanRowsSpan
  rw [hgen, AddSubgroup.closure_union]

/-- The span of an empty row list is the trivial subgroup. -/
theorem booleanRowsSpan_nil {n : ℕ} : booleanRowsSpan ([] : List (Reg n)) = ⊥ := by
  unfold booleanRowsSpan
  rw [show {v : BooleanVec n | ∃ r, r ∈ ([] : List (Reg n)) ∧
      v = regBooleanEquiv n r} = ∅ by
    ext v
    simp]
  exact AddSubgroup.closure_empty

/-- Repeated insertion preserves echelon form, joins the initial and input row spans, and
increases the counters by at most the stated bounds. -/
theorem booleanEchelonContinue_invariant {n : ℕ} :
    ∀ (rows : List (Reg n)) (init : BooleanEchelonResult n),
      IsBooleanEchelon init.pivots →
      IsBooleanEchelon (rows.foldl booleanInsertRow init).pivots ∧
      booleanPivotSpan (rows.foldl booleanInsertRow init).pivots =
        booleanPivotSpan init.pivots ⊔ booleanRowsSpan rows ∧
      (rows.foldl booleanInsertRow init).xorCount ≤ init.xorCount + rows.length * n ∧
      (rows.foldl booleanInsertRow init).bitOps ≤
        init.bitOps + rows.length * (4 * n ^ 2 + 4 * n) := by
  intro rows
  induction rows with
  | nil =>
    intro init hech
    refine ⟨hech, ?_, Nat.le_add_right _ _, Nat.le_add_right _ _⟩
    simp [booleanRowsSpan_nil]
  | cons x xs ih =>
    intro init hech
    have hstep_xc : (booleanInsertRow init x).xorCount ≤ init.xorCount + n := by
      unfold booleanInsertRow
      split <;>
        exact Nat.add_le_add_left
          (booleanReduceFull_invariant init.pivots x hech).2.2.1 _
    have hstep_bo : (booleanInsertRow init x).bitOps ≤
        init.bitOps + (4 * n ^ 2 + 4 * n) := by
      obtain ⟨-, -, -, hbo⟩ := booleanReduceFull_invariant init.pivots x hech
      obtain ⟨-, -, hfind⟩ := booleanFindFirstTrue_sound (booleanReduceFull init.pivots x).row
      unfold booleanInsertRow
      split
      · show init.bitOps + (booleanReduceFull init.pivots x).bitOps +
            (booleanFindFirstTrue (booleanReduceFull init.pivots x).row).2 ≤
          init.bitOps + (4 * n ^ 2 + 4 * n)
        rw [hfind]
        have h1 : n * (2 + 4 * n) = 4 * n ^ 2 + 2 * n := by ring
        omega
      · show init.bitOps + (booleanReduceFull init.pivots x).bitOps +
            (booleanFindFirstTrue (booleanReduceFull init.pivots x).row).2 + n ≤
          init.bitOps + (4 * n ^ 2 + 4 * n)
        rw [hfind]
        have h1 : n * (2 + 4 * n) = 4 * n ^ 2 + 2 * n := by ring
        omega
    simp only [List.foldl_cons, List.length_cons]
    obtain ⟨ihech, ihspan, ihxc, ihbo⟩ :=
      ih (booleanInsertRow init x) (booleanInsertRow_echelon init x hech)
    refine ⟨ihech, ?_, ?_, ?_⟩
    · calc booleanPivotSpan
            (List.foldl booleanInsertRow (booleanInsertRow init x) xs).pivots
          = booleanPivotSpan (booleanInsertRow init x).pivots ⊔ booleanRowsSpan xs :=
          ihspan
        _ = (booleanPivotSpan init.pivots ⊔ booleanRowsSpan [x]) ⊔ booleanRowsSpan xs := by
          rw [booleanInsertRow_span init x hech]
        _ = booleanPivotSpan init.pivots ⊔ (booleanRowsSpan [x] ⊔ booleanRowsSpan xs) :=
          sup_assoc _ _ _
        _ = booleanPivotSpan init.pivots ⊔ booleanRowsSpan (x :: xs) := by
          rw [← booleanRowsSpan_cons]
    · calc (List.foldl booleanInsertRow (booleanInsertRow init x) xs).xorCount
          ≤ (booleanInsertRow init x).xorCount + xs.length * n := ihxc
        _ ≤ init.xorCount + n + xs.length * n := Nat.add_le_add_right hstep_xc _
        _ = init.xorCount + (x :: xs).length * n := by
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          ring
    · calc (List.foldl booleanInsertRow (booleanInsertRow init x) xs).bitOps
          ≤ (booleanInsertRow init x).bitOps + xs.length * (4 * n ^ 2 + 4 * n) := ihbo
        _ ≤ init.bitOps + (4 * n ^ 2 + 4 * n) + xs.length * (4 * n ^ 2 + 4 * n) :=
          Nat.add_le_add_right hstep_bo _
        _ = init.bitOps + (x :: xs).length * (4 * n ^ 2 + 4 * n) := by
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          ring

/-- Boolean elimination returns an echelon table spanning the input rows and uses at most
`rows.length * n` XOR operations. -/
theorem boolean_gaussian_actual_echelon {n : ℕ} (rows : List (Reg n)) :
    IsBooleanEchelon (booleanEchelonRun rows).pivots ∧
    booleanPivotSpan (booleanEchelonRun rows).pivots = booleanRowsSpan rows ∧
    (booleanEchelonRun rows).xorCount ≤ rows.length * n := by
  unfold booleanEchelonRun booleanEchelonContinue
  obtain ⟨hech, hspan, hxc, -⟩ := booleanEchelonContinue_invariant rows
    ⟨fun _ => none, 0, 0⟩ isBooleanEchelon_none
  refine ⟨hech, ?_, ?_⟩
  · rw [hspan]
    show booleanPivotSpan (fun _ : Fin n => none) ⊔ booleanRowsSpan rows =
      booleanRowsSpan rows
    rw [booleanPivotSpan_none, bot_sup_eq]
  · show (List.foldl booleanInsertRow ⟨fun _ => none, 0, 0⟩ rows).xorCount ≤
      rows.length * n
    simpa using hxc

/-- Elimination on concatenated rows has the same pivots as continuing from the first prefix,
and the concatenated row span is the join of the two spans. -/
theorem boolean_gaussian_span_and_prefix {n : ℕ} (xs ys : List (Reg n)) :
    (booleanEchelonRun (xs ++ ys)).pivots =
      (booleanEchelonContinue (booleanEchelonRun xs).pivots ys).pivots ∧
    booleanRowsSpan (xs ++ ys) = booleanRowsSpan xs ⊔ booleanRowsSpan ys := by
  constructor
  · have hinvariant : ∀ (zs : List (Reg n)) (a b : BooleanEchelonResult n),
        a.pivots = b.pivots →
        (zs.foldl booleanInsertRow a).pivots = (zs.foldl booleanInsertRow b).pivots := by
      intro zs
      induction zs with
      | nil => intro a b hab; simp [hab]
      | cons z zs ihz =>
        intro a b hab
        simp only [List.foldl_cons]
        apply ihz
        unfold booleanInsertRow
        rw [hab]
        split <;> rfl
    unfold booleanEchelonRun booleanEchelonContinue
    rw [List.foldl_append]
    exact hinvariant ys _ _ rfl
  · have hgen : {v : BooleanVec n | ∃ r, r ∈ xs ++ ys ∧ v = regBooleanEquiv n r} =
        {v | ∃ r, r ∈ xs ∧ v = regBooleanEquiv n r} ∪
          {v | ∃ r, r ∈ ys ∧ v = regBooleanEquiv n r} := by
      ext v
      constructor
      · rintro ⟨r, hr, rfl⟩
        rw [List.mem_append] at hr
        rcases hr with hr | hr
        · exact Or.inl ⟨r, hr, rfl⟩
        · exact Or.inr ⟨r, hr, rfl⟩
      · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
        · exact ⟨r, List.mem_append_left _ hr, rfl⟩
        · exact ⟨r, List.mem_append_right _ hr, rfl⟩
    unfold booleanRowsSpan
    rw [hgen, AddSubgroup.closure_union]

/-- Encoding a conditional XOR fold gives the initial encoded bit plus the sum of encoded bits
at selected entries. -/
theorem boolZModEquiv_foldl_xor_ite {ι : Type*} (l : List ι) (p : ι → Prop)
    [DecidablePred p] (g : ι → Bool) (b : Bool) :
    boolZModEquiv (l.foldl (fun acc j => if p j then acc ^^ g j else acc) b) =
      boolZModEquiv b + (l.map (fun j => if p j then boolZModEquiv (g j) else 0)).sum := by
  induction l generalizing b with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    by_cases hj : p j
    · simp only [hj, if_true]
      rw [ih, boolZModEquiv_xor]
      ring
    · simp only [hj, if_false]
      rw [ih]
      simp

/-- Compute the parity of coordinatewise products strictly after column `i`, together with a
bit-operation counter. -/
def booleanTailParityFull {n : ℕ} (row x : Reg n) (i : Fin n) : Bool × ℕ :=
  (List.finRange n).foldl (fun acc j =>
    if i < j then (acc.1 ^^ (row j && x j), acc.2 + 5) else (acc.1, acc.2 + 1)) (false, 0)

/-- The parity component of `booleanTailParityFull`. -/
def booleanTailParity {n : ℕ} (row x : Reg n) (i : Fin n) : Bool :=
  (booleanTailParityFull row x i).1

/-- The parity component of the counted tail computation equals the corresponding conditional
XOR fold. -/
theorem booleanTailParityFull_fst {n : ℕ} (row x : Reg n) (i : Fin n) :
    (booleanTailParityFull row x i).1 =
      (List.finRange n).foldl (fun acc j =>
        if i < j then acc ^^ (row j && x j) else acc) false := by
  unfold booleanTailParityFull
  have hgen : ∀ (l : List (Fin n)) (b : Bool) (c : ℕ),
      (l.foldl (fun (acc : Bool × ℕ) j =>
          if i < j then (acc.1 ^^ (row j && x j), acc.2 + 5) else (acc.1, acc.2 + 1))
        (b, c)).1 =
      l.foldl (fun acc j => if i < j then acc ^^ (row j && x j) else acc) b := by
    intro l b c
    induction l generalizing b c with
    | nil => rfl
    | cons j l ih =>
      simp only [List.foldl_cons]
      by_cases hij : i < j
      · simp only [hij, if_true]
        exact ih _ _
      · simp only [hij, if_false]
        exact ih _ _
  exact hgen _ false 0

/-- Tail parity depends only on coordinates strictly after the pivot column. -/
theorem booleanTailParity_congr {n : ℕ} (row : Reg n) (i : Fin n) {x y : Reg n}
    (h : ∀ j, i < j → x j = y j) :
    booleanTailParity row x i = booleanTailParity row y i := by
  rw [booleanTailParity, booleanTailParityFull_fst, booleanTailParity,
    booleanTailParityFull_fst]
  have hgen : ∀ (l : List (Fin n)) (b : Bool),
      (l.foldl (fun acc j => if i < j then acc ^^ (row j && x j) else acc) b) =
      (l.foldl (fun acc j => if i < j then acc ^^ (row j && y j) else acc) b) := by
    intro l b
    induction l generalizing b with
    | nil => rfl
    | cons j l ih =>
      simp only [List.foldl_cons]
      by_cases hij : i < j
      · simp only [hij, if_true, h j hij]
        exact ih _
      · simp only [hij, if_false]
        exact ih _
  exact hgen _ false

/-- The tail parity bit-operation count is at most `5 * n`. -/
theorem booleanTailParityFull_snd_le {n : ℕ} (row x : Reg n) (i : Fin n) :
    (booleanTailParityFull row x i).2 ≤ 5 * n := by
  unfold booleanTailParityFull
  have hgen : ∀ (l : List (Fin n)) (acc : Bool × ℕ),
      (l.foldl (fun (acc : Bool × ℕ) j =>
          if i < j then (acc.1 ^^ (row j && x j), acc.2 + 5) else (acc.1, acc.2 + 1))
        acc).2 ≤ acc.2 + 5 * l.length := by
    intro l acc
    induction l generalizing acc with
    | nil => simp
    | cons j l ih =>
      simp only [List.foldl_cons, List.length_cons]
      split
      · have h1 := ih (acc.1 ^^ (row j && x j), acc.2 + 5)
        have h2 : ((acc.1 ^^ (row j && x j), acc.2 + 5) : Bool × ℕ).2 = acc.2 + 5 := rfl
        omega
      · have h1 := ih (acc.1, acc.2 + 1)
        have h2 : ((acc.1, acc.2 + 1) : Bool × ℕ).2 = acc.2 + 1 := rfl
        omega
  have h := hgen (List.finRange n) (false, 0)
  rw [List.length_finRange] at h
  have h0 : ((false, 0) : Bool × ℕ).2 = 0 := rfl
  rwa [h0, zero_add] at h

/-- Encoded tail parity equals the sum of encoded coordinate products strictly after the pivot
column. -/
theorem boolZModEquiv_booleanTailParity {n : ℕ} (row x : Reg n) (i : Fin n) :
    boolZModEquiv (booleanTailParity row x i) =
      ∑ j ∈ Finset.univ.filter (fun j => i < j),
        regBooleanEquiv n row j * regBooleanEquiv n x j := by
  rw [booleanTailParity, booleanTailParityFull_fst, boolZModEquiv_foldl_xor_ite]
  simp only [boolZModEquiv_false, zero_add]
  rw [listSum_finRange_map]
  simp only [boolZModEquiv_and_mul]
  rw [← Finset.sum_filter]
  exact Finset.sum_congr rfl (fun j _ => rfl)

/-- Set a free coordinate from the supplied free register or a pivot coordinate from its row's
tail parity, updating the operation count. -/
def booleanBackSubstituteStep {n : ℕ} (piv : Fin n → Option (Reg n)) (free : Reg n)
    (acc : Reg n × ℕ) (i : Fin n) : Reg n × ℕ :=
  match piv i with
  | none => (Function.update acc.1 i (free i), acc.2 + 2)
  | some row =>
    (Function.update acc.1 i (booleanTailParity row acc.1 i),
      acc.2 + 2 + (booleanTailParityFull row acc.1 i).2)

/-- Perform one back-substitution step at the reversed coordinate `Fin.rev k`. -/
def booleanBackSubstituteRevStep {n : ℕ} (piv : Fin n → Option (Reg n)) (free : Reg n)
    (acc : Reg n × ℕ) (k : Fin n) : Reg n × ℕ :=
  booleanBackSubstituteStep piv free acc (Fin.rev k)

/-- At an unoccupied pivot column, back substitution updates that coordinate with its supplied
free bit. -/
theorem booleanBackSubstituteStep_fst_none {n : ℕ} (piv : Fin n → Option (Reg n))
    (free : Reg n) (acc : Reg n × ℕ) {i : Fin n} (h : piv i = none) :
    (booleanBackSubstituteStep piv free acc i).1 = Function.update acc.1 i (free i) := by
  unfold booleanBackSubstituteStep
  rw [h]

/-- At an occupied pivot column, back substitution updates that coordinate with the pivot row's
tail parity. -/
theorem booleanBackSubstituteStep_fst_some {n : ℕ} (piv : Fin n → Option (Reg n))
    (free : Reg n) (acc : Reg n × ℕ) {i : Fin n} {row : Reg n} (h : piv i = some row) :
    (booleanBackSubstituteStep piv free acc i).1 =
      Function.update acc.1 i (booleanTailParity row acc.1 i) := by
  unfold booleanBackSubstituteStep
  rw [h]

/-- Perform counted back substitution in decreasing coordinate order, starting from the supplied
free register. -/
def booleanBackSubstituteFull {n : ℕ} (piv : Fin n → Option (Reg n)) (free : Reg n) :
    Reg n × ℕ :=
  ((List.finRange n).reverse).foldl (booleanBackSubstituteStep piv free) (free, 0)

/-- The register produced by the counted back-substitution procedure. -/
def booleanBackSubstitute {n : ℕ} (piv : Fin n → Option (Reg n)) (free : Reg n) :
    Reg n :=
  (booleanBackSubstituteFull piv free).1

/-- The back-substituted register equals the free bit at an unoccupied column and the final tail
parity at an occupied column. -/
theorem booleanBackSubstitute_apply {n : ℕ} (piv : Fin n → Option (Reg n)) (free : Reg n)
    (i : Fin n) :
    booleanBackSubstitute piv free i =
      match piv i with
      | none => free i
      | some row => booleanTailParity row (booleanBackSubstitute piv free) i := by
  unfold booleanBackSubstitute booleanBackSubstituteFull
  rw [List.finRange_reverse, List.foldl_map]
  have hstep_eq : (fun (acc : Reg n × ℕ) (k : Fin n) =>
      booleanBackSubstituteStep piv free acc (Fin.rev k)) =
      booleanBackSubstituteRevStep piv free := rfl
  rw [hstep_eq]
  have h := foldl_finRange_induction
    (booleanBackSubstituteRevStep piv free)
    (free, 0)
    (fun k acc => ∀ j : Fin n, n - k ≤ j.val →
      acc.1 j = match piv j with
        | none => free j
        | some row => booleanTailParity row acc.1 j)
    (by intro j hj; omega)
    (by
      intro k hk acc hacc
      unfold booleanBackSubstituteRevStep
      set i₀ : Fin n := Fin.rev ⟨k, hk⟩ with hi₀
      have hi₀val : i₀.val = n - 1 - k := by
        rw [hi₀, Fin.val_rev]
        show n - (k + 1) = n - 1 - k
        omega
      intro j hj
      by_cases hjj : n - k ≤ j.val
      · have hjne : j ≠ i₀ := by
          intro h
          subst h
          omega
        have hupd : ∀ v, Function.update acc.1 i₀ v j = acc.1 j :=
          fun v => Function.update_of_ne hjne v acc.1
        have hstepj : (booleanBackSubstituteStep piv free acc i₀).1 j = acc.1 j := by
          cases hp : piv i₀ with
          | none => rw [booleanBackSubstituteStep_fst_none piv free acc hp]; exact hupd _
          | some row => rw [booleanBackSubstituteStep_fst_some piv free acc hp]; exact hupd _
        rw [hstepj, hacc j hjj]
        cases hpj : piv j with
        | none => rfl
        | some row =>
          apply booleanTailParity_congr
          intro l hjl
          have hst2 : (booleanBackSubstituteStep piv free acc i₀).1 l = acc.1 l := by
            cases hp2 : piv i₀ with
            | none =>
              rw [booleanBackSubstituteStep_fst_none piv free acc hp2]
              exact Function.update_of_ne (show l ≠ i₀ from by
                intro h
                subst h
                omega) _ _
            | some row2 =>
              rw [booleanBackSubstituteStep_fst_some piv free acc hp2]
              exact Function.update_of_ne (show l ≠ i₀ from by
                intro h
                subst h
                omega) _ _
          exact hst2.symm
      · have hji : j = i₀ := Fin.ext (by omega)
        subst hji
        cases hp : piv i₀ with
        | none =>
          rw [booleanBackSubstituteStep_fst_none piv free acc hp]
          exact Function.update_self ..
        | some row =>
          rw [booleanBackSubstituteStep_fst_some piv free acc hp]
          rw [Function.update_self]
          show booleanTailParity row acc.1 i₀ =
            booleanTailParity row
              (Function.update acc.1 i₀ (booleanTailParity row acc.1 i₀)) i₀
          apply booleanTailParity_congr
          intro l hjl
          exact (Function.update_of_ne (show l ≠ i₀ from by
            intro h
            subst h
            omega) _ _).symm)
  exact h i (Nat.sub_self n ▸ Nat.zero_le _)

/-- Split a sum over `Fin n` into indices before `i`, the term at `i`, and indices after `i`. -/
theorem finSum_split_three {n : ℕ} (i : Fin n) (g : Fin n → ZMod 2) :
    ∑ j, g j = (∑ j ∈ Finset.univ.filter (· < i), g j) + g i +
      (∑ j ∈ Finset.univ.filter (i < ·), g j) := by
  have hle : Finset.univ.filter (fun j : Fin n => j ≤ i) =
      Finset.univ.filter (· < i) ∪ {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact le_of_lt h
      · exact le_of_eq h
  have hdisj : Disjoint (Finset.univ.filter (· < i)) ({i} : Finset (Fin n)) := by
    simp [Finset.disjoint_singleton_right]
  have hmain : ∑ j : Fin n, g j =
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ i), g j) +
        (∑ j ∈ Finset.univ.filter (fun j => i < j), g j) := by
    have hnot : Finset.univ.filter (fun j : Fin n => ¬ j ≤ i) =
        Finset.univ.filter (fun j => i < j) := by
      ext j
      simp [not_le]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ≤ i) g, hnot]
  rw [hmain, hle, Finset.sum_union hdisj, Finset.sum_singleton, add_assoc]

/-- For an echelon pivot table, back substitution produces a vector orthogonal to every pivot
row and preserves all supplied free coordinates. -/
theorem boolean_gaussian_back_substitution {n : ℕ} (piv : Fin n → Option (Reg n))
    (free : Reg n) :
    IsBooleanEchelon piv →
    (∀ i row, piv i = some row → booleanDot (regBooleanEquiv n row)
      (regBooleanEquiv n (booleanBackSubstitute piv free)) = 0) ∧
    (∀ i, piv i = none → booleanBackSubstitute piv free i = free i) := by
  intro hech
  constructor
  · intro i row hrow
    obtain ⟨hlead, hlow⟩ := hech i row hrow
    have hsplit := finSum_split_three i
      (fun j => regBooleanEquiv n row j * regBooleanEquiv n (booleanBackSubstitute piv free) j)
    have hlow0 : (∑ j ∈ Finset.univ.filter (· < i),
        regBooleanEquiv n row j * regBooleanEquiv n (booleanBackSubstitute piv free) j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_filter] at hj
      have hjf := hlow j hj.2
      simp [regBooleanEquiv_apply, hjf]
    have hlead1 : regBooleanEquiv n row i = 1 := by simp [regBooleanEquiv_apply, hlead]
    have hbsi : regBooleanEquiv n (booleanBackSubstitute piv free) i =
        boolZModEquiv (booleanTailParity row (booleanBackSubstitute piv free) i) := by
      rw [regBooleanEquiv_apply, booleanBackSubstitute_apply, hrow]
    unfold booleanDot
    rw [hsplit, hlow0, zero_add, hlead1, one_mul, hbsi, ← boolZModEquiv_booleanTailParity,
      ← boolZModEquiv_xor, Bool.xor_self, boolZModEquiv_false]
  · intro i hi
    rw [booleanBackSubstitute_apply, hi]

/-- The list of coordinates with no pivot row, in increasing order. -/
def booleanFreeColumns {n : ℕ} (piv : Fin n → Option (Reg n)) : List (Fin n) :=
  (List.finRange n).filter (fun i => (piv i).isNone)

/-- A coordinate is listed as free exactly when its pivot entry is `none`. -/
theorem mem_booleanFreeColumns {n : ℕ} {piv : Fin n → Option (Reg n)} {j : Fin n} :
    j ∈ booleanFreeColumns piv ↔ piv j = none := by
  simp [booleanFreeColumns, Option.isNone_iff_eq_none]

/-- The list of free columns has no duplicates. -/
theorem nodup_booleanFreeColumns {n : ℕ} (piv : Fin n → Option (Reg n)) :
    (booleanFreeColumns piv).Nodup :=
  List.Nodup.filter _ (List.nodup_finRange n)

/-- The number of free columns is at most `n`. -/
theorem length_booleanFreeColumns_le {n : ℕ} (piv : Fin n → Option (Reg n)) :
    (booleanFreeColumns piv).length ≤ n :=
  (List.length_filter_le _ _).trans_eq List.length_finRange

/-- A fold that appends one computed element at each step produces the initial list followed by
the mapped input list. -/
theorem foldl_append_singleton_fst {α β : Type*} (l : List β) (g : β → α) (c : β → ℕ) :
    ∀ (acc : List α) (z : ℕ),
      (l.foldl (fun (a : List α × ℕ) j => (a.1 ++ [g j], a.2 + c j)) (acc, z)).1 =
        acc ++ l.map g := by
  induction l with
  | nil => intro acc z; simp
  | cons j l ih =>
    intro acc z
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp [List.append_assoc]

/-- If each step adds at most `B` to the counter, the final counter is at most its initial value
plus the list length times `B`. -/
theorem foldl_append_singleton_snd {α β : Type*} (l : List β) (g : β → α) (c : β → ℕ)
    (B : ℕ) :
    ∀ (_hc : ∀ j ∈ l, c j ≤ B) (acc : List α) (z : ℕ),
      (l.foldl (fun (a : List α × ℕ) j => (a.1 ++ [g j], a.2 + c j)) (acc, z)).2 ≤
        z + l.length * B := by
  induction l with
  | nil => intro _ acc z; simp
  | cons j l ih =>
    intro hc acc z
    simp only [List.foldl_cons, List.length_cons]
    have h2 : c j ≤ B := hc j (by simp)
    have h4 := ih (fun j' hj' => hc j' (List.mem_cons_of_mem _ hj')) (acc ++ [g j])
      (z + c j)
    have h5 : (l.length + 1) * B = l.length * B + B := Nat.succ_mul _ _
    omega

/-- Back-substitute a unit free assignment for every free column, collecting the resulting
registers and their operation counts. -/
def booleanKernelBasisFull {n : ℕ} (piv : Fin n → Option (Reg n)) : List (Reg n) × ℕ :=
  (booleanFreeColumns piv).foldl (fun acc j =>
    (acc.1 ++ [(booleanBackSubstituteFull piv (fun i => decide (i = j))).1],
      acc.2 + (booleanBackSubstituteFull piv (fun i => decide (i = j))).2))
    ([], n)

/-- The list component of `booleanKernelBasisFull`. -/
def booleanKernelBasis {n : ℕ} (piv : Fin n → Option (Reg n)) : List (Reg n) :=
  (booleanKernelBasisFull piv).1

/-- The constructed kernel list is the map of unit free assignments through back substitution. -/
theorem booleanKernelBasis_eq_map {n : ℕ} (piv : Fin n → Option (Reg n)) :
    booleanKernelBasis piv =
      (booleanFreeColumns piv).map (fun j =>
        booleanBackSubstitute piv (fun i => decide (i = j))) := by
  unfold booleanKernelBasis booleanKernelBasisFull
  rw [foldl_append_singleton_fst]
  simp [booleanBackSubstitute]

/-- The counted back-substitution cost is at most `n * (2 + 5 * n)`. -/
theorem booleanBackSubstituteFull_snd_le {n : ℕ} (piv : Fin n → Option (Reg n))
    (free : Reg n) :
    (booleanBackSubstituteFull piv free).2 ≤ n * (2 + 5 * n) := by
  unfold booleanBackSubstituteFull
  have hgen : ∀ (l : List (Fin n)) (acc : Reg n × ℕ),
      (l.foldl (booleanBackSubstituteStep piv free) acc).2 ≤
        acc.2 + l.length * (2 + 5 * n) := by
    intro l acc
    induction l generalizing acc with
    | nil => simp
    | cons j l ih =>
      simp only [List.foldl_cons, List.length_cons]
      have hstep : (booleanBackSubstituteStep piv free acc j).2 ≤ acc.2 + (2 + 5 * n) := by
        unfold booleanBackSubstituteStep
        split
        · show acc.2 + 2 ≤ acc.2 + (2 + 5 * n)
          omega
        · rename_i row hrow
          show acc.2 + 2 + (booleanTailParityFull row acc.1 j).2 ≤ acc.2 + (2 + 5 * n)
          have := booleanTailParityFull_snd_le row acc.1 j
          omega
      have h1 := ih (booleanBackSubstituteStep piv free acc j)
      have h5 : (l.length + 1) * (2 + 5 * n) = l.length * (2 + 5 * n) + (2 + 5 * n) :=
        Nat.succ_mul _ _
      omega
  have h := hgen (List.finRange n).reverse (free, 0)
  rw [List.length_reverse, List.length_finRange] at h
  simpa using h

/-- The counted kernel-list construction cost is at most `n + n * (n * (2 + 5 * n))`. -/
theorem booleanKernelBasisFull_snd_le {n : ℕ} (piv : Fin n → Option (Reg n)) :
    (booleanKernelBasisFull piv).2 ≤
      n + n * (n * (2 + 5 * n)) := by
  unfold booleanKernelBasisFull
  have hle := length_booleanFreeColumns_le piv
  have hbound : ∀ j ∈ booleanFreeColumns piv,
      (booleanBackSubstituteFull piv (fun i => decide (i = j))).2 ≤ n * (2 + 5 * n) :=
    fun j _ => booleanBackSubstituteFull_snd_le piv _
  have h := foldl_append_singleton_snd (booleanFreeColumns piv)
    (fun j => (booleanBackSubstituteFull piv (fun i => decide (i = j))).1)
    (fun j => (booleanBackSubstituteFull piv (fun i => decide (i = j))).2)
    (n * (2 + 5 * n)) hbound [] n
  calc (booleanKernelBasisFull piv).2
      ≤ n +
          (booleanFreeColumns piv).length * (n * (2 + 5 * n)) := h
    _ ≤ n + n * (n * (2 + 5 * n)) :=
      Nat.add_le_add_left (Nat.mul_le_mul hle le_rfl) n

/-- The free-column list length equals the cardinality of the set of unoccupied pivot columns. -/
theorem length_booleanFreeColumns {n : ℕ} (piv : Fin n → Option (Reg n)) :
    (booleanFreeColumns piv).length =
      (Finset.univ.filter (fun i => piv i = none)).card := by
  have htoFinset : (booleanFreeColumns piv).toFinset =
      Finset.univ.filter (fun i => piv i = none) := by
    ext i
    simp [booleanFreeColumns, Option.isNone_iff_eq_none]
  have hcard := List.toFinset_card_of_nodup (nodup_booleanFreeColumns piv)
  rw [htoFinset] at hcard
  exact hcard.symm

/-- Back substitution of the unit assignment at `j` has bit `decide (i = j)` at every free
column `i`. -/
theorem booleanBackSubstitute_apply_free {n : ℕ} (piv : Fin n → Option (Reg n))
    (j i : Fin n) (hi : piv i = none) :
    booleanBackSubstitute piv (fun l => decide (l = j)) i = decide (i = j) := by
  rw [booleanBackSubstitute_apply, hi]

/-- Equal lists have equal entries at the same valid index, independently of the chosen bound
proofs. -/
theorem list_getElem_eq_of_eq {α : Type*} {l₁ l₂ : List α} (h : l₁ = l₂) (i : ℕ)
    (h₁ : i < l₁.length) (h₂ : i < l₂.length) : l₁[i]'h₁ = l₂[i]'h₂ := by
  subst h
  rfl

/-- The encoded kernel-list vectors restrict to the identity matrix on the ordered free columns. -/
theorem booleanKernelBasis_eval_free {n : ℕ} {piv : Fin n → Option (Reg n)}
    (i : ℕ) (hi : i < (booleanKernelBasis piv).length)
    (j : ℕ) (hj : j < (booleanFreeColumns piv).length) :
    regBooleanEquiv n ((booleanKernelBasis piv)[i]'hi) ((booleanFreeColumns piv)[j]'hj) =
      if j = i then (1 : ZMod 2) else 0 := by
  have hlen : (booleanKernelBasis piv).length = (booleanFreeColumns piv).length := by
    rw [booleanKernelBasis_eq_map, List.length_map]
  have hifree : i < (booleanFreeColumns piv).length := hlen ▸ hi
  have himap : i < ((booleanFreeColumns piv).map (fun k =>
      booleanBackSubstitute piv (fun l => decide (l = k)))).length := by
    rw [List.length_map]
    exact hifree
  rw [congrArg (fun v => regBooleanEquiv n v ((booleanFreeColumns piv)[j]'hj))
    (list_getElem_eq_of_eq (booleanKernelBasis_eq_map piv) i hi himap)]
  simp only [List.getElem_map, regBooleanEquiv_apply]
  have hjmem : ((booleanFreeColumns piv)[j]'hj) ∈ booleanFreeColumns piv :=
    List.getElem_mem _
  have hjnone : piv ((booleanFreeColumns piv)[j]'hj) = none :=
    mem_booleanFreeColumns.mp hjmem
  rw [booleanBackSubstitute_apply piv
    (fun l => decide (l = (booleanFreeColumns piv)[i])), hjnone]
  show boolZModEquiv (decide ((booleanFreeColumns piv)[j] =
      (booleanFreeColumns piv)[i])) = if j = i then (1 : ZMod 2) else 0
  by_cases hji : j = i
  · subst hji
    simp
  · have hne : ((booleanFreeColumns piv)[j]'hj) ≠ ((booleanFreeColumns piv)[i]'hifree) := by
      intro h
      exact hji ((nodup_booleanFreeColumns piv).getElem_inj_iff.mp h)
    have h0 : decide (((booleanFreeColumns piv)[j]'hj) =
        ((booleanFreeColumns piv)[i]'hifree)) = false :=
      decide_eq_false_iff_not.mpr hne
    rw [h0, if_neg hji]
    exact boolZModEquiv_false

/-- The constructed kernel list has no repeated registers. -/
theorem booleanKernelBasis_nodup {n : ℕ} (piv : Fin n → Option (Reg n)) :
    (booleanKernelBasis piv).Nodup := by
  rw [booleanKernelBasis_eq_map]
  apply List.Nodup.map_on
  · intro j₁ hj₁ j₂ hj₂ h
    have h1 := mem_booleanFreeColumns.mp hj₁
    have hv := congrFun h j₁
    rw [booleanBackSubstitute_apply_free piv j₁ j₁ h1,
      booleanBackSubstitute_apply_free piv j₂ j₁ h1] at hv
    simp at hv
    exact hv
  · exact nodup_booleanFreeColumns piv

/-- The encoded vectors of the constructed kernel list are linearly independent over `ZMod 2`. -/
theorem booleanKernelBasis_linearIndependent {n : ℕ} (piv : Fin n → Option (Reg n)) :
    LinearIndependent (ZMod 2) (fun j : Fin (booleanKernelBasis piv).length =>
      regBooleanEquiv n ((booleanKernelBasis piv)[j])) := by
  rw [linearIndependent_iff']
  intro s f hf j hj
  have hlen : (booleanKernelBasis piv).length = (booleanFreeColumns piv).length := by
    rw [booleanKernelBasis_eq_map, List.length_map]
  have hjlt : j.val < (booleanFreeColumns piv).length := hlen ▸ j.isLt
  have h0 := congrFun hf ((booleanFreeColumns piv)[j.val]'hjlt)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
  have hterm : ∀ i ∈ s, f i *
      regBooleanEquiv n ((booleanKernelBasis piv)[i])
        ((booleanFreeColumns piv)[j.val]'hjlt) =
      f i * (if j = i then 1 else 0) := by
    intro i _
    show f i * regBooleanEquiv n ((booleanKernelBasis piv)[i.val]'i.isLt)
        ((booleanFreeColumns piv)[j.val]'hjlt) = f i * (if j = i then 1 else 0)
    rw [booleanKernelBasis_eval_free i.val i.isLt j.val hjlt]
    by_cases hji : j = i
    · rw [if_pos hji]
      subst hji
      simp
    · rw [if_neg hji, if_neg (by intro h; exact hji (Fin.ext h))]
  rw [Finset.sum_congr rfl hterm] at h0
  rw [Finset.sum_eq_single j (fun i _ hij => by
      rw [if_neg (fun h => hij h.symm), mul_zero]) (fun hn => absurd hj hn)] at h0
  simpa using h0

/-- Every element of `ZMod 2` is zero or one. -/
theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  have hv : c.val = 0 ∨ c.val = 1 := by
    have hlt := ZMod.val_lt c
    omega
  have hcast : ((c.val : ℕ) : ZMod 2) = c := ZMod.natCast_zmod_val c
  rcases hv with h0 | h1
  · left
    rw [← hcast, h0]
    simp
  · right
    rw [← hcast, h1]
    simp

/-- Adding an element of `ZMod 2` to itself gives zero. -/
theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_eq_zero_or_one a with h | h
  · rw [h, add_zero]
  · rw [h, ← Nat.cast_one, ← Nat.cast_add]
    exact ZMod.natCast_self 2

/-- Two elements of `ZMod 2` whose sum is zero are equal. -/
theorem zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  have hbb := zmod2_add_self b
  calc a = a + (b + b) := by rw [hbb]; simp
    _ = (a + b) + b := by rw [add_assoc]
    _ = 0 + b := by rw [h]
    _ = b := zero_add b

/-- For an echelon pivot table, the constructed kernel-list span is contained in the pivot
kernel. -/
theorem booleanRowsSpan_kernelBasis_le {n : ℕ} (piv : Fin n → Option (Reg n))
    (hech : IsBooleanEchelon piv) :
    booleanRowsSpan (booleanKernelBasis piv) ≤ booleanPivotKernel piv := by
  unfold booleanRowsSpan
  rw [AddSubgroup.closure_le]
  intro v hv
  rcases hv with ⟨r, hr, rfl⟩
  rw [booleanKernelBasis_eq_map] at hr
  rw [List.mem_map] at hr
  rcases hr with ⟨j, -, rfl⟩
  show regBooleanEquiv n (booleanBackSubstitute piv (fun i => decide (i = j))) ∈
    booleanPivotKernel piv
  rw [mem_booleanPivotKernel]
  intro i row hrow
  exact (boolean_gaussian_back_substitution piv _ hech).1 i row hrow

/-- For an echelon pivot table, every vector in the pivot kernel lies in the constructed
kernel-list span. -/
theorem booleanPivotKernel_le_span {n : ℕ} (piv : Fin n → Option (Reg n))
    (hech : IsBooleanEchelon piv) :
    booleanPivotKernel piv ≤ booleanRowsSpan (booleanKernelBasis piv) := by
  intro x hx
  rw [mem_booleanPivotKernel] at hx
  have hlen : (booleanKernelBasis piv).length = (booleanFreeColumns piv).length := by
    rw [booleanKernelBasis_eq_map, List.length_map]
  set L := (booleanFreeColumns piv).length with hL
  set y : BooleanVec n := ∑ t : Fin L, x ((booleanFreeColumns piv)[t.val]'t.isLt) •
    regBooleanEquiv n ((booleanKernelBasis piv)[t.val]'(by
      have := t.isLt; omega)) with hy_def
  have hy_span : y ∈ booleanRowsSpan (booleanKernelBasis piv) := by
    rw [hy_def]
    apply sum_mem
    intro t _
    cases zmod2_eq_zero_or_one (x ((booleanFreeColumns piv)[t.val]'t.isLt)) with
    | inl hc =>
      rw [hc, zero_smul]
      exact zero_mem _
    | inr hc =>
      rw [hc, one_smul]
      exact mem_booleanRowsSpan_of_mem (List.getElem_mem _)
  have hy_eq_x : y = x := by
    have hstep : ∀ k : ℕ, ∀ i : Fin n, n - k ≤ i.val → x i = y i := by
      intro k
      induction k with
      | zero =>
        intro i hi
        omega
      | succ k ih =>
        intro i hi
        by_cases hi' : n - k ≤ i.val
        · exact ih i hi'
        · have hival : i.val = n - k - 1 := by omega
          cases hp : piv i with
          | none =>

            obtain ⟨t₀, ht₀lt, ht₀⟩ :=
              List.mem_iff_getElem.mp (mem_booleanFreeColumns.mpr hp)
            have hy_apply : y i =
                ∑ t : Fin L, x ((booleanFreeColumns piv)[t.val]'t.isLt) *
                  regBooleanEquiv n ((booleanKernelBasis piv)[t.val]'
                    (by have := t.isLt; omega)) i := by
              rw [hy_def, Finset.sum_apply]
              simp [Pi.smul_apply, smul_eq_mul]
            rw [hy_apply, ← ht₀]
            have hterm : ∀ t : Fin L, t ∈ (Finset.univ : Finset (Fin L)) →
                x ((booleanFreeColumns piv)[t.val]'t.isLt) *
                  regBooleanEquiv n ((booleanKernelBasis piv)[t.val]'
                    (by have := t.isLt; omega)) ((booleanFreeColumns piv)[t₀]'ht₀lt) =
                  x ((booleanFreeColumns piv)[t.val]'t.isLt) *
                    (if ⟨t₀, ht₀lt⟩ = t then (1 : ZMod 2) else 0) := by
              intro t _
              rw [booleanKernelBasis_eval_free t.val _ t₀ ht₀lt]
              by_cases htt : (⟨t₀, ht₀lt⟩ : Fin L) = t
              · rw [if_pos htt]
                subst htt
                simp
              · rw [if_neg htt, if_neg (by
                  intro h
                  exact htt (Fin.ext h))]
            rw [Finset.sum_congr rfl hterm]
            rw [Finset.sum_eq_single ⟨t₀, ht₀lt⟩]
            · simp
            · intro t _ htt
              rw [if_neg (fun h => htt h.symm), mul_zero]
            · simp
          | some row =>

            obtain ⟨hlead, hlow⟩ := hech i row hp
            have hxeq := hx i row hp
            have hyker : y ∈ booleanPivotKernel piv :=
              booleanRowsSpan_kernelBasis_le piv hech hy_span
            have hyeq := (mem_booleanPivotKernel piv y).mp hyker i row hp
            have hsolve : ∀ z : BooleanVec n,
                booleanDot (regBooleanEquiv n row) z = 0 →
                z i = ∑ j ∈ Finset.univ.filter (i < ·),
                  regBooleanEquiv n row j * z j := by
              intro z hz
              have hsplit := finSum_split_three i
                (fun j => regBooleanEquiv n row j * z j)
              unfold booleanDot at hz
              rw [hsplit] at hz
              have hlow0 : (∑ j ∈ Finset.univ.filter (· < i),
                  regBooleanEquiv n row j * z j) = 0 := by
                apply Finset.sum_eq_zero
                intro j hj
                rw [Finset.mem_filter] at hj
                have hjf := hlow j hj.2
                simp [regBooleanEquiv_apply, hjf]
              rw [hlow0, zero_add] at hz
              have hlead1 : regBooleanEquiv n row i = 1 := by
                simp [regBooleanEquiv_apply, hlead]
              rw [hlead1, one_mul] at hz
              exact zmod2_eq_of_add_eq_zero hz
            rw [hsolve x hxeq, hsolve y hyeq]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mem_filter] at hj
            have hj' : n - k ≤ j.val := by
              have hlt : i.val < j.val := hj.2
              omega
            rw [ih j hj']
    funext i
    exact (hstep n i (Nat.sub_self n ▸ Nat.zero_le i.val)).symm
  rw [← hy_eq_x]
  exact hy_span

/-- For an echelon pivot table, the constructed list has no duplicates, is linearly independent,
spans the pivot kernel, and has one entry per free column. -/
theorem boolean_gaussian_kernel_basis {n : ℕ} (piv : Fin n → Option (Reg n)) :
    IsBooleanEchelon piv →
    (booleanKernelBasis piv).Nodup ∧
    LinearIndependent (ZMod 2) (fun j : Fin (booleanKernelBasis piv).length =>
      regBooleanEquiv n ((booleanKernelBasis piv)[j])) ∧
    booleanRowsSpan (booleanKernelBasis piv) = booleanPivotKernel piv ∧
    (booleanKernelBasis piv).length = (Finset.univ.filter (fun i => piv i = none)).card := by
  intro hech
  refine ⟨booleanKernelBasis_nodup piv, booleanKernelBasis_linearIndependent piv, ?_,
    ?_⟩
  · exact le_antisymm (booleanRowsSpan_kernelBasis_le piv hech)
      (booleanPivotKernel_le_span piv hech)
  · rw [booleanKernelBasis_eq_map, List.length_map]
    exact length_booleanFreeColumns piv

/-- The pivot kernel obtained by eliminating a sample list equals the Boolean sample candidate
subgroup. -/
theorem boolean_gaussian_record_kernel {n m : ℕ} (samples : Fin m → Reg n) :
    booleanPivotKernel (booleanEchelonRun (List.ofFn samples)).pivots =
      booleanSampleCandidate (fun i => regBooleanEquiv n (samples i)) := by
  rw [booleanPivotKernel_eq_booleanOrthogonal_span,
    (boolean_gaussian_actual_echelon (List.ofFn samples)).2.1,
    booleanSampleCandidate_eq_booleanOrthogonal_span]
  congr 1
  unfold booleanRowsSpan booleanSampleSpan
  congr 1
  ext v
  constructor
  · rintro ⟨r, hr, rfl⟩
    rw [List.mem_ofFn] at hr
    rcases hr with ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨samples i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩

/-- The additive subgroup generated by one Boolean vector is its subgroup of integer multiples. -/
theorem addSubgroupClosure_singleton_eq_zmultiples {n : ℕ} (a : BooleanVec n) :
    AddSubgroup.closure {a} = AddSubgroup.zmultiples a := by
  ext x
  rw [AddSubgroup.mem_closure_singleton, AddSubgroup.mem_zmultiples_iff]

/-- For Boolean vectors, membership in the linear span over `ZMod 2` is equivalent to membership
in the additive subgroup closure. -/
theorem mem_span_iff_mem_closure_zmod2 {n : ℕ} (s : Set (BooleanVec n))
    (x : BooleanVec n) :
    x ∈ Submodule.span (ZMod 2) s ↔ x ∈ AddSubgroup.closure s := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact AddSubgroup.subset_closure hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul c y _ hy =>
      rcases zmod2_eq_zero_or_one c with hc | hc
      · rw [hc, zero_smul]
        exact zero_mem _
      · rw [hc, one_smul]
        exact hy
  · intro hx
    apply AddSubgroup.closure_induction (k := s)
      (p := fun y _ => y ∈ Submodule.span (ZMod 2) s) (x := x)
    · intro y hy
      exact Submodule.subset_span hy
    · exact zero_mem _
    · intro y z _ _ hy hz
      exact add_mem hy hz
    · intro y _ hy
      exact neg_mem hy
    · exact hx

/-- For an echelon pivot table, the pivot kernel has cardinality two to the length of its
constructed basis list. -/
theorem booleanPivotKernel_card_eq_two_pow {n : ℕ} (piv : Fin n → Option (Reg n))
    (hech : IsBooleanEchelon piv) :
    Fintype.card (booleanPivotKernel piv) = 2 ^ (booleanKernelBasis piv).length := by
  classical
  set L := (booleanKernelBasis piv).length with hL
  set vfun : Fin L → BooleanVec n := fun j =>
    regBooleanEquiv n ((booleanKernelBasis piv)[j]) with hvfun
  set M : Submodule (ZMod 2) (BooleanVec n) := Submodule.span (ZMod 2) (Set.range vfun)
    with hM
  have hli : LinearIndependent (ZMod 2) vfun := booleanKernelBasis_linearIndependent piv
  have hfinrank : Module.finrank (ZMod 2) M = L := by
    rw [hM, finrank_span_eq_card hli]
    exact Fintype.card_fin L
  have hgen : Set.range vfun =
      {v | ∃ r, r ∈ booleanKernelBasis piv ∧ v = regBooleanEquiv n r} := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨((booleanKernelBasis piv)[j]), List.getElem_mem _, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
      exact ⟨⟨i, hi⟩, rfl⟩
  have hspan : M = AddSubgroup.toZModSubmodule 2 (booleanPivotKernel piv) := by
    apply SetLike.ext
    intro x
    rw [hM, mem_span_iff_mem_closure_zmod2]
    rw [hgen]
    have hsp : AddSubgroup.closure {v | ∃ r, r ∈ booleanKernelBasis piv ∧
        v = regBooleanEquiv n r} = booleanRowsSpan (booleanKernelBasis piv) := rfl
    rw [hsp]
    have hkernel := (boolean_gaussian_kernel_basis piv hech).2.2.1
    rw [hkernel]
    exact Iff.rfl
  have hcardM : Fintype.card M = 2 ^ L := by
    rw [← hfinrank]
    exact (Module.card_eq_pow_finrank (K := ZMod 2) (V := M)).trans (by
      simp [ZMod.card])
  have hcardK : Fintype.card (booleanPivotKernel piv) = Fintype.card M := by
    rw [hspan]
    exact Fintype.card_congr (Equiv.refl _)
  rw [hcardK, hcardM]

/-- Return zero for an empty kernel basis, its sole vector for a singleton basis, or `none` for
a larger basis, together with the elimination and kernel-construction cost. -/
def decodeSimonWithCost {n m : ℕ} (samples : Fin m → Reg n) : Option (Reg n) × ℕ :=
  (match booleanKernelBasis (booleanEchelonRun (List.ofFn samples)).pivots with
   | [] => some (ZeroStr n)
   | [v] => some v
   | _ => none,
   (booleanEchelonRun (List.ofFn samples)).bitOps +
     (booleanKernelBasisFull (booleanEchelonRun (List.ofFn samples)).pivots).2)

/-- The optional secret returned by `decodeSimonWithCost`. -/
def decodeSimonSecret {n m : ℕ} (samples : Fin m → Reg n) : Option (Reg n) :=
  (decodeSimonWithCost samples).1

/-- The span of a singleton row list equals the additive subgroup generated by its encoded
vector. -/
theorem booleanRowsSpan_singleton {n : ℕ} (x : Reg n) :
    booleanRowsSpan [x] = AddSubgroup.closure {regBooleanEquiv n x} := by
  unfold booleanRowsSpan
  congr 1
  ext v
  simp

/-- The natural number `2 ^ L` exceeds two exactly when `L` is at least two. -/
theorem two_lt_two_pow_iff (L : ℕ) : 2 < 2 ^ L ↔ 2 ≤ L := by
  constructor
  · intro h
    by_contra hL
    have hL2 : L < 2 := Nat.lt_of_not_ge hL
    interval_cases L <;> simp at h
  · intro h
    calc 2 < 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) h

/-- The decoder returns `some s` exactly when the sample candidate equals the Simon subgroup
generated by the encoded `s` [Simon1997]. -/
theorem boolean_gaussian_simon_decode_iff {n m : ℕ} (samples : Fin m → Reg n)
    (s : Reg n) :
    decodeSimonSecret samples = some s ↔
      booleanSampleCandidate (fun i => regBooleanEquiv n (samples i)) =
        booleanSimonSubgroup (regBooleanEquiv n s) := by
  classical
  set piv := (booleanEchelonRun (List.ofFn samples)).pivots with hpiv
  have hech : IsBooleanEchelon piv := (boolean_gaussian_actual_echelon _).1
  have hspan := (boolean_gaussian_kernel_basis piv hech).2.2.1
  have hcard := booleanPivotKernel_card_eq_two_pow piv hech
  have hK : booleanPivotKernel piv =
      booleanSampleCandidate (fun i => regBooleanEquiv n (samples i)) :=
    boolean_gaussian_record_kernel samples
  constructor
  · intro hdecode
    unfold decodeSimonSecret decodeSimonWithCost at hdecode
    rw [← hpiv] at hdecode
    cases hb : booleanKernelBasis piv with
    | nil =>
      rw [hb] at hdecode

      have hs : s = ZeroStr n := (Option.some.inj hdecode).symm
      rw [hs, ← hK, ← hspan, hb, booleanRowsSpan_nil,
        regBooleanEquiv_zeroStr, booleanSimonSubgroup_zero]
    | cons v rest =>
      rw [hb] at hdecode
      cases rest with
      | nil =>
        have hs : s = v := (Option.some.inj hdecode).symm
        rw [hs, ← hK, ← hspan, hb, booleanRowsSpan_singleton,
          addSubgroupClosure_singleton_eq_zmultiples]
        rfl
      | cons v₂ rest' =>
        simp at hdecode
  · intro hcand
    by_cases hs0 : s = ZeroStr n
    · have hsreg : regBooleanEquiv n s = 0 := by rw [hs0]; simp
      have hcardK : Fintype.card (booleanPivotKernel piv) = 1 := by
        rw [hK, hcand, hsreg, booleanSimonSubgroup_zero]
        simp
      have hL : (booleanKernelBasis piv).length = 0 := by
        rw [hcard] at hcardK
        by_contra hne
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
        rw [hk, pow_succ] at hcardK
        have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
        omega
      have hb : booleanKernelBasis piv = [] := List.length_eq_zero_iff.mp hL
      unfold decodeSimonSecret decodeSimonWithCost
      rw [hb]
      rw [hs0]
    · have hsreg : regBooleanEquiv n s ≠ 0 := by
        intro h0
        exact hs0 (regBooleanEquiv_injective n (by rw [h0]; simp))
      have hcardK : Fintype.card (booleanPivotKernel piv) = 2 := by
        rw [hK, hcand]
        exact card_booleanSimonSubgroup_eq_two_of_ne_zero _ hsreg
      have hL : (booleanKernelBasis piv).length = 1 := by
        rw [hcard] at hcardK
        have h2 : 2 ^ (booleanKernelBasis piv).length = 2 ^ 1 := by
          rw [hcardK]
          norm_num
        exact Nat.pow_right_injective (by norm_num) h2
      obtain ⟨v, hb⟩ := List.length_eq_one_iff.mp hL

      have hvmem : regBooleanEquiv n v ∈ booleanPivotKernel piv := by
        rw [← hspan]
        exact mem_booleanRowsSpan_of_mem (by rw [hb]; simp)
      rw [hK, hcand] at hvmem
      rcases (mem_booleanSimonSubgroup_iff _ _).mp hvmem with h0 | hs
      · exfalso
        have hfc : (booleanFreeColumns piv).length = 1 := by
          rw [← hL, booleanKernelBasis_eq_map, List.length_map]
        obtain ⟨c, hfc'⟩ := List.length_eq_one_iff.mp hfc
        have hv_eq : v = booleanBackSubstitute piv (fun l => decide (l = c)) := by
          have hmap := booleanKernelBasis_eq_map piv
          rw [hb, hfc'] at hmap
          simp at hmap
          exact hmap
        have hcnone : piv c = none :=
          mem_booleanFreeColumns.mp (by rw [hfc']; simp)
        have hvc : v c = true := by
          rw [hv_eq, booleanBackSubstitute_apply_free piv c c hcnone]
          simp
        have hv0 : v = ZeroStr n :=
          regBooleanEquiv_injective n (by rw [h0]; simp)
        rw [hv0] at hvc
        simp [ZeroStr] at hvc
      · have hvs : v = s := regBooleanEquiv_injective n hs
        unfold decodeSimonSecret decodeSimonWithCost
        rw [hb]
        rw [hvs]

/-- The decoder returns `none` exactly when the sample candidate subgroup has cardinality
greater than two. -/
theorem boolean_gaussian_ambiguous_record {n m : ℕ} (samples : Fin m → Reg n) :
    decodeSimonSecret samples = none ↔
      2 < Fintype.card (booleanSampleCandidate (fun i => regBooleanEquiv n (samples i))) := by
  classical
  set piv := (booleanEchelonRun (List.ofFn samples)).pivots with hpiv
  have hech : IsBooleanEchelon piv := (boolean_gaussian_actual_echelon _).1
  have hcard := booleanPivotKernel_card_eq_two_pow piv hech
  have hK : booleanPivotKernel piv =
      booleanSampleCandidate (fun i => regBooleanEquiv n (samples i)) :=
    boolean_gaussian_record_kernel samples
  have hlen2 : decodeSimonSecret samples = none ↔
      2 ≤ (booleanKernelBasis piv).length := by
    unfold decodeSimonSecret decodeSimonWithCost
    rw [← hpiv]
    cases hb : booleanKernelBasis piv with
    | nil => simp
    | cons v rest =>
      cases rest with
      | nil => simp
      | cons v₂ rest' => simp [List.length_cons]
  rw [hlen2, ← hK, hcard, two_lt_two_pow_iff]

/-- The counted decoder returns `decodeSimonSecret`, its total cost is at most `10 * (m * n ^ 2
+ n ^ 3 + m * n + n ^ 2 + n + 1)`, and its elimination cost satisfies the displayed
quadratic bound. -/
theorem boolean_gaussian_actual_operation_bound {n m : ℕ} (samples : Fin m → Reg n) :
    (decodeSimonWithCost samples).1 = decodeSimonSecret samples ∧
    (decodeSimonWithCost samples).2 ≤ 10*(m*n^2+n^3+m*n+n^2+n+1) ∧
    (booleanEchelonRun (List.ofFn samples)).bitOps ≤ 10*(m*n^2+m*n+m) := by
  have hbitOps := (booleanEchelonContinue_invariant (List.ofFn samples)
    ⟨fun _ => none, 0, 0⟩ isBooleanEchelon_none).2.2.2
  rw [List.length_ofFn] at hbitOps
  have hbitOps' : (booleanEchelonRun (List.ofFn samples)).bitOps ≤
      m * (4 * n ^ 2 + 4 * n) := by
    have h0 : (⟨fun _ => none, 0, 0⟩ : BooleanEchelonResult n).bitOps = 0 := rfl
    unfold booleanEchelonRun booleanEchelonContinue
    rw [h0, zero_add] at hbitOps
    exact hbitOps
  have hback := booleanKernelBasisFull_snd_le (booleanEchelonRun (List.ofFn samples)).pivots
  refine ⟨rfl, ?_, ?_⟩
  · unfold decodeSimonWithCost
    calc (booleanEchelonRun (List.ofFn samples)).bitOps +
            (booleanKernelBasisFull (booleanEchelonRun (List.ofFn samples)).pivots).2
        ≤ m * (4 * n ^ 2 + 4 * n) + (n + n * (n * (2 + 5 * n))) :=
          Nat.add_le_add hbitOps' hback
      _ ≤ 10 * (m * n ^ 2 + n ^ 3 + m * n + n ^ 2 + n + 1) := by
        have e1 : m * (4 * n ^ 2 + 4 * n) + (n + n * (n * (2 + 5 * n))) =
            4 * (m * n ^ 2) + 5 * n ^ 3 + 4 * (m * n) + 2 * n ^ 2 + n + 0 := by ring
        have e2 : 10 * (m * n ^ 2 + n ^ 3 + m * n + n ^ 2 + n + 1) =
            10 * (m * n ^ 2) + 10 * n ^ 3 + 10 * (m * n) + 10 * n ^ 2 + 10 * n + 10 := by
          ring
        rw [e1, e2]
        exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add
            (Nat.mul_le_mul (by omega) le_rfl)
            (Nat.mul_le_mul (by omega) le_rfl))
          (Nat.mul_le_mul (by omega) le_rfl))
          (Nat.mul_le_mul (by omega) le_rfl))
          (by
            calc n = 1 * n := (one_mul n).symm
              _ ≤ 10 * n := Nat.mul_le_mul (by omega) le_rfl))
          (by omega)
  · calc (booleanEchelonRun (List.ofFn samples)).bitOps ≤ m * (4 * n ^ 2 + 4 * n) :=
        hbitOps'
      _ ≤ 10 * (m * n ^ 2 + m * n + m) := by
        have e1 : m * (4 * n ^ 2 + 4 * n) = 4 * (m * n ^ 2) + 4 * (m * n) + 0 := by ring
        have e2 : 10 * (m * n ^ 2 + m * n + m) = 10 * (m * n ^ 2) + 10 * (m * n) + 10 * m := by
          ring
        rw [e1, e2]
        exact Nat.add_le_add (Nat.add_le_add
          (Nat.mul_le_mul (by omega) le_rfl)
          (Nat.mul_le_mul (by omega) le_rfl)) (by omega)

end Qatlib.Concepts.HspRecovery.ReductionCore
