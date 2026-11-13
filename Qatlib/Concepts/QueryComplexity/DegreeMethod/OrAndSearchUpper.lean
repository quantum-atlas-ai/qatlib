/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
import Qatlib.Concepts.QueryComplexity.AdversarySearch.OrZeroErrorQueryLowerBoundBeal

/-!
# Exact and zero-error complexity of OR, AND, and search

This module constructs exact search programs by reading the input and returning its first marked
index, or reporting that no index is marked. The predicates `SearchExact` and `SearchZeroError`
also allow a separate inconclusive outcome.

The constructions attain the linear lower bounds for OR, AND, and search in the exact and
zero-error models of [BealsEtAl2001]. Complementing each query transfers the OR lower bound to
AND without changing the query count.

## Main statements

* `or_zeroErrorMinimum`: The zero-error query complexity of OR on `n` bits is `n`.
* `and_exactMinimum`: The exact query complexity of AND on `n` bits is `n`.
* `search_first_feasible`: First-marked search is realized with `n` queries and `3 * n` gates.
* `search_exactMinimum`: Exact search has minimum query count `n`.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1500000
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs.Coin
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.OrAndSearchUpper
open Matrix
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs

/-- Returns the least index at which the Boolean input is true, or `none` when every bit is
false. -/
def firstMarked : (n : ℕ) → (Fin n → Bool) → Option (Fin n)
  | 0,_ => none
  | n+1,x => if x 0 then some 0 else (firstMarked n (fun i => x i.succ)).map Fin.succ

/-- Specifies either that no input bit is true or that the returned index is the first true bit. -/
def FirstSpec {n : ℕ} (x : Fin n → Bool) : Option (Fin n) → Prop
  | none => ∀ i,x i=false
  | some j => x j=true ∧ ∀ i,i.val < j.val → x i=false

/-- The result of `firstMarked` satisfies the first-marked specification. -/
theorem firstMarked_spec (n : ℕ) (x : Fin n → Bool) : FirstSpec x (firstMarked n x) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    cases h0 : x 0 with
    | true =>
      simp only [firstMarked,h0,ite_true,FirstSpec]
      exact ⟨True.intro,by intro i hi; simp at hi⟩
    | false =>
      simp only [firstMarked,h0,Bool.false_eq_true,ite_false]
      have htail := ih (fun i => x i.succ)
      cases ht : firstMarked n (fun i => x i.succ) with
      | none =>
        simp only [Option.map_none,FirstSpec]
        simp only [ht,FirstSpec] at htail
        intro i
        refine Fin.cases h0 (fun j => htail j) i
      | some j =>
        simp only [Option.map_some,FirstSpec]
        simp only [ht,FirstSpec] at htail
        refine ⟨htail.1,?_⟩
        intro i hi
        refine Fin.cases (fun _ => h0) (fun k hk => htail.2 k ?_) i hi
        simpa only [Fin.val_succ,Nat.add_lt_add_iff_right] using! hk

/-- The first-marked search returns `none` exactly when every input bit is false. -/
theorem firstMarked_none {n : ℕ} (x : Fin n → Bool) :
    firstMarked n x=none ↔ ∀ i,x i=false := by
  constructor
  · intro h; simpa only [h,FirstSpec] using! firstMarked_spec n x
  · intro h
    cases he : firstMarked n x with
    | none => rfl
    | some j =>
      have ht : x j=true :=
          (show FirstSpec x (some j) by simpa only [he] using! firstMarked_spec n x).1
      simp [h j] at ht

/-- An index returned by `firstMarked` is marked, and all smaller indices are unmarked. -/
theorem firstMarked_some {n : ℕ} (x : Fin n → Bool) (j : Fin n)
    (h : firstMarked n x=some j) : x j=true ∧ ∀ i,i.val < j.val → x i=false := by
  simpa only [h,FirstSpec] using! firstMarked_spec n x

open scoped Classical
noncomputable section

/-- The Boolean OR of all input bits. -/
def orValue {n : ℕ} (x : Fin n → Bool) : Bool := decide (∃ i,x i=true)
/-- The Boolean AND of all input bits. -/
def andValue {n : ℕ} (x : Fin n → Bool) : Bool := decide (∀ i,x i=true)

/-- Every zero-error program computing OR on `n` bits uses at least `n` queries, for either
choice of strictness. -/
theorem or_zeroError_lower {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (strict : Bool) (P : Program n W) (E0 : Finset (Space n W))
    (h : ZeroError strict P E0 orValue) : n ≤ QueryCount P.circuit := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ m =>
    have hw : ZeroError false P E0 orValue := by
      cases strict with
      | false => exact h
      | true => exact zeroError_strict_weak P E0 orValue h
    have hno (x : Fin (m+1) → Bool) (hx : ∃ i,x i=true) :
        MeasureProb (output P x) E0=0 := (hw.2 x).1 (by simp [orValue,hx])
    have hz : acceptProb P (fun _ => false)=0 :=
      (hw.2 (fun _ => false)).2.1 (by simp [orValue])
    have hp : 0 < MeasureProb (output P (fun _ => false)) E0 := by
      have hq := (hw.2 (fun _ => false)).2.2
      simp only [Bool.false_eq_true,ite_false,hz,add_zero] at hq
      linarith
    have hl := Qatlib.Concepts.QueryComplexity.AdversarySearch.orZeroErrorQueryLowerBound (Fin (m+1)) W
      P.circuit (initial P) E0 (by simp) hno hp
    simpa only [Fintype.card_fin] using! hl

/-- The minimum zero-error query count for OR on `n` bits is `n`, under either strictness
convention. See [Beals et al., Proposition 6.1][BealsEtAl2001]. -/
theorem or_zeroErrorMinimum (n : ℕ) (strict : Bool) : zeroErrorMinimum strict (@orValue n)=n := by
  apply Nat.le_antisymm
  · cases strict with
    | false =>
      exact (zeroError_minima_order (@orValue n)).1.trans
        ((zeroError_minima_order (@orValue n)).2.trans (minima_upper_and_order (@orValue n)).2)
    | true => exact (zeroError_minima_order (@orValue n)).2.trans (minima_upper_and_order (@orValue n)).2
  · obtain ⟨S,hS,dS,P,E0,hq,hp⟩ := zeroErrorMinimum_attained strict (@orValue n)
    letI := hS
    letI := dS
    simpa only [hq] using! or_zeroError_lower strict P E0 hp

/-- The minimum exact query count for OR on `n` bits is `n` [BealsEtAl2001]. -/
theorem or_exactMinimum (n : ℕ) : exactMinimum (@orValue n)=n := by
  apply Nat.le_antisymm (minima_upper_and_order (@orValue n)).2
  have h := (zeroError_minima_order (@orValue n)).2
  rw [or_zeroErrorMinimum] at h
  exact h

namespace Complement
variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The gate that flips the oracle target bit and acts as the identity on the workspace. -/
noncomputable def targetX : Matrix (PolynomialWorkspace I W) (PolynomialWorkspace I W) ℂ :=
  TensorGate (BitOracleOn (fun _ : I => true)) 1

/-- The target-bit flip `targetX` is unitary. -/
theorem targetX_unitary :
    targetX (I := I) (W := W) ∈ Matrix.unitaryGroup (PolynomialWorkspace I W) ℂ :=
  tensorGate_unitary (bitOracleOn_unitary _) (Submonoid.one_mem _)

/-- Flipping the target bit after a query to `f` implements a query to the pointwise complement
of `f`. -/
theorem targetX_after_query (f : I → Bool) (ψ : QState (PolynomialWorkspace I W)) :
    ApplyGate targetX (ApplyGate (TensorGate (BitOracleOn f) 1) ψ) =
      ApplyGate (TensorGate (BitOracleOn (fun i => !(f i))) 1) ψ := by
  funext p
  obtain ⟨⟨i, b⟩, w⟩ := p
  simp only [targetX, applyGate_bitOracleOn_workspace]
  change ψ ((i, (b ^^ true) ^^ f i), w) = ψ ((i, b ^^ !(f i)), w)
  cases b <;> cases f i <;> rfl

/-- Inserts a target-bit flip after each query, leaving the other gates unchanged. -/
noncomputable def complementQueries : Circuit (PolynomialWorkspace I W) →
    Circuit (PolynomialWorkspace I W)
  | [] => []
  | .gate U :: C => .gate U :: complementQueries C
  | .query :: C => .query :: .gate targetX :: complementQueries C

/-- The transformed circuit with oracle `f` has the same output state as the original circuit
with the complemented oracle. -/
theorem complementQueries_run (C : Circuit (PolynomialWorkspace I W))
    (f : I → Bool) (ψ : QState (PolynomialWorkspace I W)) :
    Run (TensorGate (BitOracleOn f) 1) (complementQueries C) ψ =
      Run (TensorGate (BitOracleOn (fun i => !(f i))) 1) C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simpa only [complementQueries, run_gate] using! ih (ApplyGate U ψ)
    | query =>
      simp only [complementQueries, run_query, run_gate, targetX_after_query]
      exact ih _

omit [Fintype I] [Fintype W] in

/-- Complementing a circuit's queries preserves its query count. -/
theorem complementQueries_queryCount (C : Circuit (PolynomialWorkspace I W)) :
    QueryCount (complementQueries C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [complementQueries, ih]

omit [Fintype I] [Fintype W] in

/-- Complementing the queries adds exactly one gate per query to the gate count. -/
theorem complementQueries_gateCount (C : Circuit (PolynomialWorkspace I W)) :
    GateCount (complementQueries C) = GateCount C + QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [complementQueries, ih] <;> omega

/-- The query-complement transformation preserves unitarity of the circuit's gates. -/
theorem complementQueries_unitary (C : Circuit (PolynomialWorkspace I W))
    (hC : IsUnitaryCircuit C) : IsUnitaryCircuit (complementQueries C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [isUnitaryCircuit_gate] at hC
      exact (isUnitaryCircuit_gate _ _).mpr ⟨hC.1, ih hC.2⟩
    | query =>
      exact (isUnitaryCircuit_query _).mpr
        ((isUnitaryCircuit_gate _ _).mpr ⟨targetX_unitary, ih ((isUnitaryCircuit_query _).mp hC)⟩)

/-- A nonempty-input circuit whose chosen event has positive probability on the all-true input
and zero probability on every other input uses at least one query per input index. -/
theorem and_lower (C : Circuit (PolynomialWorkspace I W))
    (ψ : QState (PolynomialWorkspace I W)) (E1 : Finset (PolynomialWorkspace I W))
    (hcard : 0 < Fintype.card I)
    (hbad : ∀ f : I → Bool, (∃ i, f i = false) →
      MeasureProb (Run (TensorGate (BitOracleOn f) 1) C ψ) E1 = 0)
    (hgood : 0 < MeasureProb
      (Run (TensorGate (BitOracleOn (fun _ : I => true)) 1) C ψ) E1) :
    Fintype.card I ≤ QueryCount C := by
  have h := Qatlib.Concepts.QueryComplexity.AdversarySearch.orZeroErrorQueryLowerBound
    I W (complementQueries C) ψ E1 hcard
  rw [complementQueries_queryCount] at h
  apply h
  · intro f hf
    rw [complementQueries_run]
    apply hbad
    obtain ⟨i, hi⟩ := hf
    exact ⟨i, by simp [hi]⟩
  · simpa only [complementQueries_run, Bool.not_false] using! hgood

end Complement

/-- Every zero-error program computing AND on `n` bits uses at least `n` queries, for either
choice of strictness. -/
theorem and_zeroError_lower {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (strict : Bool) (P : Program n W) (E0 : Finset (Space n W))
    (h : ZeroError strict P E0 andValue) : n ≤ QueryCount P.circuit := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ m =>
    have hw : ZeroError false P E0 andValue := by
      cases strict with
      | false => exact h
      | true => exact zeroError_strict_weak P E0 andValue h
    have hno (x : Fin (m+1) → Bool) (hx : ∃ i,x i=false) : acceptProb P x=0 := by
      apply (hw.2 x).2.1
      obtain ⟨i,hi⟩ := hx
      have hn : ¬∀ i,x i=true := fun ha => by
        have hh := ha i
        rw [hi] at hh
        exact Bool.false_ne_true hh
      simp [andValue,hn]
    have hz : MeasureProb (output P (fun _ => true)) E0=0 :=
      (hw.2 (fun _ => true)).1 (by simp [andValue])
    have hp : 0 < acceptProb P (fun _ => true) := by
      have hq := (hw.2 (fun _ => true)).2.2
      simp only [Bool.false_eq_true,ite_false,hz,zero_add] at hq
      linarith
    have hl :=
        Complement.and_lower (I:=Fin (m+1)) (W:=W) P.circuit (initial P) P.accept (by simp) hno hp
    simpa only [Fintype.card_fin] using! hl

/-- The minimum zero-error query count for AND on `n` bits is `n`, under either strictness
convention. -/
theorem and_zeroErrorMinimum (n : ℕ) (strict : Bool) : zeroErrorMinimum strict (@andValue n)=n := by
  apply Nat.le_antisymm
  · cases strict with
    | false =>
      exact (zeroError_minima_order (@andValue n)).1.trans
        ((zeroError_minima_order (@andValue n)).2.trans (minima_upper_and_order (@andValue n)).2)
    | true => exact (zeroError_minima_order (@andValue n)).2.trans (minima_upper_and_order (@andValue n)).2
  · obtain ⟨S,hS,dS,P,E0,hq,hp⟩ := zeroErrorMinimum_attained strict (@andValue n)
    letI := hS
    letI := dS
    simpa only [hq] using! and_zeroError_lower strict P E0 hp

/-- The minimum exact query count for AND on `n` bits is `n`. -/
theorem and_exactMinimum (n : ℕ) : exactMinimum (@andValue n)=n := by
  apply Nat.le_antisymm (minima_upper_and_order (@andValue n)).2
  have h := (zeroError_minima_order (@andValue n)).2
  rw [and_zeroErrorMinimum] at h
  exact h

/-- Specifies a correct search answer: `none` certifies that all bits are false, while `some i`
identifies a true bit. -/
def SearchValid {n : ℕ} (x : Fin n → Bool) : Option (Fin n) → Prop
  | none => ∀ i,x i=false
  | some i => x i=true

/-- The result of `firstMarked` is a valid search answer. -/
theorem firstMarked_valid {n : ℕ} (x : Fin n → Bool) : SearchValid x (firstMarked n x) := by
  have h := firstMarked_spec n x
  cases he : firstMarked n x with
  | none => simpa only [he,FirstSpec,SearchValid] using! h
  | some i =>
    have hi : FirstSpec x (some i) := by simpa only [he] using! h
    exact hi.1

/-- A query program equipped with a decoder for an inconclusive outcome, a no-solution answer,
or a marked index. -/
structure SearchProgram (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] where
  base : Program n W
  decode : Space n W → Option (Option (Fin n))

variable {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- The measurement outcomes decoded as a conclusive search answer. -/
def answeredEvent (P : SearchProgram n W) : Finset (Space n W) :=
  Finset.univ.filter (fun q => (P.decode q).isSome)

/-- The measurement outcomes decoded as a conclusive answer that is invalid for the input. -/
def wrongEvent (P : SearchProgram n W) (x : Fin n → Bool) : Finset (Space n W) :=
  Finset.univ.filter (fun q => match P.decode q with | none => False | some a => ¬SearchValid x a)

/-- Requires zero probability of a wrong answer and probability one of a conclusive answer on
every input. -/
def SearchExact (P : SearchProgram n W) : Prop := ∀ x,
  MeasureProb (output P.base x) (wrongEvent P x)=0 ∧ MeasureProb (output P.base x) (answeredEvent P)=1

/-- Requires zero probability of a wrong answer and conclusive probability at least one half, or
strictly greater than one half when `strict` is true. -/
def SearchZeroError (strict : Bool) (P : SearchProgram n W) : Prop := ∀ x,
  MeasureProb (output P.base x) (wrongEvent P x)=0 ∧
  (if strict then (1:ℝ)/2 < MeasureProb (output P.base x) (answeredEvent P)
    else (1:ℝ)/2 ≤ MeasureProb (output P.base x) (answeredEvent P))

/-- An exact search program satisfies either zero-error strictness convention. -/
theorem searchExact_zeroError (strict : Bool) (P : SearchProgram n W) (h : SearchExact P) :
    SearchZeroError strict P := by
  intro x
  refine ⟨(h x).1,?_⟩
  rw [(h x).2]
  cases strict <;> norm_num

/-- The measurement outcomes decoded as a conclusive no-solution answer. -/
def negativeEvent (P : SearchProgram n W) : Finset (Space n W) :=
  Finset.univ.filter (fun q => P.decode q=some none)

/-- The measurement outcomes decoded as a marked-index answer. -/
def positiveEvent (P : SearchProgram n W) : Finset (Space n W) :=
  Finset.univ.filter (fun q => ∃ i,P.decode q=some (some i))

/-- The no-solution and marked-index answer events are disjoint. -/
theorem answer_disjoint (P : SearchProgram n W) : Disjoint (negativeEvent P) (positiveEvent P) := by
  apply Finset.disjoint_left.mpr
  intro q hn hp
  have hn' := (Finset.mem_filter.mp hn).2
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hp).2
  rw [hn'] at hi
  cases hi

/-- The union of the no-solution and marked-index events is exactly the conclusive-answer event. -/
theorem answer_union (P : SearchProgram n W) : negativeEvent P∪positiveEvent P=answeredEvent P := by
  ext q
  cases he : P.decode q with
  | none => simp [negativeEvent,positiveEvent,answeredEvent,he]
  | some a => cases a <;> simp [negativeEvent,positiveEvent,answeredEvent,he]

/-- Converts a search program to an OR decision program by accepting marked-index answers. -/
def searchOrProgram (P : SearchProgram n W) : Program n W := {P.base with accept:=positiveEvent P}

/-- Every subevent of the wrong-answer event has probability zero when the wrong-answer event
has probability zero. -/
theorem wrong_subset_zero (P : SearchProgram n W) (x : Fin n → Bool) (E : Finset (Space n W))
    (hw : MeasureProb (output P.base x) (wrongEvent P x)=0) (he : E ⊆ wrongEvent P x) :
    MeasureProb (output P.base x) E=0 :=
  le_antisymm ((measureProb_mono _ he).trans_eq hw) (measureProb_nonneg _ _)

/-- A zero-error search program yields a zero-error OR decision program with the same underlying
circuit. -/
theorem search_or_zeroError (strict : Bool) (P : SearchProgram n W) (h : SearchZeroError strict P) :
    ZeroError strict (searchOrProgram P) (negativeEvent P) orValue := by
  refine ⟨answer_disjoint P,?_⟩
  intro x
  refine ⟨?_,?_,?_⟩
  · intro hx
    change MeasureProb (output P.base x) (negativeEvent P)=0
    apply wrong_subset_zero P x _ (h x).1
    intro q hq
    have hd := (Finset.mem_filter.mp hq).2
    simp only [wrongEvent,Finset.mem_filter,Finset.mem_univ,true_and,hd]
    change ¬∀ i,x i=false
    have hmark : ∃ i,x i=true := of_decide_eq_true hx
    obtain ⟨i,hi⟩ := hmark
    intro hall
    rw [hall i] at hi
    cases hi
  · intro hx
    change MeasureProb (output P.base x) (positiveEvent P)=0
    apply wrong_subset_zero P x _ (h x).1
    intro q hq
    obtain ⟨i,hd⟩ := (Finset.mem_filter.mp hq).2
    simp only [wrongEvent,Finset.mem_filter,Finset.mem_univ,true_and,hd]
    change ¬x i=true
    intro hi
    have ht : orValue x=true := by simp [orValue]; exact ⟨i,hi⟩
    rw [hx] at ht
    cases ht
  · change (if strict then (1:ℝ)/2 < MeasureProb (output P.base x) (negativeEvent P)+
          MeasureProb (output P.base x) (positiveEvent P)
        else (1:ℝ)/2 ≤ MeasureProb (output P.base x) (negativeEvent P)+
          MeasureProb (output P.base x) (positiveEvent P))
    rw [← measureProb_union _ (answer_disjoint P),answer_union]
    exact (h x).2

/-- Every zero-error search program on `n` bits uses at least `n` queries. -/
theorem search_zeroError_lower (strict : Bool) (P : SearchProgram n W) (h : SearchZeroError strict P) :
    n ≤ QueryCount P.base.circuit :=
  or_zeroError_lower strict (searchOrProgram P) (negativeEvent P) (search_or_zeroError strict P h)

/-- The search program on `m + 1` bits that reads the input and decodes its first marked index. -/
def positiveSearch (m : ℕ) : SearchProgram (m+1) (Fin (m+1) → Bool) where
  base := positiveProgram m (fun _ => false)
  decode := fun q => some (firstMarked (m+1) q.2)

/-- The search program on an empty input that always reports no solution. -/
def zeroSearch : SearchProgram 0 Unit where
  base := constantProgram 0 false
  decode := fun _ => some none

/-- The first-marked program on `m + 1` bits is exact. -/
theorem positiveSearch_exact (m : ℕ) : SearchExact (positiveSearch m) := by
  intro x
  have hr : output (positiveSearch m).base x=Qatlib.Foundations.PureStateMath.Ket ((cleanAddress (m+1),false),x) :=
    positiveProgram_output m (fun _ => false) x
  have hv := firstMarked_valid x
  constructor
  · rw [hr,basis_probability]
    simp [wrongEvent,positiveSearch,hv]
  · rw [hr,basis_probability]
    simp [answeredEvent,positiveSearch]

/-- The empty-input search program is exact. -/
theorem zeroSearch_exact : SearchExact zeroSearch := by
  intro x
  have hr :
      output zeroSearch.base x=Qatlib.Foundations.PureStateMath.Ket
      ((cleanAddress 0,false),()) := rfl
  constructor
  · rw [hr,basis_probability]
    simp [wrongEvent,zeroSearch,SearchValid]
  · rw [hr,basis_probability]
    simp [answeredEvent,zeroSearch]

/-- The first-marked program on `m + 1` bits uses `m + 1` queries and `3 * (m + 1)` gates. -/
theorem positiveSearch_counts (m : ℕ) :
    QueryCount (positiveSearch m).base.circuit=m+1 ∧
      GateCount (positiveSearch m).base.circuit=3*(m+1) :=
  positiveProgram_counts m (fun _ => false)

/-- The probability that measuring a search program's output yields the specified decoded
outcome. -/
def decodedProbability (P : SearchProgram n W) (x : Fin n → Bool) (a : Option (Option (Fin n))) : ℝ :=
  MeasureProb (output P.base x) (Finset.univ.filter (fun q => P.decode q=a))

/-- The inconclusive probability and the conclusive-answer probability sum to one. -/
theorem search_inconclusive_identity (P : SearchProgram n W) (x : Fin n → Bool) :
    decodedProbability P x none+MeasureProb (output P.base x) (answeredEvent P)=1 := by
  have he : (answeredEvent P)ᶜ=Finset.univ.filter (fun q => P.decode q=none) := by
    ext q
    cases hd : P.decode q <;> simp [answeredEvent,hd]
  have h := event_complement ({P.base with accept:=answeredEvent P}) x
  change MeasureProb (output P.base x) (answeredEvent P)ᶜ+
    MeasureProb (output P.base x) (answeredEvent P)=1 at h
  rw [he] at h
  exact h

/-- Zero-error search is equivalent to having no wrong answers and inconclusive probability at
most one half, with a strict inequality when requested. -/
theorem search_zeroError_inconclusive (strict : Bool) (P : SearchProgram n W) :
    SearchZeroError strict P ↔ ∀ x,
      MeasureProb (output P.base x) (wrongEvent P x)=0 ∧
        (if strict then decodedProbability P x none < (1:ℝ)/2
          else decodedProbability P x none ≤ (1:ℝ)/2) := by
  constructor
  · intro h x
    refine ⟨(h x).1,?_⟩
    have hi := search_inconclusive_identity P x
    have hs := (h x).2
    cases strict <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hs ⊢ <;> linarith
  · intro h x
    refine ⟨(h x).1,?_⟩
    have hi := search_inconclusive_identity P x
    have hs := (h x).2
    cases strict <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hs ⊢ <;> linarith

/-- The positive-length search program returns `firstMarked` with probability one. -/
theorem positiveSearch_first (m : ℕ) (x : Fin (m+1) → Bool) :
    decodedProbability (positiveSearch m) x (some (firstMarked (m+1) x))=1 := by
  unfold decodedProbability
  rw [show output (positiveSearch m).base x=Qatlib.Foundations.PureStateMath.Ket ((cleanAddress (m+1),false),x)
    from positiveProgram_output m (fun _ => false) x,basis_probability]
  simp [positiveSearch]

/-- The empty-input search program reports no solution with probability one. -/
theorem zeroSearch_none (x : Fin 0 → Bool) : decodedProbability zeroSearch x (some none)=1 := by
  unfold decodedProbability
  rw [show output zeroSearch.base x=Qatlib.Foundations.PureStateMath.Ket ((cleanAddress 0,false),()) from rfl,basis_probability]
  simp [zeroSearch]

/-- The positive-length search program has zero probability of an inconclusive outcome. -/
theorem positiveSearch_not_inconclusive (m : ℕ) (x : Fin (m+1) → Bool) :
    decodedProbability (positiveSearch m) x none=0 := by
  simp [decodedProbability,positiveSearch,MeasureProb]

/-- Asserts the existence of an exact program using `n` queries and `3 * n` gates that returns
`firstMarked` with probability one. -/
def SearchFirstFeasible (n : ℕ) : Prop :=
  ∃ (S : Type) (hS : Fintype S) (dS : DecidableEq S) (P : @SearchProgram n S hS dS),
    QueryCount P.base.circuit=n ∧ GateCount P.base.circuit=3*n ∧ @SearchExact n S hS dS P ∧
      ∀ x, @decodedProbability n S hS dS P x (some (firstMarked n x))=1

/-- First-marked search is feasible with `n` queries and `3 * n` gates for every input length. -/
theorem search_first_feasible (n : ℕ) : SearchFirstFeasible n := by
  cases n with
  | zero => exact ⟨Unit,inferInstance,inferInstance,zeroSearch,rfl,rfl,zeroSearch_exact,zeroSearch_none⟩
  | succ m => exact ⟨Fin (m+1) → Bool,inferInstance,inferInstance,positiveSearch m,
      (positiveSearch_counts m).1,(positiveSearch_counts m).2,positiveSearch_exact m,positiveSearch_first m⟩

/-- Asserts the existence of an exact search program on `n` bits using exactly `t` queries over
some finite workspace. -/
def SearchExactFeasible (n t : ℕ) : Prop :=
  ∃ (S : Type) (hS : Fintype S) (dS : DecidableEq S) (P : @SearchProgram n S hS dS),
    QueryCount P.base.circuit=t ∧ @SearchExact n S hS dS P

/-- Asserts the existence of a zero-error search program on `n` bits using exactly `t` queries
with the chosen strictness convention. -/
def SearchZeroErrorFeasible (strict : Bool) (n t : ℕ) : Prop :=
  ∃ (S : Type) (hS : Fintype S) (dS : DecidableEq S) (P : @SearchProgram n S hS dS),
    QueryCount P.base.circuit=t ∧ @SearchZeroError n S hS dS strict P

/-- Exact search on `n` bits is feasible with exactly `n` queries. -/
theorem search_exact_feasible (n : ℕ) : SearchExactFeasible n n := by
  cases n with
  | zero => exact ⟨Unit,inferInstance,inferInstance,zeroSearch,rfl,zeroSearch_exact⟩
  | succ m => exact ⟨Fin (m+1) → Bool,inferInstance,inferInstance,positiveSearch m,
      (positiveSearch_counts m).1,positiveSearch_exact m⟩

/-- Any query count feasible for exact search is feasible for zero-error search under either
strictness convention. -/
theorem searchExactFeasible_zeroError (strict : Bool) (n t : ℕ) (h : SearchExactFeasible n t) :
    SearchZeroErrorFeasible strict n t := by
  obtain ⟨S,hS,dS,P,hq,hp⟩ := h
  letI := hS
  letI := dS
  exact ⟨S,hS,dS,P,hq,searchExact_zeroError strict P hp⟩

/-- There exists a feasible exact-search query count for every input length. -/
theorem searchExactFeasible_nonempty (n : ℕ) : ∃ t,SearchExactFeasible n t :=
    ⟨n,search_exact_feasible n⟩

/-- There exists a feasible zero-error-search query count for every input length and strictness
convention. -/
theorem searchZeroErrorFeasible_nonempty (strict : Bool) (n : ℕ) :
    ∃ t,SearchZeroErrorFeasible strict n t :=
  ⟨n,searchExactFeasible_zeroError strict n n (search_exact_feasible n)⟩

/-- The least query count among exact search programs on `n` bits over finite workspaces. -/
def searchExactMinimum (n : ℕ) : ℕ := Nat.find (searchExactFeasible_nonempty n)
/-- The least query count among zero-error search programs on `n` bits with the specified
strictness convention. -/
def searchZeroErrorMinimum (strict : Bool) (n : ℕ) : ℕ :=
    Nat.find (searchZeroErrorFeasible_nonempty strict n)

/-- The minimum zero-error search query count on `n` bits is `n`, for either strictness
convention [BealsEtAl2001]. -/
theorem search_zeroErrorMinimum (n : ℕ) (strict : Bool) : searchZeroErrorMinimum strict n=n := by
  apply Nat.le_antisymm
  · exact Nat.find_min' (searchZeroErrorFeasible_nonempty strict n)
      (searchExactFeasible_zeroError strict n n (search_exact_feasible n))
  · obtain ⟨S,hS,dS,P,hq,hp⟩ := Nat.find_spec (searchZeroErrorFeasible_nonempty strict n)
    letI := hS
    letI := dS
    simpa only [hq] using! search_zeroError_lower strict P hp

/-- The minimum exact search query count on `n` bits is `n` [BealsEtAl2001]. -/
theorem search_exactMinimum (n : ℕ) : searchExactMinimum n=n := by
  apply Nat.le_antisymm
  · exact Nat.find_min' (searchExactFeasible_nonempty n) (search_exact_feasible n)
  · obtain ⟨S,hS,dS,P,hq,hp⟩ := Nat.find_spec (searchExactFeasible_nonempty n)
    letI := hS
    letI := dS
    simpa only [hq] using! search_zeroError_lower true P (searchExact_zeroError true P hp)

/-- Collects correctness and feasibility of first-marked search together with the exact and
zero-error minimum query counts for OR, AND, and search. -/
theorem frontier1 (n : ℕ) :
    (∀ x : Fin n → Bool,FirstSpec x (firstMarked n x)) ∧
    SearchFirstFeasible n ∧
    SearchExactFeasible n n ∧
    exactMinimum (@orValue n)=n ∧ exactMinimum (@andValue n)=n ∧
    searchExactMinimum n=n ∧
    (∀ strict : Bool,zeroErrorMinimum strict (@orValue n)=n ∧
      zeroErrorMinimum strict (@andValue n)=n ∧ searchZeroErrorMinimum strict n=n) :=
  ⟨firstMarked_spec n,search_first_feasible n,search_exact_feasible n,or_exactMinimum n,and_exactMinimum n,
   search_exactMinimum n,fun strict => ⟨or_zeroErrorMinimum n strict,and_zeroErrorMinimum n strict,
     search_zeroErrorMinimum n strict⟩⟩

end
end Qatlib.Concepts.QueryComplexity.DegreeMethod.OrAndSearchUpper
