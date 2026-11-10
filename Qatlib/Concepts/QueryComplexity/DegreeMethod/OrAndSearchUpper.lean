/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
import Qatlib.Concepts.QueryComplexity.AdversarySearch.OrZeroErrorQueryLowerBoundBeal
set_option warningAsError false
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

def firstMarked : (n : ℕ) → (Fin n → Bool) → Option (Fin n)
  | 0,_ => none
  | n+1,x => if x 0 then some 0 else (firstMarked n (fun i => x i.succ)).map Fin.succ

def FirstSpec {n : ℕ} (x : Fin n → Bool) : Option (Fin n) → Prop
  | none => ∀ i,x i=false
  | some j => x j=true ∧ ∀ i,i.val < j.val → x i=false

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

theorem firstMarked_some {n : ℕ} (x : Fin n → Bool) (j : Fin n)
    (h : firstMarked n x=some j) : x j=true ∧ ∀ i,i.val < j.val → x i=false := by
  simpa only [h,FirstSpec] using! firstMarked_spec n x

open scoped Classical
noncomputable section

def orValue {n : ℕ} (x : Fin n → Bool) : Bool := decide (∃ i,x i=true)
def andValue {n : ℕ} (x : Fin n → Bool) : Bool := decide (∀ i,x i=true)

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

theorem or_exactMinimum (n : ℕ) : exactMinimum (@orValue n)=n := by
  apply Nat.le_antisymm (minima_upper_and_order (@orValue n)).2
  have h := (zeroError_minima_order (@orValue n)).2
  rw [or_zeroErrorMinimum] at h
  exact h

namespace Complement
variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

noncomputable def targetX : Matrix (PolynomialWorkspace I W) (PolynomialWorkspace I W) ℂ :=
  TensorGate (BitOracleOn (fun _ : I => true)) 1

theorem targetX_unitary :
    targetX (I := I) (W := W) ∈ Matrix.unitaryGroup (PolynomialWorkspace I W) ℂ :=
  tensorGate_unitary (bitOracleOn_unitary _) (Submonoid.one_mem _)

theorem targetX_after_query (f : I → Bool) (ψ : QState (PolynomialWorkspace I W)) :
    ApplyGate targetX (ApplyGate (TensorGate (BitOracleOn f) 1) ψ) =
      ApplyGate (TensorGate (BitOracleOn (fun i => !(f i))) 1) ψ := by
  funext p
  obtain ⟨⟨i, b⟩, w⟩ := p
  simp only [targetX, applyGate_bitOracleOn_workspace]
  change ψ ((i, (b ^^ true) ^^ f i), w) = ψ ((i, b ^^ !(f i)), w)
  cases b <;> cases f i <;> rfl

noncomputable def complementQueries : Circuit (PolynomialWorkspace I W) →
    Circuit (PolynomialWorkspace I W)
  | [] => []
  | .gate U :: C => .gate U :: complementQueries C
  | .query :: C => .query :: .gate targetX :: complementQueries C

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

theorem complementQueries_queryCount (C : Circuit (PolynomialWorkspace I W)) :
    QueryCount (complementQueries C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [complementQueries, ih]

omit [Fintype I] [Fintype W] in

theorem complementQueries_gateCount (C : Circuit (PolynomialWorkspace I W)) :
    GateCount (complementQueries C) = GateCount C + QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [complementQueries, ih] <;> omega

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

theorem and_exactMinimum (n : ℕ) : exactMinimum (@andValue n)=n := by
  apply Nat.le_antisymm (minima_upper_and_order (@andValue n)).2
  have h := (zeroError_minima_order (@andValue n)).2
  rw [and_zeroErrorMinimum] at h
  exact h

def SearchValid {n : ℕ} (x : Fin n → Bool) : Option (Fin n) → Prop
  | none => ∀ i,x i=false
  | some i => x i=true

theorem firstMarked_valid {n : ℕ} (x : Fin n → Bool) : SearchValid x (firstMarked n x) := by
  have h := firstMarked_spec n x
  cases he : firstMarked n x with
  | none => simpa only [he,FirstSpec,SearchValid] using! h
  | some i =>
    have hi : FirstSpec x (some i) := by simpa only [he] using! h
    exact hi.1

structure SearchProgram (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] where
  base : Program n W
  decode : Space n W → Option (Option (Fin n))

variable {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]

def answeredEvent (P : SearchProgram n W) : Finset (Space n W) :=
  Finset.univ.filter (fun q => (P.decode q).isSome)

def wrongEvent (P : SearchProgram n W) (x : Fin n → Bool) : Finset (Space n W) :=
  Finset.univ.filter (fun q => match P.decode q with | none => False | some a => ¬SearchValid x a)

def SearchExact (P : SearchProgram n W) : Prop := ∀ x,
  MeasureProb (output P.base x) (wrongEvent P x)=0 ∧ MeasureProb (output P.base x) (answeredEvent P)=1

def SearchZeroError (strict : Bool) (P : SearchProgram n W) : Prop := ∀ x,
  MeasureProb (output P.base x) (wrongEvent P x)=0 ∧
  (if strict then (1:ℝ)/2 < MeasureProb (output P.base x) (answeredEvent P)
    else (1:ℝ)/2 ≤ MeasureProb (output P.base x) (answeredEvent P))

theorem searchExact_zeroError (strict : Bool) (P : SearchProgram n W) (h : SearchExact P) :
    SearchZeroError strict P := by
  intro x
  refine ⟨(h x).1,?_⟩
  rw [(h x).2]
  cases strict <;> norm_num

def negativeEvent (P : SearchProgram n W) : Finset (Space n W) :=
  Finset.univ.filter (fun q => P.decode q=some none)

def positiveEvent (P : SearchProgram n W) : Finset (Space n W) :=
  Finset.univ.filter (fun q => ∃ i,P.decode q=some (some i))

theorem answer_disjoint (P : SearchProgram n W) : Disjoint (negativeEvent P) (positiveEvent P) := by
  apply Finset.disjoint_left.mpr
  intro q hn hp
  have hn' := (Finset.mem_filter.mp hn).2
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hp).2
  rw [hn'] at hi
  cases hi

theorem answer_union (P : SearchProgram n W) : negativeEvent P∪positiveEvent P=answeredEvent P := by
  ext q
  cases he : P.decode q with
  | none => simp [negativeEvent,positiveEvent,answeredEvent,he]
  | some a => cases a <;> simp [negativeEvent,positiveEvent,answeredEvent,he]

def searchOrProgram (P : SearchProgram n W) : Program n W := {P.base with accept:=positiveEvent P}

theorem wrong_subset_zero (P : SearchProgram n W) (x : Fin n → Bool) (E : Finset (Space n W))
    (hw : MeasureProb (output P.base x) (wrongEvent P x)=0) (he : E ⊆ wrongEvent P x) :
    MeasureProb (output P.base x) E=0 :=
  le_antisymm ((measureProb_mono _ he).trans_eq hw) (measureProb_nonneg _ _)

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

theorem search_zeroError_lower (strict : Bool) (P : SearchProgram n W) (h : SearchZeroError strict P) :
    n ≤ QueryCount P.base.circuit :=
  or_zeroError_lower strict (searchOrProgram P) (negativeEvent P) (search_or_zeroError strict P h)

def positiveSearch (m : ℕ) : SearchProgram (m+1) (Fin (m+1) → Bool) where
  base := positiveProgram m (fun _ => false)
  decode := fun q => some (firstMarked (m+1) q.2)

def zeroSearch : SearchProgram 0 Unit where
  base := constantProgram 0 false
  decode := fun _ => some none

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

theorem positiveSearch_counts (m : ℕ) :
    QueryCount (positiveSearch m).base.circuit=m+1 ∧
      GateCount (positiveSearch m).base.circuit=3*(m+1) :=
  positiveProgram_counts m (fun _ => false)

def decodedProbability (P : SearchProgram n W) (x : Fin n → Bool) (a : Option (Option (Fin n))) : ℝ :=
  MeasureProb (output P.base x) (Finset.univ.filter (fun q => P.decode q=a))

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

theorem positiveSearch_first (m : ℕ) (x : Fin (m+1) → Bool) :
    decodedProbability (positiveSearch m) x (some (firstMarked (m+1) x))=1 := by
  unfold decodedProbability
  rw [show output (positiveSearch m).base x=Qatlib.Foundations.PureStateMath.Ket ((cleanAddress (m+1),false),x)
    from positiveProgram_output m (fun _ => false) x,basis_probability]
  simp [positiveSearch]

theorem zeroSearch_none (x : Fin 0 → Bool) : decodedProbability zeroSearch x (some none)=1 := by
  unfold decodedProbability
  rw [show output zeroSearch.base x=Qatlib.Foundations.PureStateMath.Ket ((cleanAddress 0,false),()) from rfl,basis_probability]
  simp [zeroSearch]

theorem positiveSearch_not_inconclusive (m : ℕ) (x : Fin (m+1) → Bool) :
    decodedProbability (positiveSearch m) x none=0 := by
  simp [decodedProbability,positiveSearch,MeasureProb]

def SearchFirstFeasible (n : ℕ) : Prop :=
  ∃ (S : Type) (hS : Fintype S) (dS : DecidableEq S) (P : @SearchProgram n S hS dS),
    QueryCount P.base.circuit=n ∧ GateCount P.base.circuit=3*n ∧ @SearchExact n S hS dS P ∧
      ∀ x, @decodedProbability n S hS dS P x (some (firstMarked n x))=1

theorem search_first_feasible (n : ℕ) : SearchFirstFeasible n := by
  cases n with
  | zero => exact ⟨Unit,inferInstance,inferInstance,zeroSearch,rfl,rfl,zeroSearch_exact,zeroSearch_none⟩
  | succ m => exact ⟨Fin (m+1) → Bool,inferInstance,inferInstance,positiveSearch m,
      (positiveSearch_counts m).1,(positiveSearch_counts m).2,positiveSearch_exact m,positiveSearch_first m⟩

def SearchExactFeasible (n t : ℕ) : Prop :=
  ∃ (S : Type) (hS : Fintype S) (dS : DecidableEq S) (P : @SearchProgram n S hS dS),
    QueryCount P.base.circuit=t ∧ @SearchExact n S hS dS P

def SearchZeroErrorFeasible (strict : Bool) (n t : ℕ) : Prop :=
  ∃ (S : Type) (hS : Fintype S) (dS : DecidableEq S) (P : @SearchProgram n S hS dS),
    QueryCount P.base.circuit=t ∧ @SearchZeroError n S hS dS strict P

theorem search_exact_feasible (n : ℕ) : SearchExactFeasible n n := by
  cases n with
  | zero => exact ⟨Unit,inferInstance,inferInstance,zeroSearch,rfl,zeroSearch_exact⟩
  | succ m => exact ⟨Fin (m+1) → Bool,inferInstance,inferInstance,positiveSearch m,
      (positiveSearch_counts m).1,positiveSearch_exact m⟩

theorem searchExactFeasible_zeroError (strict : Bool) (n t : ℕ) (h : SearchExactFeasible n t) :
    SearchZeroErrorFeasible strict n t := by
  obtain ⟨S,hS,dS,P,hq,hp⟩ := h
  letI := hS
  letI := dS
  exact ⟨S,hS,dS,P,hq,searchExact_zeroError strict P hp⟩

theorem searchExactFeasible_nonempty (n : ℕ) : ∃ t,SearchExactFeasible n t :=
    ⟨n,search_exact_feasible n⟩

theorem searchZeroErrorFeasible_nonempty (strict : Bool) (n : ℕ) :
    ∃ t,SearchZeroErrorFeasible strict n t :=
  ⟨n,searchExactFeasible_zeroError strict n n (search_exact_feasible n)⟩

def searchExactMinimum (n : ℕ) : ℕ := Nat.find (searchExactFeasible_nonempty n)
def searchZeroErrorMinimum (strict : Bool) (n : ℕ) : ℕ :=
    Nat.find (searchZeroErrorFeasible_nonempty strict n)

theorem search_zeroErrorMinimum (n : ℕ) (strict : Bool) : searchZeroErrorMinimum strict n=n := by
  apply Nat.le_antisymm
  · exact Nat.find_min' (searchZeroErrorFeasible_nonempty strict n)
      (searchExactFeasible_zeroError strict n n (search_exact_feasible n))
  · obtain ⟨S,hS,dS,P,hq,hp⟩ := Nat.find_spec (searchZeroErrorFeasible_nonempty strict n)
    letI := hS
    letI := dS
    simpa only [hq] using! search_zeroError_lower strict P hp

theorem search_exactMinimum (n : ℕ) : searchExactMinimum n=n := by
  apply Nat.le_antisymm
  · exact Nat.find_min' (searchExactFeasible_nonempty n) (search_exact_feasible n)
  · obtain ⟨S,hS,dS,P,hq,hp⟩ := Nat.find_spec (searchExactFeasible_nonempty n)
    letI := hS
    letI := dS
    simpa only [hq] using! search_zeroError_lower true P (searchExact_zeroError true P hp)

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
