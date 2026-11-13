/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryDegree
import Qatlib.Concepts.QueryComplexity.DegreeMethod.AlphabetInterrogation
import Qatlib.Concepts.QueryComplexity.DegreeMethod.LocalCapability
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel

/-!
# Attained minima for Boolean quantum query programs

This module packages Boolean oracle algorithms as unitary `Program`s with a clean basis input
and an acceptance event. It defines attained minima for exact, bounded-error, and two zero-error
success conventions, including the zero-input case. The query model and polynomial degree
estimates follow the framework of [BealsEtAl2001].

An explicit reader computes every total Boolean function using `n` queries. Adding a fair coin
converts a zero-error program into a bounded-error program without extra queries, yielding the
order of all four minima and positivity for nonconstant functions.

## Main statements

* `read_all_feasible`: every total Boolean function is exactly feasible with `n` queries.
* `minimum_degree_bounds`: exact and approximate degrees are at most twice the corresponding
  query minima.
* `minimum_order_all`: orders bounded-error, weak zero-error, strict zero-error, and exact
  minima.
* `nonconstant_minima_positive`: each minimum is positive for a nonconstant function.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.HspRecovery.RecordExtract

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
open Matrix
open scoped Classical BigOperators ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

/-- The oracle address type, using `Unit` for zero input length and `Fin n` for positive input
length. -/
def Address : ℕ→Type
  | 0 => Unit
  | n+1 => Fin (n+1)

/-- The finite type structure on `Address n`, selected according to whether the input length is
zero or positive. -/
@[reducible] def addressFintype : (n : ℕ)→Fintype (Address n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => inferInstanceAs (Fintype (Fin (n+1)))

instance (n : ℕ) : Fintype (Address n) := addressFintype n

/-- Decidable equality on `Address n`, selected according to whether the input length is zero or
positive. -/
@[reducible] def addressDecidableEq : (n : ℕ)→DecidableEq (Address n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n+1 => inferInstanceAs (DecidableEq (Fin (n+1)))

instance (n : ℕ) : DecidableEq (Address n) := addressDecidableEq n

/-- The distinguished initial address, given by the unique unit value at length zero and
coordinate zero at positive length. -/
def cleanAddress : (n : ℕ)→Address n
  | 0 => ()
  | n+1 => ⟨0,Nat.zero_lt_succ n⟩

instance (n : ℕ) : Inhabited (Address n) := ⟨cleanAddress n⟩

/-- The Boolean input extended to `Address n`, with constant false value when the input length
is zero. -/
def inputAt : (n : ℕ)→(Fin n→Bool)→Address n→Bool
  | 0,_,_ => false
  | _+1,x,i => x i

/-- The state index type comprising an address, a Boolean response register, and a workspace
register. -/
abbrev Space (n : ℕ) (W : Type) := (Address n×Bool)×W

/-- A unitary Boolean query circuit equipped with a clean workspace basis value and a finite
acceptance event. -/
structure Program (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] where
  circuit : Circuit (Space n W)
  unitary : IsUnitaryCircuit circuit
  clean : W
  accept : Finset (Space n W)

variable {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- The clean initial basis state of a Boolean query program. -/
def initial (P : Program n W) : QState (Space n W) :=
  Qatlib.Foundations.PureStateMath.Ket ((cleanAddress n,false),P.clean)

/-- The final state obtained by running the program with the bit oracle for input `x`. -/
def output (P : Program n W) (x : Fin n→Bool) : QState (Space n W) :=
  Run (workspaceBitOracle (inputAt n x)) P.circuit (initial P)

/-- The probability of the program acceptance event in its final state on input `x`. -/
def acceptProb (P : Program n W) (x : Fin n→Bool) : ℝ := MeasureProb (output P x) P.accept

/-- The output state of a Boolean query program is normalized on every input. -/
theorem output_normalized (P : Program n W) (x : Fin n→Bool) : Normalized (output P x) :=
  P.unitary.normalized_run (workspaceBitOracle_unitary _) (normalized_ket _)

/-- The condition that the acceptance probability equals the zero-one encoding of `f` on every
input. -/
def Exact (P : Program n W) (f : (Fin n→Bool)→Bool) : Prop :=
  ∀ x, acceptProb P x=if f x then 1 else 0

/-- The condition that the acceptance probability approximates the zero-one encoding of `f`
within one-third on every input. -/
def Bounded (P : Program n W) (f : (Fin n→Bool)→Bool) : Prop :=
  ∀ x, |acceptProb P x-(if f x then (1:ℝ) else 0)|≤1/3

/-- An exact program satisfies the one-third bounded-error condition. -/
theorem exact_bounded (P : Program n W) (f : (Fin n→Bool)→Bool) (h : Exact P f) : Bounded P f := by
  intro x
  rw [h x]
  norm_num

namespace Reader
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The basis permutation exchanging two addresses while preserving the response and input
storage registers. -/
def addressSwap (j i : I) : Equiv.Perm ((I×Bool)×(I→Bool)) :=
  ((Equiv.swap j i).prodCongr (Equiv.refl Bool)).prodCongr (Equiv.refl _)

/-- The basis permutation exchanging the Boolean response register with storage cell `i`. -/
def storeSwap (i : I) : Equiv.Perm ((I×Bool)×(I→Bool)) where
  toFun p := ((p.1.1,p.2 i),Function.update p.2 i p.1.2)
  invFun p := ((p.1.1,p.2 i),Function.update p.2 i p.1.2)
  left_inv p := by ext k <;> simp [Function.update_idem]
  right_inv p := by ext k <;> simp [Function.update_idem]

/-- A circuit round that queries coordinate `i`, exchanges its response with storage cell `i`,
and restores the address register. -/
def round (j i : I) : Circuit ((I×Bool)×(I→Bool)) :=
  [.gate (permMatrix (addressSwap j i)),.query,.gate (permMatrix (storeSwap i)),
    .gate (permMatrix (addressSwap j i))]

/-- The circuit formed by concatenating reader rounds for the listed coordinates. -/
def readList (j : I) : List I→Circuit ((I×Bool)×(I→Bool))
  | [] => []
  | i::is => round j i++readList j is

/-- A permutation matrix sends a basis state to the basis state at the permuted index. -/
theorem perm_ket {H : Type} [Fintype H] [DecidableEq H] (e : Equiv.Perm H) (j : H) :
    permMatrix e *ᵥ Qatlib.Foundations.PureStateMath.Ket j=Qatlib.Foundations.PureStateMath.Ket (e j) := by
  ext x
  simp [Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,permMatrix]

/-- Each reader round is a unitary circuit. -/
theorem round_unitary (j i : I) : IsUnitaryCircuit (round j i) := by
  have ha := permMatrix_unitary_of_injective (addressSwap j i).injective
  have hs := permMatrix_unitary_of_injective (storeSwap i).injective
  simp [round,ha,hs]

/-- When storage cell `i` is false, a reader round writes `x i` into that cell and restores the
original address and false response. -/
theorem round_run (j i : I) (x s : I→Bool) (hi : s i=false) :
    Run (workspaceBitOracle x) (round j i) (Qatlib.Foundations.PureStateMath.Ket ((j,false),s)) =
      Qatlib.Foundations.PureStateMath.Ket ((j,false),Function.update s i (x i)) := by
  have ho : workspaceBitOracle x *ᵥ Qatlib.Foundations.PureStateMath.Ket ((i,false),s)=
      Qatlib.Foundations.PureStateMath.Ket ((i,x i),s) := by
    change ApplyGate (workspaceBitOracle x)
        (Qatlib.Foundations.PureStateMath.Ket ((i,false),s))=_
    rw [workspaceBitOracle,← tensorState_ket_ket (i,false) s,applyGate_tensorGate,
      applyGate_bitOracleOn_ket,applyGate_one,tensorState_ket_ket]
    simp
  simp only [round,Run,ApplyGate]
  rw [perm_ket]
  have hr : addressSwap j i ((j,false),s)=((i,false),s) := by
    simp [addressSwap,Equiv.prodCongr,Prod.map]
  rw [hr,ho,perm_ket]
  simp only [storeSwap,Equiv.coe_fn_mk,hi]
  rw [perm_ket]
  simp [addressSwap,Equiv.prodCongr,Prod.map]

/-- Reading distinct coordinates writes the input into those initially false storage cells and
preserves the other storage values. -/
theorem readList_run (j : I) (is : List I) (hn : is.Nodup) (x s : I→Bool)
    (hz : ∀ i∈is, s i=false) :
    Run (workspaceBitOracle x) (readList j is) (Qatlib.Foundations.PureStateMath.Ket ((j,false),s)) =
      Qatlib.Foundations.PureStateMath.Ket ((j,false),fun k => if k∈is then x k else s k) := by
  induction is generalizing s with
  | nil => simp [readList]
  | cons i is ih =>
    have hnot := (List.nodup_cons.mp hn).1
    rw [readList,run_append,round_run j i x s (hz i (by simp))]
    rw [ih (List.nodup_cons.mp hn).2 _ (by
      intro k hk
      have hki : k≠i := by intro h; subst k; exact hnot hk
      simp [Function.update,hki,hz k (by simp [hk])])]
    apply congrArg (fun s => Qatlib.Foundations.PureStateMath.Ket ((j,false),s))
    funext k
    by_cases hki : k=i
    · subst k; simp [hnot]
    · simp [hki,Function.update]

/-- Reading a coordinate list gives a unitary circuit with one query and three gates per list
element. -/
theorem readList_resources (j : I) (is : List I) :
    IsUnitaryCircuit (readList j is) ∧ QueryCount (readList j is)=is.length ∧
      GateCount (readList j is)=3*is.length := by
  induction is with
  | nil => simp [readList]
  | cons i is ih =>
    refine ⟨(isUnitaryCircuit_append _ _).mpr ⟨round_unitary j i,ih.1⟩,?_,?_⟩
    · simp [readList,round,QueryCount,ih.2.1]
    · simp [readList,round,GateCount,ih.2.2]; omega

/-- The circuit reading every coordinate of the finite address type into storage. -/
def readAll (j : I) : Circuit ((I×Bool)×(I→Bool)) :=
  readList j (Finset.univ : Finset I).toList

/-- Starting with false storage, the full reader produces the basis state storing the entire
input and restores the address and false response. -/
theorem readAll_run (j : I) (x : I→Bool) :
    Run (workspaceBitOracle x) (readAll j) (Qatlib.Foundations.PureStateMath.Ket ((j,false),fun _ => false)) =
      Qatlib.Foundations.PureStateMath.Ket ((j,false),x) := by
  rw [readAll,readList_run j _ (Finset.nodup_toList _) x (fun _ => false) (by simp)]
  apply congrArg (fun s => Qatlib.Foundations.PureStateMath.Ket ((j,false),s))
  funext k
  simp

/-- The full reader is unitary and uses one query and three gates per coordinate. -/
theorem readAll_resources (j : I) :
    IsUnitaryCircuit (readAll j) ∧ QueryCount (readAll j)=Fintype.card I ∧
      GateCount (readAll j)=3*Fintype.card I := by
  simpa only [readAll,Finset.length_toList,Finset.card_univ] using!
    readList_resources j (Finset.univ : Finset I).toList

end Reader

/-- A basis state gives an event probability of one exactly when its index belongs to the event,
and zero otherwise. -/
theorem basis_probability {H : Type} [Fintype H] [DecidableEq H] (j : H) (E : Finset H) :
    MeasureProb (Qatlib.Foundations.PureStateMath.Ket j) E=if j∈E then 1 else 0 := by
  simpa only [one_smul] using! measureProb_smul_ket (c:=1) (by simp) j E

/-- The unique Boolean input on the empty coordinate type `Fin 0`. -/
def emptyInput : Fin 0→Bool := fun i => Fin.elim0 i

/-- The query-free program for a zero-length input, with acceptance chosen by the value of `f`
at the unique input. -/
def zeroProgram (f : (Fin 0→Bool)→Bool) : Program 0 Unit where
  circuit := []
  unitary := by simp [IsUnitaryCircuit]
  clean := ()
  accept := if f emptyInput then Finset.univ else ∅

/-- The zero-length program computes its Boolean function exactly. -/
theorem zeroProgram_exact (f : (Fin 0→Bool)→Bool) : Exact (zeroProgram f) f := by
  intro x
  have hx : x=emptyInput := by funext i; exact Fin.elim0 i
  rw [hx]
  simp only [acceptProb,output,initial,zeroProgram,Run]
  rw [basis_probability]
  by_cases hf : f emptyInput=true <;> simp [hf]

/-- The program that reads all coordinates of a positive-length input and accepts according to
`f` of the stored input. -/
def positiveProgram (m : ℕ) (f : (Fin (m+1)→Bool)→Bool) : Program (m+1) (Fin (m+1)→Bool) where
  circuit := Reader.readAll (cleanAddress (m+1))
  unitary := (Reader.readAll_resources (cleanAddress (m+1))).1
  clean := fun _ => false
  accept := Finset.univ.filter (fun p => f p.2=true)

/-- The full reader program outputs the basis state storing `x`, with the clean address and
false response. -/
theorem positiveProgram_output (m : ℕ) (f : (Fin (m+1)→Bool)→Bool) (x : Fin (m+1)→Bool) :
    output (positiveProgram m f) x=Qatlib.Foundations.PureStateMath.Ket ((cleanAddress (m+1),false),x) := by
  exact Reader.readAll_run (cleanAddress (m+1)) x

/-- The positive-length full reader program computes `f` exactly. -/
theorem positiveProgram_exact (m : ℕ) (f : (Fin (m+1)→Bool)→Bool) :
    Exact (positiveProgram m f) f := by
  intro x
  rw [acceptProb,positiveProgram_output,basis_probability]
  simp only [positiveProgram,Finset.mem_filter,Finset.mem_univ,true_and]

/-- The full reader program on `m + 1` input bits uses `m + 1` queries and `3 * (m + 1)` gates. -/
theorem positiveProgram_counts (m : ℕ) (f : (Fin (m+1)→Bool)→Bool) :
    QueryCount (positiveProgram m f).circuit=m+1 ∧ GateCount (positiveProgram m f).circuit=3*(m+1) := by
  have h := (Reader.readAll_resources (I:=Fin (m+1)) (cleanAddress (m+1))).2
  simpa only [positiveProgram,Fintype.card_fin] using! h

/-- The existence of an exact program over some finite workspace with exactly `t` oracle
queries. -/
def ExactFeasible (f : (Fin n→Bool)→Bool) (t : ℕ) : Prop :=
  ∃ (S : Type) (hS : Fintype S) (dS : DecidableEq S) (P : @Program n S hS dS),
    QueryCount P.circuit=t ∧ @Exact n S hS dS P f

/-- The existence of a one-third bounded-error program over some finite workspace with exactly
`t` oracle queries. -/
def BoundedFeasible (f : (Fin n→Bool)→Bool) (t : ℕ) : Prop :=
  ∃ (S : Type) (hS : Fintype S) (dS : DecidableEq S) (P : @Program n S hS dS),
    QueryCount P.circuit=t ∧ @Bounded n S hS dS P f

/-- Every total Boolean function on `n` bits has an exact program using exactly `n` queries. -/
theorem read_all_feasible (f : (Fin n→Bool)→Bool) : ExactFeasible f n := by
  cases n with
  | zero => exact ⟨Unit,inferInstance,inferInstance,zeroProgram f,rfl,zeroProgram_exact f⟩
  | succ m =>
    exact ⟨Fin (m+1)→Bool,inferInstance,inferInstance,positiveProgram m f,
      (positiveProgram_counts m f).1,positiveProgram_exact m f⟩

/-- Exact feasibility at query count `t` implies bounded-error feasibility at the same count. -/
theorem exactFeasible_bounded (f : (Fin n→Bool)→Bool) (t : ℕ) (h : ExactFeasible f t) :
    BoundedFeasible f t := by
  obtain ⟨S,hS,dS,P,hq,hp⟩ := h
  letI := hS
  letI := dS
  exact ⟨S,hS,dS,P,hq,exact_bounded P f hp⟩

/-- Every total Boolean function has an exact feasible query count. -/
theorem exactFeasible_nonempty (f : (Fin n→Bool)→Bool) : ∃ t, ExactFeasible f t :=
  ⟨n,read_all_feasible f⟩

/-- Every total Boolean function has a bounded-error feasible query count. -/
theorem boundedFeasible_nonempty (f : (Fin n→Bool)→Bool) : ∃ t, BoundedFeasible f t :=
  ⟨n,exactFeasible_bounded f n (read_all_feasible f)⟩

/-- The least query count of an exact program computing `f`. -/
def exactMinimum (f : (Fin n→Bool)→Bool) : ℕ := Nat.find (exactFeasible_nonempty f)
/-- The least query count of a one-third bounded-error program computing `f`. -/
def boundedMinimum (f : (Fin n→Bool)→Bool) : ℕ := Nat.find (boundedFeasible_nonempty f)

/-- An exact program exists at the query count `exactMinimum f`. -/
theorem exactMinimum_attained (f : (Fin n→Bool)→Bool) : ExactFeasible f (exactMinimum f) :=
  Nat.find_spec (exactFeasible_nonempty f)

/-- A bounded-error program exists at the query count `boundedMinimum f`. -/
theorem boundedMinimum_attained (f : (Fin n→Bool)→Bool) : BoundedFeasible f (boundedMinimum f) :=
  Nat.find_spec (boundedFeasible_nonempty f)

/-- The exact query minimum is at most every exact feasible query count. -/
theorem exactMinimum_le (f : (Fin n→Bool)→Bool) (t : ℕ) (h : ExactFeasible f t) :
    exactMinimum f≤t := Nat.find_min' (exactFeasible_nonempty f) h

/-- The bounded-error query minimum is at most every bounded-error feasible query count. -/
theorem boundedMinimum_le (f : (Fin n→Bool)→Bool) (t : ℕ) (h : BoundedFeasible f t) :
    boundedMinimum f≤t := Nat.find_min' (boundedFeasible_nonempty f) h

/-- The bounded-error minimum is at most the exact minimum, and the exact minimum is at most the
input length. -/
theorem minima_upper_and_order (f : (Fin n→Bool)→Bool) :
    boundedMinimum f≤exactMinimum f ∧ exactMinimum f≤n :=
  ⟨boundedMinimum_le f _ (exactFeasible_bounded f _ (exactMinimum_attained f)),
    exactMinimum_le f n (read_all_feasible f)⟩

/-- The query-free program accepting all basis outcomes or none according to the constant output
bit `b`. -/
def constantProgram (n : ℕ) (b : Bool) : Program n Unit where
  circuit := []
  unitary := by simp [IsUnitaryCircuit]
  clean := ()
  accept := if b then Finset.univ else ∅

/-- The constant program computes the constant Boolean function exactly. -/
theorem constantProgram_exact (b : Bool) : Exact (constantProgram n b) (fun _ => b) := by
  intro x
  simp only [acceptProb,output,initial,constantProgram,Run]
  rw [basis_probability]
  cases b <;> simp

/-- Both exact and bounded-error query minima of a constant Boolean function are zero. -/
theorem constant_minima (b : Bool) :
    exactMinimum (fun _ : Fin n→Bool => b)=0 ∧
      boundedMinimum (fun _ : Fin n→Bool => b)=0 := by
  have h : ExactFeasible (fun _ : Fin n→Bool => b) 0 :=
    ⟨Unit,inferInstance,inferInstance,constantProgram n b,rfl,constantProgram_exact b⟩
  exact ⟨Nat.eq_zero_of_le_zero (exactMinimum_le _ 0 h),
    Nat.eq_zero_of_le_zero (boundedMinimum_le _ 0 (exactFeasible_bounded _ _ h))⟩
open Qatlib
open Qatlib

/-- Both exact degree and one-third approximate degree of a constant Boolean function are zero. -/
theorem constant_degrees (b : Bool) :
    exactDegree (fun _ : Fin n→Bool => b)=0 ∧
      approxDegree (fun _ : Fin n→Bool => b)=0 := by
  have he : ∀ x : Fin n→Bool,
      boolEval (MvPolynomial.C (if b then (1:ℝ) else 0)) x=if b then 1 else 0 := by
    intro x; simp [boolEval]
  constructor
  · apply Nat.eq_zero_of_le_zero
    unfold exactDegree
    exact csInf_le' ⟨MvPolynomial.C (if b then (1:ℝ) else 0),he,by cases b <;> simp⟩
  · apply Nat.eq_zero_of_le_zero
    unfold approxDegree
    refine csInf_le' ⟨MvPolynomial.C (if b then (1:ℝ) else 0),?_,by cases b <;> simp⟩
    intro x; rw [he]; norm_num

/-- Every Boolean function on zero-length inputs is the constant function given by its value at
`emptyInput`. -/
theorem empty_function_constant (f : (Fin 0→Bool)→Bool) : f=(fun _ => f emptyInput) := by
  funext x
  congr 1
  funext i
  exact Fin.elim0 i

/-- The exact degree of a function computed exactly by `P` is at most twice the query count of
`P` [BealsEtAl2001]. -/
theorem exact_degree_program (P : Program n W) (f : (Fin n→Bool)→Bool) (hf : Exact P f) :
    exactDegree f≤2*QueryCount P.circuit := by
  cases n with
  | zero => rw [empty_function_constant f,(constant_degrees (f emptyInput)).1]; omega
  | succ m =>
    obtain ⟨hd,_,he⟩ := acceptance_boolean_multilinearization_preserves_run
      P.circuit (initial P) P.accept
    apply le_trans ?_ hd
    unfold exactDegree
    apply csInf_le'
    refine ⟨booleanAcceptancePolynomial P.circuit (initial P) P.accept,?_,rfl⟩
    intro x
    exact (he x).trans (hf x)

/-- The one-third approximate degree of a function computed with bounded error by `P` is at most
twice the query count of `P` [BealsEtAl2001]. -/
theorem approximate_degree_program (P : Program n W) (f : (Fin n→Bool)→Bool)
    (hf : Bounded P f) : approxDegree f≤2*QueryCount P.circuit := by
  cases n with
  | zero => rw [empty_function_constant f,(constant_degrees (f emptyInput)).2]; omega
  | succ m =>
    obtain ⟨hd,_,he⟩ := acceptance_boolean_multilinearization_preserves_run
      P.circuit (initial P) P.accept
    apply le_trans ?_ hd
    unfold approxDegree
    apply csInf_le'
    refine ⟨booleanAcceptancePolynomial P.circuit (initial P) P.accept,?_,rfl⟩
    intro x
    have hx : boolEval (booleanAcceptancePolynomial P.circuit (initial P) P.accept) x=
        acceptProb P x := he x
    exact (congrArg (fun a : ℝ => |a-(if f x then (1:ℝ) else 0)|) hx).trans_le (hf x)

/-- Exact degree and approximate degree are at most twice the exact and bounded-error query
minima, respectively [BealsEtAl2001]. -/
theorem minimum_degree_bounds (f : (Fin n→Bool)→Bool) :
    exactDegree f≤2*exactMinimum f ∧ approxDegree f≤2*boundedMinimum f := by
  constructor
  · obtain ⟨S,hS,dS,P,hq,hp⟩ := exactMinimum_attained f
    letI := hS
    letI := dS
    simpa only [hq] using! exact_degree_program P f hp
  · obtain ⟨S,hS,dS,P,hq,hp⟩ := boundedMinimum_attained f
    letI := hS
    letI := dS
    simpa only [hq] using! approximate_degree_program P f hp

/-- The exact and bounded-error minima are attained, are ordered below the input length, and
satisfy their respective polynomial degree lower bounds. -/
theorem frontier1 (f : (Fin n→Bool)→Bool) :
    ExactFeasible f (exactMinimum f) ∧ BoundedFeasible f (boundedMinimum f) ∧
      boundedMinimum f≤exactMinimum f ∧ exactMinimum f≤n ∧
      exactDegree f≤2*exactMinimum f ∧ approxDegree f≤2*boundedMinimum f :=
  ⟨exactMinimum_attained f,boundedMinimum_attained f,(minima_upper_and_order f).1,
    (minima_upper_and_order f).2,(minimum_degree_bounds f).1,(minimum_degree_bounds f).2⟩

/-- The probability of the complement of the acceptance event plus the acceptance probability is
one. -/
theorem event_complement (P : Program n W) (x : Fin n→Bool) :
    MeasureProb (output P x) P.acceptᶜ+acceptProb P x=1 := by
  change MeasureProb (output P x) P.acceptᶜ+MeasureProb (output P x) P.accept=1
  rw [← measureProb_union _ disjoint_compl_left,Finset.union_comm,Finset.union_compl]
  exact measureProb_univ (output_normalized P x)

/-- The probability of the acceptance event for a true function value or its complement for a
false function value. -/
def successProbability (P : Program n W) (f : (Fin n→Bool)→Bool) (x : Fin n→Bool) : ℝ :=
  MeasureProb (output P x) (if f x then P.accept else P.acceptᶜ)

/-- The one-third bounded-error condition is equivalent to success probability at least
two-thirds on every input. -/
theorem bounded_iff_success (P : Program n W) (f : (Fin n→Bool)→Bool) :
    Bounded P f ↔ ∀x,(2:ℝ)/3 ≤ successProbability P f x := by
  constructor
  · intro h x
    have he := abs_le.mp (h x)
    have hc := event_complement P x
    cases hf : f x with
    | false =>
        simp only [hf,Bool.false_eq_true,ite_false,sub_zero] at he
        simp only [successProbability,hf,Bool.false_eq_true,ite_false]
        linarith
    | true =>
        simp only [hf,ite_true] at he
        simp only [successProbability,hf,ite_true]
        change (2:ℝ)/3≤acceptProb P x
        linarith
  · intro h x
    have hs := h x
    have hc := event_complement P x
    have h0 : 0≤acceptProb P x := measureProb_nonneg _ _
    have h1 : acceptProb P x≤1 := measureProb_le_one (output_normalized P x) _
    rw [abs_le]
    cases hf : f x with
    | false =>
        simp only [successProbability,hf,Bool.false_eq_true,ite_false] at hs
        simp only [Bool.false_eq_true,ite_false,sub_zero]
        constructor <;> linarith
    | true =>
        simp only [successProbability,hf,ite_true] at hs
        simp only [ite_true]
        change (2:ℝ)/3≤acceptProb P x at hs
        constructor <;> linarith

/-- The condition that disjoint rejection and acceptance events never give an incorrect answer
and have combined probability greater than one-half when `strict` is true, or at least
one-half otherwise. -/
def ZeroError (strict : Bool) (P : Program n W) (E0 : Finset (Space n W))
    (f : (Fin n→Bool)→Bool) : Prop :=
  Disjoint E0 P.accept ∧ ∀ x,
    (f x=true → MeasureProb (output P x) E0=0) ∧
    (f x=false → acceptProb P x=0) ∧
    (if strict then (1:ℝ)/2<MeasureProb (output P x) E0+acceptProb P x
      else (1:ℝ)/2≤MeasureProb (output P x) E0+acceptProb P x)

/-- An exact program satisfies either zero-error convention when the rejection event is the
complement of its acceptance event. -/
theorem exact_zeroError (strict : Bool) (P : Program n W) (f : (Fin n→Bool)→Bool)
    (h : Exact P f) : ZeroError strict P P.acceptᶜ f := by
  refine ⟨disjoint_compl_left,?_⟩
  intro x
  have hc := event_complement P x
  have hx := h x
  refine ⟨?_,?_,?_⟩
  · intro hf
    simp only [hf,ite_true] at hx
    linarith
  · intro hf
    simpa only [hf,Bool.false_eq_true,ite_false] using! hx
  · rw [hc]
    cases strict <;> norm_num

/-- The strict zero-error success condition implies the weak condition for the same events and
program. -/
theorem zeroError_strict_weak (P : Program n W) (E0 : Finset (Space n W))
    (f : (Fin n→Bool)→Bool) (h : ZeroError true P E0 f) : ZeroError false P E0 f := by
  refine ⟨h.1,fun x => ⟨(h.2 x).1,(h.2 x).2.1,?_⟩⟩
  exact le_of_lt ((h.2 x).2.2)

/-- For a zero-error program, the probability of an inconclusive outcome plus the combined
rejection and acceptance probability equals one. -/
theorem inconclusive_identity (strict : Bool) (P : Program n W)
    (E0 : Finset (Space n W)) (f : (Fin n→Bool)→Bool) (h : ZeroError strict P E0 f)
    (x : Fin n→Bool) :
    MeasureProb (output P x) (E0∪P.accept)ᶜ+
      (MeasureProb (output P x) E0+acceptProb P x)=1 := by
  change MeasureProb (output P x) (E0∪P.accept)ᶜ+
    (MeasureProb (output P x) E0+MeasureProb (output P x) P.accept)=1
  rw [← measureProb_union _ h.1]
  rw [← measureProb_union _ disjoint_compl_left,Finset.union_comm,Finset.union_compl]
  exact measureProb_univ (output_normalized P x)

/-- The existence of a program and rejection event satisfying the selected zero-error convention
with exactly `t` queries. -/
def ZeroErrorFeasible (strict : Bool) (f : (Fin n→Bool)→Bool) (t : ℕ) : Prop :=
  ∃ (S : Type) (hS : Fintype S) (dS : DecidableEq S) (P : @Program n S hS dS)
    (E0 : Finset (Space n S)), QueryCount P.circuit=t ∧ @ZeroError n S hS dS strict P E0 f

/-- Exact feasibility implies zero-error feasibility at the same query count for either success
convention. -/
theorem exactFeasible_zeroError (strict : Bool) (f : (Fin n→Bool)→Bool) (t : ℕ)
    (h : ExactFeasible f t) : ZeroErrorFeasible strict f t := by
  obtain ⟨S,hS,dS,P,hq,hp⟩ := h
  letI := hS
  letI := dS
  exact ⟨S,hS,dS,P,P.acceptᶜ,hq,exact_zeroError strict P f hp⟩

/-- Every total Boolean function has a feasible query count under either zero-error convention. -/
theorem zeroErrorFeasible_nonempty (strict : Bool) (f : (Fin n→Bool)→Bool) :
    ∃ t, ZeroErrorFeasible strict f t :=
  ⟨n,exactFeasible_zeroError strict f n (read_all_feasible f)⟩

/-- The least feasible query count under the selected zero-error success convention. -/
def zeroErrorMinimum (strict : Bool) (f : (Fin n→Bool)→Bool) : ℕ :=
  Nat.find (zeroErrorFeasible_nonempty strict f)

/-- A zero-error program exists at the query count `zeroErrorMinimum strict f`. -/
theorem zeroErrorMinimum_attained (strict : Bool) (f : (Fin n→Bool)→Bool) :
    ZeroErrorFeasible strict f (zeroErrorMinimum strict f) :=
  Nat.find_spec (zeroErrorFeasible_nonempty strict f)

/-- The selected zero-error query minimum is at most every feasible count for that convention. -/
theorem zeroErrorMinimum_le (strict : Bool) (f : (Fin n→Bool)→Bool) (t : ℕ)
    (h : ZeroErrorFeasible strict f t) : zeroErrorMinimum strict f≤t :=
  Nat.find_min' (zeroErrorFeasible_nonempty strict f) h

/-- The weak zero-error minimum is at most the strict zero-error minimum, which is at most the
exact minimum. -/
theorem zeroError_minima_order (f : (Fin n→Bool)→Bool) :
    zeroErrorMinimum false f≤zeroErrorMinimum true f ∧
      zeroErrorMinimum true f≤exactMinimum f := by
  constructor
  · obtain ⟨S,hS,dS,P,E0,hq,hp⟩ := zeroErrorMinimum_attained true f
    letI := hS
    letI := dS
    exact zeroErrorMinimum_le false f _ ⟨S,hS,dS,P,E0,hq,zeroError_strict_weak P E0 f hp⟩
  · exact zeroErrorMinimum_le true f _
      (exactFeasible_zeroError true f _ (exactMinimum_attained f))

/-- A constant Boolean function has zero query minimum under either zero-error convention. -/
theorem constant_zeroError_minimum (strict : Bool) (b : Bool) :
    zeroErrorMinimum strict (fun _ : Fin n→Bool => b)=0 := by
  apply Nat.eq_zero_of_le_zero
  apply zeroErrorMinimum_le
  apply exactFeasible_zeroError
  exact ⟨Unit,inferInstance,inferInstance,constantProgram n b,rfl,constantProgram_exact b⟩

namespace Coin
variable {J : Type} [Fintype J] [DecidableEq J]

/-- The circuit obtained by adding a Boolean register to `C` and applying a Hadamard gate to
that register after `C`. -/
def circuit (C : Circuit J) : Circuit (J×Bool) :=
  LiftCircuitTo Bool C++[.gate (TensorGate (1:Matrix J J ℂ) Hadamard)]

/-- Running the lifted circuit from a false coin register produces the original output state
tensored with `Plus`. -/
theorem run (O : Matrix J J ℂ) (C : Circuit J) (ψ : QState J) :
    Run (TensorGate O (1:Matrix Bool Bool ℂ)) (circuit C)
      (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket false))=TensorState (Run O C ψ) Plus := by
  rw [circuit,run_append,run_liftCircuitTo_liftedOracle]
  simp only [run_gate,run_nil,applyGate_tensorGate,applyGate_one,applyGate_hadamard_ket_false]

/-- The coin circuit preserves unitarity and query count while adding exactly one gate. -/
theorem resources (C : Circuit J) (h : IsUnitaryCircuit C) :
    IsUnitaryCircuit (circuit C) ∧ QueryCount (circuit C)=QueryCount C ∧
      GateCount (circuit C)=GateCount C+1 := by
  refine ⟨(isUnitaryCircuit_append _ _).mpr ⟨isUnitaryCircuit_liftCircuitTo h,?_⟩,?_,?_⟩
  · exact (isUnitaryCircuit_gate _ _).mpr
      ⟨tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary,isUnitaryCircuit_nil⟩
  · simp [circuit,queryCount_append,queryCount_liftCircuitTo]
  · simp [circuit,gateCount_append,gateCount_liftCircuitTo]

/-- Measuring `Plus` gives the outcome true with probability one-half. -/
theorem plus_true_mass : MeasureProb Plus {true}=(1:ℝ)/2 := by
  have he : Plus=Uniform Bool := by
    funext b
    simp [Plus,Uniform,hadamard_apply_false]
  rw [he,measureProb_uniform]
  norm_num

/-- The event that accepts every outcome in `E1` and accepts an outcome outside `E0 ∪ E1`
exactly when the coin is true. -/
def event (E0 E1 : Finset J) : Finset (J×Bool) :=
  (E1×ˢFinset.univ)∪((E0∪E1)ᶜ×ˢ{true})

/-- For an independent `Plus` coin, the guessing event has probability equal to the mass of `E1`
plus half the mass outside `E0 ∪ E1`. -/
theorem event_mass (ψ : QState J) (E0 E1 : Finset J) :
    MeasureProb (TensorState ψ Plus) (event E0 E1)=
      MeasureProb ψ E1+MeasureProb ψ (E0∪E1)ᶜ/2 := by
  have hd : Disjoint (E1×ˢ(Finset.univ:Finset Bool)) ((E0∪E1)ᶜ×ˢ{true}) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have h1 := (Finset.mem_product.mp hp).1
    have hI := (Finset.mem_product.mp hq).1
    exact (Finset.mem_compl.mp hI) (Finset.mem_union_right E0 h1)
  rw [event,measureProb_union _ hd,measureProb_tensorState_prod,
    measureProb_tensorState_prod,measureProb_univ normalized_plus,plus_true_mass]
  ring

end Coin

/-- The reassociation equivalence placing an additional Boolean register inside the program
workspace. -/
def coinAssoc : (Space n W×Bool)≃Space n (W×Bool) :=
  Equiv.prodAssoc (Address n×Bool) W Bool

/-- Reassociating the workspace and coin registers identifies the lifted bit oracle with the bit
oracle on the enlarged workspace. -/
theorem coin_oracle (x : Fin n→Bool) :
    relabelGate (coinAssoc (n:=n) (W:=W))
      (TensorGate (workspaceBitOracle (W:=W) (inputAt n x)) (1:Matrix Bool Bool ℂ))=
      workspaceBitOracle (W:=W×Bool) (inputAt n x) := by
  unfold coinAssoc workspaceBitOracle
  rw [relabelGate_prodAssoc,tensorGate_one]

/-- Reassociating the clean initial state and a false coin gives the clean basis state of the
enlarged workspace. -/
theorem coin_initial (P : Program n W) :
    relabelState coinAssoc (TensorState (initial P) (Qatlib.Foundations.PureStateMath.Ket false))=
      Qatlib.Foundations.PureStateMath.Ket ((cleanAddress n,false),(P.clean,false)) := by
  rw [show initial P=TensorState (Qatlib.Foundations.PureStateMath.Ket (cleanAddress n,false))
      (Qatlib.Foundations.PureStateMath.Ket P.clean) from (tensorState_ket_ket _ _).symm]
  rw [coinAssoc,relabelState_prodAssoc,tensorState_ket_ket,tensorState_ket_ket]

/-- The program that adds a fair coin and uses it to guess on outcomes outside the rejection and
acceptance events. -/
def guessProgram (P : Program n W) (E0 : Finset (Space n W)) : Program n (W×Bool) where
  circuit := relabelCircuit coinAssoc (Coin.circuit P.circuit)
  unitary := (relabelCircuit_legality_resources coinAssoc (Coin.circuit P.circuit)).1.mpr
    (Coin.resources P.circuit P.unitary).1
  clean := (P.clean,false)
  accept := (Coin.event E0 P.accept).map coinAssoc.toEmbedding

/-- Adding fair-coin guessing preserves the query count and adds one gate. -/
theorem guessProgram_counts (P : Program n W) (E0 : Finset (Space n W)) :
    QueryCount (guessProgram P E0).circuit=QueryCount P.circuit ∧
      GateCount (guessProgram P E0).circuit=GateCount P.circuit+1 := by
  have hr := relabelCircuit_legality_resources coinAssoc (Coin.circuit P.circuit)
  exact ⟨hr.2.1.trans (Coin.resources P.circuit P.unitary).2.1,
    hr.2.2.1.trans (Coin.resources P.circuit P.unitary).2.2⟩

/-- The guessing program acceptance probability is the original acceptance probability plus half
the inconclusive outcome probability. -/
theorem guessProgram_probability (P : Program n W) (E0 : Finset (Space n W))
    (x : Fin n→Bool) :
    acceptProb (guessProgram P E0) x=
      acceptProb P x+MeasureProb (output P x) (E0∪P.accept)ᶜ/2 := by
  have hr := (run_relabelCircuit_readout coinAssoc
    (TensorGate (workspaceBitOracle (W:=W) (inputAt n x)) (1:Matrix Bool Bool ℂ))
    (Coin.circuit P.circuit) (TensorState (initial P) (Qatlib.Foundations.PureStateMath.Ket false))
    (Coin.event E0 P.accept)).2
  rw [coin_oracle,coin_initial,Coin.run] at hr
  exact hr.trans (Coin.event_mass _ _ _)

/-- Fair-coin guessing converts a weak zero-error program into a program whose acceptance
probability approximates `f` within one-quarter. -/
theorem zeroError_guess_error_quarter (P : Program n W) (E0 : Finset (Space n W))
    (f : (Fin n→Bool)→Bool) (h : ZeroError false P E0 f) :
    ∀x, |acceptProb (guessProgram P E0) x-(if f x then (1:ℝ) else 0)|≤1/4 := by
  intro x
  rw [guessProgram_probability]
  have hi := inconclusive_identity false P E0 f h x
  have hu := measureProb_nonneg (output P x) (E0∪P.accept)ᶜ
  have hc : (1:ℝ)/2≤MeasureProb (output P x) E0+acceptProb P x := (h.2 x).2.2
  rw [abs_le]
  cases hf : f x with
  | false =>
      have hz := (h.2 x).2.1 hf
      simp only [Bool.false_eq_true,ite_false]
      constructor <;> linarith
  | true =>
      have hz := (h.2 x).1 hf
      simp only [ite_true]
      constructor <;> linarith

/-- Fair-coin guessing converts a weak zero-error program into a one-third bounded-error
program. -/
theorem zeroError_guess_bounded (P : Program n W) (E0 : Finset (Space n W))
    (f : (Fin n→Bool)→Bool) (h : ZeroError false P E0 f) :
    Bounded (guessProgram P E0) f := by
  intro x
  exact (zeroError_guess_error_quarter P E0 f h x).trans (by norm_num)

/-- Weak zero-error feasibility implies bounded-error feasibility at the same query count. -/
theorem zeroErrorFeasible_bounded (f : (Fin n→Bool)→Bool) (t : ℕ)
    (h : ZeroErrorFeasible false f t) : BoundedFeasible f t := by
  obtain ⟨S,hS,dS,P,E0,hq,hp⟩ := h
  letI := hS
  letI := dS
  exact ⟨S×Bool,inferInstance,inferInstance,guessProgram P E0,
    (guessProgram_counts P E0).1.trans hq,zeroError_guess_bounded P E0 f hp⟩

/-- The minima satisfy bounded-error ≤ weak zero-error ≤ strict zero-error ≤ exact ≤ input
length. -/
theorem minimum_order_all (f : (Fin n→Bool)→Bool) :
    boundedMinimum f≤zeroErrorMinimum false f ∧
      zeroErrorMinimum false f≤zeroErrorMinimum true f ∧
      zeroErrorMinimum true f≤exactMinimum f ∧ exactMinimum f≤n :=
  ⟨boundedMinimum_le f _ (zeroErrorFeasible_bounded f _ (zeroErrorMinimum_attained false f)),
    (zeroError_minima_order f).1,(zeroError_minima_order f).2,(minima_upper_and_order f).2⟩

/-- A program with zero oracle queries has the same output state on every input. -/
theorem query_free_output (P : Program n W) (hq : QueryCount P.circuit=0)
    (x y : Fin n→Bool) : output P x=output P y :=
  run_eq_of_queryCount_eq_zero _ _ P.circuit hq (initial P)

/-- A bounded-error program for a function taking both false and true values uses at least one
query. -/
theorem nonconstant_program_positive (P : Program n W) (f : (Fin n→Bool)→Bool)
    (h : Bounded P f) (x y : Fin n→Bool) (hx : f x=false) (hy : f y=true) :
    1≤QueryCount P.circuit := by
  by_contra hq
  have hz : QueryCount P.circuit=0 := by omega
  have hp : acceptProb P x=acceptProb P y :=
    congrArg (fun ψ => MeasureProb ψ P.accept) (query_free_output P hz x y)
  have h0 := (abs_le.mp (h x)).2
  have h1 := (abs_le.mp (h y)).1
  simp only [hx,Bool.false_eq_true,ite_false,sub_zero] at h0
  simp only [hy,ite_true] at h1
  linarith

/-- For a function taking both Boolean values, the bounded-error, both zero-error, and exact
query minima are all at least one. -/
theorem nonconstant_minima_positive (f : (Fin n→Bool)→Bool)
    (x y : Fin n→Bool) (hx : f x=false) (hy : f y=true) :
    1≤boundedMinimum f ∧ 1≤zeroErrorMinimum false f ∧
      1≤zeroErrorMinimum true f ∧ 1≤exactMinimum f := by
  obtain ⟨S,hS,dS,P,hq,hp⟩ := boundedMinimum_attained f
  letI := hS
  letI := dS
  have hb : 1≤boundedMinimum f := hq ▸ nonconstant_program_positive P f hp x y hx hy
  have ho := minimum_order_all f
  exact ⟨hb,hb.trans ho.1,(hb.trans ho.1).trans ho.2.1,
    ((hb.trans ho.1).trans ho.2.1).trans ho.2.2.1⟩

/-- For zero-length inputs, the exact, bounded-error, and both zero-error query minima are all
zero. -/
theorem empty_minima (f : (Fin 0→Bool)→Bool) :
    exactMinimum f=0 ∧ boundedMinimum f=0 ∧
      zeroErrorMinimum false f=0 ∧ zeroErrorMinimum true f=0 := by
  rw [empty_function_constant f]
  exact ⟨(constant_minima _).1,(constant_minima _).2,
    constant_zeroError_minimum false _,constant_zeroError_minimum true _⟩

/-- Both zero-error minima are attained and satisfy the full ordering with the bounded-error and
exact minima and the input length. -/
theorem frontier2 (f : (Fin n→Bool)→Bool) :
    ZeroErrorFeasible false f (zeroErrorMinimum false f) ∧
      ZeroErrorFeasible true f (zeroErrorMinimum true f) ∧
      boundedMinimum f≤zeroErrorMinimum false f ∧
      zeroErrorMinimum false f≤zeroErrorMinimum true f ∧
      zeroErrorMinimum true f≤exactMinimum f ∧ exactMinimum f≤n :=
  ⟨zeroErrorMinimum_attained false f,zeroErrorMinimum_attained true f,minimum_order_all f⟩

end
end Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
