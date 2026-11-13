/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.MajorityAndRestrictionDegree
import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote

/-!
# Majority lower bounds by restriction

This module constructs an explicit oracle restriction compiler in `Restrict` and lifts it to
Boolean query programs through `ProgramRestriction.compileProgram`. The compiler substitutes
selected input coordinates and fixes inactive coordinates to false while preserving query count
and output event probabilities. The padding map `padding` turns majority on `2*k+1` bits into
AND on `k+1` bits, allowing the amplitude polynomial lower bound for AND to yield exact and
zero-error majority lower bounds, using the polynomial approach of [BealsEtAl2001].

## Main statements

* `Restrict.query_simulation` and `Restrict.run_compile` establish oracle and circuit
  simulation.
* `ProgramRestriction.counts_compile` records the unchanged query count and the added routing
  and preparation gates.
* `ProgramRestriction.exact_compile` and `ProgramRestriction.zeroError_compile` preserve the
  corresponding correctness conditions under restriction.
* `majority_padding` identifies padded majority with AND, and `and_zeroError_lower` gives the
  AND query lower bound.
* `majority_zeroError_lower`, `majority_exact_lower`, and `majority_minima_lower` give the lower
  bound `k+1` for majority on `2*k+1` bits.
* `frontier1` packages the program-level and minimum query bounds.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.Amplification
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs.Coin
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.MajorityAndRestriction
open Qatlib Matrix
open scoped Classical BigOperators

namespace Restrict
variable {I J W : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
/-- The simulated query register `(J × Bool)` together with its workspace `W`. -/
abbrev Data (J W : Type) := (J × Bool) × W
/-- The physical query register `(I × Bool)` together with the simulated register and workspace
`Data J W`. -/
abbrev Full (I J W : Type) := (I × Bool) × Data J W

/-- Routes the physical address by swapping `r` with `slot j`, and swaps the physical and
simulated response bits exactly when `active j` is true. The simulated address and workspace
are preserved. -/
def route (r : I) (slot : J → I) (active : J → Bool) : Full I J W → Full I J W :=
  fun p => ((Equiv.swap r (slot p.2.1.1) p.1.1,
    if active p.2.1.1 then p.2.1.2 else p.1.2),
    ((p.2.1.1,if active p.2.1.1 then p.1.2 else p.2.1.2),p.2.2))

omit [Fintype I] [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W] in

/-- Applying `route r slot active` twice restores every basis index. -/
theorem route_involutive (r : I) (slot : J → I) (active : J → Bool) :
    Function.Involutive (route (W := W) r slot active) := by
  intro ⟨⟨i,a⟩,⟨⟨j,b⟩,w⟩⟩
  cases h : active j <;> simp [route,h]

/-- The permutation matrix implementing the basis routing map `route`. -/
def routeGate (r : I) (slot : J → I) (active : J → Bool) :
    Matrix (Full I J W) (Full I J W) ℂ := permMatrix (route r slot active)

/-- The routing permutation matrix `routeGate` is unitary. -/
theorem routeGate_unitary (r : I) (slot : J → I) (active : J → Bool) :
    routeGate (W := W) r slot active ∈ Matrix.unitaryGroup (Full I J W) ℂ :=
  permMatrix_unitary (route_involutive r slot active)

/-- Embeds a simulated state by adjoining physical address `r` and a response qubit in the plus
state. -/
def embedded (r : I) (ψ : QState (Data J W)) : QState (Full I J W) :=
  TensorState (TensorState (Ket r) Plus) ψ

/-- Substitutes `x (slot j)` at active simulated addresses and fixes every inactive coordinate
to false. -/
def restrictedInput (slot : J → I) (active : J → Bool) (x : I → Bool) : J → Bool :=
  fun j => if active j then x (slot j) else false

/-- Conjugating one physical query by the routing gate simulates a query to `restrictedInput
slot active x` on an embedded state. The adjoined address and plus-state response qubit are
restored. -/
theorem query_simulation (r : I) (slot : J → I) (active : J → Bool)
    (x : I → Bool) (ψ : QState (Data J W)) :
    ApplyGate (routeGate r slot active)
      (ApplyGate (TensorGate (BitOracleOn x) 1)
        (ApplyGate (routeGate r slot active) (embedded r ψ))) =
    embedded r (ApplyGate (TensorGate (BitOracleOn (restrictedInput slot active x)) 1) ψ) := by
  funext p
  obtain ⟨⟨i,a⟩,⟨⟨j,b⟩,w⟩⟩ := p
  simp only [routeGate,applyGate_permMatrix (route_involutive r slot active),
    applyGate_bitOracleOn_workspace]
  simp only [embedded,TensorState,applyGate_bitOracleOn_workspace,route,flipWorkspace]
  by_cases hi : i = r
  · subst i
    cases h : active j <;>
      simp [restrictedInput,h,Plus,Qatlib.Foundations.PureStateMath.Ket,Hadamard]
  · cases h : active j <;>
      simp [Qatlib.Foundations.PureStateMath.Ket,hi]

/-- Extending a simulated gate by the identity on the physical query register commutes with
`embedded`. -/
theorem gate_simulation (r : I) (U : Matrix (Data J W) (Data J W) ℂ)
    (ψ : QState (Data J W)) :
    ApplyGate (TensorGate (1 : Matrix (I×Bool) (I×Bool) ℂ) U) (embedded r ψ) =
      embedded r (ApplyGate U ψ) := by
  rw [embedded,applyGate_tensorGate,applyGate_one]
  rfl

/-- Compiles a simulated circuit by extending its gates with an identity and surrounding each
physical query with two routing gates. -/
def compile (r : I) (slot : J → I) (active : J → Bool) :
    Circuit (Data J W) → Circuit (Full I J W)
  | [] => []
  | .gate U :: C => .gate (TensorGate 1 U) :: compile r slot active C
  | .query :: C => .gate (routeGate r slot active) :: .query ::
      .gate (routeGate r slot active) :: compile r slot active C

/-- Running the compiled circuit on an embedded state reproduces the embedded result of the
original circuit on the restricted input. -/
theorem run_compile (r : I) (slot : J → I) (active : J → Bool)
    (C : Circuit (Data J W)) (x : I → Bool) (ψ : QState (Data J W)) :
    Run (TensorGate (BitOracleOn x) 1) (compile r slot active C) (embedded r ψ) =
      embedded r (Run (TensorGate (BitOracleOn (restrictedInput slot active x)) 1) C ψ) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simp only [compile,run_gate,gate_simulation,ih]
    | query => simp only [compile,run_gate,run_query,query_simulation,ih]

omit [Fintype I] [Fintype J] [Fintype W] in

/-- Restriction compilation preserves the circuit's query count. -/
theorem compile_queries (r : I) (slot : J → I) (active : J → Bool)
    (C : Circuit (Data J W)) : QueryCount (compile r slot active C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [compile,ih]

omit [Fintype I] [Fintype J] [Fintype W] in

/-- Restriction compilation adds exactly two gates for each original query. -/
theorem compile_gates (r : I) (slot : J → I) (active : J → Bool)
    (C : Circuit (Data J W)) :
    GateCount (compile r slot active C) = GateCount C + 2*QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [compile,ih] <;> omega

/-- Restriction compilation preserves the property that every circuit gate is unitary. -/
theorem compile_unitary (r : I) (slot : J → I) (active : J → Bool)
    (C : Circuit (Data J W)) (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (compile r slot active C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [isUnitaryCircuit_gate] at hC
      exact (isUnitaryCircuit_gate _ _).mpr
        ⟨tensorGate_unitary (Submonoid.one_mem _) hC.1,ih hC.2⟩
    | query =>
      exact (isUnitaryCircuit_gate _ _).mpr ⟨routeGate_unitary r slot active,
        (isUnitaryCircuit_query _).mpr ((isUnitaryCircuit_gate _ _).mpr
          ⟨routeGate_unitary r slot active,ih ((isUnitaryCircuit_query _).mp hC)⟩)⟩

/-- An event on the simulated registers has the same measurement probability after embedding,
when the physical query register is unrestricted. -/
theorem embedded_measure (r : I) (ψ : QState (Data J W)) (E : Finset (Data J W)) :
    MeasureProb (embedded r ψ) (Finset.univ ×ˢ E) = MeasureProb ψ E :=
  measureProb_tensorState_right (normalized_tensorState (normalized_ket r) normalized_plus) ψ E

/-- Applies a Hadamard gate to the physical response qubit, with identity gates on the physical
address and simulated data. -/
def prepare : Matrix (Full I J W) (Full I J W) ℂ :=
  TensorGate (TensorGate (1 : Matrix I I ℂ) Hadamard) 1

/-- The preparation gate `prepare` is unitary. -/
theorem prepare_unitary : prepare (I := I) (J := J) (W := W) ∈
    Matrix.unitaryGroup (Full I J W) ℂ :=
  tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary)
    (Submonoid.one_mem _)

/-- The preparation gate turns a physical response qubit initialized to false into the
plus-state ancilla used by `embedded`. -/
theorem prepare_clean (r : I) (ψ : QState (Data J W)) :
    ApplyGate prepare (TensorState (TensorState (Qatlib.Foundations.PureStateMath.Ket r)
      (Qatlib.Foundations.PureStateMath.Ket false)) ψ) = embedded r ψ := by
  rw [prepare,applyGate_tensorGate,applyGate_tensorGate,applyGate_one,
    applyGate_one,applyGate_hadamard_ket_false]
  rfl

end Restrict

namespace ProgramRestriction
variable {n m : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- Compiles a Boolean query program to run on inputs substituted by `slot` and `active`,
adjoining registers for the simulated query. It prepends the ancilla preparation gate and
lifts the acceptance event over the new physical query register. -/
def compileProgram (P : Program (n+1) W) (slot : Fin (n+1) → Fin (m+1))
    (active : Fin (n+1) → Bool) : Program (m+1) (Restrict.Data (Fin (n+1)) W) where
  circuit := .gate Restrict.prepare ::
    Restrict.compile (0 : Fin (m+1)) slot active P.circuit
  unitary := (isUnitaryCircuit_gate _ _).mpr
    ⟨Restrict.prepare_unitary,Restrict.compile_unitary (0 : Fin (m+1)) slot active P.circuit P.unitary⟩
  clean := (((0 : Fin (n+1)),false),P.clean)
  accept := Finset.univ ×ˢ P.accept

/-- The compiled program's output is the embedded output of the original program on the
restricted input, with physical address zero. -/
theorem output_compile (P : Program (n+1) W) (slot : Fin (n+1) → Fin (m+1))
    (active : Fin (n+1) → Bool) (x : Fin (m+1) → Bool) :
    output (compileProgram P slot active) x =
      Restrict.embedded (0 : Fin (m+1)) (output P (Restrict.restrictedInput slot active x)) := by
  unfold output
  change Run (TensorGate (BitOracleOn x) 1)
    (.gate Restrict.prepare :: Restrict.compile (0 : Fin (m+1)) slot active P.circuit)
    (Qatlib.Foundations.PureStateMath.Ket (((0 : Fin (m+1)),false),(((0 : Fin (n+1)),false),P.clean))) = _
  rw [run_gate,← tensorState_ket_ket ((0 : Fin (m+1)),false) (((0 : Fin (n+1)),false),P.clean),
    ← tensorState_ket_ket (0 : Fin (m+1)) false,Restrict.prepare_clean,
    Restrict.run_compile]
  rfl

/-- Compiling a program preserves the probability of every output event lifted over the physical
query register. -/
theorem event_compile (P : Program (n+1) W) (slot : Fin (n+1) → Fin (m+1))
    (active : Fin (n+1) → Bool) (x : Fin (m+1) → Bool)
    (E : Finset (Space (n+1) W)) :
    MeasureProb (output (compileProgram P slot active) x) (Finset.univ ×ˢ E) =
      MeasureProb (output P (Restrict.restrictedInput slot active x)) E := by
  rw [output_compile]
  exact Restrict.embedded_measure (I := Fin (m+1)) (J := Fin (n+1))
    (0 : Fin (m+1)) (output P (Restrict.restrictedInput slot active x)) E

/-- The compiled program accepts with the same probability as the original program evaluated on
the restricted input. -/
theorem accept_compile (P : Program (n+1) W) (slot : Fin (n+1) → Fin (m+1))
    (active : Fin (n+1) → Bool) (x : Fin (m+1) → Bool) :
    acceptProb (compileProgram P slot active) x =
      acceptProb P (Restrict.restrictedInput slot active x) :=
  event_compile P slot active x P.accept

/-- Program restriction preserves query count and adds two routing gates per query together with
one preparation gate. -/
theorem counts_compile (P : Program (n+1) W) (slot : Fin (n+1) → Fin (m+1))
    (active : Fin (n+1) → Bool) :
    QueryCount (compileProgram P slot active).circuit = QueryCount P.circuit ∧
      GateCount (compileProgram P slot active).circuit =
        GateCount P.circuit + 2*QueryCount P.circuit + 1 := by
  constructor
  · exact Restrict.compile_queries (I := Fin (m+1)) (J := Fin (n+1)) _ slot active P.circuit
  · have h := Restrict.compile_gates (I := Fin (m+1)) (J := Fin (n+1))
      (0 : Fin (m+1)) slot active P.circuit
    change GateCount (Restrict.compile (0 : Fin (m+1)) slot active P.circuit) + 1 = _
    rw [h]

/-- An exact program for `f` compiles to an exact program for `f` composed with
`restrictedInput`. -/
theorem exact_compile (P : Program (n+1) W) (slot : Fin (n+1) → Fin (m+1))
    (active : Fin (n+1) → Bool) (f : (Fin (n+1) → Bool) → Bool) (h : Exact P f) :
    Exact (compileProgram P slot active) (fun x => f (Restrict.restrictedInput slot active x)) := by
  intro x
  rw [accept_compile,h]

/-- Program restriction preserves `ZeroError strict` for the restricted function, lifting the
zero-output event over the physical query register. -/
theorem zeroError_compile (strict : Bool) (P : Program (n+1) W)
    (slot : Fin (n+1) → Fin (m+1)) (active : Fin (n+1) → Bool)
    (E0 : Finset (Space (n+1) W)) (f : (Fin (n+1) → Bool) → Bool)
    (h : ZeroError strict P E0 f) :
    ZeroError strict (compileProgram P slot active) (Finset.univ ×ˢ E0)
      (fun x => f (Restrict.restrictedInput slot active x)) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    exact Finset.disjoint_left.mp h.1 (Finset.mem_product.mp hp).2
      (Finset.mem_product.mp hq).2
  · intro x
    simpa only [event_compile,accept_compile] using! h.2 (Restrict.restrictedInput slot active x)

end ProgramRestriction

/-- Marks the first `k+1` coordinates of a `2*k+1`-bit input as active. -/
def majorityActive (k : ℕ) (j : Fin (k+k+1)) : Bool := decide (j.val < k+1)

/-- Maps each of the first `k+1` padded coordinates to the corresponding input coordinate and
maps the remaining coordinates to zero. -/
def majoritySlot (k : ℕ) (j : Fin (k+k+1)) : Fin (k+1) :=
  if h : j.val < k+1 then ⟨j.val,h⟩ else 0

/-- Extends a `k+1`-bit input to `2*k+1` bits by keeping the first `k+1` coordinates and
appending `k` false bits. -/
def padding (k : ℕ) (x : Fin (k+1) → Bool) : Fin (k+k+1) → Bool :=
  Restrict.restrictedInput (majoritySlot k) (majorityActive k) x

/-- Every true bit in `padding k x` lies among its first `k+1` coordinates. -/
theorem padding_true_active (k : ℕ) (x : Fin (k+1) → Bool) (j : Fin (k+k+1))
    (h : padding k x j = true) : j.val < k+1 := by
  by_contra hn
  simp [padding,Restrict.restrictedInput,majorityActive,hn] at h

/-- Appending false bits through `padding` preserves the number of true coordinates. -/
theorem padding_count (k : ℕ) (x : Fin (k+1) → Bool) :
    MajorityCount (padding k x) = MajorityCount x := by
  unfold MajorityCount
  apply Finset.card_bij (fun j hj =>
    (⟨j.val,padding_true_active k x j (Finset.mem_filter.mp hj).2⟩ : Fin (k+1)))
  · intro j hj
    have ha := padding_true_active k x j (Finset.mem_filter.mp hj).2
    have hx := (Finset.mem_filter.mp hj).2
    simpa [padding,Restrict.restrictedInput,majorityActive,majoritySlot,ha] using! hx
  · intro i hi j hj hij
    exact Fin.ext (congrArg (fun q : Fin (k+1) => q.val) hij)
  · intro i hi
    let j : Fin (k+k+1) := ⟨i.val,by omega⟩
    have ha : j.val < k+1 := i.isLt
    have hmem : j ∈ Finset.univ.filter (fun j => padding k x j = true) := by
      have hx := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr ⟨Finset.mem_univ j,?_⟩
      simpa [padding,Restrict.restrictedInput,majorityActive,majoritySlot,ha,j,i.isLt] using! hx
    exact ⟨j,hmem,Fin.ext rfl⟩

/-- Majority of the padded `2*k+1`-bit input is true exactly when all `k+1` original input bits
are true. -/
theorem majority_padding (k : ℕ) (x : Fin (k+1) → Bool) :
    MajorityBit (padding k x) = decide (∀ i, x i=true) := by
  have hdiv : (k+k+1)/2 = k := by omega
  simp only [MajorityBit,hdiv,padding_count]
  congr 1
  apply propext
  constructor
  · intro hcount
    have hle : MajorityCount x ≤ k+1 := by
      exact (Finset.card_filter_le _ _).trans (by simp)
    have heq : (Finset.univ.filter fun i => x i=true).card =
        (Finset.univ : Finset (Fin (k+1))).card := by
      change MajorityCount x = _
      simp only [Finset.card_univ,Fintype.card_fin]
      omega
    exact fun i => Finset.card_filter_eq_iff.mp heq i (Finset.mem_univ i)
  · intro hx
    simp [MajorityCount,hx]

/-- Every program satisfying `ZeroError strict` for AND on `n` bits uses at least `n` queries.
The proof applies the amplitude polynomial bound `sameCircuit_and_lower` in the polynomial
method of [BealsEtAl2001]. -/
theorem and_zeroError_lower {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (strict : Bool) (P : Program n W) (E0 : Finset (Space n W))
    (h : ZeroError strict P E0 (fun x => decide (∀ i,x i=true))) : n ≤ QueryCount P.circuit := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ m =>
    have hw : ZeroError false P E0 (fun x => decide (∀ i,x i=true)) := by
      cases strict with
      | false => exact h
      | true => exact zeroError_strict_weak P E0 (fun x => decide (∀ i,x i=true)) h
    have hno (x : Fin (m+1) → Bool) (hx : ∃ i,x i=false) : acceptProb P x=0 := by
      apply (hw.2 x).2.1
      obtain ⟨i,hi⟩ := hx
      have hn : ¬∀ i,x i=true := fun ha => by
        have hh := ha i
        rw [hi] at hh
        exact Bool.false_ne_true hh
      simp [hn]
    have hz : MeasureProb (output P (fun _ => true)) E0=0 :=
      (hw.2 (fun _ => true)).1 (by simp )
    have hp : 0 < acceptProb P (fun _ => true) := by
      have hq := (hw.2 (fun _ => true)).2.2
      simp only [Bool.false_eq_true,ite_false,hz,zero_add] at hq
      linarith
    have hl :=
        Qatlib.Concepts.QueryComplexity.DegreeMethod.sameCircuit_and_lower (I:=Fin (m+1))
        (W:=W) P.circuit (initial P) P.accept hno hp
    simpa only [Fintype.card_fin] using! hl

variable {W : Type} [Fintype W] [DecidableEq W]

/-- Restricting a zero-error majority program through `majoritySlot` and `majorityActive` yields
a zero-error program for AND on `k+1` bits. -/
theorem majority_zeroError_compile (k : ℕ) (strict : Bool) (P : Program (k+k+1) W)
    (E0 : Finset (Space (k+k+1) W)) (h : ZeroError strict P E0 MajorityBit) :
    ZeroError strict (ProgramRestriction.compileProgram P (majoritySlot k) (majorityActive k))
      (Finset.univ ×ˢ E0) (fun x => decide (∀ i, x i=true)) := by
  have ht := ProgramRestriction.zeroError_compile strict P (majoritySlot k) (majorityActive k)
    E0 MajorityBit h
  change ZeroError strict _ _ (fun x => MajorityBit (padding k x)) at ht
  simpa only [majority_padding] using! ht

/-- Every program satisfying either zero-error convention for majority on `2*k+1` bits uses at
least `k+1` queries. -/
theorem majority_zeroError_lower (k : ℕ) (strict : Bool) (P : Program (k+k+1) W)
    (E0 : Finset (Space (k+k+1) W)) (h : ZeroError strict P E0 MajorityBit) :
    k+1 ≤ QueryCount P.circuit := by
  have ht := and_zeroError_lower strict
    (ProgramRestriction.compileProgram P (majoritySlot k) (majorityActive k))
    (Finset.univ ×ˢ E0) (majority_zeroError_compile k strict P E0 h)
  rwa [(ProgramRestriction.counts_compile P (majoritySlot k) (majorityActive k)).1] at ht

/-- Every exact program for majority on `2*k+1` bits uses at least `k+1` queries. -/
theorem majority_exact_lower (k : ℕ) (P : Program (k+k+1) W) (h : Exact P MajorityBit) :
    k+1 ≤ QueryCount P.circuit :=
  majority_zeroError_lower k false P P.acceptᶜ (exact_zeroError false P MajorityBit h)

/-- Every feasible zero-error query count for majority on `2*k+1` bits is at least `k+1`, for
either value of `strict`. -/
theorem majority_feasible_lower (k : ℕ) (strict : Bool) (t : ℕ)
    (h : ZeroErrorFeasible strict (@MajorityBit (k+k+1)) t) : k+1 ≤ t := by
  obtain ⟨S,hS,dS,P,E0,hq,hp⟩ := h
  letI := hS
  letI := dS
  rw [← hq]
  exact majority_zeroError_lower k strict P E0 hp

/-- The weak zero-error, strict zero-error, and exact query minima for majority on `2*k+1` bits
are all at least `k+1`. -/
theorem majority_minima_lower (k : ℕ) :
    k+1 ≤ zeroErrorMinimum false (@MajorityBit (k+k+1)) ∧
    k+1 ≤ zeroErrorMinimum true (@MajorityBit (k+k+1)) ∧
    k+1 ≤ exactMinimum (@MajorityBit (k+k+1)) := by
  refine ⟨majority_feasible_lower k false _ (zeroErrorMinimum_attained false _),
    majority_feasible_lower k true _ (zeroErrorMinimum_attained true _),?_⟩
  exact (majority_feasible_lower k true _ (zeroErrorMinimum_attained true _)).trans
    (zeroError_minima_order _).2

/-- Collects the exact and zero-error program lower bounds for odd majority together with the
corresponding lower bounds on all three query minima. -/
theorem frontier1 (k : ℕ) :
    (∀ (P : Program (k+k+1) W), Exact P MajorityBit → k+1 ≤ QueryCount P.circuit) ∧
    (∀ (strict : Bool) (P : Program (k+k+1) W) (E0 : Finset (Space (k+k+1) W)),
      ZeroError strict P E0 MajorityBit → k+1 ≤ QueryCount P.circuit) ∧
    k+1 ≤ zeroErrorMinimum false (@MajorityBit (k+k+1)) ∧
    k+1 ≤ zeroErrorMinimum true (@MajorityBit (k+k+1)) ∧
    k+1 ≤ exactMinimum (@MajorityBit (k+k+1)) :=
  ⟨fun P h => majority_exact_lower k P h,
    fun strict P E0 h => majority_zeroError_lower k strict P E0 h,majority_minima_lower k⟩

end Qatlib.Concepts.QueryComplexity.DegreeMethod.MajorityAndRestriction
