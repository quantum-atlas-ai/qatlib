/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.CheatSheet15.BornBaseline.CheatSheetQuantumUpperBoundStat

public import Qatlib.Concepts.HspRecovery.RecordExtract.ExecutionSemantics
public import Qatlib.Concepts.QueryComplexity.Amplification.ParallelCopies
public import Qatlib.Concepts.QueryComplexity.Amplification.SubroutineCleaning
public import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
public import Qatlib.Concepts.BlockEncoding.LinearCombination
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.Amplification
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Papers.CheatSheet15.BornBaseline

/-- For a certifying verifier, every block of an accepted cheat-sheet input lies in the domain
and its selected certificate's first bit equals the block's function value. -/
theorem cheatSheetAccepted_in_domain {c M κ : ℕ} (hκ : 0 < κ)
    (dom : (Fin M → Bool) → Prop) (g : (Fin M → Bool) → Bool)
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool)
    (hcert : IsCertifying M κ hκ dom g φ) (z : CheatSheetIndex c M κ → Bool)
    (hz : cheatSheetFun (c := c) g φ z = true) :
    ∀ i : Fin c, dom (cheatBlock z i) ∧
      cheatCert z (sheetIndex fun j => g (cheatBlock z j)) i ⟨0, hκ⟩ = g (cheatBlock z i) := by
  have hh : ∀ i : Fin c,
      φ (cheatBlock z i) (cheatCert z (sheetIndex fun j => g (cheatBlock z j)) i) = true :=
    of_decide_eq_true hz
  intro i
  exact hcert.1 _ _ (hh i)

/-- For a certifying verifier, a cheat-sheet input with any block outside the domain is
rejected. -/
theorem cheatSheetOutsideDomain_rejects {c M κ : ℕ} (hκ : 0 < κ)
    (dom : (Fin M → Bool) → Prop) (g : (Fin M → Bool) → Bool)
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool)
    (hcert : IsCertifying M κ hκ dom g φ) (z : CheatSheetIndex c M κ → Bool)
    (i : Fin c) (hi : ¬ dom (cheatBlock z i)) :
    cheatSheetFun (c := c) g φ z = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact hi (cheatSheetAccepted_in_domain hκ dom g φ hcert z h i).1

set_option synthInstance.maxSize 100000 in

/-- For positive block count, normalized block and verifier states ensure the existence of a
normalized state in the combined cheat-sheet workspace. -/
theorem cheatSheetWorkspace_has_state (c M κ : ℕ) (hc : 0 < c)
    (Wg Wφ : Type) [Fintype Wg] [DecidableEq Wg] [Fintype Wφ] [DecidableEq Wφ]
    (ψg : Qatlib.Foundations.PureStateMath.QState ((Fin M × Bool) × Wg))
    (ψφ : Qatlib.Foundations.PureStateMath.QState (((Fin M ⊕ Fin κ) × Bool) × Wφ))
    (hg : Qatlib.Foundations.PureStateMath.Normalized ψg) (hφ : Qatlib.Foundations.PureStateMath.Normalized ψφ) :
    ∃ ψ₀ : Qatlib.Foundations.PureStateMath.QState ((CheatSheetIndex c M κ × Bool) ×
        ((Fin c → ((Fin M × Bool) × Wg)) ×
            (Fin c → (((Fin M ⊕ Fin κ) × Bool) × Wφ)) × (Fin c → Bool) × Bool)),
      Qatlib.Foundations.PureStateMath.Normalized ψ₀ := by
  classical
  have hng : Nonempty ((Fin M × Bool) × Wg) := by
    by_contra h
    have : IsEmpty ((Fin M × Bool) × Wg) := not_nonempty_iff.mp h
    simp [Qatlib.Foundations.PureStateMath.Normalized] at hg
  have hnφ : Nonempty (((Fin M ⊕ Fin κ) × Bool) × Wφ) := by
    by_contra h
    have : IsEmpty (((Fin M ⊕ Fin κ) × Bool) × Wφ) := not_nonempty_iff.mp h
    simp [Qatlib.Foundations.PureStateMath.Normalized] at hφ
  obtain ⟨⟨m, b⟩, wg⟩ := Classical.choice hng
  obtain ⟨_, wφ⟩ := Classical.choice hnφ
  let i : Fin c := ⟨0, hc⟩
  let v : ((CheatSheetIndex c M κ × Bool) ×
      ((Fin c → ((Fin M × Bool) × Wg)) ×
            (Fin c → (((Fin M ⊕ Fin κ) × Bool) × Wφ)) × (Fin c → Bool) × Bool)) :=
    ((Sum.inl (i, m), b), (fun _ => ((m, b), wg)),
      (fun _ => ((Sum.inl m, false), wφ)), (fun _ => false), false)
  exact ⟨Qatlib.Foundations.PureStateMath.Ket v,
      Qatlib.Foundations.PureStateMath.normalized_ket v⟩

open Matrix
open scoped Classical BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

section SharedPortRouting
variable {Q J W R : Type} [Fintype Q] [DecidableEq Q] [Fintype J] [DecidableEq J]
  [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]

/-- The permutation matrix of a permutation sends a basis ket to the ket at the permuted index. -/
private theorem permutation_on_ket {H : Type} [Fintype H] [DecidableEq H]
    (σ : Equiv.Perm H) (a : H) : ApplyGate (permMatrix σ) (Ket a) = Ket (σ a) := by
  funext u
  simp only [ApplyGate, mulVec_ket_apply, permMatrix, Matrix.of_apply, Ket]

/-- The workspace bit oracle XORs the queried oracle bit into the target of a basis ket. -/
private theorem workspace_on_ket (z : Q → Bool) (q : Q) (b : Bool) (w : W) :
    ApplyGate (workspaceBitOracle z) (Ket ((q, b), w)) = Ket ((q, b ^^ z q), w) := by
  rw [← tensorState_ket_ket, workspaceBitOracle, applyGate_tensorGate,
    applyGate_bitOracleOn_ket, applyGate_one, tensorState_ket_ket]

private def localXor (e : R → J ↪ Q) (z : Q → Bool)
    (a : ((J × Bool) × W) × R) : ((J × Bool) × W) × R :=
  (((a.1.1.1, a.1.1.2 ^^ z (e a.2 a.1.1.1)), a.1.2), a.2)

/-- The local XOR transformation is involutive. -/
private theorem localXor_involutive (e : R → J ↪ Q) (z : Q → Bool) :
    Function.Involutive (localXor (W := W) e z) := by
  rintro ⟨⟨⟨j, b⟩, w⟩, r⟩
  simp [localXor]

private noncomputable def localOracle (e : R → J ↪ Q) (z : Q → Bool) :
    Matrix (((J × Bool) × W) × R) (((J × Bool) × W) × R) ℂ :=
  permMatrix (localXor e z)

private def readyBasis (d : Q × Bool) (a : ((J × Bool) × W) × R) := (d, a)
private def queryBasis (q₀ : J × Bool) (e : R → J ↪ Q)
    (a : ((J × Bool) × W) × R) : (Q × Bool) × (((J × Bool) × W) × R) :=
  ((e a.2 a.1.1.1, a.1.1.2), ((q₀, a.1.2), a.2))

/-- For a fixed bus value, `readyBasis` is injective. -/
private theorem readyBasis_injective (d : Q × Bool) :
    Function.Injective (readyBasis (W := W) (R := R) (J := J) d) := by
  intro a b h
  exact congrArg Prod.snd h

/-- For a fixed local query value and embedding family, `queryBasis` is injective. -/
private theorem queryBasis_injective (q₀ : J × Bool) (e : R → J ↪ Q) :
    Function.Injective (queryBasis (W := W) q₀ e) := by
  rintro ⟨⟨⟨j, b⟩, w⟩, r⟩ ⟨⟨⟨j', b'⟩, w'⟩, r'⟩ h
  have hr : r = r' := congrArg (fun u => u.2.2) h
  subst r'
  have hj : j = j' := (e r).injective (congrArg (fun u => u.1.1) h)
  have hb : b = b' := congrArg (fun u => u.1.2) h
  have hw : w = w' := congrArg (fun u => u.2.1.2) h
  subst j'; subst b'; subst w'; rfl

private noncomputable def routePerm (d : Q × Bool) (q₀ : J × Bool) (e : R → J ↪ Q) :
    Equiv.Perm ((Q × Bool) × (((J × Bool) × W) × R)) :=
  Classical.choose (Equiv.Perm.exists_extending_pair (readyBasis d) (queryBasis q₀ e)
    (readyBasis_injective d) (queryBasis_injective q₀ e))

/-- The routing permutation sends each ready basis state to its corresponding query basis state. -/
private theorem routePerm_ready (d : Q × Bool) (q₀ : J × Bool) (e : R → J ↪ Q)
    (a : ((J × Bool) × W) × R) :
    routePerm d q₀ e (readyBasis d a) = queryBasis q₀ e a :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair (readyBasis d) (queryBasis q₀ e)
    (readyBasis_injective d) (queryBasis_injective q₀ e)) a

/-- Routing a basis state through one global query and then undoing the routing applies the
local oracle while restoring the bus ket. -/
private theorem routed_query_basis (d : Q × Bool) (q₀ : J × Bool) (e : R → J ↪ Q)
    (z : Q → Bool) (a : ((J × Bool) × W) × R) :
    ApplyGate (permMatrix (routePerm d q₀ e).symm)
      (ApplyGate (workspaceBitOracle z)
        (ApplyGate (permMatrix (routePerm d q₀ e)) (Ket (readyBasis d a)))) =
      TensorState (Ket d) (ApplyGate (localOracle e z) (Ket a)) := by
  rw [permutation_on_ket, routePerm_ready]
  rcases a with ⟨⟨⟨j, b⟩, w⟩, r⟩
  rw [show queryBasis q₀ e (((j, b), w), r) =
    ((e r j, b), ((q₀, w), r)) from rfl, workspace_on_ket, permutation_on_ket]
  have hinv := congrArg (routePerm (W := W) d q₀ e).symm
    (routePerm_ready d q₀ e (((j, b ^^ z (e r j)), w), r))
  simp only [Equiv.symm_apply_apply, queryBasis] at hinv
  rw [← hinv]
  rw [localOracle, applyGate_permMatrix_ket (localXor_involutive e z)]
  exact (tensorState_ket_ket d (localXor e z (((j, b), w), r))).symm

/-- A matrix identity on all basis states with a fixed bus value extends to arbitrary states
tensored with that bus ket. -/
private theorem transport_bus {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (d : B) (M : Matrix (B × A) (B × A) ℂ)
    (L : Matrix A A ℂ)
    (h : ∀ a : A, ApplyGate M (Ket (d, a)) = TensorState (Ket d) (ApplyGate L (Ket a)))
    (ψ : QState A) :
    ApplyGate M (TensorState (Ket d) ψ) = TensorState (Ket d) (ApplyGate L ψ) := by
  have hcol : ∀ (u : B × A) (a : A), M u (d, a) = Ket d u.1 * L u.2 a := by
    intro u a
    have hc := congrFun (h a) u
    simpa only [ApplyGate, mulVec_ket_apply, TensorState] using hc
  funext u
  simp only [ApplyGate, Matrix.mulVec, dotProduct, TensorState]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single d]
  · simp only [ket_self, one_mul]
    simp_rw [hcol]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  · intro b _ hb
    simp [Ket, hb]
  · simp

/-- A routing gate, one global query, and the inverse routing gate implement one local oracle
application while restoring the bus state. -/
theorem cheatSheet_single_query_routing (d : Q × Bool) (q₀ : J × Bool)
    (e : R → J ↪ Q) (z : Q → Bool) (ψ : QState (((J × Bool) × W) × R)) :
    let route : Equiv.Perm ((Q × Bool) × (((J × Bool) × W) × R)) :=
      Classical.choose (Equiv.Perm.exists_extending_pair
        (fun a : ((J × Bool) × W) × R => (d, a))
        (fun a : ((J × Bool) × W) × R =>
          ((e a.2 a.1.1.1, a.1.1.2), ((q₀, a.1.2), a.2)))
        (by intro a b h; exact congrArg Prod.snd h)
        (by
          rintro ⟨⟨⟨j, b⟩, w⟩, r⟩ ⟨⟨⟨j', b'⟩, w'⟩, r'⟩ h
          have hr : r = r' := congrArg (fun u => u.2.2) h
          subst r'
          have hj : j = j' := (e r).injective (congrArg (fun u => u.1.1) h)
          have hb : b = b' := congrArg (fun u => u.1.2) h
          have hw : w = w' := congrArg (fun u => u.2.1.2) h
          subst j'; subst b'; subst w'; rfl))
    Run (workspaceBitOracle z)
      [Step.gate (permMatrix route), Step.query, Step.gate (permMatrix route.symm)]
      (TensorState (Ket d) ψ) =
      TensorState (Ket d) (ApplyGate (permMatrix (fun a : ((J × Bool) × W) × R =>
        (((a.1.1.1, a.1.1.2 ^^ z (e a.2 a.1.1.1)), a.1.2), a.2))) ψ) := by
  change Run (workspaceBitOracle z)
    [Step.gate (permMatrix (routePerm d q₀ e)), Step.query,
      Step.gate (permMatrix (routePerm d q₀ e).symm)] (TensorState (Ket d) ψ) =
    TensorState (Ket d) (ApplyGate (localOracle e z) ψ)
  have ht := transport_bus d
    (permMatrix (routePerm d q₀ e).symm * workspaceBitOracle z * permMatrix (routePerm d q₀ e))
    (localOracle e z) (fun a => by
      rw [applyGate_mul, applyGate_mul]
      exact routed_query_basis d q₀ e z a) ψ
  simpa only [Run, ← applyGate_mul, Matrix.mul_assoc] using ht

private noncomputable def localWord : Circuit ((J × Bool) × W) → Circuit (((J × Bool) × W) × R)
  | [] => []
  | Step.gate U :: C => Step.gate (TensorGate U 1) :: localWord C
  | Step.query :: C => Step.query :: localWord C

private noncomputable def routedWord (d : Q × Bool) (q₀ : J × Bool) (e : R → J ↪ Q) :
    Circuit ((J × Bool) × W) → Circuit ((Q × Bool) × (((J × Bool) × W) × R))
  | [] => []
  | Step.gate U :: C => Step.gate (TensorGate 1 (TensorGate U 1)) :: routedWord d q₀ e C
  | Step.query :: C => Step.gate (permMatrix (routePerm d q₀ e)) :: Step.query ::
      Step.gate (permMatrix (routePerm d q₀ e).symm) :: routedWord d q₀ e C

/-- Routing a unitary circuit produces a unitary circuit. -/
private theorem routedWord_unitary (d : Q × Bool) (q₀ : J × Bool) (e : R → J ↪ Q)
    (C : Circuit ((J × Bool) × W)) (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (routedWord d q₀ e C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
    have htail : IsUnitaryCircuit C := fun U hU => hC U (List.mem_cons_of_mem _ hU)
    cases s with
    | gate U =>
      exact (isUnitaryCircuit_gate _ _).mpr
        ⟨tensorGate_unitary (Submonoid.one_mem _) (tensorGate_unitary
          (hC U List.mem_cons_self) (Submonoid.one_mem _)), ih htail⟩
    | query =>
      exact (isUnitaryCircuit_gate _ _).mpr
        ⟨permMatrix_unitary_of_injective (routePerm d q₀ e).injective,
          (isUnitaryCircuit_query _).mpr ((isUnitaryCircuit_gate _ _).mpr
            ⟨permMatrix_unitary_of_injective (routePerm d q₀ e).symm.injective, ih htail⟩)⟩

/-- Routing a circuit preserves its query count. -/
private theorem routedWord_queries (d : Q × Bool) (q₀ : J × Bool) (e : R → J ↪ Q)
    (C : Circuit ((J × Bool) × W)) :
    QueryCount (routedWord d q₀ e C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [routedWord, QueryCount, ih]

/-- Routing a circuit adds exactly two gates per query to its gate count. -/
private theorem routedWord_gates (d : Q × Bool) (q₀ : J × Bool) (e : R → J ↪ Q)
    (C : Circuit ((J × Bool) × W)) :
    GateCount (routedWord d q₀ e C) = GateCount C + 2 * QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [routedWord, GateCount, QueryCount, ih] <;> omega

/-- Running a routed circuit implements the corresponding local circuit and restores the bus
state. -/
private theorem routedWord_run (d : Q × Bool) (q₀ : J × Bool) (e : R → J ↪ Q)
    (z : Q → Bool) (C : Circuit ((J × Bool) × W))
    (ψ : QState (((J × Bool) × W) × R)) :
    Run (workspaceBitOracle z) (routedWord d q₀ e C) (TensorState (Ket d) ψ) =
      TensorState (Ket d) (Run (localOracle e z) (localWord C) ψ) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [routedWord, run_gate, applyGate_tensorGate, applyGate_one, ih]
      rfl
    | query =>
      have hr := cheatSheet_single_query_routing d q₀ e z ψ
      change ApplyGate (permMatrix (routePerm d q₀ e).symm)
        (ApplyGate (workspaceBitOracle z)
          (ApplyGate (permMatrix (routePerm d q₀ e)) (TensorState (Ket d) ψ))) =
        TensorState (Ket d) (ApplyGate (localOracle e z) ψ) at hr
      rw [routedWord, run_gate, run_query, run_gate, hr, ih]
      rfl

/-- A gate tensored with the identity acts by the original gate on each fixed auxiliary-register
fiber. -/
private theorem local_gate_fiber {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (ψ : QState (I × R)) (i : I) (r : R) :
    ApplyGate (TensorGate U 1) ψ (i, r) = ApplyGate U (fun a => ψ (a, r)) i := by
  simp only [ApplyGate, TensorGate, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single r]
  · simp
  · intro r' _ hr
    simp [Ne.symm hr]
  · simp

/-- On each auxiliary-register fiber, the local circuit runs the original circuit against the
oracle restricted by that fiber's embedding. -/
private theorem localWord_fiber (e : R → J ↪ Q) (z : Q → Bool)
    (C : Circuit ((J × Bool) × W)) (ψ : QState (((J × Bool) × W) × R))
    (i : (J × Bool) × W) (r : R) :
    Run (localOracle e z) (localWord C) ψ (i, r) =
      Run (workspaceBitOracle (fun j => z (e r j))) C (fun a => ψ (a, r)) i := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [localWord, run_gate, run_gate, ih]
      congr 1
      funext a
      exact local_gate_fiber U ψ a r
    | query =>
      rw [localWord, run_query, run_query, ih]
      congr 1
      funext a
      rw [localOracle, applyGate_permMatrix (localXor_involutive e z), applyGate_workspaceBitOracle]
      rfl

/-- A unitary subroutine can be routed through the global oracle with the same query count and
two extra gates per query, acting independently on each auxiliary-register fiber. -/
theorem cheatSheet_routed_subroutine (d : Q × Bool) (q₀ : J × Bool)
    (e : R → J ↪ Q) (C : Circuit ((J × Bool) × W)) (hC : IsUnitaryCircuit C) :
    ∃ D : Circuit ((Q × Bool) × (((J × Bool) × W) × R)),
      IsUnitaryCircuit D ∧ QueryCount D = QueryCount C ∧
      GateCount D = GateCount C + 2 * QueryCount C ∧
      ∀ (z : Q → Bool) (ψ : QState (((J × Bool) × W) × R)),
        Run (workspaceBitOracle z) D (TensorState (Ket d) ψ) =
          TensorState (Ket d) (fun a =>
            Run (workspaceBitOracle (fun j => z (e a.2 j))) C
              (fun i => ψ (i, a.2)) a.1) := by
  refine ⟨routedWord d q₀ e C, routedWord_unitary d q₀ e C hC,
    routedWord_queries d q₀ e C, routedWord_gates d q₀ e C, ?_⟩
  intro z ψ
  rw [routedWord_run]
  congr 1
  funext a
  exact localWord_fiber e z C ψ a.1 a.2

end SharedPortRouting

def cheatSheet_block_embedding {c M κ : ℕ} (i : Fin c) : Fin M ↪ CheatSheetIndex c M κ :=
  ⟨fun m => Sum.inl (i, m), by intro m m' h; simpa using h⟩

def cheatSheet_verifier_embedding {c M κ : ℕ} (i : Fin c) (a : Fin c → Bool) :
    (Fin M ⊕ Fin κ) ↪ CheatSheetIndex c M κ :=
  ⟨Sum.elim (fun m => Sum.inl (i, m)) (fun k => Sum.inr (sheetIndex a, i, k)), by
    intro u v h
    cases u <;> cases v <;> simp_all⟩

/-- Restricting the cheat-sheet oracle along a block embedding gives the corresponding block
oracle. -/
theorem cheatSheet_block_oracle {c M κ : ℕ} (i : Fin c)
    (z : CheatSheetIndex c M κ → Bool) :
    (fun j => z (cheatSheet_block_embedding i j)) = cheatBlock z i := rfl

/-- Restricting the cheat-sheet oracle along a verifier embedding gives the combined block and
selected certificate oracle. -/
theorem cheatSheet_verifier_oracle {c M κ : ℕ} (i : Fin c) (a : Fin c → Bool)
    (z : CheatSheetIndex c M κ → Bool) :
    (fun j => z (cheatSheet_verifier_embedding i a j)) =
      Sum.elim (cheatBlock z i) (cheatCert z (sheetIndex a) i) := by
  funext j
  cases j <;> rfl

set_option synthInstance.maxSize 100000 in

noncomputable def cheatSheet_tensor_start (c M κ : ℕ)
    {Wg Wφ : Type} [Fintype Wg] [DecidableEq Wg] [Fintype Wφ] [DecidableEq Wφ]
    (d : CheatSheetIndex c M κ × Bool)
    (ψg : QState ((Fin M × Bool) × Wg))
    (ψφ : QState (((Fin M ⊕ Fin κ) × Bool) × Wφ)) :
    QState ((CheatSheetIndex c M κ × Bool) ×
      ((Fin c → ((Fin M × Bool) × Wg)) ×
        (Fin c → (((Fin M ⊕ Fin κ) × Bool) × Wφ)) × (Fin c → Bool) × Bool)) :=
  TensorState (Ket d) (TensorState (PiTensorState (fun _ : Fin c => ψg))
    (TensorState (PiTensorState (fun _ : Fin c => ψφ))
      (TensorState (Ket (fun _ : Fin c => false)) (Ket false))))

set_option synthInstance.maxSize 100000 in

/-- Normalized block and verifier states give a normalized cheat-sheet tensor start state. -/
theorem cheatSheet_tensor_start_normalized (c M κ : ℕ)
    {Wg Wφ : Type} [Fintype Wg] [DecidableEq Wg] [Fintype Wφ] [DecidableEq Wφ]
    (d : CheatSheetIndex c M κ × Bool)
    (ψg : QState ((Fin M × Bool) × Wg))
    (ψφ : QState (((Fin M ⊕ Fin κ) × Bool) × Wφ))
    (hg : Normalized ψg) (hφ : Normalized ψφ) :
    Normalized (cheatSheet_tensor_start c M κ d ψg ψφ) :=
  normalized_tensorState (normalized_ket _) (normalized_tensorState
    (normalized_piTensorState (fun _ => hg)) (normalized_tensorState
      (normalized_piTensorState (fun _ => hφ))
      (normalized_tensorState (normalized_ket _) (normalized_ket _))))

section WorkspaceTransport
variable {Q J W R V : Type} [Fintype Q] [DecidableEq Q] [Fintype J] [DecidableEq J]
  [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R] [Fintype V] [DecidableEq V]

/-- Relabeling only the workspace leaves the workspace bit oracle unchanged up to that
relabeling. -/
private theorem workspace_oracle_relabel {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (u : A ≃ B) (z : Q → Bool) :
    relabelGate (Equiv.prodCongr (Equiv.refl (Q × Bool)) u) (workspaceBitOracle (W := A) z) =
      workspaceBitOracle (W := B) z := by
  ext a b
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Equiv.refl_symm, workspaceBitOracle,
    TensorGate, Matrix.kroneckerMap_apply, Matrix.one_apply]
  change (BitOracleOn z a.1 b.1 * (if u.symm a.2 = u.symm b.2 then 1 else 0)) =
    BitOracleOn z a.1 b.1 * (if a.2 = b.2 then 1 else 0)
  simp only [u.symm.injective.eq_iff]

/-- A unitary subroutine can be routed through an equivalent workspace with unchanged query
count and the stated fiberwise action. -/
theorem cheatSheet_routed_workspace (d : Q × Bool) (q₀ : J × Bool)
    (u : V ≃ ((J × Bool) × W) × R) (e : R → J ↪ Q)
    (C : Circuit ((J × Bool) × W)) (hC : IsUnitaryCircuit C) :
    ∃ D : Circuit ((Q × Bool) × V),
      IsUnitaryCircuit D ∧ QueryCount D = QueryCount C ∧
      ∀ (z : Q → Bool) (ψ : QState V),
        Run (workspaceBitOracle z) D (TensorState (Ket d) ψ) =
          TensorState (Ket d) (fun w =>
            Run (workspaceBitOracle (fun j => z (e (u w).2 j))) C
              (fun i => ψ (u.symm (i, (u w).2))) (u w).1) := by
  obtain ⟨D, hu, hq, _, hr⟩ := cheatSheet_routed_subroutine d q₀ e C hC
  let t := Equiv.prodCongr (Equiv.refl (Q × Bool)) u.symm
  obtain ⟨hlegal, hqueries, _, _⟩ := relabelCircuit_legality_resources t D
  refine ⟨relabelCircuit t D, hlegal.mpr hu, hqueries.trans hq, ?_⟩
  intro z ψ
  have ht := (run_relabelCircuit_readout t (workspaceBitOracle z) D
    (TensorState (Ket d) (relabelState u ψ)) Finset.univ).1
  have hinput : relabelState t (TensorState (Ket d) (relabelState u ψ)) =
      TensorState (Ket d) ψ := by
    funext a
    change Ket d a.1 * ψ (u.symm (u a.2)) = Ket d a.1 * ψ a.2
    rw [Equiv.symm_apply_apply]
  rw [workspace_oracle_relabel, hinput, hr] at ht
  exact ht

end WorkspaceTransport

/-- Circuit execution commutes with multiplication of the initial state by a complex scalar. -/
private theorem run_complex_scale {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C : Circuit I) (a : ℂ) (ψ : QState I) :
    Run O C (a • ψ) = a • Run O C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [run_gate, run_gate, show ApplyGate U (a • ψ) = a • ApplyGate U ψ from
        Matrix.mulVec_smul U a ψ, ih]
    | query =>
      rw [run_query, run_query, show ApplyGate O (a • ψ) = a • ApplyGate O ψ from
        Matrix.mulVec_smul O a ψ, ih]

section ControlledFactor
variable {c : ℕ} {Q J W R : Type} [Fintype Q] [DecidableEq Q] [Fintype J] [DecidableEq J]
  [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]

private def factorSplit (j : Fin c) :
    ((Fin c → (J × Bool) × W) × R) ≃
      ((J × Bool) × W) × (({l : Fin c // l ≠ j} → (J × Bool) × W) × R) :=
  (Equiv.prodCongr (Equiv.funSplitAt j ((J × Bool) × W)) (Equiv.refl R)).trans
    (Equiv.prodAssoc _ _ _)

/-- Recombining a factor split after replacing its selected factor corresponds to updating that
factor in the original family. -/
private theorem factorSplit_update (j : Fin c) (ω : Fin c → (J × Bool) × W)
    (r : R) (a : (J × Bool) × W) :
    (factorSplit j).symm (a, (factorSplit j (ω, r)).2) = (Function.update ω j a, r) := by
  apply Prod.ext
  · funext l
    by_cases hl : l = j
    · subst l; simp [factorSplit, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [factorSplit, Equiv.funSplitAt, Equiv.piSplitAt, hl]
  · rfl

/-- Evaluating a tensor-product state at a tuple with one updated coordinate factors out that
coordinate's amplitude. -/
private theorem factor_product_update {I : Type} [Fintype I] [DecidableEq I]
    (j : Fin c) (ψ : Fin c → QState I) (ω : Fin c → I) (a : I) :
    PiTensorState ψ (Function.update ω j a) =
      ψ j a * ∏ l ∈ Finset.univ.erase j, ψ l (ω l) := by
  rw [PiTensorState, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  rw [Function.update_of_ne (Finset.mem_erase.mp hl).1]

/-- Updating one state in a tensor-product family factors its amplitude out of the product at
any tuple. -/
private theorem factor_family_update {I : Type} [Fintype I] [DecidableEq I]
    (j : Fin c) (ψ : Fin c → QState I) (ω : Fin c → I) (φ : QState I) :
    PiTensorState (Function.update ψ j φ) ω =
      φ (ω j) * ∏ l ∈ Finset.univ.erase j, ψ l (ω l) := by
  rw [PiTensorState, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  rw [Function.update_of_ne (Finset.mem_erase.mp hl).1]

/-- A unitary subroutine can be routed to one chosen tensor factor with unchanged query count
while preserving the other factors and auxiliary amplitudes. -/
theorem cheatSheet_routed_factor (d : Q × Bool) (q₀ : J × Bool)
    (j : Fin c) (e : R → J ↪ Q) (C : Circuit ((J × Bool) × W))
    (hC : IsUnitaryCircuit C) :
    ∃ D : Circuit ((Q × Bool) × ((Fin c → (J × Bool) × W) × R)),
      IsUnitaryCircuit D ∧ QueryCount D = QueryCount C ∧
      ∀ (z : Q → Bool) (χ : QState R) (ψ : R → Fin c → QState ((J × Bool) × W)),
        Run (workspaceBitOracle z) D (TensorState (Ket d)
          (fun a => PiTensorState (ψ a.2) a.1 * χ a.2)) =
        TensorState (Ket d) (fun a =>
          PiTensorState (Function.update (ψ a.2) j
            (Run (workspaceBitOracle (fun l => z (e a.2 l))) C (ψ a.2 j))) a.1 * χ a.2) := by
  obtain ⟨D, hu, hq, hr⟩ := cheatSheet_routed_workspace d q₀ (factorSplit j)
    (fun r => e r.2) C hC
  refine ⟨D, hu, hq, ?_⟩
  intro z χ ψ
  rw [hr]
  congr 1
  funext a
  rcases a with ⟨ω, r⟩
  simp only [factorSplit_update]
  change Run (workspaceBitOracle (fun l => z (e r l))) C
    (fun i => PiTensorState (ψ r) (Function.update ω j i) * χ r) (ω j) = _
  let scale := (∏ l ∈ Finset.univ.erase j, ψ r l (ω l)) * χ r
  have hinput : (fun i => PiTensorState (ψ r) (Function.update ω j i) * χ r) =
      scale • ψ r j := by
    funext i
    rw [factor_product_update]
    simp only [Pi.smul_apply, smul_eq_mul]
    dsimp [scale]
    ring
  rw [hinput, run_complex_scale, Pi.smul_apply, smul_eq_mul, factor_family_update]
  dsimp [scale]
  ring

/-- Executing routed factor circuits over a list without duplicates applies the subroutine
exactly to the listed factors. -/
private theorem routed_factors_list (d : Q × Bool)
    (C : Circuit ((J × Bool) × W)) (e : Fin c → R → J ↪ Q)
    (D : Fin c → Circuit ((Q × Bool) × ((Fin c → (J × Bool) × W) × R)))
    (hD : ∀ j (z : Q → Bool) (χ : QState R) (ψ : R → Fin c → QState ((J × Bool) × W)),
      Run (workspaceBitOracle z) (D j) (TensorState (Ket d)
        (fun a => PiTensorState (ψ a.2) a.1 * χ a.2)) =
      TensorState (Ket d) (fun a => PiTensorState (Function.update (ψ a.2) j
        (Run (workspaceBitOracle (fun l => z (e j a.2 l))) C (ψ a.2 j))) a.1 * χ a.2))
    (z : Q → Bool) (χ : QState R) (L : List (Fin c)) (hL : L.Nodup)
    (ψ : R → Fin c → QState ((J × Bool) × W)) :
    Run (workspaceBitOracle z) (L.flatMap D)
      (TensorState (Ket d) (fun a => PiTensorState (ψ a.2) a.1 * χ a.2)) =
      TensorState (Ket d) (fun a => PiTensorState (fun j => if j ∈ L then
        Run (workspaceBitOracle (fun l => z (e j a.2 l))) C (ψ a.2 j) else ψ a.2 j) a.1 * χ a.2) := by
  induction L generalizing ψ with
  | nil => simp
  | cons j L ih =>
    obtain ⟨hj, hnd⟩ := List.nodup_cons.mp hL
    rw [List.flatMap_cons, run_append, hD j]
    rw [ih hnd (fun r => Function.update (ψ r) j
      (Run (workspaceBitOracle (fun l => z (e j r l))) C (ψ r j)))]
    apply congrArg (TensorState (Ket d))
    funext a
    apply congrArg (fun φ => PiTensorState φ a.1 * χ a.2)
    funext l
    by_cases hl : l = j
    · subst l; simp [hj]
    · simp [hl]

/-- Concatenating a list of unitary circuits gives a unitary circuit. -/
private theorem list_words_unitary {I A : Type} [Fintype I] [DecidableEq I]
    (D : A → Circuit I) (hD : ∀ a, IsUnitaryCircuit (D a)) (L : List A) :
    IsUnitaryCircuit (L.flatMap D) := by
  induction L with
  | nil => exact isUnitaryCircuit_nil
  | cons a L ih =>
    simp only [List.flatMap_cons, isUnitaryCircuit_append]
    exact ⟨hD a, ih⟩

/-- Concatenating a list of circuits with the same query count gives the list length times that
query count. -/
private theorem list_words_queries {I A : Type} [Fintype I] [DecidableEq I]
    (D : A → Circuit I) (q : ℕ) (hD : ∀ a, QueryCount (D a) = q) (L : List A) :
    QueryCount (L.flatMap D) = L.length * q := by
  induction L with
  | nil => simp
  | cons a L ih => simp [queryCount_append, hD, ih, Nat.succ_mul, Nat.add_comm]

/-- A unitary subroutine can be routed to every tensor factor with total query count equal to
the number of factors times its original query count. -/
theorem cheatSheet_routed_factors (d : Q × Bool) (q₀ : J × Bool)
    (e : Fin c → R → J ↪ Q) (C : Circuit ((J × Bool) × W)) (hC : IsUnitaryCircuit C) :
    ∃ D : Circuit ((Q × Bool) × ((Fin c → (J × Bool) × W) × R)),
      IsUnitaryCircuit D ∧ QueryCount D = c * QueryCount C ∧
      ∀ (z : Q → Bool) (χ : QState R) (ψ : R → Fin c → QState ((J × Bool) × W)),
        Run (workspaceBitOracle z) D (TensorState (Ket d)
          (fun a => PiTensorState (ψ a.2) a.1 * χ a.2)) =
        TensorState (Ket d) (fun a => PiTensorState (fun j =>
          Run (workspaceBitOracle (fun l => z (e j a.2 l))) C (ψ a.2 j)) a.1 * χ a.2) := by
  classical
  choose D hu hq hr using fun j => cheatSheet_routed_factor d q₀ j (e j) C hC
  refine ⟨(List.finRange c).flatMap D, list_words_unitary D hu _, ?_, ?_⟩
  · simpa using list_words_queries D (QueryCount C) hq (List.finRange c)
  · intro z χ ψ
    simpa using routed_factors_list d C e D hr z χ (List.finRange c) (List.nodup_finRange c) ψ

end ControlledFactor

section ProducedProgram
set_option synthInstance.maxSize 100000
variable {c M κ : ℕ} {Wg Wφ : Type} [Fintype Wg] [DecidableEq Wg] [Fintype Wφ] [DecidableEq Wφ]

private abbrev GRegister := (Fin M × Bool) × Wg
private abbrev PhiRegister := ((Fin M ⊕ Fin κ) × Bool) × Wφ
private abbrev RetainedWorkspace :=
  (Fin c → GRegister (M := M) (Wg := Wg)) ×
    (Fin c → PhiRegister (M := M) (κ := κ) (Wφ := Wφ)) × (Fin c → Bool) × Bool

private def retainedSwap {A B F : Type} : A × B × F ≃ B × A × F where
  toFun w := (w.2.1, w.1, w.2.2)
  invFun w := (w.2.1, w.1, w.2.2)
  left_inv := by rintro ⟨a, b, f⟩; rfl
  right_inv := by rintro ⟨b, a, f⟩; rfl

private def copiedVerdicts (Eg : Finset (GRegister (M := M) (Wg := Wg)))
    (ug : Fin c → GRegister (M := M) (Wg := Wg)) : Fin c → Bool :=
  fun i => decide (ug i ∈ Eg)

private def copyRetained (Eg : Finset (GRegister (M := M) (Wg := Wg)))
    (w : RetainedWorkspace (c := c) (M := M) (κ := κ) (Wg := Wg) (Wφ := Wφ)) :=
  (w.1, w.2.1, (fun i => w.2.2.1 i ^^ copiedVerdicts Eg w.1 i), w.2.2.2)

/-- The transformation `copyRetained` is involutive. -/
private theorem copyRetained_involutive (Eg : Finset (GRegister (M := M) (Wg := Wg))) :
    Function.Involutive (copyRetained (c := c) (κ := κ) (Wφ := Wφ) Eg) := by
  rintro ⟨ug, up, a, f⟩
  dsimp [copyRetained]
  congr 3
  funext i
  simp

/-- The all-false ket evaluated at the pointwise XOR of two Boolean vectors equals the ket of
one evaluated at the other. -/
private theorem clear_verdict_ket (a v : Fin c → Bool) :
    Ket (fun _ : Fin c => false) (fun i => a i ^^ v i) = Ket v a := by
  have h : (fun i => a i ^^ v i) = (fun _ => false) ↔ a = v := by
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      cases ha : a i <;> cases hv : v i <;> simp_all
    · intro h
      subst a
      funext i
      simp
  simp only [Ket, h]

private noncomputable def cheatSheet_output
    (d : CheatSheetIndex c M κ × Bool)
    (Cg : Circuit (GRegister (M := M) (Wg := Wg))) (ψg : QState (GRegister (M := M) (Wg := Wg)))
    (Eg : Finset (GRegister (M := M) (Wg := Wg)))
    (Cφ : Circuit (PhiRegister (M := M) (κ := κ) (Wφ := Wφ)))
    (ψφ : QState (PhiRegister (M := M) (κ := κ) (Wφ := Wφ)))
    (z : CheatSheetIndex c M κ → Bool) :
    QState ((CheatSheetIndex c M κ × Bool) ×
      RetainedWorkspace (c := c) (M := M) (κ := κ) (Wg := Wg) (Wφ := Wφ)) :=
  TensorState (Ket d) (fun w =>
    PiTensorState (fun i => Run (workspaceBitOracle (cheatBlock z i)) Cg ψg) w.1 *
    PiTensorState (fun i => Run (workspaceBitOracle
      (Sum.elim (cheatBlock z i) (cheatCert z (sheetIndex w.2.2.1) i))) Cφ ψφ) w.2.1 *
    Ket (copiedVerdicts Eg w.1) w.2.2.1 * Ket false w.2.2.2)

/-- Compiles unitary block and verifier circuits into a unitary cheat-sheet circuit with the
specified output state and query count equal to the block count times the sum of subroutine
query counts. -/
theorem cheatSheet_compiled_program
    (d : CheatSheetIndex c M κ × Bool) (qg₀ : Fin M × Bool)
    (qφ₀ : (Fin M ⊕ Fin κ) × Bool)
    (Cg : Circuit ((Fin M × Bool) × Wg)) (ψg : QState ((Fin M × Bool) × Wg))
    (Eg : Finset ((Fin M × Bool) × Wg))
    (Cφ : Circuit (((Fin M ⊕ Fin κ) × Bool) × Wφ))
    (ψφ : QState (((Fin M ⊕ Fin κ) × Bool) × Wφ))
    (hg : IsUnitaryCircuit Cg) (hφ : IsUnitaryCircuit Cφ) :
    ∃ D : Circuit ((CheatSheetIndex c M κ × Bool) ×
        ((Fin c → ((Fin M × Bool) × Wg)) ×
          (Fin c → (((Fin M ⊕ Fin κ) × Bool) × Wφ)) × (Fin c → Bool) × Bool)),
      IsUnitaryCircuit D ∧ QueryCount D = c * (QueryCount Cg + QueryCount Cφ) ∧
      ∀ z : CheatSheetIndex c M κ → Bool,
        Run (workspaceBitOracle z) D (cheatSheet_tensor_start c M κ d ψg ψφ) =
          TensorState (Ket d) (fun w =>
            PiTensorState (fun i => Run (workspaceBitOracle (cheatBlock z i)) Cg ψg) w.1 *
            PiTensorState (fun i => Run (workspaceBitOracle
              (Sum.elim (cheatBlock z i) (cheatCert z (sheetIndex w.2.2.1) i))) Cφ ψφ) w.2.1 *
            Ket (fun i => decide (w.1 i ∈ Eg)) w.2.2.1 * Ket false w.2.2.2) := by
  change ∃ D : Circuit ((CheatSheetIndex c M κ × Bool) ×
      RetainedWorkspace (c := c) (M := M) (κ := κ) (Wg := Wg) (Wφ := Wφ)),
    IsUnitaryCircuit D ∧ QueryCount D = c * (QueryCount Cg + QueryCount Cφ) ∧
    ∀ z : CheatSheetIndex c M κ → Bool,
      Run (workspaceBitOracle z) D (cheatSheet_tensor_start c M κ d ψg ψφ) =
        cheatSheet_output d Cg ψg Eg Cφ ψφ z
  let Pg := Fin c → GRegister (M := M) (Wg := Wg)
  let Pφ := Fin c → PhiRegister (M := M) (κ := κ) (Wφ := Wφ)
  let A := (Fin c → Bool) × Bool
  obtain ⟨Dg, hgu, hgq, hgr⟩ := cheatSheet_routed_factors (R := Pφ × A)
    d qg₀ (fun i _ => cheatSheet_block_embedding i) Cg hg
  obtain ⟨Dφ, hφu, hφq, hφr⟩ := cheatSheet_routed_factors (R := Pg × A)
    d qφ₀ (fun i r => cheatSheet_verifier_embedding i r.2.1) Cφ hφ
  let t := Equiv.prodCongr (Equiv.refl (CheatSheetIndex c M κ × Bool))
    (retainedSwap (A := Pφ) (B := Pg) (F := A))
  obtain ⟨htlegal, htq, _, _⟩ := relabelCircuit_legality_resources t Dφ
  let U := TensorGate (1 : Matrix (CheatSheetIndex c M κ × Bool) _ ℂ)
    (permMatrix (copyRetained (c := c) (κ := κ) (Wφ := Wφ) Eg))
  have hU : U ∈ Matrix.unitaryGroup _ ℂ :=
    tensorGate_unitary (Submonoid.one_mem _) (permMatrix_unitary (copyRetained_involutive Eg))
  refine ⟨Dg ++ [Step.gate U] ++ relabelCircuit t Dφ, ?_, ?_, ?_⟩
  · exact (isUnitaryCircuit_append _ _).mpr
      ⟨(isUnitaryCircuit_append _ _).mpr ⟨hgu,
        (isUnitaryCircuit_gate _ _).mpr ⟨hU, isUnitaryCircuit_nil⟩⟩, htlegal.mpr hφu⟩
  · simp only [queryCount_append, htq, hgq, hφq, QueryCount]
    ring
  · intro z
    let G := fun i => Run (workspaceBitOracle (cheatBlock z i)) Cg ψg
    let Φ := fun a i => Run (workspaceBitOracle
      (Sum.elim (cheatBlock z i) (cheatCert z (sheetIndex a) i))) Cφ ψφ
    let χg := fun r : Pφ × A => PiTensorState (fun _ : Fin c => ψφ) r.1 *
      Ket (fun _ : Fin c => false) r.2.1 * Ket false r.2.2
    let χφ := fun r : Pg × A => PiTensorState G r.1 *
      Ket (copiedVerdicts Eg r.1) r.2.1 * Ket false r.2.2
    have hforward := hgr z χg (fun _ _ => ψg)
    simp only [cheatSheet_block_oracle] at hforward
    have hstart : cheatSheet_tensor_start c M κ d ψg ψφ =
        TensorState (Ket d) (fun a => PiTensorState (fun _ : Fin c => ψg) a.1 * χg a.2) := by
      funext a
      simp only [cheatSheet_tensor_start, TensorState, χg]
      ring
    have hcopy : ApplyGate U (TensorState (Ket d)
        (fun a => PiTensorState G a.1 * χg a.2)) =
        relabelState t (TensorState (Ket d)
          (fun a => PiTensorState (fun _ : Fin c => ψφ) a.1 * χφ a.2)) := by
      rw [applyGate_tensorGate, applyGate_one]
      funext a
      rw [tensorState_apply]
      rw [applyGate_permMatrix (copyRetained_involutive Eg)]
      change Ket d a.1 * (PiTensorState G a.2.1 * χg
        ((copyRetained Eg a.2).2)) = _
      simp only [χg, χφ, copyRetained, clear_verdict_ket, relabelState]
      change Ket d a.1 * (PiTensorState G a.2.1 *
        (PiTensorState (fun _ : Fin c => ψφ) a.2.2.1 *
          Ket (copiedVerdicts Eg a.2.1) a.2.2.2.1 * Ket false a.2.2.2.2)) =
        Ket d a.1 * (PiTensorState (fun _ : Fin c => ψφ) a.2.2.1 *
          (PiTensorState G a.2.1 * Ket (copiedVerdicts Eg a.2.1) a.2.2.2.1 * Ket false a.2.2.2.2))
      ring
    have hverifier := (run_relabelCircuit_readout t (workspaceBitOracle z) Dφ
      (TensorState (Ket d) (fun a => PiTensorState (fun _ : Fin c => ψφ) a.1 * χφ a.2))
      Finset.univ).1
    rw [workspace_oracle_relabel, hφr z χφ (fun _ _ => ψφ)] at hverifier
    simp only [cheatSheet_verifier_oracle] at hverifier
    rw [run_append, run_append, hstart, hforward]
    change Run (workspaceBitOracle z) (relabelCircuit t Dφ)
      (ApplyGate U (TensorState (Ket d) (fun a => PiTensorState G a.1 * χg a.2))) = _
    rw [hcopy, hverifier]
    funext a
    change Ket d a.1 * (PiTensorState (Φ a.2.2.2.1) a.2.2.1 * χφ
      (a.2.1, a.2.2.2)) = _
    simp only [cheatSheet_output, TensorState, χφ]
    change Ket d a.1 * (PiTensorState (Φ a.2.2.2.1) a.2.2.1 *
      (PiTensorState G a.2.1 * Ket (copiedVerdicts Eg a.2.1) a.2.2.2.1 * Ket false a.2.2.2.2)) =
      Ket d a.1 * (PiTensorState G a.2.1 * PiTensorState (Φ a.2.2.2.1) a.2.2.1 *
        Ket (copiedVerdicts Eg a.2.1) a.2.2.2.1 * Ket false a.2.2.2.2)
    ring

end ProducedProgram

section FibreProbability
variable {A B T : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype T] [DecidableEq T]

private noncomputable def fibreState (χ : QState A) (φ : B → QState T) (v : A → B) :
    QState (A × T × B × Bool) :=
  fun w => χ w.1 * φ w.2.2.1 w.2.1 * Ket (v w.1) w.2.2.1 * Ket false w.2.2.2

/-- The measurement mass of a fiber-state event equals the sum of its conditional event masses
weighted by the outer Born probabilities. -/
private theorem fibre_mass (χ : QState A) (φ : B → QState T) (v : A → B) (S : Finset T) :
    MeasureProb (fibreState χ φ v) (Finset.univ.filter fun w => w.2.1 ∈ S) =
      ∑ a : A, BornProb χ a * MeasureProb (φ (v a)) S := by
  have hmeas : ∀ b, MeasureProb (φ b) S =
      ∑ t : T, if t ∈ S then BornProb (φ b) t else 0 := by
    intro b
    rw [show S = Finset.univ.filter (fun t => t ∈ S) by ext t; simp,
      MeasureProb, Finset.sum_filter]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp_rw [hmeas]
  simp only [MeasureProb, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_eq_single (v a)]
  · rw [Finset.sum_eq_single false]
    · by_cases ht : t ∈ S <;>
        simp [ht, fibreState, BornProb, mul_pow]
    · intro f _ hf
      simp [fibreState, BornProb, Ket, hf]
    · simp
  · intro b _ hb
    simp [fibreState, BornProb, Ket, hb]
  · simp

/-- A uniform lower bound on conditional event masses over an outer event yields the outer event
mass times that bound as a lower bound on the fiber-state event mass. -/
private theorem fibre_lower (χ : QState A) (φ : B → QState T) (v : A → B)
    (G : Finset A) (S : Finset T) (q : ℝ)
    (hq : ∀ a ∈ G, q ≤ MeasureProb (φ (v a)) S) :
    MeasureProb χ G * q ≤
      MeasureProb (fibreState χ φ v) (Finset.univ.filter fun w => w.2.1 ∈ S) := by
  rw [fibre_mass, MeasureProb, Finset.sum_mul]
  calc
    (∑ a ∈ G, BornProb χ a * q) ≤
        ∑ a ∈ G, BornProb χ a * MeasureProb (φ (v a)) S := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hq a ha) (bornProb_nonneg χ a)
    _ ≤ ∑ a : A, BornProb χ a * MeasureProb (φ (v a)) S :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
        (fun a _ _ => mul_nonneg (bornProb_nonneg χ a) (measureProb_nonneg _ _))

end FibreProbability

/-- The measurement mass of a tensor-product cylinder event is the product of the component
event masses. -/
private theorem tensor_cylinder_mass {I ι : Type} [Fintype I] [DecidableEq I]
    [Fintype ι] [DecidableEq ι] (ψ : ι → QState I) (S : ι → Finset I) :
    MeasureProb (PiTensorState ψ) (Fintype.piFinset S) = ∏ j, MeasureProb (ψ j) (S j) := by
  unfold MeasureProb
  simp_rw [bornProb_piTensorState]
  exact (Finset.prod_univ_sum S (fun j a => BornProb (ψ j) a)).symm

/-- A finite product of probabilities each at least one minus a nonnegative error is at least
one minus the number of factors times that error. -/
private theorem finite_product_error {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hbound : ∀ i, 1 - ε ≤ p i) :
    1 - (Fintype.card ι : ℝ) * ε ≤ ∏ i, p i := by
  have hfin : ∀ S : Finset ι, 1 - (S.card : ℝ) * ε ≤ ∏ i ∈ S, p i := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
      have hprod0 : 0 ≤ ∏ j ∈ S, p j := Finset.prod_nonneg (fun j _ => (hp j).1)
      have hprod1 : (∏ j ∈ S, p j) ≤ 1 := Finset.prod_le_one₀ (fun j _ => (hp j).1)
        (fun j _ => (hp j).2)
      have hdef := hbound i
      have hnew := mul_nonneg (by linarith : 0 ≤ p i - (1 - ε)) hprod0
      have herr := mul_nonneg hε (by linarith : 0 ≤ 1 - ∏ j ∈ S, p j)
      nlinarith
  simpa using hfin Finset.univ

/-- For a normalized state, every event has measurement probability between zero and one. -/
private theorem normalized_event_bound {I : Type} [Fintype I] [DecidableEq I]
    (ψ : QState I) (hψ : Normalized ψ) (S : Finset I) :
    0 ≤ MeasureProb ψ S ∧ MeasureProb ψ S ≤ 1 := by
  refine ⟨measureProb_nonneg ψ S, ?_⟩
  rw [← measureProb_univ hψ]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun i _ _ => bornProb_nonneg ψ i)

/-- For normalized tensor factors, the measurement probability of an event in one coordinate
equals that factor's event probability. -/
private theorem tensor_coordinate_mass {ι I : Type} [Fintype ι] [DecidableEq ι]
    [Fintype I] [DecidableEq I] (ψ : ι → QState I) (hψ : ∀ i, Normalized (ψ i))
    (j : ι) (S : Finset I) :
    MeasureProb (PiTensorState ψ) (Finset.univ.filter fun ω => ω j ∈ S) =
      MeasureProb (ψ j) S := by
  have hset : (Finset.univ.filter fun ω : ι → I => ω j ∈ S) =
      Fintype.piFinset (fun i => if i = j then S else Finset.univ) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i = j <;> simp [hi, h]
    · intro h
      simpa using h j
  rw [hset, tensor_cylinder_mass, Finset.prod_eq_single j]
  · simp
  · intro i _ hi
    simp [hi, measureProb_univ (hψ i)]
  · simp

section ProducedProbability
set_option synthInstance.maxSize 100000
variable {c M κ : ℕ} {Wg Wφ : Type} [Fintype Wg] [DecidableEq Wg] [Fintype Wφ] [DecidableEq Wφ]

/-- The verifier-register event mass in the compiled cheat-sheet output equals the corresponding
event mass in its explicit fiber-state representation. -/
private theorem output_event_mass
    (d : CheatSheetIndex c M κ × Bool)
    (Cg : Circuit (GRegister (M := M) (Wg := Wg))) (ψg : QState (GRegister (M := M) (Wg := Wg)))
    (Eg : Finset (GRegister (M := M) (Wg := Wg)))
    (Cφ : Circuit (PhiRegister (M := M) (κ := κ) (Wφ := Wφ)))
    (ψφ : QState (PhiRegister (M := M) (κ := κ) (Wφ := Wφ)))
    (z : CheatSheetIndex c M κ → Bool)
    (S : Finset (Fin c → PhiRegister (M := M) (κ := κ) (Wφ := Wφ))) :
    MeasureProb (cheatSheet_output d Cg ψg Eg Cφ ψφ z)
      (Finset.univ.filter fun w => w.2.2.1 ∈ S) =
    MeasureProb (fibreState
      (PiTensorState (fun i => Run (workspaceBitOracle (cheatBlock z i)) Cg ψg))
      (fun a => PiTensorState (fun i => Run (workspaceBitOracle
        (Sum.elim (cheatBlock z i) (cheatCert z (sheetIndex a) i))) Cφ ψφ))
      (copiedVerdicts Eg)) (Finset.univ.filter fun w => w.2.1 ∈ S) := by
  have hset : (Finset.univ.filter fun w : (CheatSheetIndex c M κ × Bool) ×
      RetainedWorkspace (c := c) (M := M) (κ := κ) (Wg := Wg) (Wφ := Wφ) => w.2.2.1 ∈ S) =
      Finset.univ ×ˢ (Finset.univ.filter fun w => w.2.1 ∈ S) := by
    ext w; simp
  rw [hset]
  exact measureProb_tensorState_right (normalized_ket d) _ _

/-- The event that every verifier gives its correct local verdict is contained in the event
giving the correct overall cheat-sheet verdict. -/
private theorem verifier_good_subset
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool)
    (g : (Fin M → Bool) → Bool) (z : CheatSheetIndex c M κ → Bool)
    (Eφ : Finset (PhiRegister (M := M) (κ := κ) (Wφ := Wφ))) :
    Fintype.piFinset (fun i : Fin c =>
      if φ (cheatBlock z i) (cheatCert z (sheetIndex fun j => g (cheatBlock z j)) i)
      then Eφ else Eφᶜ) ⊆
      (if cheatSheetFun (c := c) g φ z then Fintype.piFinset (fun _ : Fin c => Eφ)
        else (Fintype.piFinset (fun _ : Fin c => Eφ))ᶜ) := by
  intro ω hω
  have hg := Fintype.mem_piFinset.mp hω
  cases hb : cheatSheetFun (c := c) g φ z with
  | true =>
    simp only [↓reduceIte]
    apply Fintype.mem_piFinset.mpr
    have hh : ∀ i : Fin c,
        φ (cheatBlock z i) (cheatCert z (sheetIndex fun j => g (cheatBlock z j)) i) = true :=
      of_decide_eq_true hb
    intro i
    simpa [hh i] using hg i
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_compl]
    have hh : ¬ ∀ i : Fin c,
        φ (cheatBlock z i) (cheatCert z (sheetIndex fun j => g (cheatBlock z j)) i) = true :=
      of_decide_eq_false hb
    push Not at hh
    obtain ⟨j, hj⟩ := hh
    intro hacc
    have hhj : φ (cheatBlock z j)
        (cheatCert z (sheetIndex fun i => g (cheatBlock z i)) j) = false := Bool.eq_false_iff.mpr hj
    have hbad : ω j ∉ Eφ := by simpa [hhj] using hg j
    exact hbad (Fintype.mem_piFinset.mp hacc j)

/-- For a tuple of block states yielding prescribed event-membership verdicts, `copiedVerdicts`
equals the prescribed Boolean vector. -/
private theorem good_verdicts
    (Eg : Finset (GRegister (M := M) (Wg := Wg))) (a : Fin c → Bool)
    (ω : Fin c → GRegister (M := M) (Wg := Wg))
    (hω : ω ∈ Fintype.piFinset (fun i => if a i then Eg else Egᶜ)) :
    copiedVerdicts Eg ω = a := by
  funext i
  have hi := Fintype.mem_piFinset.mp hω i
  cases ha : a i <;> simp [ha] at hi <;> simp [copiedVerdicts, hi]

end ProducedProbability

set_option synthInstance.maxSize 100000 in
set_option maxHeartbeats 1000000 in

/-- Under the certifying and subroutine success assumptions, constructs a bounded-error quantum
cheat-sheet algorithm using at most the block count times the sum of the subroutine query
counts. -/
theorem cheatSheetQuantumUpperBound : CheatSheetQuantumUpperBound := by
  intro c M κ hc hκ dom g φ Wg Wφ _ _ _ _ Cg ψg Eg Cφ ψφ Eφ
    hcert hCg hψg hCφ hψφ hsg hsφ
  classical
  have hn : Nonempty ((Fin M × Bool) × Wg) := by
    by_contra h
    have : IsEmpty ((Fin M × Bool) × Wg) := not_nonempty_iff.mp h
    simp [Normalized] at hψg
  obtain ⟨⟨m, _⟩, _⟩ := Classical.choice hn
  let d : CheatSheetIndex c M κ × Bool := (Sum.inl (⟨0, hc⟩, m), false)
  obtain ⟨D, hu, hq, hr⟩ := cheatSheet_compiled_program d (m, false) (Sum.inl m, false)
    Cg ψg Eg Cφ ψφ hCg hCφ
  change ∀ z : CheatSheetIndex c M κ → Bool,
    Run (workspaceBitOracle z) D (cheatSheet_tensor_start c M κ d ψg ψφ) =
      cheatSheet_output d Cg ψg Eg Cφ ψφ z at hr
  let Accept := Fintype.piFinset (fun _ : Fin c => Eφ)
  let E : Finset ((CheatSheetIndex c M κ × Bool) ×
      RetainedWorkspace (c := c) (M := M) (κ := κ) (Wg := Wg) (Wφ := Wφ)) :=
    Finset.univ.filter fun w => w.2.2.1 ∈ Accept
  refine ⟨D, cheatSheet_tensor_start c M κ d ψg ψφ, E, hu,
    cheatSheet_tensor_start_normalized c M κ d ψg ψφ hψg hψφ, hq.le, ?_⟩
  intro z
  let δ : ℝ := 1 / (6 * (c : ℝ))
  have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr hc
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast (Nat.succ_le_iff.mpr hc)
  have hδ : 0 ≤ δ := by positivity
  have hcδ : (c : ℝ) * δ = 1 / 6 := by
    dsimp [δ]
    field_simp
  have hδsmall : δ ≤ 1 / 6 := by
    dsimp [δ]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  let G := fun i => Run (workspaceBitOracle (cheatBlock z i)) Cg ψg
  let P := fun a i => Run (workspaceBitOracle
    (Sum.elim (cheatBlock z i) (cheatCert z (sheetIndex a) i))) Cφ ψφ
  have hGN : ∀ i, Normalized (G i) := fun i =>
    hCg.normalized_run (workspaceBitOracle_unitary _) hψg
  have hPN : ∀ a i, Normalized (P a i) := fun a i =>
    hCφ.normalized_run (workspaceBitOracle_unitary _) hψφ
  let S := if cheatSheetFun (c := c) g φ z then Accept else Acceptᶜ
  have hE : (if cheatSheetFun (c := c) g φ z then E else Eᶜ) =
      Finset.univ.filter (fun w => w.2.2.1 ∈ S) := by
    cases h : cheatSheetFun (c := c) g φ z <;> ext w <;> simp [E, S, h]
  rw [hr, hE, output_event_mass]
  change (2 / 3 : ℝ) ≤ MeasureProb (fibreState (PiTensorState G)
    (fun a => PiTensorState (P a)) (copiedVerdicts Eg))
    (Finset.univ.filter fun w => w.2.1 ∈ S)
  by_cases hdom : ∀ i : Fin c, dom (cheatBlock z i)
  · let a₀ := fun i => g (cheatBlock z i)
    let Good := Fintype.piFinset (fun i => if a₀ i then Eg else Egᶜ)
    have hgood : (5 / 6 : ℝ) ≤ MeasureProb (PiTensorState G) Good := by
      rw [tensor_cylinder_mass]
      have hp := finite_product_error (fun i => MeasureProb (G i) (if a₀ i then Eg else Egᶜ))
        δ hδ (fun i => normalized_event_bound (G i) (hGN i) _)
        (fun i => hsg (cheatBlock z i) (hdom i))
      simp only [Fintype.card_fin, hcδ] at hp
      norm_num at hp
      exact hp
    have hverify : ∀ ω ∈ Good, (5 / 6 : ℝ) ≤ MeasureProb
        (PiTensorState (P (copiedVerdicts Eg ω))) S := by
      intro ω hω
      rw [good_verdicts Eg a₀ ω hω]
      let Vgood := Fintype.piFinset (fun i : Fin c =>
        if φ (cheatBlock z i) (cheatCert z (sheetIndex a₀) i) then Eφ else Eφᶜ)
      have hcorrect : (5 / 6 : ℝ) ≤ MeasureProb (PiTensorState (P a₀)) Vgood := by
        rw [tensor_cylinder_mass]
        have hp := finite_product_error (fun i => MeasureProb (P a₀ i)
            (if φ (cheatBlock z i) (cheatCert z (sheetIndex a₀) i) then Eφ else Eφᶜ))
          δ hδ (fun i => normalized_event_bound (P a₀ i) (hPN a₀ i) _)
          (fun i => hsφ (cheatBlock z i) (cheatCert z (sheetIndex a₀) i))
        simp only [Fintype.card_fin, hcδ] at hp
        norm_num at hp
        exact hp
      exact hcorrect.trans (Finset.sum_le_sum_of_subset_of_nonneg
        (verifier_good_subset φ g z Eφ) (fun i _ _ => bornProb_nonneg _ i))
    have htotal := fibre_lower (PiTensorState G) (fun a => PiTensorState (P a))
      (copiedVerdicts Eg) Good S (5 / 6) hverify
    nlinarith
  · push Not at hdom
    obtain ⟨j, hj⟩ := hdom
    have hfalse := cheatSheetOutsideDomain_rejects hκ dom g φ hcert z j hj
    have hS : S = Acceptᶜ := by simp [S, hfalse]
    have hreject : ∀ y, φ (cheatBlock z j) y = false := by
      intro y
      apply Bool.eq_false_iff.mpr
      intro h
      exact hj (hcert.1 _ _ h).1
    let Reject := Finset.univ.filter fun ω : Fin c → PhiRegister (M := M) (κ := κ) (Wφ := Wφ) =>
      ω j ∈ Eφᶜ
    have hsubset : Reject ⊆ S := by
      rw [hS]
      intro ω hω
      rw [Finset.mem_compl]
      intro hacc
      exact (Finset.mem_compl.mp (Finset.mem_filter.mp hω).2)
        (Fintype.mem_piFinset.mp hacc j)
    have hverify : ∀ a, 1 - δ ≤ MeasureProb (PiTensorState (P a)) S := by
      intro a
      calc
        1 - δ ≤ MeasureProb (P a j) Eφᶜ := by
          simpa [hreject, P, δ] using hsφ (cheatBlock z j) (cheatCert z (sheetIndex a) j)
        _ = MeasureProb (PiTensorState (P a)) Reject :=
          (tensor_coordinate_mass (P a) (hPN a) j Eφᶜ).symm
        _ ≤ MeasureProb (PiTensorState (P a)) S :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ => bornProb_nonneg _ i)
    have htotal := fibre_lower (PiTensorState G) (fun a => PiTensorState (P a))
      (copiedVerdicts Eg) Finset.univ S (1 - δ) (fun a _ => hverify _)
    rw [measureProb_univ (normalized_piTensorState hGN), one_mul] at htotal
    linarith

end Qatlib.Papers.CheatSheet15.BornBaseline
