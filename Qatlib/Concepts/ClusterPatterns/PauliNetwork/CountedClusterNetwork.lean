/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetwork
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkBranch
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkCore
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkInstrument
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkRouting
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkTransport

/-!
# Resource counts and adjoints for cluster networks

This module derives resource ledgers from the observed Kraus leaves of the concrete wire and CZ
programs. It counts queries, gates, measurements, and feedback bits along valid histories, and
defines a wire-occupancy trace whose peak is `n` for an empty word and `n + 2` otherwise.

It also constructs an adjoint network word by reversing the gate order and replacing each wire
gate with a three-gate word. These implementation-specific counts refine the cluster computation
framework of [RaussendorfBriegel2000].

## Main statements

* `networkWireProgramLeafFields` and `networkCzProgramLeafFields` establish the costs of every
  physical program leaf.
* `cluster_network_actual_leaf_feedback_and_peak_ledger` gives the total query, gate,
  measurement, feedback, and peak-wire ledger.
* `cluster_network_actual_adjoint_word_and_paid_cost` proves legality and matrix correctness of
  the adjoint word and computes its gate counts.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000], *Quantum computing via measurements
  only*.
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ClusterPatterns.WireComposition

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.ClusterPatterns.PauliNetwork

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder

set_option autoImplicit false

/-- The observed Kraus leaf for wire-program outcome `a`, lifted at wire `i` to the network
register of `n + 2` qubits. -/
noncomputable def networkWireLiftedLeaf {n : ℕ} (i : Fin n) (ζ : ℂ) (a : Bool) :
    ObservedKrausLeaf (2 ^ (n + 2)) :=
  networkStepLiftLeaf (eWireFin n i)
    (observedLeaf (1 : Operator 4) (clusterWireProgram ζ) (clusterWireLeaf ζ a))

/-- The observed Kraus leaf for CZ-program outcome pair `(a, d)`, lifted at ordered wires `lo <
hi` to the network register of `n + 2` qubits. -/
noncomputable def networkCzLiftedLeaf {n : ℕ} (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (a d : Bool) : ObservedKrausLeaf (2 ^ (n + 2)) :=
  networkStepLiftLeaf (eCzFin n lo hi h1)
    (observedLeaf (1 : Operator 16) clusterCZProgram (clusterCZLeaf a d))

/-- For a unit-norm phase, every specified lifted wire leaf is accepted and records zero
queries, five gates, and one measurement. -/
theorem networkWireLiftedLeaf_fields {n : ℕ} (i : Fin n) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (a : Bool) :
    (networkWireLiftedLeaf i ζ a).accepted = true ∧
      (networkWireLiftedLeaf i ζ a).queries = 0 ∧
      (networkWireLiftedLeaf i ζ a).gates = 5 ∧
      (networkWireLiftedLeaf i ζ a).measurements = 1 := by
  have h := (cluster_wire_actual_counts ζ hζ).2.2.1 a
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Every specified lifted CZ leaf at ordered distinct wires is accepted and records zero
queries, thirteen gates, and two measurements. -/
theorem networkCzLiftedLeaf_fields {n : ℕ} (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (a d : Bool) :
    (networkCzLiftedLeaf lo hi h1 a d).accepted = true ∧
      (networkCzLiftedLeaf lo hi h1 a d).queries = 0 ∧
      (networkCzLiftedLeaf lo hi h1 a d).gates = 13 ∧
      (networkCzLiftedLeaf lo hi h1 a d).measurements = 2 := by
  have h := (cluster_cz_actual_program_and_feedback_cost).2.2.2.1 a d
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- For a unit-norm phase, every observed Kraus leaf of the physical wire-step program started
from the identity is accepted and records zero queries, five gates, and one measurement. -/
theorem networkWireProgramLeafFields {n : ℕ} (i : Fin n) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (L : ObservedKrausLeaf (2 ^ (n + 2)))
    (hL : L ∈ observedKrausLeaves (1 : Operator (2 ^ (n + 2)))
      (networkPhysicalStepProgram (.inl (i, ζ)))) :
    L.accepted = true ∧ L.queries = 0 ∧ L.gates = 5 ∧ L.measurements = 1 := by
  have hLift : observedKrausLeaves (1 : Operator (2 ^ (n + 2)))
      (networkPhysicalStepProgram (.inl (i, ζ)))
      = (observedKrausLeaves (1 : Operator 4) (clusterWireProgram ζ)).map
          (networkStepLiftLeaf (eWireFin n i)) := by
    have h := observedKrausLeaves_networkStepLift (eWireFin n i) (1 : Operator 4)
      (clusterWireProgram ζ)
    rwa [networkStepLiftGate_one] at h
  rw [hLift, List.mem_map] at hL
  obtain ⟨L₀, hL₀mem, rfl⟩ := hL
  rw [← observedLeaf_ofFn, List.mem_ofFn] at hL₀mem
  obtain ⟨k, rfl⟩ := hL₀mem
  obtain ⟨b, hb⟩ := (cluster_wire_actual_counts ζ hζ).2.2.2.2 k
  subst hb
  have hc := (cluster_wire_actual_counts ζ hζ).2.2.1 b
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩

/-- For distinct endpoints, every observed Kraus leaf of the physical CZ-step program started
from the identity is accepted and records zero queries, thirteen gates, and two
measurements. -/
theorem networkCzProgramLeafFields {n : ℕ} (i j : Fin n) (h : (i : ℕ) ≠ (j : ℕ))
    (L : ObservedKrausLeaf (2 ^ (n + 2)))
    (hL : L ∈ observedKrausLeaves (1 : Operator (2 ^ (n + 2)))
      (networkPhysicalStepProgram (.inr (i, j)))) :
    L.accepted = true ∧ L.queries = 0 ∧ L.gates = 13 ∧ L.measurements = 2 := by
  have hP : networkPhysicalStepProgram (.inr (i, j))
      = networkStepLift
          (eCzFin n (networkCzLo i j) (networkCzHi i j) (networkCzLo_lt_hi i j h))
          clusterCZProgram := dif_pos h
  rw [hP] at hL
  have hLift : observedKrausLeaves (1 : Operator (2 ^ (n + 2)))
      (networkStepLift
          (eCzFin n (networkCzLo i j) (networkCzHi i j) (networkCzLo_lt_hi i j h))
          clusterCZProgram)
      = (observedKrausLeaves (1 : Operator 16) clusterCZProgram).map
          (networkStepLiftLeaf
            (eCzFin n (networkCzLo i j) (networkCzHi i j) (networkCzLo_lt_hi i j h))) :=
    observedKrausLeaves_networkStepLift _ (1 : Operator 16) clusterCZProgram
  rw [hLift, List.mem_map] at hL
  obtain ⟨L₀, hL₀mem, rfl⟩ := hL
  rw [← observedLeaf_ofFn, List.mem_ofFn] at hL₀mem
  obtain ⟨k, rfl⟩ := hL₀mem
  obtain ⟨b, hb⟩ := (cluster_cz_actual_program_and_feedback_cost).2.2.1.2 k
  obtain ⟨a, d⟩ := b
  subst hb
  have hc := (cluster_cz_actual_program_and_feedback_cost).2.2.2.1 a d
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩

/-- The tuple of query, gate, measurement, and feedback-bit costs of a network gate at a given
outcome pair, extracted from its lifted leaf and feedback message. Wire outcomes whose
second bit is true and CZ gates with coincident endpoints are assigned the zero tuple. -/
noncomputable def networkLeafCost {n : ℕ} :
    ClusterNetworkGate n → Bool × Bool → ℕ × ℕ × ℕ × ℕ
  | .inl (i, ζ), (a, false) =>
      ((networkWireLiftedLeaf i ζ a).queries,
        (networkWireLiftedLeaf i ζ a).gates,
        (networkWireLiftedLeaf i ζ a).measurements,
        (clusterWireMessage a).length)
  | .inl (_, _), (_, true) => (0, 0, 0, 0)
  | .inr (i, j), (a, d) =>
      if h : (i : ℕ) ≠ (j : ℕ) then
        ((networkCzLiftedLeaf (networkCzLo i j) (networkCzHi i j)
            (networkCzLo_lt_hi i j h) a d).queries,
          (networkCzLiftedLeaf (networkCzLo i j) (networkCzHi i j)
            (networkCzLo_lt_hi i j h) a d).gates,
          (networkCzLiftedLeaf (networkCzLo i j) (networkCzHi i j)
            (networkCzLo_lt_hi i j h) a d).measurements,
          (clusterCZMessage a d).length)
      else (0, 0, 0, 0)

/-- A wire gate with unit-norm phase and a valid outcome tag has cost tuple `(0, 5, 1, 1)` for
queries, gates, measurements, and feedback bits. -/
theorem networkLeafCost_inl_valid {n : ℕ} (i : Fin n) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (o : Bool × Bool) (ho : o.2 = false) :
    networkLeafCost (.inl (i, ζ)) o = (0, 5, 1, 1) := by
  obtain ⟨a, b⟩ := o
  subst ho
  obtain ⟨_, hq, hg, hm⟩ := networkWireLiftedLeaf_fields i ζ hζ a
  simp only [networkLeafCost, hq, hg, hm]
  simp [clusterWireMessage]

/-- A wire outcome whose second bit is true has the zero cost tuple. -/
theorem networkLeafCost_inl_fake {n : ℕ} (i : Fin n) (ζ : ℂ) (a : Bool) :
    networkLeafCost (.inl (i, ζ)) (a, true) = (0, 0, 0, 0) := rfl

/-- A CZ gate with distinct endpoints has cost tuple `(0, 13, 2, 2)` for every outcome pair,
counting queries, gates, measurements, and feedback bits. -/
theorem networkLeafCost_inr_valid {n : ℕ} (i j : Fin n) (h : (i : ℕ) ≠ (j : ℕ))
    (o : Bool × Bool) :
    networkLeafCost (.inr (i, j)) o = (0, 13, 2, 2) := by
  obtain ⟨a, d⟩ := o
  obtain ⟨_, hq, hg, hm⟩ := networkCzLiftedLeaf_fields (networkCzLo i j) (networkCzHi i j)
    (networkCzLo_lt_hi i j h) a d
  simp only [networkLeafCost, dif_pos h, hq, hg, hm]
  simp [clusterCZMessage]

/-- A CZ gate with coincident endpoints has the zero cost tuple for every outcome pair. -/
theorem networkLeafCost_inr_self {n : ℕ} (i : Fin n) (o : Bool × Bool) :
    networkLeafCost (.inr (i, i)) o = (0, 0, 0, 0) := by
  obtain ⟨a, d⟩ := o
  simp only [networkLeafCost, dif_neg (fun h : (i : ℕ) ≠ (i : ℕ) => h rfl)]

/-- The maximum branch length before halting, counting each circuit step, measurement, or
projection as one and a halt as zero. -/
def networkStepSpan {D : ℕ} : ObservedCircuit (Fin D) → ℕ
  | .halt _ => 0
  | .step _ next => 1 + networkStepSpan next
  | .measure _ _ next => 1 + Finset.univ.sup (fun o => networkStepSpan (next o))
  | .project _ onFalse onTrue => 1 + max (networkStepSpan onFalse) (networkStepSpan onTrue)

/-- The wire-occupancy trace that starts at `n` and records `n + 2` during each physical gate
program, using its maximum branch length for the repeated entries. The empty word has trace
`[n]`. -/
noncomputable def networkWireTrace {n : ℕ} : List (ClusterNetworkGate n) → List ℕ
  | [] => [n]
  | g :: gs => n :: (n + 2) ::
      (List.replicate (networkStepSpan (networkPhysicalStepProgram g)) (n + 2)
        ++ networkWireTrace gs)

/-- Folding maximum over a natural-number list with initial value `b` returns `b` whenever every
list entry is at most `b`. -/
theorem networkFoldl_max_eq_bound : ∀ (b : ℕ) (l : List ℕ), (∀ x ∈ l, x ≤ b) →
    l.foldl max b = b := by
  intro b l
  induction l generalizing b with
  | nil => intro _; rfl
  | cons x l ih =>
    intro h
    rw [List.foldl_cons,
      ih (max b x) (fun y hy =>
        le_trans (h y (List.mem_cons_of_mem _ hy)) (Nat.le_max_left b x)),
      Nat.max_eq_left (h x List.mem_cons_self)]

/-- Every entry of a network word's wire-occupancy trace is at most `n + 2`. -/
theorem networkWireTrace_le {n : ℕ} :
    ∀ (gs : List (ClusterNetworkGate n)) (x : ℕ), x ∈ networkWireTrace gs → x ≤ n + 2 := by
  intro gs
  induction gs with
  | nil =>
    intro x hx
    simp only [networkWireTrace, List.mem_singleton] at hx
    omega
  | cons g gs ih =>
    intro x hx
    simp only [networkWireTrace, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · rcases hx with rfl | hx
      · omega
      · rw [List.mem_append] at hx
        rcases hx with hx | hx
        · have heq : x = n + 2 := (List.mem_replicate.mp hx).2
          omega
        · exact ih x hx

/-- The maximum of a network word's wire-occupancy trace is `n` for the empty word and `n + 2`
for every nonempty word. -/
theorem networkWireTrace_peak {n : ℕ} :
    ∀ (gs : List (ClusterNetworkGate n)),
      (networkWireTrace gs).foldl max 0 = if gs = [] then n else n + 2 := by
  intro gs
  induction gs with
  | nil => simp [networkWireTrace]
  | cons g gs _ih =>
    show (n :: (n + 2) ::
      (List.replicate (networkStepSpan (networkPhysicalStepProgram g)) (n + 2)
        ++ networkWireTrace gs)).foldl max 0 = n + 2
    rw [List.foldl_cons, List.foldl_cons, Nat.zero_max,
      show max n (n + 2) = n + 2 from by omega]
    apply networkFoldl_max_eq_bound
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · have heq : x = n + 2 := (List.mem_replicate.mp hx).2
      omega
    · exact networkWireTrace_le gs x hx

/-- Concatenating two legal network words gives a legal network word. -/
theorem networkLegal_append {n : ℕ} (as bs : List (ClusterNetworkGate n))
    (ha : networkLegal as) (hb : networkLegal bs) : networkLegal (as ++ bs) := by
  intro g hg
  rw [List.mem_append] at hg
  rcases hg with hg | hg
  · exact ha g hg
  · exact hb g hg

/-- The logical matrix of `as ++ bs` is the logical matrix of `bs` multiplied by that of `as`,
matching execution of `as` before `bs`. -/
theorem networkLogicalMatrix_append {n : ℕ} (as bs : List (ClusterNetworkGate n)) :
    networkLogicalMatrix (as ++ bs) = networkLogicalMatrix bs * networkLogicalMatrix as := by
  induction as with
  | nil => simp only [List.nil_append, networkLogicalMatrix, Matrix.mul_one]
  | cons a as ih =>
    rw [List.cons_append]
    show networkLogicalMatrix (as ++ bs) * networkGateMatrix a
        = networkLogicalMatrix bs * networkLogicalMatrix (a :: as)
    rw [ih, Matrix.mul_assoc]
    rfl

/-- Wire-gate and CZ-gate counts add componentwise under concatenation of network words. -/
theorem networkCounts_append {n : ℕ} (as bs : List (ClusterNetworkGate n)) :
    networkCounts (as ++ bs)
      = ((networkCounts as).1 + (networkCounts bs).1,
        (networkCounts as).2 + (networkCounts bs).2) := by
  refine Prod.ext ?_ ?_
  · induction as with
    | nil => simp [networkCounts]
    | cons a as ih =>
      rcases a with ⟨_, _⟩ | ⟨_, _⟩
      all_goals simp only [networkCounts, List.cons_append, ih]
      all_goals omega
  · induction as with
    | nil => simp [networkCounts]
    | cons a as ih =>
      rcases a with ⟨_, _⟩ | ⟨_, _⟩
      all_goals simp only [networkCounts, List.cons_append, ih]
      all_goals omega

/-- If a scalar cost is constant at `wv` on valid wire outcomes with unit-norm phase and at
`czv` on CZ outcomes with distinct endpoints, its sum along any valid history of a legal
word is `wv` times the wire count plus `czv` times the CZ count. -/
theorem networkLedgerGeneric {n : ℕ} (cost : ClusterNetworkGate n → Bool × Bool → ℕ)
    (wv czv : ℕ)
    (hw : ∀ (i : Fin n) (ζ : ℂ), ‖ζ‖ = 1 → ∀ o : Bool × Bool, o.2 = false →
      cost (.inl (i, ζ)) o = wv)
    (hc : ∀ (i j : Fin n), (i : ℕ) ≠ (j : ℕ) → ∀ o : Bool × Bool, cost (.inr (i, j)) o = czv) :
    ∀ (gs : List (ClusterNetworkGate n)), networkLegal gs →
      ∀ (hist : Fin gs.length → Bool × Bool), networkBranchValid gs hist →
      ∑ k, cost (gs.get k) (hist k) = wv * (networkCounts gs).1 + czv * (networkCounts gs).2 := by
  intro gs
  induction gs with
  | nil => intro _ _ _; simp [networkCounts]
  | cons g gs ih =>
    intro hgs hist hval
    have hsplit : ∑ k : Fin (g :: gs).length, cost ((g :: gs).get k) (hist k)
        = cost g (hist 0) + ∑ k : Fin gs.length, cost (gs.get k) (hist k.succ) := by
      show ∑ k : Fin (gs.length + 1), cost ((g :: gs).get k) (hist k)
          = cost g (hist 0) + ∑ k : Fin gs.length, cost (gs.get k) (hist k.succ)
      rw [Fin.sum_univ_succ]
      rfl
    rw [hsplit]
    cases g with
    | inl p =>
      obtain ⟨i, ζ⟩ := p
      have hζ : ‖ζ‖ = 1 := hgs _ List.mem_cons_self
      rw [hw i ζ hζ (hist 0) (hval 0),
        ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (fun k => hist k.succ)
          (fun k => hval k.succ)]
      have h1 : (networkCounts (Sum.inl (i, ζ) :: gs)).1 = (networkCounts gs).1 + 1 := rfl
      have h2 : (networkCounts (Sum.inl (i, ζ) :: gs)).2 = (networkCounts gs).2 := rfl
      rw [h1, h2]
      ring
    | inr p =>
      obtain ⟨i, j⟩ := p
      have hne : (i : ℕ) ≠ (j : ℕ) := by
        intro h
        exact hgs _ List.mem_cons_self (Fin.ext h)
      rw [hc i j hne (hist 0),
        ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (fun k => hist k.succ)
          (fun k => hval k.succ)]
      have h1 : (networkCounts (Sum.inr (i, j) :: gs)).1 = (networkCounts gs).1 := rfl
      have h2 : (networkCounts (Sum.inr (i, j) :: gs)).2 = (networkCounts gs).2 + 1 := rfl
      rw [h1, h2]
      ring


/-- For a legal word with `W` wire gates and `C` CZ gates, every valid history has zero queries,
`5 * W + 13 * C` gates, and `W + 2 * C` measurements and feedback bits, with peak `n` wires
when empty and `n + 2` otherwise. These are the costs of the concrete cluster programs used
here in the measurement-based framework of [RaussendorfBriegel2000]. -/
theorem cluster_network_actual_leaf_feedback_and_peak_ledger :
    ∀ (n : ℕ) (gs : List (ClusterNetworkGate n)) (hgs : networkLegal gs)
      (hist : Fin gs.length → Bool × Bool),
      networkBranchValid gs hist →
      (∑ i, (networkLeafCost (gs.get i) (hist i)).1) = 0 ∧
      (∑ i, (networkLeafCost (gs.get i) (hist i)).2.1) = 5 * (networkCounts gs).1
        + 13 * (networkCounts gs).2 ∧
      (∑ i, (networkLeafCost (gs.get i) (hist i)).2.2.1)
        = (networkCounts gs).1 + 2 * (networkCounts gs).2 ∧
      (∑ i, (networkLeafCost (gs.get i) (hist i)).2.2.2)
        = (networkCounts gs).1 + 2 * (networkCounts gs).2 ∧
      (networkWireTrace gs).foldl max 0 = (if gs = [] then n else n + 2) := by
  intro n gs hgs hist hval
  have hwq : ∀ (i : Fin n) (ζ : ℂ), ‖ζ‖ = 1 → ∀ o : Bool × Bool, o.2 = false →
      (networkLeafCost (.inl (i, ζ)) o).1 = 0 := fun i ζ hζ o ho => by
    rw [networkLeafCost_inl_valid i ζ hζ o ho]
  have hcq : ∀ (i j : Fin n), (i : ℕ) ≠ (j : ℕ) → ∀ o : Bool × Bool,
      (networkLeafCost (.inr (i, j)) o).1 = 0 := fun i j h o => by
    rw [networkLeafCost_inr_valid i j h o]
  have hwg : ∀ (i : Fin n) (ζ : ℂ), ‖ζ‖ = 1 → ∀ o : Bool × Bool, o.2 = false →
      (networkLeafCost (.inl (i, ζ)) o).2.1 = 5 := fun i ζ hζ o ho => by
    rw [networkLeafCost_inl_valid i ζ hζ o ho]
  have hcg : ∀ (i j : Fin n), (i : ℕ) ≠ (j : ℕ) → ∀ o : Bool × Bool,
      (networkLeafCost (.inr (i, j)) o).2.1 = 13 := fun i j h o => by
    rw [networkLeafCost_inr_valid i j h o]
  have hwm : ∀ (i : Fin n) (ζ : ℂ), ‖ζ‖ = 1 → ∀ o : Bool × Bool, o.2 = false →
      (networkLeafCost (.inl (i, ζ)) o).2.2.1 = 1 := fun i ζ hζ o ho => by
    rw [networkLeafCost_inl_valid i ζ hζ o ho]
  have hcm : ∀ (i j : Fin n), (i : ℕ) ≠ (j : ℕ) → ∀ o : Bool × Bool,
      (networkLeafCost (.inr (i, j)) o).2.2.1 = 2 := fun i j h o => by
    rw [networkLeafCost_inr_valid i j h o]
  have hwf : ∀ (i : Fin n) (ζ : ℂ), ‖ζ‖ = 1 → ∀ o : Bool × Bool, o.2 = false →
      (networkLeafCost (.inl (i, ζ)) o).2.2.2 = 1 := fun i ζ hζ o ho => by
    rw [networkLeafCost_inl_valid i ζ hζ o ho]
  have hcf : ∀ (i j : Fin n), (i : ℕ) ≠ (j : ℕ) → ∀ o : Bool × Bool,
      (networkLeafCost (.inr (i, j)) o).2.2.2 = 2 := fun i j h o => by
    rw [networkLeafCost_inr_valid i j h o]
  have h1 := networkLedgerGeneric (fun g o => (networkLeafCost g o).1) 0 0 hwq hcq gs hgs
      hist hval
  have h2 := networkLedgerGeneric (fun g o => (networkLeafCost g o).2.1) 5 13 hwg hcg gs hgs
      hist hval
  have h3 := networkLedgerGeneric (fun g o => (networkLeafCost g o).2.2.1) 1 2 hwm hcm gs
      hgs hist hval
  have h4 := networkLedgerGeneric (fun g o => (networkLeafCost g o).2.2.2) 1 2 hwf hcf gs
      hgs hist hval
  have h1' : ∑ i, (networkLeafCost (gs.get i) (hist i)).1
      = 0 * (networkCounts gs).1 + 0 * (networkCounts gs).2 := h1
  have h2' : ∑ i, (networkLeafCost (gs.get i) (hist i)).2.1
      = 5 * (networkCounts gs).1 + 13 * (networkCounts gs).2 := h2
  have h3' : ∑ i, (networkLeafCost (gs.get i) (hist i)).2.2.1
      = 1 * (networkCounts gs).1 + 2 * (networkCounts gs).2 := h3
  have h4' : ∑ i, (networkLeafCost (gs.get i) (hist i)).2.2.2
      = 1 * (networkCounts gs).1 + 2 * (networkCounts gs).2 := h4
  exact ⟨by rw [h1']; ring, by rw [h2'], by rw [h3']; ring, by rw [h4']; ring,
    networkWireTrace_peak gs⟩

/-- The cluster phase matrix at phase 1 is the identity matrix. -/
theorem networkClusterPhase_one : clusterPhase 1 = 1 := by
  ext i j
  simp only [clusterPhase, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = 0 <;> by_cases hij : i = j <;> simp [h, hij]

/-- The conjugate transpose of the cluster phase matrix at `ζ` is the cluster phase matrix at
its complex conjugate. -/
theorem networkClusterPhase_conjTranspose (ζ : ℂ) :
    (clusterPhase ζ)ᴴ = clusterPhase (star ζ) := by
  unfold clusterPhase
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : i = 0 <;> simp [h]

/-- The product `clusterJ 1 * clusterJ (star ζ) * clusterJ 1` equals the conjugate transpose of
`clusterJ ζ` for every complex phase parameter. -/
theorem networkClusterJ_star_word (ζ : ℂ) :
    clusterJ 1 * clusterJ (star ζ) * clusterJ 1 = (clusterJ ζ)ᴴ := by
  have hH2 : (relabelGate boolEquivFin2 (Hadamard : Matrix Bool Bool ℂ))
        * relabelGate boolEquivFin2 (Hadamard : Matrix Bool Bool ℂ) = 1 := by
    rw [← teleportRelabelGate_mul, hadamard_mul_self, teleportRelabelGate_one]
  have hHstar : (relabelGate boolEquivFin2 (Hadamard : Matrix Bool Bool ℂ))ᴴ
      = relabelGate boolEquivFin2 (Hadamard : Matrix Bool Bool ℂ) := by
    rw [teleportRelabelGate_conjTranspose, hadamard_conjTranspose]
  unfold clusterJ
  rw [networkClusterPhase_one, Matrix.mul_one, ← Matrix.mul_assoc, hH2, Matrix.one_mul,
    Matrix.conjTranspose_mul, networkClusterPhase_conjTranspose, hHstar]

/-- Three wire gates at the same position, with parameters 1, the complex conjugate of `ζ`, and
1, multiply to the conjugate transpose of the wire gate at `ζ`. -/
theorem networkWireGate_star_word {n : ℕ} (i : Fin n) (ζ : ℂ) :
    networkWireGate i 1 * networkWireGate i (star ζ) * networkWireGate i 1
      = (networkWireGate i ζ)ᴴ := by
  unfold networkWireGate
  rw [tensorPauliWireGate_mul, tensorPauliWireGate_mul, tensorPauliWireGate_conjTranspose,
    networkClusterJ_star_word]

/-- The Boolean-register-indexed network CZ matrix equals its conjugate transpose. -/
theorem networkCzGateB_conjTranspose {n : ℕ} (i j : Fin n) :
    (networkCzGateB i j)ᴴ = networkCzGateB i j := by
  unfold networkCzGateB
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  cases h1 : x i <;> cases h2 : x j <;> simp [h1, h2]

/-- The Boolean-register-indexed network CZ matrix squares to the identity. -/
theorem networkCzGateB_mul_self {n : ℕ} (i j : Fin n) :
    networkCzGateB i j * networkCzGateB i j = 1 := by
  unfold networkCzGateB
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  cases x i <;> cases x j <;> simp

/-- The network CZ matrix squares to the identity. -/
theorem networkCzGate_mul_self {n : ℕ} (i j : Fin n) :
    networkCzGate i j * networkCzGate i j = 1 := by
  unfold networkCzGate
  rw [← teleportRelabelGate_mul, networkCzGateB_mul_self, teleportRelabelGate_one]

/-- The network CZ matrix equals its conjugate transpose. -/
theorem networkCzGate_conjTranspose {n : ℕ} (i j : Fin n) :
    (networkCzGate i j)ᴴ = networkCzGate i j := by
  unfold networkCzGate
  rw [teleportRelabelGate_conjTranspose, networkCzGateB_conjTranspose]

/-- The network word obtained by reversing gate order, replacing each wire gate at `ζ` with wire
gates at 1, `star ζ`, and 1, and retaining each CZ gate. -/
noncomputable def networkAdjointWord {n : ℕ} :
    List (ClusterNetworkGate n) → List (ClusterNetworkGate n)
  | [] => []
  | .inl (i, ζ) :: gs =>
      networkAdjointWord gs ++ [.inl (i, (1 : ℂ)), .inl (i, star ζ), .inl (i, (1 : ℂ))]
  | .inr (i, j) :: gs => networkAdjointWord gs ++ [.inr (i, j)]

/-- The logical matrix of the three-wire-gate word with parameters 1, `star ζ`, and 1 is the
conjugate transpose of the original wire-gate matrix. -/
theorem networkLogicalMatrix_word3 {n : ℕ} (i : Fin n) (ζ : ℂ) :
    networkLogicalMatrix [.inl (i, (1 : ℂ)), .inl (i, star ζ), .inl (i, (1 : ℂ))]
      = (networkGateMatrix (.inl (i, ζ)))ᴴ := by
  show ((1 : Operator (2 ^ n)) * networkWireGate i (1 : ℂ)) * networkWireGate i (star ζ)
      * networkWireGate i (1 : ℂ) = (networkWireGate i ζ)ᴴ
  rw [Matrix.one_mul, networkWireGate_star_word]

/-- For every legal network word, `networkAdjointWord` is legal and its logical matrix is the
conjugate transpose of the original, with three times the wire-gate count and the same
CZ-gate count. This records the explicit adjoint-word overhead for the cluster
implementation in the setting of [RaussendorfBriegel2000]. -/
theorem cluster_network_actual_adjoint_word_and_paid_cost :
    ∀ (n : ℕ) (gs : List (ClusterNetworkGate n)), networkLegal gs →
      networkLegal (networkAdjointWord gs) ∧
      networkLogicalMatrix (networkAdjointWord gs) = (networkLogicalMatrix gs)ᴴ ∧
      networkCounts (networkAdjointWord gs) = (3 * (networkCounts gs).1, (networkCounts gs).2) := by
  intro n gs
  induction gs with
  | nil =>
    intro _
    refine ⟨fun g hg => by simp [networkAdjointWord] at hg, ?_, ?_⟩
    · simp only [networkAdjointWord, networkLogicalMatrix, Matrix.conjTranspose_one]
    · simp only [networkAdjointWord, networkCounts]
  | cons g gs ih =>
    intro hgs
    have ih' := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hleg, hmat, hcnt⟩ := ih'
    obtain ⟨i, ζ⟩ | ⟨i, j⟩ := g
    · have hζ : ‖ζ‖ = 1 := hgs _ List.mem_cons_self
      have e1 : networkAdjointWord (Sum.inl (i, ζ) :: gs)
          = networkAdjointWord gs
              ++ [.inl (i, (1 : ℂ)), .inl (i, star ζ), .inl (i, (1 : ℂ))] := rfl
      refine ⟨networkLegal_append _ _ hleg (by
        intro g' hg'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl
        · simp
        · show ‖star ζ‖ = 1
          rw [norm_star]
          exact hζ
        · simp), ?_, ?_⟩
      · rw [e1, networkLogicalMatrix_append, hmat, networkLogicalMatrix_word3]
        have hL : networkLogicalMatrix (Sum.inl (i, ζ) :: gs)
            = networkLogicalMatrix gs * networkGateMatrix (Sum.inl (i, ζ)) := rfl
        rw [hL, Matrix.conjTranspose_mul]
      · have e2 : networkCounts (networkAdjointWord (Sum.inl (i, ζ) :: gs))
            = ((networkCounts (networkAdjointWord gs)).1 + 3,
              (networkCounts (networkAdjointWord gs)).2 + 0) := by
          rw [e1, networkCounts_append]
          rfl
        have hc1 : (networkCounts (Sum.inl (i, ζ) :: gs)).1
            = (networkCounts gs).1 + 1 := rfl
        have hc2 : (networkCounts (Sum.inl (i, ζ) :: gs)).2 = (networkCounts gs).2 := rfl
        rw [e2, hcnt, hc1, hc2]
        exact Prod.ext (by ring) (by ring)
    · have hne : i ≠ j := hgs _ List.mem_cons_self
      have e1 : networkAdjointWord (Sum.inr (i, j) :: gs)
          = networkAdjointWord gs ++ [.inr (i, j)] := rfl
      refine ⟨networkLegal_append _ _ hleg (by
        intro g' hg'
        simp only [List.mem_singleton] at hg'
        subst hg'
        exact hne), ?_, ?_⟩
      · rw [e1, networkLogicalMatrix_append, hmat, networkLogicalMatrix_cons]
        have hL : networkLogicalMatrix (Sum.inr (i, j) :: gs)
            = networkLogicalMatrix gs * networkCzGate i j := rfl
        rw [hL, Matrix.conjTranspose_mul, networkCzGate_conjTranspose]
        rfl
      · have e2 : networkCounts (networkAdjointWord (Sum.inr (i, j) :: gs))
            = ((networkCounts (networkAdjointWord gs)).1 + 0,
              (networkCounts (networkAdjointWord gs)).2 + 1) := by
          rw [e1, networkCounts_append]
          rfl
        have hc1 : (networkCounts (Sum.inr (i, j) :: gs)).1 = (networkCounts gs).1 := rfl
        have hc2 : (networkCounts (Sum.inr (i, j) :: gs)).2
            = (networkCounts gs).2 + 1 := rfl
        rw [e2, hcnt, hc1, hc2]
        exact Prod.ext (by ring) (by ring)

end Qatlib.Concepts.ClusterPatterns.PauliNetwork
