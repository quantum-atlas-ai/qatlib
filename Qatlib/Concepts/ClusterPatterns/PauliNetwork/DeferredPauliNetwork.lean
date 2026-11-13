/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.PauliNetwork.CountedClusterNetwork
import Qatlib.Concepts.ClusterPatterns.PauliNetwork.ClusterNetworkConsumers
import Qatlib.Concepts.GateVocabulary.LocalReflectionGates

/-!
# Deferred Pauli corrections in cluster networks

This module defines `PauliFrame`, the outcome-dependent update `frameUpdate`, and the
uncorrected measurement branches `rawNetworkStepBranch` and `deferredHistoryBranch`. These
constructions track the Pauli factors produced by the cluster measurement scheme of
[RaussendorfBriegel2000] while adjusting subsequent wire parameters.

For legal networks acting on inputs carrying the initial Pauli frame, the branch formulas
express every valid history as a weighted conjugation by the logical matrix followed by its
final Pauli frame; invalid histories give zero. `frameCorrectionSteps` realizes the inverse
final frame with local Pauli gates, and the cost lemmas count the raw measurements, messages,
and terminal correction gates.

## Main statements

* `deferred_pauli_actual_raw_step_frame_transport`: transport a Pauli frame through one legal
  measurement step.
* `deferred_pauli_actual_history_linear_branch`: express a full history using its logical matrix
  and final frame.
* `deferredCorrectedBranch_eq`: remove the final frame from a history branch.
* `deferred_pauli_terminal_correction_actual_local_cost`: realize the inverse frame using at
  most `2 * n` local gates.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ClusterPatterns.WireComposition
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- A pair of Boolean registers recording the local Pauli X and Z exponents on `n` wires. -/
abbrev PauliFrame (n : ℕ) := Reg n×Reg n

/-- The Pauli frame with every X and Z exponent equal to `false`. -/
def zeroPauliFrame (n : ℕ) : PauliFrame n := (fun _=>false,fun _=>false)

/-- The tensor product of the local X-times-Z Pauli factors selected by `F.1` and `F.2`, indexed
by `Fin (2 ^ n)`. -/
noncomputable def pauliFrameGate (n : ℕ) (F : PauliFrame n) : Operator (2^n) :=
 relabelGate (bitVecEquiv n) (pauliProductDensity (fun i=>
  relabelGate boolEquivFin2 ((if F.1 i then PauliX else 1)*(if F.2 i then PauliZ else 1))))

/-- Adjust a wire gate by conjugating its complex parameter when the current X frame bit is set;
a CZ gate retains its endpoints. -/
noncomputable def frameAdjustedGate {n : ℕ} (F : PauliFrame n) : ClusterNetworkGate n→ClusterNetworkGate n
 | .inl (i,ζ) => .inl (i,if F.1 i then star ζ else ζ)
 | .inr (i,j) => .inr (i,j)

/-- Update the X and Z frame registers after a wire or CZ step with the given pair of
measurement outcomes. -/
def frameUpdate {n : ℕ} (F : PauliFrame n) : ClusterNetworkGate n→(Bool×Bool)→PauliFrame n
 | .inl (i,_),o => (Function.update F.1 i (o.1 ^^ F.2 i),Function.update F.2 i (F.1 i))
 | .inr (i,j),o =>
   let lo := networkCzLo i j
   let hi := networkCzHi i j
   (fun k=>if k=lo then F.1 k ^^ o.1 else if k=hi then F.1 k ^^ o.2 else F.1 k,
    fun k=>if k=lo then (F.2 k ^^ F.1 hi) ^^ o.2
           else if k=hi then (F.2 k ^^ F.1 lo) ^^ o.1 else F.2 k)

/-- Propagate an initial Pauli frame through a gate list by applying `frameUpdate` along the
outcome history. -/
def finalPauliFrame {n : ℕ} : (gs : List (ClusterNetworkGate n))→
 (Fin gs.length→Bool×Bool)→PauliFrame n→PauliFrame n
 | [],_,F => F
 | g::gs,hist,F => finalPauliFrame gs (fun k=>hist k.succ) (frameUpdate F g (hist 0))

/-- The observed cluster wire circuit consisting of four gates and one binary measurement,
terminating without an outcome-dependent correction. -/
noncomputable def uncorrectedWireProgram (ζ : ℂ) : ObservedCircuit (Fin 4) :=
 .step (.gate clusterWireHbGate) (.step (.gate (clusterWirePhaseGate ζ))
  (.step (.gate clusterCZ) (.step (.gate clusterWireHaGate)
   (.measure 2 clusterAliceLabel (fun _=>.halt true)))))

/-- The observed cluster CZ circuit consisting of nine gates and two binary measurements,
terminating without outcome-dependent corrections. -/
noncomputable def uncorrectedCZProgram : ObservedCircuit (Fin 16) :=
 .step (.gate clusterCZHaGate) (.step (.gate clusterCZHdGate)
  (.step (.gate clusterCZHbGate) (.step (.gate clusterCZHcGate)
   (.step (.gate clusterCZEdgeAbGate) (.step (.gate clusterCZEdgeDcGate)
    (.step (.gate clusterCZEdgeBcGate) (.step (.gate clusterCZHaGate)
     (.step (.gate clusterCZHdGate)
      (.measure 2 clusterCZLabelA (fun _=>.measure 2 clusterCZLabelD (fun _=>.halt true)))))))))))

/-- Lift the outcome-`a` leaf of `uncorrectedWireProgram` at wire `i` to an operator on the `n +
2` network wires. -/
noncomputable def rawNetworkWireLeaf (n : ℕ) (i : Fin n) (ζ : ℂ) (a : Bool) : Operator (2^(n+2)) :=
 (networkStepLiftLeaf (eWireFin n i)
  (observedLeaf 1 (uncorrectedWireProgram ζ) (Fin.cast (by rfl) (boolEquivFin2 a)))).operator

/-- Lift the outcome-`(a, d)` leaf of `uncorrectedCZProgram` at ordered endpoints `lo < hi` to
the `n + 2` network wires. -/
noncomputable def rawNetworkCZLeaf (n : ℕ) (lo hi : Fin n) (h : (lo:ℕ)<hi)
 (a d : Bool) : Operator (2^(n+2)) :=
 (networkStepLiftLeaf (eCzFin n lo hi h)
  (observedLeaf 1 uncorrectedCZProgram (Fin.cast (by rfl) (teleportOutcomeEquiv (a,d))))).operator

/-- The uncorrected operator map obtained by loading the network frame, applying the selected
measurement leaf, and tracing out the auxiliary factor. Wire outcomes with a true second bit
and CZ steps with coincident endpoints give zero. -/
noncomputable def rawNetworkStepCore {n : ℕ} : ClusterNetworkGate n→Bool×Bool→Operator (2^n)→Operator (2^n)
 | .inl (i,ζ),o,ρ => if o.2 then 0 else
   Matrix.traceLeft (relabelGate (eWireOutFin n i).symm
    (rawNetworkWireLeaf n i ζ o.1 * (networkFrame n * ρ * (networkFrame n)ᴴ) *
     (rawNetworkWireLeaf n i ζ o.1)ᴴ))
 | .inr (i,j),o,ρ => if h : (i:ℕ)≠j then
   Matrix.traceLeft (relabelGate (eCzOutFin n (networkCzLo i j) (networkCzHi i j)
     (networkCzLo_lt_hi i j h)).symm
    (rawNetworkCZLeaf n (networkCzLo i j) (networkCzHi i j) (networkCzLo_lt_hi i j h) o.1 o.2 *
     (networkFrame n * ρ * (networkFrame n)ᴴ) *
     (rawNetworkCZLeaf n (networkCzLo i j) (networkCzHi i j) (networkCzLo_lt_hi i j h) o.1 o.2)ᴴ))
   else 0

/-- Compose the raw step maps along a history, adjusting each gate to the current Pauli frame
and updating that frame after the step. -/
noncomputable def deferredHistoryCore {n : ℕ} : (gs : List (ClusterNetworkGate n))→
 (Fin gs.length→Bool×Bool)→PauliFrame n→Operator (2^n)→Operator (2^n)
 | [],_,_,ρ => ρ
 | g::gs,hist,F,ρ => deferredHistoryCore gs (fun k=>hist k.succ)
   (frameUpdate F g (hist 0)) (rawNetworkStepCore (frameAdjustedGate F g) (hist 0) ρ)

/-- The list of local Pauli X and Z gates selected by the frame bits, ordered by wire with X
preceding Z on each wire. -/
noncomputable def frameCorrectionSteps {n : ℕ} (F : PauliFrame n) : List (ReflectionGate n) :=
 (List.ofFn (fun i : Fin n=>
  (if F.1 i then [Sum.inl (i,PauliX)] else []) ++
  (if F.2 i then [Sum.inl (i,PauliZ)] else []))).flatten

/-- The total number of true X and Z frame bits, counting the local Pauli gates needed for the
terminal correction. -/
def frameCorrectionCost {n : ℕ} (F : PauliFrame n) : ℕ :=
 ∑i,((if F.1 i then 1 else 0)+(if F.2 i then 1 else 0))

/-- The query, gate, measurement, and message-bit counts of the selected uncorrected network
leaf. Invalid wire outcomes and CZ steps with coincident endpoints receive the zero tuple. -/
noncomputable def rawNetworkStepCost {n : ℕ} : ClusterNetworkGate n→Bool×Bool→ℕ×ℕ×ℕ×ℕ
 | .inl (i,ζ),o => if o.2 then (0,0,0,0) else
   let L := networkStepLiftLeaf (eWireFin n i)
      (observedLeaf 1 (uncorrectedWireProgram ζ) (Fin.cast (by rfl) (boolEquivFin2 o.1)))
   (L.queries,L.gates,L.measurements,(clusterWireMessage o.1).length)
 | .inr (i,j),o => if h : (i:ℕ)≠j then
   let L := networkStepLiftLeaf (eCzFin n (networkCzLo i j) (networkCzHi i j) (networkCzLo_lt_hi i j h))
      (observedLeaf 1 uncorrectedCZProgram (Fin.cast (by rfl) (teleportOutcomeEquiv o)))
   (L.queries,L.gates,L.measurements,(clusterCZMessage o.1 o.2).length)
   else (0,0,0,0)

/-- Accumulate the four raw resource counts along a history while adjusting gates and
propagating the Pauli frame. -/
noncomputable def deferredRawPathCost {n : ℕ} : (gs : List (ClusterNetworkGate n))→
 (Fin gs.length→Bool×Bool)→PauliFrame n→ℕ×ℕ×ℕ×ℕ
 | [],_,_ => (0,0,0,0)
 | g::gs,hist,F =>
   let s := rawNetworkStepCost (frameAdjustedGate F g) (hist 0)
   let t := deferredRawPathCost gs (fun k=>hist k.succ) (frameUpdate F g (hist 0))
   (s.1+t.1,s.2.1+t.2.1,s.2.2.1+t.2.2.1,s.2.2.2+t.2.2.2)

/-- The raw history cost with the length of the final frame correction added to its gate count. -/
noncomputable def deferredPathCost {n : ℕ} (gs : List (ClusterNetworkGate n))
 (hist : Fin gs.length→Bool×Bool) (F : PauliFrame n) : ℕ×ℕ×ℕ×ℕ :=
 let c := deferredRawPathCost gs hist F
 (c.1,c.2.1+(frameCorrectionSteps (finalPauliFrame gs hist F)).length,c.2.2.1,c.2.2.2)

/-- Package `rawNetworkStepCore` as a complex-linear map on operators for the specified gate and
outcome. -/
noncomputable def rawNetworkStepBranch {n : ℕ} (g : ClusterNetworkGate n) (o : Bool × Bool) :
    Operator (2 ^ n) →ₗ[ℂ] Operator (2 ^ n) where
  toFun := rawNetworkStepCore g o
  map_add' := by
    intro ρ σ
    cases g with
    | inl p =>
      obtain ⟨i, ζ⟩ := p
      by_cases ho : o.2
      · simp [rawNetworkStepCore, ho]
      · simp only [rawNetworkStepCore, if_neg ho, Matrix.mul_add, Matrix.add_mul,
          relabelGate_add', traceLeft_add]
    | inr p =>
      obtain ⟨i, j⟩ := p
      by_cases hv : (i : ℕ) ≠ (j : ℕ)
      · simp only [rawNetworkStepCore, dif_pos hv, Matrix.mul_add, Matrix.add_mul,
          relabelGate_add', traceLeft_add]
      · simp [rawNetworkStepCore, hv]
  map_smul' := by
    intro r ρ
    cases g with
    | inl p =>
      obtain ⟨i, ζ⟩ := p
      by_cases ho : o.2
      · simp [rawNetworkStepCore, ho]
      · simp only [rawNetworkStepCore, if_neg ho, Matrix.mul_smul, Matrix.smul_mul,
          relabelGate_smul', traceLeft_smul, RingHom.id_apply]
    | inr p =>
      obtain ⟨i, j⟩ := p
      by_cases hv : (i : ℕ) ≠ (j : ℕ)
      · simp only [rawNetworkStepCore, dif_pos hv, Matrix.mul_smul, Matrix.smul_mul,
          relabelGate_smul', traceLeft_smul, RingHom.id_apply]
      · simp [rawNetworkStepCore, hv]

/-- The complex-linear history map obtained by composing frame-adjusted raw step branches and
propagating the initial Pauli frame. -/
noncomputable def deferredHistoryBranch {n : ℕ} :
    (gs : List (ClusterNetworkGate n)) → (Fin gs.length → Bool × Bool) →
    PauliFrame n → Operator (2 ^ n) →ₗ[ℂ] Operator (2 ^ n)
  | [], _, _ => LinearMap.id
  | g :: gs, hist, F =>
      (deferredHistoryBranch gs (fun k => hist k.succ) (frameUpdate F g (hist 0))).comp
        (rawNetworkStepBranch (frameAdjustedGate F g) (hist 0))

/-- Evaluating the linear history branch agrees with the recursively defined
`deferredHistoryCore` on every operator. -/
theorem deferredHistoryBranch_apply {n : ℕ} (gs : List (ClusterNetworkGate n))
    (hist : Fin gs.length → Bool × Bool) (F : PauliFrame n) (ρ : Operator (2 ^ n)) :
    deferredHistoryBranch gs hist F ρ = deferredHistoryCore gs hist F ρ := by
  induction gs generalizing F ρ with
  | nil => rfl
  | cons g gs ih =>
      exact ih (fun k => hist k.succ) (frameUpdate F g (hist 0))
        (rawNetworkStepCore (frameAdjustedGate F g) (hist 0) ρ)

/-- The correction block on one wire has matrix equal to the local Z choice multiplied by the
local X choice, embedded at that wire. -/
theorem frameCorrectionBlock_matrix {n : ℕ} (F : PauliFrame n) (i : Fin n) :
    reflectionProgramMatrix
      ((if F.1 i then [Sum.inl (i, PauliX)] else []) ++
       (if F.2 i then [Sum.inl (i, PauliZ)] else [])) =
      wireGate n i ((if F.2 i then PauliZ else 1) *
        (if F.1 i then PauliX else 1)) := by
  cases hx : F.1 i <;> cases hz : F.2 i <;>
    simp [reflectionProgramMatrix, reflectionGateMatrix, hx, hz,
      wireGate_one, wireGate_mul]

/-- Every terminal frame correction list satisfies `reflectionLegal`. -/
theorem frameCorrectionSteps_legal {n : ℕ} (F : PauliFrame n) :
    reflectionLegal (frameCorrectionSteps F) := by
  intro g hg
  simp only [frameCorrectionSteps, List.mem_flatten, List.mem_ofFn] at hg
  obtain ⟨_, ⟨i, rfl⟩, hg⟩ := hg
  cases hx : F.1 i <;> cases hz : F.2 i <;>
    simp [hx, hz] at hg
  all_goals rcases hg with rfl | rfl <;>
    simp only [reflectionGateLegal] <;> first | exact pauliX_unitary | exact pauliZ_unitary

/-- The number of gates in `frameCorrectionSteps` equals `frameCorrectionCost`. -/
theorem frameCorrectionSteps_length {n : ℕ} (F : PauliFrame n) :
    (frameCorrectionSteps F).length = frameCorrectionCost F := by
  simp only [frameCorrectionSteps, List.length_flatten, List.map_ofFn,
    List.length_append]
  simp only [List.sum_ofFn, frameCorrectionCost, List.length_append]
  apply Finset.sum_congr rfl
  intro i _
  cases hx : F.1 i <;> cases hz : F.2 i <;> simp [hx, hz]

/-- Correcting a Pauli frame on `n` wires requires at most `2 * n` local Pauli gates. -/
theorem frameCorrectionCost_le {n : ℕ} (F : PauliFrame n) :
    frameCorrectionCost F ≤ 2 * n := by
  calc
    frameCorrectionCost F ≤ ∑ _i : Fin n, 2 := by
      apply Finset.sum_le_sum
      intro i _
      cases hx : F.1 i <;> cases hz : F.2 i <;> simp [hx, hz]
    _ = 2 * n := by simp [Nat.mul_comm]

/-- For a list of distinct wires, the product of their correction blocks equals the reindexed
tensor product of their local Z-times-X factors, with identity on unlisted wires. -/
theorem frameCorrectionList_matrix {n : ℕ} (F : PauliFrame n) (is : List (Fin n))
    (his : is.Nodup) :
    reflectionProgramMatrix (is.flatMap (fun i =>
      (if F.1 i then [Sum.inl (i, PauliX)] else []) ++
      (if F.2 i then [Sum.inl (i, PauliZ)] else []))) =
      relabelGate (bitVecEquiv n).symm (tensorPauliProduct n (fun i =>
        if i ∈ is then relabelGate boolEquivFin2
          ((if F.2 i then PauliZ else 1) * (if F.1 i then PauliX else 1)) else 1)) := by
  induction is with
  | nil => simp [reflectionProgramMatrix, tensorPauliProduct_one, teleportRelabelGate_one]
  | cons i is ih =>
      rw [List.nodup_cons] at his
      rw [List.flatMap_cons, reflectionProgramMatrix_append, ih his.2,
        frameCorrectionBlock_matrix]
      simp only [wireGate, ← teleportRelabelGate_mul, tensorPauliWireGate,
        tensorPauliProduct_mul]
      congr 2
      funext j
      by_cases hji : j = i
      · subst j
        simp [his.1]
      · simp [hji]

/-- The matrix of the complete terminal correction list is the conjugate transpose of
`pauliFrameGate`, reindexed to Boolean registers. -/
theorem frameCorrectionSteps_matrix {n : ℕ} (F : PauliFrame n) :
    reflectionProgramMatrix (frameCorrectionSteps F) =
      relabelGate (bitVecEquiv n).symm ((pauliFrameGate n F)ᴴ) := by
  have hm := frameCorrectionList_matrix F (List.ofFn (fun i : Fin n => i))
    (List.nodup_ofFn.mpr Function.injective_id)
  simp only [frameCorrectionSteps, List.flatMap, List.map_ofFn, Function.comp_def] at *
  rw [hm]
  simp only [List.mem_ofFn, exists_apply_eq_apply, if_true]
  unfold tensorPauliProduct pauliFrameGate
  rw [teleportRelabelGate_conjTranspose, pauliProductDensity_conjTranspose]
  congr 3
  funext i
  rw [teleportRelabelGate_conjTranspose, Matrix.conjTranspose_mul]
  cases hx : F.1 i <;> cases hz : F.2 i <;>
    simp [hx, hz, pauliX_conjTranspose, pauliZ_conjTranspose]

/-- The terminal correction list is legal, has length `frameCorrectionCost F ≤ 2 * n`, and its
compiled circuit acts by the reindexed conjugate transpose of the frame operator on every
state. -/
theorem deferred_pauli_terminal_correction_actual_local_cost :
    ∀ (n : ℕ) (F : PauliFrame n),
      reflectionLegal (frameCorrectionSteps F) ∧
      (frameCorrectionSteps F).length = frameCorrectionCost F ∧
      frameCorrectionCost F ≤ 2 * n ∧
      (∀ ψ : QState (Reg n), Run (1 : Matrix (Reg n) (Reg n) ℂ)
        (reflectionCompile (frameCorrectionSteps F)) ψ =
        relabelGate (bitVecEquiv n).symm ((pauliFrameGate n F)ᴴ) *ᵥ ψ) := by
  intro n F
  refine ⟨frameCorrectionSteps_legal F, frameCorrectionSteps_length F,
    frameCorrectionCost_le F, ?_⟩
  intro ψ
  rw [run_reflectionCompile, frameCorrectionSteps_matrix]
  rfl

/-- A valid uncorrected wire step uses zero queries, four gates, one measurement, and one
message bit. -/
theorem rawNetworkWireCost (n : ℕ) (i : Fin n) (ζ : ℂ) (a : Bool) :
    rawNetworkStepCost (.inl (i, ζ)) (a, false) = (0, 4, 1, 1) := by
  cases a <;> rfl

/-- An uncorrected CZ step on distinct wires uses zero queries, nine gates, two measurements,
and two message bits. -/
theorem rawNetworkCZCost (n : ℕ) (i j : Fin n) (h : i ≠ j) (a d : Bool) :
    rawNetworkStepCost (.inr (i, j)) (a, d) = (0, 9, 2, 2) := by
  have hv : (i : ℕ) ≠ (j : ℕ) := fun hv => h (Fin.ext hv)
  simp only [rawNetworkStepCost, dif_pos hv]
  cases a <;> cases d <;> rfl

/-- For a legal network and valid history, the raw path cost is `(0, 4 * u + 9 * c, u + 2 * c, u
+ 2 * c)`, where `u` and `c` are its wire and CZ counts, for every initial frame. -/
theorem deferredRawPathCost_eq {n : ℕ} (gs : List (ClusterNetworkGate n))
    (hist : Fin gs.length → Bool × Bool) (F : PauliFrame n)
    (hgs : networkLegal gs) (hh : networkBranchValid gs hist) :
    deferredRawPathCost gs hist F =
      (0, 4 * (networkCounts gs).1 + 9 * (networkCounts gs).2,
        (networkCounts gs).1 + 2 * (networkCounts gs).2,
        (networkCounts gs).1 + 2 * (networkCounts gs).2) := by
  induction gs generalizing F with
  | nil => rfl
  | cons g gs ih =>
      have hg := networkLegal_cons_self g gs hgs
      have ht := networkLegal_cons_of g gs hgs
      rw [networkBranchValid_cons] at hh
      simp only [deferredRawPathCost]
      rw [ih (fun k => hist k.succ) (frameUpdate F g (hist 0)) ht hh.2]
      cases g with
      | inl p =>
          obtain ⟨i, ζ⟩ := p
          have ho : (hist 0).2 = false := by
            simpa [networkBranchValid] using hh.1 (0 : Fin 1)
          rcases he : hist 0 with ⟨a, d⟩
          rw [he] at ho
          change d = false at ho
          subst d
          rw [frameAdjustedGate, rawNetworkWireCost]
          simp [networkCounts]
          omega
      | inr p =>
          obtain ⟨i, j⟩ := p
          have hij : i ≠ j := hg (.inr (i, j)) (by simp)
          rcases he : hist 0 with ⟨a, d⟩
          rw [frameAdjustedGate, rawNetworkCZCost n i j hij]
          simp [networkCounts]
          omega

/-- The two-qubit leaf operator for outcome `a` of the uncorrected wire circuit with parameter
`ζ`. -/
noncomputable def rawWireSmallLeaf (ζ : ℂ) (a : Bool) : Operator 4 :=
  (observedLeaf 1 (uncorrectedWireProgram ζ) (Fin.cast (by rfl) (boolEquivFin2 a))).operator

/-- The corrected wire leaf equals the uncorrected leaf followed by the outcome-dependent X
feedback operator. -/
theorem correctedWireLeaf_eq (ζ : ℂ) (a : Bool) :
    networkWireSmallLeafOp ζ a = clusterWireXbGate a * rawWireSmallLeaf ζ a := by
  have hr : rawWireSmallLeaf ζ a =
      (((((1 : Operator 4) * Projector (Finset.univ.filter
        (fun i => clusterAliceLabel i = boolEquivFin2 a))) * clusterWireHaGate) *
        clusterCZ) * clusterWirePhaseGate ζ) * clusterWireHbGate := by
    cases a <;> rfl
  rw [networkWireSmallLeafOp, clusterWireLeafOperator_eq, hr]
  simp only [Equiv.symm_apply_apply, Matrix.one_mul, Matrix.mul_assoc]

/-- The outcome-dependent wire X feedback operator squares to the identity. -/
theorem wireFeedback_square (a : Bool) :
    clusterWireXbGate a * clusterWireXbGate a = 1 := by
  unfold clusterWireXbGate clusterWireXbB
  rw [← teleportRelabelGate_mul, tensorGate_mul]
  cases a <;> simp [PauliX, permMatrix_mul_self Bool.not_not, teleportRelabelGate_one,
      tensorGate_one]

/-- The uncorrected wire leaf is recovered by multiplying the corrected leaf on the left by the
X feedback operator. -/
theorem rawWireSmallLeaf_eq (ζ : ℂ) (a : Bool) :
    rawWireSmallLeaf ζ a = clusterWireXbGate a * networkWireSmallLeafOp ζ a := by
  rw [correctedWireLeaf_eq, ← Matrix.mul_assoc, wireFeedback_square, Matrix.one_mul]

/-- On a basis input with a false auxiliary bit, the reindexed raw wire leaf fixes the measured
bit to `a` and applies `pauliXChoice a * clusterJ ζ` to the output with amplitude factor `1
/ √2`. -/
theorem rawWireSmallLeaf_column (ζ : ℂ) (a bb : Bool) :
    (relabelGate teleportOutcomeEquiv.symm (rawWireSmallLeaf ζ a)) *ᵥ Qatlib.Foundations.PureStateMath.Ket (bb, false) =
      (fun q : Bool × Bool => if q.1 = a then ((Real.sqrt 2 : ℂ)⁻¹) *
        (pauliXChoice a * clusterJ ζ) (boolEquivFin2 q.2) (boolEquivFin2 bb) else 0) := by
  rw [rawWireSmallLeaf_eq, teleportRelabelGate_mul]
  change ApplyGate _ (Qatlib.Foundations.PureStateMath.Ket (bb, false)) = _
  rw [applyGate_mul, networkWireSmallLeaf_apply]
  have hx : relabelGate teleportOutcomeEquiv.symm (clusterWireXbGate a) = clusterWireXbB a := by
    unfold clusterWireXbGate
    exact relabelGate_relabelGate _ _
  rw [hx, clusterWireXbB_apply]
  funext q
  obtain ⟨b, c⟩ := q
  cases a <;> cases b <;> cases c <;> cases bb <;>
    simp [pauliXChoice, Matrix.mul_apply, Fin.sum_univ_two, PauliX, permMatrix,
      relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, boolEquivFin2]

/-- The Boolean-register tensor operator acting by `pauliXChoice a * clusterJ ζ` on wire `i` and
by identity on the other wires. -/
noncomputable def rawNetworkWireGateB {n : ℕ} (i : Fin n) (ζ : ℂ) (a : Bool) :
    Matrix (Reg n) (Reg n) ℂ :=
  pauliProductDensity (fun j => if j = i then pauliXChoice a * clusterJ ζ else 1)
/-- The operator `pauliXChoice a * clusterJ ζ` embedded on wire `i`, indexed by `Fin (2 ^ n)`. -/
noncomputable def rawNetworkWireGate {n : ℕ} (i : Fin n) (ζ : ℂ) (a : Bool) : Operator (2 ^ n) :=
  tensorPauliWireGate n i (pauliXChoice a * clusterJ ζ)

/-- The Boolean-register raw wire operator is the reindexing of `rawNetworkWireGate` along the
inverse bit-vector equivalence. -/
theorem rawNetworkWireGateB_eq {n : ℕ} (i : Fin n) (ζ : ℂ) (a : Bool) :
    rawNetworkWireGateB i ζ a = relabelGate (bitVecEquiv n).symm (rawNetworkWireGate i ζ a) := by
  unfold rawNetworkWireGateB rawNetworkWireGate tensorPauliWireGate tensorPauliProduct
  rw [relabelGate_relabelGate]

/-- Each raw wire matrix entry is the local entry on wire `i` multiplied by Kronecker delta
factors on all other wires. -/
theorem rawNetworkWireGateB_apply (n : ℕ) (i : Fin n) (ζ : ℂ) (a : Bool) (w v : Reg n) :
    rawNetworkWireGateB i ζ a w v
      = (pauliXChoice a * clusterJ ζ) (boolEquivFin2 (w i)) (boolEquivFin2 (v i))
        * ∏ j ∈ Finset.univ.erase i, (if w j = v j then (1 : ℂ) else 0) := by
  have hne : ∀ j ∈ Finset.univ.erase i,
      (if j = i then (pauliXChoice a * clusterJ ζ) else (1 : Operator 2)) (boolEquivFin2 (w j))
          (boolEquivFin2 (v j))
        = if w j = v j then (1 : ℂ) else 0 := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [if_neg hji, Matrix.one_apply]
    by_cases hw : w j = v j
    · rw [if_pos (congrArg boolEquivFin2 hw), if_pos hw]
    · rw [if_neg (fun h => hw (boolEquivFin2.injective h)), if_neg hw]
  have h1 : (if (i : Fin n) = i then (pauliXChoice a * clusterJ ζ) else (1 : Operator 2))
        (boolEquivFin2 (w i)) (boolEquivFin2 (v i))
      = (pauliXChoice a * clusterJ ζ) (boolEquivFin2 (w i)) (boolEquivFin2 (v i)) := by
    rw [if_pos rfl]
  show (∏ j : Fin n, (if j = i then (pauliXChoice a * clusterJ ζ) else (1 : Operator 2)) (boolEquivFin2 (w j))
        (boolEquivFin2 (v j))) = _
  exact ((Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
      (fun j => (if j = i then (pauliXChoice a * clusterJ ζ) else (1 : Operator 2)) (boolEquivFin2 (w j))
        (boolEquivFin2 (v j))) (Finset.mem_univ i)).symm).trans
    (congrArg₂ (· * ·) h1 (Finset.prod_congr rfl fun j hj => hne j hj))

/-- The raw wire operator sends a basis ket to the local wire output, supported on registers
agreeing with the input away from `i`. -/
theorem rawNetworkWireGateB_mulVec_ket (n : ℕ) (i : Fin n) (ζ : ℂ) (a : Bool) (w v : Reg n) :
    (rawNetworkWireGateB i ζ a *ᵥ Qatlib.Foundations.PureStateMath.Ket v) w
      = (pauliXChoice a * clusterJ ζ) (boolEquivFin2 (w i)) (boolEquivFin2 (v i))
        * (if (fun k => if k = i then false else w k)
            = (fun k => if k = i then false else v k) then (1 : ℂ) else 0) := by
  simp only [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
  rw [Fintype.sum_eq_single v (fun u hu => by rw [if_neg hu, mul_zero]),
    if_pos rfl, mul_one, rawNetworkWireGateB_apply, networkIndicator_prod_erase]

/-- Applying a lifted raw wire leaf to a column of `networkFrame` gives the routed tensor
product of its measured local output and the unchanged spectator basis state, with amplitude
factor `1 / √2`. -/
theorem rawNetworkWireLeaf_column (n : ℕ) (i : Fin n) (ζ : ℂ) (a : Bool) (x : Fin (2 ^ n)) :
    (rawNetworkWireLeaf n i ζ a) *ᵥ (fun r => networkFrame n r x)
      = relabelState (bitVecEquiv (n + 2)) (relabelState (networkWireRoute n i)
          (TensorState
            (fun q : Bool × Bool =>
              if q.1 = a then ((Real.sqrt 2 : ℂ)⁻¹) * (pauliXChoice a * clusterJ ζ) (boolEquivFin2 q.2)
                (boolEquivFin2 (((bitVecEquiv n).symm x) i)) else 0)
            (Qatlib.Foundations.PureStateMath.Ket (fun k : Fin n => if k = i then false else ((bitVecEquiv n).symm x) k)))) := by
  have hL : rawNetworkWireLeaf n i ζ a
      = relabelGate (bitVecEquiv (n + 2)) (relabelGate (networkWireRoute n i)
          (TensorGate (relabelGate teleportOutcomeEquiv.symm (rawWireSmallLeaf ζ a))
            (1 : Matrix (Reg n) (Reg n) ℂ))) := by
    simp only [rawNetworkWireLeaf, networkStepLiftLeaf, networkStepLiftGate, eWireFin,
      rawWireSmallLeaf]
    rw [← networkRelabelGate_trans, ← networkRelabelGate_trans,
      relabelGate_prodCongr_tensorGate_one]
  show ApplyGate (rawNetworkWireLeaf n i ζ a) (fun r => networkFrame n r x) = _
  rw [hL, networkFrame_column, applyGate_relabelGate, applyGate_relabelGate',
    networkRelabelState_ket, networkWireRoute_symm_frameVec, ← tensorState_ket_ket,
    applyGate_tensorGate, applyGate_one]
  simp only [ApplyGate]
  rw [rawWireSmallLeaf_column]

/-- After output reindexing, a raw wire leaf applied to a frame column is supported on auxiliary
label `(a, false)` and has logical component `rawNetworkWireGateB` scaled by `1 / √2`. -/
theorem rawNetworkWireLeaf_firstFactor (n : ℕ) (i : Fin n) (ζ : ℂ) (a : Bool)
    (x : Fin (2 ^ n)) :
    relabelState (eWireOutFin n i).symm
        ((rawNetworkWireLeaf n i ζ a) *ᵥ (fun r => networkFrame n r x))
      = (fun q : Fin 4 × Fin (2 ^ n) =>
          if q.1 = teleportOutcomeEquiv (a, false)
          then ((Real.sqrt 2 : ℂ)⁻¹)
            * (relabelState (bitVecEquiv n) ((rawNetworkWireGateB i ζ a)
                *ᵥ (Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv n).symm x)))) q.2
          else 0) := by
  rw [rawNetworkWireLeaf_column, relabelState_trans]
  funext q
  have hrr : ∀ v : Reg (n + 2),
      (networkWireRoute n i).symm v = networkWireRouteFromF n i v := fun _ => rfl
  have heq : ((bitVecEquiv (n + 2)).trans (eWireOutFin n i).symm).symm q
      = networkWireOutToF n i (teleportOutcomeEquiv.symm q.1, (bitVecEquiv n).symm q.2) := by
    have h1 : ((bitVecEquiv (n + 2)).trans (eWireOutFin n i).symm).symm q
        = (bitVecEquiv (n + 2)).symm (eWireOutFin n i q) := rfl
    have h2 : eWireOutFin n i q
        = (bitVecEquiv (n + 2)) (networkWireOutToF n i
            (teleportOutcomeEquiv.symm q.1, (bitVecEquiv n).symm q.2)) := rfl
    rw [h1, h2, Equiv.symm_apply_apply]
  show TensorState
      (fun q : Bool × Bool =>
          if q.1 = a then ((Real.sqrt 2 : ℂ)⁻¹) * (pauliXChoice a * clusterJ ζ) (boolEquivFin2 q.2)
            (boolEquivFin2 (((bitVecEquiv n).symm x) i)) else 0)
      (Qatlib.Foundations.PureStateMath.Ket (fun k : Fin n => if k = i then false else ((bitVecEquiv n).symm x) k))
      ((networkWireRoute n i).symm
        (((bitVecEquiv (n + 2)).trans (eWireOutFin n i).symm).symm q))
      = _
  rw [heq, hrr, networkWireRouteFromF_outToF]
  show (if (teleportOutcomeEquiv.symm q.1).1 = a
        then ((Real.sqrt 2 : ℂ)⁻¹) * (pauliXChoice a * clusterJ ζ)
            (boolEquivFin2 (((bitVecEquiv n).symm q.2) i))
            (boolEquivFin2 (((bitVecEquiv n).symm x) i))
        else 0)
      * (if (fun k : Fin n => if k = i then (teleportOutcomeEquiv.symm q.1).2
              else ((bitVecEquiv n).symm q.2) k)
            = (fun k : Fin n => if k = i then false else ((bitVecEquiv n).symm x) k)
          then (1 : ℂ) else 0)
      = (if q.1 = teleportOutcomeEquiv (a, false)
          then ((Real.sqrt 2 : ℂ)⁻¹)
              * ((rawNetworkWireGateB i ζ a *ᵥ Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv n).symm x))
                  ((bitVecEquiv n).symm q.2))
          else 0)
  by_cases hq : q.1 = teleportOutcomeEquiv (a, false)
  · rw [if_pos hq]
    have hsym : teleportOutcomeEquiv.symm q.1 = (a, false) := by
      rw [hq, Equiv.symm_apply_apply]
    rw [hsym, rawNetworkWireGateB_mulVec_ket, if_pos rfl]
    exact mul_assoc _ _ _
  · rw [if_neg hq]
    by_cases h1 : (teleportOutcomeEquiv.symm q.1).1 = a
    · have h2 : (fun k : Fin n => if k = i then (teleportOutcomeEquiv.symm q.1).2
              else ((bitVecEquiv n).symm q.2) k)
            ≠ (fun k : Fin n => if k = i then false else ((bitVecEquiv n).symm x) k) := by
        intro hf
        have hi := congrFun hf i
        simp only [] at hi
        simp only [if_true] at hi
        exact hq ((Equiv.symm_apply_eq teleportOutcomeEquiv).mp (Prod.ext h1 hi))
      rw [if_pos h1, if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

/-- On a matrix unit, the raw wire step is one half of conjugation by `rawNetworkWireGate`. -/
theorem rawNetworkWireBranch_matUnit (n : ℕ) (i : Fin n) (ζ : ℂ) (a : Bool)
    (x y : Fin (2 ^ n)) :
    rawNetworkStepCore (.inl (i, ζ)) (a, false) (networkMatUnit x y)
      = ((2 : ℂ)⁻¹) • (rawNetworkWireGate i ζ a * networkMatUnit x y
          * (rawNetworkWireGate i ζ a).conjTranspose) := by
  have hreal : (starRingEnd ℂ) ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    have h := Complex.conj_ofReal ((Real.sqrt 2 : ℝ)⁻¹)
    rw [Complex.ofReal_inv] at h
    exact h
  have hsmulpw : ∀ (V : QState (Fin (2 ^ n))) (q : Fin 4 × Fin (2 ^ n)),
      (if q.1 = teleportOutcomeEquiv (a, false)
        then ((Real.sqrt 2 : ℂ)⁻¹) * V q.2 else 0)
        = ((Real.sqrt 2 : ℂ)⁻¹)
          • (if q.1 = teleportOutcomeEquiv (a, false) then V q.2 else 0) := by
    intro V q
    by_cases hq : q.1 = teleportOutcomeEquiv (a, false)
    · rw [if_pos hq, if_pos hq, smul_eq_mul]
    · rw [if_neg hq, if_neg hq, smul_eq_mul, mul_zero]
  have hsmul : ∀ V : QState (Fin (2 ^ n)),
      (fun q : Fin 4 × Fin (2 ^ n) =>
          if q.1 = teleportOutcomeEquiv (a, false)
          then ((Real.sqrt 2 : ℂ)⁻¹) * V q.2 else 0)
        = ((Real.sqrt 2 : ℂ)⁻¹) • (fun q : Fin 4 × Fin (2 ^ n) =>
          if q.1 = teleportOutcomeEquiv (a, false) then V q.2 else 0) := by
    intro V
    funext q
    exact hsmulpw V q
  have htlsmul : ∀ (c : ℂ) (M : Matrix (Fin 4 × Fin (2 ^ n)) (Fin 4 × Fin (2 ^ n)) ℂ),
      Matrix.traceLeft (c • M) = c • Matrix.traceLeft M := by
    intro c M
    ext u u'
    simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.smul_apply, Finset.mul_sum,
      smul_eq_mul]
  have hAx : ∀ v : Fin (2 ^ n),
      ApplyGate (rawNetworkWireLeaf n i ζ a) (fun r => networkFrame n r v)
        = (rawNetworkWireLeaf n i ζ a) *ᵥ (fun r => networkFrame n r v) := fun _ => rfl
  have hB : ∀ v : Fin (2 ^ n), (rawNetworkWireGateB i ζ a *ᵥ Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv n).symm v))
      = relabelState (bitVecEquiv n).symm (rawNetworkWireGate i ζ a *ᵥ Qatlib.Foundations.PureStateMath.Ket v) := by
    intro v
    have hBB : rawNetworkWireGateB i ζ a
        = relabelGate (bitVecEquiv n).symm (rawNetworkWireGate i ζ a) := rawNetworkWireGateB_eq i ζ a
    have hket : Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv n).symm v)
        = relabelState (bitVecEquiv n).symm (Qatlib.Foundations.PureStateMath.Ket v) := (networkRelabelState_ket _ _).symm
    rw [hBB, hket]
    show ApplyGate (relabelGate (bitVecEquiv n).symm (rawNetworkWireGate i ζ a))
        (relabelState (bitVecEquiv n).symm (Qatlib.Foundations.PureStateMath.Ket v))
      = relabelState (bitVecEquiv n).symm (rawNetworkWireGate i ζ a *ᵥ Qatlib.Foundations.PureStateMath.Ket v)
    rw [applyGate_relabelGate]
    rfl
  simp only [rawNetworkStepCore]
  rw [if_neg (by simp)]
  rw [networkFrame_matUnit, matOuter_sandwich, relabelGate_matOuter_fwd,
    hAx x, hAx y,
    rawNetworkWireLeaf_firstFactor, rawNetworkWireLeaf_firstFactor,
    hsmul _, hsmul _, matOuter_smul_smul, hreal, sqrt2_inv_sq, one_div, htlsmul,
    traceLeft_matOuter_supported, relabelGate_matOuter_back, hB x, hB y,
    relabelGate_matOuter_back, networkRelabelGate_symm,
    networkMatUnit_eq_matOuter_ket x y,
    show (rawNetworkWireGate i ζ a *ᵥ Qatlib.Foundations.PureStateMath.Ket x) = ApplyGate
        (rawNetworkWireGate i ζ a) (Qatlib.Foundations.PureStateMath.Ket x) from rfl,
    show (rawNetworkWireGate i ζ a *ᵥ Qatlib.Foundations.PureStateMath.Ket y) = ApplyGate
        (rawNetworkWireGate i ζ a) (Qatlib.Foundations.PureStateMath.Ket y) from rfl,
    ← matOuter_sandwich]

/-- For every operator, the valid raw wire branch is one half of conjugation by
`rawNetworkWireGate`. -/
theorem rawNetworkWireBranch_apply (n : ℕ) (i : Fin n) (ζ : ℂ) (a : Bool)
    (ρ : Operator (2 ^ n)) :
    rawNetworkStepBranch (.inl (i, ζ)) (a, false) ρ =
      (2 : ℂ)⁻¹ • conjBranch (rawNetworkWireGate i ζ a) ρ := by
  rw [networkMatUnit_decomp ρ, map_sum, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro xy _
  rw [map_smul, map_smul]
  change ρ xy.1 xy.2 • rawNetworkStepCore (.inl (i, ζ)) (a, false)
    (networkMatUnit xy.1 xy.2) = _
  rw [rawNetworkWireBranch_matUnit, conjBranch_apply, smul_smul, smul_smul]
  rw [mul_comm]

/-- The scalar factor `(if x then star ζ else 1) * (if x && z then -1 else 1)` arising when a
wire step transports a local Pauli frame. -/
noncomputable def wireFramePhase (ζ : ℂ) (x z : Bool) : ℂ :=
  (if x then star ζ else 1) * (if x && z then -1 else 1)

/-- For a unit-norm parameter, multiplying the adjusted raw wire matrix by the input Pauli frame
equals the updated output frame times `clusterJ ζ`, up to `wireFramePhase`. -/
theorem wireFrameTransport (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x z a : Bool) :
    (pauliXChoice a * clusterJ (if x then star ζ else ζ)) *
      relabelGate boolEquivFin2 ((if x then PauliX else 1) * (if z then PauliZ else 1)) =
    wireFramePhase ζ x z •
      (relabelGate boolEquivFin2
        ((if a ^^ z then PauliX else 1) * (if x then PauliZ else 1)) * clusterJ ζ) := by
  have hz : star ζ * ζ = 1 := by
    have h := Complex.normSq_eq_conj_mul_self (z := ζ)
    rw [Complex.normSq_eq_norm_sq, hζ, one_pow] at h
    exact h.symm
  cases x <;> cases z <;> cases a <;> ext c i <;> fin_cases c <;> fin_cases i <;>
    simp [wireFramePhase, pauliXChoice, clusterJ_entry, Matrix.mul_apply,
      Fin.sum_univ_two, PauliX, PauliZ, permMatrix, relabelGate,
      Matrix.reindex_apply, Matrix.submatrix_apply, boolEquivFin2, Matrix.smul_apply,
      smul_eq_mul] <;>
    try ring
  all_goals change (starRingEnd ℂ) ζ * ζ = 1 at hz
  all_goals rw [mul_assoc, hz, mul_one]

/-- For `‖ζ‖ = 1`, the adjusted raw wire operator multiplied by the input frame equals
`wireFramePhase` times the updated frame multiplied by the logical wire gate. -/
theorem wireFrameTransport_network (n : ℕ) (i : Fin n) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (F : PauliFrame n) (a : Bool) :
    rawNetworkWireGate i (if F.1 i then star ζ else ζ) a * pauliFrameGate n F =
      wireFramePhase ζ (F.1 i) (F.2 i) •
        (pauliFrameGate n (frameUpdate F (.inl (i, ζ)) (a, false)) * networkWireGate i ζ) := by
  let c : Fin n → ℂ := fun j => if j = i then wireFramePhase ζ (F.1 i) (F.2 i) else 1
  have hc : ∏ j, c j = wireFramePhase ζ (F.1 i) (F.2 i) := by
    simp [c]
  change tensorPauliProduct n (fun j => if j = i then
      pauliXChoice a * clusterJ (if F.1 i then star ζ else ζ) else 1) *
      tensorPauliProduct n (fun j => relabelGate boolEquivFin2
        ((if F.1 j then PauliX else 1) * (if F.2 j then PauliZ else 1))) = _
  change _ = wireFramePhase ζ (F.1 i) (F.2 i) •
    (tensorPauliProduct n (fun j => relabelGate boolEquivFin2
      ((if (frameUpdate F (.inl (i, ζ)) (a, false)).1 j then PauliX else 1) *
       (if (frameUpdate F (.inl (i, ζ)) (a, false)).2 j then PauliZ else 1))) *
      tensorPauliProduct n (fun j => if j = i then clusterJ ζ else 1))
  rw [tensorPauliProduct_mul, tensorPauliProduct_mul, ← hc,
    ← tensorPauliProduct_smul]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simpa [c, frameUpdate] using wireFrameTransport ζ hζ (F.1 i) (F.2 i) a
  · simp [c, frameUpdate, Function.update_of_ne hj, hj]

/-- The wire frame transport scalar has norm one whenever `ζ` has norm one. -/
theorem wireFramePhase_norm (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x z : Bool) :
    ‖wireFramePhase ζ x z‖ = 1 := by
  cases x <;> cases z <;> simp [wireFramePhase, norm_mul, hζ]

/-- Multiplying a conjugating operator by a unit-norm scalar leaves its conjugation map
unchanged. -/
theorem deferred_conj_phase {D : ℕ} (c : ℂ) (hc : ‖c‖ = 1) (U : Operator D)
    (ρ : Operator D) : conjBranch (c • U) ρ = conjBranch U ρ := by
  have hh : c * star c = 1 := by
    have h := Complex.normSq_eq_conj_mul_self (z := c)
    rw [Complex.normSq_eq_norm_sq, hc, one_pow] at h
    exact (mul_comm _ _).trans h.symm
  simp only [conjBranch_apply, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [mul_comm (star c) c, hh, one_smul]

/-- For a unit-norm wire parameter, the adjusted raw step applied to a framed input equals one
half of conjugation by the updated frame times the logical wire gate. -/
theorem deferred_wire_actual_frame_transport (n : ℕ) (i : Fin n) (ζ : ℂ)
    (hζ : ‖ζ‖ = 1) (F : PauliFrame n) (a : Bool) (ρ : Operator (2 ^ n)) :
    rawNetworkStepCore (frameAdjustedGate F (.inl (i, ζ))) (a, false)
      (conjBranch (pauliFrameGate n F) ρ) =
      (2 : ℂ)⁻¹ • conjBranch
        (pauliFrameGate n (frameUpdate F (.inl (i, ζ)) (a, false)) * networkWireGate i ζ) ρ := by
  change rawNetworkStepBranch (.inl (i, if F.1 i then star ζ else ζ)) (a, false)
    (conjBranch (pauliFrameGate n F) ρ) = _
  rw [rawNetworkWireBranch_apply]
  have hm : ∀ (A B : Operator (2 ^ n)), conjBranch A (conjBranch B ρ) =
      conjBranch (A * B) ρ := by
    intro A B
    simp [conjBranch_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hm, wireFrameTransport_network n i ζ hζ F a,
    deferred_conj_phase _ (wireFramePhase_norm ζ hζ (F.1 i) (F.2 i))]

/-- The four-qubit leaf operator for outcomes `(a, d)` of the uncorrected CZ circuit. -/
noncomputable def rawCZSmallLeaf (a d : Bool) : Operator 16 :=
  (observedLeaf 1 uncorrectedCZProgram (Fin.cast (by rfl) (teleportOutcomeEquiv (a, d)))).operator

/-- The uncorrected CZ leaf is the preparation operator followed by the two measurement
Hadamards and the projectors selecting outcomes `a` and `d`. -/
theorem rawCZSmallLeaf_operator (a d : Bool) :
    rawCZSmallLeaf a d =
      Projector (Finset.univ.filter (fun r => clusterCZLabelD r = boolEquivFin2 d)) *
      (Projector (Finset.univ.filter (fun r => clusterCZLabelA r = boolEquivFin2 a)) *
        (clusterCZHdGate * (clusterCZHaGate * clusterCZPreparationGate))) := by
  have hr : rawCZSmallLeaf a d =
      (((((((((((1 : Operator 16) * Projector (Finset.univ.filter
        (fun r => clusterCZLabelD r = boolEquivFin2 d))) * Projector (Finset.univ.filter
        (fun r => clusterCZLabelA r = boolEquivFin2 a))) * clusterCZHdGate) * clusterCZHaGate) *
        clusterCZEdgeBcGate) * clusterCZEdgeDcGate) * clusterCZEdgeAbGate) * clusterCZHcGate) *
        clusterCZHbGate) * clusterCZHdGate) * clusterCZHaGate := by
    cases a <;> cases d <;> rfl
  rw [hr]
  simp only [Matrix.one_mul, Matrix.mul_assoc]
  rfl

/-- On a basis input with two false auxiliary bits, the raw CZ leaf selects measurement label
`(a, d)` and shifts the logical bits by those outcomes with the CZ sign and amplitude factor
`1 / 2`. -/
theorem rawCZSmallLeaf_column (a d x y : Bool) :
    ApplyGate (rawCZSmallLeaf a d)
      (relabelState clusterCZRegisterEquiv (Qatlib.Foundations.PureStateMath.Ket ((x, y), (false, false)))) =
    relabelState clusterCZRegisterEquiv
      (fun q : (Bool × Bool) × (Bool × Bool) =>
        if q.1 = (a, d) then (1 / 2 : ℂ) *
          (if q.1.1 = (x ^^ q.2.1) ∧ q.1.2 = (y ^^ q.2.2)
            then (if q.2.1 && q.2.2 then -1 else 1) else 0) else 0) := by
  have hG : clusterCZHdGate * (clusterCZHaGate * clusterCZPreparationGate)
      = relabelGate clusterCZRegisterEquiv
          (clusterCZHdB * (clusterCZHaB * clusterCZPreparationB)) := by
    rw [clusterCZPreparationGate_eq_relabel]
    unfold clusterCZHdGate clusterCZHaGate
    rw [← teleportRelabelGate_mul, ← teleportRelabelGate_mul]
  have hPAsymm : Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelA r
          = boolEquivFin2 a))
      = relabelGate clusterCZRegisterEquiv (relabelGate clusterCZRegisterEquiv.symm
          (Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelA r
            = boolEquivFin2 a)))) :=
    (relabelGate_relabelGate _ _).symm
  have hPlabA : relabelGate clusterCZRegisterEquiv.symm
        (Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelA r
          = boolEquivFin2 a)))
      = relabelGate clusterCZRegisterEquiv.symm
          (Projector (Finset.univ.filter (fun r : Fin 16 =>
            (boolEquivFin2 ∘ (fun q : (Bool × Bool) × (Bool × Bool) => q.1.1)
              ∘ clusterCZRegisterEquiv.symm) r = boolEquivFin2 a))) := rfl
  have hPDsymm : Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelD r
          = boolEquivFin2 d))
      = relabelGate clusterCZRegisterEquiv (relabelGate clusterCZRegisterEquiv.symm
          (Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelD r
            = boolEquivFin2 d)))) :=
    (relabelGate_relabelGate _ _).symm
  have hPlabD : relabelGate clusterCZRegisterEquiv.symm
        (Projector (Finset.univ.filter (fun r : Fin 16 => clusterCZLabelD r
          = boolEquivFin2 d)))
      = relabelGate clusterCZRegisterEquiv.symm
          (Projector (Finset.univ.filter (fun r : Fin 16 =>
            (boolEquivFin2 ∘ (fun q : (Bool × Bool) × (Bool × Bool) => q.1.2)
              ∘ clusterCZRegisterEquiv.symm) r = boolEquivFin2 d))) := rfl

  rw [rawCZSmallLeaf_operator, hG, applyGate_mul, applyGate_mul,
    applyGate_relabelGate, clusterCZDecoded,
    hPAsymm, hPlabA, applyGate_relabelGate,
    applyGate_relabelBoolProjector (comp := fun q : (Bool × Bool) × (Bool × Bool) => q.1.1),
    hPDsymm, hPlabD, applyGate_relabelGate,
    applyGate_relabelBoolProjector (comp := fun q : (Bool × Bool) × (Bool × Bool) => q.1.2)]
  funext r
  obtain ⟨⟨⟨a', d'⟩, ⟨b, c⟩⟩, hr⟩ : ∃ q : (Bool × Bool) × (Bool × Bool),
      r = clusterCZRegisterEquiv q := ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
  subst hr
  cases a <;> cases d <;> cases a' <;> cases d' <;>
    simp [relabelState, Function.comp_apply, Equiv.symm_apply_apply]

/-- The complex sign equal to `-1` when both Boolean arguments are true and to `1` otherwise. -/
def frameBitSign (z b : Bool) : ℂ := if z && b then -1 else 1

/-- The product of the local Z-frame signs evaluated on the bits of the basis register `v`. -/
noncomputable def frameSign {n : ℕ} (F : PauliFrame n) (v : Reg n) : ℂ :=
  ∏ i, frameBitSign (F.2 i) (v i)

/-- Flip each basis-register bit according to the corresponding X-frame bit. -/
def frameShift {n : ℕ} (F : PauliFrame n) (v : Reg n) : Reg n :=
  fun i => v i ^^ F.1 i

/-- The tensor product of local X-times-Z frame factors, indexed directly by Boolean registers. -/
noncomputable def pauliFrameGateB {n : ℕ} (F : PauliFrame n) : Matrix (Reg n) (Reg n) ℂ :=
  pauliProductDensity (fun i => relabelGate boolEquivFin2
    ((if F.1 i then PauliX else 1) * (if F.2 i then PauliZ else 1)))

/-- A local X-times-Z frame entry is the delta selecting the X-shifted output bit multiplied by
the Z sign of the input bit. -/
theorem frameLocal_entry (x z w v : Bool) :
    relabelGate boolEquivFin2 ((if x then PauliX else 1) * (if z then PauliZ else 1))
      (boolEquivFin2 w) (boolEquivFin2 v) =
      (if w = (v ^^ x) then (1 : ℂ) else 0) * frameBitSign z v := by
  cases x <;> cases z <;> cases w <;> cases v <;>
    simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.mul_apply, Fintype.sum_bool, PauliX, PauliZ, permMatrix, boolEquivFin2, frameBitSign]

/-- A Boolean-register frame matrix entry is `frameSign F v` when the output is `frameShift F
v`, and zero otherwise. -/
theorem pauliFrameGateB_entry {n : ℕ} (F : PauliFrame n) (w v : Reg n) :
    pauliFrameGateB F w v = if w = frameShift F v then frameSign F v else 0 := by
  change (∏ i, relabelGate boolEquivFin2
    ((if F.1 i then PauliX else 1) * (if F.2 i then PauliZ else 1))
      (boolEquivFin2 (w i)) (boolEquivFin2 (v i))) = _
  simp_rw [frameLocal_entry]
  rw [Finset.prod_mul_distrib]
  have hi : (∏ i : Fin n, if w i = (v i ^^ F.1 i) then (1 : ℂ) else 0) =
      if w = frameShift F v then 1 else 0 := by
    by_cases hw : w = frameShift F v
    · have hb : ∀ i, w i = (v i ^^ F.1 i) := fun i => congrFun hw i
      simp [hb, hw, frameShift]
    · have hb : ∃ i, w i ≠ (v i ^^ F.1 i) := by
        by_contra h
        push Not at h
        exact hw (funext h)
      obtain ⟨i, hb⟩ := hb
      rw [if_neg hw]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact if_neg hb
  rw [hi]
  by_cases hw : w = frameShift F v <;> simp [hw, frameSign]

/-- Flip the bit at `lo` by `a` and, at a distinct index `hi`, by `d`, preserving all other
bits. The `lo` case takes precedence if the endpoints coincide. -/
def rawCZShift {n : ℕ} (lo hi : Fin n) (a d : Bool) (v : Reg n) : Reg n :=
  fun k => if k = lo then v k ^^ a else if k = hi then v k ^^ d else v k

/-- The Boolean-register raw CZ operator obtained by multiplying `networkCzGateB` by the
permutation matrix of `rawCZShift`. -/
noncomputable def rawNetworkCZGateB {n : ℕ} (lo hi : Fin n) (a d : Bool) :
    Matrix (Reg n) (Reg n) ℂ := networkCzGateB lo hi * permMatrix (rawCZShift lo hi a d)
/-- The reindexing of `rawNetworkCZGateB` to `Fin (2 ^ n)`. -/
noncomputable def rawNetworkCZGate {n : ℕ} (lo hi : Fin n) (a d : Bool) : Operator (2 ^ n) :=
  relabelGate (bitVecEquiv n) (rawNetworkCZGateB lo hi a d)

/-- A raw CZ matrix entry vanishes unless the output is the outcome-dependent bit shift of the
input; its nonzero value is the CZ sign of the output bits. -/
theorem rawNetworkCZGateB_entry {n : ℕ} (lo hi : Fin n) (a d : Bool) (w v : Reg n) :
    rawNetworkCZGateB lo hi a d w v =
      if w = rawCZShift lo hi a d v then (if w lo && w hi then (-1 : ℂ) else 1) else 0 := by
  simp [rawNetworkCZGateB, networkCzGateB, Matrix.diagonal_mul, permMatrix]

/-- The raw CZ operator sends a basis ket to its outcome-shifted register with the CZ sign
determined by the shifted endpoint bits. -/
theorem rawNetworkCZGateB_mulVec_ket {n : ℕ} (lo hi : Fin n) (a d : Bool) (w v : Reg n) :
    (rawNetworkCZGateB lo hi a d *ᵥ Qatlib.Foundations.PureStateMath.Ket v) w =
      if w = rawCZShift lo hi a d v then (if w lo && w hi then (-1 : ℂ) else 1) else 0 := by
  simp only [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
  rw [Fintype.sum_eq_single v (fun u hu => by rw [if_neg hu, mul_zero]),
    if_pos rfl, mul_one, rawNetworkCZGateB_entry]

/-- For ordered distinct endpoints, the raw CZ bit shift preserves every spectator coordinate
enumerated by `networkCzSpec`. -/
theorem rawCZShift_spec {n : ℕ} (lo hi : Fin n) (h : (lo : ℕ) < (hi : ℕ))
    (a d : Bool) (v : Reg n) (k : Fin (n - 2)) :
    rawCZShift lo hi a d v
      ⟨networkCzSpec lo hi k, networkCzSpec_lt n lo hi k h hi.isLt k.isLt⟩ =
    v ⟨networkCzSpec lo hi k, networkCzSpec_lt n lo hi k h hi.isLt k.isLt⟩ := by
  have hh := networkCzSpec_ne lo hi k h
  have hl : (⟨networkCzSpec lo hi k, networkCzSpec_lt n lo hi k h hi.isLt k.isLt⟩ : Fin n) ≠ lo :=
    fun he => hh.1 (congrArg Fin.val he)
  have hr : (⟨networkCzSpec lo hi k, networkCzSpec_lt n lo hi k h hi.isLt k.isLt⟩ : Fin n) ≠ hi :=
    fun he => hh.2 (congrArg Fin.val he)
  simp [rawCZShift, hl, hr]

/-- In product coordinates, the raw CZ leaf fixes the measured pair to `(a, d)` and sends `(x,
y)` to `(x ^^ a, y ^^ d)` with its CZ sign and amplitude factor `1 / 2`. -/
theorem rawCZSmallLeaf_apply (a d x y : Bool) :
    ApplyGate (relabelGate clusterCZRegisterEquiv.symm (rawCZSmallLeaf a d))
      (Qatlib.Foundations.PureStateMath.Ket ((x, y), (false, false))) =
    fun q : (Bool × Bool) × (Bool × Bool) =>
      if q.1 = (a, d) then (1 / 2 : ℂ) *
        (if q.2 = (x ^^ a, y ^^ d) then
          (if q.2.1 && q.2.2 then -1 else 1) else 0) else 0 := by
  have hkey := rawCZSmallLeaf_column a d x y
  rw [networkRelabelState_ket] at hkey
  rw [applyGate_relabelGate',
    show clusterCZRegisterEquiv.symm.symm = clusterCZRegisterEquiv from Equiv.symm_symm _,
    networkRelabelState_ket, hkey, relabelState_relabelState]
  funext q
  obtain ⟨⟨a', d'⟩, ⟨b, c⟩⟩ := q
  cases a <;> cases d <;> cases a' <;> cases d' <;> cases x <;> cases y <;>
    cases b <;> cases c <;> simp

/-- The local raw CZ matrix entry, supported on the outcome-shifted bit pair and carrying the CZ
sign of the output pair. -/
def rawCZEntry (a d : Bool) (w v : Bool × Bool) : ℂ :=
  if w = (v.1 ^^ a, v.2 ^^ d) then (if w.1 && w.2 then -1 else 1) else 0

/-- The product-coordinate raw CZ leaf on a basis input has measured label `(a, d)` and logical
amplitudes equal to one half of `rawCZEntry`. -/
theorem rawCZSmallLeaf_apply_entry (a d x y : Bool) :
    ApplyGate (relabelGate clusterCZRegisterEquiv.symm (rawCZSmallLeaf a d))
      (Qatlib.Foundations.PureStateMath.Ket ((x, y), (false, false))) =
    fun q : (Bool × Bool) × (Bool × Bool) =>
      if q.1 = (a, d) then (1 / 2 : ℂ) * rawCZEntry a d q.2 (x, y) else 0 :=
  rawCZSmallLeaf_apply a d x y

/-- For ordered endpoints, equality to the raw CZ shift is equivalent to the two prescribed
endpoint flips and equality of all spectator coordinates. -/
theorem rawCZSupport_split {n : ℕ} (lo hi : Fin n) (h : (lo : ℕ) < (hi : ℕ))
    (a d : Bool) (w v : Reg n) :
    (w = rawCZShift lo hi a d v) ↔
      ((w lo, w hi) = (v lo ^^ a, v hi ^^ d) ∧
        (fun k : Fin (n - 2) =>
          w ⟨networkCzSpec lo hi k, networkCzSpec_lt n lo hi k h hi.isLt k.isLt⟩) =
        (fun k : Fin (n - 2) =>
          v ⟨networkCzSpec lo hi k, networkCzSpec_lt n lo hi k h hi.isLt k.isLt⟩)) := by
  have hn : hi ≠ lo := fun he => by have := congrArg Fin.val he; omega
  have hh := networkCzSupport_split n lo hi h w (rawCZShift lo hi a d v)
  have hs : (fun k : Fin (n - 2) => rawCZShift lo hi a d v
      ⟨networkCzSpec lo hi k, networkCzSpec_lt n lo hi k h hi.isLt k.isLt⟩) =
      (fun k : Fin (n - 2) => v
      ⟨networkCzSpec lo hi k, networkCzSpec_lt n lo hi k h hi.isLt k.isLt⟩) := by
    funext k
    exact rawCZShift_spec lo hi h a d v k
  rw [hs] at hh
  simpa [rawCZShift, hn] using hh

/-- A lifted raw CZ leaf applied to a frame column factors, after routing, into the measured
local CZ output scaled by one half and the unchanged spectator basis state. -/
theorem rawNetworkCZLeaf_column (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (a d : Bool) (x : Fin (2 ^ n)) :
    (rawNetworkCZLeaf n lo hi h1 a d) *ᵥ (fun r => networkFrame n r x)
      = relabelState (bitVecEquiv (n + 2)) (relabelState (networkCzRoute n lo hi h1)
          (TensorState
            (fun q : (Bool × Bool) × (Bool × Bool) =>
              if q.1 = (a, d) then (1 / 2 : ℂ)
                * rawCZEntry a d q.2 (((bitVecEquiv n).symm x) lo,
                    ((bitVecEquiv n).symm x) hi) else 0)
            (Qatlib.Foundations.PureStateMath.Ket (fun k : Fin (n - 2) =>
              ((bitVecEquiv n).symm x) ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
                networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩)))) := by
  have hL : rawNetworkCZLeaf n lo hi h1 a d
      = relabelGate (bitVecEquiv (n + 2)) (relabelGate (networkCzRoute n lo hi h1)
          (TensorGate (relabelGate clusterCZRegisterEquiv.symm (rawCZSmallLeaf a d))
            (1 : Matrix (Reg (n - 2)) (Reg (n - 2)) ℂ))) := by
    simp only [rawNetworkCZLeaf, networkStepLiftLeaf, networkStepLiftGate, eCzFin,
      rawCZSmallLeaf]
    rw [← networkRelabelGate_trans, ← networkRelabelGate_trans,
      relabelGate_prodCongr_tensorGate_one]
  show ApplyGate (rawNetworkCZLeaf n lo hi h1 a d) (fun r => networkFrame n r x) = _
  rw [hL, networkFrame_column, applyGate_relabelGate, applyGate_relabelGate',
    networkRelabelState_ket, networkCzRoute_symm_frameVec, ← tensorState_ket_ket,
    applyGate_tensorGate, applyGate_one, rawCZSmallLeaf_apply_entry]

/-- After output reindexing, the raw CZ leaf on a frame column is supported on auxiliary label
`(a, d)` and has logical component `rawNetworkCZGateB` scaled by one half. -/
theorem rawNetworkCZLeaf_firstFactor (n : ℕ) (lo hi : Fin n) (h1 : (lo : ℕ) < (hi : ℕ))
    (a d : Bool) (x : Fin (2 ^ n)) :
    relabelState (eCzOutFin n lo hi h1).symm
        ((rawNetworkCZLeaf n lo hi h1 a d) *ᵥ (fun r => networkFrame n r x))
      = (fun q : Fin 4 × Fin (2 ^ n) =>
          if q.1 = teleportOutcomeEquiv (a, d)
          then (1 / 2 : ℂ)
            * (relabelState (bitVecEquiv n) ((rawNetworkCZGateB lo hi a d)
                *ᵥ (Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv n).symm x)))) q.2
          else 0) := by
  rw [rawNetworkCZLeaf_column, relabelState_trans]
  funext q
  have hrr : ∀ v : Reg (n + 2),
      (networkCzRoute n lo hi h1).symm v = networkCzRouteFromF n lo hi h1 v := fun _ => rfl
  have heq : ((bitVecEquiv (n + 2)).trans (eCzOutFin n lo hi h1).symm).symm q
      = networkCzOutToF n lo hi (teleportOutcomeEquiv.symm q.1, (bitVecEquiv n).symm q.2) := by
    have h1' : ((bitVecEquiv (n + 2)).trans (eCzOutFin n lo hi h1).symm).symm q
        = (bitVecEquiv (n + 2)).symm (eCzOutFin n lo hi h1 q) := rfl
    have h2' : eCzOutFin n lo hi h1 q
        = (bitVecEquiv (n + 2)) (networkCzOutToF n lo hi
            (teleportOutcomeEquiv.symm q.1, (bitVecEquiv n).symm q.2)) := rfl
    rw [h1', h2', Equiv.symm_apply_apply]
  show TensorState
      (fun q : (Bool × Bool) × (Bool × Bool) =>
          if q.1 = (a, d) then (1 / 2 : ℂ)
            * rawCZEntry a d q.2 (((bitVecEquiv n).symm x) lo,
                ((bitVecEquiv n).symm x) hi) else 0)
      (Qatlib.Foundations.PureStateMath.Ket (fun k : Fin (n - 2) =>
          ((bitVecEquiv n).symm x) ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
            networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩))
      ((networkCzRoute n lo hi h1).symm
        (((bitVecEquiv (n + 2)).trans (eCzOutFin n lo hi h1).symm).symm q))
      = _
  rw [heq, hrr, networkCzRouteFromF_outToF]
  show (if ((teleportOutcomeEquiv.symm q.1).1, (teleportOutcomeEquiv.symm q.1).2) = (a, d)
        then (1 / 2 : ℂ)
          * rawCZEntry a d
              (((bitVecEquiv n).symm q.2) lo, ((bitVecEquiv n).symm q.2) hi)
              (((bitVecEquiv n).symm x) lo, ((bitVecEquiv n).symm x) hi)
        else 0)
      * (if (fun k : Fin (n - 2) =>
            ((bitVecEquiv n).symm q.2) ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
              networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩)
            = (fun k : Fin (n - 2) =>
              ((bitVecEquiv n).symm x) ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
                networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩)
          then (1 : ℂ) else 0)
      = (if q.1 = teleportOutcomeEquiv (a, d)
          then (1 / 2 : ℂ)
            * ((rawNetworkCZGateB lo hi a d *ᵥ Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv n).symm x))
                ((bitVecEquiv n).symm q.2))
          else 0)
  by_cases hq : q.1 = teleportOutcomeEquiv (a, d)
  · rw [if_pos hq]
    have hsym : teleportOutcomeEquiv.symm q.1 = (a, d) := by
      rw [hq, Equiv.symm_apply_apply]
    rw [hsym, if_pos rfl, rawCZEntry, rawNetworkCZGateB_mulVec_ket]
    by_cases hc1 : (((bitVecEquiv n).symm q.2) lo, ((bitVecEquiv n).symm q.2) hi)
        = (((bitVecEquiv n).symm x) lo ^^ a, ((bitVecEquiv n).symm x) hi ^^ d)
    · by_cases hc2 : (fun k : Fin (n - 2) =>
          ((bitVecEquiv n).symm q.2) ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
            networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩)
        = (fun k : Fin (n - 2) =>
          ((bitVecEquiv n).symm x) ⟨networkCzSpec (lo : ℕ) (hi : ℕ) (k : ℕ),
            networkCzSpec_lt n (lo : ℕ) (hi : ℕ) (k : ℕ) h1 hi.isLt k.isLt⟩)
      · rw [if_pos hc1, if_pos hc2, mul_one]
        rw [if_pos ((rawCZSupport_split lo hi h1 a d _ _).mpr ⟨hc1, hc2⟩)]
      · rw [if_pos hc1, if_neg hc2, mul_zero]
        rw [if_neg (fun hw => hc2 ((rawCZSupport_split lo hi h1 a d _ _).mp hw).2), mul_zero]
    · rw [if_neg hc1, mul_zero, zero_mul,
        if_neg (fun hw => hc1 ((rawCZSupport_split lo hi h1 a d _ _).mp hw).1), mul_zero]
  · have hpairne : ¬(((teleportOutcomeEquiv.symm q.1).1, (teleportOutcomeEquiv.symm q.1).2)
        = (a, d)) := by
      intro hp
      exact hq ((Equiv.symm_apply_eq teleportOutcomeEquiv).mp
        (Prod.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)))
    rw [if_neg hpairne, zero_mul, if_neg hq]

/-- For distinct CZ endpoints, the raw step on a matrix unit equals one quarter of conjugation
by the raw CZ operator with canonically ordered endpoints. -/
theorem rawNetworkCZBranch_matUnit (n : ℕ) (i j : Fin n) (h : (i : ℕ) ≠ (j : ℕ))
    (a d : Bool) (x y : Fin (2 ^ n)) :
    rawNetworkStepCore (.inr (i, j)) (a, d) (networkMatUnit x y)
      = ((2 : ℂ)⁻¹) ^ 2 • (rawNetworkCZGate (networkCzLo i j) (networkCzHi i j) a d * networkMatUnit x y
          * (rawNetworkCZGate (networkCzLo i j) (networkCzHi i j) a d).conjTranspose) := by
  have hlohi : (networkCzLo i j : ℕ) < (networkCzHi i j : ℕ) := networkCzLo_lt_hi i j h
  have hεreal : (starRingEnd ℂ) (1 / 2 : ℂ)
      = (1 / 2 : ℂ) := by
    cases a <;> cases d <;> simp [Complex.conj_ofNat]
  have hεsq : (1 / 2 : ℂ) * (1 / 2 : ℂ)
      = 1 / 4 := by
    cases a <;> cases d <;> norm_num
  have hq4 : (1 / 4 : ℂ) = ((2 : ℂ)⁻¹) ^ 2 := by norm_num
  have hsmulpw : ∀ (V : QState (Fin (2 ^ n))) (q : Fin 4 × Fin (2 ^ n)),
      (if q.1 = teleportOutcomeEquiv (a, d)
        then (1 / 2 : ℂ) * V q.2 else 0)
        = (1 / 2 : ℂ)
          • (if q.1 = teleportOutcomeEquiv (a, d) then V q.2 else 0) := by
    intro V q
    by_cases hq : q.1 = teleportOutcomeEquiv (a, d)
    · rw [if_pos hq, if_pos hq, smul_eq_mul]
    · rw [if_neg hq, if_neg hq, smul_eq_mul, mul_zero]
  have hsmul : ∀ V : QState (Fin (2 ^ n)),
      (fun q : Fin 4 × Fin (2 ^ n) =>
          if q.1 = teleportOutcomeEquiv (a, d)
          then (1 / 2 : ℂ) * V q.2 else 0)
        = (1 / 2 : ℂ) • (fun q : Fin 4 × Fin (2 ^ n) =>
          if q.1 = teleportOutcomeEquiv (a, d) then V q.2 else 0) := by
    intro V
    funext q
    exact hsmulpw V q
  have htlsmul : ∀ (c : ℂ) (M : Matrix (Fin 4 × Fin (2 ^ n)) (Fin 4 × Fin (2 ^ n)) ℂ),
      Matrix.traceLeft (c • M) = c • Matrix.traceLeft M := by
    intro c M
    ext u u'
    simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.smul_apply, Finset.mul_sum,
      smul_eq_mul]
  have hAx : ∀ v : Fin (2 ^ n),
      ApplyGate (rawNetworkCZLeaf n (networkCzLo i j) (networkCzHi i j)
          (networkCzLo_lt_hi i j h) a d) (fun r => networkFrame n r v)
        = (rawNetworkCZLeaf n (networkCzLo i j) (networkCzHi i j)
            (networkCzLo_lt_hi i j h) a d) *ᵥ (fun r => networkFrame n r v) := fun _ => rfl
  have hBB : rawNetworkCZGateB (networkCzLo i j) (networkCzHi i j) a d
      = relabelGate (bitVecEquiv n).symm
          (rawNetworkCZGate (networkCzLo i j) (networkCzHi i j) a d) := by
    show rawNetworkCZGateB (networkCzLo i j) (networkCzHi i j) a d
        = relabelGate (bitVecEquiv n).symm
            (relabelGate (bitVecEquiv n) (rawNetworkCZGateB (networkCzLo i j) (networkCzHi i j) a d))
    exact (networkRelabelGate_symm _ _).symm
  have hB : ∀ v : Fin (2 ^ n),
      (rawNetworkCZGateB (networkCzLo i j) (networkCzHi i j) a d *ᵥ Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv n).symm v))
        = relabelState (bitVecEquiv n).symm
            (rawNetworkCZGate (networkCzLo i j) (networkCzHi i j) a d *ᵥ Qatlib.Foundations.PureStateMath.Ket v) := by
    intro v
    have hket : Qatlib.Foundations.PureStateMath.Ket ((bitVecEquiv n).symm v)
        = relabelState (bitVecEquiv n).symm (Qatlib.Foundations.PureStateMath.Ket v) := (networkRelabelState_ket _ _).symm
    rw [hBB, hket]
    show ApplyGate (relabelGate (bitVecEquiv n).symm
          (rawNetworkCZGate (networkCzLo i j) (networkCzHi i j) a d))
        (relabelState (bitVecEquiv n).symm (Qatlib.Foundations.PureStateMath.Ket v))
      = relabelState (bitVecEquiv n).symm
          (rawNetworkCZGate (networkCzLo i j) (networkCzHi i j) a d *ᵥ Qatlib.Foundations.PureStateMath.Ket v)
    rw [applyGate_relabelGate]
    rfl
  simp only [rawNetworkStepCore]
  rw [dif_pos h]
  rw [networkFrame_matUnit, matOuter_sandwich, relabelGate_matOuter_fwd,
    hAx x, hAx y,
    rawNetworkCZLeaf_firstFactor, rawNetworkCZLeaf_firstFactor,
    hsmul _, hsmul _, matOuter_smul_smul, hεreal, hεsq, hq4, htlsmul,
    traceLeft_matOuter_supported, relabelGate_matOuter_back, hB x, hB y,
    relabelGate_matOuter_back, networkRelabelGate_symm,
    networkMatUnit_eq_matOuter_ket x y,
    show (rawNetworkCZGate (networkCzLo i j) (networkCzHi i j) a d *ᵥ Qatlib.Foundations.PureStateMath.Ket x) = ApplyGate (rawNetworkCZGate (networkCzLo i j) (networkCzHi i j) a d) (Qatlib.Foundations.PureStateMath.Ket x) from rfl,
    show (rawNetworkCZGate (networkCzLo i j) (networkCzHi i j) a d *ᵥ Qatlib.Foundations.PureStateMath.Ket y) = ApplyGate (rawNetworkCZGate (networkCzLo i j) (networkCzHi i j) a d) (Qatlib.Foundations.PureStateMath.Ket y) from rfl,
    ← matOuter_sandwich]

/-- For distinct CZ endpoints, the raw CZ branch on every operator equals one quarter of
conjugation by `rawNetworkCZGate` with canonically ordered endpoints. -/
theorem rawNetworkCZBranch_apply (n : ℕ) (i j : Fin n) (h : (i : ℕ) ≠ (j : ℕ))
    (a d : Bool) (ρ : Operator (2 ^ n)) :
    rawNetworkStepBranch (.inr (i, j)) (a, d) ρ =
      (2 : ℂ)⁻¹ ^ 2 • conjBranch
        (rawNetworkCZGate (networkCzLo i j) (networkCzHi i j) a d) ρ := by
  rw [networkMatUnit_decomp ρ, map_sum, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro xy _
  rw [map_smul, map_smul]
  change ρ xy.1 xy.2 • rawNetworkStepCore (.inr (i, j)) (a, d)
    (networkMatUnit xy.1 xy.2) = _
  rw [rawNetworkCZBranch_matUnit n i j h, conjBranch_apply, smul_smul, smul_smul]
  rw [mul_comm]

/-- The explicit X and Z frame registers after a CZ outcome at the specified endpoints,
including the cross-coupled input X bits in the Z updates. -/
def czFrameResult {n : ℕ} (F : PauliFrame n) (lo hi : Fin n) (a d : Bool) : PauliFrame n :=
  (fun k => if k = lo then F.1 k ^^ a else if k = hi then F.1 k ^^ d else F.1 k,
   fun k => if k = lo then (F.2 k ^^ F.1 hi) ^^ d
     else if k = hi then (F.2 k ^^ F.1 lo) ^^ a else F.2 k)

/-- The sign associated with the XOR of two frame bits is the product of their signs on the same
basis bit. -/
theorem frameBitSign_xor (z x b : Bool) :
    frameBitSign (z ^^ x) b = frameBitSign z b * frameBitSign x b := by
  cases z <;> cases x <;> cases b <;> norm_num [frameBitSign]

/-- The updated CZ frame shift is the input frame shift followed by `rawCZShift`. -/
theorem czFrameResult_shift {n : ℕ} (F : PauliFrame n) (lo hi : Fin n)
    (a d : Bool) (v : Reg n) :
    frameShift (czFrameResult F lo hi a d) v =
      rawCZShift lo hi a d (frameShift F v) := by
  funext k
  by_cases hl : k = lo
  · subst k
    simp [frameShift, czFrameResult, rawCZShift, Bool.xor_assoc]
  · by_cases hh : k = hi
    · subst k
      simp [frameShift, czFrameResult, rawCZShift, hl, Bool.xor_assoc]
    · simp [frameShift, czFrameResult, rawCZShift, hl, hh]

/-- For distinct endpoints, the updated frame sign equals the input frame sign times the two
cross-coupled endpoint signs from the X frame and measurement outcomes. -/
theorem czFrameResult_sign {n : ℕ} (F : PauliFrame n) (lo hi : Fin n) (hn : lo ≠ hi)
    (a d : Bool) (v : Reg n) :
    frameSign (czFrameResult F lo hi a d) v =
      frameSign F v * (frameBitSign (F.1 hi ^^ d) (v lo) *
        frameBitSign (F.1 lo ^^ a) (v hi)) := by
  have hl : ∀ k : Fin n,
      frameBitSign ((czFrameResult F lo hi a d).2 k) (v k) =
        frameBitSign (F.2 k) (v k) *
          ((if k = lo then frameBitSign (F.1 hi ^^ d) (v lo) else 1) *
           (if k = hi then frameBitSign (F.1 lo ^^ a) (v hi) else 1)) := by
    intro k
    by_cases hk : k = lo
    · subst k
      simp [czFrameResult, hn, ← frameBitSign_xor, Bool.xor_assoc]
    · by_cases hh : k = hi
      · subst k
        simp [czFrameResult, hk, ← frameBitSign_xor, Bool.xor_assoc]
      · simp [czFrameResult, hk, hh]
  unfold frameSign
  simp_rw [hl]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp

/-- For distinct endpoints, the raw CZ operator times the Boolean-register input frame equals
the updated frame times the logical CZ operator, up to the displayed endpoint-dependent
sign. -/
theorem czFrameTransportB {n : ℕ} (F : PauliFrame n) (lo hi : Fin n) (hn : lo ≠ hi)
    (a d : Bool) :
    rawNetworkCZGateB lo hi a d * pauliFrameGateB F =
      (if (F.1 lo ^^ a) && (F.1 hi ^^ d) then (-1 : ℂ) else 1) •
        (pauliFrameGateB (czFrameResult F lo hi a d) * networkCzGateB lo hi) := by
  ext w v
  have hv : ∀ u : Reg n, u ≠ frameShift F v →
      rawNetworkCZGateB lo hi a d w u * pauliFrameGateB F u v = 0 := by
    intro u hu
    rw [pauliFrameGateB_entry, if_neg hu, mul_zero]
  rw [Matrix.mul_apply, Fintype.sum_eq_single (frameShift F v) hv,
    pauliFrameGateB_entry, if_pos rfl, rawNetworkCZGateB_entry]
  simp only [Matrix.smul_apply, smul_eq_mul, networkCzGateB, Matrix.mul_diagonal]
  rw [pauliFrameGateB_entry, czFrameResult_shift, czFrameResult_sign F lo hi hn]
  by_cases hw : w = rawCZShift lo hi a d (frameShift F v)
  · rw [if_pos hw, if_pos hw]
    have hlo : w lo = ((v lo ^^ F.1 lo) ^^ a) := by
      rw [hw]
      simp [rawCZShift, frameShift]
    have hhi : w hi = ((v hi ^^ F.1 hi) ^^ d) := by
      rw [hw]
      simp [rawCZShift, frameShift, Ne.symm hn]
    rw [hlo, hhi]
    cases hx : F.1 lo <;> cases hz : F.1 hi <;> cases a <;> cases d <;>
      cases vl : v lo <;> cases vh : v hi <;>
      simp [frameBitSign, hx, hz, vl, vh] <;> ring
  · rw [if_neg hw, if_neg hw]
    simp

/-- For distinct endpoints, a raw CZ step on a framed input equals one quarter of conjugation by
the updated Pauli frame times the logical CZ gate. -/
theorem deferred_cz_actual_frame_transport (n : ℕ) (i j : Fin n)
    (h : (i : ℕ) ≠ (j : ℕ)) (F : PauliFrame n) (a d : Bool) (ρ : Operator (2 ^ n)) :
    rawNetworkStepCore (.inr (i, j)) (a, d) (conjBranch (pauliFrameGate n F) ρ) =
      (2 : ℂ)⁻¹ ^ 2 • conjBranch
        (pauliFrameGate n (frameUpdate F (.inr (i, j)) (a, d)) * networkCzGate i j) ρ := by
  let lo := networkCzLo i j
  let hi := networkCzHi i j
  have hn : lo ≠ hi := by
    intro he
    have hh := networkCzLo_lt_hi i j h
    change (lo : ℕ) < (hi : ℕ) at hh
    rw [he] at hh
    exact (lt_irrefl _ hh)
  let c : ℂ := if (F.1 lo ^^ a) && (F.1 hi ^^ d) then -1 else 1
  have hc : ‖c‖ = 1 := by
    unfold c
    split <;> norm_num
  have hm : rawNetworkCZGate lo hi a d * pauliFrameGate n F =
      c • (pauliFrameGate n (frameUpdate F (.inr (i, j)) (a, d)) * networkCzGate i j) := by
    rw [← networkCzGate_lo_hi i j]
    change relabelGate (bitVecEquiv n) (rawNetworkCZGateB lo hi a d) *
      relabelGate (bitVecEquiv n) (pauliFrameGateB F) =
      c • (relabelGate (bitVecEquiv n) (pauliFrameGateB (czFrameResult F lo hi a d)) *
        relabelGate (bitVecEquiv n) (networkCzGateB lo hi))
    rw [← teleportRelabelGate_mul, ← teleportRelabelGate_mul,
      czFrameTransportB F lo hi hn, relabelGate_smul']
  change rawNetworkStepBranch (.inr (i, j)) (a, d) (conjBranch (pauliFrameGate n F) ρ) = _
  rw [rawNetworkCZBranch_apply n i j h]
  have hcomp : conjBranch (rawNetworkCZGate lo hi a d) (conjBranch (pauliFrameGate n F) ρ) =
      conjBranch (rawNetworkCZGate lo hi a d * pauliFrameGate n F) ρ :=
    by
      show ((conjBranch (rawNetworkCZGate lo hi a d)).comp
        (conjBranch (pauliFrameGate n F))) ρ = _
      rw [conjBranch_comp]
  rw [hcomp, hm, deferred_conj_phase c hc]

/-- For one legal gate, the frame-adjusted raw branch transports the input frame to
`frameUpdate` and implements the logical gate with weight one half for a wire or one quarter
for CZ; invalid outcomes give zero. This is the single-step frame identity for the
measurement scheme of [RaussendorfBriegel2000]. -/
theorem deferred_pauli_actual_raw_step_frame_transport :
    ∀ (n : ℕ) (F : PauliFrame n) (g : ClusterNetworkGate n)
      (o : Bool × Bool) (ρ : Operator (2 ^ n)), networkLegal [g] →
      rawNetworkStepCore (frameAdjustedGate F g) o (conjBranch (pauliFrameGate n F) ρ) =
        if networkBranchValid [g] (fun _ => o) then
          ((2 : ℂ)⁻¹)^((networkCounts [g]).1 + 2 * (networkCounts [g]).2) •
            conjBranch (pauliFrameGate n (frameUpdate F g o) * networkLogicalMatrix [g]) ρ
        else 0 := by
  intro n F g o ρ hg
  obtain ⟨a, d⟩ := o
  cases g with
  | inl p =>
      obtain ⟨i, ζ⟩ := p
      have hζ : ‖ζ‖ = 1 := hg (.inl (i, ζ)) (by simp)
      cases d with
      | false =>
          simpa [networkBranchValid, networkCounts, networkLogicalMatrix, networkGateMatrix] using
            deferred_wire_actual_frame_transport n i ζ hζ F a ρ
      | true => simp [frameAdjustedGate, rawNetworkStepCore, networkBranchValid]
  | inr p =>
      obtain ⟨i, j⟩ := p
      have hij : i ≠ j := hg (.inr (i, j)) (by simp)
      have h : (i : ℕ) ≠ (j : ℕ) := fun he => hij (Fin.ext he)
      simpa [frameAdjustedGate, networkBranchValid, networkCounts,
        networkLogicalMatrix, networkGateMatrix] using
        deferred_cz_actual_frame_transport n i j h F a d ρ

/-- Composing conjugation by `B` with conjugation by `A` gives conjugation by the matrix product
`A * B`. -/
theorem deferredConj_comp_apply {D : ℕ} (A B : Operator D) (ρ : Operator D) :
    conjBranch A (conjBranch B ρ) = conjBranch (A * B) ρ := by
  show ((conjBranch A).comp (conjBranch B)) ρ = _
  rw [conjBranch_comp]

/-- For a legal network, the linear history map agrees with `deferredHistoryCore` and sends a
framed input to conjugation by the final frame times the logical matrix, weighted by `2` to
the negative wire-plus-twice-CZ count on valid histories and zero otherwise. This gives the
history frame identity for the measurement scheme of [RaussendorfBriegel2000]. -/
theorem deferred_pauli_actual_history_linear_branch :
    ∀ (n : ℕ) (gs : List (ClusterNetworkGate n))
      (hist : Fin gs.length → Bool × Bool) (F : PauliFrame n), networkLegal gs →
      (∀ ρ : Operator (2 ^ n), deferredHistoryBranch gs hist F ρ = deferredHistoryCore gs hist F ρ) ∧
      (∀ ρ : Operator (2 ^ n), deferredHistoryBranch gs hist F (conjBranch (pauliFrameGate n F) ρ) =
        if networkBranchValid gs hist then
          ((2 : ℂ)⁻¹)^((networkCounts gs).1 + 2 * (networkCounts gs).2) •
            conjBranch (pauliFrameGate n (finalPauliFrame gs hist F) * networkLogicalMatrix gs) ρ
        else 0) := by
  intro n gs
  induction gs with
  | nil =>
      intro hist F _
      refine ⟨fun ρ => rfl, ?_⟩
      intro ρ
      have hv : networkBranchValid [] hist := fun k => absurd k.isLt (by simp)
      simp [deferredHistoryBranch, hv, finalPauliFrame, networkCounts, networkLogicalMatrix]
  | cons g gs ih =>
      intro hist F hgs
      refine ⟨fun ρ => deferredHistoryBranch_apply _ _ _ _, ?_⟩
      intro ρ
      have hg := networkLegal_cons_self g gs hgs
      have ht := networkLegal_cons_of g gs hgs
      have hstep : rawNetworkStepBranch (frameAdjustedGate F g) (hist 0)
          (conjBranch (pauliFrameGate n F) ρ) = _ :=
        deferred_pauli_actual_raw_step_frame_transport n F g (hist 0) ρ hg
      simp only [deferredHistoryBranch, LinearMap.comp_apply]
      rw [hstep]
      by_cases hV1 : networkBranchValid [g] (fun _ => hist 0)
      · rw [if_pos hV1, map_smul]
        have hf : conjBranch (pauliFrameGate n (frameUpdate F g (hist 0)) * networkLogicalMatrix [g]) ρ =
            conjBranch (pauliFrameGate n (frameUpdate F g (hist 0)))
              (conjBranch (networkLogicalMatrix [g]) ρ) :=
          by
            symm
            show ((conjBranch (pauliFrameGate n (frameUpdate F g (hist 0)))).comp
              (conjBranch (networkLogicalMatrix [g]))) ρ = _
            rw [conjBranch_comp]
        rw [hf, (ih ((fun k => hist k.succ)) (frameUpdate F g (hist 0)) ht).2]
        by_cases hV2 : networkBranchValid gs ((fun k => hist k.succ))
        · rw [if_pos hV2,
            if_pos ((networkBranchValid_cons g gs hist).mpr ⟨hV1, hV2⟩),
            smul_smul, ← pow_add, networkCounts_cons g gs, networkLogicalMatrix_cons' g gs, finalPauliFrame]
          rw [deferredConj_comp_apply, Matrix.mul_assoc]

        · rw [if_neg hV2, smul_zero,
            if_neg (fun hv => hV2 ((networkBranchValid_cons g gs hist).mp hv).2)]
      · rw [if_neg hV1, map_zero,
          if_neg (fun hv => hV1 ((networkBranchValid_cons g gs hist).mp hv).1)]

/-- Every Pauli frame operator belongs to the unitary group on `Fin (2 ^ n)`. -/
theorem pauliFrameGate_unitary (n : ℕ) (F : PauliFrame n) :
    pauliFrameGate n F ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  let A : Fin n → Operator 2 := fun i => relabelGate boolEquivFin2
    ((if F.1 i then PauliX else 1) * (if F.2 i then PauliZ else 1))
  have hu : ∀ i, A i ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    intro i
    apply teleportRelabelGate_mem_unitaryGroup
    apply (Matrix.unitaryGroup Bool ℂ).mul_mem
    · cases hx : F.1 i
      · exact (Matrix.unitaryGroup Bool ℂ).one_mem
      · exact pauliX_unitary
    · cases hz : F.2 i
      · exact (Matrix.unitaryGroup Bool ℂ).one_mem
      · exact pauliZ_unitary
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  change (tensorPauliProduct n A)ᴴ * tensorPauliProduct n A = 1
  rw [tensorPauliProduct_conjTranspose, tensorPauliProduct_mul]
  have hh : (fun i => (A i)ᴴ * A i) = fun _ => (1 : Operator 2) := by
    funext i
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp (hu i)
  rw [hh, tensorPauliProduct_one]

/-- The operator of the zero Pauli frame is the identity matrix. -/
theorem zeroPauliFrame_gate (n : ℕ) : pauliFrameGate n (zeroPauliFrame n) = 1 := by
  change tensorPauliProduct n (fun i => relabelGate boolEquivFin2
    ((if (zeroPauliFrame n).1 i then PauliX else 1) *
     (if (zeroPauliFrame n).2 i then PauliZ else 1))) = 1
  simp [zeroPauliFrame, teleportRelabelGate_one, tensorPauliProduct_one]

/-- Starting from the zero frame, a legal network history is weighted conjugation by its final
Pauli frame times the logical matrix when valid, and is zero otherwise. -/
theorem deferredHistoryBranch_zero_formula {n : ℕ} (gs : List (ClusterNetworkGate n))
    (hist : Fin gs.length → Bool × Bool) (hgs : networkLegal gs) (ρ : Operator (2 ^ n)) :
    deferredHistoryBranch gs hist (zeroPauliFrame n) ρ =
      if networkBranchValid gs hist then
        ((2 : ℂ)⁻¹)^((networkCounts gs).1 + 2 * (networkCounts gs).2) •
          conjBranch (pauliFrameGate n (finalPauliFrame gs hist (zeroPauliFrame n)) *
            networkLogicalMatrix gs) ρ else 0 := by
  have h := (deferred_pauli_actual_history_linear_branch n gs hist (zeroPauliFrame n) hgs).2 ρ
  rw [zeroPauliFrame_gate] at h
  simp only [conjBranch_apply, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] at h
  exact h

/-- For a legal network, composing a zero-frame history branch with the inverse final frame
gives conjugation by the logical matrix weighted by `2` to the negative wire-plus-twice-CZ
count for valid histories, and the zero map otherwise. -/
theorem deferredCorrectedBranch_eq {n : ℕ} (gs : List (ClusterNetworkGate n))
    (hist : Fin gs.length → Bool × Bool) (hgs : networkLegal gs) :
    (conjBranch ((pauliFrameGate n (finalPauliFrame gs hist (zeroPauliFrame n)))ᴴ)).comp
      (deferredHistoryBranch gs hist (zeroPauliFrame n)) =
      if networkBranchValid gs hist then
        ((2 : ℂ)⁻¹)^((networkCounts gs).1 + 2 * (networkCounts gs).2) •
          conjBranch (networkLogicalMatrix gs) else 0 := by
  let P := pauliFrameGate n (finalPauliFrame gs hist (zeroPauliFrame n))
  have hp : Pᴴ * P = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp (pauliFrameGate_unitary n
        (finalPauliFrame gs hist (zeroPauliFrame n)))
  apply LinearMap.ext
  intro ρ
  rw [LinearMap.comp_apply, deferredHistoryBranch_zero_formula gs hist hgs ρ]
  by_cases hv : networkBranchValid gs hist
  · rw [if_pos hv, if_pos hv, map_smul]
    change _ = _
    have hc : conjBranch Pᴴ (conjBranch (P * networkLogicalMatrix gs) ρ) =
        conjBranch (networkLogicalMatrix gs) ρ := by
      show ((conjBranch Pᴴ).comp (conjBranch (P * networkLogicalMatrix gs))) ρ = _
      rw [conjBranch_comp, ← Matrix.mul_assoc, hp, Matrix.one_mul]
    exact congrArg (fun X => ((2 : ℂ)⁻¹)^((networkCounts gs).1 + 2 * (networkCounts gs).2) • X) hc
  · simp [hv]

end Qatlib.Concepts.ClusterPatterns.PauliNetwork
