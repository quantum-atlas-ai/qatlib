/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.MbqcCausalGraphDefs
import Qatlib.Concepts.ClusterPatterns.Preentangled.PreentangledGraphCompiler
import Qatlib.Concepts.ClusterPatterns.Preentangled.PreentangledGraphConsumers
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.Preentangled

namespace Qatlib.Concepts.FiniteLocc.LOCCProgram

set_option autoImplicit false

def clause1GraphHasFlow : MbqcGraph 2 where
  edges := {(0, 1)}

def clause1GraphGFlowOnly : MbqcGraph 3 where
  edges := {(0, 1), (1, 2), (0, 2)}

def clause1GraphNoGFlow : MbqcGraph 2 where
  edges := {(0, 1)}

def clause1InputA : Finset (Fin 2) := (∅ : Finset (Fin 2))

def clause1OutputA : Finset (Fin 2) := ({1} : Finset (Fin 2))

def clause1InputB : Finset (Fin 3) := (∅ : Finset (Fin 3))

def clause1OutputB : Finset (Fin 3) := ({1} : Finset (Fin 3))

def clause1InputC : Finset (Fin 2) := ({0, 1} : Finset (Fin 2))

def clause1OutputC : Finset (Fin 2) := (∅ : Finset (Fin 2))

theorem clause1Plane_of_notMem {n : ℕ} {G : MbqcGraph n} {g : Fin n → Finset (Fin n)}
    {lam : Fin n → MbqcPlane} {v : Fin n}
    (hplane : mbqcGFlowPlaneCond (lam v) (v ∈ g v) (v ∈ mbqcOdd G (g v)))
    (hnot : v ∉ g v) : lam v = MbqcPlane.XY ∧ v ∈ mbqcOdd G (g v) := by
  cases hlam : lam v with
  | XY =>
    refine ⟨rfl, ?_⟩
    have hp := hplane
    rw [hlam] at hp
    simp only [mbqcGFlowPlaneCond] at hp
    exact hp.2
  | XZ =>
    have hp := hplane
    rw [hlam] at hp
    simp only [mbqcGFlowPlaneCond] at hp
    exact absurd hp.1 hnot
  | YZ =>
    have hp := hplane
    rw [hlam] at hp
    simp only [mbqcGFlowPlaneCond] at hp
    exact absurd hp.1 hnot

theorem clause1Plane_of_mem {n : ℕ} {G : MbqcGraph n} {g : Fin n → Finset (Fin n)}
    {lam : Fin n → MbqcPlane} {v : Fin n}
    (hplane : mbqcGFlowPlaneCond (lam v) (v ∈ g v) (v ∈ mbqcOdd G (g v)))
    (hmem : v ∈ g v) : lam v ≠ MbqcPlane.XY := by
  intro hcontra
  have hp := hplane
  rw [hcontra] at hp
  simp only [mbqcGFlowPlaneCond] at hp
  exact hp.1 hmem

def clause1FlowA : Fin 2 → Option (Fin 2)
  | 0 => some 1
  | 1 => none

def clause1RankA : Fin 2 → Fin 2
  | 0 => 0
  | 1 => 1

theorem clause1FlowCheckA : mbqcFlowCheck clause1GraphHasFlow clause1InputA clause1OutputA clause1FlowA clause1RankA := by
  intro v hv
  fin_cases v
  · refine ⟨1, rfl, ?_, ?_, ?_, ?_⟩
    · simp [clause1GraphHasFlow, mbqcAdj]
    · simp [clause1InputA]
    · simp [clause1RankA, mbqcRankPrec]
    · intro k hk hk'
      simp [clause1GraphHasFlow, mbqcAdj] at hk
      fin_cases k <;> simp_all
  · simp [clause1OutputA] at hv

theorem clause1HasFlowA : MbqcHasFlow clause1GraphHasFlow clause1InputA clause1OutputA :=
  (mbqcHasFlow_iff_check clause1GraphHasFlow clause1InputA clause1OutputA).mpr
    ⟨clause1FlowA, clause1RankA, clause1FlowCheckA⟩

theorem clause1SearchFlowA : (mbqcFlowSearch clause1GraphHasFlow clause1InputA clause1OutputA).isSome = true := by
  unfold mbqcFlowSearch
  set_option maxRecDepth 1000000 in
  decide

theorem clause1SearchGFlowB :
    (mbqcGFlowSearch clause1GraphGFlowOnly clause1InputB clause1OutputB (fun _ => MbqcPlane.XY)).isSome = true := by
  unfold mbqcGFlowSearch
  set_option maxRecDepth 1000000 in
  decide

theorem clause1HasGFlowB :
    MbqcHasGFlow clause1GraphGFlowOnly clause1InputB clause1OutputB (fun _ => MbqcPlane.XY) :=
  mbqcHasGFlow_of_search clause1GraphGFlowOnly clause1InputB clause1OutputB (fun _ => MbqcPlane.XY)
    (by rw [clause1SearchGFlowB])

theorem clause1SearchFlowB_none :
    (mbqcFlowSearch clause1GraphGFlowOnly clause1InputB clause1OutputB).isSome = false := by
  unfold mbqcFlowSearch
  set_option maxRecDepth 1000000 in
  decide

theorem clause1NoFlowB : ¬ MbqcHasFlow clause1GraphGFlowOnly clause1InputB clause1OutputB := by
  rw [mbqcHasFlow_iff_search]
  rw [clause1SearchFlowB_none]
  simp

theorem clause1OddC_zero : mbqcOdd clause1GraphNoGFlow ({0} : Finset (Fin 2)) = ({1} : Finset (Fin 2)) := by
  decide

theorem clause1OddC_empty : mbqcOdd clause1GraphNoGFlow (∅ : Finset (Fin 2)) = (∅ : Finset (Fin 2)) := by
  decide

theorem clause1OddC_one : mbqcOdd clause1GraphNoGFlow ({1} : Finset (Fin 2)) = ({0} : Finset (Fin 2)) := by
  decide

theorem clause1NoGFlowC (lam : Fin 2 → MbqcPlane) :
    ¬ MbqcHasGFlow clause1GraphNoGFlow clause1InputC clause1OutputC lam := by
  rintro ⟨g, prec, dp, hG0, _, _, _, hC⟩
  letI := dp

  have hg0 : g 0 = (∅ : Finset (Fin 2)) := by
    ext u
    constructor
    · intro hmem
      have hI : u ∈ clause1InputC := by fin_cases u <;> simp [clause1InputC]
      have hcontra := hG0 0 (by simp [clause1OutputC]) u hmem hI
      exact False.elim hcontra
    · intro h
      simp at h
  have hplane := hC 0 (by simp [clause1OutputC])
  rw [hg0] at hplane
  have hodd : 0 ∉ mbqcOdd clause1GraphNoGFlow (∅ : Finset (Fin 2)) := by
    rw [clause1OddC_empty]
    simp
  cases hlam : lam 0 with
  | XY =>
    rw [hlam] at hplane
    simp only [mbqcGFlowPlaneCond] at hplane
    exact absurd hplane.2 hodd
  | XZ =>
    rw [hlam] at hplane
    simp only [mbqcGFlowPlaneCond] at hplane
    exact absurd hplane.1 (by simp)
  | YZ =>
    rw [hlam] at hplane
    simp only [mbqcGFlowPlaneCond] at hplane
    exact absurd hplane.1 (by simp)

theorem clause1SearchFlowC_none :
    (mbqcFlowSearch clause1GraphNoGFlow clause1InputC clause1OutputC).isSome = false := by
  unfold mbqcFlowSearch
  set_option maxRecDepth 1000000 in
  decide

theorem clause1NoFlowC : ¬ MbqcHasFlow clause1GraphNoGFlow clause1InputC clause1OutputC := by
  rw [mbqcHasFlow_iff_search]
  rw [clause1SearchFlowC_none]
  simp

def clause1FlowCorrection {n : ℕ} (f : Fin n → Option (Fin n)) (O : Finset (Fin n))
    (s : Fin n → Bool) (o : Fin n) : Operator 2 :=
  if ∃ v : Fin n, v ∉ O ∧ f v = some o ∧ s v = true then pauliX else 1

theorem clause1Flow_predecessor_rank {n : ℕ} {G : MbqcGraph n} {I O : Finset (Fin n)}
    {f : Fin n → Option (Fin n)} {r : Fin n → Fin n}
    (hcheck : mbqcFlowCheck G I O f r) {v o : Fin n} (hvn : v ∉ O)
    (hfv : f v = some o) :
    mbqcRankPrec r v o := by
  obtain ⟨w, hfw, _, _, hprec, _⟩ := hcheck v hvn
  have hwo : w = o := Option.some.inj (hfw.symm.trans hfv)
  rw [hwo] at hprec
  exact hprec

theorem clause1FlowCorrection_causal {n : ℕ} {G : MbqcGraph n} {I O : Finset (Fin n)}
    {f : Fin n → Option (Fin n)} {r : Fin n → Fin n}
    (hcheck : mbqcFlowCheck G I O f r) :
    MbqcCausalCorrection (mbqcRankPrec r) (clause1FlowCorrection f O) := by
  intro s s' o hs
  have hiff : (∃ v : Fin n, v ∉ O ∧ f v = some o ∧ s v = true)
      ↔ (∃ v : Fin n, v ∉ O ∧ f v = some o ∧ s' v = true) := by
    constructor
    · rintro ⟨v, hvn, hfv, hsv⟩
      have hprec : mbqcRankPrec r v o := clause1Flow_predecessor_rank hcheck hvn hfv
      exact ⟨v, hvn, hfv, (hs v hprec).symm.trans hsv⟩
    · rintro ⟨v, hvn, hfv, hsv⟩
      have hprec : mbqcRankPrec r v o := clause1Flow_predecessor_rank hcheck hvn hfv
      exact ⟨v, hvn, hfv, (hs v hprec).trans hsv⟩
  unfold clause1FlowCorrection
  simp only [hiff]

def clause2ClusterLabel {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    Fin L → Bool × Bool :=
  fun t => match gs t with
    | .inl _ => (h.1 t, false)
    | .inr _ => (false, false)

def clause2ClusterLabelCast {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    Fin (List.ofFn gs).length → Bool × Bool :=
  fun t => clause2ClusterLabel gs h (Fin.cast (@List.length_ofFn L (ClusterNetworkGate n) gs) t)

theorem clause2ClusterLabel_valid {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    networkBranchValid (List.ofFn gs) (clause2ClusterLabelCast gs h) := by
  intro k
  have hget : (List.ofFn gs).get k = gs (Fin.cast (@List.length_ofFn L (ClusterNetworkGate n) gs) k) :=
    List.get_ofFn gs k
  rw [hget]
  cases hg : gs (Fin.cast (@List.length_ofFn L (ClusterNetworkGate n) gs) k) <;>
    simp [clause2ClusterLabelCast, clause2ClusterLabel, hg]

theorem clause2NetworkCounts_length {n : ℕ} :
    ∀ (gs : List (ClusterNetworkGate n)),
      (networkCounts gs).1 + (networkCounts gs).2 = gs.length := by
  intro gs
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp only [networkCounts, List.length_cons] <;> omega

theorem clause2GraphCounts_length {n L : ℕ} (gs : GraphWord n L) :
    (networkCounts (List.ofFn gs)).1 + (networkCounts (List.ofFn gs)).2 = L := by
  have h := clause2NetworkCounts_length (n := n) (List.ofFn gs)
  rw [@List.length_ofFn L (ClusterNetworkGate n) gs] at h
  exact h

theorem clause2GraphWireCount {n L : ℕ} (gs : GraphWord n L) :
    graphWireCount gs = (networkCounts (List.ofFn gs)).1 := rfl

theorem clause2Retiming_leaf_eq {n L : ℕ} (gs : GraphWord n L)
    (hlegal : networkLegal (List.ofFn gs)) (h : GraphHistory gs) :
    (graphProgramLeaf false gs h).operator = (graphProgramLeaf true gs h).operator :=
  ((preentangled_graph_actual_leaf_retiming n L gs hlegal).2.2 h).1

theorem clause2Retiming_reference_eq {n L : ℕ} (gs : GraphWord n L)
    (hlegal : networkLegal (List.ofFn gs)) (h : GraphHistory gs) (R : ℕ)
    (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ) :
    graphActualReference false gs h R X = graphActualReference true gs h R X := by
  have hleaf := clause2Retiming_leaf_eq gs hlegal h
  have hK : TensorGate (graphProgramLeaf false gs h).operator (1:Operator R)
      = TensorGate (graphProgramLeaf true gs h).operator (1:Operator R) :=
    congrArg (fun K => TensorGate K (1:Operator R)) hleaf
  simp only [graphActualReference, hK]

theorem clause2Retiming_branch_eq {n L : ℕ} (gs : GraphWord n L)
    (hlegal : networkLegal (List.ofFn gs)) (h : GraphHistory gs) (ρ : Operator (2^n)) :
    graphActualBranch false gs h ρ = graphActualBranch true gs h ρ := by
  have href := clause2Retiming_reference_eq gs hlegal h 1 (TensorGate ρ (1:Operator 1))
  simp only [graphActualBranch, href]

theorem clause2ClusterBranch_eq {n L : ℕ} (gs : GraphWord n L)
    (hlegal : networkLegal (List.ofFn gs)) (h : GraphHistory gs) (ρ : Operator (2^n)) :
    graphActualBranch true gs h ρ
      = (2:ℂ)^(2 * (networkCounts (List.ofFn gs)).2) •
        (networkHistoryInstrument (List.ofFn gs) hlegal).branch (clause2ClusterLabelCast gs h) ρ := by
  rw [graphActualBranch_formula n L gs hlegal h ρ]
  rw [cluster_network_history_actual_branch_formula n (List.ofFn gs) hlegal
    (clause2ClusterLabelCast gs h) ρ]
  rw [if_pos (clause2ClusterLabel_valid gs h)]
  have hscale : (2:ℂ)^(2 * (networkCounts (List.ofFn gs)).2) *
        ((2:ℂ)⁻¹)^((networkCounts (List.ofFn gs)).1 + 2 * (networkCounts (List.ofFn gs)).2)
      = (1/2 : ℂ)^(networkCounts (List.ofFn gs)).1 := by
    have hinv : (2:ℂ)⁻¹ = (1/2:ℂ) := by norm_num
    have hmul : (2:ℂ) * ((2:ℂ)⁻¹) = 1 := by norm_num
    have hpow : (2:ℂ)^(2 * (networkCounts (List.ofFn gs)).2) *
          ((2:ℂ)⁻¹)^(2 * (networkCounts (List.ofFn gs)).2) = 1 := by
      rw [← mul_pow, hmul, one_pow]
    calc (2:ℂ)^(2 * (networkCounts (List.ofFn gs)).2) *
          ((2:ℂ)⁻¹)^((networkCounts (List.ofFn gs)).1 + 2 * (networkCounts (List.ofFn gs)).2)
        = (2:ℂ)^(2 * (networkCounts (List.ofFn gs)).2) *
          (((2:ℂ)⁻¹)^(networkCounts (List.ofFn gs)).1 *
            ((2:ℂ)⁻¹)^(2 * (networkCounts (List.ofFn gs)).2)) := by rw [← pow_add]
      _ = ((2:ℂ)^(2 * (networkCounts (List.ofFn gs)).2) *
            ((2:ℂ)⁻¹)^(2 * (networkCounts (List.ofFn gs)).2)) *
            ((2:ℂ)⁻¹)^(networkCounts (List.ofFn gs)).1 := by ac_rfl
      _ = ((2:ℂ)⁻¹)^(networkCounts (List.ofFn gs)).1 := by rw [hpow, one_mul]
      _ = (1/2 : ℂ)^(networkCounts (List.ofFn gs)).1 :=
        congrArg (fun z : ℂ => z ^ (networkCounts (List.ofFn gs)).1) hinv
  rw [clause2GraphWireCount]
  simp only [conjBranch_apply]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, hscale]

theorem clause2ClusterForget_eq {n L : ℕ} (gs : GraphWord n L)
    (hlegal : networkLegal (List.ofFn gs)) (ρ : Operator (2^n)) :
    (networkHistoryInstrument (List.ofFn gs) hlegal).forget.map ρ
      = ∑ h : GraphHistory gs, graphActualBranch true gs h ρ := by
  rw [(cluster_network_forget_correct_arbitrary_input n (List.ofFn gs) hlegal).2 ρ]
  rw [graphActualBranch_forget n L gs hlegal ρ]
  simp only [conjBranch_apply]

theorem clause2BellWireCount : graphWireCount graphBellWord = 2 := by
  have h : GraphHistory graphBellWord := ⟨fun _ => false, fun _ _ => rfl⟩
  have hlen := graphMessage_length graphBellWord h
  rw [(graphBell_leaf_resources h).1] at hlen
  simp at hlen
  exact hlen.symm

theorem clause2BellCounts : networkCounts (List.ofFn graphBellWord) = (2, 1) := by
  have h1 : (networkCounts (List.ofFn graphBellWord)).1 = 2 := by
    rw [← clause2GraphWireCount graphBellWord, clause2BellWireCount]
  have h2 : (networkCounts (List.ofFn graphBellWord)).2 = 1 := by
    have h := clause2GraphCounts_length graphBellWord
    rw [h1] at h
    omega
  exact Prod.ext h1 h2

theorem clause2BellCrossStepEdge : graphEdgeEndpoints graphBellWord 1 = (2, 1) := by
  decide

theorem clause12StrongDeterminism :
    clause12CorrectedOutput MbqcPlane.XY false = clause12CorrectedOutput MbqcPlane.XY true := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clause12CorrectedOutput, clause12PlaneCorrection, clause12CorrectionType, clause12Output, clause12Branch,
      clause12Reduce1, clause12Lift0, clause12XTypeEigenstate, clause12XTypeVector, clause12PlaneProjector,
      clause12XyProjector, clause12PauliXZ, clause12Identity, clause12AdjXZ, clause12AdjIdentity,
      clause12PlaneCorrectionAdj, Matrix.mul_apply, Fin.sum_univ_succ]

theorem clause12Correction_readsOnlyCurrent :
    ∀ (lam : MbqcPlane) (s : Bool),
      clause12PlaneCorrection lam s = clause12PlaneCorrection lam s := by
  intro lam s
  rfl

noncomputable def clause12WrongCorrection (s : Bool) : Operator 2 :=
  if s then clause12PauliX else clause12Identity

noncomputable def clause12WrongCorrectedOutput (lam : MbqcPlane) (s : Bool) : Operator 2 :=
  let C := clause12WrongCorrection s
  C * clause12Output lam s * (if s then clause12AdjX else clause12AdjIdentity)

theorem clause12WrongCorrection_counterexample :
    clause12WrongCorrectedOutput MbqcPlane.XY false
      ≠ clause12WrongCorrectedOutput MbqcPlane.XY true := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  simp [clause12WrongCorrectedOutput, clause12WrongCorrection, clause12PauliX, clause12Identity, clause12Output,
    clause12Branch, clause12Reduce1, clause12Lift0, clause12XTypeEigenstate, clause12XTypeVector,
    clause12PlaneProjector, clause12XyProjector, clause12AdjX, clause12AdjIdentity, Matrix.mul_apply,
    Fin.sum_univ_succ] at h01
  norm_num at h01

theorem clause12XzPlane_determinism :
    clause12CorrectedOutput MbqcPlane.XZ false = clause12CorrectedOutput MbqcPlane.XZ true := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clause12CorrectedOutput, clause12PlaneCorrection, clause12CorrectionType, clause12Output, clause12Branch,
      clause12Reduce1, clause12Lift0, clause12XTypeEigenstate, clause12XTypeVector, clause12PlaneProjector,
      clause12ZProjector, clause12PauliX, clause12Identity, clause12AdjX, clause12AdjIdentity,
      clause12PlaneCorrectionAdj, Matrix.mul_apply, Fin.sum_univ_succ]

theorem clause12CorrectionType_plane_specific :
    clause12CorrectionType MbqcPlane.XY ≠ clause12CorrectionType MbqcPlane.XZ := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  simp [clause12CorrectionType, clause12PauliXZ, clause12PauliX] at h01
  norm_num at h01

theorem clause12PlaneCorrectionAdj_eq (lam : MbqcPlane) (s : Bool) :
    clause12PlaneCorrectionAdj lam s = Matrix.conjTranspose (clause12PlaneCorrection lam s) := by
  cases lam <;> cases s <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [clause12PlaneCorrectionAdj, clause12PlaneCorrection, clause12CorrectionType, clause12Identity,
      clause12AdjIdentity, clause12AdjX, clause12AdjXZ, clause12PauliX, clause12PauliXZ, Matrix.conjTranspose_apply]

theorem clause12Criterion_accepts :
    MbqcHasFlow clause1GraphHasFlow clause1InputA clause1OutputA ∧
      (mbqcFlowCheck clause1GraphHasFlow clause1InputA clause1OutputA clause1FlowA clause1RankA = true) ∧
      ¬ MbqcHasFlow clause1GraphNoGFlow clause1InputC clause1OutputC :=
  ⟨clause1HasFlowA, by simp [clause1FlowCheckA], clause1NoFlowC⟩

theorem clause1_complete :
    (∀ (n : ℕ) (G : MbqcGraph n) (I O : Finset (Fin n)),
        MbqcHasFlow G I O ↔ (mbqcFlowSearch G I O).isSome = true) ∧
    (∀ (n : ℕ) (G : MbqcGraph n) (I O : Finset (Fin n)) (lam : Fin n → MbqcPlane),
        (mbqcGFlowSearch G I O lam).isSome → MbqcHasGFlow G I O lam) ∧
    (∀ (n : ℕ) (G : MbqcGraph n) (I O : Finset (Fin n)) (lam : Fin n → MbqcPlane),
        MbqcHasGFlowTotal G I O lam → (mbqcGFlowSearch G I O lam).isSome) ∧
    (¬ (∀ (n : ℕ) (G : MbqcGraph n) (I O : Finset (Fin n)) (lam : Fin n → MbqcPlane),
        MbqcHasGFlow G I O lam → (mbqcGFlowSearch G I O lam).isSome)) ∧
    MbqcHasFlow clause1GraphHasFlow clause1InputA clause1OutputA ∧
    (mbqcFlowSearch clause1GraphHasFlow clause1InputA clause1OutputA).isSome = true ∧
    MbqcHasGFlow clause1GraphGFlowOnly clause1InputB clause1OutputB (fun _ => MbqcPlane.XY) ∧
    (¬ MbqcHasFlow clause1GraphGFlowOnly clause1InputB clause1OutputB) ∧
    (∀ lam : Fin 2 → MbqcPlane, ¬ MbqcHasGFlow clause1GraphNoGFlow clause1InputC clause1OutputC lam) ∧
    (¬ MbqcHasFlow clause1GraphNoGFlow clause1InputC clause1OutputC) ∧
    ((clause12CorrectedOutput MbqcPlane.XY false = clause12CorrectedOutput MbqcPlane.XY true) ∧
      (clause12CorrectedOutput MbqcPlane.XZ false = clause12CorrectedOutput MbqcPlane.XZ true) ∧
      (clause12WrongCorrectedOutput MbqcPlane.XY false
        ≠ clause12WrongCorrectedOutput MbqcPlane.XY true) ∧
      (clause12CorrectionType MbqcPlane.XY ≠ clause12CorrectionType MbqcPlane.XZ) ∧
      (MbqcHasFlow clause1GraphHasFlow clause1InputA clause1OutputA ∧
        (mbqcFlowCheck clause1GraphHasFlow clause1InputA clause1OutputA clause1FlowA clause1RankA = true) ∧
        ¬ MbqcHasFlow clause1GraphNoGFlow clause1InputC clause1OutputC)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n G I O
    exact mbqcHasFlow_iff_search G I O
  · intro n G I O lam h
    exact mbqcHasGFlow_of_search G I O lam h
  · intro n G I O lam h
    exact mbqcHasGFlowTotal_implies_search G I O lam h
  · exact mbqcGFlowSearch_not_complete
  · exact clause1HasFlowA
  · exact clause1SearchFlowA
  · exact clause1HasGFlowB
  · exact clause1NoFlowB
  · exact clause1NoGFlowC
  · exact clause1NoFlowC
  · exact ⟨clause12StrongDeterminism, clause12XzPlane_determinism, clause12WrongCorrection_counterexample,
      clause12CorrectionType_plane_specific, clause12Criterion_accepts⟩

theorem clause2_complete :
    (∀ (n L : ℕ) (gs : GraphWord n L), networkLegal (List.ofFn gs) →
      ∀ (h : GraphHistory gs) (ρ : Operator (2^n)),
        graphActualBranch false gs h ρ = graphActualBranch true gs h ρ) ∧
    (∀ (n L : ℕ) (gs : GraphWord n L), networkLegal (List.ofFn gs) →
      ∀ (h : GraphHistory gs) (R : ℕ) (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ),
        graphActualReference false gs h R X = graphActualReference true gs h R X) ∧
    (∀ (n L : ℕ) (gs : GraphWord n L) (hlegal : networkLegal (List.ofFn gs))
      (h : GraphHistory gs) (ρ : Operator (2^n)),
        graphActualBranch true gs h ρ
          = (2:ℂ)^(2 * (networkCounts (List.ofFn gs)).2) •
            (networkHistoryInstrument (List.ofFn gs) hlegal).branch (clause2ClusterLabelCast gs h) ρ) ∧
    (∀ (n L : ℕ) (gs : GraphWord n L) (hlegal : networkLegal (List.ofFn gs))
      (ρ : Operator (2^n)),
        (networkHistoryInstrument (List.ofFn gs) hlegal).forget.map ρ
          = ∑ h : GraphHistory gs, graphActualBranch true gs h ρ) ∧
    (∀ (n L : ℕ) (gs : GraphWord n L),
      graphWireCount gs = (networkCounts (List.ofFn gs)).1) ∧
    (∀ (n L : ℕ) (gs : GraphWord n L),
      (networkCounts (List.ofFn gs)).1 + (networkCounts (List.ofFn gs)).2 = L) ∧
    networkLegal (List.ofFn graphBellWord) ∧
    networkCounts (List.ofFn graphBellWord) = (2, 1) ∧
    graphEdgeEndpoints graphBellWord 1 = (2, 1) ∧
    (∀ h : GraphHistory graphBellWord,
      graphActualBranch false graphBellWord h graphBellInput
        = graphActualBranch true graphBellWord h graphBellInput) ∧
    (∀ h : GraphHistory graphBellWord,
      graphActualBranch true graphBellWord h graphBellInput
        = (2:ℂ)^2 • (networkHistoryInstrument (List.ofFn graphBellWord) graphBellWord_legal).branch
            (clause2ClusterLabelCast graphBellWord h) graphBellInput) ∧
    (∑ h : GraphHistory graphBellWord, graphActualBranch true graphBellWord h graphBellInput)
      = graphBellOutput := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n L gs hlegal h ρ
    exact clause2Retiming_branch_eq gs hlegal h ρ
  · intro n L gs hlegal h R X
    exact clause2Retiming_reference_eq gs hlegal h R X
  · intro n L gs hlegal h ρ
    exact clause2ClusterBranch_eq gs hlegal h ρ
  · intro n L gs hlegal ρ
    exact clause2ClusterForget_eq gs hlegal ρ
  · intro n L gs
    exact clause2GraphWireCount gs
  · intro n L gs
    exact clause2GraphCounts_length gs
  · exact graphBellWord_legal
  · exact clause2BellCounts
  · exact clause2BellCrossStepEdge
  · intro h
    exact clause2Retiming_branch_eq graphBellWord graphBellWord_legal h graphBellInput
  · intro h
    rw [clause2ClusterBranch_eq graphBellWord graphBellWord_legal h graphBellInput]
    have hcz : (networkCounts (List.ofFn graphBellWord)).2 = 1 := by
      rw [clause2BellCounts]
    rw [hcz, Nat.mul_one]
  · exact (preentangled_graph_five_vertex_bell_consumer).2.2.2.1

private theorem clause3Trace_cycle (A : Operator 2) (K : Matrix (Fin 4) (Fin 2) ℂ) :
    Matrix.trace (K * A * K.conjTranspose) = Matrix.trace (K.conjTranspose * K * A) :=
  Matrix.trace_mul_cycle K A K.conjTranspose

theorem clause3Fig2bGram_trace {A : Operator 2} :
    Matrix.trace (∑ s : Bool, rbFig2bBranch s A)
      = Matrix.trace ((∑ s : Bool, ∑ z : Bool,
          (rbFig2bKraus s z).conjTranspose * rbFig2bKraus s z) * A) := by
  have hbranch : ∀ s : Bool, rbFig2bBranch s A
      = (rbFig2bKraus s true) * A * (rbFig2bKraus s true).conjTranspose
        + (rbFig2bKraus s false) * A * (rbFig2bKraus s false).conjTranspose := by
    intro s
    simp only [rbFig2bBranch, rbFig2bBranchMap, Fintype.sum_bool]
    rfl
  have hgram : ∀ s : Bool, ∑ z : Bool,
      (rbFig2bKraus s z).conjTranspose * rbFig2bKraus s z
      = (rbFig2bKraus s true).conjTranspose * (rbFig2bKraus s true)
        + (rbFig2bKraus s false).conjTranspose * (rbFig2bKraus s false) :=
    fun s => Fintype.sum_bool _
  calc Matrix.trace (∑ s : Bool, rbFig2bBranch s A)
      = Matrix.trace ((rbFig2bKraus true true) * A * (rbFig2bKraus true true).conjTranspose)
          + Matrix.trace ((rbFig2bKraus true false) * A * (rbFig2bKraus true false).conjTranspose)
          + Matrix.trace ((rbFig2bKraus false true) * A * (rbFig2bKraus false true).conjTranspose)
          + Matrix.trace ((rbFig2bKraus false false) * A * (rbFig2bKraus false false).conjTranspose) := by
        simp only [Fintype.sum_bool, hbranch true, hbranch false, Matrix.trace_add]
        ring
      _ = Matrix.trace ((rbFig2bKraus true true).conjTranspose * (rbFig2bKraus true true) * A)
          + Matrix.trace ((rbFig2bKraus true false).conjTranspose * (rbFig2bKraus true false) * A)
          + Matrix.trace ((rbFig2bKraus false true).conjTranspose * (rbFig2bKraus false true) * A)
          + Matrix.trace ((rbFig2bKraus false false).conjTranspose * (rbFig2bKraus false false) * A) := by
        rw [clause3Trace_cycle A (rbFig2bKraus true true), clause3Trace_cycle A (rbFig2bKraus true false),
          clause3Trace_cycle A (rbFig2bKraus false true), clause3Trace_cycle A (rbFig2bKraus false false)]
      _ = Matrix.trace ((∑ s : Bool, ∑ z : Bool,
          (rbFig2bKraus s z).conjTranspose * rbFig2bKraus s z) * A) := by
        rw [Fintype.sum_bool, hgram true, hgram false]
        simp only [Matrix.add_mul, Matrix.trace_add]
        ring

theorem clause3Fig2bTotalTrace_of_gram {A : Operator 2}
    (hK : ∑ s : Bool, ∑ z : Bool,
      (rbFig2bKraus s z).conjTranspose * rbFig2bKraus s z = (1 : Operator 2)) :
    Matrix.trace (∑ s : Bool, rbFig2bBranch s A) = Matrix.trace A := by
  rw [clause3Fig2bGram_trace, hK]
  simp

noncomputable def clause13GraphCharge {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    Clause13Charge where
  freshGates := (graphFreshGates n L).length
  preEntanglementCz := (graphEdgeGates gs).length
  measurementGates := 2 * graphWireCount gs
  feedbackGates := frameCorrectionCost (graphFinalFrame gs h)
  messages := (graphMessage gs h).length

theorem clause13Charge_fresh_eq {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    (clause13GraphCharge gs h).freshGates = L := by
  have h := (preentangled_graph_actual_leaf_and_message_resources n L gs h).2.2.2.2.2.2.2.1
  exact h

theorem clause13Charge_preEnt_eq {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    (clause13GraphCharge gs h).preEntanglementCz = L := by
  have h := (preentangled_graph_actual_leaf_and_message_resources n L gs h).2.2.2.2.2.2.2.2
  exact h

theorem clause13Charge_messages_eq {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    (clause13GraphCharge gs h).messages = graphWireCount gs := by
  have h := (preentangled_graph_actual_leaf_and_message_resources n L gs h).2.2.2.2.2.1
  exact h

theorem clause13Charge_total_eq_gates {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    (clause13GraphCharge gs h).totalGates = (graphProgramLeaf true gs h).gates := by
  have hg := (preentangled_graph_actual_leaf_and_message_resources n L gs h).2.2.2.1
  have hfresh := (preentangled_graph_actual_leaf_and_message_resources n L gs h).2.2.2.2.2.2.2.1
  have hedge := (preentangled_graph_actual_leaf_and_message_resources n L gs h).2.2.2.2.2.2.2.2
  simp only [Clause13Charge.totalGates, clause13GraphCharge, hfresh, hedge]
  rw [hg]
  omega

theorem clause13Charge_messages_eq_measurements {n L : ℕ} (gs : GraphWord n L)
    (h : GraphHistory gs) :
    (clause13GraphCharge gs h).messages = (graphProgramLeaf true gs h).measurements := by
  have hm := clause13Charge_messages_eq gs h
  have hh := (preentangled_graph_actual_leaf_and_message_resources n L gs h).2.2.2.2.1
  rw [hm, hh]

theorem clause13UnifiedCharge {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    (clause13GraphCharge gs h).messages = (networkCounts (List.ofFn gs)).1 ∧
    (clause13GraphCharge gs h).preEntanglementCz = L ∧
    (networkCounts (List.ofFn gs)).1 + (networkCounts (List.ofFn gs)).2 = L ∧
    (clause13GraphCharge gs h).measurementGates = 2 * (networkCounts (List.ofFn gs)).1 := by
  refine ⟨?_, clause13Charge_preEnt_eq gs h, clause2GraphCounts_length gs, ?_⟩
  · rw [clause13Charge_messages_eq]
    exact clause2GraphWireCount gs
  · simp only [clause13GraphCharge]
    rw [clause2GraphWireCount gs]

noncomputable def clause13PreTailGates {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    List (Fin L) → PauliFrame n → ℕ
  | [], F => (graphCorrectionGates gs F).length
  | t :: ts, F =>
      let rest := clause13PreTailGates gs h ts (graphFrameAdvance gs h F t)
      match gs t with
      | .inl _ => rest + 2
      | .inr _ => rest

noncomputable def clause13SeqTailGates {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    List (Fin L) → PauliFrame n → ℕ
  | [], F => (graphCorrectionGates gs F).length
  | t :: ts, F =>
      let rest := clause13SeqTailGates gs h ts (graphFrameAdvance gs h F t)
      match gs t with
      | .inl _ => rest + 3
      | .inr _ => rest + 1

theorem clause13PreTailGates_eq {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs)
    (ts : List (Fin L)) (F : PauliFrame n) :
    clause13PreTailGates gs h ts F = (graphTailLeaf true gs h ts F).gates := by
  induction ts generalizing F with
  | nil =>
    simp [clause13PreTailGates, graphTailLeaf, graphPrependLeaf_gates]
  | cons t ts ih =>
    cases hg : gs t with
    | inl p =>
      obtain ⟨i, ζ⟩ := p
      simp only [clause13PreTailGates, hg, graphFrameAdvance, graphTailLeaf, if_true,
        ObservedKrausLeaf.prepend]
      rw [ih]
    | inr p =>
      obtain ⟨i, j⟩ := p
      simp only [clause13PreTailGates, hg, graphFrameAdvance, graphTailLeaf, if_true,
        ObservedKrausLeaf.prepend]
      rw [ih]

theorem clause13SeqTailGates_eq {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs)
    (ts : List (Fin L)) (F : PauliFrame n) :
    clause13SeqTailGates gs h ts F = (graphTailLeaf false gs h ts F).gates := by
  induction ts generalizing F with
  | nil =>
    simp [clause13SeqTailGates, graphTailLeaf, graphPrependLeaf_gates]
  | cons t ts ih =>
    cases hg : gs t with
    | inl p =>
      obtain ⟨i, ζ⟩ := p
      simp only [clause13SeqTailGates, hg, graphFrameAdvance, graphTailLeaf, Bool.false_eq_true,
        if_false, ObservedKrausLeaf.prepend]
      rw [ih]
    | inr p =>
      obtain ⟨i, j⟩ := p
      simp only [clause13SeqTailGates, hg, graphFrameAdvance, graphTailLeaf, Bool.false_eq_true,
        if_false, ObservedKrausLeaf.prepend]
      rw [ih]

def clause13LeadingSteps {n L : ℕ} (gs : GraphWord n L) : List (Fin L) → ℕ
  | [] => 0
  | t :: ts => if graphWireAt gs t then 0 else 1 + clause13LeadingSteps gs ts

def clause13TrailingSteps {n L : ℕ} (gs : GraphWord n L) : List (Fin L) → ℕ
  | [] => 0
  | t :: ts => if graphWireAt gs t then ts.length else clause13TrailingSteps gs ts

theorem clause13LeadingTrailing_sum {n L : ℕ} (gs : GraphWord n L) (ts : List (Fin L))
    (hw : ∃ t ∈ ts, graphWireAt gs t = true) :
    clause13LeadingSteps gs ts + 1 + clause13TrailingSteps gs ts = ts.length := by
  induction ts with
  | nil => simp at hw
  | cons t ts ih =>
    cases hwt : graphWireAt gs t with
    | true =>
      simp only [clause13LeadingSteps, clause13TrailingSteps, hwt, if_true, List.length_cons]
      omega
    | false =>
      have hw' : ∃ t' ∈ ts, graphWireAt gs t' = true := by
        obtain ⟨t', ht'mem, ht'cond⟩ := hw
        simp only [List.mem_cons] at ht'mem
        rcases ht'mem with rfl | ht'mem
        · exact absurd ht'cond (by rw [hwt]; simp)
        · exact ⟨t', ht'mem, ht'cond⟩
      have h := ih hw'
      simp only [clause13LeadingSteps, clause13TrailingSteps, hwt, Bool.false_eq_true, if_false,
        List.length_cons]
      omega

def clause13WireCountIn {n L : ℕ} (gs : GraphWord n L) : List (Fin L) → ℕ
  | [] => 0
  | t :: ts => (if graphWireAt gs t then 1 else 0) + clause13WireCountIn gs ts

theorem clause13WireCountIn_eq {n L : ℕ} (gs : GraphWord n L) (ts : List (Fin L)) :
    clause13WireCountIn gs ts = graphSlotCount gs ts := by
  induction ts with
  | nil => simp [clause13WireCountIn, graphSlotCount]
  | cons t ts ih =>
    simp only [clause13WireCountIn, graphSlotCount, List.map_cons, List.sum_cons]
    rw [ih]
    rfl

theorem clause13SeqTailGates_value {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs)
    (ts : List (Fin L)) (F : PauliFrame n) :
    clause13SeqTailGates gs h ts F = ts.length + 2 * clause13WireCountIn gs ts
        + (graphCorrectionGates gs (ts.foldl (graphFrameAdvance gs h) F)).length := by
  induction ts generalizing F with
  | nil => simp [clause13SeqTailGates, clause13WireCountIn]
  | cons t ts ih =>
    cases hg : gs t with
    | inl p =>
      obtain ⟨i, ζ⟩ := p
      simp only [clause13SeqTailGates, clause13WireCountIn, hg, graphFrameAdvance, graphWireAt,
        List.foldl_cons, List.length_cons, if_true]
      rw [ih]
      all_goals omega
    | inr p =>
      obtain ⟨i, j⟩ := p
      simp only [clause13SeqTailGates, clause13WireCountIn, hg, graphFrameAdvance, graphWireAt,
        List.foldl_cons, List.length_cons, Bool.false_eq_true, if_false]
      rw [ih]
      all_goals omega

theorem clause13PreTailGates_value {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs)
    (ts : List (Fin L)) (F : PauliFrame n) :
    clause13PreTailGates gs h ts F = 2 * clause13WireCountIn gs ts
        + (graphCorrectionGates gs (ts.foldl (graphFrameAdvance gs h) F)).length := by
  induction ts generalizing F with
  | nil => simp [clause13PreTailGates, clause13WireCountIn]
  | cons t ts ih =>
    cases hg : gs t with
    | inl p =>
      obtain ⟨i, ζ⟩ := p
      simp only [clause13PreTailGates, clause13WireCountIn, hg, graphFrameAdvance, graphWireAt,
        List.foldl_cons, if_true]
      rw [ih]
      all_goals omega
    | inr p =>
      obtain ⟨i, j⟩ := p
      simp only [clause13PreTailGates, clause13WireCountIn, hg, graphFrameAdvance, graphWireAt,
        List.foldl_cons, Bool.false_eq_true, if_false]
      rw [ih]
      all_goals omega

theorem clause13CommandExchangeCharge_eq {n L : ℕ} (gs : GraphWord n L) (h : GraphHistory gs) :
    (graphProgramLeaf false gs h).gates = (graphProgramLeaf true gs h).gates := by
  have hslot : clause13WireCountIn gs (List.ofFn (fun t : Fin L => t)) = graphWireCount gs := by
    rw [clause13WireCountIn_eq]
    simp [graphSlotCount, List.map_ofFn, List.sum_ofFn, graphWireCount_eq_sum]
  have hfresh := (preentangled_graph_actual_leaf_and_message_resources n L gs h).2.2.2.2.2.2.2.1
  have hpre : (graphProgramLeaf true gs h).gates
      = L + L + 2 * graphWireCount gs
        + frameCorrectionCost (graphFinalFrame gs h) := by
    have hg := (preentangled_graph_actual_leaf_and_message_resources n L gs h).2.2.2.1
    rw [hg]
    omega
  have hseq : (graphProgramLeaf false gs h).gates
      = L + L + 2 * graphWireCount gs
        + frameCorrectionCost (graphFinalFrame gs h) := by
    have hleaf : (graphProgramLeaf false gs h)
        = graphPrependLeaf (graphFreshGates n L)
            (graphTailLeaf false gs h (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n)) := by
      rw [graphProgramLeaf_eq]
      simp only [Bool.false_eq_true, if_false]
    rw [hleaf, graphPrependLeaf_gates, ← clause13SeqTailGates_eq, clause13SeqTailGates_value]
    have hcorr := graphCorrectionGates_length gs (graphFinalFrame gs h)
    have hfold : (List.ofFn (fun t : Fin L => t)).foldl (graphFrameAdvance gs h)
        (zeroPauliFrame n) = graphFinalFrame gs h := rfl
    rw [hfold, hcorr, hslot]
    simp only [List.length_ofFn, hfresh]
    omega
  rw [hpre, hseq]

def clause13GatesBeforeFirstMeasure {m : ℕ} : ObservedCircuit (Fin m) → ℕ
  | .halt _ => 0
  | .step (.gate _) next => 1 + clause13GatesBeforeFirstMeasure next
  | .step .query next => clause13GatesBeforeFirstMeasure next
  | .measure _ _ _ => 0
  | .project _ _ _ => 0

theorem clause13GatesBeforeFirstMeasure_prepend {m : ℕ} (Us : List (Operator m))
    (P : ObservedCircuit (Fin m)) :
    clause13GatesBeforeFirstMeasure (graphPrepend Us P)
      = Us.length + clause13GatesBeforeFirstMeasure P := by
  induction Us with
  | nil => simp [graphPrepend]
  | cons U Us ih =>
    change clause13GatesBeforeFirstMeasure (.step (.gate U) (graphPrepend Us P)) = _
    simp only [clause13GatesBeforeFirstMeasure, List.length_cons]
    rw [ih]
    omega

def clause13TailGatesBeforeMeasure {n L : ℕ} (gs : GraphWord n L) : List (Fin L) → ℕ
  | [] => 0
  | t :: ts => if graphWireAt gs t then 2 else clause13TailGatesBeforeMeasure gs ts

theorem clause13Tail_gatesBeforeMeasure {n L : ℕ} (gs : GraphWord n L)
    (F : PauliFrame n) (ts : List (Fin L)) (hw : ∃ t ∈ ts, graphWireAt gs t = true) :
    clause13GatesBeforeFirstMeasure (graphTail true gs ts F)
      = clause13TailGatesBeforeMeasure gs ts := by
  induction ts generalizing F with
  | nil => simp at hw
  | cons t ts ih =>
    cases hg : gs t with
    | inl p =>
      obtain ⟨i, ζ⟩ := p
      simp only [clause13TailGatesBeforeMeasure, graphWireAt, hg, if_true]
      simp [graphTail, hg, clause13GatesBeforeFirstMeasure]
    | inr p =>
      obtain ⟨i, j⟩ := p
      simp only [clause13TailGatesBeforeMeasure, graphWireAt, hg, Bool.false_eq_true, if_false]
      have hw' : ∃ t' ∈ ts, graphWireAt gs t' = true := by
        obtain ⟨t', ht'mem, ht'cond⟩ := hw
        simp only [List.mem_cons] at ht'mem
        rcases ht'mem with rfl | ht'mem
        · exact absurd ht'cond (by simp [graphWireAt, hg])
        · exact ⟨t', ht'mem, ht'cond⟩
      simp only [graphTail, hg]
      exact ih (graphCzFrame F i j) hw'

theorem clause13TailGatesBeforeMeasure_of_wire {n L : ℕ} (gs : GraphWord n L)
    (ts : List (Fin L)) (hw : ∃ t ∈ ts, graphWireAt gs t = true) :
    clause13TailGatesBeforeMeasure gs ts = 2 := by
  induction ts with
  | nil => simp at hw
  | cons t ts ih =>
    cases hwt : graphWireAt gs t with
    | true => simp [clause13TailGatesBeforeMeasure, hwt]
    | false =>
      have hw' : ∃ t' ∈ ts, graphWireAt gs t' = true := by
        obtain ⟨t', ht'mem, ht'cond⟩ := hw
        simp only [List.mem_cons] at ht'mem
        rcases ht'mem with rfl | ht'mem
        · exact absurd ht'cond (by rw [hwt]; simp)
        · exact ⟨t', ht'mem, ht'cond⟩
      have hih := ih hw'
      simp [clause13TailGatesBeforeMeasure, hwt, hih]

theorem clause13PreEntangledResourcesBeforeFirstMeasure {n L : ℕ} (gs : GraphWord n L)
    (h : GraphHistory gs) (hw : ∃ t : Fin L, graphWireAt gs t = true) :
    clause13GatesBeforeFirstMeasure (graphProgram true gs) = 2 * L + 2 := by
  have hw' : ∃ t ∈ (List.ofFn (fun t : Fin L => t)), graphWireAt gs t = true := by
    obtain ⟨t, ht⟩ := hw
    exact ⟨t, List.mem_ofFn.mpr ⟨t, rfl⟩, ht⟩
  have htail : clause13GatesBeforeFirstMeasure
        (graphTail true gs (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n)) = 2 := by
    rw [clause13Tail_gatesBeforeMeasure gs (zeroPauliFrame n) _ hw']
    exact clause13TailGatesBeforeMeasure_of_wire gs _ hw'
  have hprog : graphProgram true gs
      = graphPrepend (graphFreshGates n L)
          (graphPrepend (graphEdgeGates gs)
            (graphTail true gs (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n))) := by
    simp [graphProgram]
  rw [hprog, clause13GatesBeforeFirstMeasure_prepend, clause13GatesBeforeFirstMeasure_prepend,
      htail]
  have hfresh : (graphFreshGates n L).length = L := clause13Charge_fresh_eq gs h
  have hedge : (graphEdgeGates gs).length = L := clause13Charge_preEnt_eq gs h
  rw [hfresh, hedge]
  omega

end Qatlib.Concepts.FiniteLocc.LOCCProgram
