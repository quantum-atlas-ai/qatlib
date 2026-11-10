/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.ChainFeedback.ClusterWireConsumers
import Qatlib.Concepts.ClusterPatterns.Preentangled.PreentangledGraphConsumers
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.Preentangled
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.ClusterPatterns.ChainFeedback

open Matrix
open scoped Classical
set_option linter.unusedSectionVars false

def clusterChainWord (L : ℕ) : GraphWord 1 L := fun _ => Sum.inl (0, (1 : ℂ))

def wireFeedbackStep (p : Bool × Bool) (s : Bool) : Bool × Bool := (s ^^ p.2, p.1)

def wireFeedbackBits (msg : List Bool) : Bool × Bool :=
  msg.foldl wireFeedbackStep (false, false)

noncomputable def clusterWireByproductGate (px pz : Bool) : Operator 2 :=
  pauliFrameGate 1 (fun _ => px, fun _ => pz)

theorem cluster_chain_legal (L : ℕ) : networkLegal (List.ofFn (clusterChainWord L)) := by
  intro g hg
  obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hg
  exact clusterOne_norm

theorem cluster_chain_layout_prefix_val (L k : ℕ) (hk : k ≤ L) :
    ((graphLayoutPrefix (clusterChainWord L) k 0 : Fin (1 + L)) : ℕ) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkl : k < L := by omega
    rw [graphLayoutPrefix_step _ _ hkl]
    have hstep : graphAdvance (clusterChainWord L) (graphLayoutPrefix (clusterChainWord L) k)
          ⟨k, hkl⟩ =
        Function.update (graphLayoutPrefix (clusterChainWord L) k) 0
          (graphFresh 1 L ⟨k, hkl⟩) := by
      simp [graphAdvance, clusterChainWord]
    rw [hstep, Function.update_self, graphFresh, Fin.val_natAdd]
    exact Nat.add_comm 1 k

theorem cluster_chain_edge (L : ℕ) (t : Fin L) :
    ((graphEdgeEndpoints (clusterChainWord L) t).1 : ℕ) = (t : ℕ) ∧
    ((graphEdgeEndpoints (clusterChainWord L) t).2 : ℕ) = (t : ℕ) + 1 := by
  have e1 : (graphEdgeEndpoints (clusterChainWord L) t).1 =
      graphLayoutBefore (clusterChainWord L) t 0 := by
    simp [graphEdgeEndpoints, clusterChainWord]
  have e2 : (graphEdgeEndpoints (clusterChainWord L) t).2 = graphFresh 1 L t := by
    simp [graphEdgeEndpoints, clusterChainWord]
  rw [e1, e2]
  refine ⟨cluster_chain_layout_prefix_val L t.val (Nat.le_of_lt t.isLt), ?_⟩
  simp [graphFresh, Fin.val_natAdd]
  omega

theorem cluster_chain_layout_final_val (L : ℕ) :
    ((graphLayoutFinal (clusterChainWord L) 0 : Fin (1 + L)) : ℕ) = L := by
  have hfinal : graphLayoutPrefix (clusterChainWord L) L = graphLayoutFinal (clusterChainWord L) := by
    unfold graphLayoutPrefix graphLayoutFinal
    rw [List.take_of_length_le (by simp)]
  rw [← hfinal]
  exact cluster_chain_layout_prefix_val L L le_rfl

theorem cluster_chain_wire_count (L : ℕ) : graphWireCount (clusterChainWord L) = L := by
  rw [graphWireCount_eq_sum]
  simp [clusterChainWord, graphWireAt]

theorem cluster_chain_word_resource :
    networkLegal (List.ofFn (clusterChainWord 2)) ∧
    (∀ (L : ℕ) (t : Fin L), ((graphEdgeEndpoints (clusterChainWord L) t).1 : ℕ) = (t : ℕ) ∧
      ((graphEdgeEndpoints (clusterChainWord L) t).2 : ℕ) = (t : ℕ) + 1) ∧
    (∀ (L : ℕ), ((graphLayoutFinal (clusterChainWord L) 0 : Fin (1 + L)) : ℕ) = L) ∧
    (∀ (L : ℕ), graphWireCount (clusterChainWord L) = L) :=
  ⟨cluster_chain_legal 2, fun L t => cluster_chain_edge L t,
   fun L => cluster_chain_layout_final_val L, fun L => cluster_chain_wire_count L⟩

private theorem cluster_chain_message (L : ℕ) (h : GraphHistory (clusterChainWord L)) :
    graphMessage (clusterChainWord L) h = List.ofFn h.1 := by
  have hc : ∀ ts : List (Fin L),
      (ts.filterMap (fun t => if graphWireAt (clusterChainWord L) t then some (h.1 t)
        else none)) = ts.map (fun t => h.1 t) := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t ts ih => simp [clusterChainWord, graphWireAt]
  have hc' := hc (List.ofFn (fun t : Fin L => t))
  simpa [graphMessage, List.map_ofFn] using! hc'

private theorem chain_frame_foldl_gen (x z : Bool) (bs : List Bool) :
    bs.foldl (fun F s => graphWireFrame F 0 s) ((fun _ : Fin 1 => x), (fun _ : Fin 1 => z)) =
      ((fun _ : Fin 1 => (bs.foldl wireFeedbackStep (x, z)).1),
       (fun _ : Fin 1 => (bs.foldl wireFeedbackStep (x, z)).2)) := by
  induction bs generalizing x z with
  | nil => rfl
  | cons s bs ih =>
    have hstep : graphWireFrame ((fun _ : Fin 1 => x), (fun _ : Fin 1 => z)) (0 : Fin 1) s =
        ((fun _ : Fin 1 => s ^^ z), (fun _ : Fin 1 => x)) := by
      simp only [graphWireFrame]
      refine Prod.ext ?_ ?_ <;>
        funext j <;> fin_cases j <;> simp [Function.update_self]
    simp only [List.foldl_cons, hstep, ih, wireFeedbackStep]

private theorem chain_frame_foldl (bs : List Bool) :
    bs.foldl (fun F s => graphWireFrame F 0 s) (zeroPauliFrame 1) =
      ((fun _ : Fin 1 => (wireFeedbackBits bs).1), (fun _ : Fin 1 => (wireFeedbackBits bs).2)) :=
  chain_frame_foldl_gen false false bs

private theorem cluster_chain_final_frame (L : ℕ) (h : GraphHistory (clusterChainWord L)) :
    graphFinalFrame (clusterChainWord L) h =
      ((fun _ : Fin 1 => (wireFeedbackBits (List.ofFn h.1)).1),
       (fun _ : Fin 1 => (wireFeedbackBits (List.ofFn h.1)).2)) := by
  have hmap : (List.map h.1 (List.ofFn (fun t : Fin L => t))).foldl
        (fun F s => graphWireFrame F 0 s) (zeroPauliFrame 1) =
      (List.ofFn (fun t : Fin L => t)).foldl (fun F t => graphWireFrame F 0 (h.1 t))
        (zeroPauliFrame 1) :=
    List.foldl_map
  have h1 := chain_frame_foldl (List.ofFn fun t : Fin L => h.1 t)
  have hofn : List.map h.1 (List.ofFn (fun t : Fin L => t)) = List.ofFn (fun t : Fin L => h.1 t) := by
    rw [List.map_ofFn]
    congr 1
  rw [hofn] at hmap
  show (List.ofFn (fun t : Fin L => t)).foldl (fun F t => graphWireFrame F 0 (h.1 t))
      (zeroPauliFrame 1) =
    ((fun _ : Fin 1 => (wireFeedbackBits (List.ofFn h.1)).1),
     (fun _ : Fin 1 => (wireFeedbackBits (List.ofFn h.1)).2))
  rw [← hmap]
  exact h1

theorem cluster_chain_two_bit_parity_feedback :
    ∀ (L : ℕ) (h : GraphHistory (clusterChainWord L)),
      graphMessage (clusterChainWord L) h = List.ofFn h.1 ∧
      graphFinalFrame (clusterChainWord L) h =
        ((fun _ => (wireFeedbackBits (List.ofFn h.1)).1),
         (fun _ => (wireFeedbackBits (List.ofFn h.1)).2)) ∧
      frameCorrectionCost (graphFinalFrame (clusterChainWord L) h) ≤ 2 ∧
      pauliFrameGate 1 (graphFinalFrame (clusterChainWord L) h) =
        clusterWireByproductGate (wireFeedbackBits (List.ofFn h.1)).1
          (wireFeedbackBits (List.ofFn h.1)).2 := by
  intro L h
  refine ⟨cluster_chain_message L h, cluster_chain_final_frame L h, ?_, ?_⟩
  · rw [cluster_chain_final_frame L h]
    cases (wireFeedbackBits (List.ofFn h.1)).1 <;>
      cases (wireFeedbackBits (List.ofFn h.1)).2 <;>
      simp [frameCorrectionCost]
  · rw [cluster_chain_final_frame L h]
    rfl

private theorem cluster_chain_replicate (L : ℕ) :
    List.ofFn (clusterChainWord L) =
      List.replicate L (Sum.inl ((0 : Fin 1), (1 : ℂ)) : ClusterNetworkGate 1) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [List.ofFn_succ, List.replicate_succ]
    simp only [clusterChainWord]
    congr 1

private theorem network_logical_matrix_replicate (n : ℕ) (g : ClusterNetworkGate n) (L : ℕ) :
    networkLogicalMatrix (List.replicate L g) = (networkGateMatrix g)^L := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [List.replicate_succ]
    simp only [networkLogicalMatrix]
    rw [ih]
    exact (pow_succ _ _).symm

theorem cluster_chain_logical_matrix :
    (∀ L : ℕ, networkLogicalMatrix (List.ofFn (clusterChainWord L)) =
      (networkWireGate (n := 1) 0 (1 : ℂ))^L) ∧
    (∀ k : ℕ, networkLogicalMatrix (List.ofFn (clusterChainWord (2 * k))) = 1) := by
  have h2 : (networkGateMatrix (Sum.inl ((0 : Fin 1), (1 : ℂ)) : ClusterNetworkGate 1))^2 = 1 := by
    rw [pow_two]
    simp only [networkGateMatrix, networkWireGate]
    rw [tensorPauliWireGate_mul, clusterJ_one_sq]
    have hone : tensorPauliWireGate 1 (0 : Fin 1) (1 : Operator 2) = 1 := by
      rw [tensorPauliWireGate]
      have hfac : (fun j : Fin 1 => if j = (0 : Fin 1) then (1 : Operator 2) else 1) =
          (fun _ => (1 : Operator 2)) := by
        funext j
        by_cases h : j = (0 : Fin 1) <;> simp [h]
      rw [hfac, tensorPauliProduct_one]
    exact hone
  have hmat : ∀ L : ℕ, networkLogicalMatrix (List.ofFn (clusterChainWord L)) =
      (networkGateMatrix (Sum.inl ((0 : Fin 1), (1 : ℂ)) : ClusterNetworkGate 1))^L := by
    intro L
    rw [cluster_chain_replicate L]
    induction L with
    | zero => rfl
    | succ L ih =>
      rw [List.replicate_succ]
      simp only [networkLogicalMatrix]
      rw [ih]
      exact (pow_succ _ _).symm
  refine ⟨?_, ?_⟩
  · intro L
    have he : (networkGateMatrix (Sum.inl ((0 : Fin 1), (1 : ℂ)) : ClusterNetworkGate 1)) =
        networkWireGate (n := 1) 0 (1 : ℂ) := rfl
    rw [hmat L, he]
  · intro k
    rw [hmat (2 * k), pow_mul, h2, one_pow]

theorem cluster_chain_branch_instrument_forget :
    ∀ (L : ℕ) (ρ : Operator 2), ∃ I : Instrument (GraphHistory (clusterChainWord L)) 2 2,
      (∀ h : GraphHistory (clusterChainWord L),
        I.branch h ρ = graphActualBranch true (clusterChainWord L) h ρ) ∧
      (∀ (hρ : IsDensityOperator ρ) (h : GraphHistory (clusterChainWord L)),
        instrumentProb I ρ h = (1 / 2 : ℝ)^L) ∧
      (∑ h : GraphHistory (clusterChainWord L),
          graphActualBranch true (clusterChainWord L) h ρ) =
        networkLogicalMatrix (List.ofFn (clusterChainWord L)) * ρ *
          (networkLogicalMatrix (List.ofFn (clusterChainWord L)))ᴴ := by
  intro L ρ
  obtain ⟨I, hbr, hprob, -⟩ :=
    preentangled_graph_actual_cp_instrument_and_forget 1 L (clusterChainWord L)
      (cluster_chain_legal L)
  refine ⟨I, fun h => hbr h ρ, fun hρ h => ?_, ?_⟩
  · rw [hprob ρ hρ h, cluster_chain_wire_count L]
  · exact graphActualBranch_forget 1 L (clusterChainWord L) (cluster_chain_legal L) ρ

theorem cluster_chain_odd_wire_identity_transport :
    ∀ (k : ℕ) (ρ : Operator 2) (h : GraphHistory (clusterChainWord (2 * k))),
      (∑ h' : GraphHistory (clusterChainWord (2 * k)),
          graphActualBranch true (clusterChainWord (2 * k)) h' ρ) = ρ ∧
      graphActualBranch true (clusterChainWord (2 * k)) h ρ = (1 / 2 : ℂ)^(2 * k) • ρ ∧
      (graphProgramLeaf true (clusterChainWord (2 * k)) h).accepted = true ∧
      (graphProgramLeaf true (clusterChainWord (2 * k)) h).queries = 0 ∧
      (graphProgramLeaf true (clusterChainWord (2 * k)) h).measurements = 2 * k ∧
      (graphProgramLeaf true (clusterChainWord (2 * k)) h).gates =
        8 * k + frameCorrectionCost (graphFinalFrame (clusterChainWord (2 * k)) h) ∧
      (graphMessage (clusterChainWord (2 * k)) h).length = 2 * k := by
  intro k ρ h
  have hforget := graphActualBranch_forget 1 (2 * k) (clusterChainWord (2 * k))
    (cluster_chain_legal (2 * k)) ρ
  have hform := graphActualBranch_formula 1 (2 * k) (clusterChainWord (2 * k))
    (cluster_chain_legal (2 * k)) h ρ
  obtain ⟨-, hacc, hq, hgates, hmeas, hmsglen, -, -, -⟩ :=
    preentangled_graph_actual_leaf_and_message_resources 1 (2 * k) (clusterChainWord (2 * k)) h
  refine ⟨?_, ?_, hacc, hq, ?_, ?_, ?_⟩
  · rw [hforget, cluster_chain_logical_matrix.2 k, Matrix.one_mul,
      Matrix.conjTranspose_one, Matrix.mul_one]
  · rw [hform, cluster_chain_wire_count, cluster_chain_logical_matrix.2 k, Matrix.one_mul,
      Matrix.conjTranspose_one, Matrix.mul_one]
  · rw [hmeas, cluster_chain_wire_count]
  · rw [hgates, cluster_chain_wire_count]
    omega
  · rw [hmsglen, cluster_chain_wire_count]

theorem cluster_chain_reference_transport :
    (∀ (L R : ℕ) (X : Matrix (Fin 2 × Fin R) (Fin 2 × Fin R) ℂ),
      (∑ h : GraphHistory (clusterChainWord L),
          graphActualReference true (clusterChainWord L) h R X) =
        TensorGate (networkLogicalMatrix (List.ofFn (clusterChainWord L))) (1 : Operator R) * X *
          (TensorGate (networkLogicalMatrix (List.ofFn (clusterChainWord L))) (1 : Operator R))ᴴ) ∧
    (∀ (k R : ℕ) (X : Matrix (Fin 2 × Fin R) (Fin 2 × Fin R) ℂ),
      (∑ h : GraphHistory (clusterChainWord (2 * k)),
          graphActualReference true (clusterChainWord (2 * k)) h R X) = X) := by
  refine ⟨?_, ?_⟩
  · intro L R X
    obtain ⟨I, -, -, hforget⟩ :=
      preentangled_graph_actual_cp_instrument_and_forget 1 L (clusterChainWord L)
        (cluster_chain_legal L)
    exact hforget R X
  · intro k R X
    obtain ⟨I, -, -, hforget⟩ :=
      preentangled_graph_actual_cp_instrument_and_forget 1 (2 * k) (clusterChainWord (2 * k))
        (cluster_chain_legal (2 * k))
    have h := hforget R X
    rw [cluster_chain_logical_matrix.2 k] at h
    have h1 : TensorGate (1 : Operator (2 ^ 1)) (1 : Operator R) = 1 := tensorGate_one
    rw [h1, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] at h
    exact h

end Qatlib.Concepts.ClusterPatterns.ChainFeedback
