/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.MultiKnownQubitControl

/-!
# Subset-controlled rotation syntax and basis transport

This module defines subset controls, Toffoli folds, and the original Figure 2 rotation-word
construction. It proves basis-state transport and the final conjunction value for the recursive
fold under its disjointness and clean-work hypotheses, and records that the original frame
excludes empty control lists.

The polynomial payoff-rotation setting is described in [WoernerEgger2019].

## Main statements

* `subsetAndFold_basis_transport`: The compiled `subsetAndFold` transports each basis ket to the
  ket of `subsetFoldBasis` under the stated wire-disjointness hypotheses.
* `subsetAndFold_basis_last`: With equally long control and clean-work lists and the stated
  disjointness, the last fold flag equals the conjunction of the initial flag and all controls.
* `subsetRotationFrame_empty_false`: No empty control list satisfies the original
  `subsetRotationFrame`.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.RiskEstimation.PolyRotation

open Matrix

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-- The Boolean conjunction of the register bits on the listed control wires. -/
def subsetControlTrue {N : ℕ} (S : List (Fin N)) (x : Reg N) : Bool :=
  S.all (fun w => x w)

/-- The original subset-rotation frame, requiring distinct control and work wires, separation
from the target, disjoint control and work lists, and `works.length + 1 = S.length`. -/
def subsetRotationFrame {N : ℕ} (S : List (Fin N)) (target : Fin N)
    (works : List (Fin N)) : Prop :=
  S.Nodup ∧ works.Nodup ∧ works.length + 1 = S.length ∧
    (∀ w ∈ S, w ≠ target) ∧ (∀ w ∈ works, w ≠ target) ∧
    (∀ w ∈ S, ∀ u ∈ works, w ≠ u)

/-- The recursive Toffoli gate list that combines a running flag with successive controls into
successive work wires. -/
noncomputable def subsetAndFold {N : ℕ} (flag : Fin N) :
    List (Fin N) → List (Fin N) → List (ReflectionGate N)
  | c :: cs, w :: ws => toffoliLocalSteps flag c w ++ subsetAndFold w cs ws
  | _, _ => []

/-- The original Toffoli ladder, initialized by the first two controls and continued with the
list beginning at the second control. -/
noncomputable def subsetAndLadder {N : ℕ} (S works : List (Fin N)) :
    List (ReflectionGate N) :=
  match S, works with
  | c0 :: c1 :: cs, w :: ws => toffoliLocalSteps c0 c1 w ++ subsetAndFold w (c1 :: cs) ws
  | _, _ => []

/-- The selected flag wire: the first control, with target fallback, when there are no work
wires, or the last work wire otherwise. -/
def subsetFlagWire {N : ℕ} (S : List (Fin N)) (target : Fin N)
    (works : List (Fin N)) : Fin N :=
  match works with
  | [] => S.headD target
  | _ => works.getLastD target

/-- The original subset-controlled rotation word, using an unconditional target rotation for an
empty control list and a ladder, controlled rotation, and inverse ladder otherwise. -/
noncomputable def subsetRotationSteps {N : ℕ} (S : List (Fin N)) (target : Fin N)
    (works : List (Fin N)) (θ : ℝ) : List (ReflectionGate N) :=
  match S with
  | [] => [.inl (target, qubitEulerRotation θ)]
  | _ => subsetAndLadder S works ++
      multiKnownPairSteps (subsetFlagWire S target works) target ⟨0, 0, θ, 0⟩ ++
      reflectionAdjoint (subsetAndLadder S works)

/-- The sum of angles of terms whose control subsets are true in the given register. -/
def subsetRotationAngle {N : ℕ} (terms : List (List (Fin N) × ℝ)) (x : Reg N) : ℝ :=
  ((terms.filter (fun p => subsetControlTrue p.1 x)).map Prod.snd).sum

/-- The concatenation of the original subset-rotation words for all listed angle terms. -/
noncomputable def figTwoRotationSteps {N : ℕ} (target : Fin N) (works : List (Fin N))
    (terms : List (List (Fin N) × ℝ)) : List (ReflectionGate N) :=
  terms.flatMap (fun p => subsetRotationSteps p.1 target works p.2)

/-- The basis-register update that XORs the conjunction of wires `a` and `c` into wire `w`. -/
noncomputable def subsetStageBasis {N : ℕ} (y : Reg N) (a c w : Fin N) : Reg N :=
  Function.update y w (y w ^^ (y a && y c))

/-- The basis-register transformation produced by recursively folding control bits into work
wires. -/
noncomputable def subsetFoldBasis {N : ℕ} (f : Fin N) :
    List (Fin N) → List (Fin N) → Reg N → Reg N
  | c :: cs, w :: ws, y => subsetFoldBasis w cs ws (subsetStageBasis y f c w)
  | _, _, y => y

/-- The last element with fallback of a nonempty list equals that of its tail with the head as
fallback. -/
private theorem getLastD_cons_cons {α : Type} (w : α) (ws : List α) (f : α) :
    (w :: ws).getLastD f = ws.getLastD w := by
  cases ws <;> simp [List.getLastD]

/-- The compiled local Toffoli on three distinct wires acts on a basis ket by
`subsetStageBasis`. -/
private theorem subsetStage_action {N : ℕ} (a c w : Fin N) (hac : a ≠ c) (haw : a ≠ w)
    (hcw : c ≠ w) (y : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (toffoliLocalSteps a c w))
        (Ket y) = Ket (subsetStageBasis y a c w) :=
  (local_toffoli_fifteen_exact N a c w hac haw hcw).2.2 y

/-- Under the stated wire-disjointness conditions, the compiled Toffoli fold maps each basis ket
according to `subsetFoldBasis`. -/
private theorem subsetFold_action {N : ℕ} :
    ∀ (cs ws : List (Fin N)) (_hdis : ∀ u ∈ cs, ∀ v ∈ ws, u ≠ v) (_hwnodup : ws.Nodup)
      (f : Fin N) (_hflag : ∀ v, (v ∈ cs ∨ v ∈ ws) → f ≠ v) (y : Reg N),
      Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (subsetAndFold f cs ws)) (Ket y)
        = Ket (subsetFoldBasis f cs ws y) := by
  intro cs
  induction cs with
  | nil =>
      intro ws _ _ f _ y
      cases ws with
      | nil => simp [subsetAndFold, subsetFoldBasis, reflectionCompile]
      | cons w ws => simp [subsetAndFold, subsetFoldBasis, reflectionCompile]
  | cons c cs ih =>
      intro ws hdis hwnodup f hflag y
      cases ws with
      | nil => simp [subsetAndFold, subsetFoldBasis, reflectionCompile]
      | cons w ws =>
          have hcw : c ≠ w := hdis c (by simp) w (by simp)
          have hfc : f ≠ c := fun h => hflag c (Or.inl (by simp)) h
          have hfw : f ≠ w := fun h => hflag w (Or.inr (by simp)) h
          have hdis' : ∀ u ∈ cs, ∀ v ∈ ws, u ≠ v := by
            intro u hu v hv
            exact hdis u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv)
          have hwnodup' : ws.Nodup := by
            rw [List.Nodup, List.pairwise_cons] at hwnodup
            exact hwnodup.2
          have hwflag : ∀ v, (v ∈ cs ∨ v ∈ ws) → w ≠ v := by
            intro v hv
            rcases hv with hv | hv
            · exact fun h => hdis v (List.mem_cons_of_mem _ hv) w (by simp) h.symm
            · rw [List.Nodup, List.pairwise_cons] at hwnodup
              exact hwnodup.1 v hv
          rw [subsetAndFold, subsetFoldBasis, reflectionCompile_append, run_append]
          rw [subsetStage_action f c w hfc hfw hcw]
          exact ih ws hdis' hwnodup' w hwflag _

/-- For equal-length control and clean-work lists satisfying the stated disjointness conditions,
the final fold flag is the conjunction of the initial flag and all control bits. -/
private theorem subsetFold_last {N : ℕ} :
    ∀ (cs ws : List (Fin N)) (_hlen : cs.length = ws.length)
      (_hdis : ∀ u ∈ cs, ∀ v ∈ ws, u ≠ v) (_hwnodup : ws.Nodup) (y : Reg N) (f : Fin N)
      (_hclean : ∀ w ∈ ws, y w = false),
      subsetFoldBasis f cs ws y (ws.getLastD f)
        = decide (y f = true ∧ ∀ c ∈ cs, y c = true) := by
  intro cs
  induction cs with
  | nil =>
      intro ws hlen _ _ y f _
      cases ws with
      | nil => simp [subsetFoldBasis, List.getLastD]
      | cons w ws => simp at hlen
  | cons c cs ih =>
      intro ws hlen hdis hwnodup y f hclean
      cases ws with
      | nil => simp at hlen
      | cons w ws =>
          have hlen' : cs.length = ws.length := by simpa using! hlen
          have hcw : c ≠ w := hdis c (by simp) w (by simp)
          have hdis' : ∀ u ∈ cs, ∀ v ∈ ws, u ≠ v := by
            intro u hu v hv
            exact hdis u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv)
          have hne : ∀ u ∈ cs, u ≠ w := fun u hu => hdis u (List.mem_cons_of_mem _ hu) w (by simp)
          set y' : Reg N := subsetStageBasis y f c w with hy'
          have hne' : ∀ u, u ≠ w → y' u = y u := by
            intro u hu
            rw [hy', subsetStageBasis, Function.update_of_ne hu]
          have hwnodup' : ws.Nodup := by
            rw [List.Nodup, List.pairwise_cons] at hwnodup
            exact hwnodup.2
          have hneW : ∀ v ∈ ws, v ≠ w := by
            intro v hv
            rw [List.Nodup, List.pairwise_cons] at hwnodup
            exact fun h => hwnodup.1 v hv h.symm
          have hclean' : ∀ v ∈ ws, y' v = false := by
            intro v hv
            rw [hne' v (hneW v hv)]
            exact hclean v (List.mem_cons_of_mem _ hv)
          have hw : y' w = (y f && y c) := by
            rw [hy', subsetStageBasis, Function.update_self, hclean w (by simp),
              Bool.false_xor]
          rw [subsetFoldBasis, getLastD_cons_cons, ih ws hlen' hdis' hwnodup' y' w hclean', hw]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq, Bool.and_eq_true]
          constructor
          · rintro ⟨⟨hfc, hcc⟩, h⟩
            refine ⟨hfc, fun u hu => ?_⟩
            rcases List.mem_cons.mp hu with rfl | hu
            · exact hcc
            · rw [← hne' u (hne u hu)]; exact h u hu
          · rintro ⟨hfc, h⟩
            refine ⟨⟨hfc, h c (by simp)⟩, fun u hu => ?_⟩
            rw [hne' u (hne u hu)]; exact h u (List.mem_cons_of_mem _ hu)

/-- The compiled `subsetAndFold` transports each basis ket to the ket of `subsetFoldBasis` under
the stated wire-disjointness hypotheses. -/
theorem subsetAndFold_basis_transport {N : ℕ} (cs ws : List (Fin N))
    (hdis : ∀ u∈cs,∀ v∈ws,u≠v) (hwn : ws.Nodup) (f : Fin N)
    (hf : ∀ v,v∈cs ∨ v∈ws → f≠v) (y : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (subsetAndFold f cs ws)) (Ket y)=
      Ket (subsetFoldBasis f cs ws y) := subsetFold_action cs ws hdis hwn f hf y

/-- With equally long control and clean-work lists and the stated disjointness, the last fold
flag equals the conjunction of the initial flag and all controls. -/
theorem subsetAndFold_basis_last {N : ℕ} (cs ws : List (Fin N)) (hlen : cs.length=ws.length)
    (hdis : ∀ u∈cs,∀ v∈ws,u≠v) (hwn : ws.Nodup) (y : Reg N) (f : Fin N)
    (hc : ∀ w∈ws,y w=false) :
    subsetFoldBasis f cs ws y (ws.getLastD f)=decide (y f=true ∧ ∀ c∈cs,y c=true) :=
  subsetFold_last cs ws hlen hdis hwn y f hc

/-- No empty control list satisfies the original `subsetRotationFrame`. -/
theorem subsetRotationFrame_empty_false {N : ℕ} (t : Fin N) (ws : List (Fin N)) :
    ¬subsetRotationFrame [] t ws := by
  intro h
  have he:=h.2.2.1
  simp only [List.length_nil] at he
  omega

end Qatlib.Concepts.RiskEstimation.PolyRotation
