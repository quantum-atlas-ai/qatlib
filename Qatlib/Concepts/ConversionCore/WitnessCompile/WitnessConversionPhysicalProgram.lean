/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.WitnessConversionPhaseProgram
import Qatlib.Concepts.ConversionCore.WitnessCompile.ReflectionsQueryProgram
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option synthInstance.maxSize 512
noncomputable section
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.QueryComplexity.Reflections

theorem conversion_compile_frame_word
    {A G X : Type} [Fintype A] [DecidableEq A] [Fintype G] [DecidableEq G] {n : ℕ}
    (addr : G → Fin (n+1)) (input : X → Fin (n+1) → Bool)
    (V : X → Matrix (A × G) (A × G) ℂ)
    (Cf Cb : Circuit ((Fin (n+1) × Bool) × (A × G)))
    (hCf : IsUnitaryCircuit Cf) (hCb : IsUnitaryCircuit Cb)
    (hQf : QueryCount Cf = 2) (hQb : QueryCount Cb = 2)
    (hGf : GateCount Cf = 2) (hGb : GateCount Cb = 2)
    (hf : ∀ x ψ, Run (workspaceBitOracle (W := A × G) (input x)) Cf
      (reflectionsFrame addr ψ) = reflectionsFrame addr (ApplyGate (V x) ψ))
    (hb : ∀ x ψ, Run (workspaceBitOracle (W := A × G) (input x)) Cb
      (reflectionsFrame addr ψ) = reflectionsFrame addr (ApplyGate (V x)ᴴ ψ))
    (cs : List (AdjointStep (A × G))) (hcs : WellFormedAdjointCircuit cs) :
    ∃ C : Circuit ((Fin (n+1) × Bool) × (A × G)),
      IsUnitaryCircuit C ∧ QueryCount C = 2 * adjointQueryCount cs ∧
      GateCount C = adjointGateCount cs + 2 * adjointQueryCount cs ∧
      ∀ x ψ, Run (workspaceBitOracle (W := A × G) (input x)) C
        (reflectionsFrame addr ψ) = reflectionsFrame addr (ApplyGate (evaluate (V x) cs) ψ) := by
  induction cs with
  | nil =>
    refine ⟨[], isUnitaryCircuit_nil, rfl, rfl, ?_⟩
    intro x ψ
    simp [Run, evaluate, applyGate_one]
  | cons c cs ih =>
    have ht : WellFormedAdjointCircuit cs := fun U hU => hcs U (List.mem_cons_of_mem c hU)
    obtain ⟨C, hC, hQ, hG, hout⟩ := ih ht
    cases c with
    | gate L =>
      have hL : L ∈ Matrix.unitaryGroup (A × G) ℂ := hcs L List.mem_cons_self
      obtain ⟨K, hK, htransport⟩ := reflectionsFrame_transport addr L hL
      refine ⟨C ++ [.gate K], (isUnitaryCircuit_append _ _).mpr ⟨hC, ?_⟩, ?_, ?_, ?_⟩
      · simpa [IsUnitaryCircuit] using! hK
      · simp [queryCount_append, QueryCount, adjointQueryCount, hQ]
      · simp [gateCount_append, GateCount, adjointGateCount, adjointQueryCount, hG]
        omega
      · intro x ψ
        rw [run_append, hout, Run, Run, htransport]
        rw [evaluate, instructionMatrix, applyGate_mul]
    | forward =>
      refine ⟨C ++ Cf, (isUnitaryCircuit_append _ _).mpr ⟨hC, hCf⟩, ?_, ?_, ?_⟩
      · simp [queryCount_append, hQ, hQf, adjointQueryCount]
        omega
      · simp [gateCount_append, hG, hGf, adjointGateCount, adjointQueryCount]
        omega
      · intro x ψ
        rw [run_append, hout, hf, evaluate, instructionMatrix, applyGate_mul]
    | backward =>
      refine ⟨C ++ Cb, (isUnitaryCircuit_append _ _).mpr ⟨hC, hCb⟩, ?_, ?_, ?_⟩
      · simp [queryCount_append, hQ, hQb, adjointQueryCount]
        omega
      · simp [gateCount_append, hG, hGb, adjointGateCount, adjointQueryCount]
        omega
      · intro x ψ
        rw [run_append, hout, hb, evaluate, instructionMatrix, applyGate_mul]

def conversionFrameAddress {H Q : Type} (n : ℕ) :
    ((H ⊕ H) ⊕ (Fin n × Bool × Q)) → Fin (n+1)
  | .inl _ => ⟨n, by omega⟩
  | .inr p => p.1.castSucc

def conversionFrameBit {H Q : Type} {n : ℕ} :
    ((H ⊕ H) ⊕ (Fin n × Bool × Q)) → Option Bool
  | .inl _ => none
  | .inr p => some (!p.2.1)

theorem conversion_frame_logical_phase {A X H Q : Type}
    [Fintype A] [DecidableEq A] [Fintype H] [DecidableEq H]
    [Fintype Q] [DecidableEq Q] {n : ℕ}
    (input : X → Fin n → Bool) (x : X) (active : A → Bool) :
    reflectionsLogicalPhase (conversionFrameAddress (H := H) (Q := Q) n)
      conversionFrameBit active (conversionPaddedInput input x) =
      reflectionsControlled active
        (ReflectionAbout (conversionLogicalProjector (H := H) (Q := Q) input x)) := by
  ext p q
  rcases p with ⟨a,g⟩
  rcases q with ⟨b,h⟩
  by_cases hab : a = b
  · subst b
    by_cases hgh : g = h
    · subst h
      cases g with
      | inl r =>
        cases ha : active a <;> norm_num [reflectionsLogicalPhase, reflectionsControlled, Select, ha,
          conversionFrameBit, conversionLogicalProjector, conversionLogicalKeep,
          ReflectionAbout]
      | inr p =>
        have hpad : conversionPaddedInput input x p.1.castSucc = input x p.1 := by
          simp [conversionPaddedInput, p.1.isLt]
        cases ha : active a <;> cases hs : p.2.1 <;> cases hi : input x p.1 <;>
          norm_num [reflectionsLogicalPhase, reflectionsControlled, Select, ha,
            conversionFrameBit, conversionFrameAddress, hpad, hs, hi,
            conversionLogicalProjector, conversionLogicalKeep, ReflectionAbout]
    · have hpq : (a,g) ≠ (a,h) := fun he => hgh (congrArg Prod.snd he)
      cases ha : active a <;> norm_num [reflectionsLogicalPhase, reflectionsControlled, Select, hpq, hgh, ha,
        conversionLogicalProjector, ReflectionAbout]
  · have hpq : (a,g) ≠ (b,h) := fun he => hab (congrArg Prod.fst he)
    norm_num [reflectionsLogicalPhase, reflectionsControlled, Select, hpq, hab]

theorem conversion_frame_walk_words {A X H Q : Type}
    [Fintype A] [DecidableEq A] [Fintype H] [DecidableEq H]
    [Fintype Q] [DecidableEq Q] {n : ℕ}
    (input : X → Fin n → Bool) (active : A → Bool)
    (Λ : Matrix ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ℂ)
    (hΛ : IsOrthogonalProjector Λ) :
    ∃ Cf Cb : Circuit ((Fin (n+1) × Bool) × (A × ((H ⊕ H) ⊕ (Fin n × Bool × Q)))),
      IsUnitaryCircuit Cf ∧ IsUnitaryCircuit Cb ∧
      QueryCount Cf = 2 ∧ QueryCount Cb = 2 ∧ GateCount Cf = 2 ∧ GateCount Cb = 2 ∧
      ∀ x ψ,
      let U :=
          ReflectionAbout (conversionLogicalProjector (H := H) (Q := Q) input x) * ReflectionAbout Λ
      Run (workspaceBitOracle (W := A × ((H ⊕ H) ⊕ (Fin n × Bool × Q)))
        (conversionPaddedInput input x)) Cf (reflectionsFrame (conversionFrameAddress n) ψ) =
        reflectionsFrame (conversionFrameAddress n) (ApplyGate (reflectionsControlled active U) ψ) ∧
      Run (workspaceBitOracle (W := A × ((H ⊕ H) ⊕ (Fin n × Bool × Q)))
        (conversionPaddedInput input x)) Cb (reflectionsFrame (conversionFrameAddress n) ψ) =
        reflectionsFrame (conversionFrameAddress n) (ApplyGate (reflectionsControlled active U)ᴴ ψ) := by
  let addr := conversionFrameAddress (H := H) (Q := Q) n
  let bit := conversionFrameBit (H := H) (Q := Q) (n := n)
  let L := reflectionsControlled active (ReflectionAbout Λ)
  have hL : L ∈ Matrix.unitaryGroup _ ℂ :=
      reflectionsControlled_unitary active _ (reflectionAbout_unitary hΛ)
  obtain ⟨K, hK, htrans⟩ := reflectionsFrame_transport addr L hL
  let D := reflectionsColumnPhase (n := n+1) bit active
  have hD : D ∈ Matrix.unitaryGroup _ ℂ := by
    simpa only [D, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using!
      reflectionsColumnPhase_unitary (n := n+1) bit active
  let Cp : Circuit ((Fin (n+1) × Bool) × (A × ((H ⊕ H) ⊕ (Fin n × Bool × Q)))) :=
    [.query, .gate D, .query]
  have hCp : IsUnitaryCircuit Cp := by
    simp only [Cp, isUnitaryCircuit_query, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
    exact ((isUnitaryCircuit_gate _ _).mp (reflections_single_gate_wellFormed D hD)).1
  have hCk : IsUnitaryCircuit ([.gate K] : Circuit _) := reflections_single_gate_wellFormed K hK
  refine ⟨[.gate K] ++ Cp, Cp ++ [.gate K],
    (isUnitaryCircuit_append _ _).mpr ⟨hCk, hCp⟩,
    (isUnitaryCircuit_append _ _).mpr ⟨hCp, hCk⟩, rfl, rfl, rfl, rfl, ?_⟩
  intro x ψ
  have hphase (φ) : Run (workspaceBitOracle (W := A × ((H ⊕ H) ⊕ (Fin n × Bool × Q)))
      (conversionPaddedInput input x)) Cp (reflectionsFrame addr φ) =
      reflectionsFrame addr (ApplyGate (reflectionsControlled active
        (ReflectionAbout (conversionLogicalProjector (H := H) (Q := Q) input x))) φ) := by
    simpa only [Cp, D, addr, bit, conversion_frame_logical_phase input x active] using!
      reflections_compute_phase_uncompute addr bit active (conversionPaddedInput input x) φ
  have hprod : reflectionsControlled active
      (ReflectionAbout (conversionLogicalProjector (H := H) (Q := Q) input x) * ReflectionAbout Λ) =
      reflectionsControlled active (ReflectionAbout (conversionLogicalProjector (H := H) (Q := Q) input x)) * L := by
    apply Matrix.mulVec_injective
    funext φ
    change ApplyGate _ φ = ApplyGate _ φ
    rw [applyGate_mul]
    exact (reflectionsControlled_product_apply active _ _ φ).symm
  have hadj : (reflectionsControlled active
      (ReflectionAbout (conversionLogicalProjector (H := H) (Q := Q) input x)) * L)ᴴ =
      L * reflectionsControlled active (ReflectionAbout (conversionLogicalProjector (H := H) (Q := Q) input x)) := by
    rw [Matrix.conjTranspose_mul]
    have hself (P : Matrix ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ℂ) (hP : IsOrthogonalProjector P) :
        (reflectionsControlled active (ReflectionAbout P))ᴴ = reflectionsControlled active (ReflectionAbout P) := by
      ext ⟨a,g⟩ ⟨b,h⟩
      by_cases he : a = b
      · subst b
        cases ha : active a
        · by_cases hgh : g = h
          · subst h; simp [reflectionsControlled, Select, Matrix.conjTranspose_apply, ha]
          · simp [reflectionsControlled, Select, Matrix.conjTranspose_apply, ha, hgh, Ne.symm hgh]
        · simpa [reflectionsControlled, Select, Matrix.conjTranspose_apply, ha] using!
            congrFun (congrFun (reflectionAbout_conjTranspose hP) g) h
      · simp [reflectionsControlled, Select, Matrix.conjTranspose_apply, he, Ne.symm he]
    rw [hself Λ hΛ, hself _ (conversionLogicalProjector_orthogonal input x)]
  constructor
  · (try dsimp only)
    rw [run_append, Run, Run, htrans, hphase, hprod, applyGate_mul]
  · (try dsimp only)
    rw [run_append, hphase, Run, Run, htrans, hprod, hadj, applyGate_mul]

def conversionPhaseFrameEquiv (G : Type) (M k : ℕ) :
    PhaseReflectionSpace G M k ≃ ((Fin k → Fin M) × Bool) × G where
  toFun p := ((p.1, p.2.1), p.2.2)
  invFun p := (p.1.1, (p.1.2, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem conversion_relabel_adjoint_word {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (U : Matrix I I ℂ)
    (cs : List (AdjointStep I)) :
    evaluate (relabelGate e U) (phaseLiftWord (relabelGate e) cs) = relabelGate e (evaluate U cs) := by
  have hstar : (relabelGate e U)ᴴ = relabelGate e Uᴴ := by
    ext i j
    rfl
  induction cs with
  | nil => simpa [phaseLiftWord, evaluate] using! (CircuitRelabel.relabelGate_one e).symm
  | cons c cs ih =>
    cases c <;> simp only [phaseLiftWord, List.map_cons, phaseLiftStep, evaluate,
      instructionMatrix] at ih ⊢ <;> rw [ih] <;>
      simp only [hstar, CircuitRelabel.relabelGate_mul]

theorem conversion_phase_frame_oracle {G : Type} [Fintype G] [DecidableEq G]
    (M k : ℕ) (U : Matrix G G ℂ) :
    relabelGate (conversionPhaseFrameEquiv G M k) (parallelOracle (controlOracle U)) =
      reflectionsControlled (fun a : (Fin k → Fin M) × Bool => a.2) U := by
  ext ⟨⟨c,b⟩,g⟩ ⟨⟨d,e⟩,h⟩
  by_cases hcd : c = d
  · subst d
    by_cases hbe : b = e
    · subst e
      cases b <;> simp [relabelGate, conversionPhaseFrameEquiv, parallelOracle, controlOracle,
        Qatlib.Concepts.BlockEncoding.LCU.select, reflectionsControlled, Select]
    · simp [relabelGate, conversionPhaseFrameEquiv, parallelOracle, controlOracle,
        Qatlib.Concepts.BlockEncoding.LCU.select, reflectionsControlled, Select, hbe]
  · simp [relabelGate, conversionPhaseFrameEquiv, parallelOracle,
      Qatlib.Concepts.BlockEncoding.LCU.select, reflectionsControlled, Select, hcd]

theorem conversion_physical_phase_word {X H Q : Type}
    [Fintype H] [DecidableEq H] [Fintype Q] [DecidableEq Q] {n : ℕ}
    (input : X → Fin n → Bool) (M : ℕ) (hM : 2 ≤ M)
    (Λ : Matrix ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ℂ)
    (hΛ : IsOrthogonalProjector Λ) :
    ∃ C : Circuit ((Fin (n+1) × Bool) × (((Fin 1 → Fin M) × Bool) ×
      ((H ⊕ H) ⊕ (Fin n × Bool × Q)))),
      IsUnitaryCircuit C ∧ QueryCount C = 4 * (M-1) ∧ GateCount C = 8 * (M-1) + 5 ∧
      ∀ x ψ,
      let U :=
          ReflectionAbout (conversionLogicalProjector (H := H) (Q := Q) input x) * ReflectionAbout Λ
      Run (workspaceBitOracle (conversionPaddedInput input x)) C
        (reflectionsFrame (conversionFrameAddress n)
          (relabelState (conversionPhaseFrameEquiv _ M 1) (phaseReflectionEmbed M 1 ψ))) =
        reflectionsFrame (conversionFrameAddress n)
          (relabelState (conversionPhaseFrameEquiv _ M 1) (phaseReflectionState U M 1 ψ)) := by
  let G := (H ⊕ H) ⊕ (Fin n × Bool × Q)
  let A := (Fin 1 → Fin M) × Bool
  let e := conversionPhaseFrameEquiv G M 1
  let U (x : X) :=
      ReflectionAbout (conversionLogicalProjector (H := H) (Q := Q) input x) * ReflectionAbout Λ
  let V (x : X) := reflectionsControlled (fun a : A => a.2) (U x)
  obtain ⟨Cf,Cb,hCf,hCb,hQf,hQb,hGf,hGb,hw⟩ :=
      conversion_frame_walk_words input (fun a : A => a.2) Λ hΛ
  let cs := phaseLiftWord (relabelGate e) (phaseReflectionWord (I := G) M 1)
  have hr := phase_reflection_actual_queries_and_macros (I := G) M 1 hM
  have hcs : WellFormedAdjointCircuit cs := phaseLiftWord_wellFormed _
    (fun L hL => (relabelGate_mem_unitaryGroup e L).mpr hL) hr.1
  obtain ⟨C,hC,hQ,hG,hout⟩ := conversion_compile_frame_word
    (conversionFrameAddress (H := H) (Q := Q) n) (conversionPaddedInput input) V Cf Cb
    hCf hCb hQf hQb hGf hGb (fun x ψ => (hw x ψ).1) (fun x ψ => (hw x ψ).2) cs hcs
  refine ⟨C,hC,?_,?_,?_⟩
  · rw [hQ, (phaseLiftWord_counts _ _).1, hr.2.1]
    omega
  · rw [hG, (phaseLiftWord_counts _ _).1, (phaseLiftWord_counts _ _).2, hr.2.1, hr.2.2]
    omega
  · intro x ψ
    (try dsimp only)
    rw [hout]
    have heval : evaluate (V x) cs = relabelGate e
        (evaluate (parallelOracle (controlOracle (U x))) (phaseReflectionWord M 1)) := by
      dsimp only [V]
      rw [← conversion_phase_frame_oracle M 1 (U x)]
      exact conversion_relabel_adjoint_word e _ _
    rw [heval, applyGate_relabelGate]
    rfl

def conversionWorkspaceEquiv (S H : Type) [Fintype S] (n : ℕ) :
    (((Fin (n+1) × Bool) × S) × (Bool × H)) ≃
      ((Fin (n+1) × Bool) × ((Bool × H) × Fin (Fintype.card S))) where
  toFun p := (p.1.1, (p.2, (Fintype.equivFin S) p.1.2))
  invFun p := ((p.1, (Fintype.equivFin S).symm p.2.2), p.2.1)
  left_inv p := by simp
  right_inv p := by simp

def conversionWorkspaceEmbed {S H : Type} [Fintype S] [DecidableEq H] (n : ℕ) (h0 : H)
    (ψ : QState ((Fin (n+1) × Bool) × S)) :
    QState ((Fin (n+1) × Bool) × ((Bool × H) × Fin (Fintype.card S))) :=
  relabelState (conversionWorkspaceEquiv S H n) (TensorState ψ (Ket (false,h0)))

def conversionWorkspaceStep {S H : Type} [Fintype S] [Fintype H] [DecidableEq H]
    (n : ℕ) : Step ((Fin (n+1) × Bool) × S) →
    Step ((Fin (n+1) × Bool) × ((Bool × H) × Fin (Fintype.card S)))
  | .query => .query
  | .gate U => .gate (relabelGate (conversionWorkspaceEquiv S H n)
      (TensorGate U (1 : Matrix (Bool × H) (Bool × H) ℂ)))

def conversionWorkspaceCircuit {S H : Type} [Fintype S] [Fintype H] [DecidableEq H]
    (n : ℕ) (C : Circuit ((Fin (n+1) × Bool) × S)) := C.map (conversionWorkspaceStep (H := H) n)

theorem conversion_workspace_resources {S H : Type} [Fintype S] [DecidableEq S]
    [Fintype H] [DecidableEq H] (n : ℕ) (C : Circuit ((Fin (n+1) × Bool) × S))
    (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (conversionWorkspaceCircuit (H := H) n C) ∧
      QueryCount (conversionWorkspaceCircuit (H := H) n C) = QueryCount C ∧
      GateCount (conversionWorkspaceCircuit (H := H) n C) = GateCount C := by
  induction C with
  | nil => exact ⟨isUnitaryCircuit_nil, rfl, rfl⟩
  | cons c C ih =>
    cases c with
    | query =>
      obtain ⟨hC,hQ,hG⟩ := ih ((isUnitaryCircuit_query _).mp hC)
      exact ⟨(isUnitaryCircuit_query _).mpr hC, congrArg (fun t => t+1) hQ, hG⟩
    | gate U =>
      obtain ⟨hU,hC⟩ := (isUnitaryCircuit_gate _ _).mp hC
      obtain ⟨ht,hQ,hG⟩ := ih hC
      have htens : TensorGate U (1 : Matrix (Bool × H) (Bool × H) ℂ) ∈ Matrix.unitaryGroup _ ℂ :=
        tensorGate_unitary hU (Submonoid.one_mem _)
      have hK := (relabelGate_mem_unitaryGroup (conversionWorkspaceEquiv S H n) _).mpr htens
      refine ⟨(isUnitaryCircuit_gate _ _).mpr ⟨?_,ht⟩,hQ,congrArg (fun t => t+1) hG⟩
      exact ((isUnitaryCircuit_gate _ _).mp (reflections_single_gate_wellFormed _ hK)).1

theorem conversion_workspace_run {S H : Type} [Fintype S] [DecidableEq S]
    [Fintype H] [DecidableEq H] (n : ℕ) (h0 : H) (f : Fin (n+1) → Bool)
    (C : Circuit ((Fin (n+1) × Bool) × S)) (ψ : QState ((Fin (n+1) × Bool) × S)) :
    Run (workspaceBitOracle (W := (Bool × H) × Fin (Fintype.card S)) f)
      (conversionWorkspaceCircuit n C) (conversionWorkspaceEmbed n h0 ψ) =
      conversionWorkspaceEmbed n h0 (Run (workspaceBitOracle (W := S) f) C ψ) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons c C ih =>
    cases c with
    | gate U =>
      simp only [conversionWorkspaceCircuit, List.map_cons, conversionWorkspaceStep, Run]
      have he : ApplyGate (relabelGate (conversionWorkspaceEquiv S H n)
          (TensorGate U (1 : Matrix (Bool × H) (Bool × H) ℂ))) (conversionWorkspaceEmbed n h0 ψ) =
          conversionWorkspaceEmbed n h0 (ApplyGate U ψ) := by
        rw [conversionWorkspaceEmbed, applyGate_relabelGate, applyGate_tensorGate, applyGate_one]
        rfl
      rw [he]
      exact ih _
    | query =>
      simp only [conversionWorkspaceCircuit, List.map_cons, conversionWorkspaceStep, Run]
      have he : ApplyGate (workspaceBitOracle (W := (Bool × H) × Fin (Fintype.card S)) f)
          (conversionWorkspaceEmbed n h0 ψ) =
          conversionWorkspaceEmbed n h0 (ApplyGate (workspaceBitOracle (W := S) f) ψ) := by
        funext ⟨⟨j,b⟩,v,t⟩
        simp only [applyGate_workspaceBitOracle_mk, conversionWorkspaceEmbed,
          relabelState_apply, conversionWorkspaceEquiv, Equiv.coe_fn_symm_mk, TensorState]
      rw [he]
      exact ih _

theorem conversion_workspace_inner {S H : Type} [Fintype S] [DecidableEq S]
    [Fintype H] [DecidableEq H] (n : ℕ) (h0 : H)
    (ψ φ : QState ((Fin (n+1) × Bool) × S)) :
    Inner (conversionWorkspaceEmbed n h0 ψ) (conversionWorkspaceEmbed n h0 φ) = Inner ψ φ := by
  rw [conversionWorkspaceEmbed, conversionWorkspaceEmbed, inner_relabelState]
  change (∑ p : ((Fin (n+1) × Bool) × S) × (Bool × H),
    star (ψ p.1 * Ket (false,h0) p.2) * (φ p.1 * Ket (false,h0) p.2)) =
      ∑ z, star (ψ z) * φ z
  rw [Fintype.sum_prod_type]
  have ht : ∀ z, (∑ v : Bool × H, star (ψ z * Ket (false,h0) v) *
      (φ z * Ket (false,h0) v)) = star (ψ z) * φ z := by
    intro z
    simp [Ket, mul_comm]
  exact Finset.sum_congr rfl fun z _ => ht z

theorem conversion_clean_transport_word
    {X H : Type} [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
    (n r : ℕ) (hr : 0 < r) (input : X → Fin n → Bool) (ρ σ : X → QState H)
    (start target : X → QState ((Fin (n+1) × Bool) × ((Bool × H) × Fin r)))
    (hstart : ∀ x y, Inner (start x) (start y) = Inner (ρ x) (ρ y))
    (htarget : ∀ x y, Inner (target x) (target y) = Inner (σ x) (σ y))
    (C : Circuit ((Fin (n+1) × Bool) × ((Bool × H) × Fin r))) (hC : IsUnitaryCircuit C)
    (ε : ℝ) (herr : ∀ x, ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (conversionPaddedInput input x)) C (start x) - target x)‖ ≤ ε) :
    ∃ D : Circuit ((Fin (n+1) × Bool) × ((Bool × H) × Fin r)),
      IsUnitaryCircuit D ∧ QueryCount D = QueryCount C ∧ GateCount D = GateCount C + 2 ∧
      ∀ x, ‖toEuclidean_fromVec (Run (workspaceBitOracle (conversionPaddedInput input x)) D
        (conversionCleanEmbed n r hr false (ρ x)) - conversionCleanEmbed n r hr true (σ x))‖ ≤ ε := by
  let P := (Fin (n+1) × Bool) × ((Bool × H) × Fin r)
  let V : Matrix P X ℂ := fun i x => conversionCleanEmbed n r hr false (ρ x) i
  let S : Matrix P X ℂ := fun i x => start x i
  let T : Matrix P X ℂ := fun i x => target x i
  let Z : Matrix P X ℂ := fun i x => conversionCleanEmbed n r hr true (σ x) i
  have hVS : Vᴴ * V = Sᴴ * S := by
    ext x y
    change Inner (conversionCleanEmbed n r hr false (ρ x))
      (conversionCleanEmbed n r hr false (ρ y)) = Inner (start x) (start y)
    rw [conversion_clean_inner, hstart, if_pos rfl, one_mul]
  have hTZ : Tᴴ * T = Zᴴ * Z := by
    ext x y
    change Inner (target x) (target y) = Inner (conversionCleanEmbed n r hr true (σ x))
      (conversionCleanEmbed n r hr true (σ y))
    rw [conversion_clean_inner, htarget, if_pos rfl, one_mul]
  obtain ⟨U,hU,hUS⟩ := gram_equal_actual_unitary_transport P X V S hVS
  obtain ⟨B,hB,hBZ⟩ := gram_equal_actual_unitary_transport P X T Z hTZ
  have hsin (x) : ApplyGate U (conversionCleanEmbed n r hr false (ρ x)) = start x := by
    funext i
    exact congrFun (congrFun hUS i) x
  have htout (x) : ApplyGate B (target x) = conversionCleanEmbed n r hr true (σ x) := by
    funext i
    exact congrFun (congrFun hBZ i) x
  refine ⟨[.gate U] ++ C ++ [.gate B], ?_, ?_, ?_, ?_⟩
  · exact (isUnitaryCircuit_append _ _).mpr
      ⟨(isUnitaryCircuit_append _ _).mpr ⟨reflections_single_gate_wellFormed U hU,hC⟩,
        reflections_single_gate_wellFormed B hB⟩
  · simp [queryCount_append, QueryCount]
  · simp [gateCount_append, GateCount]
  · intro x
    rw [run_append, run_append, Run, Run, Run, Run, hsin, ← htout]
    simp only [ApplyGate, ← Matrix.mulVec_sub]
    change ‖toEuclidean_fromVec (ApplyGate B
      (Run (workspaceBitOracle (conversionPaddedInput input x)) C (start x) - target x))‖ ≤ ε
    rw [norm_applyGate_of_mem_unitaryGroup hB]
    exact herr x

theorem conversion_frame_inner {A G : Type} [Fintype A] [DecidableEq A]
    [Fintype G] [DecidableEq G] {n : ℕ} (addr : G → Fin (n+1)) (ψ φ : QState (A × G)) :
    Inner (reflectionsFrame addr ψ) (reflectionsFrame addr φ) = Inner ψ φ := by
  rw [← reflectionsFrameMatrix_apply addr ψ, ← reflectionsFrameMatrix_apply addr φ,
    inner_mulVec_left_rect, Matrix.mulVec_mulVec, reflectionsFrameMatrix_isometry, Matrix.one_mulVec]

theorem conversion_inner_norm_transport {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (ψ : QState I) (φ : QState J) (h : Inner ψ ψ = Inner φ φ) :
    ‖toEuclidean_fromVec ψ‖ = ‖toEuclidean_fromVec φ‖ := by
  have hs : ‖toEuclidean_fromVec ψ‖ ^ 2 = ‖toEuclidean_fromVec φ‖ ^ 2 := by
    rw [norm_toEuclidean_sq_eq_re_inner, norm_toEuclidean_sq_eq_re_inner, h]
  nlinarith [norm_nonneg (toEuclidean_fromVec ψ), norm_nonneg (toEuclidean_fromVec φ)]

end Qatlib.Concepts.ConversionCore.WitnessCompile
