/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.ReflectionCompile.CleanZeroReflection
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Concepts.CircuitImpl.ReflectionCompile
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

noncomputable def reflectionLiftGate (n : ℕ) : ReflectionGate n → ReflectionGate (n+(n-1))
  | .inl (w,U) => .inl (reflectionDataWire n w,U)
  | .inr (c,t) => .inr (reflectionDataWire n c,reflectionDataWire n t)

noncomputable def reflectionPreparationMatrix {n : ℕ} (gs : List (ReflectionGate n)) :=
  reflectionProgramMatrix gs

noncomputable def localPreparedAABlock (n : ℕ) (gs : List (ReflectionGate n)) :
    Circuit (Reg (n+(n-1))) :=
  [Step.query] ++ reflectionCompile ((reflectionAdjoint gs).map (reflectionLiftGate n)) ++
    reflectionCompile (localZeroReflectionSteps n) ++
    reflectionCompile (gs.map (reflectionLiftGate n))

noncomputable def localPreparedAACircuit (n : ℕ) (gs : List (ReflectionGate n)) (k : ℕ) :
    Circuit (Reg (n+(n-1))) :=
  reflectionCompile (gs.map (reflectionLiftGate n)) ++ RepeatCircuit (localPreparedAABlock n gs) k

noncomputable def localHadamardReflectionSteps (n : ℕ) : List (ReflectionGate n) :=
  (List.finRange n).map (fun w => Sum.inl (w,Hadamard))

private theorem reflectionJoin_update_data (n : ℕ) (x : Reg n) (w : Reg (n-1))
    (i : Fin n) (b : Bool) :
    Function.update ((reflectionSplit n).symm (x,w)) (reflectionDataWire n i) b =
      (reflectionSplit n).symm (Function.update x i b,w) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · by_cases hj : j=i
    · subst j
      rw [Function.update_self, reflectionJoin_data, Function.update_self]
    · have hne : reflectionDataWire n j ≠ reflectionDataWire n i := by
        intro h; exact hj (Fin.ext (by have := congrArg Fin.val h; simpa using this))
      rw [Function.update_of_ne hne, reflectionJoin_data, reflectionJoin_data,
        Function.update_of_ne hj]
  · have hne : reflectionWorkWire n j ≠ reflectionDataWire n i := by
      intro h; have := congrArg Fin.val h; simp [reflectionWorkWire,reflectionDataWire] at this; omega
    rw [Function.update_of_ne hne, reflectionJoin_work, reflectionJoin_work]

private theorem reflectionEmbed_add (n : ℕ) (ψ φ : QState (Reg n)) :
    reflectionEmbed n (ψ+φ) = reflectionEmbed n ψ + reflectionEmbed n φ := by
  funext z
  simp only [reflectionEmbed, Pi.add_apply]
  split <;> simp

private theorem reflectionLiftGate_legal (n : ℕ) (g : ReflectionGate n)
    (hg : reflectionGateLegal g) : reflectionGateLegal (reflectionLiftGate n g) := by
  rcases g with ⟨w,U⟩ | ⟨c,t⟩
  · exact hg
  · intro h
    exact hg (Fin.ext (by have := congrArg Fin.val h; simpa using this))

private theorem reflectionLiftGate_ket (n : ℕ) (g : ReflectionGate n)
    (hg : reflectionGateLegal g) (x : Reg n) :
    ApplyGate (reflectionGateMatrix (reflectionLiftGate n g)) (reflectionEmbed n (Qatlib.Foundations.PureStateMath.Ket x)) =
      reflectionEmbed n (ApplyGate (reflectionGateMatrix g) (Qatlib.Foundations.PureStateMath.Ket x)) := by
  rw [reflectionEmbed_ket]
  rcases g with ⟨w,U⟩ | ⟨c,t⟩
  · change ApplyGate (wireGate _ (reflectionDataWire n w) U)
      (Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm (x,fun _ => false))) =
        reflectionEmbed n (ApplyGate (wireGate n w U) (Qatlib.Foundations.PureStateMath.Ket x))
    rw [applyGate_wireGate_ket, applyGate_wireGate_ket, reflectionEmbed_add]
    simp only [reflectionJoin_data, reflectionJoin_update_data, reflectionEmbed_smul,
      reflectionEmbed_ket]
  · have hct : c≠t := hg
    have hct' : reflectionDataWire n c ≠ reflectionDataWire n t :=
      reflectionLiftGate_legal n (.inr (c,t)) hg
    change ApplyGate (cnotGate _ (reflectionDataWire n c) (reflectionDataWire n t))
      (Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm (x,fun _ => false))) =
        reflectionEmbed n (ApplyGate (cnotGate n c t) (Qatlib.Foundations.PureStateMath.Ket x))
    rw [applyGate_cnotGate_ket _ _ _ hct', applyGate_cnotGate_ket _ _ _ hct,
      reflectionEmbed_ket]
    simp only [reflectionJoin_data, reflectionJoin_update_data]

private theorem localApply_sum {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (U : Matrix I I ℂ) (ψ : J → QState I) :
    ApplyGate U (∑ j,ψ j) = ∑ j,ApplyGate U (ψ j) := Matrix.mulVec_sum _ _ _

private theorem reflectionLiftGate_embed (n : ℕ) (g : ReflectionGate n)
    (hg : reflectionGateLegal g) (ψ : QState (Reg n)) :
    ApplyGate (reflectionGateMatrix (reflectionLiftGate n g)) (reflectionEmbed n ψ) =
      reflectionEmbed n (ApplyGate (reflectionGateMatrix g) ψ) := by
  conv_lhs => rw [state_ket_expansion ψ]
  rw [reflectionEmbed_sum, localApply_sum]
  simp only [reflectionEmbed_smul, reflectionApplyGate_smul, reflectionLiftGate_ket n g hg]
  conv_rhs => arg 2; arg 2; rw [state_ket_expansion ψ]
  simp only [localApply_sum, reflectionApplyGate_smul, reflectionEmbed_sum, reflectionEmbed_smul]

private theorem reflectionLiftCompile_embed (n : ℕ) (gs : List (ReflectionGate n))
    (hgs : reflectionLegal gs) (ψ : QState (Reg n)) :
    Run (1 : Matrix (Reg (n+(n-1))) (Reg (n+(n-1))) ℂ)
      (reflectionCompile (gs.map (reflectionLiftGate n))) (reflectionEmbed n ψ) =
      reflectionEmbed n (ApplyGate (reflectionPreparationMatrix gs) ψ) := by
  induction gs generalizing ψ with
  | nil => simp [reflectionCompile, reflectionPreparationMatrix, reflectionProgramMatrix]
  | cons g gs ih =>
    simp only [List.map_cons, reflectionCompile, List.map_cons, run_gate]
    rw [reflectionLiftGate_embed n g (hgs g List.mem_cons_self)]
    change Run _ (reflectionCompile (gs.map (reflectionLiftGate n))) _ = _
    rw [ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg))]
    change reflectionEmbed n (ApplyGate (reflectionProgramMatrix gs)
      (ApplyGate (reflectionGateMatrix g) ψ)) =
      reflectionEmbed n (ApplyGate (reflectionProgramMatrix gs * reflectionGateMatrix g) ψ)
    rw [applyGate_mul]

private theorem reflectionLiftCompile_oracle (n : ℕ) (gs : List (ReflectionGate n))
    (hgs : reflectionLegal gs) (O : Matrix (Reg (n+(n-1))) (Reg (n+(n-1))) ℂ)
    (ψ : QState (Reg n)) :
    Run O (reflectionCompile (gs.map (reflectionLiftGate n))) (reflectionEmbed n ψ) =
      reflectionEmbed n (ApplyGate (reflectionPreparationMatrix gs) ψ) := by
  rw [run_eq_of_queryCount_eq_zero O 1 _ (queryCount_reflectionCompile _)]
  exact reflectionLiftCompile_embed n gs hgs ψ

private theorem localPreparedAABlock_embed (n : ℕ) (gs : List (ReflectionGate n))
    (hgs : reflectionLegal gs) (S : Finset (Reg n)) (ψ : QState (Reg n)) :
    Run (reflectionLift n (preparedMark S)) (localPreparedAABlock n gs) (reflectionEmbed n ψ) =
      reflectionEmbed n (Run (preparedMark S)
        [Step.query, Step.gate (reflectionPreparationMatrix gs)ᴴ,
          Step.gate (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)))),
          Step.gate (reflectionPreparationMatrix gs)] ψ) := by
  simp only [localPreparedAABlock, run_append, run_query, run_nil]
  rw [reflectionLift_embed, reflectionLiftCompile_oracle n (reflectionAdjoint gs)
    (reflectionAdjoint_legal gs hgs)]
  rw [reflectionPreparationMatrix, reflectionAdjoint_matrix gs hgs]
  rw [run_eq_of_queryCount_eq_zero (reflectionLift n (preparedMark S)) 1
    (reflectionCompile (localZeroReflectionSteps n)) (queryCount_reflectionCompile _)]
  rw [(local_zero_reflection_clean_semantics_and_cost n).2.2.2,
    reflectionLiftCompile_oracle n gs hgs]
  rfl

private theorem localPreparedAARepeat_embed (n k : ℕ) (gs : List (ReflectionGate n))
    (hgs : reflectionLegal gs) (S : Finset (Reg n)) (ψ : QState (Reg n)) :
    Run (reflectionLift n (preparedMark S)) (RepeatCircuit (localPreparedAABlock n gs) k)
      (reflectionEmbed n ψ) = reflectionEmbed n (Run (preparedMark S)
        (RepeatCircuit [Step.query, Step.gate (reflectionPreparationMatrix gs)ᴴ,
          Step.gate (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)))),
          Step.gate (reflectionPreparationMatrix gs)] k) ψ) := by
  induction k generalizing ψ with
  | zero => rfl
  | succ k ih =>
    simp only [RepeatCircuit, run_append]
    rw [localPreparedAABlock_embed n gs hgs S ψ, ih]

theorem local_prepared_aa_actual_state_and_three_counts (n k : ℕ)
    (gs : List (ReflectionGate n)) (S : Finset (Reg n)) (hgs : reflectionLegal gs) :
    let A := reflectionPreparationMatrix gs
    Run (reflectionLift n (preparedMark S)) (localPreparedAACircuit n gs k)
        (reflectionEmbed n (Qatlib.Foundations.PureStateMath.Ket (fun _ => false))) =
      reflectionEmbed n (Run (preparedMark S) (preparedAACircuit A (fun _ => false) k)
        (Qatlib.Foundations.PureStateMath.Ket (fun _ => false))) ∧
    QueryCount (localPreparedAACircuit n gs k) = k ∧
    GateCount (localPreparedAACircuit n gs k) = (2*k+1)*gs.length+k*localReflectionCost n := by
  (try dsimp only)
  refine ⟨?_,?_,?_⟩
  · rw [localPreparedAACircuit, run_append, reflectionLiftCompile_oracle n gs hgs,
      localPreparedAARepeat_embed n k gs hgs, preparedAACircuit, run_append]
    rfl
  · simp [localPreparedAACircuit, localPreparedAABlock, queryCount_append,
      queryCount_repeatCircuit, queryCount_reflectionCompile]
  · simp only [localPreparedAACircuit, localPreparedAABlock, gateCount_append,
      gateCount_repeatCircuit, gateCount_query, gateCount_nil, gateCount_reflectionCompile,
      List.length_map, reflectionAdjoint_length, localZeroReflectionSteps_length]
    ring

theorem localPreparedAACircuit_unitary (n k : ℕ) (gs : List (ReflectionGate n))
    (hgs : reflectionLegal gs) : IsUnitaryCircuit (localPreparedAACircuit n gs k) := by
  have hlift : ∀ ds : List (ReflectionGate n), reflectionLegal ds →
      IsUnitaryCircuit (reflectionCompile (ds.map (reflectionLiftGate n))) := by
    intro ds hds
    apply (local_reflection_gate_support_unitarity_counts _ _ ?_).1
    intro g hg
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
    exact reflectionLiftGate_legal n g' (hds g' hg')
  have hforward := hlift gs hgs
  have hbackward := hlift (reflectionAdjoint gs) (reflectionAdjoint_legal gs hgs)
  have hzero := (local_reflection_gate_support_unitarity_counts _ _
    (localZeroReflectionSteps_legal n)).1
  have hblock : IsUnitaryCircuit (localPreparedAABlock n gs) := by
    simp only [localPreparedAABlock,isUnitaryCircuit_append]
    exact ⟨⟨⟨by simp,hbackward⟩,hzero⟩,hforward⟩
  rw [localPreparedAACircuit,isUnitaryCircuit_append]
  exact ⟨hforward,hblock.repeatCircuit k⟩

theorem localHadamardReflectionSteps_legal (n : ℕ) :
    reflectionLegal (localHadamardReflectionSteps n) := by
  intro g hg
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp hg
  exact hadamard_unitary

@[simp] theorem localHadamardReflectionSteps_length (n : ℕ) :
    (localHadamardReflectionSteps n).length = n := by simp [localHadamardReflectionSteps]

theorem localHadamardReflectionSteps_matrix (n : ℕ) :
    reflectionPreparationMatrix (localHadamardReflectionSteps n) = HadamardN n := by
  have hmap : ∀ ws : List (Fin n),
      reflectionProgramMatrix (ws.map (fun w => Sum.inl (w,Hadamard))) =
        localProgramMatrix (ws.map LocalQFTGate.h) := by
    intro ws
    induction ws with
    | nil => rfl
    | cons w ws ih =>
      simp only [List.map_cons, reflectionProgramMatrix, localProgramMatrix, ih]
      congr 1
      ext x y
      exact wireGate_apply n w Hadamard x y
  rw [reflectionPreparationMatrix, localHadamardReflectionSteps, hmap]
  exact localProgramMatrix_localHadamard n

private theorem uniform_two_apply (x : Reg 2) : Uniform (Reg 2) x = (1/2 : ℂ) := by
  have h4 : Real.sqrt 4 = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [Uniform,card_reg,h4]

private theorem uniform_two_outer : outerProduct (Uniform (Reg 2)) = AverageProjection (Reg 2) := by
  ext x y
  rw [outerProduct_apply, uniform_two_apply, uniform_two_apply]
  norm_num [AverageProjection,card_reg,map_ofNat]

private theorem prepared_two_search (target : Reg 2) :
    Run (preparedMark ({target} : Finset (Reg 2)))
      (preparedAACircuit (HadamardN 2) (fun _ => false) 1) (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)) = Qatlib.Foundations.PureStateMath.Ket target := by
  have hrun := (prepared_aa_actual_circuit (HadamardN 2) (fun _ => false)
    ({target} : Finset (Reg 2)) 1 (hadamardN_unitary 2)).2.2.2
  have hstate : preparedAAState (HadamardN 2) (fun _ => false) = Uniform (Reg 2) :=
    applyGate_hadamardN_ket_zero 2
  have hconj := (prepared_aa_reflection_and_access (HadamardN 2) (fun _ => false)
    ({target} : Finset (Reg 2)) (hadamardN_unitary 2)).2.2.1
  rw [hstate, uniform_two_outer] at hconj
  rw [hrun, pow_one, preparedAAIterate, hconj, hstate]
  have hm : ApplyGate (preparedMark ({target} : Finset (Reg 2))) (Uniform (Reg 2)) =
      MarkedVector ({target} : Finset (Reg 2)) (-1/2) (1/2) := by
    funext x
    simp only [preparedMark, ApplyGate, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, Projector, Matrix.mulVec_diagonal, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mem_singleton, uniform_two_apply, MarkedVector]
    split_ifs <;> ring
  rw [applyGate_mul]
  change ApplyGate (Diffusion (Reg 2)) _ = _
  rw [hm]
  funext x
  rw [applyGate_diffusion, sum_markedVector]
  norm_num only [Finset.card_singleton, card_reg, Nat.reducePow]
  simp only [MarkedVector, Finset.mem_singleton, Qatlib.Foundations.PureStateMath.Ket]
  split_ifs <;> norm_num

theorem local_two_qubit_search_actual_consumer (target : Reg 2) :
    Run (reflectionLift 2 (preparedMark ({target} : Finset (Reg 2))))
        (localPreparedAACircuit 2 (localHadamardReflectionSteps 2) 1)
        (reflectionEmbed 2 (Qatlib.Foundations.PureStateMath.Ket (fun _ => false))) = reflectionEmbed 2 (Qatlib.Foundations.PureStateMath.Ket target) ∧
    QueryCount (localPreparedAACircuit 2 (localHadamardReflectionSteps 2) 1) = 1 ∧
    GateCount (localPreparedAACircuit 2 (localHadamardReflectionSteps 2) 1) = 44 := by
  have h := local_prepared_aa_actual_state_and_three_counts 2 1
    (localHadamardReflectionSteps 2) ({target} : Finset (Reg 2))
    (localHadamardReflectionSteps_legal 2)
  dsimp only at h
  rw [localHadamardReflectionSteps_matrix, prepared_two_search] at h
  refine ⟨h.1,h.2.1,?_⟩
  rw [h.2.2, localHadamardReflectionSteps_length]
  norm_num [localReflectionCost]

end Qatlib.Concepts.CircuitImpl.ReflectionCompile
