/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Concepts.MonteCarloMean.PayoffEncoding
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Qatlib.Concepts.NativeNumerics.LayeredMean.CountedHHLProgram

/-!
# Native layered mean estimation

This module constructs rational dyadic payoffs, finite-precision payoff preparations, and the
joint amplitude-estimation record law `nativeLayerLaw`. The dyadic decomposition follows the
layered mean-estimation setting of [Montanaro2015], using amplitude estimation as in
[BrassardEtAl2002].

The preparation and circuit perturbation bounds give an explicit ℓ¹ distance of at most
`(1/2)^k` between the native and ideal laws on the same record space.

## Main statements

* `native_layered_payoff_exact_partition`: Rational layers lie in `[0,1]` and agree with the
  real dyadic payoffs.
* `native_layered_actual_record_law`: The native joint law factors into the amplitude-estimation
  trial laws.
* `native_layered_same_record_variation_budget`: The native and ideal record laws differ in ℓ¹
  norm by at most `(1/2)^k`.

## References

* [Montanaro, 2015][Montanaro2015]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

namespace Qatlib.Concepts.NativeNumerics.LayeredMean
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The rational dyadic payoff: layer zero retains values below one, and layer `l+1` rescales
values in `[2^l, 2^(l+1))` by `2^(l+1)`. -/
def nativeLayerPayoff {I : Type} (f : I→ℚ) : ℕ→I→ℚ
  | 0,i => if f i < 1 then f i else 0
  | l+1,i => if (2:ℚ)^l≤f i ∧ f i < (2:ℚ)^(l+1) then f i/(2:ℚ)^(l+1) else 0

/-- The bit precision `32 * (k + 16)` used for native layered payoff rotations. -/
def nativeLayerBits (k : ℕ) : ℕ := 32*(k+16)

/-- Prepares a native layer by applying `A` on the input register and then the rational payoff
rotation at precision `nativeLayerBits k`. -/
noncomputable def nativeLayerPrepare {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (f : I→ℚ) (k l : ℕ) : Matrix (I×Bool) (I×Bool) ℂ :=
  rationalPayoffRotation (nativeLayerPayoff f l) (nativeLayerBits k)*TensorGate A (1 : Matrix Bool Bool ℂ)

/-- The measurement event consisting of all basis states whose payoff flag is `true`. -/
def nativeLayerEvent (I : Type) [Fintype I] [DecidableEq I] : Finset (I×Bool) :=
  Finset.univ.filter (fun p => p.2=true)

/-- For a nonnegative rational payoff, each native dyadic layer lies in `[0,1]` and its real
cast equals `layerPayoff`. This identifies the partition used in the layered construction
associated with [Montanaro2015, Algorithm 2][Montanaro2015]. -/
theorem native_layered_payoff_exact_partition (I : Type) (f : I → ℚ) (hf : ∀ i, 0≤f i)
    (l : ℕ) (i : I) :
    0≤nativeLayerPayoff f l i ∧ nativeLayerPayoff f l i≤1 ∧
    (nativeLayerPayoff f l i:ℝ)=layerPayoff (fun j => (f j:ℝ)) l i := by
  have he : (nativeLayerPayoff f l i:ℝ)=layerPayoff (fun j => (f j:ℝ)) l i := by
    cases l with
    | zero =>
      simp only [nativeLayerPayoff, layerPayoff_zero]
      have hc : f i<1 ↔ (f i:ℝ)<1 := by exact_mod_cast Iff.rfl
      by_cases h : f i<1
      · simp [h, hc.mp h]
      · have hn : ¬(f i:ℝ)<1 := fun hh => h (hc.mpr hh)
        simp only [if_neg h, if_neg hn, Rat.cast_zero]
    | succ l =>
      simp only [nativeLayerPayoff, layerPayoff_succ]
      have hc : (2:ℚ)^l≤f i ∧ f i<(2:ℚ)^(l+1) ↔
          (2:ℝ)^l≤(f i:ℝ) ∧ (f i:ℝ)<(2:ℝ)^(l+1) := by
        constructor
        · intro h; exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
        · intro h; exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
      by_cases h : (2:ℚ)^l≤f i ∧ f i<(2:ℚ)^(l+1)
      · simp [h, hc.mp h]
      · have hn : ¬((2:ℝ)^l≤(f i:ℝ) ∧ (f i:ℝ)<(2:ℝ)^(l+1)) := fun hh => h (hc.mpr hh)
        simp only [if_neg h, if_neg hn, Rat.cast_zero]
  have hb : 0≤nativeLayerPayoff f l i ∧ nativeLayerPayoff f l i≤1 := by
    cases l with
    | zero =>
      simp only [nativeLayerPayoff]
      split
      · exact ⟨hf i, le_of_lt (by assumption)⟩
      · norm_num
    | succ l =>
      simp only [nativeLayerPayoff]
      split
      · rename_i h
        exact ⟨div_nonneg (hf i) (by positivity), (div_le_one₀ (by positivity)).mpr h.2.le⟩
      · norm_num
  exact ⟨hb.1,hb.2,he⟩

/-- The native layer preparation is unitary when `A` is unitary and the payoff is nonnegative. -/
theorem nativeLayerPrepare_unitary {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (f : I→ℚ) (k l : ℕ)
    (hA : A∈Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0≤f i) :
    nativeLayerPrepare A f k l∈Matrix.unitaryGroup (I×Bool) ℂ := by
  have hp (i : I) := native_layered_payoff_exact_partition I f hf l i
  exact (Matrix.unitaryGroup _ ℂ).mul_mem
    (rational_payoff_unitary_value_and_operator_error I _ _ (fun i => ⟨(hp i).1,(hp i).2.1⟩)).1
    (tensorGate_unitary hA (by simp))

/-- The law of `2 * layerRepetitions k + 1` independent amplitude-estimation outcomes for a
fixed native layer. -/
noncomputable def nativeLayerTrialLaw {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I→ℚ) (k : ℕ)
    (hP : ∀ l : Fin (k+2),nativeLayerPrepare A f k l∈Matrix.unitaryGroup (I×Bool) ℂ)
    (l : Fin (k+2)) : FinDist (Fin (2*layerRepetitions k+1)→Fin (layerGrid k)) where
  prob u := (aeLaw (layerGrid k) (nativeLayerPrepare A f k l) (j,false) (nativeLayerEvent I)
    (hP l) (layerGrid_ge_two k)).probOf u
  nonneg u := Finset.prod_nonneg fun n _ => (aeLaw _ _ _ _ (hP l) (layerGrid_ge_two k)).nonneg (u n)
  sum_one := Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.sum_probOf _ _

/-- The independent joint law of the repeated amplitude-estimation records across all `k+2`
native layers. -/
noncomputable def nativeLayerLaw {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I→ℚ) (k : ℕ)
    (hP : ∀ l : Fin (k+2),nativeLayerPrepare A f k l∈Matrix.unitaryGroup (I×Bool) ℂ) :
    FinDist (LayerRecord k) := independentSampleLaw (nativeLayerTrialLaw A j f k hP)

/-- For unitary `A` and nonnegative `f`, native layer preparations are unitary and possess a
joint record law with the stated product probabilities. This supplies the layerwise sampling
law for the construction associated with [Montanaro2015, Algorithm 2][Montanaro2015]. -/
theorem native_layered_actual_record_law
    (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I) (f : I→ℚ) (k : ℕ)
    (hA : A∈Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0≤f i) :
    ∃ hP : ∀ l : Fin (k+2),nativeLayerPrepare A f k l∈Matrix.unitaryGroup (I×Bool) ℂ,
    ∃ law : FinDist (LayerRecord k), ∀ ω : LayerRecord k,
      law.prob ω=∏ l : Fin (k+2),
        (aeLaw (layerGrid k) (nativeLayerPrepare A f k l) (j,false) (nativeLayerEvent I)
          (hP l) (layerGrid_ge_two k)).probOf (ω l) := by
  let hP := fun l : Fin (k+2) => nativeLayerPrepare_unitary A f k l hA hf
  exact ⟨hP,nativeLayerLaw A j f k hP,fun _ => rfl⟩

/-- The ℓ¹ distance between finite product laws is bounded by the sum of the ℓ¹ distances
between their factors. -/
theorem native_product_l1 {X : Type} [Fintype X] [DecidableEq X] (n : ℕ)
    (p q : Fin n→FinDist X) :
    (∑ ω : Fin n→X, |(∏ i,(p i).prob (ω i))-(∏ i,(q i).prob (ω i))|) ≤
      ∑ i,∑ x,|(p i).prob x-(q i).prob x| := by
  induction n with
  | zero => simp
  | succ n ih =>
    let P := independentSampleLaw (fun i : Fin n => p i.succ)
    let Q := independentSampleLaw (fun i : Fin n => q i.succ)
    have hsum : (∑ ω : Fin (n+1)→X, |(∏ i,(p i).prob (ω i))-(∏ i,(q i).prob (ω i))|) =
        ∑ a : X, ∑ u : Fin n→X, |(p 0).prob a*P.prob u-(q 0).prob a*Q.prob u| := by
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => X))]
      simp only [Fintype.sum_prod_type, Fin.prod_univ_succ, Fin.consEquiv_apply,
        Fin.cons_zero, Fin.cons_succ]
      rfl
    rw [hsum, Fin.sum_univ_succ]
    calc
      _ ≤ ∑ a : X, ∑ u : Fin n→X,
          (|(p 0).prob a-(q 0).prob a| * P.prob u + (q 0).prob a*|P.prob u-Q.prob u|) := by
        apply Finset.sum_le_sum; intro a _
        apply Finset.sum_le_sum; intro u _
        have ht :=
            abs_sub_le ((p 0).prob a*P.prob u) ((q 0).prob a*P.prob u) ((q 0).prob a*Q.prob u)
        simpa only [← sub_mul, ← mul_sub, abs_mul, abs_of_nonneg (P.nonneg u),
          abs_of_nonneg ((q 0).nonneg a)] using! ht
      _ = (∑ x,|(p 0).prob x-(q 0).prob x|) + ∑ u,|P.prob u-Q.prob u| := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, P.sum_one, mul_one, ← Finset.sum_mul,
          (q 0).sum_one, one_mul]
      _ ≤ _ := add_le_add le_rfl (ih (fun i => p i.succ) (fun i => q i.succ))

/-- If every event probability differs by at most `δ`, the ℓ¹ distance between two finite
probability laws is at most `2 * δ`. -/
theorem native_l1_from_events {X : Type} [Fintype X] [DecidableEq X]
    (p q : FinDist X) (δ : ℝ)
    (he : ∀ E : Finset X, |(∑ x∈E,p.prob x)-(∑ x∈E,q.prob x)|≤δ) :
    (∑ x,|p.prob x-q.prob x|)≤2*δ := by
  let E := Finset.univ.filter (fun x => q.prob x≤p.prob x)
  have hz : (∑ x : X, (p.prob x - q.prob x))=0 := by
    rw [Finset.sum_sub_distrib,p.sum_one,q.sum_one]; ring
  have ha (x : X) : |p.prob x-q.prob x| =
      2*(if x∈E then p.prob x-q.prob x else 0)-(p.prob x-q.prob x) := by
    by_cases h : q.prob x≤p.prob x
    · simp [E,h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
    · simp [E,h,abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]
  simp_rw [ha]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz, sub_zero, ← Finset.sum_filter]
  have hE : Finset.univ.filter (fun x => x∈E)=E := by ext x; simp
  rw [hE, Finset.sum_sub_distrib]
  exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (he E)) (by norm_num)

/-- The matrix of a circuit step, interpreting fixed gates by their matrices and query steps by
the oracle `O`. -/
private def nativeStepMatrix {R : Type} (O : Matrix R R ℂ) : Step R→Matrix R R ℂ
  | .gate U => U
  | .query => O

/-- Running a circuit equals applying the product of its step matrices in reverse list order to
the initial state. -/
private theorem native_run_matrix {R : Type} [Fintype R] [DecidableEq R]
    (O : Matrix R R ℂ) (C : Circuit R) (ψ : QState R) :
    Run O C ψ=(C.reverse.map (nativeStepMatrix O)).prod*ᵥψ := by
  induction C generalizing ψ with
  | nil => simp
  | cons s C ih =>
    cases s <;> simp [Run, ApplyGate, ih, List.reverse_cons, List.map_append,
      List.prod_append, nativeStepMatrix, Matrix.mulVec_mulVec]

/-- Tensoring two matrices with the same identity matrix does not increase the norm of their
difference. -/
private theorem native_tensor_identity_sub {R T : Type} [Fintype R] [DecidableEq R]
    [Fintype T] [DecidableEq T] (A B : Matrix T T ℂ) :
    ‖TensorGate (1:Matrix R R ℂ) A-TensorGate (1:Matrix R R ℂ) B‖≤‖A-B‖ := by
  rw [tensorGate_sub_right, l2_norm_tensorGate]
  exact (mul_le_mul_of_nonneg_right l2_norm_one_le (norm_nonneg _)).trans_eq (one_mul _)

/-- The controlled amplitude-estimation lift does not increase the norm of a matrix
perturbation. -/
private theorem native_ae_control_sub {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (A B : Matrix I I ℂ) : ‖aeControlledGate M A-aeControlledGate M B‖≤‖A-B‖ :=
  (native_tensor_identity_sub (R:=Fin M) _ _).trans (norm_controlOracle_sub A B)

/-- The sum of instruction perturbations is at most the number of input accesses times `‖A-B‖`. -/
private theorem native_ae_instruction_sum {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (A B : Matrix I I ℂ) (j : I) (O : Matrix (Fin M×(Bool×I)) (Fin M×(Bool×I)) ℂ)
    (w : List (AEAccessStep (Fin M×(Bool×I)))) :
    (w.map (fun s => ‖nativeStepMatrix O (aeAccessInstruction M A j s)-
      nativeStepMatrix O (aeAccessInstruction M B j s)‖)).sum≤(aeInputAccesses w:ℝ)*‖A-B‖ := by
  induction w with
  | nil => simp [aeInputAccesses]
  | cons s w ih =>
    cases s with
    | «initialize» =>
      have he := (native_tensor_identity_sub (R:=Fin M) _ _).trans
        (native_tensor_identity_sub (R:=Bool) A B)
      simp only [List.map_cons, List.sum_cons, aeAccessInstruction, nativeStepMatrix,
        aeInputAccesses, Nat.cast_add, Nat.cast_one] at *
      linarith
    | prepareForward =>
      have he := native_ae_control_sub M A B
      simp only [List.map_cons, List.sum_cons, aeAccessInstruction, nativeStepMatrix,
        aeInputAccesses, Nat.cast_add, Nat.cast_one] at *
      linarith
    | prepareBackward =>
      have he := native_ae_control_sub M Aᴴ Bᴴ
      rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose] at he
      simp only [List.map_cons, List.sum_cons, aeAccessInstruction, nativeStepMatrix,
        aeInputAccesses, Nat.cast_add, Nat.cast_one] at *
      linarith
    | sourceReflection => simpa [aeInputAccesses,aeAccessInstruction,nativeStepMatrix] using! ih
    | mark => simpa [aeInputAccesses,aeAccessInstruction,nativeStepMatrix] using! ih
    | fixed U => simpa [aeInputAccesses,aeAccessInstruction,nativeStepMatrix] using! ih

/-- Replacing unitary preparation `A` by `B` changes the counted amplitude-estimation output
state by at most `(2 * (M-1) + 1) * ‖A-B‖` in Euclidean norm. -/
theorem native_ae_output_distance {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2≤M) (A B : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A∈Matrix.unitaryGroup I ℂ) (hB : B∈Matrix.unitaryGroup I ℂ) :
    let O := aeControlledGate M (preparedMark S)
    let input := TensorState (Ket (⟨0,by omega⟩:Fin M)) (TensorState (Ket false) (Ket j))
    ‖toEuclidean_fromVec (Run O (countedAECircuit M A j) input-
      Run O (countedAECircuit M B j) input)‖≤(2*(M-1)+1:ℕ)*‖A-B‖ := by
  (try dsimp only)
  let O := aeControlledGate M (preparedMark S)
  let w := aeAccessWord (I:=I) M
  let F := fun s => nativeStepMatrix O (aeAccessInstruction M A j s)
  let G := fun s => nativeStepMatrix O (aeAccessInstruction M B j s)
  have hca := (prepared_ae_expanded_access_and_output M hM A j S hA).2.2.1
  have hcb := (prepared_ae_expanded_access_and_output M hM B j S hB).2.2.1
  have hO : O∈Matrix.unitaryGroup (Fin M×(Bool×I)) ℂ := tensorGate_unitary (by simp)
    (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle_unitary (prepared_aa_reflection_and_access A j S hA).1)
  have hvalid (D : Matrix I I ℂ) (hD : IsUnitaryCircuit (countedAECircuit M D j)) :
      ∀ s∈w.reverse, nativeStepMatrix O (aeAccessInstruction M D j s)∈Matrix.unitaryGroup (Fin M×(Bool×I)) ℂ := by
    intro s hs
    have hm : aeAccessInstruction M D j s∈countedAECircuit M D j := by
      apply List.mem_map.mpr
      exact ⟨s,List.mem_reverse.mp hs,rfl⟩
    cases hh : aeAccessInstruction M D j s with
    | gate U => exact hD U (by simpa [hh] using! hm)
    | query => simpa [hh,nativeStepMatrix] using! hO
  have hop := (l2_norm_list_map_prod_sub_prod_le w.reverse F G
    (fun s hs => l2_norm_unitary_le_one (hvalid A hca s hs))
    (fun s hs => l2_norm_unitary_le_one (hvalid B hcb s hs))).trans
      (native_ae_instruction_sum M A B j O w.reverse)
  have hc := (prepared_ae_access_ledger M (by omega) A j).2.2.1
  have hrev : aeInputAccesses w.reverse=aeInputAccesses w := by
    simp [aeInputAccesses, List.map_reverse]
  rw [hrev,hc] at hop
  let input := TensorState (Ket (⟨0,by omega⟩:Fin M)) (TensorState (Ket false) (Ket j))
  have hrA : Run O (countedAECircuit M A j) input=(w.reverse.map F).prod*ᵥinput := by
    rw [native_run_matrix]
    simp only [countedAECircuit, List.map_reverse, List.map_map, Function.comp_def]
    rfl
  have hrB : Run O (countedAECircuit M B j) input=(w.reverse.map G).prod*ᵥinput := by
    rw [native_run_matrix]
    simp only [countedAECircuit, List.map_reverse, List.map_map, Function.comp_def]
    rfl
  change ‖toEuclidean_fromVec
      (Run O (countedAECircuit M A j) input-Run O (countedAECircuit M B j) input)‖≤_
  rw [hrA,hrB,← Matrix.sub_mulVec]
  have he := l2_norm_mulVec_fromVec_le ((w.reverse.map F).prod-(w.reverse.map G).prod)
    (TensorState (Ket (⟨0,by omega⟩:Fin M)) (TensorState (Ket false) (Ket j)))
  rw [(normalized_iff_norm_toEuclidean_fromVec _).mp
    (normalized_tensorState (normalized_ket _) (normalized_tensorState (normalized_ket _) (normalized_ket _))),mul_one] at he
  change ‖toEuclidean_fromVec (((w.reverse.map F).prod-(w.reverse.map G).prod)*ᵥinput)‖≤_
  exact he.trans hop

/-- The ℓ¹ distance between the amplitude-estimation output laws for unitary preparations `A`
and `B` is at most `4 * (2 * (M-1) + 1) * ‖A-B‖`. -/
theorem native_ae_l1 {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2≤M) (A B : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A∈Matrix.unitaryGroup I ℂ) (hB : B∈Matrix.unitaryGroup I ℂ) :
    (∑ z,|(aeLaw M A j S hA hM).prob z-(aeLaw M B j S hB hM).prob z|)≤
      4*(2*(M-1)+1:ℕ)*‖A-B‖ := by
  have ha := prepared_ae_expanded_access_and_output M hM A j S hA
  have hb := prepared_ae_expanded_access_and_output M hM B j S hB
  apply (native_l1_from_events _ _ (2*(2*(M-1)+1:ℕ)*‖A-B‖) ?_).trans_eq
    (by ring)
  intro E
  have he :=
      measureProb_sub_le_two_mul_l2 _ _ (Finset.univ.filter (fun p => p.1∈E)) ha.2.2.2.1 hb.2.2.2.1
  have hd := native_ae_output_distance M hM A B j S hA hB
  have heA := aeLaw_event M hM A j S hA (fun z => z∈E)
  have heB := aeLaw_event M hM B j S hB (fun z => z∈E)
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at heA heB
  rw [heA,heB]
  convert! he.trans (mul_le_mul_of_nonneg_left hd (by norm_num)) using 1 <;>
    simp only [aeControlledGate, mul_assoc]
  all_goals congr 5

/-- The native layer preparation differs from its ideal real-payoff preparation by at most `32 /
2^(nativeLayerBits k)` in matrix norm. -/
theorem nativeLayerPrepare_error {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (f : I→ℚ) (k l : ℕ) (hA : A∈Matrix.unitaryGroup I ℂ) (hf : ∀ i,0≤f i) :
    ‖nativeLayerPrepare A f k l-payoffPreparation A (layerPayoff (fun i => (f i:ℝ)) l)‖≤
      32/(2:ℝ)^nativeLayerBits k := by
  have hp (i : I) := native_layered_payoff_exact_partition I f hf l i
  have hfun : (fun i => (nativeLayerPayoff f l i:ℝ))=layerPayoff (fun i => (f i:ℝ)) l :=
    funext (fun i => (hp i).2.2)
  rw [← hfun]
  unfold nativeLayerPrepare payoffPreparation
  rw [← Matrix.sub_mul]
  have hr := rationalPayoffRotation_error (nativeLayerPayoff f l) (nativeLayerBits k)
    (fun i => ⟨(hp i).1,(hp i).2.1⟩)
  have hT := l2_norm_unitary_le_one (tensorGate_unitary hA (Matrix.unitaryGroup Bool ℂ).one_mem)
  exact (norm_mul_le _ _).trans
      ((mul_le_mul hr hT (norm_nonneg _) (by positivity)).trans_eq (mul_one _))

/-- The chosen native precision makes the accumulated layer, repetition, and
amplitude-estimation perturbation budget at most `(1/2)^k`. -/
theorem nativeLayerBits_record_budget (k : ℕ) :
    (k+2:ℝ)*(2*layerRepetitions k+1)*4*(2*(layerGrid k-1)+1:ℕ)*
      (32/(2:ℝ)^nativeLayerBits k)≤(1/2:ℝ)^k := by
  have hcoord : ∀ m : ℕ, m+2≤2^(m+1) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih => rw [Nat.pow_succ]; omega
  have hr : 2*layerRepetitions k+1≤32*(k+2) := by unfold layerRepetitions; omega
  have hq : 2*(layerGrid k-1)+1≤2*layerGrid k := by have := layerGrid_pos k; omega
  have hgrid : layerGrid k≤2^(k+6)*2^(k+1) := by
    unfold layerGrid
    exact Nat.mul_le_mul_left _ (hcoord k)
  have hn : (k+2)*(2*layerRepetitions k+1)*128*(2*(layerGrid k-1)+1)*2^k≤2^nativeLayerBits k := by
    calc
      _ ≤ (2^(k+1))*(32*2^(k+1))*128*(2*(2^(k+6)*2^(k+1)))*2^k := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul (hcoord k) (hr.trans (Nat.mul_le_mul_left 32 (hcoord k)))))
          (hq.trans (Nat.mul_le_mul_left 2 hgrid)))
      _ = 2^(5*k+22) := by
        rw [show 5*k+22=k+k+k+k+k+22 by omega]
        simp only [pow_add]
        norm_num
        ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold nativeLayerBits; omega)
  have hnR : ((k+2:ℝ)*(2*layerRepetitions k+1)*128*(2*(layerGrid k-1)+1:ℕ))*(2:ℝ)^k≤(2:ℝ)^nativeLayerBits k := by
    exact_mod_cast hn
  rw [_root_.one_div_pow]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^k)).mpr
  have he : ((k+2:ℝ)*(2*layerRepetitions k+1)*4*(2*(layerGrid k-1)+1:ℕ)*
      (32/(2:ℝ)^nativeLayerBits k))*(2:ℝ)^k =
      (((k+2:ℝ)*(2*layerRepetitions k+1)*128*(2*(layerGrid k-1)+1:ℕ))*(2:ℝ)^k)/(2:ℝ)^nativeLayerBits k := by ring
  rw [he]
  exact (div_le_one (by positivity)).mpr hnR

/-- Any native record law with the specified product probabilities has ℓ¹ distance at most
`(1/2)^k` from the ideal `layerLaw`. -/
theorem native_layered_same_record_variation_budget
    (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I) (f : I→ℚ) (k : ℕ)
    (hA : A∈Matrix.unitaryGroup I ℂ) (hf : ∀ i,0≤f i)
    (hP : ∀ l : Fin (k+2),nativeLayerPrepare A f k l∈Matrix.unitaryGroup (I×Bool) ℂ)
    (law : FinDist (LayerRecord k))
    (hlaw : ∀ ω,law.prob ω=∏ l : Fin (k+2),
      (aeLaw (layerGrid k) (nativeLayerPrepare A f k l) (j,false) (nativeLayerEvent I)
        (hP l) (layerGrid_ge_two k)).probOf (ω l)) :
    (∑ ω : LayerRecord k,|law.prob ω-
      (layerLaw k A j (fun i => (f i:ℝ)) hA (fun i => by change (0:ℝ)≤(f i:ℝ); exact_mod_cast hf i)).prob ω|)≤(1/2:ℝ)^k := by
  let hfR := fun i => (show (0:ℝ)≤(f i:ℝ) by exact_mod_cast hf i)
  let p := nativeLayerTrialLaw A j f k hP
  let q := layerTrialLaw k A j (fun i => (f i:ℝ)) hA hfR
  have hl : ∀ l : Fin (k+2),
      (∑ u,|(p l).prob u-(q l).prob u|)≤
        (2*layerRepetitions k+1:ℕ)*(4*(2*(layerGrid k-1)+1:ℕ)*(32/(2:ℝ)^nativeLayerBits k)) := by
    intro l
    let P :=
        aeLaw (layerGrid k) (nativeLayerPrepare A f k l) (j,false) (nativeLayerEvent I) (hP l)
        (layerGrid_ge_two k)
    let Q := meanLaw (layerGrid k) A j (layerPayoff (fun i => (f i:ℝ)) l) hA
      (layerPayoff_mem_Icc _ hfR _) (layerGrid_ge_two k)
    have ht := native_product_l1 (2*layerRepetitions k+1) (fun _ => P) (fun _ => Q)
    have hae := (native_ae_l1 (layerGrid k) (layerGrid_ge_two k) (nativeLayerPrepare A f k l)
      (payoffPreparation A (layerPayoff (fun i => (f i:ℝ)) l)) (j,false) (nativeLayerEvent I) (hP l)
      (payoffPreparation_mem_unitaryGroup A _ hA (layerPayoff_mem_Icc _ hfR _))).trans
        (mul_le_mul_of_nonneg_left (nativeLayerPrepare_error A f k l hA hf) (by positivity))
    refine ht.trans ?_
    calc
      _ ≤ ∑ _ : Fin (2*layerRepetitions k+1),
          (4*(2*(layerGrid k-1)+1:ℕ)*(32/(2:ℝ)^nativeLayerBits k)) :=
        Finset.sum_le_sum (fun _ _ => hae)
      _ = _ := by simp
  have ht := native_product_l1 (k+2) p q
  simp_rw [hlaw, layerLaw_prob]
  refine ht.trans ?_
  calc
    _ ≤ ∑ _ : Fin (k+2),
        (2*layerRepetitions k+1:ℕ)*(4*(2*(layerGrid k-1)+1:ℕ)*(32/(2:ℝ)^nativeLayerBits k)) :=
      Finset.sum_le_sum (fun l _ => hl l)
    _ = (k+2:ℝ)*(2*layerRepetitions k+1)*4*(2*(layerGrid k-1)+1:ℕ)*(32/(2:ℝ)^nativeLayerBits k) := by simp; ring
    _ ≤ _ := nativeLayerBits_record_budget k

end Qatlib.Concepts.NativeNumerics.LayeredMean
