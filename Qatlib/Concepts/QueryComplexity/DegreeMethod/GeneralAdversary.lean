/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryExt
import Qatlib.Concepts.GramQueryCore.ModelSemantics.BooleanValueCompatibilityQuan
import Qatlib.Concepts.QueryComplexity.StateConversion.RealBudgetConversionAlgorithmQuan
import Qatlib.Concepts.QueryComplexity.DegreeMethod.AlphabetAdversary
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryConsumers
import Qatlib.Concepts.QueryComplexity.DegreeMethod.AlphabetInterrogation
import Qatlib.Concepts.SignedWeights.Representations.GeneralAdversaryLoss
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryRefinedDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.CircuitCompile
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.StateConversion
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.SignedWeights.Representations.LossCompletion

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false

open Matrix
open Qatlib
open Qatlib.Concepts.SignedWeights.Representations
open scoped Matrix.Norms.L2Operator ComplexOrder ENNReal
open Classical BigOperators

theorem povm_output_condition_transports_to_lift {H Y : Type} [Fintype H]
    [DecidableEq H] [Fintype Y] [DecidableEq Y] (out : Y → Matrix H H ℂ)
    (hout : IsPovm out) (v : QState H) (y : Y) :
    MeasureProb (povmLiftMatrix out *ᵥ v) (outcomeEvent Prod.fst y) = povmProb out y v :=
  povmLift_born out hout v y

set_option maxHeartbeats 800000 in

theorem general_povm_final_progress
    (X H Y : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
    [Fintype Y] [DecidableEq Y] (Gamma : Matrix X X ℂ) (weight : QState X)
    (out : Y → Matrix H H ℂ) (hout : IsPovm out) (states : X → QState H)
    (f : X → Y) (eps : ℝ)
    (hG : Gamma.IsHermitian) (hw : Normalized weight) (hs : ∀ x, Normalized (states x))
    (hz : ∀ x y, f x = f y → Gamma x y = 0) (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2)
    (hsuccess : ∀ x, 1 - eps ≤ povmProb out (f x) (states x)) :
    |advProgress Gamma weight (fun x => (povmLiftMatrix out : Matrix (Y × H) H ℂ) *ᵥ states x)|
      ≤ (2 * Real.sqrt (eps * (1 - eps)) + 2 * eps) * ‖Gamma‖ := by
  have hmain : ∀ (w : QState X) (st : X → QState (Y × H)),
      Gamma.IsHermitian → Normalized w → (∀ x, Normalized (st x)) →
      (∀ x y, f x = f y → Gamma x y = 0) → 0 ≤ eps → eps ≤ 1 / 2 →
      (∀ x, 1 - eps ≤ MeasureProb (st x) (Finset.univ.filter (fun h' => Prod.fst h' = f x))) →
      |advProgress Gamma w st| ≤ (2 * Real.sqrt (eps * (1 - eps)) + 2 * eps) * ‖Gamma‖ := by
    intro w st hG' hw' hs' hz' he0' he1' hsucc'
    exact multioutput_adversary_actual_final_progress X (Y × H) Y Gamma w st f Prod.fst eps
      hG' hw' hs' hz' he0' he1' hsucc'
  refine hmain weight (fun x => (povmLiftMatrix out : Matrix (Y × H) H ℂ) *ᵥ states x) hG hw ?_ hz
    he0 he1 ?_
  · intro x
    exact povmLift_normalized out hout (states x) (hs x)
  · intro x
    have h1 : MeasureProb ((povmLiftMatrix out : Matrix (Y × H) H ℂ) *ᵥ states x)
        (Finset.univ.filter (fun h' => Prod.fst h' = f x))
        = povmProb out (f x) (states x) := by
      have heq : Finset.univ.filter (fun h' => Prod.fst h' = f x)
          = outcomeEvent (Prod.fst : Y × H → Y) (f x) := rfl
      rw [heq]
      exact povmLift_born out hout (states x) (f x)
    rw [h1]
    exact hsuccess x

set_option maxHeartbeats 800000 in

theorem general_povm_final_progress_of_label
    (X H Y : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
    [Fintype Y] [DecidableEq Y] (Gamma : Matrix X X ℂ) (weight : QState X)
    (label : H → Y) (states : X → QState H) (f : X → Y) (eps : ℝ)
    (hG : Gamma.IsHermitian) (hw : Normalized weight) (hs : ∀ x, Normalized (states x))
    (hz : ∀ x y, f x = f y → Gamma x y = 0) (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2)
    (hsuccess : ∀ x, 1 - eps ≤ MeasureProb (states x) (outcomeEvent label (f x))) :
    |advProgress Gamma weight
        (fun x => (povmLiftMatrix (labelPovm label) : Matrix (Y × H) H ℂ) *ᵥ states x)|
      ≤ (2 * Real.sqrt (eps * (1 - eps)) + 2 * eps) * ‖Gamma‖ := by
  refine general_povm_final_progress X H Y Gamma weight (labelPovm label)
    (isPovm_labelPovm label) states f eps hG hw hs hz he0 he1 ?_
  intro x
  rw [labelPovm_povmProb]
  exact hsuccess x

theorem blockCosts_eq_block_value {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (gin : ∀ i, X i → Fin (n i) → Bool) (g : ∀ i, X i → Bool)
    (α : ((i : Fin k) × Fin (n i)) → ℝ) (i : Fin k) :
    blockCosts gin g α i
      = advAlphaENN (gin i) (g i) (fun j => ENNReal.ofReal (α ⟨i, j⟩)) := rfl

theorem composition_upper_bound_on_source_scope {k : ℕ} {Y : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (gin : ∀ i, Y i → Fin (n i) → Bool) (g : ∀ i, Y i → Bool)
    (f : (Fin k → Bool) → Bool) (alpha : ((i : Fin k) × Fin (n i)) → ℝ)
    (ha : ∀ c, 0 < alpha c) (hfn : ∃ (u v : Fin k → Bool), f u ≠ f v)
    (hgn : ∀ i, ∃ (a b : Y i), g i a ≠ g i b) (hfin : ∀ i, blockCosts gin g alpha i < ⊤) :
    advAlphaENN (composedInput gin) (composedFunction g f) (fun c => ENNReal.ofReal (alpha c))
      ≤ advAlphaENN (fun u : Fin k → Bool => u) f (blockCosts gin g alpha) :=
  (Qatlib.Concepts.AdversaryBounds.AdvDuality.stageA_general_adversary_clause18_source_complete
    gin g f alpha ha hfn hgn hfin).1

theorem real_zero_reciprocal_is_top : (ENNReal.ofReal (0 : ℝ))⁻¹ = ⊤ := by
  rw [ENNReal.ofReal_zero, ENNReal.inv_zero]

set_option linter.unusedVariables false in

theorem advAlphaR_mono_of_cost_le {X κ : Type} [Fintype X] [DecidableEq X]
    [Fintype κ] [DecidableEq κ] (input : X → κ → Bool) (g : X → Bool)
    (α α' : κ → ℝ) (hα : ∀ i, 0 ≤ α i) (hle : ∀ i, α i ≤ α' i) :
    advAlphaR input g α ≤ advAlphaR input g α' := by
  unfold advAlphaR
  refine iSup_mono fun A : {A : Matrix X X ℝ // A.IsSymm ∧ (∀ x y, 0 ≤ A x y) ∧
      (∀ x y, g x = g y → A x y = 0) ∧ A ≠ 0} => ?_
  unfold advAlphaWitnessR
  refine iInf_mono fun i : κ => ?_
  have hmul : ENNReal.ofReal (α i) ≤ ENNReal.ofReal (α' i) := ENNReal.ofReal_le_ofReal (hle i)
  rw [mul_div_assoc, mul_div_assoc]
  gcongr

set_option maxHeartbeats 800000 in

theorem instrument_terminal_progress
    (X : Type) [Fintype X] [DecidableEq X] {Y : Type} [Fintype Y] {D E : ℕ}
    (I : Instrument Y D E) (Gamma : Matrix X X ℂ) (weight : QState X)
    (states : X → QState (Fin D)) (f : X → Y) (eps : ℝ)
    (hG : Gamma.IsHermitian) (hw : Normalized weight) (hs : ∀ x, Normalized (states x))
    (hz : ∀ x y, f x = f y → Gamma x y = 0) (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2)
    (hsuccess : ∀ x, 1 - eps ≤ povmProb (instrumentReadout I) (f x) (states x)) :
    |advProgress Gamma weight
        (fun x => (povmLiftMatrix (instrumentReadout I) : Matrix (Y × Fin D) (Fin D) ℂ) *ᵥ states x)|
      ≤ (2 * Real.sqrt (eps * (1 - eps)) + 2 * eps) * ‖Gamma‖ := by
  refine general_povm_final_progress X (Fin D) Y Gamma weight (instrumentReadout I)
    (instrumentReadout_isPovm I) states f eps hG hw hs hz he0 he1 hsuccess

theorem instrument_branch_probability {Y : Type} [Fintype Y] {D E : ℕ}
    (I : Instrument Y D E) (y : Y) (psi : QState (Fin D)) :
    povmProb (instrumentReadout I) y psi = (Matrix.trace (I.branch y (outerProduct psi))).re :=
  instrumentReadout_prob I y psi

private theorem inner_hermitian_mulVec {H : Type} [Fintype H] [DecidableEq H]
    (M : Matrix H H ℂ) (hM : M.IsHermitian) (u v : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (M *ᵥ u) v = Qatlib.Foundations.PureStateMath.Inner u (M *ᵥ v) := by
  classical
  have h := lift_inner_rect (K := H) M u v
  rwa [hM] at h

private theorem inner_hermitian_two_mulVec {H : Type} [Fintype H] [DecidableEq H]
    (M N : Matrix H H ℂ) (hM : M.IsHermitian) (u v : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (M *ᵥ u) (N *ᵥ v) = Qatlib.Foundations.PureStateMath.Inner u ((M * N) *ᵥ v) := by
  classical
  calc Qatlib.Foundations.PureStateMath.Inner (M *ᵥ u) (N *ᵥ v) = Qatlib.Foundations.PureStateMath.Inner u (Mᴴ *ᵥ (N *ᵥ v)) := lift_inner_rect _ _ _
    _ = Qatlib.Foundations.PureStateMath.Inner u ((Mᴴ * N) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = Qatlib.Foundations.PureStateMath.Inner u ((M * N) *ᵥ v) := by rw [hM]

private theorem inner_add_right' {H : Type} [Fintype H] [DecidableEq H]
    (u v w : QState H) : Qatlib.Foundations.PureStateMath.Inner u (v + w) = Qatlib.Foundations.PureStateMath.Inner u v + Qatlib.Foundations.PureStateMath.Inner u w := by
  simp only [Qatlib.Foundations.PureStateMath.inner_apply, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]

private theorem inner_sub_right' {H : Type} [Fintype H] [DecidableEq H]
    (u v w : QState H) : Qatlib.Foundations.PureStateMath.Inner u (v - w) = Qatlib.Foundations.PureStateMath.Inner u v - Qatlib.Foundations.PureStateMath.Inner u w := by
  simp only [Qatlib.Foundations.PureStateMath.inner_apply, Pi.sub_apply, mul_sub,
      Finset.sum_sub_distrib]

private theorem inner_add_left' {H : Type} [Fintype H] [DecidableEq H]
    (u v w : QState H) : Qatlib.Foundations.PureStateMath.Inner (u + v) w = Qatlib.Foundations.PureStateMath.Inner u w + Qatlib.Foundations.PureStateMath.Inner v w := by
  simp only [Qatlib.Foundations.PureStateMath.inner_apply, Pi.add_apply, map_add, add_mul,
      Finset.sum_add_distrib]

private theorem inner_sub_left' {H : Type} [Fintype H] [DecidableEq H]
    (u v w : QState H) : Qatlib.Foundations.PureStateMath.Inner (u - v) w = Qatlib.Foundations.PureStateMath.Inner u w - Qatlib.Foundations.PureStateMath.Inner v w := by
  simp only [Qatlib.Foundations.PureStateMath.inner_apply, Pi.sub_apply, map_sub, sub_mul,
      Finset.sum_sub_distrib]

private theorem inner_stack_expand {X H : Type} [Fintype X] [DecidableEq X] [Fintype H]
    [DecidableEq H] (Γ : Matrix X X ℂ) (weight : QState X) (u w : X → QState H) :
    Qatlib.Foundations.PureStateMath.Inner (advStack weight u) (TensorGate Γ (1 : Matrix H H ℂ) *ᵥ (advStack weight w))
      = ∑ x, ∑ y, (starRingEnd ℂ) (weight x) * Γ x y * weight y * Qatlib.Foundations.PureStateMath.Inner (u x) (w y) := by
  classical
  simp only [Qatlib.Foundations.PureStateMath.inner_apply, Fintype.sum_prod_type,
    advTensor_mulVec, advStack, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Finset.sum_congr rfl fun h _ => ?_
  ring

private theorem stack_sq_eq {X H : Type} [Fintype X] [DecidableEq X] [Fintype H]
    [DecidableEq H] (weight : QState X) (u : X → QState H) :
    ‖toEuclidean_fromVec (advStack weight u)‖ ^ 2 = ∑ x, ‖weight x‖ ^ 2 * (∑ h, ‖u x h‖ ^ 2) := by
  rw [norm_toEuclidean_fromVec_sq]
  simp only [Fintype.sum_prod_type, advStack, norm_mul, mul_pow]
  apply Finset.sum_congr rfl
  intro x _
  exact (Finset.mul_sum Finset.univ (fun h => ‖u x h‖ ^ 2) (‖weight x‖ ^ 2)).symm

theorem projective_correct_components_orthogonal {X H Y : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Fintype Y] [DecidableEq Y]
    (P : OrthogonalProjectors H Y) (f : X → Y) (states : X → QState H) (x y : X)
    (hxy : f x ≠ f y) :
    Qatlib.Foundations.PureStateMath.Inner (projectiveCorrect P f states x) (projectiveCorrect P f states y) = 0 := by
  classical
  have hzero : P.proj (f x) * P.proj (f y) = 0 := P.horth (f x) (f y) hxy
  calc Qatlib.Foundations.PureStateMath.Inner (projectiveCorrect P f states x) (projectiveCorrect P f states y)
      = Qatlib.Foundations.PureStateMath.Inner (states x) ((P.proj (f x) * P.proj (f y)) *ᵥ states y) := by
        exact inner_hermitian_two_mulVec _ _ (P.hherm (f x)) _ _
    _ = Qatlib.Foundations.PureStateMath.Inner (states x) (0 *ᵥ states y) := by rw [hzero]
    _ = 0 := by simp [Qatlib.Foundations.PureStateMath.inner_apply]

theorem projective_correct_error_orthogonal {X H Y : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Fintype Y] [DecidableEq Y]
    (P : OrthogonalProjectors H Y) (f : X → Y) (states : X → QState H) (x : X) :
    Qatlib.Foundations.PureStateMath.Inner (projectiveCorrect P f states x) (projectiveError P f states x) = 0 ∧
    Qatlib.Foundations.PureStateMath.Inner (projectiveError P f states x) (projectiveCorrect P f states x) = 0 := by
  classical
  have hself : Qatlib.Foundations.PureStateMath.Inner (P.proj (f x) *ᵥ states x) (P.proj (f x) *ᵥ states x)
      = Qatlib.Foundations.PureStateMath.Inner (states x) (P.proj (f x) *ᵥ states x) := by
    have h := inner_hermitian_two_mulVec (P.proj (f x)) (P.proj (f x)) (P.hherm (f x))
      (states x) (states x)
    rwa [P.hidem (f x)] at h
  have hcross : Qatlib.Foundations.PureStateMath.Inner (P.proj (f x) *ᵥ states x) (states x)
      = Qatlib.Foundations.PureStateMath.Inner (states x) (P.proj (f x) *ᵥ states x) :=
    inner_hermitian_mulVec _ (P.hherm (f x)) _ _
  refine ⟨?_, ?_⟩
  · show Qatlib.Foundations.PureStateMath.Inner (P.proj (f x) *ᵥ states x) (states x - P.proj (f x) *ᵥ states x) = 0
    rw [inner_sub_right', hcross, hself]
    ring
  · show Qatlib.Foundations.PureStateMath.Inner (states x - P.proj (f x) *ᵥ states x) (P.proj (f x) *ᵥ states x) = 0
    rw [inner_sub_left', hcross.symm, hself, hcross]
    ring

theorem projective_correct_mass_is_born {X H Y : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Fintype Y] [DecidableEq Y]
    (P : OrthogonalProjectors H Y) (f : X → Y) (states : X → QState H) (x : X) :
    (Qatlib.Foundations.PureStateMath.Inner (projectiveCorrect P f states x) (projectiveCorrect P f states x)).re
      = povmProb (projectivePovm P) (f x) (states x) := by
  classical
  have hself : Qatlib.Foundations.PureStateMath.Inner (P.proj (f x) *ᵥ states x) (P.proj (f x) *ᵥ states x)
      = Qatlib.Foundations.PureStateMath.Inner (states x) (P.proj (f x) *ᵥ states x) := by
    have h := inner_hermitian_two_mulVec (P.proj (f x)) (P.proj (f x)) (P.hherm (f x))
      (states x) (states x)
    rwa [P.hidem (f x)] at h
  show (Qatlib.Foundations.PureStateMath.Inner (P.proj (f x) *ᵥ states x) (P.proj (f x) *ᵥ states x)).re
      = povmProb (projectivePovm P) (f x) (states x)
  rw [hself]
  rfl

theorem projective_error_mass {X H Y : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Fintype Y] [DecidableEq Y]
    (P : OrthogonalProjectors H Y) (f : X → Y) (states : X → QState H) (x : X)
    (hs : Normalized (states x)) :
    (Qatlib.Foundations.PureStateMath.Inner (projectiveError P f states x) (projectiveError P f states x)).re
      = 1 - povmProb (projectivePovm P) (f x) (states x) := by
  classical
  have horth := projective_correct_error_orthogonal P f states x
  have hexp : Qatlib.Foundations.PureStateMath.Inner (projectiveCorrect P f states x + projectiveError P f states x)
      (projectiveCorrect P f states x + projectiveError P f states x)
      = Qatlib.Foundations.PureStateMath.Inner (projectiveCorrect P f states x) (projectiveCorrect P f states x)
        + Qatlib.Foundations.PureStateMath.Inner (projectiveError P f states x) (projectiveError P f states x) := by
    rw [inner_add_right', inner_add_left', inner_add_left', horth.1, horth.2]
    ring
  have hexp2 : Qatlib.Foundations.PureStateMath.Inner (states x) (states x)
      = Qatlib.Foundations.PureStateMath.Inner (projectiveCorrect P f states x) (projectiveCorrect P f states x)
        + Qatlib.Foundations.PureStateMath.Inner (projectiveError P f states x) (projectiveError P f states x) := by
    calc Qatlib.Foundations.PureStateMath.Inner (states x) (states x) = Qatlib.Foundations.PureStateMath.Inner
          (projectiveCorrect P f states x + projectiveError P f states x)
          (projectiveCorrect P f states x + projectiveError P f states x) := by
            rw [projectiveCorrect_add_error P f states x]
      _ = _ := hexp
  have hnorm : (Qatlib.Foundations.PureStateMath.Inner (states x) (states x)).re = 1 := by
    have h1 : ‖toEuclidean_fromVec (states x)‖ = 1 :=
      (normalized_iff_norm_toEuclidean_fromVec _).mp hs
    rw [← norm_toEuclidean_sq_eq_re_inner, h1, one_pow]
  have hre : (Qatlib.Foundations.PureStateMath.Inner (projectiveError P f states x) (projectiveError P f states x)).re
      = (Qatlib.Foundations.PureStateMath.Inner (states x) (states x)).re
        - (Qatlib.Foundations.PureStateMath.Inner (projectiveCorrect P f states x) (projectiveCorrect P f states x)).re := by
    have h := congrArg Complex.re hexp2
    rw [Complex.add_re] at h
    linarith
  rw [hre, hnorm, projective_correct_mass_is_born P f states x]

theorem projective_correct_component_self_term_vanishes {X H Y : Type} [Fintype X]
    [DecidableEq X] [Fintype H] [DecidableEq H] [Fintype Y] [DecidableEq Y]
    (Γ : Matrix X X ℂ) (weight : QState X) (P : OrthogonalProjectors H Y)
    (states : X → QState H) (f : X → Y)
    (hz : ∀ x y, f x = f y → Γ x y = 0) :
    Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveCorrect P f states x))
      (TensorGate Γ (1 : Matrix H H ℂ) *ᵥ
        (advStack weight (fun x => projectiveCorrect P f states x))) = 0 := by
  classical
  have hexp := inner_stack_expand Γ weight (fun x => projectiveCorrect P f states x)
    (fun x => projectiveCorrect P f states x)
  rw [hexp]
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  by_cases hxy : f x = f y
  · rw [hz x y hxy]
    ring
  · rw [projective_correct_components_orthogonal P f states x y hxy]
    ring

private theorem norm_add_four {E : Type} [NormedAddCommGroup E] (a b c d : E) :
    ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 : ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
  have h2 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    calc ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
      _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by
          calc ‖a + b‖ + ‖c‖ ≤ (‖a‖ + ‖b‖) + ‖c‖ :=
                add_le_add_left (norm_add_le _ _) _
          _ = ‖a‖ + ‖b‖ + ‖c‖ := by ring
  calc ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := h1
    _ ≤ (‖a‖ + ‖b‖ + ‖c‖) + ‖d‖ := add_le_add_left h2 _
    _ = ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by ring

theorem projective_final_progress_on_original_register :
    ∀ (X H Y : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
      [Fintype Y] [DecidableEq Y] (Γ : Matrix X X ℂ) (weight : QState X)
      (P : OrthogonalProjectors H Y) (states : X → QState H) (f : X → Y) (eps : ℝ),
    Γ.IsHermitian → Normalized weight → (∀ x, Normalized (states x)) →
    (∀ x y, f x = f y → Γ x y = 0) → 0 ≤ eps → eps ≤ 1 / 2 →
    (∀ x, 1 - eps ≤ povmProb (projectivePovm P) (f x) (states x)) →
    |advProgress Γ weight states| ≤ (2 * Real.sqrt (eps * (1 - eps)) + 2 * eps) * ‖Γ‖ := by
  intro X H Y _ _ _ _ _ _ Γ weight P states f eps hG hw hs hz he0 he1 hsucc
  classical

  have hself := projective_correct_component_self_term_vanishes Γ weight P states f hz
  have hA : ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ ≤ ‖Γ‖ := by
    (try dsimp)
    rw [l2_norm_tensorGate]
    exact (mul_le_mul_of_nonneg_left l2_norm_one_le (norm_nonneg _)).trans_eq (mul_one _)

  have hcsq : ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ ^ 2 = ∑ x, ‖weight x‖ ^ 2 * povmProb (projectivePovm P) (f x) (states x) := by
    rw [stack_sq_eq]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← norm_toEuclidean_fromVec_sq, norm_toEuclidean_sq_eq_re_inner,
      projective_correct_mass_is_born P f states x]
  have hbsq : ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ ^ 2 = ∑ x, ‖weight x‖ ^ 2
        * (1 - povmProb (projectivePovm P) (f x) (states x)) := by
    rw [stack_sq_eq]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← norm_toEuclidean_fromVec_sq, norm_toEuclidean_sq_eq_re_inner,
      projective_error_mass P f states x (hs x)]
  have hwsum : (∑ x, ‖weight x‖ ^ 2) = 1 := by
    exact hw
  have hcmass : 1 - eps ≤ ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ ^ 2 := by
    have h1 : (∑ x, ‖weight x‖ ^ 2 * povmProb (projectivePovm P) (f x) (states x))
        ≥ ∑ x, ‖weight x‖ ^ 2 * (1 - eps) := by
      refine Finset.sum_le_sum fun x _ => ?_
      exact mul_le_mul_of_nonneg_left (hsucc x) (sq_nonneg _)
    have h2 : (∑ x, ‖weight x‖ ^ 2 * (1 - eps)) = 1 - eps := by
      rw [← Finset.sum_mul, hwsum]
      ring
    rw [hcsq]
    linarith
  have hbsmall : ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ ^ 2 ≤ eps := by
    have h1 : (∑ x, ‖weight x‖ ^ 2 * (1 - povmProb (projectivePovm P) (f x) (states x)))
        ≤ ∑ x, ‖weight x‖ ^ 2 * eps := by
      refine Finset.sum_le_sum fun x _ => ?_
      have hb : 1 - eps ≤ povmProb (projectivePovm P) (f x) (states x) := hsucc x
      have h1' : 1 - povmProb (projectivePovm P) (f x) (states x) ≤ eps := by linarith
      exact mul_le_mul_of_nonneg_left h1' (sq_nonneg _)
    have h2 : (∑ x, ‖weight x‖ ^ 2 * eps) = eps := by
      rw [← Finset.sum_mul, hwsum]
      ring
    rw [hbsq]
    linarith

  have hvb : advStack weight states = (advStack weight (fun x => projectiveCorrect P f states x)) + (advStack weight (fun x => projectiveError P f states x)) := by
    funext p
    simp only [advStack, projectiveCorrect, projectiveError, Pi.sub_apply, Pi.add_apply]
    ring

  have hsum1 : (∑ x, ‖weight x‖ ^ 2 * povmProb (projectivePovm P) (f x) (states x))
      + (∑ x, ‖weight x‖ ^ 2 * (1 - povmProb (projectivePovm P) (f x) (states x))) = 1 := by
    have h1 : ∀ x, ‖weight x‖ ^ 2 * povmProb (projectivePovm P) (f x) (states x)
        + ‖weight x‖ ^ 2 * (1 - povmProb (projectivePovm P) (f x) (states x))
        = ‖weight x‖ ^ 2 := by
      intro x
      ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun x _ => h1 x, hwsum]
  have hsq1 : ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ ^ 2 + ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ ^ 2 = 1 := by
    rw [hcsq, hbsq, hsum1]
  have hprod : ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ ≤ Real.sqrt (eps * (1 - eps)) := by
    have hnon : 0 ≤ eps * (1 - eps) := mul_nonneg he0 (by linarith)
    have hsqrt : Real.sqrt (eps * (1 - eps)) ^ 2 = eps * (1 - eps) := Real.sq_sqrt hnon
    have hmul : eps * (1 - eps) - (‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ ^ 2 * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ ^ 2)
        = (eps - ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ ^ 2) * (1 - eps - ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ ^ 2) := by
      have h1 :
          ‖toEuclidean_fromVec
          (advStack weight (fun x => projectiveCorrect P f states x))‖ ^ 2 = 1 - ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ ^ 2 := by linarith [hsq1]
      rw [h1]
      ring
    have hpos : 0 ≤ (eps - ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ ^ 2) * (1 - eps - ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ ^ 2) := by
      apply mul_nonneg
      · linarith [hbsmall]
      · linarith [hbsmall, he1]
    have htn :
        0 ≤ ‖toEuclidean_fromVec
        (advStack weight (fun x => projectiveCorrect P f states x))‖ * ‖toEuclidean_fromVec
        (advStack weight (fun x => projectiveError P f states x))‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsn : 0 ≤ Real.sqrt (eps * (1 - eps)) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ - Real.sqrt (eps * (1 - eps)))]

  have hsplit : Qatlib.Foundations.PureStateMath.Inner (advStack weight states) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ advStack weight states)
      = Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveCorrect P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveCorrect P f states x))) + Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveError P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveCorrect P f states x))) + Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveCorrect P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveError P f states x))) + Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveError P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveError P f states x))) := by
    rw [hvb, Matrix.mulVec_add, inner_add_right', inner_add_left', inner_add_left']
    ring
  have hnorm4 : ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight states) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ advStack weight states)‖
      ≤ ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveCorrect P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveCorrect P f states x)))‖ + ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveError P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveCorrect P f states x)))‖ + ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveCorrect P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveError P f states x)))‖ + ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveError P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveError P f states x)))‖ := by
    rw [hsplit]
    exact norm_add_four _ _ _ _
  have hself0 : ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveCorrect P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveCorrect P f states x)))‖ = 0 := by
    rw [hself]
    simp
  have hcross' :
      ‖Qatlib.Foundations.PureStateMath.Inner
      (advStack weight (fun x => projectiveError P f states x))
      ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveCorrect P f states x)))‖ ≤ ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ := adv_inner_matrix_bound _ _ _
  have hcross :
      ‖Qatlib.Foundations.PureStateMath.Inner
      (advStack weight (fun x => projectiveCorrect P f states x))
      ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveError P f states x)))‖ ≤ ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ := adv_inner_matrix_bound _ _ _
  have herr :
      ‖Qatlib.Foundations.PureStateMath.Inner
      (advStack weight (fun x => projectiveError P f states x))
      ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveError P f states x)))‖ ≤ ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ := adv_inner_matrix_bound _ _ _
  have hbound : ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight states) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ advStack weight states)‖
      ≤ 0 + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖) + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖) + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖) := by
    calc
      ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight states) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ advStack weight states)‖
          ≤ ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveCorrect P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveCorrect P f states x)))‖ + ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveError P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveCorrect P f states x)))‖ + ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveCorrect P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveError P f states x)))‖ + ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveError P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveError P f states x)))‖ := hnorm4
      _ = 0 + ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveError P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveCorrect P f states x)))‖ + ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveCorrect P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveError P f states x)))‖ + ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight (fun x => projectiveError P f states x)) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ (advStack weight (fun x => projectiveError P f states x)))‖ := by rw [hself0]
      _ ≤ 0 + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖) + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖) + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖) := by
          gcongr

  have hprog : advProgress Γ weight states
      = (Qatlib.Foundations.PureStateMath.Inner (advStack weight states) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ advStack weight states)).re :=
    advProgress_stack Γ weight states
  have hstep : 0 + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖) + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖) + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖)
      ≤ 2 * Real.sqrt (eps * (1 - eps)) * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ + eps * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ := by
    have h1 : ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ ≤ ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * Real.sqrt (eps * (1 - eps)) := by
      calc ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ = ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * (‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖) := by ring
        _ ≤ ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * Real.sqrt (eps * (1 - eps)) := by
          have hh := mul_le_mul_of_nonneg_left hprod (norm_nonneg (TensorGate Γ (1 : Matrix H H ℂ)))
          nlinarith [hh]
    have h2 : ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ ≤ ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * Real.sqrt (eps * (1 - eps)) := by
      calc ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ = ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * (‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖) := by ring
        _ ≤ ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * Real.sqrt (eps * (1 - eps)) := by
          have hh := mul_le_mul_of_nonneg_left hprod (norm_nonneg (TensorGate Γ (1 : Matrix H H ℂ)))
          nlinarith [hh]
    have h3 : ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ ≤ eps * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ := by
      have hb2 :
          ‖toEuclidean_fromVec
          (advStack weight (fun x => projectiveError P f states x))‖ ^ 2 ≤ eps := hbsmall
      have hAn : 0 ≤ ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ :=
        norm_nonneg (TensorGate Γ (1 : Matrix H H ℂ))
      have hh : ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ ^ 2
          * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖
          ≤ eps * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ :=
        mul_le_mul_of_nonneg_right hb2 hAn
      calc ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ = ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ ^ 2 * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ := by ring
        _ ≤ eps * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ := hh
    calc
      0 + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖) + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖) + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖)
          ≤ 0 + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * Real.sqrt (eps * (1 - eps)))
            + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * Real.sqrt (eps * (1 - eps))) + (eps * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖) := by
              nlinarith [h1, h2, h3]
      _ = 2 * Real.sqrt (eps * (1 - eps)) * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ + eps * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ := by ring
  have hstep2 : 2 * Real.sqrt (eps * (1 - eps)) * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ + eps * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖
      ≤ 2 * Real.sqrt (eps * (1 - eps)) * ‖Γ‖ + eps * ‖Γ‖ := by
    calc 2 * Real.sqrt (eps * (1 - eps)) * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ + eps * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖
        = (2 * Real.sqrt (eps * (1 - eps)) + eps) * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ := by ring
      _ ≤ (2 * Real.sqrt (eps * (1 - eps)) + eps) * ‖Γ‖ := by
        have hA' : ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ ≤ ‖Γ‖ := hA
        gcongr
      _ = 2 * Real.sqrt (eps * (1 - eps)) * ‖Γ‖ + eps * ‖Γ‖ := by ring
  have hstep3 : 2 * Real.sqrt (eps * (1 - eps)) * ‖Γ‖ + eps * ‖Γ‖
      ≤ (2 * Real.sqrt (eps * (1 - eps)) + 2 * eps) * ‖Γ‖ := by
    nlinarith [norm_nonneg Γ]
  calc |advProgress Γ weight states|
      = |(Qatlib.Foundations.PureStateMath.Inner (advStack weight states) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ advStack weight states)).re| := by
        rw [hprog]
    _ ≤ ‖Qatlib.Foundations.PureStateMath.Inner (advStack weight states) ((TensorGate Γ (1 : Matrix H H ℂ)) *ᵥ advStack weight states)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ 0 + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖) + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveCorrect P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖) + (‖(TensorGate Γ (1 : Matrix H H ℂ))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖ * ‖toEuclidean_fromVec (advStack weight (fun x => projectiveError P f states x))‖) := hbound
    _ ≤ 2 * Real.sqrt (eps * (1 - eps)) * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ + eps * ‖(TensorGate Γ (1 : Matrix H H ℂ))‖ := hstep
    _ ≤ 2 * Real.sqrt (eps * (1 - eps)) * ‖Γ‖ + eps * ‖Γ‖ := hstep2
    _ ≤ (2 * Real.sqrt (eps * (1 - eps)) + 2 * eps) * ‖Γ‖ := hstep3

theorem genCutWitness_hermitian {X : Type} [Fintype X] [DecidableEq X] (x y : X) :
    (genCutWitness x y).IsHermitian := by
  have hGadj : (cutWitness x y)ᴴ = cutWitness x y := cutWitness_hermitian x y
  have hGadj' : ∀ i j, star ((cutWitness x y) j i) = (cutWitness x y) i j := by
    intro i j
    have h := congrArg (fun M : Matrix X X ℂ => M i j) hGadj
    simpa [Matrix.conjTranspose_apply] using! h
  ext i j
  simp [genCutWitness, Matrix.conjTranspose_apply, Matrix.smul_apply, Complex.conj_ofReal,
    hGadj']

theorem genCutWitness_zero_on_equal {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {g : X → E} (x y : X) (hgy : g x ≠ g y) (u v : X)
    (h : g u = g v) : genCutWitness x y u v = 0 := by
  have hz : cutWitness x y u v = 0 := cutWitness_support x y hgy u v h
  rw [genCutWitness, Matrix.smul_apply, hz]
  simp

theorem genCutWitness_norm {X : Type} [Fintype X] [DecidableEq X] (x y : X)
    (hxy : x ≠ y) : ‖genCutWitness x y‖ = 1 := by
  set m := ‖cutWitness x y‖ with hmdef
  have hpos : 0 < m := by
    have h1 : 1 ≤ m := by
      rw [hmdef]
      exact cutWitness_norm_ge_one x y hxy
    exact lt_of_lt_of_le (by norm_num) h1
  have hG' : genCutWitness x y = ((1 / m : ℝ) : ℂ) • cutWitness x y := by
    simp [genCutWitness, hmdef]
  have hnorm : ‖genCutWitness x y‖ = ‖cutWitness x y‖ / m := by
    rw [hG', l2_opNorm_def, l2_opNorm_def, map_smul, norm_smul]
    rw [show ‖((1 / m : ℝ) : ℂ)‖ = |1 / m| from RCLike.norm_ofReal (1 / m : ℝ),
      abs_of_pos (by positivity : (0 : ℝ) < 1 / m)]
    field_simp
  rw [hnorm, hmdef]
  exact div_self (ne_of_gt hpos)

theorem genCutWitness_filter_le_one {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] (input : X → Fin n → A)
    (x y : X) (hxy : x ≠ y) (j : Fin n) :
    ‖genFilterDelta input j ⊙ genCutWitness x y‖ ≤ 1 := by
  set m := ‖cutWitness x y‖ with hmdef
  have hpos : 0 < m := by
    have h1 : 1 ≤ m := by
      rw [hmdef]
      exact cutWitness_norm_ge_one x y hxy
    exact lt_of_lt_of_le (by norm_num) h1
  have hG' : genCutWitness x y = ((1 / m : ℝ) : ℂ) • cutWitness x y := by
    simp [genCutWitness, hmdef]
  have hhad : genFilterDelta input j ⊙ genCutWitness x y =
      ((1 / m : ℝ) : ℂ) • (genFilterDelta input j ⊙ cutWitness x y) := by
    rw [hG']
    ext u v
    simp [Matrix.smul_apply, Matrix.hadamard_apply]
    ring
  have hfilter : genFilterDelta input j ⊙ cutWitness x y =
      genAdvFilter input (cutWitness x y) j :=
    (genAdvFilter_eq_genFilterDelta input (cutWitness x y) j).symm
  have hbound : ‖genAdvFilter input (cutWitness x y) j‖ ≤ ‖cutWitness x y‖ :=
    genAdvFilter_cutWitness_le input x y j
  rw [hhad, l2_opNorm_def, map_smul, norm_smul]
  rw [show ‖((1 / m : ℝ) : ℂ)‖ = |1 / m| from RCLike.norm_ofReal (1 / m : ℝ),
    abs_of_pos (by positivity : (0 : ℝ) < 1 / m)]
  rw [hfilter]
  have hmul : (1 / m : ℝ) * ‖genAdvFilter input (cutWitness x y) j‖ ≤
      (1 / m : ℝ) * ‖cutWitness x y‖ :=
    mul_le_mul_of_nonneg_left hbound (by positivity)
  calc (1 / m : ℝ) * ‖genAdvFilter input (cutWitness x y) j‖ ≤
      (1 / m : ℝ) * ‖cutWitness x y‖ := hmul
    _ = 1 := by
      have hmm : (1 / m : ℝ) * m = 1 := by field_simp
      rw [hmdef] at hmm
      exact hmm

theorem gen_adversaryValue_ge_one_of_cross_output
    {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
    {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (input : X → Fin n → A) (f : X → E) (x y : X) (hgy : f x ≠ f y) :
    1 ≤ genAdversaryValue input f := by
  have hxy : x ≠ y := by
    intro h
    exact hgy (h ▸ rfl)
  have hnorm : ‖genCutWitness x y‖ = 1 := genCutWitness_norm x y hxy
  have hfeas : (genCutWitness x y).IsHermitian ∧
      (∀ u v, f u = f v → genCutWitness x y u v = 0) ∧
      (∀ j, ‖genFilterDelta input j ⊙ genCutWitness x y‖ ≤ 1) := by
    refine ⟨genCutWitness_hermitian x y, ?_, ?_⟩
    · intro u v h
      exact genCutWitness_zero_on_equal x y hgy u v h
    · intro j
      exact genCutWitness_filter_le_one input x y hxy j
  have hle : ENNReal.ofReal ‖genCutWitness x y‖ ≤ genAdversaryValue input f := by
    refine le_iSup_of_le ⟨genCutWitness x y, hfeas.1, hfeas.2.1, hfeas.2.2⟩ ?_
    show ENNReal.ofReal ‖genCutWitness x y‖ ≤ ENNReal.ofReal ‖genCutWitness x y‖
    exact ENNReal.ofReal_le_ofReal le_rfl
  rw [hnorm] at hle
  simpa using! hle

theorem gen_ratio_le_sdp
    {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
    {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (input : X → Fin n → A) (f : X → E) (Γ : Matrix X X ℂ)
    (hG : Γ.IsHermitian) (hz : ∀ x y, f x = f y → Γ x y = 0)
    (hm : 0 < maxFilterNorm input Γ) :
    ENNReal.ofReal (‖Γ‖ / maxFilterNorm input Γ) ≤ genAdversaryValue input f := by
  set m := maxFilterNorm input Γ with hmdef
  have hmpos : 0 < m := hm
  set c : ℂ := ((1 / m : ℝ) : ℂ) with hc
  set Γ' : Matrix X X ℂ := c • Γ with hG'
  have hnorm : ‖Γ'‖ = ‖Γ‖ / m := by
    rw [hG', l2_opNorm_def, l2_opNorm_def, map_smul, norm_smul]
    rw [hc, show ‖((1 / m : ℝ) : ℂ)‖ = |1 / m| from RCLike.norm_ofReal (1 / m : ℝ),
      abs_of_pos (by positivity : (0 : ℝ) < 1 / m)]
    field_simp
  have hG'herm : Γ'.IsHermitian := by
    have hGadj : Γᴴ = Γ := hG
    have hGadj' : ∀ i j, star (Γ j i) = Γ i j := by
      intro i j
      have h := congrArg (fun M : Matrix X X ℂ => M i j) hGadj
      simpa [Matrix.conjTranspose_apply] using! h
    ext i j
    simp [hG', Matrix.conjTranspose_apply, Matrix.smul_apply, hc, Complex.conj_ofReal, hGadj']
  have hz' : ∀ x y, f x = f y → Γ' x y = 0 := by
    intro x y hxy
    simp [hG', Matrix.smul_apply, hc]
    rw [hz x y hxy]
    simp
  have hfilter : ∀ j, ‖genFilterDelta input j ⊙ Γ'‖ ≤ 1 := by
    intro j
    have hhad : genFilterDelta input j ⊙ Γ' = c • (genFilterDelta input j ⊙ Γ) := by
      ext x y
      simp [hG', Matrix.smul_apply, Matrix.hadamard_apply]
      ring
    rw [hhad, l2_opNorm_def, map_smul, norm_smul]
    rw [hc, show ‖((1 / m : ℝ) : ℂ)‖ = |1 / m| from RCLike.norm_ofReal (1 / m : ℝ),
      abs_of_pos (by positivity : (0 : ℝ) < 1 / m), ← l2_opNorm_def]
    have hle : ‖genFilterDelta input j ⊙ Γ‖ ≤ m := by
      rw [← genAdvFilter_eq_genFilterDelta input Γ j]
      exact Qatlib.Concepts.AdversaryBounds.AdvDuality.genAdvFilter_le_maxFilterNorm input Γ j
    have hmul : (1 / m : ℝ) * ‖genFilterDelta input j ⊙ Γ‖ ≤ (1 / m : ℝ) * m :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    calc (1 / m : ℝ) * ‖genFilterDelta input j ⊙ Γ‖ ≤ (1 / m : ℝ) * m := hmul
      _ = 1 := by field_simp
  refine le_iSup_of_le ⟨Γ', hG'herm, hz', hfilter⟩ ?_
  rw [hnorm]

theorem gen_cutWitness_certified_coordinate
    {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    {A : Type} [DecidableEq A] (input : X → κ → A) (β : κ → ℝ≥0∞) (x y : X) (j : κ)
    (hsep : input x j ≠ input y j) :
    β j ≤ β j * ENNReal.ofReal ‖cutWitness x y‖
      / ENNReal.ofReal ‖genAdvFilter input (cutWitness x y) j‖ := by
  have hxy : x ≠ y := fun h => hsep (h ▸ rfl)
  have hnorm : 1 ≤ ‖cutWitness x y‖ := cutWitness_norm_ge_one x y hxy
  have hfilter : ‖genAdvFilter input (cutWitness x y) j‖ ≤ ‖cutWitness x y‖ :=
    genAdvFilter_cutWitness_le input x y j
  have hA : 1 ≤ ENNReal.ofReal ‖cutWitness x y‖ := by
    simpa using! (ENNReal.ofReal_le_ofReal hnorm)
  have hApos : 0 < ENNReal.ofReal ‖cutWitness x y‖ := ENNReal.ofReal_pos.mpr (by
    have : (0 : ℝ) < ‖cutWitness x y‖ := lt_of_lt_of_le (by norm_num) hnorm
    exact this)
  have hB : ENNReal.ofReal ‖genAdvFilter input (cutWitness x y) j‖
      ≤ ENNReal.ofReal ‖cutWitness x y‖ := ENNReal.ofReal_le_ofReal hfilter
  have hfilterj : genAdvFilter input (cutWitness x y) j = cutWitness x y :=
    genAdvFilter_cutWitness input x y j hsep
  have hBpos : 0 < ENNReal.ofReal ‖genAdvFilter input (cutWitness x y) j‖ := by
    rw [hfilterj]
    exact ENNReal.ofReal_pos.mpr (by
      have : (0 : ℝ) < ‖cutWitness x y‖ := lt_of_lt_of_le (by norm_num) hnorm
      exact this)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hBpos))
    (Or.inl ENNReal.ofReal_ne_top)).2
  exact mul_le_mul_of_nonneg_left hB (bot_le)

def Clause16BaseContent : Prop := Qatlib.Concepts.AdversaryBounds.AdvDuality.clause16Prop

def Clause16CoreContent {m D : ℕ} (C : Qatlib.Concepts.SignedWeights.Representations.LossCompletion m D) : Prop :=
  (∑ o, (C.completed o)ᴴ * C.completed o = 1) ∧
    (∀ rho : Operator D, C.totalMass rho = (Matrix.trace rho).re) ∧
    (∀ rho : Operator D, C.genuineMass rho + C.lossMass rho = (Matrix.trace rho).re) ∧
    (∀ rho : Operator D, C.lossMass rho = (Matrix.trace (C.defect * rho)).re) ∧
    (∀ A : Operator D,
      (∑ i, ((C.kraus i)ᴴ * (C.kraus i)) * A) + ((C.lossKraus)ᴴ * (C.lossKraus)) * A = A)

def Clause20BaseContent {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
    {n : ℕ} (input : X → Fin n → Bool) (f : X → E) : Prop :=
  generalAdversaryValue input f ≤
    filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input) ∧
    (∀ (Γ : Matrix X X ℂ), Γ.IsHermitian → (∀ x y, f x = f y → Γ x y = 0) →
      (∀ j, ‖gramFilterDelta input j ⊙ Γ‖ ≤ 1) →
      ENNReal.ofReal ‖Γ‖ ≤ filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input))

def Clause20CoreContent {X : Type} [Fintype X] [DecidableEq X] {n : ℕ} {A : Type}
    [DecidableEq A] (input : X → Fin n → A) (delta : ℝ) (rho sigma : Matrix X X ℂ)
    (_hdelta : 0 ≤ delta) (_hsigma : sigma.PosSemidef) : Prop :=
  (stateConversionSDPGeneral input delta rho sigma ≤ crossFilteredGamma2 input (rho - sigma)) ∧
    (∀ j, ConstantCoordinate input j → genFilterDelta input j = 0) ∧
    (∀ diff, ZeroFilterInstance input → (∃ x y, diff x y ≠ 0) →
      crossFilteredGamma2 input diff = ⊤)

def Clause21BaseContent {H E : Type} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]
    (label : H → E) : Prop :=
  IsPovm (labelPovm label) ∧
    (∀ (y y' : E), y ≠ y' → labelPovm label y * labelPovm label y' = 0)

def Clause21CoreContent {d : ℕ} (O : Operator d) (_hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (P : Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuit d)
    (_hP : Qatlib.Concepts.Execution.CircuitCompile.instrumentCircuitWellFormed P) (rho : Operator d)
    (_hrho : rho.PosSemidef) (K : ℕ) : Prop :=
  (∀ t ∈ Qatlib.Concepts.Execution.CircuitCompile.instrumentCircuitMixedTraces O (truncateInstrumentQueries P K) rho,
      t.queries ≤ K) ∧
    (instrumentTotalMass O (truncateInstrumentQueries P K) rho =
      (Matrix.trace rho).re) ∧
    (acceptedMass O P rho K + neverMass O P rho K
      = instrumentTotalMass O (truncateInstrumentQueries P K) rho) ∧
    (neverQueryCost O P rho K
      ≤ Qatlib.Concepts.Execution.CircuitCompile.instrumentCircuitExpectedQueries O (truncateInstrumentQueries P K) rho) ∧
    (neverQueryCost O P rho K ≤ (K : ℝ) * neverMass O P rho K)

def Clause18CoreContent {X : Type} [Fintype X] [DecidableEq X] {κ : Type} [Fintype κ]
    [DecidableEq κ] {A : Type} [DecidableEq A] (input : X → κ → A) (beta : κ → ℝ≥0∞)
    (x y : X) : Prop :=
  (∀ j, input x j ≠ input y j → certifiedCutCostE input beta x y ≤ beta j) ∧
    (∀ j, input x j ≠ input y j → beta j ≠ ⊤ → certifiedCutCostE input beta x y ≠ ⊤) ∧
    ((∃ j, input x j ≠ input y j) →
      (∀ j ∈ separatingCoords input x y, beta j = ⊤) →
        certifiedCutCostE input beta x y = ⊤ ∧ certifiedCutCost input beta x y = 0)

theorem truncatedQueryLedger_eq_haltJoint_of_le {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (fuel : ℕ) (o : O) (k : ℕ) (hk : k ≤ fuel) :
    truncatedQueryLedger next cfg fuel (o, k) = haltJoint next cfg o k := by
  simp only [truncatedQueryLedger]
  exact haltJoint_eq_runFor_of_le hk

theorem truncatedLedger_add_discardedMass_eq_one {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (fuel : ℕ) :
    (∑ o : O, ∑' k : ℕ, truncatedQueryLedger next cfg fuel (o, k))
      + discardedMass next cfg fuel = 1 := by
  have htsum : ∀ o : O, (∑' k : ℕ, truncatedQueryLedger next cfg fuel (o, k))
      = ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k := by
    intro o
    refine (tsum_eq_sum (L := SummationFilter.unconditional ℕ)
      (s := Finset.range (fuel + 1))
      (f := fun k => truncatedQueryLedger next cfg fuel (o, k)) ?_).trans ?_
    · intro k hk
      refine runFor_point_cost_gt_fuel next fuel cfg (Sum.inl o) k ?_
      have hj1 : ¬ (k < fuel + 1) := Finset.mem_range.not.mp hk
      omega
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ fuel := by
        have h := Finset.mem_range.mp hk
        omega
      exact truncatedQueryLedger_eq_haltJoint_of_le next cfg fuel o k hk'
  have hsum : (∑ o : O, ∑' k : ℕ, truncatedQueryLedger next cfg fuel (o, k))
      = ∑ o : O, ∑ k ∈ Finset.range (fuel + 1), haltJoint next cfg o k :=
    Finset.sum_congr rfl fun o _ => htsum o
  rw [hsum, discardedMass]
  exact (unbounded_finite_halt_pending_partition next cfg fuel).2.1

theorem truncatedQueryCount_le_unboundedQueryCount {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (fuel : ℕ) :
    truncatedQueryCount next cfg fuel ≤ unboundedQueryCount next cfg := by
  have htail : truncatedQueryCount next cfg fuel
      = ∑ k ∈ Finset.range fuel, pendingMass next cfg k := by
    rw [truncatedQueryCount, finite_stopping_cost_tail_sum]
    exact Finset.sum_congr rfl fun k _ => (pendingMass_eq_finiteSurvival next cfg k).symm
  rw [htail, unboundedQueryCount]
  exact ENNReal.sum_le_tsum (Finset.range fuel)

theorem unboundedQueryCount_eq_top_of_nontermination {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (h : 0 < nonterminationMass next cfg) :
    unboundedQueryCount next cfg = ⊤ := by
  have hsum : (∑' k : ℕ, nonterminationMass next cfg) ≤ unboundedQueryCount next cfg := by
    refine ENNReal.tsum_le_tsum fun k => ?_
    exact iInf_le (fun fuel => pendingMass next cfg fuel) k
  rw [unboundedQueryCount] at hsum
  have htop : (∑' k : ℕ, nonterminationMass next cfg) = ⊤ := by
    by_cases hc : nonterminationMass next cfg = ⊤
    · rw [hc, ENNReal.tsum_top]
    · rw [ENNReal.tsum_const_eq_top_of_ne_zero (c := nonterminationMass next cfg)
        (ne_of_gt h)]
  rw [htop] at hsum
  exact le_antisymm le_top hsum

theorem discardedMass_ge_nonterminationMass {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (fuel : ℕ) :
    nonterminationMass next cfg ≤ discardedMass next cfg fuel := by
  show nonterminationMass next cfg ≤ pendingMass next cfg fuel
  exact iInf_le (fun f => pendingMass next cfg f) fuel

theorem tail_truncation_charge {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (tol : ℝ≥0∞) (ε : ℝ≥0∞)
    (hε : 0 < ε) (htol : nonterminationMass next cfg ≤ tol) :
    ∃ fuel : ℕ, discardedMass next cfg fuel ≤ tol + ε := by
  by_cases htol_top : tol = ⊤
  · refine ⟨0, ?_⟩
    show pendingMass next cfg 0 ≤ tol + ε
    have htop : tol + ε = (⊤ : ℝ≥0∞) := by simp [htol_top]
    rw [htop]
    exact le_top
  by_cases hε_top : ε = ⊤
  · refine ⟨0, ?_⟩
    show pendingMass next cfg 0 ≤ tol + ε
    have htop : tol + ε = (⊤ : ℝ≥0∞) := by simp [hε_top]
    rw [htop]
    exact le_top
  have htol_lt : tol < ⊤ := lt_top_iff_ne_top.mpr htol_top
  have hsum_gt : tol < tol + ε := by
    have h := ENNReal.add_lt_add_left (a := tol) (b := 0) (c := ε) htol_top hε
    simpa using! h
  by_contra hcon
  have hcon' : ∀ fuel : ℕ, tol + ε < discardedMass next cfg fuel := by
    intro fuel
    by_contra h
    exact hcon ⟨fuel, le_of_not_gt h⟩
  have hle : tol + ε ≤ ⨅ fuel : ℕ, pendingMass next cfg fuel := by
    refine le_ciInf fun fuel => ?_
    exact le_of_lt (hcon' fuel)
  rw [show (⨅ fuel : ℕ, pendingMass next cfg fuel) = nonterminationMass next cfg from rfl] at hle
  exact absurd (lt_of_le_of_lt (hle.trans htol) hsum_gt) (lt_irrefl _)

theorem zeno_unit_charge_impossible {S : Type} (step : S → CostedLaw S) (s : ℕ → S)
    (hunit : ∀ k : ℕ, (1 : ℝ≥0∞) ≤ CostedLaw.expectedCost (step (s k))) :
    ¬ Qatlib.Concepts.ConversionCore.WitnessCompile.ZenoRun step s := by
  intro hz
  have htop : (⊤ : ℝ≥0∞) ≤ ∑' k : ℕ, CostedLaw.expectedCost (step (s k)) := by
    have h1 : (∑' k : ℕ, (1 : ℝ≥0∞)) ≤ ∑' k : ℕ, CostedLaw.expectedCost (step (s k)) := by
      refine ENNReal.tsum_le_tsum fun k => hunit k
    rw [ENNReal.tsum_const_eq_top_of_ne_zero (c := 1) (by norm_num)] at h1
    exact h1
  exact (not_lt_of_ge htop) hz.2

theorem truncated_run_bounded_by_fuel {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (fuel : ℕ) :
    CostedLaw.BoundedBy (RandomizedExecution.runFor next fuel cfg) fuel :=
  RandomizedExecution.runFor_bounded next fuel cfg

theorem truncated_vs_original_query_ledger {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (fuel : ℕ) :
    (∀ o k, k ≤ fuel → truncatedQueryLedger next cfg fuel (o, k) = haltJoint next cfg o k) ∧
    (∑ o : O, ∑' k : ℕ, truncatedQueryLedger next cfg fuel (o, k))
      + discardedMass next cfg fuel = 1 ∧
    truncatedQueryCount next cfg fuel ≤ unboundedQueryCount next cfg ∧
    nonterminationMass next cfg ≤ discardedMass next cfg fuel ∧
    CostedLaw.BoundedBy (RandomizedExecution.runFor next fuel cfg) fuel := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro o k hk
    exact truncatedQueryLedger_eq_haltJoint_of_le next cfg fuel o k hk
  · exact truncatedLedger_add_discardedMass_eq_one next cfg fuel
  · exact truncatedQueryCount_le_unboundedQueryCount next cfg fuel
  · exact discardedMass_ge_nonterminationMass next cfg fuel
  · exact truncated_run_bounded_by_fuel next cfg fuel

theorem interrogationResources_polyBounded {n a : ℕ} [NeZero a] :
    Qatlib.Concepts.ConversionCore.WitnessCompile.AdversaryResources.PolyBounded
      (interrogationResources (n := n) (a := a)) := by
  have hbits : 1 ≤ alphabetSymbolBits a := by
    unfold alphabetSymbolBits
    omega
  have hn : n ≤ n * alphabetSymbolBits a := by
    simpa using! (Nat.mul_le_mul_left n hbits)
  refine ⟨3, 1, ?_, ?_⟩
  · show (3 * n : ℕ) ≤ 3 * (n * alphabetSymbolBits a + 1) ^ 1
    rw [Nat.pow_one]
    have h2 : n ≤ n * alphabetSymbolBits a + 1 := le_trans hn (Nat.le_succ _)
    omega
  · show (n * alphabetSymbolBits a : ℕ) ≤ 3 * (n * alphabetSymbolBits a + 1) ^ 1
    rw [Nat.pow_one]
    omega

theorem interrogation_actual_program_resources {n a : ℕ} [NeZero a] (hn : 0 < n) :
    ∃ (C : Circuit ((Fin n × ZMod a) × (Fin n → ZMod a))),
      IsUnitaryCircuit C ∧ QueryCount C = n ∧ GateCount C = 3 * n ∧
      (interrogationResources (n := n) (a := a)).gates = GateCount C := by
  let j : Fin n := ⟨0, hn⟩
  let is : List (Fin n) := (Finset.univ : Finset (Fin n)).toList
  have hlen : is.length = n := by
    simp [is, Finset.length_toList, Finset.card_univ, Fintype.card_fin]
  obtain ⟨hC, hq, hg⟩ := alphabetInterrogationList_resources (a := a) j is
  refine ⟨alphabetInterrogationList (a := a) j is, hC, ?_, ?_, ?_⟩
  · rw [hq, hlen]
  · rw [hg, hlen]
  · show (3 * n : ℕ) = GateCount (alphabetInterrogationList (a := a) j is)
    rw [hg, hlen]

theorem adaptiveAlphabetExecution_correct {n D a : ℕ} (hn : 0 < n) (hD : 0 < D)
    (ha : 0 < a) :
    Qatlib.Concepts.ConversionCore.WitnessCompile.AlphabetAdaptive.Correct
      (adaptiveAlphabetExecution (n := n) (D := D) (a := a) (hn := hn)) :=
  ⟨ha, hn, hD⟩

theorem adaptive_round_instrument_is_projective {n D a : ℕ} (hn : 0 < n) (i : Fin n) :
    ((adaptiveAlphabetExecution (n := n) (D := D) (a := a) (hn := hn)).round i).inst
      = projectiveInstrument := rfl

theorem adaptive_execution_rounds_eq_interrogation_queries {n a : ℕ} [NeZero a]
    (hn : 0 < n) :
    ∃ (C : Circuit ((Fin n × ZMod a) × (Fin n → ZMod a))),
      QueryCount C = n ∧
        (adaptiveAlphabetExecution (n := n) (D := n) (a := a) (hn := hn)).rounds = n := by
  obtain ⟨C, _hC, hq, _hg, _hres⟩ := interrogation_actual_program_resources (a := a) hn
  exact ⟨C, hq, rfl⟩

theorem adaptiveCoordinate_eq_self {n : ℕ} (hn : 0 < n) (o : Fin n) :
    adaptiveCoordinate (D := n) hn o = o := by
  apply Fin.ext
  simp [adaptiveCoordinate, Nat.mod_eq_of_lt o.isLt]

theorem adaptiveCoordinate_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (adaptiveCoordinate (D := n) hn) := by
  intro a b hab
  have h1 : adaptiveCoordinate (D := n) hn a = a := adaptiveCoordinate_eq_self hn a
  have h2 : adaptiveCoordinate (D := n) hn b = b := adaptiveCoordinate_eq_self hn b
  rw [h1, h2] at hab
  exact hab

theorem adaptiveInstrumentRound_outcome_mass {n D : ℕ} (hn : 0 < n) (c : Fin D) :
    instrumentProb (adaptiveInstrumentRound (D := D) hn).inst
        (outerProduct (Qatlib.Foundations.PureStateMath.Ket c)) c = 1 ∧
      (∀ c' : Fin D, c' ≠ c →
        instrumentProb (adaptiveInstrumentRound (D := D) hn).inst
          (outerProduct (Qatlib.Foundations.PureStateMath.Ket c)) c' = 0) := by
  have h1 : instrumentProb projectiveInstrument
      (outerProduct (Qatlib.Foundations.PureStateMath.Ket c)) c = 1 := by
    rw [instrumentProb_projective_pure]
    simp [Qatlib.Foundations.PureStateMath.Ket, BornProb]
  have h2 : ∀ c' : Fin D, c' ≠ c →
      instrumentProb projectiveInstrument (outerProduct (Qatlib.Foundations.PureStateMath.Ket c)) c' = 0 := by
    intro c' hc'
    rw [instrumentProb_projective_pure]
    simp [Qatlib.Foundations.PureStateMath.Ket, BornProb, hc']
  exact ⟨h1, h2⟩

private theorem runFor_succ_cost {S O : Type} (next : S → PMF (Configuration S O))
    (cfg c d : Configuration S O) (j m : ℕ)
    (htick : RandomizedExecution.tick next cfg = PMF.pure (c, 1))
    (hrun : RandomizedExecution.runFor next j c = PMF.pure (d, m)) :
    RandomizedExecution.runFor next (j + 1) cfg = PMF.pure (d, m + 1) := by
  rw [show RandomizedExecution.runFor next (j + 1) cfg
      = CostedLaw.bind (RandomizedExecution.tick next cfg) (RandomizedExecution.runFor next j) from rfl]
  rw [htick]
  show PMF.bind (PMF.pure (c, 1))
      (fun x => CostedLaw.charge x.2 (RandomizedExecution.runFor next j x.1))
      = PMF.pure (d, m + 1)
  rw [PMF.pure_bind, hrun]
  show CostedLaw.charge 1 (PMF.pure (d, m)) = PMF.pure (d, m + 1)
  rw [CostedLaw.charge, PMF.pure_map]
  have h : ((d, m).1, 1 + (d, m).2) = (d, m + 1) := by
    apply Prod.ext
    · rfl
    · show 1 + m = m + 1
      omega
  rw [h]

private theorem label_lt {D : ℕ} (c : Fin D) (j : ℕ) : c.val - j < D := by
  have h1 : c.val - j ≤ c.val := Nat.sub_le _ _
  exact lt_of_le_of_lt h1 c.isLt

private theorem adaptiveAdvance_at {D : ℕ} (c : Fin D) (hc : c.val ≠ 0) :
    adaptiveAdvance c = some (adaptiveLabelStep c) := by
  simp only [adaptiveAdvance, if_neg hc]

private theorem adaptive_tick_eq {D : ℕ} (c : Fin D) (hc : c.val ≠ 0) :
    RandomizedExecution.tick (adaptiveUnboundedNext (D := D)) (Sum.inr c)
      = PMF.pure (Sum.inr (adaptiveLabelStep c), 1) := by
  have hnext : adaptiveUnboundedNext (D := D) c
      = PMF.pure (Sum.inr (adaptiveLabelStep c)) := by
    simp only [adaptiveUnboundedNext, adaptiveAdvance_at c hc]
  show (adaptiveUnboundedNext (D := D) c).map (fun cfg => (cfg, 1))
      = PMF.pure (Sum.inr (adaptiveLabelStep c), 1)
  rw [hnext, PMF.pure_map]

private theorem adaptive_tick_halt {D : ℕ} (hD : 0 < D) (c : Fin D) (hc : c.val = 0) :
    RandomizedExecution.tick (adaptiveUnboundedNext (D := D)) (Sum.inr c)
      = PMF.pure (Sum.inl (⟨0, hD⟩ : Fin D), 1) := by
  have hnext : adaptiveUnboundedNext (D := D) c
      = PMF.pure (Sum.inl (⟨0, hD⟩ : Fin D)) := by
    simp only [adaptiveUnboundedNext, adaptiveAdvance, if_pos hc]
    apply congrArg (fun x => PMF.pure (Sum.inl x))
    apply Fin.ext
    simp [hc]
  show (adaptiveUnboundedNext (D := D) c).map (fun cfg => (cfg, 1))
      = PMF.pure (Sum.inl (⟨0, hD⟩), 1)
  rw [hnext, PMF.pure_map]

private theorem adaptive_runFor_aux {D : ℕ} (hD : 0 < D) :
    ∀ j : ℕ, ∀ c : Fin D, c.val ≤ D →
      (j ≤ c.val →
        RandomizedExecution.runFor (adaptiveUnboundedNext (D := D)) j (Sum.inr c)
          = PMF.pure (Sum.inr ⟨c.val - j, label_lt c j⟩, j)) ∧
      (c.val < j →
        RandomizedExecution.runFor (adaptiveUnboundedNext (D := D)) j (Sum.inr c)
          = PMF.pure (Sum.inl (⟨0, hD⟩), c.val + 1)) := by
  intro j
  induction j with
  | zero =>
      intro c _
      refine ⟨?_, ?_⟩
      · intro hrun
        show RandomizedExecution.runFor (adaptiveUnboundedNext (D := D)) 0 (Sum.inr c)
          = PMF.pure (Sum.inr ⟨c.val - 0, label_lt c 0⟩, 0)
        simp [RandomizedExecution.runFor, CostedLaw.ret]
      · intro hrun
        omega
  | succ j ih =>
      intro c hcD
      have hsub1 : c.val - 1 ≤ c.val := Nat.sub_le _ _
      by_cases hrun : j + 1 ≤ c.val
      · refine ⟨?_, ?_⟩
        · intro _
          have hpos : 1 ≤ c.val := by omega
          have hrel : c.val = (c.val - 1) + 1 := (Nat.sub_add_cancel hpos).symm
          have hleD : c.val - 1 ≤ D := le_trans hsub1 hcD
          have hlej : j ≤ c.val - 1 := by omega
          have htick := adaptive_tick_eq c (by omega)
          have hrun2 := (ih ⟨c.val - 1, label_lt c 1⟩ hleD).1 hlej
          have hres := runFor_succ_cost (adaptiveUnboundedNext (D := D))
            (Sum.inr c) (Sum.inr ⟨c.val - 1, label_lt c 1⟩)
            (Sum.inr ⟨c.val - 1 - j, label_lt ⟨c.val - 1, label_lt c 1⟩ j⟩) j j htick hrun2
          rw [hres]
          apply congrArg PMF.pure
          apply Prod.ext
          · apply congrArg Sum.inr
            apply Fin.ext
            simp [Nat.sub_sub, Nat.add_comm 1 j]
          · rfl
        · intro hhalt
          by_cases h0 : c.val = 0
          · have htick := adaptive_tick_halt hD c h0
            have hhalt' : RandomizedExecution.runFor (adaptiveUnboundedNext (D := D))
                j (Sum.inl (⟨0, hD⟩ : Fin D)) = PMF.pure (Sum.inl (⟨0, hD⟩), 0) := by
              rw [RandomizedExecution.runFor_halted]
              rfl
            have hres := runFor_succ_cost (adaptiveUnboundedNext (D := D))
              (Sum.inr c) (Sum.inl (⟨0, hD⟩ : Fin D)) (Sum.inl (⟨0, hD⟩)) j 0 htick hhalt'
            rw [hres]
            apply congrArg PMF.pure
            apply Prod.ext
            · rfl
            · omega
          · have hpos : 1 ≤ c.val := by omega
            have hrel : c.val = (c.val - 1) + 1 := (Nat.sub_add_cancel hpos).symm
            have hleD : c.val - 1 ≤ D := le_trans hsub1 hcD
            have hltj : c.val - 1 < j := by omega
            have htick := adaptive_tick_eq c (by omega)
            have hhalt2 := (ih ⟨c.val - 1, label_lt c 1⟩ hleD).2 hltj
            have hres := runFor_succ_cost (adaptiveUnboundedNext (D := D))
              (Sum.inr c) (Sum.inr ⟨c.val - 1, label_lt c 1⟩)
              (Sum.inl (⟨0, hD⟩)) j (c.val - 1 + 1) htick hhalt2
            have hcost : (c.val - 1 + 1) + 1 = c.val + 1 := by
              rw [Nat.sub_add_cancel hpos]
            rw [hres, hcost]
      · refine ⟨?_, ?_⟩
        · intro hrun
          omega
        · intro hhalt
          by_cases h0 : c.val = 0
          · have htick := adaptive_tick_halt hD c h0
            have hhalt' : RandomizedExecution.runFor (adaptiveUnboundedNext (D := D))
                j (Sum.inl (⟨0, hD⟩ : Fin D)) = PMF.pure (Sum.inl (⟨0, hD⟩), 0) := by
              rw [RandomizedExecution.runFor_halted]
              rfl
            have hres := runFor_succ_cost (adaptiveUnboundedNext (D := D))
              (Sum.inr c) (Sum.inl (⟨0, hD⟩ : Fin D)) (Sum.inl (⟨0, hD⟩)) j 0 htick hhalt'
            rw [hres]
            apply congrArg PMF.pure
            apply Prod.ext
            · rfl
            · omega
          · have hpos : 1 ≤ c.val := by omega
            have hrel : c.val = (c.val - 1) + 1 := (Nat.sub_add_cancel hpos).symm
            have hleD : c.val - 1 ≤ D := le_trans hsub1 hcD
            have hltj : c.val - 1 < j := by omega
            have htick := adaptive_tick_eq c (by omega)
            have hhalt2 := (ih ⟨c.val - 1, label_lt c 1⟩ hleD).2 hltj
            have hres := runFor_succ_cost (adaptiveUnboundedNext (D := D))
              (Sum.inr c) (Sum.inr ⟨c.val - 1, label_lt c 1⟩)
              (Sum.inl (⟨0, hD⟩)) j (c.val - 1 + 1) htick hhalt2
            have hcost : (c.val - 1 + 1) + 1 = c.val + 1 := by
              rw [Nat.sub_add_cancel hpos]
            rw [hres, hcost]

theorem adaptive_runFor_running {D : ℕ} (hD : 0 < D) (c : Fin D) {j : ℕ} (hj : j ≤ c.val) :
    RandomizedExecution.runFor (adaptiveUnboundedNext (D := D)) j (Sum.inr c)
      = PMF.pure (Sum.inr ⟨c.val - j, label_lt c j⟩, j) :=
  (adaptive_runFor_aux hD j c (by omega)).1 hj

theorem adaptive_ledger {D : ℕ} (hD : 0 < D) (c₀ : Fin D) :
    RandomizedExecution.runFor (adaptiveUnboundedNext (D := D))
        (adaptiveHaltingCost c₀) (Sum.inr c₀)
      = PMF.pure (Sum.inl (⟨0, hD⟩), adaptiveHaltingCost c₀) := by
  have hcost : adaptiveHaltingCost c₀ = c₀.val + 1 := rfl
  have h1 := (adaptive_runFor_aux hD (c₀.val + 1) c₀ (by omega)).2 (by omega)
  rw [hcost]
  have h2 : c₀.val + 1 = c₀.val + 1 := rfl
  rw [h2] at h1
  simpa using! h1

theorem adaptive_ledger_rounds_le {n D : ℕ} (c₀ : Fin D)
    (hk : c₀.val + 1 ≤ n) : adaptiveHaltingCost c₀ ≤ n := by
  simp only [adaptiveHaltingCost]
  omega

theorem adaptive_haltJoint {D : ℕ} (hD : 0 < D) (c₀ : Fin D) :
    haltJoint (adaptiveUnboundedNext (D := D)) (Sum.inr c₀)
      (⟨0, hD⟩) (adaptiveHaltingCost c₀) = 1 := by
  rw [← haltJoint_eq_runFor_of_le (k := adaptiveHaltingCost c₀)
    (fuel := adaptiveHaltingCost c₀) (le_refl _)]
  rw [adaptive_ledger hD c₀, PMF.pure_apply]
  norm_num

theorem adaptive_pendingMass_zero {D : ℕ} (hD : 0 < D) (c₀ : Fin D) :
    pendingMass (adaptiveUnboundedNext (D := D)) (Sum.inr c₀)
      (adaptiveHaltingCost c₀) = 0 := by
  have hrun : RandomizedExecution.runFor (adaptiveUnboundedNext (D := D))
      (adaptiveHaltingCost c₀) (Sum.inr c₀)
      = PMF.pure (Sum.inl (⟨0, hD⟩), adaptiveHaltingCost c₀) :=
    adaptive_ledger hD c₀
  simp only [pendingMass, hrun, PMF.pure_apply]
  apply Finset.sum_eq_zero
  intro s hs
  apply Finset.sum_eq_zero
  intro k hk
  simp

theorem adaptive_nonterminationMass {D : ℕ} (hD : 0 < D) (c₀ : Fin D) :
    nonterminationMass (adaptiveUnboundedNext (D := D)) (Sum.inr c₀) = 0 := by
  rw [nonterminationMass]
  refine le_antisymm ?_ bot_le
  exact (ciInf_le' (fun fuel => pendingMass (adaptiveUnboundedNext (D := D))
    (Sum.inr c₀) fuel) (adaptiveHaltingCost c₀)).trans
    (by rw [adaptive_pendingMass_zero hD c₀])

theorem adaptive_alphabet_execution_contract {n D a : ℕ} (hn : 0 < n) (hD : 0 < D)
    (ha : 0 < a) :
    Qatlib.Concepts.ConversionCore.WitnessCompile.AlphabetAdaptive.Correct
        (adaptiveAlphabetExecution (n := n) (D := D) (a := a) (hn := hn)) ∧
      (∀ (i : Fin n),
        ((adaptiveAlphabetExecution (n := n) (D := D) (a := a) (hn := hn)).round i).inst
          = projectiveInstrument) ∧
      (∀ (c₀ : Fin D) (_hk : c₀.val + 1 ≤ n),
        haltJoint (adaptiveUnboundedNext (D := D)) (Sum.inr c₀)
          (⟨0, hD⟩) (adaptiveHaltingCost c₀) = 1 ∧
        nonterminationMass (adaptiveUnboundedNext (D := D)) (Sum.inr c₀) = 0 ∧
        c₀.val + 1 ≤ n ∧
        adaptiveHaltingCost c₀ ≤ n) := by
  refine ⟨adaptiveAlphabetExecution_correct hn hD ha, ?_, ?_⟩
  · intro i
    exact adaptive_round_instrument_is_projective hn i
  · intro c₀ _hk
    refine ⟨adaptive_haltJoint hD c₀, adaptive_nonterminationMass hD c₀, ?_, ?_⟩
    · exact _hk
    · exact adaptive_ledger_rounds_le c₀ _hk

theorem scan_halts_at_data {a : ℕ} {w : List (Option (Fin a))} (hw : DataWord w) :
    BitMachineHaltsAt (scanMachine (a := a)) w w.length := by
  refine ⟨⟨default, (Turing.Tape.move Turing.Dir.right)^[w.length] (Turing.Tape.mk₁ w)⟩, ?_, ?_⟩
  · exact scan_after_of_noBlank (by intro j hj; exact hw j hj)
  · rw [scan_step]
    have hhead : ((Turing.Tape.move Turing.Dir.right)^[w.length] (Turing.Tape.mk₁ w)).head
        = w.getI w.length := scan_head w w.length
    rw [hhead]
    have hnil : w.getI w.length = (none : Option (Fin a)) :=
      List.getI_eq_default (l := w) (by omega)
    rw [hnil]
    rfl

theorem scan_halts_at_most_length {a : ℕ} {w : List (Option (Fin a))} {t : ℕ}
    (h : BitMachineHaltsAt (scanMachine (a := a)) w t) : t ≤ w.length := by
  obtain ⟨t₀, ht₀, hh₀⟩ := scan_halts_at_some w
  obtain ⟨final, hrun, hstop⟩ := h
  by_cases hlt : t₀ < t
  · have hnone : BitMachineAfter (scanMachine (a := a)) w t = none :=
      bitMachineAfter_none_of_halts (t := t₀) (t' := t) hh₀ hlt
    rw [hnone] at hrun
    exact absurd hrun (by simp)
  · have hle : t ≤ t₀ := by omega
    exact hle.trans ht₀

theorem scan_halts_only_at_data {a : ℕ} {w : List (Option (Fin a))} (hw : DataWord w)
    {t : ℕ} (h : BitMachineHaltsAt (scanMachine (a := a)) w t) : t = w.length := by
  by_contra heq
  have hle : t ≤ w.length := scan_halts_at_most_length h
  have hlt : t < w.length := by omega
  obtain ⟨final, hrun, hstop⟩ := h
  have hcfg := scan_after_of_noBlank (a := a) (w := w) (t := t) (by
    intro j hj; exact hw j (by omega))
  rw [hcfg] at hrun
  have hfeq : final = ⟨default, (Turing.Tape.move Turing.Dir.right)^[t]
      (Turing.Tape.mk₁ w)⟩ := Option.some.inj hrun.symm
  rw [hfeq] at hstop
  rw [scan_step] at hstop
  have hhead : ((Turing.Tape.move Turing.Dir.right)^[t] (Turing.Tape.mk₁ w)).head
      = w.getI t := scan_head w t
  rw [hhead] at hstop
  have hne : w.getI t ≠ none := hw t hlt
  simp [hne] at hstop

theorem scan_halts_at_iff_data {a : ℕ} {w : List (Option (Fin a))} (hw : DataWord w) (t : ℕ) :
    BitMachineHaltsAt (scanMachine (a := a)) w t ↔ t = w.length := by
  constructor
  · exact scan_halts_only_at_data hw
  · intro heq
    rw [heq]
    exact scan_halts_at_data hw

theorem scanFamily_uniformPolyTime {a : ℕ} :
    (scanFamily (a := a)).UniformPolyTime := by
  refine ⟨1, 1, ?_⟩
  intro len input hlen
  obtain ⟨t, ht, hhalts⟩ := scan_halts_at_some input
  refine ⟨t, ?_, hhalts⟩
  simp only [Nat.one_mul, Nat.pow_one]
  omega

theorem scanFamily_uniformPolyTime_forces_linear {a : ℕ} (hA : 0 < a) {c k : ℕ}
    (h : ∀ (len : ℕ) (input : List (Option (Fin a))), input.length = len →
      ∃ t : ℕ, t ≤ c * len ^ k + c ∧
        BitMachineHaltsAt ((scanFamily (a := a)).machine len) input t) :
    ∀ len : ℕ, len ≤ c * len ^ k + c := by
  intro len
  have hlen : (List.replicate len (some (⟨0, hA⟩ : Fin a))).length = len := List.length_replicate
  obtain ⟨t, ht, hh⟩ := h len (List.replicate len (some (⟨0, hA⟩ : Fin a))) hlen
  have hw : DataWord (a := a) (List.replicate len (some (⟨0, hA⟩ : Fin a))) :=
    dataWord_replicate (by simp) len
  have hhalt : BitMachineHaltsAt (scanMachine (a := a))
      (List.replicate len (some (⟨0, hA⟩ : Fin a))) t := by
    rw [show (scanFamily (a := a)).machine len = scanMachine (a := a) from rfl] at hh
    exact hh
  have hex : t = len := by
    have h1 := scan_halts_only_at_data hw hhalt
    rw [List.length_replicate] at h1
    exact h1
  rw [hex] at ht
  exact ht

theorem degenerateMachine_halts_at_zero {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (w : List Γ) : BitMachineHaltsAt (degenerateMachine (Γ := Γ) (Λ := Λ)) w 0 := by
  refine ⟨Turing.TM0.init w, rfl, ?_⟩
  show Turing.TM0.step (fun _ _ => none) (Turing.TM0.init w) = none
  rfl

theorem degenerateMachine_halts_only_at_zero {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (w : List Γ) (t : ℕ) :
    BitMachineHaltsAt (degenerateMachine (Γ := Γ) (Λ := Λ)) w t ↔ t = 0 := by
  constructor
  · intro h
    by_contra heq
    have hlt : 0 < t := by omega
    obtain ⟨final, hrun, hstop⟩ := h
    have hnone : BitMachineAfter (degenerateMachine (Γ := Γ) (Λ := Λ)) w t = none :=
      bitMachineAfter_none_of_halts (degenerateMachine_halts_at_zero w) hlt
    rw [hnone] at hrun
    exact absurd hrun (by simp)
  · intro heq
    rw [heq]
    exact degenerateMachine_halts_at_zero w

theorem interrogation_native_halts_at_length {a : ℕ} {n : ℕ} (symbols : Fin n → Fin a) :
    BitMachineHaltsAt ((scanFamily (a := a)).machine n) (interrogationWord n symbols) n := by
  have hw := interrogationWord_isData n symbols
  have hlen := interrogationWord_length n symbols
  have hh : BitMachineHaltsAt (scanMachine (a := a)) (interrogationWord n symbols)
      (interrogationWord n symbols).length := scan_halts_at_data hw
  rw [show (scanFamily (a := a)).machine n = scanMachine (a := a) from rfl]
  rw [hlen] at hh
  exact hh

theorem interrogation_native_halts_only_at_length {a : ℕ} {n : ℕ} (symbols : Fin n → Fin a)
    {t : ℕ} (h : BitMachineHaltsAt ((scanFamily (a := a)).machine n)
      (interrogationWord n symbols) t) : t = n := by
  have hw := interrogationWord_isData n symbols
  have hlen := interrogationWord_length n symbols
  have hh : BitMachineHaltsAt (scanMachine (a := a)) (interrogationWord n symbols) t := by
    rw [show (scanFamily (a := a)).machine n = scanMachine (a := a) from rfl] at h
    exact h
  have h1 := scan_halts_only_at_data hw hh
  rw [hlen] at h1
  exact h1

theorem interrogation_native_queries_eq_program {n a : ℕ} [NeZero a] (hn : 0 < n)
    (symbols : Fin n → Fin a) :
    ∃ (C : Circuit ((Fin n × ZMod a) × (Fin n → ZMod a))),
      IsUnitaryCircuit C ∧ QueryCount C = n ∧ GateCount C = 3 * n ∧
      (interrogationResources (n := n) (a := a)).gates = GateCount C ∧
      BitMachineHaltsAt ((scanFamily (a := a)).machine n) (interrogationWord n symbols) n := by
  obtain ⟨C, hC, hq, hg, hr⟩ := interrogation_actual_program_resources (n := n) (a := a) hn
  refine ⟨C, hC, hq, hg, hr, ?_⟩
  exact interrogation_native_halts_at_length symbols

theorem nativeInputBits_eq_interrogation_inputLen {n a : ℕ} [NeZero a] :
    nativeInputBits (n := n) (a := a) = (interrogationResources (n := n) (a := a)).inputLen := rfl

theorem nativeInputBits_eq_interrogation_space {n a : ℕ} [NeZero a] :
    nativeInputBits (n := n) (a := a) = (interrogationResources (n := n) (a := a)).space := rfl

theorem clause16_base_content : Clause16BaseContent :=
  Qatlib.Concepts.AdversaryBounds.AdvDuality.stageA_general_adversary_clause16_full_endpoint_v2

theorem clause16_core_content {m D : ℕ}
    (C : Qatlib.Concepts.SignedWeights.Representations.LossCompletion m D) : Clause16CoreContent C :=
  Qatlib.Concepts.SignedWeights.Representations.LossCompletion.clause16_complete C

theorem clause20_base_content {X E : Type} [Fintype X] [DecidableEq X] [Fintype E]
    [DecidableEq E] {n : ℕ} (input : X → Fin n → Bool) (f : X → E) :
    Clause20BaseContent input f := by
  refine ⟨?_, ?_⟩
  · exact Qatlib.Concepts.AdversaryBounds.AdvDuality.stageA_general_adversary_clause20.1 input f
  · intro Γ hG hz hfilter
    exact Qatlib.Concepts.AdversaryBounds.AdvDuality.stageA_general_adversary_clause20.2 input f Γ hG hz hfilter

theorem clause20_core_content {X : Type} [Fintype X] [DecidableEq X] {n : ℕ} {A : Type}
    [DecidableEq A] (input : X → Fin n → A) (delta : ℝ) (rho sigma : Matrix X X ℂ)
    (hdelta : 0 ≤ delta) (hsigma : sigma.PosSemidef) : Clause20CoreContent input delta rho sigma
    hdelta hsigma :=
  Qatlib.Concepts.SignedWeights.Representations.clause20_complete input delta rho sigma hdelta hsigma

theorem clause21_base_content {H E : Type} [Fintype H] [DecidableEq H] [Fintype E]
    [DecidableEq E] (label : H → E) : Clause21BaseContent label := by
  refine ⟨?_, ?_⟩
  · exact Qatlib.Concepts.AdversaryBounds.AdvDuality.stageA_general_adversary_clause21.1 label
  · intro y y' hne
    exact Qatlib.Concepts.AdversaryBounds.AdvDuality.stageA_general_adversary_clause21.2.1 label y y' hne

theorem clause21_core_content {d : ℕ} (O : Operator d) (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (P : Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuit d)
    (hP : Qatlib.Concepts.Execution.CircuitCompile.instrumentCircuitWellFormed P) (rho : Operator d)
    (hrho : rho.PosSemidef) (K : ℕ) : Clause21CoreContent O hO P hP rho hrho K :=
  Qatlib.Concepts.SignedWeights.Representations.clause21_complete O hO P hP rho hrho K

theorem clause18_core_content {X : Type} [Fintype X] [DecidableEq X] {κ : Type} [Fintype κ]
    [DecidableEq κ] {A : Type} [DecidableEq A] (input : X → κ → A) (beta : κ → ℝ≥0∞)
    (x y : X) : Clause18CoreContent input beta x y :=
  Qatlib.Concepts.SignedWeights.Representations.clause18_complete input beta x y

theorem sourceAlphabetDelta_eq_genFilterDelta {X : Type} [DecidableEq X] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) :
    Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceAlphabetDelta input
      = genFilterDelta input := rfl

theorem sourceRectValue_eq_crossFilteredGamma2 {X : Type} [Fintype X] [DecidableEq X]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (A : Matrix X X ℂ) :
    Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceRectValue A
        (Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceAlphabetDelta input)
      = crossFilteredGamma2 input A := by
  rw [Qatlib.Concepts.GramQueryCore.ModelSemantics.sourceSquareValue_eq A
    (Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceAlphabetDelta input)]
  rw [sourceAlphabetDelta_eq_genFilterDelta input]
  rfl

theorem general_alphabet_sdp_le_sourceRectValue {X : Type} [Fintype X] [DecidableEq X]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (delta : ℝ) (rho sigma : Matrix X X ℂ)
    (hdelta : 0 ≤ delta) (hsigma : sigma.PosSemidef) :
    stateConversionSDPGeneral input delta rho sigma
      ≤ Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceRectValue (rho - sigma)
          (Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceAlphabetDelta input) := by
  refine (stateConversionSDPGeneral_le_crossFilteredGamma2 input delta rho sigma
    hdelta hsigma).trans ?_
  rw [sourceRectValue_eq_crossFilteredGamma2]

theorem general_alphabet_conversion_program {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (W ε : ℝ)
    (hn : ∀ x, Normalized (ρ x) ∧ Normalized (σ x)) (hW : 0 ≤ W)
    (hvalue : gramCrossFilteredGamma2 input ρ σ ≤ ENNReal.ofReal W)
    (hε : 0 < ε) (hε1 : ε ≤ 1/3) :
    AlphabetConversionProgram n q input ρ σ W ε := by
  obtain ⟨c, hc, hconv⟩ :=
    Qatlib.Concepts.QueryComplexity.StateConversion.realBudgetConversionAlgorithm
  have hvalue' : Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceRectValue
      (gramStateMatrix ρ - gramStateMatrix σ)
      (Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceAlphabetDelta input)
      ≤ ENNReal.ofReal W := by
    rw [sourceRectValue_eq_crossFilteredGamma2]
    simpa [gramCrossFilteredGamma2, crossFilteredGamma2] using! hvalue
  obtain ⟨r, hr, C, hC, hcalls, hdeg, hsucc, herr⟩ :=
    hconv X H n q input ρ σ W ε hn hW hvalue' hε hε1
  exact ⟨c, hc, ⟨r, hr, C, hC, hcalls, hdeg, hsucc, herr⟩⟩

theorem degenerate_no_conversion_program {X : Type} [Fintype X] [DecidableEq X]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (A : Matrix X X ℂ)
    (hz : ZeroFilterInstance input) (hne : ∃ x y, A x y ≠ 0) :
    crossFilteredGamma2 input A = ⊤ ∧
      ¬ ∃ W : ℝ, Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceRectValue A
          (Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceAlphabetDelta input)
            ≤ ENNReal.ofReal W := by
  have htop : crossFilteredGamma2 input A = ⊤ :=
    crossFilteredGamma2_top_of_zeroFilter input A hz hne
  constructor
  · exact htop
  · rintro ⟨W, hW⟩
    rw [sourceRectValue_eq_crossFilteredGamma2] at hW
    rw [htop] at hW
    simp at hW

theorem clause16_endpoint :
    Clause16BaseContent ∧
    (∀ {m D : ℕ} (C : Qatlib.Concepts.SignedWeights.Representations.LossCompletion m D),
      Clause16CoreContent C) ∧
    (∀ (X H Y : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
      [Fintype Y] [DecidableEq Y] (Γ : Matrix X X ℂ) (weight : QState X)
      (out : Y → Matrix H H ℂ) (states : X → QState H) (f : X → Y) (eps : ℝ),
      IsPovm out → Γ.IsHermitian → Normalized weight → (∀ x, Normalized (states x)) →
      (∀ x y, f x = f y → Γ x y = 0) → 0 ≤ eps → eps ≤ 1 / 2 →
      (∀ x, 1 - eps ≤ povmProb out (f x) (states x)) →
      |advProgress Γ weight (fun x => (povmLiftMatrix out : Matrix (Y × H) H ℂ) *ᵥ states x)|
        ≤ (2 * Real.sqrt (eps * (1 - eps)) + 2 * eps) * ‖Γ‖) ∧
    (∀ (X H Y : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
      [Fintype Y] [DecidableEq Y] (Γ : Matrix X X ℂ) (weight : QState X)
      (P : OrthogonalProjectors H Y) (states : X → QState H) (f : X → Y) (eps : ℝ),
      Γ.IsHermitian → Normalized weight → (∀ x, Normalized (states x)) →
      (∀ x y, f x = f y → Γ x y = 0) → 0 ≤ eps → eps ≤ 1 / 2 →
      (∀ x, 1 - eps ≤ povmProb (projectivePovm P) (f x) (states x)) →
      |advProgress Γ weight states| ≤ (2 * Real.sqrt (eps * (1 - eps)) + 2 * eps) * ‖Γ‖) := by
  refine ⟨clause16_base_content, ?_, ?_, ?_⟩
  · intro m D C
    exact clause16_core_content C
  · intro X H Y _ _ _ _ _ _ Γ weight out states f eps hout hG hw hs hz he0 he1 hsuccess
    exact general_povm_final_progress X H Y Γ weight out hout states f eps hG hw hs hz he0 he1
      hsuccess
  · intro X H Y _ _ _ _ _ _ Γ weight P states f eps hG hw hs hz he0 he1 hsuccess
    exact projective_final_progress_on_original_register X H Y Γ weight P states f eps hG hw hs
      hz he0 he1 hsuccess

theorem clause18_endpoint :
    (∀ {k : ℕ} {Y : Fin k → Type} {n : Fin k → ℕ} [∀ i, Fintype (Y i)]
      [∀ i, DecidableEq (Y i)] (gin : ∀ i, Y i → Fin (n i) → Bool) (g : ∀ i, Y i → Bool)
      (f : (Fin k → Bool) → Bool) (alpha : ((i : Fin k) × Fin (n i)) → ℝ),
      (∀ c, 0 < alpha c) → (∃ (u v : Fin k → Bool), f u ≠ f v) →
      (∀ i, ∃ (a b : Y i), g i a ≠ g i b) →
      (∀ i, blockCosts gin g alpha i < ⊤) →
      advAlphaENN (composedInput gin) (composedFunction g f) (fun c => ENNReal.ofReal (alpha c))
        ≤ advAlphaENN (fun u : Fin k → Bool => u) f (blockCosts gin g alpha)) ∧
    (∀ {X : Type} [Fintype X] [DecidableEq X] {κ : Type} [Fintype κ]
      [DecidableEq κ] {A : Type} [DecidableEq A] (input : X → κ → A) (beta : κ → ℝ≥0∞)
      (x y : X), Clause18CoreContent input beta x y) ∧
    (∀ {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ} [∀ i, Fintype (X i)]
      [∀ i, DecidableEq (X i)] (gin : ∀ i, X i → Fin (n i) → Bool) (g : ∀ i, X i → Bool)
      (α : ((i : Fin k) × Fin (n i)) → ℝ) (i : Fin k),
      blockCosts gin g α i = advAlphaENN (gin i) (g i) (fun j => ENNReal.ofReal (α ⟨i, j⟩))) ∧
    (∀ {X : Type} [Fintype X] [DecidableEq X] {κ : Type} [Fintype κ]
      [DecidableEq κ] {A : Type} [DecidableEq A] (input : X → κ → A) (β : κ → ℝ≥0∞)
      (x y : X) (j : κ), input x j ≠ input y j →
      β j ≤ β j * ENNReal.ofReal ‖cutWitness x y‖
        / ENNReal.ofReal ‖genAdvFilter input (cutWitness x y) j‖) ∧
    (∀ {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
      {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] (input : X → Fin n → A) (f : X → E)
      (x y : X), f x ≠ f y → 1 ≤ genAdversaryValue input f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k Y n _ _ gin g f alpha ha hfn hgn hfin
    exact composition_upper_bound_on_source_scope gin g f alpha ha hfn hgn hfin
  · intro X _ _ κ _ _ A _ input beta x y
    exact clause18_core_content input beta x y
  · intro k X n _ _ gin g alpha i
    exact blockCosts_eq_block_value gin g alpha i
  · intro X _ _ κ _ _ A _ input beta x y j hsep
    exact gen_cutWitness_certified_coordinate input beta x y j hsep
  · intro X E _ _ _ _ n A _ _ input f x y hgy
    exact gen_adversaryValue_ge_one_of_cross_output input f x y hgy

theorem clause20_endpoint :
    (∀ {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n : ℕ}
      (input : X → Fin n → Bool) (f : X → E), Clause20BaseContent input f) ∧
    (∀ {X : Type} [Fintype X] [DecidableEq X] {n : ℕ} {A : Type} [DecidableEq A]
      (input : X → Fin n → A) (delta : ℝ) (rho sigma : Matrix X X ℂ) (hdelta : 0 ≤ delta)
      (hsigma : sigma.PosSemidef), Clause20CoreContent input delta rho sigma hdelta hsigma) ∧
    (∀ {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
      (input : X → κ → Bool) (g : X → Bool) (α α' : κ → ℝ),
      (∀ i, 0 ≤ α i) → (∀ i, α i ≤ α' i) →
      advAlphaR input g α ≤ advAlphaR input g α') ∧
    (∀ {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n : ℕ}
      {A : Type} [Fintype A] [DecidableEq A] (input : X → Fin n → A) (f : X → E)
      (Γ : Matrix X X ℂ), Γ.IsHermitian → (∀ x y, f x = f y → Γ x y = 0) →
      0 < maxFilterNorm input Γ →
      ENNReal.ofReal (‖Γ‖ / maxFilterNorm input Γ) ≤ genAdversaryValue input f) ∧
    (∀ {X : Type} [Fintype X] [DecidableEq X] {n q : ℕ}
      (input : X → Fin n → Fin (q+1)) (delta : ℝ) (rho sigma : Matrix X X ℂ),
      0 ≤ delta → sigma.PosSemidef →
      stateConversionSDPGeneral input delta rho sigma
        ≤ Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceRectValue (rho - sigma)
            (Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceAlphabetDelta input)) ∧
    (∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H]
      {n q : ℕ} (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (W ε : ℝ),
      (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0 ≤ W →
      gramCrossFilteredGamma2 input ρ σ ≤ ENNReal.ofReal W → 0 < ε → ε ≤ 1/3 →
      AlphabetConversionProgram n q input ρ σ W ε) ∧
    (∀ (X : Type) [Fintype X] [DecidableEq X] {n q : ℕ}
      (input : X → Fin n → Fin (q+1)) (A : Matrix X X ℂ),
      ZeroFilterInstance input → (∃ x y, A x y ≠ 0) →
      crossFilteredGamma2 input A = ⊤ ∧
        ¬ ∃ W : ℝ, Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceRectValue A
            (Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceAlphabetDelta input)
              ≤ ENNReal.ofReal W) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X E _ _ _ _ n input f
    exact clause20_base_content input f
  · intro X _ _ n A _ input delta rho sigma hdelta hsigma
    exact clause20_core_content input delta rho sigma hdelta hsigma
  · intro X κ _ _ _ _ input g α α' hα hle
    exact advAlphaR_mono_of_cost_le input g α α' hα hle
  · intro X E _ _ _ _ n A _ _ input f Γ hG hz hm
    exact gen_ratio_le_sdp input f Γ hG hz hm
  · intro X _ _ n q input delta rho sigma hdelta hsigma
    exact general_alphabet_sdp_le_sourceRectValue input delta rho sigma hdelta hsigma
  · intro X H _ _ _ _ _ n q input ρ σ W ε hn hW hvalue hε hε1
    exact general_alphabet_conversion_program input ρ σ W ε hn hW hvalue hε hε1
  · intro X _ _ n q input A hz hne
    exact degenerate_no_conversion_program input A hz hne

theorem clause21_endpoint :
    (∀ {H E : Type} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]
      (label : H → E), Clause21BaseContent label) ∧
    (∀ {d : ℕ} (O : Operator d) (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ)
      (P : Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuit d)
      (hP : Qatlib.Concepts.Execution.CircuitCompile.instrumentCircuitWellFormed P) (rho : Operator d)
      (hrho : rho.PosSemidef) (K : ℕ), Clause21CoreContent O hO P hP rho hrho K) ∧
    (∀ {X : Type} [Fintype X] [DecidableEq X] {Y : Type} [Fintype Y] {D E : ℕ}
      (I : Instrument Y D E) (Γ : Matrix X X ℂ) (weight : QState X)
      (states : X → QState (Fin D)) (f : X → Y) (eps : ℝ),
      Γ.IsHermitian → Normalized weight → (∀ x, Normalized (states x)) →
      (∀ x y, f x = f y → Γ x y = 0) → 0 ≤ eps → eps ≤ 1 / 2 →
      (∀ x, 1 - eps ≤ povmProb (instrumentReadout I) (f x) (states x)) →
      |advProgress Γ weight
          (fun x => (povmLiftMatrix (instrumentReadout I) : Matrix (Y × Fin D) (Fin D) ℂ) *ᵥ states x)|
        ≤ (2 * Real.sqrt (eps * (1 - eps)) + 2 * eps) * ‖Γ‖) ∧
    (∀ {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (Configuration S O)) (cfg : Configuration S O) (fuel : ℕ),
      (∀ o k, k ≤ fuel → truncatedQueryLedger next cfg fuel (o, k) = haltJoint next cfg o k) ∧
      (∑ o : O, ∑' k : ℕ, truncatedQueryLedger next cfg fuel (o, k))
        + discardedMass next cfg fuel = 1 ∧
      truncatedQueryCount next cfg fuel ≤ unboundedQueryCount next cfg ∧
      nonterminationMass next cfg ≤ discardedMass next cfg fuel ∧
      CostedLaw.BoundedBy (RandomizedExecution.runFor next fuel cfg) fuel) ∧
    (∀ {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (Configuration S O)) (cfg : Configuration S O)
      (tol ε : ℝ≥0∞), 0 < ε → nonterminationMass next cfg ≤ tol →
      ∃ fuel : ℕ, discardedMass next cfg fuel ≤ tol + ε) ∧
    (∀ {S : Type} (step : S → CostedLaw S) (s : ℕ → S),
      (∀ k : ℕ, (1 : ℝ≥0∞) ≤ CostedLaw.expectedCost (step (s k))) →
      ¬ Qatlib.Concepts.ConversionCore.WitnessCompile.ZenoRun step s) ∧
    (∀ {n a : ℕ} [NeZero a],
      Qatlib.Concepts.ConversionCore.WitnessCompile.AdversaryResources.PolyBounded
        (interrogationResources (n := n) (a := a))) ∧
    (∀ {n a : ℕ} [NeZero a], 0 < n →
      ∃ (C : Circuit ((Fin n × ZMod a) × (Fin n → ZMod a))),
        IsUnitaryCircuit C ∧ QueryCount C = n ∧ GateCount C = 3 * n ∧
        (interrogationResources (n := n) (a := a)).gates = GateCount C) ∧
    (∀ {n D a : ℕ} (hn : 0 < n) (hD : 0 < D) (_ha : 0 < a),
      Qatlib.Concepts.ConversionCore.WitnessCompile.AlphabetAdaptive.Correct
          (adaptiveAlphabetExecution (n := n) (D := D) (a := a) (hn := hn)) ∧
        (∀ (i : Fin n),
          ((adaptiveAlphabetExecution (n := n) (D := D) (a := a) (hn := hn)).round i).inst
            = projectiveInstrument) ∧
        (∀ (c₀ : Fin D) (_hk : c₀.val + 1 ≤ n),
          haltJoint (adaptiveUnboundedNext (D := D)) (Sum.inr c₀)
            (⟨0, hD⟩) (adaptiveHaltingCost c₀) = 1 ∧
          nonterminationMass (adaptiveUnboundedNext (D := D)) (Sum.inr c₀) = 0 ∧
          c₀.val + 1 ≤ n ∧
          adaptiveHaltingCost c₀ ≤ n)) ∧
    (∀ {a : ℕ}, (scanFamily (a := a)).UniformPolyTime) ∧
    (∀ {a : ℕ} (hA : 0 < a) {c k : ℕ}
      (h : ∀ (len : ℕ) (input : List (Option (Fin a))), input.length = len →
        ∃ t : ℕ, t ≤ c * len ^ k + c ∧
          BitMachineHaltsAt ((scanFamily (a := a)).machine len) input t),
      ∀ len : ℕ, len ≤ c * len ^ k + c) ∧
    (∀ {a n : ℕ} (symbols : Fin n → Fin a),
      BitMachineHaltsAt ((scanFamily (a := a)).machine n) (interrogationWord n symbols) n ∧
      (∀ {t : ℕ}, BitMachineHaltsAt ((scanFamily (a := a)).machine n)
        (interrogationWord n symbols) t → t = n)) ∧
    (∀ {n a : ℕ} [NeZero a] (hn : 0 < n) (symbols : Fin n → Fin a),
      ∃ (C : Circuit ((Fin n × ZMod a) × (Fin n → ZMod a))),
        IsUnitaryCircuit C ∧ QueryCount C = n ∧ GateCount C = 3 * n ∧
        (interrogationResources (n := n) (a := a)).gates = GateCount C ∧
        BitMachineHaltsAt ((scanFamily (a := a)).machine n)
          (interrogationWord n symbols) n) ∧
    (∀ {n a : ℕ} [NeZero a],
      nativeInputBits (n := n) (a := a) = (interrogationResources (n := n) (a := a)).inputLen ∧
      nativeInputBits (n := n) (a := a) = (interrogationResources (n := n) (a := a)).space) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro H E _ _ _ _ label
    exact clause21_base_content label
  · intro d O hO P hP rho hrho K
    exact clause21_core_content O hO P hP rho hrho K
  · intro X _ _ Y _ D E I Γ weight states f eps hG hw hs hz he0 he1 hsuccess
    exact instrument_terminal_progress X I Γ weight states f eps hG hw hs hz he0 he1 hsuccess
  · intro S O _ _ _ _ next cfg fuel
    exact truncated_vs_original_query_ledger next cfg fuel
  · intro S O _ _ _ _ next cfg tol ε hε htol
    exact tail_truncation_charge next cfg tol ε hε htol
  · intro S step s hunit
    exact zeno_unit_charge_impossible step s hunit
  · intro n a _
    exact interrogationResources_polyBounded
  · intro n a _ hn
    exact interrogation_actual_program_resources hn
  · intro n D a hn hD ha
    exact adaptive_alphabet_execution_contract hn hD ha
  · intro a
    exact scanFamily_uniformPolyTime
  · intro a hA c k h
    exact scanFamily_uniformPolyTime_forces_linear hA h
  · intro a n symbols
    refine ⟨interrogation_native_halts_at_length symbols, ?_⟩
    intro t h
    exact interrogation_native_halts_only_at_length symbols h
  · intro n a _ hn symbols
    exact interrogation_native_queries_eq_program hn symbols
  · intro n a _
    exact ⟨nativeInputBits_eq_interrogation_inputLen, nativeInputBits_eq_interrogation_space⟩
end Qatlib.Concepts.QueryComplexity.DegreeMethod
