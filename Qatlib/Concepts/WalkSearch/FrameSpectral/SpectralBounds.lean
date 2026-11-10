/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalkSearch.MultiBandFilter
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.HspRecovery.SieveLaw

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Matrix
open Qatlib
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkSearch.ClassicalStop
open Qatlib
open Qatlib.Concepts.HspRecovery.KitaevReadout
open scoped Classical BigOperators

theorem walk_spectral_clause6 : WalkSpectralClause6Prop := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro I _ _ P hP π hπ hrev
    exact reversible_stationary hP hπ hrev
  · intro I _ _ P hP π hrev
    exact szegedyWalk_fixes_stationary P hP hrev
  · intro I _ _ P hP v hv hsum
    exact normalized_szegedyEmbedState P hP hv hsum
  · intro I _ _ P hP
    exact szegedyWalk_eq_twoReflections P hP
  · intro I _ _ P hP
    exact szegedyWalk_unitary P hP
  · intro I _ _ P hP v hv θ hs hvD
    exact szegedy_spectral_map P hP v hv θ hs hvD
  · intro I _ _ J _ _ j0 v p W M k η hM hη hW hv heigen hp0 hgap c
    exact phase_reflection_reachable_source_error J j0 v p W M k η hM hη hW hv heigen hp0 hgap c
  · intro M k hM
    exact phase_reflection_actual_queries_and_macros (I := Unit) M k hM
  · intro M k t hM
    exact phase_search_fresh_access_ledger M k t hM

theorem walk_spectral_clause32 : WalkSpectralClause32Prop := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact mnrs_search_theorem_three_abstract
  · intro ε c₁ c₂ U C δ tMax hε hε1 hc₁ hc₂ hmax hδ hC hcU hcc
    exact mnrs_order_form_cost ε c₁ c₂ U C δ tMax hε hε1 hc₁ hc₂ hmax hδ hC hcU hcc
  · intro I _ _ J _ _ j0 v p W S M k t η θ hM hη hW hv heigen hp0 hgap hmark hθ hθ1 hp
    exact phase_search_actual_marked_success J j0 v p W S M k t η θ hM hη hW hv heigen hp0 hgap hmark hθ hθ1 hp
  · intro I _ _ W ψ S M k t hW hM
    exact phaseSearchState_norm W ψ S M k t hW hM
  · intro M k t hM
    exact phase_search_fresh_access_ledger M k t hM

theorem walk_spectral_clause33 : WalkSpectralClause33Prop := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M hM
    exact sin_envelope_state_normalized_and_prep M hM
  · intro M φ z hM hr
    exact sin_envelope_kernel_far_label_tail M φ z hM hr
  · intro M hM φ η hη hfar hgap
    exact sin_envelope_zero_label_gap_bound M hM φ η hη hfar hgap
  · intro I _ _ M hM
    exact sin_envelope_forward_word_counts (I := I) M hM
  · intro D M hM d hd B U hB hU
    exact sin_envelope_word_legality_and_counts D M hM d hd B U hB hU
  · intro M hM d k hk
    exact sin_envelope_aa_query_budget M hM d k hk

theorem walk_spectral_tunableGoal : WalkSpectralTunableQueryProp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro J _ _ M bands phi eta hM heta heta1 hphi hbands hmargin
    exact multiband_signed_classifier_from_geometric_margin J M bands phi eta hM heta heta1 hphi hbands hmargin
  · intro I J _ _ _ _ U M hM S v c phi T eta hU heta heta1 hgap hv hc he
    exact multiband_actual_full_uncomputed_branch_error I J U M hM S v c phi T eta hU heta heta1 hgap hv hc he
  · intro I J _ _ _ _ U M hM S v c phi T eta hU heta heta1 hgap hv hc he
    exact multiband_actual_coherent_reflection_error I J U M hM S v c phi T eta hU heta heta1 hgap hv hc he
  · intro I J _ _ _ _ U M hM S v c phi T eta hU heta heta1 hgap hv hc he
    exact multiband_derived_success_and_conditional_state I J U M hM S v c phi T eta hU heta heta1 hgap hv hc he
  · intro I _ _ M S
    exact bandSign_unitary (I := I) M S
  · intro I _ _ M S hM
    exact multiband_actual_word_forward_inverse_ledger I M S hM

theorem walk_spectral_optGoal : WalkSpectralOptimizedTunableProp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I _ _ M hM S U W psi hU hW hpsi
    exact multiband_same_word_access_perturbation I M hM S U W psi hU hW hpsi
  · intro I J _ _ _ _ U M hM S v c phi T eta hU heta heta1 hgap hv hc he
    exact multiband_derived_success_and_conditional_state I J U M hM S v c phi T eta hU heta heta1 hgap hv hc he
  · intro I J _ _ _ _ b
    exact basisColumns_norm_le b
  · intro I J _ _ _ _ b
    exact basisColumns_adjoint_mul b

theorem walk_spectral_clause36 : WalkSpectralClause36Prop := by
  refine ⟨?_, ?_, ?_⟩
  · intro O _ D E R J S ρ τ hρ hτ hequal
    exact selective_joint_mass_error J S ρ τ hρ hτ hequal
  · intro O _ D E R J S ρ τ hρ hτ hequal
    exact sharp_selective_joint_stability O D E R J S ρ τ hρ hτ hequal
  · intro O _ D E R J S ρ τ η hρ hτ hequal hη hdiff hgap
    exact sharp_selective_joint_stability_of_gap J S ρ τ η hρ hτ hequal hη hdiff hgap

theorem walk_spectral_clause37 : WalkSpectralClause37Prop := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I J _ _ _ _ W M k hM v c φ T η hW hη hv hc he ht hg
    exact degenerate_phase_zero_event_and_full_branch_error I J W M k hM v c φ T η hW hη hv hc he ht hg
  · intro I J _ _ _ _ W M k hM v c φ T η hW hη hv hc he ht hg
    exact degenerate_phase_conditional_target_state_error I J W M k hM v c φ T η hW hη hv hc he ht hg
  · intro I _ _ ψ S
    exact degenerate_postMeasure_norm_le_one ψ S
  · intro I J _ _ _ _ W M k hM v c φ he
    exact degenerate_phase_actual_spectral_packet I J W M k hM v c φ he

private theorem mulVec_mulVec' {A B C : Type} [Fintype B] [Fintype C]
    (M : Matrix A B ℂ) (N : Matrix B C ℂ) (v : C → ℂ) :
    (M * N) *ᵥ v = M *ᵥ (N *ᵥ v) := (Matrix.mulVec_mulVec v M N).symm

private theorem szegedyFrameProjector_apply {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (z : QState (I × I)) (x y : I) :
    ((SzegedyIsometry P * (SzegedyIsometry P)ᴴ) *ᵥ z) (x, y) =
      (Real.sqrt (P x y) : ℂ) * ∑ y' : I, (Real.sqrt (P x y') : ℂ) * z (x, y') := by
  have hcol : ∀ a : I, ((SzegedyIsometry P)ᴴ *ᵥ z) a =
      ∑ y' : I, (Real.sqrt (P a y') : ℂ) * z (a, y') := by
    intro a
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    simp only [Matrix.conjTranspose_apply, szegedyIsometry_apply_pair]
    rw [Finset.sum_eq_single a]
    · simp [Complex.conj_ofReal]
    · intro b _ hb
      simp [hb]
    · intro hcon
      exact absurd (Finset.mem_univ a) hcon
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]
  simp only [szegedyIsometry_apply_pair]
  rw [Finset.sum_eq_single x]
  · simp [hcol]
  · intro b _ hb
    simp [Ne.symm hb]
  · intro hcon
    exact absurd (Finset.mem_univ x) hcon

private theorem unmarkedFrame_conjTranspose_apply {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (z : QState (I × I)) (i : Unmarked I S) :
    ((unmarkedRowFrame P S)ᴴ *ᵥ z) i =
      ∑ y' : I, (Real.sqrt (P i.1 y') : ℂ) * z (i.1, y') := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_apply, unmarkedRowFrame, szegedyIsometry_apply_pair]
  rw [Finset.sum_eq_single i.1]
  · simp [Complex.conj_ofReal]
  · intro b _ hb
    simp [hb]
  · intro hcon
    exact absurd (Finset.mem_univ i.1) hcon

private theorem unmarkedFrameProjector_apply {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (z : QState (I × I)) (x y : I) :
    ((unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ) *ᵥ z) (x, y) =
      (if x ∉ S then (Real.sqrt (P x y) : ℂ) * ∑ y' : I, (Real.sqrt (P x y') : ℂ) * z (x, y')
       else 0) := by
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]
  simp only [unmarkedRowFrame, szegedyIsometry_apply_pair]
  simp only [unmarkedFrame_conjTranspose_apply P S z]
  rw [← Finset.sum_subtype (F:=inferInstance) (p:=fun i : I => i ∉ S)
    (Finset.univ.filter (fun i => i ∉ S)) (by intro i; simp)
    (fun i : I => (if x = i then (Real.sqrt (P i y) : ℂ) else 0) *
      ∑ y' : I, (Real.sqrt (P i y') : ℂ) * z (i, y'))]
  rw [Finset.sum_filter]
  rw [Finset.sum_eq_single x]
  · simp
  · intro b _ hb
    simp [hb, Ne.symm hb]
  · intro hcon
    exact absurd (Finset.mem_univ x) hcon

private theorem absorbingKernel_sqrt {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (x y : I) :
    (Real.sqrt (absorbingKernel P S x y) : ℂ) =
      (if x ∉ S then (Real.sqrt (P x y) : ℂ) else if y = x then 1 else 0) := by
  by_cases hx : x ∈ S
  · by_cases hy : y = x
    · simp [absorbingKernel, hx, hy]
    · simp [absorbingKernel, hx, hy]
  · simp [absorbingKernel, hx]

private theorem absorbingFrameProjector_apply {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (z : QState (I × I))
    (hz : lemma3TrapComplement S z) (x y : I) :
    ((SzegedyIsometry (absorbingKernel P S) *
        (SzegedyIsometry (absorbingKernel P S))ᴴ) *ᵥ z) (x, y) =
      (if x ∉ S then (Real.sqrt (P x y) : ℂ) * ∑ y' : I, (Real.sqrt (P x y') : ℂ) * z (x, y')
       else 0) := by
  rw [szegedyFrameProjector_apply (absorbingKernel P S) z x y]
  by_cases hx : x ∉ S
  · rw [if_pos hx]
    have h1 : (Real.sqrt (absorbingKernel P S x y) : ℂ) = (Real.sqrt (P x y) : ℂ) := by
      rw [absorbingKernel_sqrt P S, if_pos hx]
    have h2 : ∀ y' : I, (Real.sqrt (absorbingKernel P S x y') : ℂ) =
        (Real.sqrt (P x y') : ℂ) := by
      intro y'
      rw [absorbingKernel_sqrt P S, if_pos hx]
    simp only [h1, h2]
  · have hx0 : x ∈ S := by simpa using! hx
    have hz0 : z (x, x) = 0 := hz x hx0
    have hsum : ∑ y' : I, (Real.sqrt (absorbingKernel P S x y') : ℂ) * z (x, y') = 0 := by
      rw [Finset.sum_eq_single x]
      · rw [absorbingKernel_sqrt P S, if_neg hx, if_pos rfl, one_mul]
        exact hz0
      · intro b _ hb
        rw [absorbingKernel_sqrt P S, if_neg hx, if_neg hb]
        simp
      · intro hcon
        exact absurd (Finset.mem_univ x) hcon
    rw [if_neg hx]
    rw [absorbingKernel_sqrt P S, if_neg hx]
    by_cases h : y = x
    · rw [if_pos h, hsum]
      simp
    · rw [if_neg h, hsum]
      simp

private theorem absorbingFrame_eq_unmarkedFrame_on_trap {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (z : QState (I × I)) (hz : lemma3TrapComplement S z) :
    ((SzegedyIsometry (absorbingKernel P S) *
        (SzegedyIsometry (absorbingKernel P S))ᴴ) *ᵥ z) =
      ((unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ) *ᵥ z) := by
  funext xy
  obtain ⟨x, y⟩ := xy
  exact (absorbingFrameProjector_apply P S z hz x y).trans
    (unmarkedFrameProjector_apply P S z x y).symm

private theorem absorbingReflection_eq_unmarkedReflection_on_trap {I : Type} [Fintype I]
    [DecidableEq I] (P : I → I → ℝ) (S : Finset I) (z : QState (I × I))
    (hz : lemma3TrapComplement S z) :
    (SzegedyReflection (absorbingKernel P S)) *ᵥ z =
      (ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ)) *ᵥ z := by
  rw [SzegedyReflection, reflectionAbout_mulVec, reflectionAbout_mulVec]
  rw [absorbingFrame_eq_unmarkedFrame_on_trap P S z hz]

private theorem trapComplement_swapGate {I : Type} [Fintype I] [DecidableEq I] (S : Finset I)
    (w : QState (I × I)) (hw : lemma3TrapComplement S w) :
    lemma3TrapComplement S (SwapGate *ᵥ w) := by
  intro i hi
  rw [applyGate_swapGate]
  exact hw i hi

private theorem trapComplement_unmarkedFrameProjector {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (w : QState (I × I)) (j : I) (hj : j ∈ S) :
    ((unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ) *ᵥ w) (j, j) = 0 := by
  rw [unmarkedFrameProjector_apply P S w j j]
  simp [hj]

private theorem trapComplement_reflection {I : Type} [Fintype I] [DecidableEq I] (S : Finset I)
    (M : Matrix (I × I) (I × I) ℂ) (w : QState (I × I)) (hw : lemma3TrapComplement S w)
    (hM : ∀ j ∈ S, (M *ᵥ w) (j, j) = 0) :
    lemma3TrapComplement S (ReflectionAbout M *ᵥ w) := by
  intro j hj
  rw [reflectionAbout_mulVec]
  simp only [Pi.smul_apply, Pi.sub_apply]
  rw [hM j hj]
  simp [hw j hj]

private theorem correctedWalk_preserves_trapComplement {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (w : QState (I × I)) (hw : lemma3TrapComplement S w) :
    lemma3TrapComplement S ((correctedMarkedWalk P S) *ᵥ w) := by
  have h1 : lemma3TrapComplement S
      ((ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ)) *ᵥ w) := by
    refine trapComplement_reflection S _ w hw ?_
    intro j hj
    exact trapComplement_unmarkedFrameProjector P S w j hj
  have h2 : lemma3TrapComplement S
      (SwapGate *ᵥ ((ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ)) *ᵥ w)) :=
    trapComplement_swapGate S _ h1
  have h3 : lemma3TrapComplement S
      ((ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ)) *ᵥ
        (SwapGate *ᵥ ((ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ)) *ᵥ w))) := by
    refine trapComplement_reflection S _ _ h2 ?_
    intro j hj
    exact trapComplement_unmarkedFrameProjector P S _ j hj
  have h4 : lemma3TrapComplement S
      (SwapGate *ᵥ ((ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ)) *ᵥ
        (SwapGate *ᵥ ((ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ)) *ᵥ w)))) :=
    trapComplement_swapGate S _ h3
  rw [correctedMarkedWalk]
  rw [mulVec_mulVec', mulVec_mulVec', mulVec_mulVec']
  exact h4

private theorem absorbingWalk_step_eq_correctedWalk_step {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (w : QState (I × I)) (hw : lemma3TrapComplement S w) :
    (lemma3AbsorbingWalk P S) *ᵥ w = (correctedMarkedWalk P S) *ᵥ w := by
  have h1 : (SzegedyReflection (absorbingKernel P S)) *ᵥ w =
      (ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ)) *ᵥ w := by
    rw [absorbingReflection_eq_unmarkedReflection_on_trap P S w hw]
  have h2 : lemma3TrapComplement S
      ((ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ)) *ᵥ w) := by
    refine trapComplement_reflection S _ w hw ?_
    intro j hj
    exact trapComplement_unmarkedFrameProjector P S w j hj
  have h3 : lemma3TrapComplement S
      (SwapGate *ᵥ ((ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ)) *ᵥ w)) :=
    trapComplement_swapGate S _ h2
  have h4 : (SzegedyReflection (absorbingKernel P S)) *ᵥ
      (SwapGate *ᵥ ((ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ)) *ᵥ w)) =
      (ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ)) *ᵥ
      (SwapGate *ᵥ ((ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ)) *ᵥ w)) := by
    rw [absorbingReflection_eq_unmarkedReflection_on_trap P S _ h3]
  calc (lemma3AbsorbingWalk P S) *ᵥ w
      = SwapGate *ᵥ (SzegedyReflection (absorbingKernel P S) *ᵥ
          (SwapGate *ᵥ (SzegedyReflection (absorbingKernel P S) *ᵥ w))) := by
        rw [lemma3AbsorbingWalk, SzegedyWalk, mulVec_mulVec', mulVec_mulVec', mulVec_mulVec']
    _ = SwapGate *ᵥ ((ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ)) *ᵥ
          (SwapGate *ᵥ ((ReflectionAbout (unmarkedRowFrame P S * (unmarkedRowFrame P S)ᴴ)) *ᵥ w))) := by
        rw [h1, h4]
    _ = (correctedMarkedWalk P S) *ᵥ w := by
        rw [correctedMarkedWalk, mulVec_mulVec', mulVec_mulVec', mulVec_mulVec']

theorem lemma3_absorbing_corrected_walk_bridge {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (z : QState (I × I)) (hz : lemma3TrapComplement S z) :
    ∀ K : ℕ, lemma3TrapComplement S ((lemma3AbsorbingWalk P S) ^ K *ᵥ z) ∧
      (lemma3AbsorbingWalk P S) ^ K *ᵥ z = (correctedMarkedWalk P S) ^ K *ᵥ z := by
  intro K
  induction K with
  | zero =>
      refine ⟨?_, ?_⟩
      · rw [pow_zero, Matrix.one_mulVec]
        exact hz
      · rw [show (lemma3AbsorbingWalk P S) ^ 0 = 1 from pow_zero _,
          show (correctedMarkedWalk P S) ^ 0 = 1 from pow_zero _]
  | succ K ih =>
      obtain ⟨hw, hzK⟩ := ih
      have hw' : lemma3TrapComplement S ((correctedMarkedWalk P S) ^ K *ᵥ z) := by
        rw [← hzK]
        exact hw
      have hstep : (lemma3AbsorbingWalk P S) *ᵥ ((correctedMarkedWalk P S) ^ K *ᵥ z) =
          (correctedMarkedWalk P S) *ᵥ ((correctedMarkedWalk P S) ^ K *ᵥ z) :=
        absorbingWalk_step_eq_correctedWalk_step P S _ hw'
      refine ⟨?_, ?_⟩
      · rw [pow_succ', mulVec_mulVec', hzK, hstep]
        exact correctedWalk_preserves_trapComplement P S _ hw'
      · rw [pow_succ', mulVec_mulVec', hzK, hstep, pow_succ', mulVec_mulVec']

theorem walk_spectral_clause38 : WalkSpectralClause38Prop := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro I _ _ _ P S δ L hδ hδ1 hP hp hL
    exact corrected_szegedy_busy_random_power_difference I P S δ L hδ hδ1 hP hp hL
  · intro I _ _ _ P S hP
    exact detectionUnmarkedInitial_norm_sq P S hP
  · intro I _ _ P S
    exact detectionUnmarkedInitial_trapComplement P S
  · intro I _ _ P S hP
    exact absorbingKernel_isTransitionMatrix P S hP
  · intro δ ε hδ hε
    exact lemma3Length_bounds δ ε hδ hε
  · intro I _ _ _ P S δ L hδ hδ1 hgap ha hL
    exact lemma3_threshold_event P S δ L hδ hδ1 hgap ha hL

theorem lemma3_absorbing_threshold_mass_eq {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (L : ℕ) :
    lemma3ThresholdMass (lemma3AbsorbingWalk P S) (detectionUnmarkedInitial P S) L =
      lemma3ThresholdMass (correctedMarkedWalk P S) (detectionUnmarkedInitial P S) L := by
  have hbridge : ∀ k : Fin L,
      (lemma3AbsorbingWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S =
        (correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S := by
    intro k
    exact (lemma3_absorbing_corrected_walk_bridge P S (detectionUnmarkedInitial P S)
      (detectionUnmarkedInitial_trapComplement P S) (k.val + 1)).2
  have hfilter :
      Finset.univ.filter (fun k : Fin L =>
        ‖toEuclidean_fromVec (detectionUnmarkedInitial P S +
          (lemma3AbsorbingWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S)‖ ^ 2 ≤ 3) =
      Finset.univ.filter (fun k : Fin L =>
        ‖toEuclidean_fromVec (detectionUnmarkedInitial P S +
          (correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S)‖ ^ 2 ≤ 3) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hk
      have hstep : detectionUnmarkedInitial P S +
          (lemma3AbsorbingWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S =
          detectionUnmarkedInitial P S +
            (correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S := by
        rw [hbridge k]
      rw [hstep] at hk
      exact hk
    · intro hk
      have hstep : detectionUnmarkedInitial P S +
          (correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S =
          detectionUnmarkedInitial P S +
            (lemma3AbsorbingWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S := by
        rw [hbridge k]
      rw [hstep] at hk
      exact hk
  unfold lemma3ThresholdMass
  rw [hfilter]

theorem walk_spectral_clause38_full_endpoint_v2 : WalkSpectralClause38FullEndpoint := by
  intro I _ _ _ P S δ hδ hδ1 hgap ha ha1
  (try dsimp only)
  have hth := lemma3_threshold_event P S δ (lemma3Length δ (markedFraction S))
    hδ hδ1 hgap ha rfl
  have hLpos : 0 < lemma3Length δ (markedFraction S) := hth.1
  have hLpos' : 0 < ((lemma3Length δ (markedFraction S) : ℝ)) := by
    exact_mod_cast hLpos
  have hmass : (1 / 6 : ℝ) ≤
      lemma3ThresholdMass (correctedMarkedWalk P S) (detectionUnmarkedInitial P S)
        (lemma3Length δ (markedFraction S)) := by
    have hdiv : ((lemma3Length δ (markedFraction S) : ℝ)) / 6 ≤
        (Finset.univ.filter (fun k : Fin (lemma3Length δ (markedFraction S)) =>
          ‖toEuclidean_fromVec (detectionUnmarkedInitial P S +
            (correctedMarkedWalk P S) ^ (k.val + 1) *ᵥ detectionUnmarkedInitial P S)‖ ^ 2
            ≤ 3)).card := hth.2
    unfold lemma3ThresholdMass
    rw [le_div_iff₀ hLpos']
    have hring : (1 / 6 : ℝ) * ((lemma3Length δ (markedFraction S) : ℝ)) =
        ((lemma3Length δ (markedFraction S) : ℝ)) / 6 := by ring
    rw [hring]
    exact hdiv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact absorbingKernel_isTransitionMatrix P S hgap.1
  · exact detectionUnmarkedInitial_trapComplement P S
  · intro z hz K
    exact lemma3_absorbing_corrected_walk_bridge P S z hz K
  · exact detectionUnmarkedInitial_norm_sq P S hgap.1
  · obtain ⟨hL0, hL1, hL2⟩ := lemma3Length_bounds δ (markedFraction S) hδ ha
    exact hL0
  · obtain ⟨hL0, hL1, hL2⟩ := lemma3Length_bounds δ (markedFraction S) hδ ha
    exact hL1
  · obtain ⟨hL0, hL1, hL2⟩ := lemma3Length_bounds δ (markedFraction S) hδ ha
    exact hL2
  · exact hmass
  · rw [lemma3_absorbing_threshold_mass_eq P S (lemma3Length δ (markedFraction S))]
    exact hmass

theorem walk_spectral_clause39 : WalkSpectralClause39Prop := by
  refine ⟨?_, ?_, ?_⟩
  · exact eigenphaseEstimateSubgoal
  · intro M I _ _ U ψ k hψ
    exact controlledPowers_kickback hψ
  · intro δ ε hδ hδ1 hε hε1 I _ _ U ψ φ heig s hs
    exact eigenphaseEstimateSubgoal δ ε hδ hδ1 hε hε1 I U ψ φ heig s hs

end Qatlib.Concepts.WalkSearch.FrameSpectral
