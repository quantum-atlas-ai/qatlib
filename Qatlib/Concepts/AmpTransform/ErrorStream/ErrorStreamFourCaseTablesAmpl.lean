/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.ErrorStreamFourCaseTablesStat
import Qatlib.Concepts.AmpTransform.ErrorStream.ProgressionFourierCases
import Qatlib.Concepts.AmpTransform.ErrorStream.AmplifiedMarkedSetAmplitudes
set_option warningAsError false

open Qatlib.Concepts.AmpTransform.NoiseEnvelope

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.AmpTransform.ErrorStream
open scoped Classical BigOperators

theorem errorStreamFourCaseTables : ErrorStreamFourCaseTables := by
  intro N hN s M L P G h hM hP hbound h2T hG hdis hmark
  (try dsimp only)
  let C := aqProgressionSet N s M P ∪ G
  let T := M+L
  have hMpos : 0 < M := by omega
  have hTpos : 0 < T := by dsimp [T]; omega
  have hcard : C.card=T := by
    dsimp [C,T]
    rw [Finset.card_union_of_disjoint hdis.symm,
      aqProgression_card N s M P hMpos hP hbound, hG]
  have hF (y : Fin N) : (∑ x ∈ C, aqPhase N x.val y.val)=
      aqProgressionFourier N s M P y.val+∑ z ∈ G, aqPhase N z.val y.val := by
    dsimp [C]
    rw [Finset.sum_union hdis.symm, aq_progression_root_sum N s M P y.val hMpos hP hbound]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BornProb, aq_zero_amplitude N hN T C hcard hTpos h2T,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · rw [aq_marked_phase_zero_amplitude, hcard]
  · rw [aq_marked_qhs_zero_amplitude N hN C h hmark, hcard]
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hsub : ((N-T : ℕ) : ℝ)=(N : ℝ)-(T : ℝ) :=
      Nat.cast_sub (by dsimp [T]; omega)
    change ((T : ℝ)/(N : ℝ))^2+(1-(T : ℝ)/(N : ℝ))^2=
      1-2*(T : ℝ)*((N-T : ℕ) : ℝ)/(N : ℝ)^2
    rw [hsub]
    field_simp
    ring
  · intro y hy
    exact aq_marked_three_probabilities N hN T C h y hTpos hcard h2T hmark hy
  · intro y hy
    rw [hF, aq_progression_fourier_resonant N s M P y.val hMpos hN hy]
  · intro y hy _hyMP
    rw [hF, aq_progression_fourier_geometric N s M P y.val hMpos hN hy]
  · intro y hy hyMP
    rw [hF, aq_progression_fourier_annihilated N s M P y.val hN hy hyMP, zero_add]

end Qatlib.Concepts.AmpTransform.ErrorStream
