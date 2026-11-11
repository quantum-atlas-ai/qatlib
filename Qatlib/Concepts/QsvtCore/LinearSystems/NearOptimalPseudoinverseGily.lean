/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.NearOptimalPseudoinverseStat
import Qatlib.Concepts.QsvtCore.LinearSystems.NearOptimalPseudoinverseLine
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec

/-!
# Near optimal QSVT pseudoinverse theorem

This module proves `NearOptimalPseudoinverse`, combining the reciprocal polynomial construction
with a source phase word and postselection estimates. The theorem supplies a degree bound
proportional to `κ * log (κ / ε)` together with encoding, circuit count, minimum norm, and least
squares guarantees. The mathematical background is developed in [GilyenSuLowWiebe2019].

## Main statements

* `nearOptimalPseudoinverse`: the combined pseudoinverse implementation and output theorem.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QsVtMain

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The near optimal pseudoinverse specification holds, including the phase length bound, scaled
encoding, counts, and minimum norm and least squares postselection guarantees; see [Gilyén
et al., Theorem 41][GilyenSuLowWiebe2019]. -/
theorem nearOptimalPseudoinverse : NearOptimalPseudoinverse := by
  intro H I O _ _ _ _ _ _ A U L R κ ε hκ hε hε1 henc hgap
  let J := nearOptimalReciprocalJ κ ε
  let c : ℝ := (4*(J : ℝ))⁻¹
  obtain ⟨Φ, hlen, _, hcounts, hW⟩ := nearOptimalReciprocal_inverse_word
    H I O A U L R κ ε hκ hε hε1 henc hgap
  have hc := nearOptimalReciprocal_scale_parameters κ ε hκ hε hε1.le
  have hc0 : 0 < c := hc.1
  have hdegree : (2*J+1 : ℝ) ≤ 32*κ*Real.log (κ/ε) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using!
      (nearOptimalReciprocal_family_degree_parity κ ε hκ hε hε1).2.2.2.2.2
  obtain ⟨V, hsource⟩ := nearOptimalReciprocal_clean_input_encoding H I O A U L R henc
  refine ⟨J, c, Φ, hlen, hdegree, hc0, hc.2, hW, hcounts, ?_, ?_⟩
  · intro v hv hrange
    have hg : 2*c*ε < c := by nlinarith
    obtain ⟨hp, _, φ, hout, hstate⟩ := scaledPseudoinverse_postselection hsource hW hv hrange hg
    change (c-2*c*ε)^2 ≤ _ at hp
    change IsMinimumNormSolutionState A v φ (2*(2*c*ε)/c) at hstate
    have he : (c-2*c*ε)^2 = (c*(1-2*ε))^2 := by ring
    have herr : 2*(2*c*ε)/c = 4*ε := by field_simp; ring
    refine ⟨?_, φ, hout, ?_⟩
    · simpa only [he] using! hp
    · simpa only [herr] using! hstate
  · intro v hv htau
    have hg : 2*c*ε < c*leastSquaresOverlap A v := by
      have hh := mul_lt_mul_of_pos_left htau hc0
      nlinarith
    obtain ⟨hp, _, φ, hout, hstate⟩ := leastSquares_actual_postselection
      A V (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)ᴴ
      (sourceAverageClean L) (sourceAverageClean R) v c 1 (2*c*ε) hsource hW hc0 hv hg
    have he : ((c*leastSquaresOverlap A v-2*c*ε)/1)^2 =
        (c*(leastSquaresOverlap A v-2*ε))^2 := by ring
    have herr : 2*(2*c*ε)/(c*leastSquaresOverlap A v) = 4*ε/leastSquaresOverlap A v := by
      field_simp
      ring
    refine ⟨?_, φ, hout, ?_⟩
    · simpa only [he] using! hp
    · simpa only [herr] using! hstate

end Qatlib.Concepts.QsvtCore.LinearSystems
