/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.EigenbasisReadoutSamplingSubgoalStat
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.HspRecovery.AbelianSampling
open Matrix
open scoped BigOperators Classical

theorem eigenbasisReadoutSamplingSubgoal : EigenbasisReadoutSamplingSubgoal := by
  intro M hM Idx I _ _ _ _ U ψ k c S horth heig _hnorm
  rw [qpe_exact_readout_linear M hM U c ψ k heig]
  have hz (z : Fin M) :
      (fun j => (∑ i, c i • TensorState (Ket (k i)) (ψ i)) (z,j))=
        ∑ i, (c i*Ket (k i) z) • ψ i := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, TensorState, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold MeasureProb BornProb
  rw [Finset.sum_product]
  have hm (z : Fin M) :
      (∑ j : I, ‖(∑ i, c i • TensorState (Ket (k i)) (ψ i)) (z,j)‖^2)=
        ∑ i, if k i=z then ‖c i‖^2 else 0 := by
    change (∑ j : I, ‖(fun j => (∑ i, c i • TensorState (Ket (k i)) (ψ i)) (z,j)) j‖^2)=_
    rw [hz, sum_norm_sq_orthonormal ψ _ (fun i j => by
      by_cases he : i=j
      · simpa only [if_pos he] using horth i j
      · simpa only [if_neg he] using horth i j)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases he : k i=z <;> simp [Ket, he, Ne.symm]
  simp_rw [hm]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_ite_eq]

end Qatlib.Concepts.HspRecovery.AbelianSampling
