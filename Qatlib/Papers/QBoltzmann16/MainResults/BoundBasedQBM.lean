/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QBoltzmann16.MainResults.BoltzmannDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Matrix Matrix.Norms.L2Operator
namespace Qatlib.Papers.QBoltzmann16.MainResults

theorem source_eq24_golden_thompson (D : ℕ) (A B : Operator D)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (NormedSpace.exp (A+B))).re ≤
      (Matrix.trace (NormedSpace.exp A*NormedSpace.exp B)).re :=
  golden_thompson_trace D A B hA hB

theorem source_eq25_27_clamped_probability_lower_bound {D E : ℕ}
    (H : Operator D) (V : Matrix (Fin D) (Fin E) ℂ)
    (hD : 0<D) (hH : H.IsHermitian) (hV : Vᴴ*V=1) :
    gibbsPartition E (clampHamiltonian V H)/gibbsPartition D H ≤
      marginalizedProbability D H (V*Vᴴ) :=
  clamped_trace_probability_lower_bound H V hD hH hV

theorem source_eq29_negative_log_likelihood_upper_bound {I : Type*} [Fintype I]
    {D E : ℕ} (hD : 0<D) (hE : 0<E) (H : Operator D) (hH : H.IsHermitian)
    (V : I→Matrix (Fin D) (Fin E) ℂ) (hV : ∀i,(V i)ᴴ*V i=1)
    (Pdata : I→ℝ) (hPdata : ∀i,0≤Pdata i) :
    -(∑i,Pdata i*Real.log (marginalizedProbability D H (V i*(V i)ᴴ))) ≤
      -(∑i,Pdata i*Real.log (gibbsPartition E (clampHamiltonian (V i) H)/gibbsPartition D H)) :=
  negative_log_likelihood_upper_bound Pdata _ _ hPdata
    (fun i=>clamped_ratio_pos (V i) H hD hE hH)
    (fun i=>clamped_trace_probability_lower_bound H (V i) hD hH (hV i))

theorem source_bound_based_qbm_main {I : Type*} [Fintype I] {D E : ℕ}
    (hD : 0<D) (hE : 0<E) (H : Operator D) (hH : H.IsHermitian)
    (V : I→Matrix (Fin D) (Fin E) ℂ) (hV : ∀i,(V i)ᴴ*V i=1)
    (Pdata : I→ℝ) (hPdata : ∀i,0≤Pdata i) :
    (∀i,gibbsPartition E (clampHamiltonian (V i) H)/gibbsPartition D H ≤
      marginalizedProbability D H (V i*(V i)ᴴ)) ∧
    -(∑i,Pdata i*Real.log (marginalizedProbability D H (V i*(V i)ᴴ))) ≤
      -(∑i,Pdata i*Real.log (gibbsPartition E (clampHamiltonian (V i) H)/gibbsPartition D H)) :=
  ⟨fun i=>source_eq25_27_clamped_probability_lower_bound H (V i) hD hH (hV i),
    source_eq29_negative_log_likelihood_upper_bound hD hE H hH V hV Pdata hPdata⟩
end Qatlib.Papers.QBoltzmann16.MainResults
