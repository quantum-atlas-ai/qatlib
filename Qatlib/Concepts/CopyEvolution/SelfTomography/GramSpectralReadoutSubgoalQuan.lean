/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.GramSpectralReadoutSubgoalStat
import Qatlib.Concepts.CopyEvolution.SelfTomography.GramFirstRegisterDensityQuan

/-!
# Spectral readout of Gram density operators

This module proves `gramSpectralReadoutSubgoal` for normalized weighted Gram states. Given a
unitary spectral decomposition, every QPE label event differs from the ideal spectral kernel law
by at most `8 * (M - 1) * π² / n`, with an exact fresh-copy resource count.

The mathematical background is described in [LloydMohseniRebentrost2014].

## Main statements

* `gramSpectralReadoutSubgoal`: the spectral-event error bound and `(M - 1) * n` copies, gates,
  and discards.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CopyEvolution.GramReadout (gramColumn gramMatrix gramState)

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.FreshCopyExec.QpeConsumers

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyEvolution.SelfTomography
open Matrix
open scoped Classical BigOperators ComplexOrder

/-- Proves the Gram spectral-event error bound `8 * (M - 1) * π² / n` and exact resource counts
for `M ≥ 2` and positive `n` under the stated normalization and spectral assumptions
[LloydMohseniRebentrost2014]. -/
theorem gramSpectralReadoutSubgoal : GramSpectralReadoutSubgoal := by
  intro r d M n ψ hψ w hw hsumw hM hn V hV eig hs E
  have hd := (gramFirstRegisterDensity r d ψ hψ w hw hsumw).2.2
  have hVV : Vᴴ*V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have hdiag : Vᴴ*gramMatrix ψ w*V = Matrix.diagonal (fun i => (eig i : ℂ)) := by
    rw [hs]
    calc
      _ = (Vᴴ*V)*Matrix.diagonal (fun i => (eig i : ℂ))*(Vᴴ*V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hVV, Matrix.one_mul, Matrix.mul_one]
  have hp := hd.1.conjTranspose_mul_mul_same V
  rw [hdiag] at hp
  have heigC : ∀ i, 0 ≤ (eig i : ℂ) := Matrix.posSemidef_diagonal_iff.mp hp
  have heig (i : Fin r) : 0 ≤ eig i := by exact_mod_cast heigC i
  exact ⟨copy_qpe_actual_spectral_label_event r M n hM hn (gramMatrix ψ w) V eig hd hV hs heig E,
    copy_qpe_same_path_fresh_resource_counts r M n hM hn⟩

end Qatlib.Concepts.CopyEvolution.SelfTomography
