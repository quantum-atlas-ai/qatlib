/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ExpSpeedup10.MainResults.Model.SourceDesign

@[expose] public section


/-! # Diagnostic for the legacy ground-eigenvalue index

The pinned model defines sourceLambda1 at antitone index zero, hence at the
largest eigenvalue. Its old positive second-smallest-gap hypothesis is then
incompatible with sourceLambda1 = 0. This diagnoses the formal model; it is
not a proof or refutation of source Lemma VI.3 (arXiv:1010.3654v2, Eq. (68)).
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
open Qatlib.Papers.ExpSpeedup10.MainResults.Model

namespace Qatlib.Papers.ExpSpeedup10.MainResults.SpectralIndex

/-- The actual antitone index convention forbids the old positive-gap premise. -/
theorem noOldGap {D : ℕ} (hD : 2 ≤ D)
    {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian)
    (hzero : sourceLambda1 (by omega : 1 ≤ D) hM = 0) :
    ¬ 0 < sourceLambda2Asc hD hM := by
  have hle : sourceLambda2Asc hD hM ≤
      sourceLambda1 (by omega : 1 ≤ D) hM := by
    exact hM.eigenvalues₀_antitone (show
      (⟨0, by have := Fintype.card_fin D; omega⟩ : Fin (Fintype.card (Fin D))) ≤
      ⟨D - 2, by have := Fintype.card_fin D; omega⟩ from Nat.zero_le _)
  rw [hzero] at hle
  exact not_lt_of_ge hle

end Qatlib.Papers.ExpSpeedup10.MainResults.SpectralIndex
