/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.SourceModel

@[expose] public section


/-! # A replacement channel satisfies the literal old perfect-recovery target

The target only asks for some channel recovering the single state sigma. It
does not specify a Petz map, dependence on t, or recovery of any second state.
The actual CPTP replacement channel proves this weak statement without those
source-theorem claims.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QShannonWilde11.MainResults.Recovery

open Qatlib.Papers.QShannonWilde11.MainResults.Model
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Qatlib.Concepts.ChannelTheory.Stinespring

/-- A genuine replacement channel satisfies the old existential recovery contract,
without a Petz recovery claim. -/
theorem exists_replacement_channel_recovering_state {d : ℕ} (σ : Dens (Fin d)) (_N : QChannel d d)
    (Nσ : Dens (Fin d)) (_hNσ : Nσ.val = _N.map σ.val) (_t : ℝ) :
    ∃ (R : QChannel d d) (Rσ : Dens (Fin d)),
      Rσ.val = R.map Nσ.val ∧ Rσ.val = σ.val := by
  let : Nonempty (Fin d) := (state σ).nonempty
  let T : CPTPMap (Fin d) (Fin d) := CPTPMap.replacement (state σ)
  refine ⟨ofPhyslib T, σ, ?_, rfl⟩
  have h := CPTPMap.mat_coe_eq_apply_mat T (state Nσ)
  simpa [T] using h

end Qatlib.Papers.QShannonWilde11.MainResults.Recovery
