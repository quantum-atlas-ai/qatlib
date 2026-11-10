/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HermitianMap26.Construction.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.DimInstruments.DimTreeExec
open Qatlib.Concepts.KrausCompile.BinaryTree

namespace Qatlib.Papers.HermitianMap26.Construction.SignedKraus

theorem complete_case_program {d r : ℕ} (D : SignedKraus d r) (hd : 0 < d)
    (hscale : D.krausSum = (D.normalization : ℂ) • (1 : Op d)) :
    ∃ P : Program d d, SingleQubit d P ∧
      (∀ t ∈ leaves P, t.measurements = Nat.clog 2 r) ∧
      (∀ i : Fin r, ∃ t ∈ leaves P, ∀ ρ,
        t.map ρ = D.normalizedKraus D.normalization i * ρ *
          (D.normalizedKraus D.normalization i).conjTranspose) := by
  let K := D.normalizedKraus D.normalization
  have hK : KrausComplete K := (D.completion_trivial_of_scaled hd hscale).2
  exact ⟨compileFamily K hK, compileFamily_singleQubit K hK,
    compileFamily_depth K hK, compileFamily_original K hK⟩

end Qatlib.Papers.HermitianMap26.Construction.SignedKraus
