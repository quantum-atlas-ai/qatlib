/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HermitianMap26.Construction.Basic

/-!
# Compilation with no completion branch

This module treats the scalar-Gram special case of the signed Kraus construction in
[CaiEtAl2026]. When `D.krausSum` equals the normalization factor times the identity, the
original normalized family is already complete.

The theorem `complete_case_program` compiles this family directly, with every original branch
represented by a leaf and exactly `Nat.clog 2 r` measurements at each leaf.

## Main statements

* `complete_case_program`: constructs the direct program and proves its branch identities and
  `SingleQubit` condition.

## References

* [Cai et al., 2026][CaiEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.DimInstruments.DimTreeExec
open Qatlib.Concepts.KrausCompile.BinaryTree

namespace Qatlib.Papers.HermitianMap26.Construction.SignedKraus

/-- When the unsigned Kraus sum is the normalization factor times the identity in positive
dimension, there is a `SingleQubit` program using exactly `Nat.clog 2 r` measurements per
leaf. Each normalized Kraus branch occurs among its leaves. [CaiEtAl2026]. -/
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
