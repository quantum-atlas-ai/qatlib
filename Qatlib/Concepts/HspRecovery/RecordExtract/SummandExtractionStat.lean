/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.CharacterTransform
open scoped ComplexOrder
set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.RecordExtract

def SourceSummandExtraction : Prop := by
  classical
  exact
  ∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G),
    sourceDifferenceGate G ∈ Matrix.unitaryGroup (G × G) ℂ ∧
    (∀ g : G, sourceDifferenceGate G * sourceDiagonalLeft G g =
      sourceRightFactorLeft G g * sourceDifferenceGate G) ∧
    ∀ rho : Matrix (G × G) (G × G) ℂ,
      rho.PosSemidef → rho.trace = 1 →
      (∀ h : H, sourceDiagonalLeft G h.val * rho = rho) →
      let out := sourceDifferenceGate G * rho * (sourceDifferenceGate G).conjTranspose
      out.PosSemidef ∧ out.trace = 1 ∧
        ∀ h : H, sourceRightFactorLeft G h.val * out = out
end Qatlib.Concepts.HspRecovery.RecordExtract
