/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.CharacterTransform

/-!
# Specification of regular summand extraction

`SourceSummandExtraction` states the matrix properties required of the regular difference gate
for a finite group. It requires unitarity, an intertwining identity, and preservation of
positivity, trace one, and subgroup invariance under conjugation by the gate. See
[Kuperberg2005] for the mathematical background.

## Main statements

* `SourceSummandExtraction`: the finite-group extraction specification.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

open scoped ComplexOrder
set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.RecordExtract

/-- The regular difference gate is unitary and intertwines diagonal left action with
right-factor left action, transporting invariant positive trace-one matrices accordingly. -/
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
