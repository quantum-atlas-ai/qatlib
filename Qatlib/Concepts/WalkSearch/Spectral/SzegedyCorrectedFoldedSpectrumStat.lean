/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.BipartiteSpectralFolding
import Qatlib.Concepts.WalkSearch.Spectral.BipartiteTauCorrespondenceConsumers

/-!
# Folded-spectrum contract for corrected marked walks

`SzegedyCorrectedFoldedSpectrum` specifies the spectrum of the corrected marked walk on the
combined unmarked-frame range. For each real source value, it requires an explicit linear
equivalence from the product of the unmarked principal eigenspaces at opposite values.

The contract also records that each signed interior phase has the sum of those source
multiplicities, while the plus-one endpoint collects the two unit endpoints and the minus-one
endpoint has twice the nullity. This is formulated in the walk spectral framework of
[Szegedy2004].

## Main statements

* `SzegedyCorrectedFoldedSpectrum`: source equivalences and folded multiplicity formulas.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false

open Matrix
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.WalkSearch.Spectral

/-- The folded-spectrum contract for corrected marked walks of symmetric transition matrices:
explicit source-space equivalences, signed interior multiplicities, and formulas for the
plus-one and minus-one multiplicities [Szegedy2004]. -/
def SzegedyCorrectedFoldedSpectrum : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (P : I→I→ℝ) (S : Finset I),
    Qatlib.Concepts.WalkSearch.TwoLevelLower.IsTransitionMatrix P → (∀ i j, P i j = P j i) →
    (∀ lam : ℝ,
      ∃ e : (↥(LinearMap.ker
            ((unmarkedPrincipal P S-(lam:ℂ)•
              (1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)).toLin')) ×
          ↥(LinearMap.ker
            ((unmarkedPrincipal P S+(lam:ℂ)•
              (1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)).toLin'))) ≃ₗ[ℂ]
        ↥(LinearMap.ker
          ((bipartiteDiscriminant (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S)-
            (lam:ℂ)•
              (1 : Matrix (Unmarked I S⊕Unmarked I S) (Unmarked I S⊕Unmarked I S) ℂ)).toLin')),
      ∀ u, (e u).1 = Sum.elim (u.1.1+u.2.1) (u.1.1-u.2.1)) ∧
    (∀ lam : ℝ, 0 < lam → lam < 1 → ∀ s : Bool,
      Module.finrank ℂ ↥(LinearMap.ker
          ((correctedMarkedWalk P S-bipartitePhase lam s•(1 : Matrix (I×I) (I×I) ℂ)).toLin') ⊓
        LinearMap.range
          (bipartiteTilde (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S)).toLin') =
        Module.finrank ℂ ↥(LinearMap.ker
          ((unmarkedPrincipal P S-(lam:ℂ)•
            (1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)).toLin'))+
        Module.finrank ℂ ↥(LinearMap.ker
          ((unmarkedPrincipal P S+(lam:ℂ)•
            (1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)).toLin'))) ∧
    Module.finrank ℂ ↥(LinearMap.ker
        ((correctedMarkedWalk P S-(1 : Matrix (I×I) (I×I) ℂ)).toLin') ⊓
      LinearMap.range
        (bipartiteTilde (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S)).toLin') =
      Module.finrank ℂ ↥(LinearMap.ker
        ((unmarkedPrincipal P S-(1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)).toLin'))+
      Module.finrank ℂ ↥(LinearMap.ker
        ((unmarkedPrincipal P S+(1 : Matrix (Unmarked I S) (Unmarked I S) ℂ)).toLin')) ∧
    Module.finrank ℂ ↥(LinearMap.ker
        ((correctedMarkedWalk P S+(1 : Matrix (I×I) (I×I) ℂ)).toLin') ⊓
      LinearMap.range
        (bipartiteTilde (unmarkedRowFrame P S) (SwapGate*unmarkedRowFrame P S)).toLin') =
      2*Module.finrank ℂ ↥(LinearMap.ker (unmarkedPrincipal P S).toLin')

end Qatlib.Concepts.WalkSearch.Spectral
