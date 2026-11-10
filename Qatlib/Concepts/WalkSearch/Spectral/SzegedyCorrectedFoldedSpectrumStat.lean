/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.BipartiteSpectralFolding
import Qatlib.Concepts.WalkSearch.Spectral.BipartiteTauCorrespondenceConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.WalkSearch.Spectral

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
