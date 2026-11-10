/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Concepts.SpectralFilter.PhaseReadout.CountedPhaseReflection
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath


namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib

def conversionPaddedInput {X : Type} {n : ℕ} (input : X → Fin n → Bool)
    (x : X) (j : Fin (n+1)) : Bool :=
  if h : j.val < n then input x ⟨j.val,h⟩ else false

noncomputable def conversionCleanEmbed (n r : ℕ) (hr : 0 < r)
    {H : Type} [Fintype H] [DecidableEq H] (b : Bool) (ψ : QState H) :
    QState ((Fin (n+1) × Bool) × ((Bool × H) × Fin r)) :=
  TensorState (Ket (0,false)) (TensorState (TensorState (Ket b) ψ) (Ket ⟨0,hr⟩))

noncomputable def conversionPrecisionPrice (ε : ℝ) : ℕ :=
  Nat.ceil (1 / ε^2) * (Nat.ceil (Real.log (2 / ε)) + 1)

end Qatlib.Concepts.GramQueryCore.LowerBoundTools
