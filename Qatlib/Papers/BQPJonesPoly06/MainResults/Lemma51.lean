/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Net
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults

open Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem lemma51_net_construction {ι : Type*} (ρhat ρ : ι → E ≃ₗᵢ[ℂ] E)
    (N : RepresentedNet ρhat) (ε : ℝ) (hε : 0 < ε)
    (hN : IsEpsNet N.carrier (ε / 2)) (hd : 0 < N.bound)
    (hgen : ∀ i, FunDistLE (ρ i) (ρhat i) (ε / (2 * N.bound))) :
    IsEpsNetFun (replacedNet ρ N) ε :=
  lemma51_net_replacement ρhat ρ N ε (ε / (2 * N.bound)) hε
    (by positivity) hN hd le_rfl hgen

end Qatlib.Papers.BQPJonesPoly06.MainResults
