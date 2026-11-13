/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Net

/-!
# Replacing generators in a represented net

This module specializes the net-replacement estimate to generator error `ε / (2 * N.bound)`. An
`ε / 2` net represented by words with a positive uniform length bound becomes an `ε` net after
replacing each generator by a sufficiently close linear isometry. See [AharonovArad2011].

## Main statements

* `lemma51_net_construction`: constructs the enlarged-error net from generator approximations.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults

open Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An `ε / 2` net represented by words of length at most the positive bound `N.bound` becomes
an `ε` net when every generator is replaced within `ε / (2 * N.bound)`. See [Aharonov and
Arad, Lemma 5.1][AharonovArad2011]. -/
theorem lemma51_net_construction {ι : Type*} (ρhat ρ : ι → E ≃ₗᵢ[ℂ] E)
    (N : RepresentedNet ρhat) (ε : ℝ) (hε : 0 < ε)
    (hN : IsEpsNet N.carrier (ε / 2)) (hd : 0 < N.bound)
    (hgen : ∀ i, FunDistLE (ρ i) (ρhat i) (ε / (2 * N.bound))) :
    IsEpsNetFun (replacedNet ρ N) ε :=
  lemma51_net_replacement ρhat ρ N ε (ε / (2 * N.bound)) hε
    (by positivity) hN hd le_rfl hgen

end Qatlib.Papers.BQPJonesPoly06.MainResults
