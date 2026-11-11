/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum
import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma7EigenSymmetryDefs

/-!
# Specification of discriminant eigenvalue symmetry

The proposition `SzegedyLemma7EigenSymmetry` states the eigenvector identity obtained by
negating the second source component. For any two finite frames, this transformation sends a
discriminant eigenvector at a real value `lam` to one at `-lam`. The quantum walk spectral
framework is developed in [Szegedy2004].

## Main statements

* `SzegedyLemma7EigenSymmetry`: The source sign flip identity for opposite eigenvalues.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SpectralFilter.BusySpectrum

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

/-- The requirement that `paperSourceFlip` sends a source eigenvector of the bipartite
discriminant with real eigenvalue `lam` to one with eigenvalue `-lam` [Szegedy, Lemma
7][Szegedy2004]. -/
def SzegedyLemma7EigenSymmetry : Prop :=
  ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
      (v : QState (I ⊕ J)) (lam : ℝ),
    bipartiteDiscriminant A B *ᵥ v = (lam : ℂ) • v →
    bipartiteDiscriminant A B *ᵥ paperSourceFlip v = (-(lam : ℂ)) • paperSourceFlip v

end Qatlib.Concepts.WalkSearch.FrameSpectral
