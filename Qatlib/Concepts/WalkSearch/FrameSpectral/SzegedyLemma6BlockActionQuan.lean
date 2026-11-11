/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma6BlockActionStat

/-!
# Off-diagonal action of the bipartite discriminant

The theorem `szegedyLemma6BlockAction` separates the two off-diagonal components of the
bipartite discriminant. If it sends `(a, b)` to `(a', b')`, then its action on each source
summand is obtained by retaining the opposite output component. The quantum walk spectral
framework is developed in [Szegedy2004].

## Main statements

* `szegedyLemma6BlockAction`: The two component identities for a discriminant image.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SpectralFilter.BusySpectrum

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

/-- If the bipartite discriminant sends `(a, b)` to `(a', b')`, it sends `(a, 0)` to `(0, b')`
and `(0, b)` to `(a', 0)` [Szegedy, Lemma 6][Szegedy2004]. -/
theorem szegedyLemma6BlockAction : SzegedyLemma6BlockAction := by
  intro H I J _ _ _ _ _ _ A B a a' b b' h
  have hd : bipartiteDiscriminant A B *ᵥ Sum.elim a b =
      Sum.elim ((Aᴴ*B)*ᵥb) ((Bᴴ*A)*ᵥa) := by
    simp [bipartiteDiscriminant, Matrix.fromBlocks_mulVec]
  have ha := congrArg (fun w : QState (I⊕J) => fun i => w (.inl i)) h
  have hb := congrArg (fun w : QState (I⊕J) => fun j => w (.inr j)) h
  simp only [hd, Sum.elim_inl] at ha
  simp only [hd, Sum.elim_inr] at hb
  constructor <;> simp [bipartiteDiscriminant, Matrix.fromBlocks_mulVec, ha, hb]

end Qatlib.Concepts.WalkSearch.FrameSpectral
