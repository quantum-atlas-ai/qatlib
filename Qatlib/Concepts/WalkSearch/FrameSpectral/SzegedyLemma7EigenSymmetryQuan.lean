/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma7EigenSymmetryStat

/-!
# Opposite eigenvalues of the bipartite discriminant

The theorem `szegedyLemma7EigenSymmetry` proves that the source sign flip exchanges the
discriminant eigenvalue `lam` with `-lam`. The statement uses only the off-diagonal block form
and does not require frame isometry. The quantum walk spectral framework is developed in
[Szegedy2004].

## Main statements

* `szegedyLemma7EigenSymmetry`: Source sign flip maps an eigenvector to the opposite eigenvalue.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib.Concepts.SpectralFilter.BusySpectrum

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

/-- If a source state is a discriminant eigenvector with real eigenvalue `lam`, its source sign
flip is an eigenvector with eigenvalue `-lam` [Szegedy, Lemma 7][Szegedy2004]. -/
theorem szegedyLemma7EigenSymmetry : SzegedyLemma7EigenSymmetry := by
  intro H I J _ _ _ _ _ _ A B v lam h
  have hd : bipartiteDiscriminant A B *ᵥ v =
      Sum.elim ((Aᴴ*B)*ᵥ(fun j => v (.inr j)))
        ((Bᴴ*A)*ᵥ(fun i => v (.inl i))) := by
    simp only [bipartiteDiscriminant, Matrix.fromBlocks_mulVec,
      Matrix.zero_mulVec, zero_add, add_zero]
    rfl
  have hf : bipartiteDiscriminant A B *ᵥ paperSourceFlip v =
      paperSourceFlip (-(bipartiteDiscriminant A B *ᵥ v)) := by
    rw [hd]
    rw [bipartiteDiscriminant, Matrix.fromBlocks_mulVec]
    simp only [paperSourceFlip, Sum.elim_comp_inl, Sum.elim_comp_inr,
      Matrix.zero_mulVec, zero_add, add_zero]
    rw [show (fun j => -v (.inr j)) = -(fun j => v (.inr j)) from rfl,
      Matrix.mulVec_neg]
    ext (i | j) <;> simp
  rw [hf, h]
  ext (i | j) <;> simp [paperSourceFlip]

end Qatlib.Concepts.WalkSearch.FrameSpectral
