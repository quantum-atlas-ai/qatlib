/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma5NormBoundStat
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws

/-!
# Contraction of the bipartite discriminant

This module proves the squared Euclidean norm contraction of the cross-frame map `Aᴴ * B` for
isometric frames. The theorem `szegedyLemma5NormBound` applies the resulting estimate to the
bipartite discriminant and identifies the common frame image for a +1 source eigenvector. The
quantum walk spectral framework is developed in [Szegedy2004].

## Main statements

* `cross_contract`: Squared norm contraction of the cross-frame matrix.
* `szegedyLemma5NormBound`: Discriminant contraction and the +1 equality property.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

/-- For isometric frames `A` and `B`, applying `Aᴴ * B` cannot increase the sum of squared
coordinate norms. -/
private theorem cross_contract {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) (hA : IsIsometry A)
    (hB : IsIsometry B) (v : QState J) :
    ∑ i, ‖((Aᴴ*B)*ᵥv) i‖^2 ≤ ∑ j, ‖v j‖^2 := by
  have hn : ‖Aᴴ*B‖ ≤ 1 := by
    calc
      ‖Aᴴ*B‖ ≤ ‖Aᴴ‖ * ‖B‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1*1 := mul_le_mul (by rw [Matrix.l2_opNorm_conjTranspose]; exact isometry_norm_le hA)
        (isometry_norm_le hB) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  have hv := Matrix.l2_opNorm_mulVec (Aᴴ*B) (toEuclidean_fromVec v)
  have hv' : ‖toEuclidean_fromVec ((Aᴴ*B)*ᵥv)‖ ≤ ‖toEuclidean_fromVec v‖ :=
    hv.trans (by simpa using! mul_le_mul_of_nonneg_right hn (norm_nonneg (toEuclidean_fromVec v)))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hv' 2
  simpa only [norm_toEuclidean_fromVec_sq] using! hs

/-- For isometric frames, the bipartite discriminant contracts the squared Euclidean norm, and
every +1 source eigenvector has equal images under the two frames [Szegedy, Lemma
5][Szegedy2004]. -/
theorem szegedyLemma5NormBound : SzegedyLemma5NormBound := by
  intro H I J _ _ _ _ _ _ A B hA hB
  constructor
  · intro x
    have hd : bipartiteDiscriminant A B *ᵥ x =
        Sum.elim ((Aᴴ*B)*ᵥ(fun j => x (.inr j)))
          ((Bᴴ*A)*ᵥ(fun i => x (.inl i))) := by
      simp only [bipartiteDiscriminant, Matrix.fromBlocks_mulVec,
        Matrix.zero_mulVec, zero_add, add_zero]
      rfl
    rw [hd, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have hb := cross_contract A B hA hB (fun j => x (.inr j))
    have ha := cross_contract B A hB hA (fun i => x (.inl i))
    linarith
  · intro a b h
    have hd : bipartiteDiscriminant A B *ᵥ Sum.elim a b =
        Sum.elim ((Aᴴ*B)*ᵥb) ((Bᴴ*A)*ᵥa) := by
      simp [bipartiteDiscriminant, Matrix.fromBlocks_mulVec]
    rw [hd] at h
    apply (two_isometry_intersection_gram_and_fixed I J H A B a b hA hB).1.mpr
    constructor
    · simpa only [Sum.elim_inl] using!
        congrArg (fun w : QState (I⊕J) => fun i => w (.inl i)) h
    · simpa only [Sum.elim_inr] using!
        congrArg (fun w : QState (I⊕J) => fun j => w (.inr j)) h

end Qatlib.Concepts.WalkSearch.FrameSpectral
