/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic
public import Qatlib.Papers.TensorPCA19.MainResults.Model.SpectralModel
public import Qatlib.Papers.TensorPCA19.MainResults.Model.TensorPCAConfig
public import Qatlib.Papers.TensorPCA19.MainResults.Source.Detection
public import Qatlib.Papers.TensorPCA19.MainResults.Source.Recovery
public import Qatlib.Papers.TensorPCA19.MainResults.Source.RecoverySampling

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open MeasureTheory
open scoped BigOperators

open Qatlib.Papers.TensorPCA19.MainResults

open Qatlib.Papers.TensorPCA19.MainResults.Detection

open Qatlib.Papers.TensorPCA19.MainResults.GaussianSpectralModel

open Qatlib.Papers.TensorPCA19.MainResults.SpectralDecomposition

open Qatlib.Papers.TensorPCA19.MainResults.SpikedTensor

namespace Qatlib.Papers.TensorPCA19.MainResults

section

/-- The `A` of the Lemma 4 exponent (p.12, Eq. (26)):
`(J/2) · n_bos^{p/2} · N^{p/2}`. -/
def Aeven (s : SpikedTensor) : ℝ :=
  (Jval s / 2) * (s.nbos : ℝ) ^ ((s.p : ℝ) / 2) * (s.N : ℝ) ^ ((s.p : ℝ) / 2)

/-- The `A` of the odd-`p` exponent (Lemma 6 at order `2(p−1)`, p.17):
`J · n_bos^{p−1} · N^p`. -/
def Aodd (s : SpikedTensor) : ℝ :=
  JvalOdd s * (s.nbos : ℝ) ^ ((s.p : ℝ) - 1) * (s.N : ℝ) ^ (s.p : ℝ)

end

end Qatlib.Papers.TensorPCA19.MainResults
