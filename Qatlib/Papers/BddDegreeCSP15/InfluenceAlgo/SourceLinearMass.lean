/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BddDegreeCSP15.FourierTools.SourceModel

@[expose] public section


/-!
# BddDegreeCSP15 — Lemma 4.3, proved linear-mass step (Block `InfluenceAlgo`)

Fixed source: arXiv:1505.03424v2, Lemma 4.3 (p. 9), first proof step.

Here the sign choice `xᵢ = sign(ĝ({i}))` makes
the linear Fourier part equal the `L¹` mass.  The full Lemma 4.3 is not
migrated: its legacy statement quantifies over the paper-level
`RandomizedAlgorithm` interface existentially after the instance
(which is not an operational algorithm model), and its residual pure-existence
core needs the DFKO biased-hypercontractivity machinery (deferred).
-/

set_option autoImplicit false

namespace Qatlib.Papers.BddDegreeCSP15.InfluenceAlgo

open scoped BigOperators
open Finset Qatlib.Papers.BddDegreeCSP15.FourierTools

/-- The sign choice `xᵢ = sign(ĝ({i}))` makes the linear Fourier part equal to the `L¹` mass:
`Σ_i ĝ({i})·sign(ĝ({i})) = Σ_i |ĝ({i})|`.  This is the first step of the proof of Lemma 4.3
(source p. 9). -/
theorem linear_part_sign_max (N k : ℕ) (p : BoolPoly N k) :
    (∑ i : Fin N, p.linearCoeff i * (if 0 ≤ p.linearCoeff i then (1 : ℝ) else -1))
      = ∑ i : Fin N, |p.linearCoeff i| := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 ≤ p.linearCoeff i
  · rw [ite_eq_left h, abs_of_nonneg h]; ring
  · rw [ite_eq_right h, abs_of_neg (by linarith)]; ring

end Qatlib.Papers.BddDegreeCSP15.InfluenceAlgo
