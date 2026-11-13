/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkGraphs00.MainResults.Core
import Qatlib.Papers.QWalkGraphs00.MainResults.Times
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The coined quantum walk on the odd cycle (Theorems 4.1, 4.2 and 5.3)

Fixed source: arXiv:quant-ph/0012090v2 (25 May 2002), Aharonov–Ambainis–Kempe–Vazirani,
*Quantum Walks On Graphs*.

This module models the walk of Section 4: nodes are `ZMod n` (the `n`-cycle), the coin is
`Fin 2` with the Hadamard matrix, and one step is "Hadamard on the coin, then shift the node
by `+1` for coin state `0` and by `-1` for coin state `1`".

Scope note: this module formalizes the walk operator. The analytic results of
Section 4 (Theorem 4.1: uniform limiting distribution for odd `n`; Theorem 4.2: mixing
time `O(n log n / ε³)`) and the amplified bounds of Theorem 5.3 are outside its scope.
Their proofs use a Fourier/character basis of `cycleStep`, the eigenvalue spacing
estimates of Claims 4.5–4.10, and the spectral error bound of Lemma 4.3.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkGraphs00.MainResults.Cycle

open Qatlib.Papers.QWalkGraphs00.MainResults

open scoped BigOperators Matrix Topology
open Filter
open Qatlib.Papers.QWalkGraphs00.MainResults.Core
open Qatlib.Papers.QWalkGraphs00.MainResults.Times

/-- The `2 × 2` Hadamard coin matrix `(1/√2) [[1,1],[1,-1]]` used in Section 4 of the paper. -/
def hadamardCoin : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 2 : ℂ)⁻¹;
     (Real.sqrt 2 : ℂ)⁻¹, -((Real.sqrt 2 : ℂ)⁻¹)]

/-- The walk operator on the `n`-cycle with the Hadamard coin: apply the Hadamard coin, then
move the node by `+1` if the (post-coin) coin state is `0` and by `-1` if it is `1`
(Section 4 of the paper, `U = S · (H ⊗ I)` on the cycle). -/
def cycleStep (n : ℕ) [NeZero n] : Matrix (Fin 2 × ZMod n) (Fin 2 × ZMod n) ℂ :=
  fun p q =>
    hadamardCoin p.1 q.1 *
      (if p.2 = q.2 + (if p.1 = 0 then (1 : ZMod n) else -1) then (1 : ℂ) else 0)

/-- The uniform distribution on the nodes of the `n`-cycle, `π(v) = 1/n`. -/
def uniformDist (n : ℕ) [NeZero n] : ZMod n → ℝ := fun _ => (Fintype.card (ZMod n) : ℝ)⁻¹


end Qatlib.Papers.QWalkGraphs00.MainResults.Cycle
