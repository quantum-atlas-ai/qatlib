/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DQIQuadOpt25.MainResults.Source.PaperModel
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Complex.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# DQIQuadOpt25 — procedure and decoding model

Fixed arXiv:2510.08061v2.  This module supplies the lightweight algorithmic
layer used to phrase the "efficiently prepares" and "efficient decoding
scheme" hypotheses of Theorems 1–2:

* `StateProcedure p n` records the amplitude vector produced by a preparation
  procedure together with a declared resource count (number of elementary
  operations); `PreparesIn ψ T` asserts that some procedure produces exactly
  the vector `ψ` within `T` elementary operations.  This is the same declared
  resource accounting as the `Procedure`/`PreparesIn` model used in other
  paper layers of this repository;
* `syndrome D` is the parity-check map `y ↦ Dᵀy = ∑_i D_{ij} y_i` whose columns
  are the constraint matrices' diagonals in Algorithm 1 (Step 5);
* `hammingWeight` is the Hamming weight of an error vector;
* `EfficientDecoder p m n ℓ D` is a single-valued decoder for the syndrome map
  `syndrome D`, correct on all error vectors of weight at most `ℓ`, with a
  declared classical cost; `HasEfficientDecoder D` states that such a decoder
  exists with polynomially bounded cost.  This is the paper's "parity-check
  matrix that has an efficient decoding scheme".

Boundary: neither gates nor a circuit compiler, oracle tapes or classical
preprocessing machines are modelled; `StateProcedure` only fixes the produced
state and the declared cost, exactly as stated in the docstring of the theorem
that uses it.  Correctness of the decoder is only asserted on errors of weight
`≤ ℓ` (Algorithm 1, Step 6); this matches the paper's usage inside the
degree-`ℓ` DQI state, where only error strings of weight `≤ ℓ` appear.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.DQIQuadOpt25.MainResults.Source

/-- A lightweight state-preparation procedure: the produced amplitude vector
and a declared resource count (number of elementary operations).  Circuit
implementability is not part of this structure (see the module note). -/
structure StateProcedure (p n : ℕ) where
  /-- The amplitude vector produced by the procedure. -/
  state : (Fin n → ZMod p) → ℂ
  /-- Declared resource count of the procedure. -/
  cost : ℕ

/-- `PreparesIn ψ T` asserts that some preparation procedure produces exactly
the amplitude vector `ψ` with resource count at most `T`. -/
def PreparesIn {p n : ℕ} (ψ : (Fin n → ZMod p) → ℂ) (T : ℕ) : Prop :=
  ∃ Q : StateProcedure p n, Q.state = ψ ∧ Q.cost ≤ T

/-- Hamming weight of a vector over `F_p`. -/
def hammingWeight {p n : ℕ} (y : Fin n → ZMod p) : ℕ :=
  (Finset.univ.filter fun j => y j ≠ 0).card

/-- The parity-check syndrome map `y ↦ Dᵀy = ∑_i D_{ij}y_i` of Algorithm 1,
Step 5: column `i` of `D` is the diagonal of the constraint matrix `C_i`. -/
def syndrome {p m n : ℕ} (D : Fin m → Fin n → ZMod p) (y : Fin m → ZMod p) :
    Fin n → ZMod p :=
  fun j => ∑ i, D i j * y i

/-- A single-valued decoder for the syndrome map `syndrome D`, correct on all
error vectors of Hamming weight at most `ℓ`, with a declared classical cost.
This is the paper's "efficient decoding scheme" for the parity-check matrix
whose columns are the diagonals of the `C_i`. -/
structure EfficientDecoder (p m n ℓ : ℕ) (D : Fin m → Fin n → ZMod p) where
  /-- The classical decoding function. -/
  decode : (Fin n → ZMod p) → (Fin m → ZMod p)
  /-- Correctness on errors of weight at most `ℓ` (the weight range occurring
  in the degree-`ℓ` DQI state). -/
  correct : ∀ y : Fin m → ZMod p, hammingWeight y ≤ ℓ → decode (syndrome D y) = y
  /-- Declared classical cost of one decoding call. -/
  cost : ℕ

/-- The parity-check matrix `D` has an efficient decoding scheme: a decoder
correct on errors of weight `≤ ℓ` whose declared cost is polynomial in the
instance size `m + n`. -/
def HasEfficientDecoder {p m n ℓ : ℕ} (D : Fin m → Fin n → ZMod p) : Prop :=
  ∃ dec : EfficientDecoder p m n ℓ D, ∃ c : ℕ, dec.cost ≤ (m + n + 1) ^ c + 1

end Qatlib.Papers.DQIQuadOpt25.MainResults.Source
