/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumLWE25.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# QuantumLWE25 — integer-lattice vocabulary shared by the CVP/DGS layer

Fixed arXiv:2310.00644v2.

The paper's lattice statements (Lemmas 50, 64, 66, 72, 73 and Theorems 60–68) quantify over
`n`-dimensional integer lattices `L ⊆ ℝ^n` and their duals `L*`. The library has no lattice
theory, so we represent a lattice by an integer basis matrix `B` and its points by integer
coordinate vectors `k : Fin n → ℤ`; a dual lattice is represented by a rational basis matrix.
This keeps every Gaussian sum a countable `∑'` over an encodable index type (`Fin n → ℤ`),
which is what Lean's `tsum` supports — a `tsum` over `ℝ^n` itself would be junk (Lean assigns
it the value `0`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumLWE25.MainResults

open scoped BigOperators Matrix
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- The lattice point `B·k ∈ ℤ^n` of the integer lattice spanned by the rows/columns of `B`. -/
def latticePointZ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Fin n → ℤ) : Fin n → ℤ :=
  fun i => ∑ j, k j * B j i

/-- The real vector underlying `latticePointZ`. -/
def latticePointR {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Fin n → ℤ) : Fin n → ℝ :=
  fun i => (latticePointZ B k i : ℝ)

/-- The point of the dual lattice spanned by the rational basis `B`. -/
def dualPointR {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (k : Fin n → ℤ) : Fin n → ℝ :=
  fun i => ∑ j, (k j : ℝ) * (B j i : ℝ)

/-- Euclidean norm on `ℝ^n`. -/
def vecNormR {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- Euclidean distance on `ℝ^n`. -/
def vecDistR {n : ℕ} (x y : Fin n → ℝ) : ℝ := vecNormR (fun i => x i - y i)

/-- The Euclidean inner product on `ℝ^n`. -/
def innerR {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i

/-- The paper's one-dimensional Gaussian `ρ_s(d) = exp(-π d²/s²)`. -/
def gaussScalar (s d : ℝ) : ℝ := Real.exp (-(Real.pi * d ^ 2 / s ^ 2))

/-- `∑_{v ∈ L} f(v)`, summed over the integer coordinates of a lattice with basis `B`. -/
def latticeSumR {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑' k : Fin n → ℤ, f (latticePointR B k)

/-- `∑_{x ∈ L*} f(x)`, summed over the integer coordinates of a dual lattice with rational
basis `B`. -/
def dualSumR {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑' k : Fin n → ℤ, f (dualPointR B k)

/-- The (unnormalized) discrete Gaussian state `|D_{L,r}⟩ = ∑_{v∈L} ρ_r(v)|v⟩`, indexed by
integer coordinates. -/
def gaussianLatticeState {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℝ) :
    QState (Fin n → ℤ) :=
  fun k => (gaussianWeightVec r (latticePointR B k) : ℂ)

/-- The discrete Gaussian state `|D_{L,r}⟩ = ∑_{v∈L} ρ_r(v)|v⟩` at precision `R`: the
finite register `(Z_R)^n` records `v mod R`, matching the paper's states on `L/R`
(Definition 47 and Theorem 56, where `R` is the precision parameter). This finite
representation is what allows the paper's trace-distance comparisons to be stated. -/
def gaussianLatticeStateMod {n R : ℕ} [NeZero R] (B : Matrix (Fin n) (Fin n) ℤ) (r : ℝ) :
    QState (Fin n → ZMod R) := by
  classical
  exact fun y => ∑' k : Fin n → ℤ,
    if (∀ i, ((latticePointZ B k i : ℤ) : ZMod R) = y i) then
      (gaussianWeightVec r (latticePointR B k) : ℂ) else 0

/-- `(Aᵀ v)_j` for `A : Z_q^{n×m}` and `v : Z_q^n`. -/
def matVecT {n m q : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q)) (v : Fin n → ZMod q) :
    Fin m → ZMod q :=
  fun j => ∑ i, A i j * v i

/-- Reduction of a real number to `ZMod q` through its integer part (used to place the phase
`⟨x', v⟩` into the `Z_q` register of the `S|LWE⟩^phase` state). -/
def realToZMod (q : ℕ) [NeZero q] (w : ℝ) : ZMod q := ((Int.floor w : ℤ) : ZMod q)

end Qatlib.Papers.QuantumLWE25.MainResults
