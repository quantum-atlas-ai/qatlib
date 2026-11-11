/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# ResolventQPE24 — shared paper-layer vocabulary

Fixed arXiv:2410.04837 (Alase–Karuvade, *Resolvent-based quantum phase
estimation: Towards estimation of parametrized eigenvalues*), Version 1
as retrieved from `assets/2410.04837.pdf`.

This file only fixes the notation used by the claim files of the block
`ResolventQPE24.MainResults`: Jordan blocks and Jordan decompositions, the
resolvent, the two restricted Kreiss constants of Definition 2.10, the
Riemann sum of Definition 2.2, the additive parametric quantum approximation
(APQA) of Definition 3.1, the resolvent-state coefficient vectors of
Eqs. (45) and (112), and the system matrices `M` of Eqs. (42)/(109).

The definitions are stated at the mathematical level of the paper.  Circuit
synthesis, query ledgers and QLSA compilation are *not* modelled here; the
complexity statements of the claim files are therefore stated as bounds on
explicit query-count expressions (see the individual docstrings).  This
boundary is recorded per claim and must not be read as a proof of a circuit
claim.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ResolventQPE24.MainResults.Prelude

/-! ## Jordan blocks, Definition/Proposition 2.4-2.5, p. 7 -/

/-- The Jordan block `J(λ, d)` of Prop. 2.4, Eq. (13): `λ` on the diagonal
and `1` on the subdiagonal, zero elsewhere. -/
def jordanBlock (lam : ℂ) (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => if i = j then lam else if (j.1 + 1 = i.1) then 1 else 0

/-- The block-diagonal matrix of Prop. 2.4, Eq. (13), attached to the block
sizes `d l` and eigenvalues `λ l`. -/
def jordanBlockDiagonal {s : ℕ} (lam : Fin s → ℂ) (d : Fin s → ℕ) :
    Matrix (Σ l, Fin (d l)) (Σ l, Fin (d l)) ℂ :=
  Matrix.blockDiagonal' fun l => jordanBlock (lam l) (d l)

/-- `C` admits the Jordan decomposition `C = T J T⁻¹` of Prop. 2.4, with `J`
block diagonal with blocks `J(λ l, d l)` and the block sizes summing (through
the reindexing `e`) to `N`. -/
def HasJordanDecomposition (N : ℕ) (C : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∃ (s : ℕ) (d : Fin s → ℕ) (lam : Fin s → ℂ) (e : Fin N ≃ Σ l, Fin (d l))
    (T : Matrix (Fin N) (Fin N) ℂ),
    (∀ l, 0 < d l) ∧ T.det ≠ 0 ∧
      C = T * (jordanBlockDiagonal lam d).submatrix e e * T⁻¹

/-- Largest Jordan block size of a given decomposition. -/
def maxBlockSize {s : ℕ} (d : Fin s → ℕ) : ℕ := Finset.univ.sup d

/-! ## Resolvent, Kreiss constants (Def. 2.10, Eqs. (25)-(26)) -/

/-- The resolvent `R(z) = (z·1 - C)⁻¹`. -/
def resolvent {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ := (z • 1 - C)⁻¹

/-- Restricted Kreiss constant with respect to the line `Re z = δ`,
Def. 2.10 Eq. (25): `K_δ(C) = δ sup_y ‖((δ + i y)·1 - C)⁻¹‖`. -/
def kreissStrip {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (δ : ℝ) : ℝ :=
  δ * sSup (Set.range fun y : ℝ => ‖resolvent C ((δ : ℂ) + Complex.I * y)‖)

/-- Restricted Kreiss constant with respect to the circle `|z| = 1 + δ`,
Def. 2.10 Eq. (26): `K_δ°(C) = δ sup_{|z|=1+δ} ‖(z·1 - C)⁻¹‖`. -/
def kreissCircle {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (δ : ℝ) : ℝ :=
  δ * sSup (Set.range fun θ : ℝ =>
    ‖resolvent C ((1 + δ : ℂ) * Complex.exp (Complex.I * θ))‖)

/-! ## Riemann sum, Definition 2.2 Eq. (9) and Lemma 2.3, p. 6 -/

/-- The Riemann sum of Def. 2.2, Eq. (9):
`∑_{tmin}^{tmax}[f,N] = (1/N) ∑_{j=⌈N tmin⌉}^{⌊N tmax⌋} f(j/N)`. -/
def riemannSum (f : ℝ → ℂ) (N : ℕ) (tmin tmax : ℝ) : ℂ :=
  ((N : ℂ)⁻¹) * ∑ j ∈ Finset.Icc (⌈(N : ℝ) * tmin⌉ : ℤ) (⌊(N : ℝ) * tmax⌋ : ℤ),
    f ((j : ℝ) / (N : ℝ))

/-! ## State norms and the APQA projector, Definition 3.1 Eq. (37)-(38) -/

/-- The squared Euclidean norm `‖|v⟩‖²` of a state vector `v`. -/
def stateNormSq {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := ∑ j, ‖v j‖ ^ 2

/-- Squared norm of the projected vector `P |v⟩` for a diagonal projector `P`. -/
def projectedNormSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ := stateNormSq (P.mulVec v)

/-- The projector `P_{λ,ε}` of Eq. (38): the diagonal projector onto the
computational-basis states `j` with `|j/2^a - γ⁻¹(λ)| ≤ ε`. -/
def apqaProjector (a : ℕ) (γinv : ℂ → ℝ) (lam : ℂ) (ε : ℝ) :
    Matrix (Fin (2 ^ a)) (Fin (2 ^ a)) ℂ :=
  Matrix.diagonal fun j =>
    if |((j : ℝ) / ((2 : ℝ) ^ a)) - γinv lam| ≤ ε then (1 : ℂ) else 0

/-- The orthogonal-complement projector `Q_{λ,ε} = 1 - P_{λ,ε}` of Eq. (38). -/
def apqaComplement (a : ℕ) (γinv : ℂ → ℝ) (lam : ℂ) (ε : ℝ) :
    Matrix (Fin (2 ^ a)) (Fin (2 ^ a)) ℂ :=
  1 - apqaProjector a γinv lam ε

/-- The resolvent-state ancilla coefficient vector `|φ̃_{λ,δ}⟩` of Eq. (45),
for the unimodular problem (curve `γ(t) = e^{2πit}`, `z_j = (1+δ)γ(j/2^a)`). -/
def phiUnimodular (lam : ℂ) (δ : ℝ) (a : ℕ) : Fin (2 ^ a) → ℂ :=
  fun j =>
    (Real.sqrt (δ * (2 + δ) / ((2 : ℝ) ^ a)) : ℂ) *
      ((1 + δ : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((j : ℝ) / ((2 : ℝ) ^ a))) - lam)⁻¹

/-- The curve `γ(t) = ρ(2t - 1)` of Problem 4.1, Eq. (107). -/
def gammaReal (ρ t : ℝ) : ℝ := ρ * (2 * t - 1)

/-- The resolvent-state ancilla coefficient vector `|φ̃_{λ,δ}⟩` of Eq. (112),
for the real-eigenvalue problem (`z_j = γ(j/2^a) + iδ`). -/
def phiReal (lam : ℂ) (δ ρ : ℝ) (a : ℕ) : Fin (2 ^ a) → ℂ :=
  fun j =>
    (Real.sqrt ((ρ * δ) / ((2 : ℝ) ^ (a - 1) * Real.pi)) : ℂ) *
      (((gammaReal ρ ((j : ℝ) / ((2 : ℝ) ^ a)) : ℂ) + Complex.I * δ) - lam)⁻¹

/-- The integrand `g_l` of Lemma 3.8, Eq. (50). -/
def gUnimodular (lam : ℂ) (δ t : ℝ) : ℝ :=
  δ * (2 + δ) / ‖(1 + δ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t) - lam‖ ^ 2

/-- The integrand `f_l` of Lemma 4.7, Eq. (117). -/
def fReal (lam : ℂ) (δ ρ t : ℝ) : ℝ :=
  2 * ρ * δ / (Real.pi * ((gammaReal ρ t - lam.re) ^ 2 + δ ^ 2))

/-! ## The system matrices `M` of Eqs. (42)/(109) -/

/-- The matrix `M = Z ⊗ 1 - 1 ⊗ A` of Eq. (42)/(109), written block
diagonally as `⨁_j (z_j·1 - A)`.  This is `Z ⊗ 1 - 1 ⊗ A` after the
canonical reindexing of the ancilla/product basis. -/
def systemMatrix {n a : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : Fin (2 ^ a) → ℂ) :
    Matrix (Σ _j : Fin (2 ^ a), Fin n) (Σ _j : Fin (2 ^ a), Fin n) ℂ :=
  Matrix.blockDiagonal' fun j => (z j • (1 : Matrix (Fin n) (Fin n) ℂ) - A)

/-- The system matrix of the QEUE problem, Def. 3.3 and Eq. (42). -/
def unimodularSystem {n a : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ) :
    Matrix (Σ _j : Fin (2 ^ a), Fin n) (Σ _j : Fin (2 ^ a), Fin n) ℂ :=
  systemMatrix A fun j =>
    (1 + δ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((j : ℝ) / ((2 : ℝ) ^ a)))

/-- The system matrix of the QERE problem, Def. 4.2 and Eq. (109). -/
def realSystem {n a : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (δ ρ : ℝ) :
    Matrix (Σ _j : Fin (2 ^ a), Fin n) (Σ _j : Fin (2 ^ a), Fin n) ℂ :=
  systemMatrix A fun j =>
    (gammaReal ρ ((j : ℝ) / ((2 : ℝ) ^ a)) : ℂ) + Complex.I * δ

/-! ## Query-count expressions used by the complexity claims -/

/-- Query count of one QLSA call (Lemma 2.14, Eq. (31)) with block-encoding
normalization `αC` and inverse-norm bound `αInv`: `αC · αInv · log(1/ε)`.
All multiplicative constants are suppressed, as in the paper's `O(·)`. -/
def qlsaQueryBound (αC αInv ε : ℝ) : ℝ := αC * αInv * Real.log (1 / ε)

/-- The QEUE query count of Eq. (91): `α_A κ_S⁴ K_δ°(A) / (ε_eig ε_st²)
· log(1/ε_st)`. -/
def qeueQueryBound (αA κS Kδ εeig εst : ℝ) : ℝ :=
  αA * κS ^ 4 * Kδ / (εeig * εst ^ 2) * Real.log (1 / εst)

/-- The QERE query count of Eq. (146): `α_A κ_S⁴ K_δ(-iA) / (ε_eig ε_st²)
· log(1/ε_st)`. -/
def qereQueryBound (αA κS Kδ εeig εst : ℝ) : ℝ :=
  αA * κS ^ 4 * Kδ / (εeig * εst ^ 2) * Real.log (1 / εst)

/-- The expectation-value-estimation query count of Proposition 2.15,
Eq. (35): `(α_A / ε_eig) · log(1/p_fail)`. -/
def expectationEstimationQueryBound (αA εeig pfail : ℝ) : ℝ :=
  αA / εeig * Real.log (1 / pfail)

end Qatlib.Papers.ResolventQPE24.MainResults.Prelude
