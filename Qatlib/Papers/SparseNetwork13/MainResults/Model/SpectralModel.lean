/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseNetwork13.MainResults.Model.ElectricalNetwork

set_option backward.isDefEq.respectTransparency false

/-!
# SparseNetwork13 — spectral model (§2.2, §4.1)

Fixed source: Guoming Wang, *Efficient Quantum Algorithms for Analyzing Large Sparse
Electrical Networks*, arXiv:1311.1851 **v10 (24 Jul 2017)**.

The paper's spectral quantities `λ₂(L_G)` and `λ₂(L̄_G)` (p.5, Eq. (12)--(13)) are the
*second-smallest* eigenvalues, equivalently the minimum of the Rayleigh quotient over the
vectors orthogonal to the constant vector (for `L_G`) resp. orthogonal to `D_G^{1/2}|1⟩`
(for the normalised Laplacian `L̄_G`).  We encode them variationally, so the paper's
statements become statements about `sInf` of a Rayleigh-quotient set, avoiding any need for
matrix-eigenvalue-order API.

We also model the modified network `G′` of §4.1 (p.19): `C_{G′} = C_G + |φ_{e₀}⟩⟨e₀|` with
`|φ_{e₀}⟩ = −√(2λ)|i_ext⟩` (Eq. (86)), so that

  `L_{G′} = C_{G′}C_{G′}ᵀ = L_G + 2λ·|i_ext⟩⟨i_ext|`,   (cf. Eq. (89))

and `D_{G′} = D_G + λ·I` (weighted degree `deg(v)+λ`, Eq. (88)).

Everything here is definitional; this module carries no `sorry`.
-/

set_option autoImplicit false
noncomputable section

open Matrix BigOperators

namespace Qatlib.Papers.SparseNetwork13.MainResults.Model

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Rayleigh quotient `⟨x, A x⟩ / ⟨x, x⟩` of a real matrix `A` at a vector `x`
(p.6, the quantity minimised in Eq. (14)). -/
def rayleigh (A : Matrix V V ℝ) (x : V → ℝ) : ℝ :=
  dotProduct x (A *ᵥ x) / dotProduct x x

/-- The Rayleigh quotients of the non-zero vectors of a set `S`. -/
def rayleighRange (A : Matrix V V ℝ) (S : Set (V → ℝ)) : Set ℝ :=
  rayleigh A '' (S \ {0})

/-- The minimum Rayleigh quotient of `A` over the non-zero vectors of `S` (an `sInf`,
so that the paper's `λ₂` is this quantity for the appropriate subspace). -/
def rayleighMinOver (A : Matrix V V ℝ) (S : Set (V → ℝ)) : ℝ :=
  sInf (rayleighRange A S)

/-- Vectors orthogonal (in the unweighted sense) to the all-ones vector `|1⟩`, i.e.
`∑_v x_v = 0` (§2.2, the constraint in Eq. (14)). -/
def constantOrthogonal : Set (V → ℝ) := {x | ∑ v, x v = 0}

/-- Vectors orthogonal to `D_G^{1/2}|1⟩`, i.e. `∑_v √(deg v)·x_v = 0`; the correct
constraint for the Rayleigh quotient of `L̄_G = D_G^{-1/2}L_G D_G^{-1/2}` (p.20). -/
def degreeOrthogonal (G : ElecNetwork V E) : Set (V → ℝ) :=
  {x | ∑ v, Real.sqrt (weightedDegree G v) * x v = 0}

/-- `λ₂(L_G)`: the spectral gap of the combinatorial Laplacian (Eq. (12)). -/
def lambda2 (G : ElecNetwork V E) : ℝ :=
  rayleighMinOver (laplacian G) constantOrthogonal

/-- `λ₂(L̄_G)`: the spectral gap of the normalised Laplacian (Eq. (13)). -/
def lambda2Normalized (G : ElecNetwork V E) : ℝ :=
  rayleighMinOver (normalizedLaplacian G) (degreeOrthogonal G)

/-- The Laplacian `L_{G′} = L_G + 2λ|i_ext⟩⟨i_ext|` of the modified network of §4.1
(p.19, Eq. (89)): since `|φ_{e₀}⟩⟨φ_{e₀}| = 2λ|i_ext⟩⟨i_ext|` and `C_G e₀ = 0`, adding the
special hyperedge of weight `λ` contributes exactly this rank-one term. -/
def modifiedLaplacian (G : ElecNetwork V E) (lam : ℝ) (iext : V → ℝ) : Matrix V V ℝ :=
  laplacian G + Matrix.of (fun u v => 2 * lam * (iext u * iext v))

/-- The normalised Laplacian `L̄_{G′}` of the modified network: `L_{G′}` normalised by the
modified weighted-degree matrix `D_{G′} = D_G + λ·I` (Eq. (90),(88)). -/
def normalizedModifiedLaplacian (G : ElecNetwork V E) (lam : ℝ) (iext : V → ℝ) :
    Matrix V V ℝ :=
  fun u v =>
    if 0 < weightedDegreeMod G lam u ∧ 0 < weightedDegreeMod G lam v then
      modifiedLaplacian G lam iext u v
        / Real.sqrt (weightedDegreeMod G lam u * weightedDegreeMod G lam v)
    else 0

/-- Vectors orthogonal to `D_{G′}^{1/2}|1⟩` for the modified network. -/
def degreeModOrthogonal (G : ElecNetwork V E) (lam : ℝ) : Set (V → ℝ) :=
  {x | ∑ v, Real.sqrt (weightedDegreeMod G lam v) * x v = 0}

/-- `λ₂(L̄_{G′})`: the spectral gap of the modified normalised Laplacian (used in
Lemma 7 and Lemma 11, §4.1--§4.2). -/
def lambda2NormalizedMod (G : ElecNetwork V E) (lam : ℝ) (iext : V → ℝ) : ℝ :=
  rayleighMinOver (normalizedModifiedLaplacian G lam iext) (degreeModOrthogonal G lam)

/-- Unfold the definition of `rayleighRange`. -/
@[simp] theorem rayleighRange_def (A : Matrix V V ℝ) (S : Set (V → ℝ)) :
    rayleighRange A S = rayleigh A '' (S \ {0}) := rfl

end Qatlib.Papers.SparseNetwork13.MainResults.Model
