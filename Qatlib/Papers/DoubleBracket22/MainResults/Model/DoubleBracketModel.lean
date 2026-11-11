/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option backward.isDefEq.respectTransparency false

/-!
# DoubleBracket22 — source model

Source: Marek Gluza, *Double-bracket quantum algorithms for diagonalization*,
arXiv:2206.11772v4 (8 Apr 2024), Quantum 2024-03-30. Fixed version v4.

The paper works with linear operators on `ℂ^{D}` (`D = 2^L`) equipped with the
Hilbert–Schmidt scalar product `⟨A,B⟩_HS = tr[A†B]` (Eq. (10)) and the induced
squared norm `‖A‖²_HS = tr[A†A]` (Eq. (11)). This file fixes the notation used by
every claim module of the paper layer:

* `commMat A B = A*B - B*A` — the bracket/commMat (Eq. (12));
* `diagPart A = diagonal (i ↦ A i i)` — the diagonal restriction `Δ`, i.e. the
  dephasing channel (Eq. (14));
* `offDiag A = A - diagPart A` — the off-diagonal restriction `σ` (Eq. (19));
* `hsInner A B = re tr[Aᴴ B]`, `hsNormSq A = hsInner A A` — (10), (11);
* `rotation s W J = e^{sW} J e^{-sW}` — a double-bracket rotation (Eq. (18)).

The *Frobenius* matrix norm (`Matrix.Norms.Frobenius`) is the Hilbert–Schmidt
norm; it is unitarily invariant, so every bound stated for the unitarily
invariant norm `‖·‖` in Appendix A holds for it, with the paper's constants.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.Frobenius BigOperators

namespace Qatlib.Papers.DoubleBracket22.MainResults.Model

/-- Paper fixed version. -/
def sourceVersion : String := "arXiv:2206.11772v4 (2024-04-08)"

/-- Square complex matrices of order `D`, the ambient space `L(ℂ^D)` of the paper. -/
abbrev Mat (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

/-- The bracket (commMat) `[A,B] = A B − B A`, Eq. (12). -/
def commMat {D : ℕ} (A B : Mat D) : Mat D := A * B - B * A

/-- The diagonal restriction `Δ` (dephasing channel), Eq. (14). -/
def diagPart {D : ℕ} (A : Mat D) : Mat D := Matrix.diagonal (fun i => A i i)

/-- The off-diagonal restriction `σ(A) = A − Δ(A)`, Eq. (19). -/
def offDiag {D : ℕ} (A : Mat D) : Mat D := A - diagPart A

/-- Hilbert–Schmidt scalar product `⟨A,B⟩_HS = tr[A†B]`, Eq. (10), as a real pairing
(the anti-Hermitian generators of the paper make the trace real). -/
def hsInner {D : ℕ} (A B : Mat D) : ℝ := ((Aᴴ * B).trace).re

/-- Squared Hilbert–Schmidt norm `‖A‖²_HS = tr[A†A]`, Eq. (11). -/
def hsNormSq {D : ℕ} (A : Mat D) : ℝ := hsInner A A

/-- A single double-bracket rotation `J_s = e^{sW} J e^{-sW}`, Eq. (18). -/
def rotation {D : ℕ} (s : ℝ) (W J : Mat D) : Mat D :=
  NormedSpace.exp (s • W) * J * NormedSpace.exp (-(s • W))

/-- The diagonal association bracket `W^(Z)(J) = [Δ^(Z)(J), J]`, Eq. (13). -/
def assocBracket {D : ℕ} (ΔZ : Mat D → Mat D) (J : Mat D) : Mat D := commMat (ΔZ J) J

/-- The canonical bracket `W^(can)(J) = [Δ(J), J]`, Eq. (15). -/
def canonicalBracket {D : ℕ} (J : Mat D) : Mat D := commMat (diagPart J) J

/-- A diagonal operator (paper: `D̂`), i.e. equal to its diagonal restriction. -/
def IsDiagonalOp {D : ℕ} (Dop : Mat D) : Prop := diagPart Dop = Dop

/-- Definition 1: a sequence of unitaries is `σ`-decreasing for `H₀` when the
off-diagonal HS norm strictly decreases at every step. -/
def SigmaDecreasing {D : ℕ} (H0 : Mat D) (Q : ℕ → Mat D) : Prop :=
  ∀ k : ℕ, ‖offDiag ((Q (k + 1))ᴴ * H0 * Q (k + 1))‖ < ‖offDiag ((Q k)ᴴ * H0 * Q k)‖

/-- One step of the diagonalization DBI with diagonal association `Λ` and step
duration `s` (abstract algorithm 1, Eqs. (1)–(2) with `D_k = Λ H_k`). -/
def dbiStep {D : ℕ} (Λ : Mat D → Mat D) (H : Mat D) (s : ℝ) : Mat D :=
  rotation s (commMat (Λ H) H) H

/-- The sequence of Hamiltonians produced by a DBI: `H_{k+1} = dbiStep Λ H_k s_k`. -/
def dbiSeq {D : ℕ} (Λ : Mat D → Mat D) (s : ℕ → ℝ) (H0 : Mat D) : ℕ → Mat D
  | 0 => H0
  | k + 1 => dbiStep Λ (dbiSeq Λ s H0 k) (s k)

/-- The unitary accumulated by `K` DBI steps (`H_k = U_k† H0 U_k`). -/
def dbiUnitary {D : ℕ} (Λ : Mat D → Mat D) (s : ℕ → ℝ) (H0 : Mat D) : ℕ → Mat D
  | 0 => 1
  | k + 1 => dbiUnitary Λ s H0 k *
      NormedSpace.exp (-(s k • commMat (Λ (dbiSeq Λ s H0 k)) (dbiSeq Λ s H0 k)))

/-- The dephasing pinching `Δ^(η)(A) = (1/R) Σ_k Ẑ_{η_k} A Ẑ_{η_k}†`, Eq. (200),
specialized to the scalar sign `(1/R) Σ_k (−1)^{η_k}` acting on a normalized
operator. -/
def pinchingSign (R : ℕ) (η : Fin R → Bool) : ℝ :=
  (1 / (R : ℝ)) * ∑ k, (if η k then (1 : ℝ) else -1)

/-- A unitary operator: `U†U = 1` and `UU† = 1`. -/
def IsUnitaryOp {D : ℕ} (U : Mat D) : Prop := Uᴴ * U = 1 ∧ U * Uᴴ = 1

/-- The gate-commMat (GCI) elemental component of Proposition 14, Eq. (171):
with `r = √(s/R)`, `Û^(GWW)_s(Ĵ) = (V̂^(∆)_r(Ĵ)†)^R e^{i√s Ĵ} (V̂^(∆)_r(Ĵ))^R e^{-i√s Ĵ}`. -/
def gciElement {D : ℕ} (Vpin : ℝ → Mat D) (R : ℕ) (s : ℝ) (J : Mat D) : Mat D :=
  let r : ℝ := Real.sqrt (s / (R : ℝ))
  (Vpin r)ᴴ ^ R * NormedSpace.exp ((Complex.I * (Real.sqrt s : ℂ)) • J) * (Vpin r) ^ R *
    NormedSpace.exp (-((Complex.I * (Real.sqrt s : ℂ)) • J))

/-- The `K`-step GWW GCI unitary approximating the flow at duration `ℓ`:
`V_0 = 1`, `V_{k+1} = V_k · Û^(GWW)_{ℓ/K}(Ĵ_k)` with `Ĵ_k = V_k† Ĥ0 V_k`
(abstract algorithm 2 / Eq. (178)), where each elemental component is the
group-commMat approximation `gciElement`. -/
def gciSeq {D : ℕ} (Vpin : ℝ → Mat D) (R : ℕ) (H0 : Mat D) (ℓ : ℝ) (K : ℕ) : ℕ → Mat D
  | 0 => 1
  | k + 1 =>
      gciSeq Vpin R H0 ℓ K k *
        gciElement Vpin R (ℓ / (K : ℝ))
          (((gciSeq Vpin R H0 ℓ K k)ᴴ) * H0 * (gciSeq Vpin R H0 ℓ K k))

/-- Recursive GWW flow approximation `Û^(N)_k` of Eqs. (232)–(237):
`Û^(N)_0 = 1`, `Û^(N)_{k+1} = Û^(N)_k e^{-s_k Ŵ_k}` with `s = ℓ/2^N` and
`Ŵ_k = [Δ(Ĥ_k), σ(Ĥ_k)]`, `Ĥ_k = (Û^(N)_k)† Ĥ Û^(N)_k`. -/
def gwwApproxU {D : ℕ} (H0 : Mat D) (ℓ : ℝ) (N : ℕ) : ℕ → Mat D
  | 0 => 1
  | k + 1 =>
      gwwApproxU H0 ℓ N k *
        NormedSpace.exp (-((ℓ / (2 : ℝ) ^ N) •
          canonicalBracket (((gwwApproxU H0 ℓ N k)ᴴ) * H0 * (gwwApproxU H0 ℓ N k))))

/-- The GWW flow map acting on an initial operator: a one-parameter family `Φ`
with `Φ_0 = id` satisfying the double-bracket flow
`∂_ℓ Φ_ℓ(J) = [W_ℓ, Φ_ℓ(J)]`, `W_ℓ = [Δ(Φ_ℓ J), Φ_ℓ J]`
(Section E; Eq. (68)/(217) context). -/
def IsGWWFlowMap {D : ℕ} (Φ : ℝ → Mat D → Mat D) : Prop :=
  (∀ J : Mat D, Φ 0 J = J) ∧
  (∀ (ℓ : ℝ), 0 ≤ ℓ → ∀ J : Mat D,
      HasDerivAt (fun t : ℝ => Φ t J) (commMat (canonicalBracket (Φ ℓ J)) (Φ ℓ J)) ℓ)

/-- A unitary lift `Û_ℓ` of the flow map, conjugating the initial operator:
`Φ_ℓ(J) = Û_ℓ(J)† J Û_ℓ(J)`, `Û_0 = 1`, each `Û_ℓ` unitary. -/
def IsUnitaryLift {D : ℕ} (Φ : ℝ → Mat D → Mat D) (Û : ℝ → Mat D → Mat D) : Prop :=
  (∀ J : Mat D, Û 0 J = 1) ∧
  (∀ (ℓ : ℝ), 0 ≤ ℓ → ∀ J : Mat D, IsUnitaryOp (Û ℓ J)) ∧
  (∀ (ℓ : ℝ), 0 ≤ ℓ → ∀ J : Mat D, Φ ℓ J = (Û ℓ J)ᴴ * J * Û ℓ J)

end Qatlib.Papers.DoubleBracket22.MainResults.Model
