/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamInversion26.SpinInversion.Model.OracleWord
import Mathlib.Analysis.Complex.Exponential

set_option backward.isDefEq.respectTransparency false

/-!
# Wedderburn block decomposition data

Fixed arXiv:2607.29382v2.

* Page 3 (Letter) and pages S9–S11 (SM): after the known change of basis, the unitary
  family decomposes into a direct sum `U(x) = ⊕_α (I_{M_α} ⊗ U_α(x))` over inequivalent
  blocks `U_α` of dimension `d_α`, each repeated `m_α` times.
* Eq. (S71), page S13: the block inclusions `ι^R_α : V_α → H_red` satisfy
  `(ι^R_α)† ι^R_β = δ_{αβ}` and `U_red(x) ι^R_α = ι^R_α U_α(x)`.
* Definition S3/S4 (pages S13, S25): sector certificates and scalar certificates.

This module gives the index-level model used by the blockwise compiler statements:
the reduced Hilbert space is the sigma type of the active block spaces, the full
Hilbert space additionally carries the multiplicity label, and `redFamily` /
`fullFamily` are the block-diagonal families of `Matrix.blockDiagonal'`.
-/

open Matrix
open scoped Kronecker BigOperators

namespace Qatlib.Papers.HamInversion26.SpinInversion.Model

set_option autoImplicit false
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The reduced Hilbert space `H_red = ⊕_α V_α`, with `dim V_α = d α` (page S9). -/
abbrev RedHilbert (d : ι → ℕ) : Type _ := Σ α : ι, Fin (d α)

/-- The physical Hilbert space before removing multiplicities,
`H_S = ⊕_α (M_α ⊗ V_α)`, with `dim M_α = m α` (page S11, Eq. (S55)). -/
abbrev FullHilbert (m d : ι → ℕ) : Type _ := Σ α : ι, (Fin (m α) × Fin (d α))

/-- The block-diagonal reduced family `U_red(x) = ⊕_α U_α(x)` (Eq. (S71), page S13). -/
def redFamily {P : Type*} {d : ι → ℕ}
    (U : ∀ α, P → Matrix (Fin (d α)) (Fin (d α)) ℂ) (x : P) :
    Matrix (RedHilbert d) (RedHilbert d) ℂ :=
  Matrix.blockDiagonal' (fun α => U α x)

/-- The physical family `⊕_α (I_{M_α} ⊗ U_α(x))` (page S11, Eq. (S56)). -/
def fullFamily {P : Type*} {m d : ι → ℕ}
    (U : ∀ α, P → Matrix (Fin (d α)) (Fin (d α)) ℂ) (x : P) :
    Matrix (FullHilbert m d) (FullHilbert m d) ℂ :=
  Matrix.blockDiagonal' (fun α => (1 : Matrix (Fin (m α)) (Fin (m α)) ℂ) ⊗ₖ U α x)

/-- A clean `q`-query circuit whose `α`-sector action is the phase `φ(x)` times
`U_α(x)†` (Definition S3, page S13; Definition S4, page S25, Eq. (S121)).  The sector
inclusion is an arbitrary matrix `ια : V_α → H_red`; for the paper's `ι^R_α` it satisfies
Eq. (S71). -/
def SectorInverts {P : Type*} {H : Type*} [Fintype H] [DecidableEq H] {d : ℕ}
    (q : ℕ) (Ured : P → Matrix H H ℂ) (ια : Matrix H (Fin d) ℂ)
    (Uα : P → Matrix (Fin d) (Fin d) ℂ) (φ : P → ℂ) : Prop :=
  ∃ W : Word H q, ∀ x, Word.eval W (Ured x) * ια = φ x • (ια * (Uα x)ᴴ)

/-- A clean scalar gadget: a `q`-query circuit acting on the whole reduced space as the
phase `φ(x)` times the identity (Definition S5, page S25, Eq. (S124)). -/
def ScalarCert {P : Type*} {H : Type*} [Fintype H] [DecidableEq H]
    (q : ℕ) (Ured : P → Matrix H H ℂ) (φ : P → ℂ) : Prop :=
  ∃ W : Word H q, ∀ x, Word.eval W (Ured x) = φ x • (1 : Matrix H H ℂ)

/-- A local block inverter (Definition S3, page S13). -/
def LocalInverter {P : Type*} {d : ℕ} (q : ℕ)
    (Uα : P → Matrix (Fin d) (Fin d) ℂ) (φα : P → ℂ) : Prop :=
  ∃ W : Word (Fin d) q, ∀ x, Word.eval W (Uα x) = φα x • (Uα x)ᴴ

/-- The automatic-completion query count of Corollary S17 (page S17). -/
def qauto {ι : Type*} [Fintype ι] (ℓ : ι → ℕ) : ℕ :=
  (∑ α, (ℓ α + 1)) - 1

/-- The determinant-synchronization query count `q_det = Σ_α (ℓ_α + 1) − 1 = Σ_α d_α s_α − 1`
of Theorem S14 (Eq. (S86), page S15). -/
def qdet {ι : Type*} [Fintype ι] (d s : ι → ℕ) : ℕ :=
  (∑ α, d α * s α) - 1

/-- The phase vector of a complex number, used for the physical families. -/
abbrev phaseChar (p : ℕ) (τ x : Fin p → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((∑ j, τ j * x j : ℝ) : ℂ))

end

end Qatlib.Papers.HamInversion26.SpinInversion.Model
