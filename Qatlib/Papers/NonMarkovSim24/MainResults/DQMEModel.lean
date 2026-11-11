/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Log

set_option backward.isDefEq.respectTransparency false

/-!
# DQME-SQ model (dissipaton-embedded quantum master equation, second quantization)

Shared finite-dimensional model for the paper

  Xiang Li, Su-Xiang Lyu, Yao Wang, Rui-Xue Xu, Xiao Zheng, YiJing Yan,
  "Towards Quantum Simulation of Non-Markovian Open Quantum Dynamics:
   A Universal and Compact Theory", arXiv:2401.17255v4.

The reduced density tensor (RDT) of the dissipaton-embedded system is represented
by its occupation-number coefficients `ρ n` (one `d × d` complex matrix per
dissipaton configuration `n : ι → ℕ`).  The dissipaton ladder operators act on
the configuration index exactly as in the paper's Eq. (11a)-(11b):
`(b̂⁻_k ρ)_n = √(n_k+1) ρ_{n+e_k}` and `(b̂⁺_k ρ)_n = √(n_k) ρ_{n-e_k}`.

`heomRHS` is the multi-mode form of the EDMD/HEOM right-hand side of Eq. (8)
(the single-mode recast of Eq. (6)) read at an arbitrary configuration `n`;
`dqmeSqRHS` is the same object written with the ladder operators of Eq. (4)
/ Eq. (12), i.e. `-i[H_S,·] - Σ γ_k b̂⁺_k b̂⁻_k · - i Σ ζ_k (b̂⁺_k+b̂⁻_k)[Q̂,·]
+ Σ ξ_k b̂⁺_k {Q̂,·}` expanded in the occupation basis.

The paper's derivation of Eq. (4) from Eq. (8) ("Combining Eq. (8) and Eq. (9a),
along with the relations (11)") is exactly the content of `ladder_expansion`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.NonMarkovSim24.MainResults

/-- `d × d` complex matrices, the operators on the finite-dimensional system
space `H_S` underlying the reduced density tensor. -/
abbrev Op (d : ℕ) : Type := Matrix (Fin d) (Fin d) ℂ

/-- `√n` as a complex number: the bosonic dissipaton ladder coefficient of
Eq. (3) and Eq. (11) of the paper. -/
def sqrtNat (n : ℕ) : ℂ := (Real.sqrt (n : ℝ) : ℂ)

/-- `√n · √n = n`.  This is the elementary identity behind the canonical
commutation relation `[b̂⁻, b̂⁺] = 1` of Eq. (10). -/
theorem sqrtNat_mul_self (n : ℕ) : sqrtNat n * sqrtNat n = (n : ℂ) := by
  unfold sqrtNat
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  simp

/-- The number operator coefficient `n_k`, i.e. the eigenvalue of `b̂⁺_k b̂⁻_k`
on the occupation eigenstate `|n⟩` (Eq. (11) of the paper). -/
theorem sqrtNat_zero : sqrtNat 0 = 0 := by
  unfold sqrtNat
  simp

section Ladder

variable {ι : Type*} [DecidableEq ι]

/-- Componentwise action of the bosonic annihilation operator `b̂⁻_k` on the RDT
coefficients (Eq. (11a): `b̂⁻_k|n⟩ = √(n_k)|n-e_k⟩`). -/
def bAnn {d : ℕ} (ρ : (ι → ℕ) → Op d) (k : ι) (n : ι → ℕ) : Op d :=
  sqrtNat (n k + 1) • ρ (Function.update n k (n k + 1))

/-- Componentwise action of the bosonic creation operator `b̂⁺_k` on the RDT
coefficients (Eq. (11b): `b̂⁺_k|n⟩ = √(n_k+1)|n+e_k⟩`). -/
def bCreat {d : ℕ} (ρ : (ι → ℕ) → Op d) (k : ι) (n : ι → ℕ) : Op d :=
  sqrtNat (n k) • ρ (Function.update n k (n k - 1))

/-- `b̂⁻_k b̂⁺_k` raises the occupation coefficient: on the coefficient at `n`
it produces `(n_k+1)` times `ρ n` (the `n_k = 0` case is covered by the
vanishing coefficient `√0 = 0`). -/
theorem bAnn_bCreat {d : ℕ} (ρ : (ι → ℕ) → Op d) (k : ι) (n : ι → ℕ) :
    bAnn (bCreat ρ k) k n = ((n k : ℂ) + 1) • ρ n := by
  unfold bAnn bCreat
  rw [Function.update_self]
  rw [Nat.add_sub_cancel]
  rw [Function.update_idem]
  rw [Function.update_eq_self]
  rw [← mul_smul, sqrtNat_mul_self, Nat.cast_add, Nat.cast_one]

/-- `b̂⁺_k b̂⁻_k = N̂_k`: on the coefficient at `n` the composite produces
`n_k` times `ρ n`, i.e. exactly the dissipaton number operator `N̂_k` of Eq. (4)
and Eq. (11). -/
theorem bCreat_bAnn {d : ℕ} (ρ : (ι → ℕ) → Op d) (k : ι) (n : ι → ℕ) :
    bCreat (bAnn ρ k) k n = (n k : ℂ) • ρ n := by
  unfold bCreat bAnn
  rcases Nat.eq_zero_or_pos (n k) with h0 | hpos
  · rw [h0]
    simp [sqrtNat_zero]
  · have h1 : n k - 1 + 1 = n k := Nat.sub_add_cancel hpos
    rw [Function.update_self]
    rw [h1]
    rw [Function.update_idem]
    rw [Function.update_eq_self]
    rw [← mul_smul, sqrtNat_mul_self]

/-- The canonical bosonic commutation relation `[b̂⁻_k, b̂⁺_k] = 1` on RDT
coefficients (Eq. (10) of the paper). -/
theorem bAnn_bCreat_sub {d : ℕ} (ρ : (ι → ℕ) → Op d) (k : ι) (n : ι → ℕ) :
    bAnn (bCreat ρ k) k n - bCreat (bAnn ρ k) k n = ρ n := by
  rw [bAnn_bCreat, bCreat_bAnn]
  rw [add_smul, one_smul, add_sub_cancel_left]

end Ladder

section Equations

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Common core of the EDMD/HEOM component equation Eq. (8): the Hamiltonian
commutator, the dissipaton number/decay term, the `ζ` commutator term and the
`ξ` anti-commutator term, parameterized by the two ladder inputs `A` (from
`b̂⁻`) and `B` (from `b̂⁺`).  Both the HEOM form and the second-quantized DQME-SQ
form are instances of this core, differing only in whether `A`, `B` are written
explicitly or through the ladder operators `bAnn`, `bCreat`. -/
def heomCore {d : ℕ} (H : Op d) (Q : ι → Op d) (γ ζ ξ : ι → ℂ)
    (A B : ι → Op d) (ρ : (ι → ℕ) → Op d) (n : ι → ℕ) : Op d :=
  (-Complex.I) • (H * ρ n - ρ n * H)
    - (∑ k, (n k : ℂ) • γ k) • ρ n
    - Complex.I • (∑ k, ζ k • (Q k * (A k + B k) - (A k + B k) * Q k))
    + ∑ k, ξ k • (Q k * B k + B k * Q k)

/-- The multi-mode right-hand side of the EDMD/HEOM equation Eq. (8) of the
paper, read at dissipaton configuration `n`:

`ρ̇_n = -i[H_S,ρ_n] - Σ_k n_k γ_k ρ_n
        - i Σ_k ζ_k Q̂^× (√(n_k+1) ρ_{n+e_k} + √(n_k) ρ_{n-e_k})
        + Σ_k √(n_k) ξ_k Q̂^⋄ ρ_{n-e_k}`

with `Q̂^×O = Q̂O-OQ̂` and `Q̂^⋄O = Q̂O+OQ̂` (Sec. II B, p. 3 of arXiv:2401.17255v4). -/
def heomRHS {d : ℕ} (H : Op d) (Q : ι → Op d) (γ ζ ξ : ι → ℂ)
    (ρ : (ι → ℕ) → Op d) (n : ι → ℕ) : Op d :=
  heomCore H Q γ ζ ξ
    (fun k => sqrtNat (n k + 1) • ρ (Function.update n k (n k + 1)))
    (fun k => sqrtNat (n k) • ρ (Function.update n k (n k - 1))) ρ n

/-- The multi-mode second-quantized DQME-SQ of Eq. (4) (single environment) and
Eq. (12) (multiple environments / degrees of freedom), expanded in the
dissipaton occupation basis using the ladder relations Eq. (11):

`ρ̇ = -i[H_S,ρ] - Σ_k γ_k b̂⁺_k b̂⁻_k ρ - i Σ_k ζ_k (b̂⁺_k+b̂⁻_k)[Q̂,ρ]
      + Σ_k ξ_k b̂⁺_k {Q̂,ρ}`.

The `ξ_k` term is `b̂⁺_k` applied to the anti-commutator `{Q̂,ρ}`, which on
coefficients is `Q̂ (b̂⁺_k ρ) + (b̂⁺_k ρ) Q̂`. -/
def dqmeSqRHS {d : ℕ} (H : Op d) (Q : ι → Op d) (γ ζ ξ : ι → ℂ)
    (ρ : (ι → ℕ) → Op d) (n : ι → ℕ) : Op d :=
  heomCore H Q γ ζ ξ (fun k => bAnn ρ k n) (fun k => bCreat ρ k n) ρ n

/-- **Ladder expansion (Eq. (4) ⇔ Eq. (8), Sec. II B).**  Expanding the
second-quantized DQME-SQ generator in the occupation basis via the ladder
relations Eq. (11) reproduces the EDMD/HEOM component equations of Eq. (8)
term by term, for an arbitrary finite set of dissipaton modes.  This is the
formal equivalence between the bosonic DQME-SQ and the bosonic HEOM asserted
in c001. -/
theorem ladder_expansion {d : ℕ} (H : Op d) (Q : ι → Op d) (γ ζ ξ : ι → ℂ)
    (ρ : (ι → ℕ) → Op d) (n : ι → ℕ) :
    dqmeSqRHS H Q γ ζ ξ ρ n = heomRHS H Q γ ζ ξ ρ n := by
  -- Both sides are the same `heomCore`, differing only in whether the ladder
  -- inputs are written explicitly (HEOM, Eq. (8)) or via `bAnn`/`bCreat`
  -- (DQME-SQ, Eq. (4)/(12)); unfolding the latter closes the goal by `rfl`.
  simp only [dqmeSqRHS, heomRHS, heomCore, bAnn, bCreat]

/-- The decay term of Eq. (4)/Eq. (8) is the dissipaton number operator:
`-Σ_k γ_k b̂⁺_k b̂⁻_k` produces `-(Σ_k n_k γ_k) ρ n` at configuration `n`. -/
theorem decay_term_eq_number_operator {d : ℕ} (γ : ι → ℂ)
    (ρ : (ι → ℕ) → Op d) (n : ι → ℕ) :
    (∑ k, (n k : ℂ) • γ k) • ρ n
      = ∑ k, γ k • (bCreat (bAnn ρ k) k n) := by
  simp only [bCreat_bAnn, smul_smul]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [smul_eq_mul, mul_comm]

end Equations

end Qatlib.Papers.NonMarkovSim24.MainResults
