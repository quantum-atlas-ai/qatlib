/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

set_option backward.isDefEq.respectTransparency false

/-!
# Truncation model: sectors, quantum-number projections, and condition (24)

Source: Tong--Albert--McClean--Preskill--Su, *Provably accurate simulation of gauge
theories and bosonic systems*, fixed arXiv:2110.06942v2 (Accepted in Quantum
2022-09-13). Local copy `/tmp/prove/assets/2110.06942.pdf` / `.txt`.

This module fixes the finite-dimensional operator model used by the paper's
Sections C (state truncation) and E (Hamiltonian truncation):

* `sectorProj ν λ` is the projection onto the sector `λ` (Section B, Eq. (25), (29),
  (31)): the diagonal `0/1` matrix supported on the basis states whose quantum
  number `ν i` equals `λ`.
* `sectorProjInterval ν a b` is `Π_[a,b] = Σ_{λ∈[a,b]} Π_λ` (Eq. (32)); its
  complement `1 - Π_[a,b]` is `Π̄_[a,b]` (Eq. (34)).
* `SatisfiesCondition24 ν χ r H_W H_R` encodes condition (24), p.18:
  `Π_λ H_W Π_λ' = 0` if `|λ-λ'|>1`, `‖H_W Π_[−Λ,Λ]‖ ≤ χ (Λ+1)^r`, and
  `[H_R, Π_λ] = 0`, with `H = H_W + H_R`.
* `leakage ν H Λ0 Δ t` is the leakage `‖Π̄_[−Λ0−Δ,Λ0+Δ] e^{−itH} Π_[−Λ0,Λ0]‖`
  of Eq. (34).

Everything is a finite matrix on `I`; this is the paper's finite-mode truncation
setting. The module deliberately states no numerical constants for the models of
Section A (those enter as the hypothesis `SatisfiesCondition24`).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.GaugeSim21.MainResults.TruncationModel

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Projection onto the quantum-number sector `λ` (Eqs. (25), (29), (31)): the diagonal
operator whose `i`-th diagonal entry is `1` when `ν i = λ` and `0` otherwise. -/
def sectorProj (ν : I → ℤ) (l : ℤ) : Matrix I I ℂ :=
  Matrix.diagonal (fun i => if ν i = l then (1 : ℂ) else 0)

/-- The interval projection `Π_[a,b] = Σ_{λ∈[a,b]} Π_λ` (Eq. (32)). -/
def sectorProjInterval (ν : I → ℤ) (a b : ℤ) : Matrix I I ℂ :=
  ∑ l ∈ Finset.Icc a b, sectorProj ν l

/-- The complementary projection `Π̄_[a,b] = I - Π_[a,b]` (Eq. (34)). -/
def sectorProjComplement (ν : I → ℤ) (a b : ℤ) : Matrix I I ℂ :=
  1 - sectorProjInterval ν a b

/-- Symmetric interval `Π_[−Λ,Λ]` for a nonnegative integer cutoff `Λ`. -/
def sectorProjNat (ν : I → ℤ) (Λ : ℕ) : Matrix I I ℂ :=
  sectorProjInterval ν (-(Λ : ℤ)) (Λ : ℤ)

/-- The complement `Π̄_[−Λ,Λ]`. -/
def sectorProjNatComplement (ν : I → ℤ) (Λ : ℕ) : Matrix I I ℂ :=
  sectorProjComplement ν (-(Λ : ℤ)) (Λ : ℤ)

/-- Condition (24), p.18: `H = H_W + H_R` where `H_W` changes the quantum number by at
most `±1` and is sublinear in the cutoff, while `H_R` commutes with every `Π_λ`. -/
def SatisfiesCondition24 (ν : I → ℤ) (χ r : ℝ) (H_W H_R : Matrix I I ℂ) : Prop :=
  (∀ l l' : ℤ, (1 : ℤ) < |l - l'| → sectorProj ν l * H_W * sectorProj ν l' = 0) ∧
  (∀ Λ : ℕ, ‖H_W * sectorProjNat ν Λ‖ ≤ χ * ((Λ : ℝ) + 1) ^ r) ∧
  (∀ l : ℤ, H_R * sectorProj ν l = sectorProj ν l * H_R)

/-- The leakage `‖Π̄_[−Λ0−Δ,Λ0+Δ] e^{−itH} Π_[−Λ0,Λ0]‖` of Eq. (34), p.20. -/
def leakage (ν : I → ℤ) (H : Matrix I I ℂ) (Λ0 Δ : ℕ) (t : ℝ) : ℝ :=
  ‖sectorProjComplement ν (-((Λ0 + Δ : ℕ) : ℤ)) ((Λ0 + Δ : ℕ) : ℤ) *
      Qatlib.Foundations.PureStateMath.HamiltonianEvolution H t *
      sectorProjInterval ν (-(Λ0 : ℤ)) (Λ0 : ℤ)‖

/-- The single-mode interval `Π_[−Λ0−Δ,Λ0+Δ]` complement used in Lemma 1 has the
diagonal `0/1` form, so it is contractive. -/
theorem norm_sectorProj_le_one (ν : I → ℤ) (l : ℤ) [Nonempty I] :
    ‖sectorProj ν l‖ ≤ 1 := by
  rw [sectorProj, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr ?_
  intro i
  split_ifs
  · simp
  · simp

end Qatlib.Papers.GaugeSim21.MainResults.TruncationModel
