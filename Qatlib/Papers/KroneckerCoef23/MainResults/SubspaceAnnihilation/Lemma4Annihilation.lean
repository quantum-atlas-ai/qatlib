/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma4Annihilation — Lemma 4 of Bravyi–Chowdhury–Gosset–Havlíček–Zhu

Fixed version: arXiv:2302.11454v3 (7 May 2024), Lemma 4 and its proof, p. 9.

Lemma 4: let `P` project onto the subspace spanned by the basis states that encode
partitions of `n − 1`,
`span{|w⟩|σ,p,q⟩ : w ∈ {0,τ₁,…,τₙ}, σ ⊢ (n−1), 1 ≤ p,q ≤ d_σ}`, and let
`g : Sₙ → ℂ` vanish on `S_{n−1}` (the subgroup fixing `n`).  Then
`P U† |0⟩|ĝ⟩ = 0`.

The proof (p. 9) writes `P = Σ_{k=0}^n P_k`, where `P_k` projects onto the `|τ_k⟩`-sector
(and `P_0` onto the `|0⟩`-sector of partitions of `n−1`).  Three facts are used:

* Eq. (22): `P_0 U†|0⟩|ĝ⟩ = 0` (from `g` vanishing on `S_{n−1}` and Eq. (21));
* Eq. (20): `U` fixes the `|τ_k⟩`-sector, hence `P_k U† = P_k` there, i.e.
  `P_k(U† x) = P_k x` for `k ≠ 0`;
* the state `x = |0⟩|ĝ⟩` has no `|τ_k⟩` component for `k ≠ 0`, i.e. `P_k x = 0`.

Then `P(U†x) = P_0(U†x) + Σ_{k=1}^n P_k(U†x) = 0 + Σ_{k=1}^n P_k x = 0`.

We formalise exactly this computation for an abstract Hilbert space `W`: `P k` are the
sector projectors, `U` the unitary of Eq. (19)–(20), and `x = |0⟩|ĝ⟩`.  The
Fourier-analytic input producing Eq. (22) from `g|_{S_{n−1}} = 0` is Eq. (21) (the
Fourier transform of `Sₙ₋₁`) and is recorded as the hypothesis `h22`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.KroneckerCoef23.MainResults.SubspaceAnnihilation

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- **Lemma 4, projection-annihilation core** (fixed arXiv:2302.11454v3, Lemma 4, p. 9):
if the `|0⟩`-sector projection kills `U† x` (Eq. (22)), the `|τ_k⟩`-sector projections
(`k ≠ 0`) are preserved by `U†` (Eq. (20)), and `x` has no `|τ_k⟩` component, then the
full partition-of-`n−1` projector `P = Σ_k P_k` kills `U† x`. -/
theorem lemma4_projection_annihilation
    (n : ℕ) (P : Fin (n + 1) → W →ₗ[ℂ] W) (U : W →ₗ[ℂ] W) (x : W)
    (h22 : P 0 (U x) = 0)
    (h20 : ∀ k : Fin (n + 1), k ≠ 0 → P k (U x) = P k x)
    (hx : ∀ k : Fin (n + 1), k ≠ 0 → P k x = 0) :
    (∑ k : Fin (n + 1), P k (U x)) = 0 := by
  rw [Fin.sum_univ_succ]
  rw [h22, zero_add]
  exact Finset.sum_eq_zero (fun i _ => by
    rw [h20 i.succ (by simp), hx i.succ (by simp)])

/-- **Lemma 4** (fixed arXiv:2302.11454v3, p. 9): the full projector
`P = Σ_{k=0}^n P_k` annihilates `U† x`, i.e. `P U† |0⟩|ĝ⟩ = 0`, stated with the sum of
projectors applied to the state. -/
theorem lemma4_annihilation (n : ℕ) (P : Fin (n + 1) → W →ₗ[ℂ] W)
    (U : W →ₗ[ℂ] W) (x : W)
    (h22 : P 0 (U x) = 0)
    (h20 : ∀ k : Fin (n + 1), k ≠ 0 → P k (U x) = P k x)
    (hx : ∀ k : Fin (n + 1), k ≠ 0 → P k x = 0) :
    (∑ k : Fin (n + 1), P k) (U x) = 0 := by
  rw [LinearMap.sum_apply]
  exact lemma4_projection_annihilation n P U x h22 h20 hx

end Qatlib.Papers.KroneckerCoef23.MainResults.SubspaceAnnihilation
