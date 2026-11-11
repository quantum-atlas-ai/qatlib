/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Pi

set_option backward.isDefEq.respectTransparency false

/-!
# IQPBornShen26 definitions: generators, Fourier supports, and the IQP
characteristic function in commutation-decomposed form

Shen–Pielawa–Dunjko–Wang, arXiv:2602.11042v2.
An `n`-qubit IQP circuit has `D` generators `s_j ∈ F₂^n` and parameters
`θ_j`, giving the diagonal unitary `U_θ = ∏_j e^{iθ_j Z_{s_j}}`.  For a Fourier
frequency `a ∈ F₂^n`, the characteristic function value of the output
distribution is `C_θ^a = ⟨+|U_θ† X^a U_θ|+⟩`.

By commuting the gates through the observable (arXiv:2602.11042v2, Eq. (22),
following Eq. (27) of [15]), `C_θ^a` expands over the zero-sum subsets
`J ⊆ S^a` (where `S^a = {s_j : s_j · a = 1}` and `∑_{j∈J} s_j = 0` in `F₂^n`)
as `C_θ^a = Σ_{J ∈ Ξ^a} R_J(θ)` with
`R_J(θ) = η_J ∏_{j∈J} sin(2θ_j) ∏_{j∈S^a∖J} cos(2θ_j)` and signs `η_J ∈ {−1,1}`.
This file defines the combinatorial data and the decomposed function
`charFunIQP`; the gate-commutation derivation of the decomposition itself is
the external interface of the theorems that use it.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.IQPBornShen26.MainResults

/-- The `F₂` inner product of two bit strings `u, v ∈ F₂^n`. -/
def dotF2 {n : ℕ} (u v : Fin n → ZMod 2) : ZMod 2 :=
  ∑ k, u k * v k

/-- The generator support `S^a = {s_j : s_j · a = 1}` (arXiv:2602.11042v2,
Theorem 3.2): the generators whose Pauli string anticommutes with `X^a`. -/
def supportGen {D n : ℕ} (s : Fin D → (Fin n → ZMod 2)) (a : Fin n → ZMod 2) :
    Finset (Fin D) :=
  Finset.univ.filter (fun j => dotF2 (s j) a = 1)

/-- The zero-sum subsets `Ξ^a = {J ⊆ S^a : ∑_{j∈J} s_j = 0}` over which the
commutation decomposition (22) of arXiv:2602.11042v2 runs. -/
def zeroSumSets {D n : ℕ} (s : Fin D → (Fin n → ZMod 2)) (a : Fin n → ZMod 2) :
    Finset (Finset (Fin D)) :=
  (supportGen s a).powerset.filter (fun J => ∑ j ∈ J, s j = 0)

/-- The summand `R_J(θ) = η_J ∏_{j∈J} sin(2θ_j) ∏_{j∈S^a∖J} cos(2θ_j)` of the
commutation decomposition (22) of arXiv:2602.11042v2; `η` is the sign function
of the decomposition, constrained to `±1` on `Ξ^a` by the theorems below. -/
def termR {D n : ℕ} (s : Fin D → (Fin n → ZMod 2)) (a : Fin n → ZMod 2)
    (η : Finset (Fin D) → ℝ) (J : Finset (Fin D)) (θ : Fin D → ℝ) : ℝ :=
  η J * (∏ j ∈ J, Real.sin (2 * θ j)) * ∏ j ∈ supportGen s a \ J, Real.cos (2 * θ j)

/-- The IQP characteristic function value `C_θ^a` in its commutation-decomposed
form (22) of arXiv:2602.11042v2: `C_θ^a = Σ_{J ∈ Ξ^a} R_J(θ)`.  The identity
with the circuit quantity `⟨+|U_θ† X^a U_θ|+⟩` is the external interface;
everything proved downstream about `charFunIQP` uses only the decomposition. -/
def charFunIQP {D n : ℕ} (s : Fin D → (Fin n → ZMod 2)) (a : Fin n → ZMod 2)
    (η : Finset (Fin D) → ℝ) (θ : Fin D → ℝ) : ℝ :=
  ∑ J ∈ zeroSumSets s a, termR s a η J θ

end Qatlib.Papers.IQPBornShen26.MainResults
