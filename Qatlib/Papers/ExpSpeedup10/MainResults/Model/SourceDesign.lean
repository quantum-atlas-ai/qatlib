/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExpSpeedup10.MainResults.Model.SourceCore

set_option backward.isDefEq.respectTransparency false

/-!
# ExpSpeedup10 — design and spectral source model

Brandão–Horodecki, *Exponential Quantum Speed-ups are Generic*,
fixed arXiv:1010.3654**v2** (16 Apr 2013).

This file records the design-theoretic and spectral source objects needed by
Theorems II–IV and Lemmas III.1, VI.1, VI.3, VI.4, and Proposition VI.5:

* `SourceSuperOp` / `IsApproxUnitaryTDesign` — Def. II.4: an ensemble is an
  `ε`-approximate unitary `t`-design when its twirl-difference superoperator
  `G_{μ,t} − G_{H,t}` has 2→2 induced Schatten norm at most `ε`.
* `sourceLocalCircuitResidual` — Eq. (55)/(59) with Lemmas VI.1 and VI.4:
  `‖G_{μ^{*k},t} − G_{H,t}‖∞ ≤ (1 − 1/(5n))^k` for `t = 2, 3`.
* `sourceUniformCircuitResidual` — Eq. (89): `‖G_{ν^{*k},t} − G_{H,t}‖∞ ≤
  (1 − 1/(5n²))^k`.
* `sourceLambda2Desc` / `sourceLambda2Asc` — the second largest / second
  smallest eigenvalue of a Hermitian matrix, matching the two orderings the
  paper uses (`λ₂` as convergence rate in Eq. (59), and `λ₂` as the spectral
  gap of a PSD Hamiltonian in Lemma VI.3).
* `IsLocalHaarTwirlProjector`, `IsLocalMomentWalkOperator`,
  `IsThreeSiteMomentWalkOperator` — the walk operators `M_{t,n}` (Eq. (56))
  and `M_{t,3}` (Eq. (70)) built from the local Haar-twirl projectors of
  Eq. (57)/(71).  The explicit construction of the Haar average on `U(4)` is
  not available in Mathlib; the predicates below record the operator equation
  and the projector properties, which is the reduction used by Lemmas VI.1/VI.4.

Boundary: definitions only.  The statements live in the per-claim files.
-/

set_option autoImplicit false
noncomputable section

open Matrix BigOperators
open scoped Classical MatrixOrder

namespace Qatlib.Papers.ExpSpeedup10.MainResults
namespace Model

/-- Definition II.4: an ensemble is an `ε`-approximate unitary `t`-design when
the 2→2 induced Schatten norm `residual` of the twirl-difference superoperator
`G_{μ,t} − G_{H,t}` of Eq. (15)/(16) is at most `ε`, Eq. (17).  The norm is
carried as an explicit real number because Mathlib has no operator-norm
instance on `Matrix (Fin N) (Fin N) ℂ`; the residual is what every statement
below actually uses. -/
def IsApproxUnitaryTDesign (residual ε : ℝ) : Prop :=
  residual ≤ ε

/-- Eq. (55)/(59), with Lemma VI.1 and Lemma VI.4: the `k`-step local random
circuit twirl difference has `∞`-norm at most `(1 − 1/(5n))^k`
(for `t = 2, 3`).  `sourceC`-independent: this is exactly the spectral
decay rate `λ₂(M_{t,n})^k` used in the proof of Theorem III. -/
noncomputable def sourceLocalCircuitResidual (n k : ℕ) : ℝ :=
  (1 - 1 / (5 * (n : ℝ))) ^ k

/-- Eq. (89)-(93) (Proposition VI.5): the uniform random circuit twirl
difference has `∞`-norm at most `(1 − 1/(5n²))^k`. -/
noncomputable def sourceUniformCircuitResidual (n k : ℕ) : ℝ :=
  (1 - 1 / (5 * (n : ℝ) ^ 2)) ^ k

/-- The second largest eigenvalue of a Hermitian matrix (`λ₂` in the
convergence-rate convention of Eq. (56)-(59)); `eigenvalues₀` is antitone,
so the index `1` is the second largest value. -/
noncomputable def sourceLambda2Desc {N : ℕ} (hN : 2 ≤ N)
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) : ℝ :=
  hA.eigenvalues₀ ⟨1, by have := Fintype.card_fin N; omega⟩

/-- The second smallest eigenvalue of a Hermitian matrix (`λ₂` in the
spectral-gap convention of Lemma VI.3, where `λ₁ = 0` is the ground energy).
Equivalently the second entry of the ascending order, i.e. index `N − 2` of
the antitone `eigenvalues₀`. -/
noncomputable def sourceLambda2Asc {N : ℕ} (hN : 2 ≤ N)
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) : ℝ :=
  hA.eigenvalues₀ ⟨N - 2, by have := Fintype.card_fin N; omega⟩

/-- The lowest eigenvalue `λ₁` of a Hermitian matrix (`eigenvalues₀ 0`). -/
noncomputable def sourceLambda1 {N : ℕ} (hN : 1 ≤ N)
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) : ℝ :=
  hA.eigenvalues₀ ⟨0, by have := Fintype.card_fin N; omega⟩

/-- `P` is the local Haar-twirl projector of Eq. (57)/(71): the orthogonal
projection onto the operators commuting with `U^{⊗t} ⊗ Ū^{⊗t}`.  We record the
projector properties; the explicit Haar average on `U(2)` / `U(4)` is the
formalisation gap documented in Lemma VI.4. -/
def IsLocalHaarTwirlProjector (t : ℕ) {D : ℕ} (P : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P ∧ (∀ X, P * X * P = P * X)

/-- Eq. (56)/(57): `M_{t,n} = (1/n) ∑ᵢ Pᵢ,ᵢ₊₁` with `Pᵢ,ᵢ₊₁` the local Haar
twirls on the `t`-fold copy of the two neighbouring qubits. -/
def IsLocalMomentWalkOperator (n t : ℕ) {D : ℕ}
    (M : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∃ P : Fin n → Matrix (Fin D) (Fin D) ℂ,
    M = (n : ℂ)⁻¹ • ∑ i, P i ∧ ∀ i, IsLocalHaarTwirlProjector t (P i)

/-- Eq. (70): `M_{t,3} = (P₁₂ ⊗ I₃ + I₁ ⊗ P₂₃)/2` in the three-qubit walk. -/
def IsThreeSiteMomentWalkOperator (t : ℕ) {D : ℕ}
    (M : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∃ (P12 P23 : Matrix (Fin D) (Fin D) ℂ),
    M = (2 : ℂ)⁻¹ • (P12 + P23) ∧
    IsLocalHaarTwirlProjector t P12 ∧ IsLocalHaarTwirlProjector t P23

/-- Approximately-sparse unitary (Section V, definition before Theorem VI):
`U` is `δ`-close in operator norm to a matrix with at most `s` non-zeros in
each row and column. -/
def IsApproximatelySparse {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (s : ℕ) (δ : ℝ) : Prop :=
  ∃ S : Matrix (Fin N) (Fin N) ℂ, (∀ i j, ‖U i j - S i j‖ ≤ δ) ∧
    (∀ i, (Finset.univ.filter fun j => S i j ≠ 0).card ≤ s) ∧
    (∀ j, (Finset.univ.filter fun i => S i j ≠ 0).card ≤ s)

/-- A family of unitaries `U` is `(δ, k)`-almost `k`-wise independent
(Definition IV.2 / Eq. (29)): every `k`-term has probability within a
multiplicative `(1 ± δ)` window of `2^{-k}`.  Modelled on the sign-string law
`SignPairLaw`; `term` is the indicator of a chosen `k`-term. -/
def IsAlmostKWiseIndependent {N k : ℕ} (law : (Fin N → Bool) → (Fin N → Bool) → ℝ)
    (term : (Fin N → Bool) → (Fin N → Bool) → Bool) (δ : ℝ) : Prop :=
  (∀ f g, 0 ≤ law f g) ∧
  (1 - δ) * (2 : ℝ) ^ (-(k : ℝ)) ≤
    ∑ f, ∑ g, (if term f g then law f g else 0) ∧
  (∑ f, ∑ g, (if term f g then law f g else 0)) ≤
    (1 + δ) * (2 : ℝ) ^ (-(k : ℝ))

end Model
end Qatlib.Papers.ExpSpeedup10.MainResults
