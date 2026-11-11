/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDistTV

set_option backward.isDefEq.respectTransparency false

/-!
# Recommender18 source model

Tang, "A quantum-inspired classical algorithm for recommendation systems",
fixed arXiv:1807.04271 (v1, 2018).  This file fixes the paper's notation:

* `l2Dist` — the ℓ₂-norm sampling distribution `D_x` of §2.2,
  `D_x(i) = x_i² / ‖x‖²`;
* `l2TV` — total variation distance between two such distributions (§2.2);
* `frobNorm` / `frobDist` — Frobenius norm and distance on finite matrices (§2);
* `rowEuc`, `rowNorm`, `rowDist` — rows as Euclidean vectors and their norms;
* `ell` — the singular-value split `ℓ(λ) = max{i | σ_i ≥ λ}` (§2);
* `IsSVD` — a finite SVD certificate `A = U Σ Vᵀ` with nonincreasing singular
  values (the paper assumes such an SVD exists for every matrix);
* `IsOrthProjector` and `IsSpectralSandwich` — orthogonal projectors and the
  paper's `P_{σ,η}` Loewner sandwich defining the class `A_{σ,η}` (§2.1);
* `IsTypical` — the `(γ, ζ)`-typical set of users (§5.1).

All norms are the paper's ℓ₂ / Frobenius norms.
-/

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.Recommender18.MainResults

noncomputable section

/-! ### The ℓ₂ sampling distribution -/

/-- Paper §2.2, `D_x`: mass `x_i² / ‖x‖²` on coordinate `i`.
The paper only defines this for a nonzero vector; `hx` records that. -/
def l2Dist {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) : FinDist (Fin n) where
  prob i := (x i) ^ 2 / ∑ j, (x j) ^ 2
  nonneg i := div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  sum_one := by
    have hpos : 0 < ∑ j, (x j) ^ 2 := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      exact pow_pos (norm_pos_iff.mpr hx) 2
    rw [← Finset.sum_div, div_self (ne_of_gt hpos)]

/-- `D_x(i) = x_i² / ‖x‖²`, in norm form. -/
theorem l2Dist_prob {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (i : Fin n) :
    (l2Dist x hx).prob i = (x i) ^ 2 / ‖x‖ ^ 2 := by
  unfold l2Dist
  simp only
  rw [EuclideanSpace.real_norm_sq_eq]

/-- `D_x(i)` written with the normalized coordinate `x_i / ‖x‖`. -/
theorem l2Dist_prob_normalized {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0)
    (i : Fin n) :
    (l2Dist x hx).prob i = (x i / ‖x‖) ^ 2 := by
  rw [l2Dist_prob, div_pow]

/-- Paper §2.2: total variation distance between `D_x` and `D_y`. -/
def l2TV {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (hy : y ≠ 0) : ℝ :=
  tvDist (l2Dist x hx) (l2Dist y hy)

/-! ### Frobenius and row norms -/

/-- Squared Frobenius norm of a finite matrix, `Σ_ij A_ij²`. -/
def frobNormSq {m n : ℕ} (A : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- Frobenius norm `‖A‖_F` of §2. -/
def frobNorm {m n : ℕ} (A : Fin m → Fin n → ℝ) : ℝ :=
  Real.sqrt (frobNormSq A)

/-- Frobenius distance `‖A − B‖_F`. -/
def frobDist {m n : ℕ} (A B : Fin m → Fin n → ℝ) : ℝ :=
  frobNorm (fun i j => A i j - B i j)

/-- A row of a matrix, as a Euclidean vector. -/
def rowEuc {m n : ℕ} (A : Fin m → Fin n → ℝ) (i : Fin m) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => A i j)

/-- The `rowEuc_apply` result for the Recommender18 paper model. -/
@[simp] theorem rowEuc_apply {m n : ℕ} (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    rowEuc A i j = A i j := rfl

/-- Row ℓ₂ norm `‖A_i‖`. -/
def rowNorm {m n : ℕ} (A : Fin m → Fin n → ℝ) (i : Fin m) : ℝ :=
  ‖rowEuc A i‖

/-- Total variation distance between the ℓ₂ distributions of two rows. -/
def rowTV {m n : ℕ} (A B : Fin m → Fin n → ℝ) (i : Fin m)
    (hA : rowEuc A i ≠ 0) (hB : rowEuc B i ≠ 0) : ℝ :=
  l2TV (rowEuc A i) (rowEuc B i) hA hB

/-! ### Singular values and the paper's low-rank notation -/

/-- A finite SVD certificate for `A : ℝ^{m×n}` (§2): orthonormal left/right
singular vector families and a nonincreasing nonnegative singular value list,
with `A i j = Σ_t σ_t U i t V j t` and `N = min m n`. -/
structure IsSVD {m n : ℕ} (A : Fin m → Fin n → ℝ) where
  N : ℕ
  σ : Fin N → ℝ
  U : Fin m → Fin N → ℝ
  V : Fin n → Fin N → ℝ
  sigma_nonneg : ∀ t, 0 ≤ σ t
  sigma_nonincreasing : ∀ t s : Fin N, t ≤ s → σ s ≤ σ t
  U_orthonormal : ∀ t s, (∑ i, U i t * U i s) = if t = s then 1 else 0
  V_orthonormal : ∀ t s, (∑ j, V j t * V j s) = if t = s then 1 else 0
  reconstruction : ∀ i j, A i j = ∑ t, σ t * U i t * V j t

/-- Paper §2: `ℓ(λ) = max{i | σ_i ≥ λ}`, expressed as the number of singular
values at least `λ` (the list is nonincreasing, so this is a prefix length). -/
def ell {N : ℕ} (σ : Fin N → ℝ) (lam : ℝ) : ℕ :=
  (Finset.univ.filter fun t => lam ≤ σ t).card

/-- Truncated matrix `A_k = Σ_{t<k} σ_t u_t v_tᵀ` from an SVD certificate. -/
def truncRank {m n : ℕ} {A : Fin m → Fin n → ℝ} (S : IsSVD A) (k : ℕ) :
    Fin m → Fin n → ℝ :=
  fun i j => ∑ t : Fin S.N, if (t : ℕ) < k then S.σ t * S.U i t * S.V j t else 0

/-- `A_k` for `k` singular vectors. -/
def Ak {m n : ℕ} (A : Fin m → Fin n → ℝ) (S : IsSVD A) (k : ℕ) : Fin m → Fin n → ℝ :=
  truncRank S k

/-- `A_σ = A_{ℓ(σ)}`. -/
def Asigma {m n : ℕ} (A : Fin m → Fin n → ℝ) (S : IsSVD A) (sigma : ℝ) :
    Fin m → Fin n → ℝ :=
  truncRank S (ell S.σ sigma)

/-- Spectral filter certificate: `B = A P` where `P` is `1` on singular vectors
with `σ_t ≥ σ(1+η)`, `0` on those with `σ_t ≤ σ(1−η)`, and an arbitrary
`[0,1]` multiplier in between.  This is the paper's class `A_{σ,η}` (§2.1),
realised on the SVD diagonal.  `c t` is the multiplier on singular vector `t`;
only its bounds matter, not its exact value. -/
def spectralFilter {m n : ℕ} {A : Fin m → Fin n → ℝ} (S : IsSVD A)
    (c : Fin S.N → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => ∑ t : Fin S.N, c t * (S.σ t * S.U i t * S.V j t)

/-- The filter hypothesis of §2.1: `Π_{σ(1+η)} ≤ P_{σ,η} ≤ Π_{σ(1−η)}`. -/
def IsSpectralFilter {m n : ℕ} {A : Fin m → Fin n → ℝ} (S : IsSVD A) (sigma eta : ℝ)
    (c : Fin S.N → ℝ) : Prop :=
  (∀ t, sigma * (1 + eta) ≤ S.σ t → c t = 1) ∧
  (∀ t, S.σ t ≤ sigma * (1 - eta) → c t = 0) ∧
  (∀ t, 0 ≤ c t ∧ c t ≤ 1)

/-! ### Orthogonal projectors (paper §2) -/

/-- A matrix is an orthogonal projector when it is a symmetric idempotent. -/
def IsOrthProjector {d : ℕ} (P : Fin d → Fin d → ℝ) : Prop :=
  (∀ i j, P j i = P i j) ∧
  (∀ i j, ∑ k, P i k * P k j = P i j)

/-- The range of an orthogonal projector as a subspace membership predicate:
`x` is in `im P` iff `P x = x`. -/
def InProjectorRange {d : ℕ} (P : Fin d → Fin d → ℝ) (x : Fin d → ℝ) : Prop :=
  ∀ i, ∑ j, P i j * x j = x i

/-- Rank (dimension of the image) as the trace of the projector. -/
def projRank {d : ℕ} (P : Fin d → Fin d → ℝ) : ℝ := ∑ i, P i i

/-! ### Typical sets of users (paper §5.1) -/

/-- Paper §5.1: `S` is a `(γ, ζ)`-typical set of users for `T` when
`|S| ≥ (1−ζ)m` and every `i ∈ S` has
`(1/(1+γ))·‖T‖_F²/m ≤ ‖T_i‖² ≤ (1+γ)·‖T‖_F²/m`. -/
def IsTypical {m n : ℕ} (T : Fin m → Fin n → ℝ) (S : Finset (Fin m))
    (γ ζ : ℝ) : Prop :=
  (1 - ζ) * (m : ℝ) ≤ (S.card : ℝ) ∧
  ∀ i ∈ S,
    (1 / (1 + γ)) * frobNormSq T / (m : ℝ) ≤ (rowNorm T i) ^ 2 ∧
    (rowNorm T i) ^ 2 ≤ (1 + γ) * frobNormSq T / (m : ℝ)

/-- Uniform average of a row functional over a finite user set. -/
def avgOver {m : ℕ} (S : Finset (Fin m)) (f : Fin m → ℝ) : ℝ :=
  (S.card : ℝ)⁻¹ * ∑ i ∈ S, f i

end

end Qatlib.Papers.Recommender18.MainResults
