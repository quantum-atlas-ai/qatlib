/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceModel — linear-regression prediction on a quantum computer

Schuld, Sinayskiy and Petruccione, *Prediction by linear regression on a
quantum computer*, fixed arXiv:1601.07823v2.

This file fixes the paper's model in the form used by the MainResults claims:

* Section II p.2, Eq. (2)–(3): with the reduced singular value decomposition
  `X = U Σ Vᵀ` of the (real) data matrix `X`, the least-squares fit is
  `w = X⁺ y = V Σ⁻¹ Uᵀ y` and the prediction for a new input `x̃` is the scalar
  `ỹ = x̃ᵀ w = Σ_r σ_r⁻¹ (v_rᵀ x̃)(u_rᵀ y)`.
* Section III p.3–4, Eq. (4)–(9): amplitude-encoded states `|ψ_X⟩`, `|ψ_y⟩`,
  `|ψ_x̃⟩` and the post-selected state `|ψ₁⟩`.
* Section III.D Eq. (10): the ancilla state
  `2^{-1/2}(|ψ₁⟩|0⟩ + |ψ₂⟩|1⟩)` and its reduced `2 × 2` density matrix.
* Section IV p.5: post-selection probability `p(1) = Σ_r (c/λ_r)²` with
  `λ_r = (σ_r)²`, and the condition number `κ = σ_max / σ_min`.

Only the rank-`R` reduced singular data is assumed; no entrywise sparsity of
`X` is used, which is the structural point of the paper. The data are real, as
in the source (the source writes transposes, not adjoints).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QRegression16.MainResults.SourceModel

/-! ## Reduced SVD data and the least-squares prediction -/

/-- Source-fixed arXiv:1601.07823v2, Section II p.2 and Section III p.3 Eq. (7):
the data matrix reconstructed from its reduced SVD, `X = U Σ Vᵀ`, where
`U : M × R` and `V : N × R` carry the left/right singular vectors and
`σ : Fin R → ℝ` the singular values. Only `R` components are used, so no
sparsity of the `M × N` matrix is required. -/
def dataMatrix {N M R : ℕ} (σ : Fin R → ℝ) (U : Matrix (Fin M) (Fin R) ℝ)
    (V : Matrix (Fin N) (Fin R) ℝ) : Matrix (Fin M) (Fin N) ℝ :=
  U * diagonal σ * Vᵀ

/-- Source-fixed arXiv:1601.07823v2, Section II p.2 Eq. (2): the reduced
Moore–Penrose pseudoinverse `X⁺ = V Σ⁻¹ Uᵀ` of the reduced-SVD data matrix.
The four Moore–Penrose identities are proved from the orthonormality of the
singular-vector matrices in `Prediction/SourcePrediction.lean`. -/
def pseudoinverseCandidate {N M R : ℕ} (σ : Fin R → ℝ)
    (U : Matrix (Fin M) (Fin R) ℝ) (V : Matrix (Fin N) (Fin R) ℝ) :
    Matrix (Fin N) (Fin M) ℝ :=
  V * diagonal (fun r => (σ r)⁻¹) * Uᵀ

/-- Source-fixed arXiv:1601.07823v2, Section II p.2 Eq. (2): the fitted
parameter vector `w = X⁺ y` of the least-squares linear regression. -/
def fittedWeights {N M R : ℕ} (σ : Fin R → ℝ) (U : Matrix (Fin M) (Fin R) ℝ)
    (V : Matrix (Fin N) (Fin R) ℝ) (y : Fin M → ℝ) : Fin N → ℝ :=
  pseudoinverseCandidate σ U V *ᵥ y

/-- Source-fixed arXiv:1601.07823v2, Section II p.2 Eq. (3): the prediction
`ỹ = Σ_r σ_r⁻¹ (v_rᵀ x̃)(u_rᵀ y)` of the linear-regression model for a new
input `x̃`, expressed through the singular components. The vectors `v_r`
(resp. `u_r`) are the columns of `V` (resp. `U`), so `v_rᵀ x̃ = (Vᵀ *ᵥ x̃) r`. -/
def predictionFromSVD {N M R : ℕ} (σ : Fin R → ℝ) (U : Matrix (Fin M) (Fin R) ℝ)
    (V : Matrix (Fin N) (Fin R) ℝ) (x : Fin N → ℝ) (y : Fin M → ℝ) : ℝ :=
  ∑ r, (σ r)⁻¹ * ((Vᵀ *ᵥ x) r) * ((Uᵀ *ᵥ y) r)

/-- The prediction evaluated through the fitted weights: `x̃ᵀ w`. This is the
quantity produced by the algorithm's single-qubit readout (Eq. (3) and
Section III.D). -/
def predictionByWeights {N M R : ℕ} (σ : Fin R → ℝ)
    (U : Matrix (Fin M) (Fin R) ℝ) (V : Matrix (Fin N) (Fin R) ℝ)
    (x : Fin N → ℝ) (y : Fin M → ℝ) : ℝ :=
  x ⬝ᵥ fittedWeights σ U V y

/-! ## Amplitude-encoded states and the ancilla readout -/

/-- The real inner product (bilinear, no conjugation) used for the paper's
amplitude-encoded real data. -/
def sourceInner {ι : Type*} [Fintype ι] (a b : ι → ℝ) : ℝ :=
  ∑ i, a i * b i

/-- Source-fixed arXiv:1601.07823v2, Section III p.4 Eq. (9): the post-selected
state `|ψ₁⟩ = p(1)^{-1/2} Σ_r (c/σ_r) |v_r⟩|u_r⟩`, on the composite register
indexed by `(m, j)` (left singular register first, then right). -/
def psiOne {N M R : ℕ} (σ : Fin R → ℝ) (U : Matrix (Fin M) (Fin R) ℝ)
    (V : Matrix (Fin N) (Fin R) ℝ) (c p : ℝ) : Fin M × Fin N → ℝ :=
  fun ⟨m, j⟩ => (1 / Real.sqrt p) * ∑ r, (c / σ r) * U m r * V j r

/-- Source-fixed arXiv:1601.07823v2, Section III.D p.4 Eq. (10): the state
`|ψ₂⟩ = |ψ_y⟩|ψ_x̃⟩` on the same composite register, with amplitudes
`y(m) x̃(j)`. -/
def psiTwo {N M : ℕ} (x : Fin N → ℝ) (y : Fin M → ℝ) : Fin M × Fin N → ℝ :=
  fun ⟨m, j⟩ => y m * x j

/-- Source-fixed arXiv:1601.07823v2, Section III.D p.4 Eq. (10): after entangling
`|ψ₁⟩` and `|ψ₂⟩` with an ancilla and tracing out the registers, the ancilla
density matrix is `(1/2) [[⟨ψ₁|ψ₁⟩, ⟨ψ₁|ψ₂⟩], [⟨ψ₂|ψ₁⟩, ⟨ψ₂|ψ₂⟩]]`. -/
def ancillaDensity {N M : ℕ} (ψ₁ ψ₂ : Fin M × Fin N → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 / 2) * sourceInner ψ₁ ψ₁, (1 / 2) * sourceInner ψ₁ ψ₂;
     (1 / 2) * sourceInner ψ₂ ψ₁, (1 / 2) * sourceInner ψ₂ ψ₂]

/-- The acceptance probability of the swap test between `ψ₁` and `ψ₂`. In the
paper's sign-ambiguity discussion (Section III.D) this equals
`1/2 + 1/2 |⟨ψ₁|ψ₂⟩|²`, which cannot reveal the sign of `⟨ψ₁|ψ₂⟩`. -/
def swapTestAcceptance {N M : ℕ} (ψ₁ ψ₂ : Fin M × Fin N → ℝ) : ℝ :=
  (1 + (sourceInner ψ₁ ψ₂) ^ 2) / 2

/-! ## Post-selection probability and condition number -/

/-- Source-fixed arXiv:1601.07823v2, Section IV p.5: the probability
`p(1) = Σ_r (c/λ_r)²` of measuring the ancilla in the excited state, written in
terms of the eigenvalues `λ_r = (σ_r)²` of `X†X`. -/
def postselectionProbability {R : ℕ} (lam : Fin R → ℝ) (c : ℝ) : ℝ :=
  ∑ r, (c / lam r) ^ 2

/-- Source-fixed arXiv:1601.07823v2, Section IV p.5: the condition number
`κ = σ_max (σ_min)⁻¹` of `X`. -/
def conditionNumber (σmin σmax : ℝ) : ℝ :=
  σmax / σmin

end Qatlib.Papers.QRegression16.MainResults.SourceModel
