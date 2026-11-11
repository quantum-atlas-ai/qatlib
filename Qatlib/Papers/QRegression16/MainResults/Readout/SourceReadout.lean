/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRegression16.MainResults.SourceModel
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fintype.BigOperators

set_option backward.isDefEq.respectTransparency false

/-!
# SourceReadout — c003 of QRegression16

Fixed arXiv:1601.07823v2 (Schuld–Sinayskiy–Petruccione), *Prediction by linear
regression on a quantum computer*, Section III.D (executing the inner products,
p.4–5).

The algorithm prepares the two states

* `|ψ₁⟩ = p(1)^{-1/2} Σ_r (c/σ_r) |v_r⟩|u_r⟩` (Eq. (9)), and
* `|ψ₂⟩ = |ψ_y⟩|ψ_x̃⟩` with amplitudes `y(m) x̃(j)` (Eq. (5)–(6)),

entangles them with an ancilla as `2^{-1/2}(|ψ₁⟩|0⟩ + |ψ₂⟩|1⟩)` (Eq. (10)) and
traces out all but the ancilla. The paper's displayed result is that the
off-diagonal element of the ancilla density matrix is

`ρ₁₂ = ρ₂₁ = (c / (2 √p(1))) Σ_r (σ_r)⁻¹ (Σ_j v_{jr} x̃_j)(Σ_m u_{rm} y_m)`

"and contain[s] the desired result (3) up to a known normalisation factor".

Formalised here:

* `psiOne_apply`: the entrywise definition of `|ψ₁⟩` is the matrix product
  `(1/√p) U diag(c/σ) Vᵀ`, which is the algebraic identity behind Eq. (7) and (9);
* `inner_psiOne_psiTwo`: the bilinear-form evaluation
  `⟨ψ₁|ψ₂⟩ = (1/√p) Σ_r (c/σ_r)(v_rᵀx̃)(u_rᵀy)`.
  The real symmetric inner product is the same bilinear form studied in the
  shared layer `QuantumAlgorithm.Concepts.SqEstimation.InnerProduct`; no
  conjugation is used because the source data are real;
* `ancilla_offdiagonal_eq_prediction`: the paper's displayed Eq. (10) readout,
  `ρ₀₁ = c/(2√p) · predictionFromSVD`, showing that the prediction is exactly
  the measured ancilla coherence up to the known factor `c/(2√p)`;
* `psiOne_normalized`: `|ψ₁⟩` is a unit vector when `p` is the norm of its
  unnormalised amplitude vector, `p = Σ_r (c/σ_r)²`;
* `ancilla_diagonal_of_normalized`: the diagonal entries of the ancilla are
  `1/2` when both `|ψ₁⟩` and `|ψ₂⟩` are unit vectors (the `|ψ₂⟩` normalisation
  is the paper's amplitude-encoding assumption);
* `swapTestAcceptance_neg_right` / `ancilla_offdiagonal_neg_right`: the sign
  blindness of the plain SWAP test (`1/2 + 1/2|⟨ψ₁|ψ₂⟩|²` is invariant under
  `|ψ₂⟩ ↦ -|ψ₂⟩`) and the sign sensitivity of the ancilla off-diagonal, which is
  exactly the motivation of Section III.D for using Eq. (10) instead.

Source remark on normalisation. Eq. (9) normalises `|ψ₁⟩` by `√p(1)` with
`|ψ₁⟩ ∝ Σ_r (c/σ_r)|v_r⟩|u_r⟩`; the displayed `p(1) = Σ_r (c/λ_r)²` of
Section IV is written for the conditional-rotation step with `λ_r = σ_r²`. The
state-normalisation constant of Eq. (9) is therefore `Σ_r (c/σ_r)²`, which is
what `psiOne_normalized` uses; the κ-scaling claim itself is formalised
independently in `Postselection/SourcePostselection.lean`.

The Moore–Penrose/least-squares identification of the read-out value with the
fitted prediction is proved in `Prediction/SourcePrediction.lean`, whose
pseudoinverse contract is the real counterpart of
`QuantumAlgorithm.Concepts.QlsReadoutSpec.PseudoInverse.singular_hermitian_pseudoinverse_and_least_squares`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QRegression16.MainResults.Readout

open Qatlib.Papers.QRegression16.MainResults.SourceModel

variable {N M R : ℕ}

/-! ## The state `|ψ₁⟩` as a matrix product -/

/-- Fixed arXiv:1601.07823v2, Section III.C Eq. (9) (with Eq. (7)): the entry
`(m,j)` of the post-selected state is `(1/√p) (U diag(c/σ) Vᵀ)(m,j)`. -/
theorem psiOne_apply (σ : Fin R → ℝ) (U : Matrix (Fin M) (Fin R) ℝ)
    (V : Matrix (Fin N) (Fin R) ℝ) (c p : ℝ) (m : Fin M) (j : Fin N) :
    psiOne σ U V c p (m, j) =
      (1 / Real.sqrt p) * (U * diagonal (fun r => c / σ r) * Vᵀ) m j := by
  simp only [psiOne]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Matrix.diagonal_mul, Matrix.transpose_apply]
  ring

/-- The entrywise double sum `Σ_{m,j} A(m,j) y(m) x(j)` is the bilinear form
`y ⬝ᵥ (A *ᵥ x)`. Used to evaluate `⟨ψ₁|ψ₂⟩` in Section III.D. -/
theorem entry_sum_eq_dotProduct {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ)
    (y : Fin M → ℝ) (x : Fin N → ℝ) :
    ∑ m, ∑ j, A m j * (y m * x j) = y ⬝ᵥ (A *ᵥ x) := by
  simp only [dotProduct, mulVec]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- Fixed arXiv:1601.07823v2, Section III.D p.4: the inner product of the two
prepared states is

`⟨ψ₁|ψ₂⟩ = (1/√p) Σ_r (c/σ_r)(v_rᵀx̃)(u_rᵀy)`,

which is the singular-component prediction times `c/√p`. This is the algebraic
content of the displayed equation for `ρ₁₂` before the `1/2` from the ancilla. -/
theorem inner_psiOne_psiTwo (σ : Fin R → ℝ) (U : Matrix (Fin M) (Fin R) ℝ)
    (V : Matrix (Fin N) (Fin R) ℝ) (c p : ℝ) (x : Fin N → ℝ) (y : Fin M → ℝ) :
    sourceInner (psiOne σ U V c p) (psiTwo x y) =
      (1 / Real.sqrt p) * ∑ r, (c / σ r) * ((Vᵀ *ᵥ x) r) * ((Uᵀ *ᵥ y) r) := by
  have hpsi : ∀ q : Fin M × Fin N, psiOne σ U V c p q =
      (1 / Real.sqrt p) * (U * diagonal (fun r => c / σ r) * Vᵀ) q.1 q.2 := by
    rintro ⟨m, j⟩
    exact psiOne_apply σ U V c p m j
  unfold sourceInner psiTwo
  rw [Fintype.sum_prod_type]
  simp only [hpsi]
  have h1 : (∑ m, ∑ j, ((1 / Real.sqrt p) *
        (U * diagonal (fun r => c / σ r) * Vᵀ) m j) * (y m * x j)) =
      (1 / Real.sqrt p) * ∑ m, ∑ j,
        (U * diagonal (fun r => c / σ r) * Vᵀ) m j * (y m * x j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [h1, entry_sum_eq_dotProduct (U * diagonal (fun r => c / σ r) * Vᵀ) y x]
  have h3 : y ⬝ᵥ ((U * diagonal (fun r => c / σ r) * Vᵀ) *ᵥ x) =
      ∑ r, (c / σ r) * ((Vᵀ *ᵥ x) r) * ((Uᵀ *ᵥ y) r) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  rw [h3]

/-! ## Ancilla density matrix entries -/

/-- Fixed arXiv:1601.07823v2, Section III.D Eq. (10): the top-left entry of the
ancilla density matrix is `(1/2)⟨ψ₁|ψ₁⟩`. -/
theorem ancillaDensity_00 {N M : ℕ} (ψ₁ ψ₂ : Fin M × Fin N → ℝ) :
    (ancillaDensity ψ₁ ψ₂) 0 0 = (1 / 2) * sourceInner ψ₁ ψ₁ := by
  simp [ancillaDensity]

/-- Fixed arXiv:1601.07823v2, Section III.D Eq. (10): the off-diagonal entry is
`(1/2)⟨ψ₁|ψ₂⟩`. -/
theorem ancillaDensity_01 {N M : ℕ} (ψ₁ ψ₂ : Fin M × Fin N → ℝ) :
    (ancillaDensity ψ₁ ψ₂) 0 1 = (1 / 2) * sourceInner ψ₁ ψ₂ := by
  simp [ancillaDensity]

/-- Fixed arXiv:1601.07823v2, Section III.D Eq. (10): the bottom-right entry of
the ancilla density matrix is `(1/2)⟨ψ₂|ψ₂⟩`. -/
theorem ancillaDensity_11 {N M : ℕ} (ψ₁ ψ₂ : Fin M × Fin N → ℝ) :
    (ancillaDensity ψ₁ ψ₂) 1 1 = (1 / 2) * sourceInner ψ₂ ψ₂ := by
  simp [ancillaDensity]

/-- Fixed arXiv:1601.07823v2, Section III.D p.4: the off-diagonal element of the
ancilla density matrix after tracing out the registers contains the desired
prediction,

`ρ₀₁ = (c / (2√p)) · Σ_r (σ_r)⁻¹ (v_rᵀx̃)(u_rᵀy) = (c/(2√p)) · predictionFromSVD`,

up to the known normalisation factor `c/(2√p)` (the paper's "known
normalisation factor"). -/
theorem ancilla_offdiagonal_eq_prediction (σ : Fin R → ℝ)
    (U : Matrix (Fin M) (Fin R) ℝ) (V : Matrix (Fin N) (Fin R) ℝ)
    (c p : ℝ) (x : Fin N → ℝ) (y : Fin M → ℝ) (hp : 0 < p) :
    (ancillaDensity (psiOne σ U V c p) (psiTwo x y)) 0 1 =
      (c / (2 * Real.sqrt p)) * predictionFromSVD σ U V x y := by
  rw [ancillaDensity_01, inner_psiOne_psiTwo]
  have hsum : (∑ r, (c / σ r) * ((Vᵀ *ᵥ x) r) * ((Uᵀ *ᵥ y) r)) =
      c * ∑ r, (σ r)⁻¹ * ((Vᵀ *ᵥ x) r) * ((Uᵀ *ᵥ y) r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [div_eq_mul_inv]
    ring
  rw [hsum]
  unfold predictionFromSVD
  have hsp : Real.sqrt p ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  field_simp

/-! ## Normalisation of the prepared states -/

/-- The squared Hilbert–Schmidt norm of `U diag(a) Vᵀ` is `Σ_r a_r²` whenever
the singular-vector matrices are orthonormal on their used `R` columns. -/
theorem sum_sq_mul_eq (a : Fin R → ℝ) (U : Matrix (Fin M) (Fin R) ℝ)
    (V : Matrix (Fin N) (Fin R) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    ∑ m, ∑ j, (U * diagonal a * Vᵀ) m j * (U * diagonal a * Vᵀ) m j =
      ∑ r, (a r) ^ 2 := by
  have htr : (∑ m, ∑ j,
        (U * diagonal a * Vᵀ) m j * (U * diagonal a * Vᵀ) m j) =
      Matrix.trace ((U * diagonal a * Vᵀ)ᵀ * (U * diagonal a * Vᵀ)) := by
    simp only [Matrix.trace]
    rw [show (∑ i, Matrix.diag ((U * diagonal a * Vᵀ)ᵀ *
            (U * diagonal a * Vᵀ)) i) =
        ∑ i, ∑ j, (U * diagonal a * Vᵀ) j i *
          (U * diagonal a * Vᵀ) j i from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Matrix.diag_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Matrix.transpose_apply]]
    rw [Finset.sum_comm]
  have hMM : ((U * diagonal a * Vᵀ)ᵀ * (U * diagonal a * Vᵀ)) =
      V * diagonal (fun r => (a r) ^ 2) * Vᵀ := by
    have htrans : (U * diagonal a * Vᵀ)ᵀ = V * diagonal a * Uᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [htrans]
    calc (V * diagonal a * Uᵀ) * (U * diagonal a * Vᵀ)
        = V * (diagonal a * (Uᵀ * (U * (diagonal a * Vᵀ)))) := by
          simp only [Matrix.mul_assoc]
      _ = V * (diagonal a * ((Uᵀ * U) * (diagonal a * Vᵀ))) := by
          rw [← Matrix.mul_assoc Uᵀ U (diagonal a * Vᵀ)]
      _ = V * (diagonal a *
            ((1 : Matrix (Fin R) (Fin R) ℝ) * (diagonal a * Vᵀ))) := by rw [hU]
      _ = V * (diagonal a * (diagonal a * Vᵀ)) := by rw [Matrix.one_mul]
      _ = V * ((diagonal a * diagonal a) * Vᵀ) := by
          rw [Matrix.mul_assoc (diagonal a) (diagonal a) Vᵀ]
      _ = V * (diagonal (fun r => (a r) ^ 2) * Vᵀ) := by
          rw [Matrix.diagonal_mul_diagonal]
          simp only [pow_two]
      _ = V * diagonal (fun r => (a r) ^ 2) * Vᵀ := by rw [← Matrix.mul_assoc]
  have htrace : Matrix.trace (V * diagonal (fun r => (a r) ^ 2) * Vᵀ) =
      ∑ r, (a r) ^ 2 := by
    rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul, Matrix.trace_diagonal]
  rw [htr, hMM, htrace]

/-- Fixed arXiv:1601.07823v2, Section III.C Eq. (9): the norm of `|ψ₁⟩` is
`(1/√p)² Σ_r (c/σ_r)²`, i.e. `|ψ₁⟩` is normalised exactly when `p` equals the
squared norm of its unnormalised amplitude vector. -/
theorem inner_psiOne_self (σ : Fin R → ℝ) (U : Matrix (Fin M) (Fin R) ℝ)
    (V : Matrix (Fin N) (Fin R) ℝ) (c p : ℝ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) :
    sourceInner (psiOne σ U V c p) (psiOne σ U V c p) =
      (1 / Real.sqrt p) ^ 2 * ∑ r, (c / σ r) ^ 2 := by
  have hpsi : ∀ q : Fin M × Fin N, psiOne σ U V c p q =
      (1 / Real.sqrt p) * (U * diagonal (fun r => c / σ r) * Vᵀ) q.1 q.2 := by
    rintro ⟨m, j⟩
    exact psiOne_apply σ U V c p m j
  unfold sourceInner
  rw [Fintype.sum_prod_type]
  simp only [hpsi]
  have h1 : (∑ m, ∑ j, ((1 / Real.sqrt p) *
        (U * diagonal (fun r => c / σ r) * Vᵀ) m j) *
        ((1 / Real.sqrt p) * (U * diagonal (fun r => c / σ r) * Vᵀ) m j)) =
      (1 / Real.sqrt p) ^ 2 * ∑ m, ∑ j,
        (U * diagonal (fun r => c / σ r) * Vᵀ) m j *
          (U * diagonal (fun r => c / σ r) * Vᵀ) m j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [h1, sum_sq_mul_eq (fun r => c / σ r) U V hU hV]

/-- Fixed arXiv:1601.07823v2, Section III.C Eq. (9): `|ψ₁⟩` is a unit vector
when `p = Σ_r (c/σ_r)²`. -/
theorem psiOne_normalized (σ : Fin R → ℝ) (U : Matrix (Fin M) (Fin R) ℝ)
    (V : Matrix (Fin N) (Fin R) ℝ) (c p : ℝ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hp : p = ∑ r, (c / σ r) ^ 2) (hp0 : 0 < p) :
    sourceInner (psiOne σ U V c p) (psiOne σ U V c p) = 1 := by
  rw [inner_psiOne_self σ U V c p hU hV, ← hp]
  have hsq : (1 / Real.sqrt p) ^ 2 = 1 / p := by
    rw [div_pow, one_pow, Real.sq_sqrt hp0.le]
  rw [hsq]
  field_simp

/-- The states `|ψ₂⟩ = |ψ_y⟩|ψ_x̃⟩` have norm `⟨x|x⟩⟨y|y⟩`; with unit
amplitude-encoded inputs this is `1`. -/
theorem inner_psiTwo_self (x : Fin N → ℝ) (y : Fin M → ℝ) :
    sourceInner (psiTwo x y) (psiTwo x y) = sourceInner x x * sourceInner y y := by
  unfold sourceInner psiTwo
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun m _ => ?_)
  ring

/-- `|ψ₂⟩` is normalised for unit amplitude encodings of `x̃` and `y`. -/
theorem inner_psiTwo_normalized (x : Fin N → ℝ) (y : Fin M → ℝ)
    (hx : sourceInner x x = 1) (hy : sourceInner y y = 1) :
    sourceInner (psiTwo x y) (psiTwo x y) = 1 := by
  rw [inner_psiTwo_self, hx, hy]
  ring

/-- Fixed arXiv:1601.07823v2, Section III.D Eq. (10): when `|ψ₁⟩` and `|ψ₂⟩`
are unit vectors, the ancilla density matrix has both diagonal entries `1/2`,
i.e. the ancilla is in the maximally mixed state on the diagonal. -/
theorem ancilla_diagonal_of_normalized {N M : ℕ} (ψ₁ ψ₂ : Fin M × Fin N → ℝ)
    (h1 : sourceInner ψ₁ ψ₁ = 1) (h2 : sourceInner ψ₂ ψ₂ = 1) :
    (ancillaDensity ψ₁ ψ₂) 0 0 = 1 / 2 ∧ (ancillaDensity ψ₁ ψ₂) 1 1 = 1 / 2 := by
  constructor
  · rw [ancillaDensity_00, h1, mul_one]
  · rw [ancillaDensity_11, h2, mul_one]

/-! ## Sign blindness of the SWAP test -/

/-- Bilinearity: the inner product against a negated vector flips sign. -/
theorem inner_neg_right {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    sourceInner a (fun i => -b i) = -sourceInner a b := by
  unfold sourceInner
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- Fixed arXiv:1601.07823v2, Section III.D p.4: the plain SWAP test measures
`1/2 + 1/2|⟨ψ₁|ψ₂⟩|²`, which is invariant under `|ψ₂⟩ ↦ -|ψ₂⟩` and hence cannot
reveal the sign of the prediction. -/
theorem swapTestAcceptance_neg_right {N M : ℕ} (ψ₁ ψ₂ : Fin M × Fin N → ℝ) :
    swapTestAcceptance ψ₁ (fun q => -ψ₂ q) = swapTestAcceptance ψ₁ ψ₂ := by
  unfold swapTestAcceptance
  rw [inner_neg_right]
  ring

/-- Fixed arXiv:1601.07823v2, Section III.D p.4: in contrast to the SWAP test,
the ancilla off-diagonal element is odd under `|ψ₂⟩ ↦ -|ψ₂⟩`, so it does carry
the sign of the prediction. This is the reason Eq. (10) replaces the direct
SWAP test. -/
theorem ancilla_offdiagonal_neg_right {N M : ℕ} (ψ₁ ψ₂ : Fin M × Fin N → ℝ) :
    (ancillaDensity ψ₁ (fun q => -ψ₂ q)) 0 1 = -(ancillaDensity ψ₁ ψ₂) 0 1 := by
  rw [ancillaDensity_01, ancillaDensity_01, inner_neg_right]
  ring

/-- **Claim c003 (fixed arXiv:1601.07823v2, Section III.D, p.4–5).** Prediction
readout from the ancilla off-diagonal: for unit amplitude-encoded states
`|ψ_y⟩`, `|ψ_x̃⟩` and a normalised `|ψ₁⟩`, the ancilla density matrix obtained by
tracing out all registers in Eq. (10) has diagonal entries `1/2` and
off-diagonal element `(c/(2√p)) · predictionFromSVD`, i.e. the desired linear
regression prediction up to the known factor `c/(2√p)`. -/
theorem source_readout_from_offdiagonal (σ : Fin R → ℝ)
    (U : Matrix (Fin M) (Fin R) ℝ) (V : Matrix (Fin N) (Fin R) ℝ)
    (c p : ℝ) (x : Fin N → ℝ) (y : Fin M → ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hp : p = ∑ r, (c / σ r) ^ 2) (hp0 : 0 < p)
    (hx : sourceInner x x = 1) (hy : sourceInner y y = 1) :
    sourceInner (psiOne σ U V c p) (psiOne σ U V c p) = 1 ∧
    (ancillaDensity (psiOne σ U V c p) (psiTwo x y)) 0 0 = 1 / 2 ∧
    (ancillaDensity (psiOne σ U V c p) (psiTwo x y)) 1 1 = 1 / 2 ∧
    (ancillaDensity (psiOne σ U V c p) (psiTwo x y)) 0 1 =
      (c / (2 * Real.sqrt p)) * predictionFromSVD σ U V x y := by
  have h1 : sourceInner (psiOne σ U V c p) (psiOne σ U V c p) = 1 :=
    psiOne_normalized σ U V c p hU hV hp hp0
  have h2 : sourceInner (psiTwo x y) (psiTwo x y) = 1 :=
    inner_psiTwo_normalized x y hx hy
  obtain ⟨hd0, hd1⟩ := ancilla_diagonal_of_normalized
    (psiOne σ U V c p) (psiTwo x y) h1 h2
  exact ⟨h1, hd0, hd1, ancilla_offdiagonal_eq_prediction σ U V c p x y hp0⟩

end Qatlib.Papers.QRegression16.MainResults.Readout
