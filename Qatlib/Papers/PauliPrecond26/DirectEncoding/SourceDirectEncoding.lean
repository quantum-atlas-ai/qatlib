/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Complex.Basic
public import Qatlib.Concepts.BlockEncoding.Basic

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Direct block encodings and parameter identities

Source: H. Nie, Z. Lai, D. An, *Pauli-structured preconditioning for quantum
linear system solvers*, arXiv:2606.01733v1, Propositions 7 and 15 and Theorem 8.

The circuit identity is proved algebraically for arbitrary matrices. Encoding
existence is proved by an exact contraction completion: for a contraction A,
the two frames (1, 0) and (A, sqrt(1 - Aᴴ * A)) compress the identity to A.
All matrix norms are Euclidean operator norms, including for empty index types.

Proposition 7 includes the missing nonnegative margin assumption. The paper
assumes δ ∈ (0, 1/2]; nonnegativity suffices for the existence statement here.
Without it the proposed normalization can be smaller than the target norm.

Theorem 8 states real parameter identities with total division, including zero
denominators. Proposition 15 combines the circuit identity for arbitrary U with
encoding existence for a norm-bounded H. No relation U = exp(iH), query bound,
gate count, or synthesis procedure is asserted by these Lean statements.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.Execution.WorkspaceCP
open scoped MatrixOrder

namespace Qatlib.Papers.PauliPrecond26.DirectEncoding

/-- Every contraction has an exact encoding between two frames on a doubled space. -/
private theorem contraction_encoding {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : ‖A‖ ≤ 1) :
    ∃ (W : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (L R : Matrix (ι ⊕ ι) ι ℂ),
      BlockEncoding A W L R 1 0 := by
  let S := CFC.sqrt (1 - Aᴴ * A)
  have hp : 0 ≤ 1 - Aᴴ * A := by
    apply sub_nonneg.mpr
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg A)).mp
    rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose_mul_self]
    nlinarith [norm_nonneg A]
  have hs : Sᴴ * S = 1 - Aᴴ * A := by
    change star S * S = _
    rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self _ hp
  refine ⟨1, Matrix.fromRows 1 0, Matrix.fromRows A S, ?_⟩
  refine ⟨?_, ?_, ?_, by norm_num, le_rfl, ?_⟩
  · exact one_mem _
  · simp [IsIsometry, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  · simp [IsIsometry, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows, hs]
  · simp [compress, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]

/-- A matrix bounded by a positive scale has an encoding with any nonnegative error. -/
private theorem scaled_encoding {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (α ε : ℝ) (hα : 0 < α) (hε : 0 ≤ ε) (hA : ‖A‖ ≤ α) :
    ∃ (W : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (L R : Matrix (ι ⊕ ι) ι ℂ),
      BlockEncoding A W L R α ε := by
  have hc : ‖α⁻¹ • A‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hα]
    exact (inv_mul_le_iff₀ hα).mpr (by simpa using hA)
  obtain ⟨W, L, R, h⟩ := contraction_encoding (α⁻¹ • A) hc
  have he : α⁻¹ • A = compress L W R := by
    have hz := h.error_le
    simpa only [one_smul, norm_le_zero_iff, sub_eq_zero] using hz
  refine ⟨W, L, R, h.unitary, h.left_isometry, h.right_isometry, hα, hε, ?_⟩
  rw [← he, smul_smul, mul_inv_cancel₀ hα.ne', one_smul, sub_self, norm_zero]
  exact hε

/-- The inverse operator norm of the matrix inverse. For invertible matrices
of positive dimension this is the smallest singular value. The definition uses
total inversion and also makes sense for singular matrices and dimension zero.

Source: Theorem 8, p. 8, and the definition of `σ_min` on p. 2. -/
def sigmaMin {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) : ℝ := ‖M⁻¹‖⁻¹

/-! ## The single-ancilla block model -/

/-- Controlled unitary `diag(1, U)` on `ι ⊕ ι` (ancilla basis `|0⟩`, `|1⟩`).

Source: Proposition 15, p. 12, "Let `cU` denote the controlled version of `U`
with a single control qubit". -/
def controlledU {ι : Type*} [DecidableEq ι] (U : Matrix ι ι ℂ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  fromBlocks (1 : Matrix ι ι ℂ) 0 0 U

/-- The adjoint control `diag(1, Uᴴ)`; this is `(controlledU U)ᴴ` (see
`controlledU_adjoint`). -/
def controlledUAdj {ι : Type*} [DecidableEq ι] (U : Matrix ι ι ℂ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  fromBlocks (1 : Matrix ι ι ℂ) 0 0 Uᴴ

/-- `ZX ⊗ I` in the ancilla block decomposition: `ZX = [[0,1],[-1,0]]`.

Source: Appendix B, Eq. (B6), the operator `(ZX ⊗ I)`. -/
def zxBlocks (ι : Type*) [DecidableEq ι] :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  fromBlocks (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) (-1 : Matrix ι ι ℂ) (0 : Matrix ι ι ℂ)

/-- The ancilla sandwich `⟨+|·|+⟩` of a matrix on `ι ⊕ ι`: the `½`-average of
its four `ι × ι` blocks.  This is `(⟨+| ⊗ I) M (|+⟩ ⊗ I)` with
`|+⟩ = (|0⟩+|1⟩)/√2`.

Source: Appendix B, Eq. (B6). -/
def ancillaPlusReduce {ι : Type*} (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) : Matrix ι ι ℂ :=
  (2 : ℂ)⁻¹ • (toBlocks₁₁ M + toBlocks₁₂ M + toBlocks₂₁ M + toBlocks₂₂ M)

/-- The "sine part" `(U - Uᴴ)/(2i)` of a matrix `U`.  For `U = e^{iH}` with
`H` Hermitian this is `sin(H)`; we name the algebraic quantity directly because
the matrix exponential is not modelled here.

Source: Proposition 15, p. 12, Eq. (B6), `sin(H) = -i(⟨+|⊗I)cU†(ZX⊗I)cU(|+⟩⊗I)`
when `U = e^{iH}`. -/
def sinPart {ι : Type*} (U : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (2 * Complex.I)⁻¹ • (U - Uᴴ)

/-! ## Block algebra -/

/-- Adjoint of the controlled-`U` block matrix: `(cU)† = cU†`.

Source: Appendix B, Eq. (B6), the controlled-`U` circuit. -/
theorem controlledU_adjoint {ι : Type*} [DecidableEq ι]
    (U : Matrix ι ι ℂ) : (controlledU U)ᴴ = controlledUAdj U := by
  unfold controlledU controlledUAdj
  rw [Matrix.fromBlocks_conjTranspose]
  simp [Matrix.conjTranspose_one, Matrix.conjTranspose_zero]

/-- Product of the adjoint controlled gate with the `ZX` block matrix:
`cU† (ZX ⊗ I) = [[0, 1], [-U†, 0]]`.

Source: Appendix B, Eq. (B6). -/
theorem controlledUAdj_mul_zx {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) :
    controlledUAdj U * zxBlocks ι
      = fromBlocks (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) (-(Uᴴ)) 0 := by
  unfold controlledUAdj zxBlocks
  rw [Matrix.fromBlocks_multiply]
  simp

/-- Left multiplication by `cU` on `[[0, 1], [-U†, 0]]`:
`[[0, 1], [-U†, 0]] cU = [[0, U], [-U†, 0]]`.

Source: Appendix B, Eq. (B6). -/
theorem fromBlocks_mul_controlledU {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) :
    fromBlocks (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) (-(Uᴴ)) 0 * controlledU U
      = fromBlocks (0 : Matrix ι ι ℂ) U (-(Uᴴ)) (0 : Matrix ι ι ℂ) := by
  unfold controlledU
  rw [Matrix.fromBlocks_multiply]
  simp

/-- `cU† (ZX ⊗ I) cU = [[0, U],[-U†, 0]]`.

Source: Appendix B, Eq. (B6), the constant-size circuit `cU†(ZX⊗I)cU`. -/
theorem controlled_conjugated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) :
    (controlledU U)ᴴ * zxBlocks ι * controlledU U
      = fromBlocks (0 : Matrix ι ι ℂ) U (-(Uᴴ)) (0 : Matrix ι ι ℂ) := by
  rw [controlledU_adjoint, controlledUAdj_mul_zx, fromBlocks_mul_controlledU]

/-- The `|+⟩` reduction of a block matrix:
`⟨+| [[A, B], [C, D]] |+⟩ = (A + B + C + D)/2`.

Source: Appendix B, Eq. (B6), the ancilla projection `⟨+| · |+⟩`. -/
theorem ancillaPlusReduce_fromBlocks {ι : Type*}
    (A B C D : Matrix ι ι ℂ) :
    ancillaPlusReduce (fromBlocks A B C D) = (2 : ℂ)⁻¹ • (A + B + C + D) := by
  unfold ancillaPlusReduce
  ext i j
  simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.of_apply]

/-- **Proposition 15 core identity (B6), algebraic form.**  For any matrix `U`,
the single-ancilla circuit computes the sine part:
`(U - U†)/(2i) = -i · ⟨+| cU†(ZX⊗I)cU |+⟩`.

For `U = e^{iH}` this is exactly the paper's `sin(H) = -i(⟨+|⊗I)cU†(ZX⊗I)cU(|+⟩⊗I)`
(Appendix B, Eq. (B6)); the step `(e^{iH} - e^{-iH})/(2i) = sin(H)` is the
definition of the matrix sine and is not modelled.

Source: Proposition 15, p. 12 and Appendix B, Eq. (B6). -/
theorem b6_circuit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) :
    sinPart U
      = (-Complex.I) • ancillaPlusReduce ((controlledU U)ᴴ * zxBlocks ι * controlledU U) := by
  unfold sinPart
  rw [controlled_conjugated, ancillaPlusReduce_fromBlocks]
  have hsub : (0 : Matrix ι ι ℂ) + U + (-(Uᴴ)) + 0 = U - Uᴴ := by
    rw [sub_eq_add_neg]
    abel
  rw [hsub]
  have hscalar : (2 * Complex.I)⁻¹ = (-Complex.I) * (2 : ℂ)⁻¹ := by
    rw [mul_inv, Complex.inv_I]
    ring
  rw [hscalar, smul_smul]

/-! ## Proposition 7 — direct block-encoding parameters  -/

/-- Proposition 7, maximal-time bound: if `t ≤ π(1-δ)/(2Λ)` and `‖Q‖ ≤ Λ`, then
`t‖Q‖ ≤ π(1-δ)/2`, the regime in which `sin` is injective on the spectrum.

Source: Proposition 7, p. 7 ("Since `t‖Q‖ ≤ tΛ_Q ≤ π(1-δ)/2 ..."). -/
theorem prop7_time_norm_le {q Λ δ t : ℝ} (hΛ : 0 < Λ) (hq : q ≤ Λ)
    (ht : 0 < t) (htle : t ≤ Real.pi * (1 - δ) / (2 * Λ)) :
    t * q ≤ Real.pi * (1 - δ) / 2 := by
  have h1 : t * q ≤ t * Λ := mul_le_mul_of_nonneg_left hq (le_of_lt ht)
  have h2 : t * Λ ≤ (Real.pi * (1 - δ) / (2 * Λ)) * Λ :=
    mul_le_mul_of_nonneg_right htle (le_of_lt hΛ)
  have h3 : (Real.pi * (1 - δ) / (2 * Λ)) * Λ = Real.pi * (1 - δ) / 2 := by
    rw [div_mul_eq_mul_div]
    exact mul_div_mul_right (Real.pi * (1 - δ)) 2 (ne_of_gt hΛ)
  linarith

/-- Proposition 7, normalization at the maximal admissible time: for
`t_Q = π(1-δ)/(2Λ)`, `π/(2t_Q) = Λ/(1-δ)`.

Source: Proposition 7, p. 7, Eq. (10) and the sentence "Taking the largest
admissible time `t_Q := π(1-δ)/(2Λ_Q)` gives `(α_Q,a_Q,ε_Q) = (Λ_Q/(1-δ), 2, ε_Q)`". -/
theorem prop7_normalization_eq {Λ δ : ℝ} (hΛ : 0 < Λ) (hδ1 : δ < 1) :
    Real.pi / (2 * (Real.pi * (1 - δ) / (2 * Λ))) = Λ / (1 - δ) := by
  have h1 : (1 - δ) ≠ 0 := by linarith
  field_simp [Real.pi_ne_zero, ne_of_gt hΛ, h1]

/-- Proposition 7: the maximal-time bound, normalization identity, and existence
of an exact encoding (hence an encoding at any nonnegative error).
The nonnegative margin is required so the normalization bounds the target norm.
Source: arXiv:2606.01733v1, Proposition 7, Eq. (10). -/
theorem proposition7 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℂ) (Λ δ t εQ : ℝ)
    (hΛ : 0 < Λ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hQnorm : ‖Q‖ ≤ Λ)
    (hmax : t = Real.pi * (1 - δ) / (2 * Λ)) (_hεQ : 0 ≤ εQ) :
    (t * ‖Q‖ ≤ Real.pi * (1 - δ) / 2) ∧
    (Real.pi / (2 * t) = Λ / (1 - δ)) ∧
    (∃ (W : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (L R : Matrix (ι ⊕ ι) ι ℂ),
      BlockEncoding Q W L R (Real.pi / (2 * t)) εQ) := by
  have ht0 : 0 < t := by
    rw [hmax]
    exact div_pos (mul_pos Real.pi_pos (by linarith)) (by linarith)
  have htle : t ≤ Real.pi * (1 - δ) / (2 * Λ) := by rw [hmax]
  refine ⟨?_, ?_, ?_⟩
  · exact prop7_time_norm_le hΛ hQnorm ht0 htle
  · rw [hmax]
    exact prop7_normalization_eq hΛ hδ1
  · have hα : 0 < Real.pi / (2 * t) := div_pos Real.pi_pos (by positivity)
    have hbound : ‖Q‖ ≤ Real.pi / (2 * t) := by
      rw [hmax, prop7_normalization_eq hΛ hδ1]
      apply hQnorm.trans
      apply (le_div_iff₀ (by linarith : 0 < 1 - δ)).mpr
      nlinarith
    exact scaled_encoding Q _ εQ hα _hεQ hbound

/-! ## Theorem 8 — effective QLS parameters for direct preconditioners  -/

/-- The real-valued effective QLS condition parameter `κ_eff(M; α) = α/σ_min(M)`
used in Theorem 8 (Eq. 11).  Unlike the `ℝ≥0∞`-valued `EncodingObstr.kappaEff`,
this is the finite, real-valued quantity the paper manipulates on the
invertible branch.  `σ_min` is `PauliMerge.sigmaMin` (`= ‖M⁻¹‖⁻¹`).

Source: Theorem 8, p. 8, Eq. (11); definition (5) of the paper. -/
def kappaEffReal {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (α : ℝ) : ℝ :=
  α / sigmaMin M

/-- Theorem 8, Eq. (11): with `α_Q = Λ_Q/(1-δ)`,
`κ_eff(Q; α_Q) = Λ_Q/((1-δ)σ_min(Q))`.

Source: Theorem 8, p. 8, Eq. (11). -/
theorem theorem8_kappaEff {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℂ) (Λ δ : ℝ) :
    kappaEffReal Q (Λ / (1 - δ)) = Λ / ((1 - δ) * sigmaMin Q) := by
  unfold kappaEffReal
  rw [div_div]

/-- Theorem 8, Eq. (12): the block-encoding precision parameter
`α_Q/ε_Q = Λ_Q/((1-δ)ε_Q)`.

Source: Theorem 8, p. 8, Eq. (12). -/
theorem theorem8_precision {Λ δ αQ εQ : ℝ} (hα : αQ = Λ / (1 - δ)) :
    αQ / εQ = Λ / ((1 - δ) * εQ) := by
  rw [hα, div_div]

/-- Theorem 8, improvement criterion: the direct block-encoding precision
contribution is no worse than the baseline, Eq. (17),
`Λ_Q/((1-δ)ε_Q) ≲ α_A/ε_A`, equivalently `Λ_Q ε_A ≤ α_A(1-δ)ε_Q`.

Source: Theorem 8, p. 8, Eq. (17) and surrounding text. -/
theorem theorem8_condition {Λ δ αA εQ εA : ℝ}
    (hδ1 : δ < 1) (hεQ : 0 < εQ) (hεA : 0 < εA) :
    (Λ / ((1 - δ) * εQ) ≤ αA / εA) ↔ (Λ * εA ≤ αA * (1 - δ) * εQ) := by
  have h2 : 0 < (1 - δ) * εQ := mul_pos (by linarith) hεQ
  rw [div_le_div_iff₀ h2 hεA]
  constructor <;> intro h <;> simpa [mul_assoc] using h

/-- **Theorem 8.**  For an invertible Hermitian operator `Q` directly
block-encoded with `α_Q = Λ_Q/(1-δ)`, the effective QLS parameters entering the
standard solver are `κ_eff(Q;α_Q) = Λ_Q/((1-δ)σ_min(Q))` (Eq. 11) and
`α_Q/ε_Q = Λ_Q/((1-δ)ε_Q)` (Eq. 12), so the matrix-oracle query complexity (13)
`T_A(κ_eff, α_Q/ε_Q, 1/ε)` may be written with those substituted arguments.

`T_A` is kept abstract: the paper invokes a *standard QLS solver* whose query
complexity is not re-derived here (interface), exactly as the paper treats it as
a black box.  The substantive parameter algebra (11), (12), (13) is proved.

Source: Theorem 8, p. 8, Eqs. (11)--(13). -/
theorem theorem8 {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℂ) (Λ δ αQ εQ ε : ℝ)
    (hα : αQ = Λ / (1 - δ)) (TA : ℝ → ℝ → ℝ → ℝ) :
    (kappaEffReal Q αQ = Λ / ((1 - δ) * sigmaMin Q)) ∧
    (αQ / εQ = Λ / ((1 - δ) * εQ)) ∧
    (TA (kappaEffReal Q αQ) (αQ / εQ) (1 / ε)
       = TA (Λ / ((1 - δ) * sigmaMin Q)) (Λ / ((1 - δ) * εQ)) (1 / ε)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold kappaEffReal
    rw [hα, div_div]
  · exact theorem8_precision hα
  · rw [hα, theorem8_kappaEff, div_div]

/-! ## Proposition 15 — single-ancilla matrix-logarithm construction  -/

/-- Proposition 15: the algebraic circuit identity and existence of an encoding
at scale π/2. The identity holds for arbitrary U; the existential encoding uses
a contraction completion of H and asserts no circuit cost or relation to U.
The upper bounds on the margin and error are unnecessary for this existence statement.
Source: arXiv:2606.01733v1, Proposition 15 and Appendix B. -/
theorem proposition15 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H U : Matrix ι ι ℂ) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε)
    (hHnorm : ‖H‖ ≤ Real.pi / 2 * (1 - δ)) :
    sinPart U
        = (-Complex.I) • ancillaPlusReduce ((controlledU U)ᴴ * zxBlocks ι * controlledU U) ∧
    (∃ (W : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (L R : Matrix (ι ⊕ ι) ι ℂ),
        BlockEncoding H W L R (Real.pi / 2) ε) := by
  refine ⟨b6_circuit U, scaled_encoding H _ ε (by positivity) hε.le ?_⟩
  nlinarith [Real.pi_pos]

end Qatlib.Papers.PauliPrecond26.DirectEncoding
