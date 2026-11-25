/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRegularLS22.MainResults.AugmentedSpectrum

@[expose] public section

/-!
# QRegularLS22 — the Hadamard mixture of two block encodings

Source: arXiv:2206.13143v2 (accepted in Quantum 2023-04-19), Lemma 22 (p.26), the
Hadamard-mixture step of the augmented-matrix construction.

Lemma 22 encodes `[[A, 0], [B, 0]]` by mixing the two branches `U_A` and `U_B`
with a Hadamard gate on a fresh SELECT qubit.  This module isolates that step in
its exact algebraic form, at a fixed width and without any ancilla bookkeeping:

* `flagMixGate a b` is `H ⊗ 1` on `Fin 2 × (K × I)`, with the real Hadamard
  `H = [[a, b], [b, -a]]`;
* `flagSelectGate W₀ W₁` is the flag-diagonal block matrix that applies `W₀` in
  the `0` branch and `W₁` in the `1` branch;
* `flagMix_blockCorner` computes the zero-flag corner of
  `H · diag(W₀, W₁) · H`: it is the convex mixture `a² • W₀ + b² • W₁`.

With `a² = α_A / (α_A + α_B)` and `b² = α_B / (α_A + α_B)` this is exactly the
paper's claim that the corner is `(α_A Ā + α_B B̄) / (α_A + α_B)`, which after
multiplication by `α_A + α_B` becomes the scale `α_A + α_B` of the augmented
matrix.  The mixture is unitary (`flagMix_mem_unitaryGroup`) whenever
`a² + b² = 1` and the two branches are unitary.

Boundary: this is the algebraic core only.  It does **not** state Lemma 22: the
two branch gates have to be built from `U_A` and `U_B` (one routing qubit that
moves the second data block out of the zero-ancilla corner, plus the ancilla
widening to `max a_A a_B`), the register has to be reindexed onto
`Enc (max a_A a_B + 2) (I ⊕ I)`, and the error ledger
`‖fromBlocks (A - α_A Ā) 0 (B - α_B B̄) 0‖ ≤ ε_A + ε_B` has to be estimated.
None of those steps is present here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators Kronecker

namespace Qatlib.Papers.QRegularLS22.MainResults

open Qatlib.Papers.QRegularLS22.MainResults
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

variable {K I : Type*} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]

/-! ## The real Hadamard gate and its unitarity -/

/-- The real two-by-two Hadamard gate `[[a, b], [b, -a]]`.  It is unitary exactly when
`a² + b² = 1`. -/
noncomputable def flagHadamard (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ), (b : ℂ); (b : ℂ), (-a : ℂ)]

/-- For real `a`, `b` with `a² + b² = 1` the squared amplitudes sum to one over `ℂ`. -/
theorem ofReal_pow_two_add {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    (a : ℂ) * (a : ℂ) + (b : ℂ) * (b : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    show a * a + b * b = 1 by simpa [pow_two] using h, Complex.ofReal_one]

/-- The real Hadamard gate is unitary when `a² + b² = 1`. -/
theorem flagHadamard_mem_unitaryGroup {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    flagHadamard a b ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flagHadamard, Matrix.mul_apply, Fin.sum_univ_two, Complex.conj_ofReal]
  all_goals first
    | linear_combination ofReal_pow_two_add h
    | ring

/-! ## The two gates of the mixture -/

/-- The SELECT flag gate `H ⊗ 1`: the Hadamard acts on the SELECT qubit and the identity
on the branch workspace `K × I`. -/
noncomputable def flagMixGate (a b : ℝ) :
    Matrix (Fin 2 × (K × I)) (Fin 2 × (K × I)) ℂ :=
  flagHadamard a b ⊗ₖ (1 : Matrix (K × I) (K × I) ℂ)

/-- The `H ⊗ 1` gate is unitary when the Hadamard is. -/
theorem flagMixGate_mem_unitaryGroup {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    flagMixGate (K := K) (I := I) a b ∈ Matrix.unitaryGroup (Fin 2 × (K × I)) ℂ :=
  Matrix.kronecker_mem_unitary (flagHadamard_mem_unitaryGroup h) (one_mem _)

/-- The flag-diagonal SELECT gate: `W₀` acts in the `0` branch and `W₁` in the `1`
branch, with the other flag entries zero. -/
noncomputable def flagSelectGate (W₀ W₁ : Matrix (K × I) (K × I) ℂ) :
    Matrix (Fin 2 × (K × I)) (Fin 2 × (K × I)) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (if p.1 = 0 then W₀ else W₁) p.2 q.2 else 0

/-- The flag-diagonal SELECT gate is unitary when both branches are. -/
theorem flagSelectGate_mem_unitaryGroup {W₀ W₁ : Matrix (K × I) (K × I) ℂ}
    (h₀ : W₀ ∈ Matrix.unitaryGroup (K × I) ℂ)
    (h₁ : W₁ ∈ Matrix.unitaryGroup (K × I) ℂ) :
    flagSelectGate W₀ W₁ ∈ Matrix.unitaryGroup (Fin 2 × (K × I)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [Matrix.mem_unitaryGroup_iff'] at h₀ h₁
  ext p q
  obtain ⟨p₁, p₂⟩ := p
  obtain ⟨q₁, q₂⟩ := q
  fin_cases p₁ <;> fin_cases q₁ <;>
    simp [flagSelectGate, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]
  · rw [← Fintype.sum_prod_type
        (f := fun j : K × I => (starRingEnd ℂ) (W₀ j p₂) * W₀ j q₂)]
    have hh := congrFun (congrFun h₀ p₂) q₂
    rw [Matrix.mul_apply] at hh
    simpa [Matrix.conjTranspose_apply, Matrix.one_apply] using hh
  · rw [← Fintype.sum_prod_type
        (f := fun j : K × I => (starRingEnd ℂ) (W₁ j p₂) * W₁ j q₂)]
    have hh := congrFun (congrFun h₁ p₂) q₂
    rw [Matrix.mul_apply] at hh
    simpa [Matrix.conjTranspose_apply, Matrix.one_apply] using hh

/-! ## The mixture -/

/-- The mixed gate `H · diag(W₀, W₁) · H` is unitary when the branches are unitary and
`a² + b² = 1`. -/
theorem flagMix_mem_unitaryGroup {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1)
    {W₀ W₁ : Matrix (K × I) (K × I) ℂ} (h₀ : W₀ ∈ Matrix.unitaryGroup (K × I) ℂ)
    (h₁ : W₁ ∈ Matrix.unitaryGroup (K × I) ℂ) :
    flagMixGate (K := K) (I := I) a b * flagSelectGate W₀ W₁
        * flagMixGate (K := K) (I := I) a b ∈ Matrix.unitaryGroup (Fin 2 × (K × I)) ℂ :=
  mul_mem
    (mul_mem (flagMixGate_mem_unitaryGroup (K := K) (I := I) h)
      (flagSelectGate_mem_unitaryGroup h₀ h₁))
    (flagMixGate_mem_unitaryGroup (K := K) (I := I) h)

/-- The zero-flag corner of the mixed gate `H · diag(W₀, W₁) · H` is the convex mixture
`a² • W₀ + b² • W₁`. -/
theorem flagMix_blockCorner (a b : ℝ) (W₀ W₁ : Matrix (K × I) (K × I) ℂ) :
    BlockCorner (flagMixGate (K := K) (I := I) a b * flagSelectGate W₀ W₁
        * flagMixGate (K := K) (I := I) a b) (0 : Fin 2)
      = (a ^ 2 : ℝ) • W₀ + (b ^ 2 : ℝ) • W₁ := by
  ext x y
  simp [flagMixGate, flagSelectGate, flagHadamard, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, BlockCorner, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, pow_two, mul_assoc]
  ring

end Qatlib.Papers.QRegularLS22.MainResults
