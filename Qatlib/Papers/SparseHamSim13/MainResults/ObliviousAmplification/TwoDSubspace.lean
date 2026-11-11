/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseHamSim13.MainResults.Model.SparseSimModel
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3.7 (2D Subspace Lemma)

Fixed source: arXiv:1312.1414 (Berry, Childs, Cleve, Kothari, Somma, *Exponential
improvement in precision for simulating sparse Hamiltonians*), Lemma 3.7, page 9,
Eqs. (8), (9), (10), (11).

The paper states the lemma for operators on `µ + n` qubits.  All the content lives
in an abstract complex inner-product space:

* `A : E →ₗᵢ[ℂ] H` is the isometry `|ψ⟩ ↦ |0^µ⟩|ψ⟩` embedding the `n`-qubit data
  register into the `(µ + n)`-qubit register;
* `U : H ≃ₗᵢ[ℂ] H` is the unitary of Eq. (8);
* `V : E ≃ₗᵢ[ℂ] E` is the `n`-qubit unitary `V` of Eq. (8);
* `Φ : E →ₗ[ℂ] H` sends `|ψ⟩` to the state `|Φ^⊥⟩` of Eq. (8);
* Eq. (8) is the hypothesis `hU`, the orthogonality `Π|Φ^⊥⟩ = 0` is `horth`
  (`A`-range is orthogonal to the `Φ`-range), and `|Φ^⊥⟩` being a state for every
  `|ψ⟩` gives the inner-product preservation `hPhiIso`.

Eq. (9) defines `|Ψ^⊥⟩` by `U|Ψ^⊥⟩ = √(1-p)|0^µ⟩V|ψ⟩ - √p|Φ^⊥⟩`; here this is
`Ψp ψ = U.symm (√(1-p) • A (V ψ) - √p • Φ ψ)`.

The Lean conclusion has two clauses:

1. `U (√p • A ψ + √(1-p) • Ψp ψ) = A (V ψ)` — Eq. (9) re-read as the image under
   `U`, exactly the paper's statement;
2. `∀ w, ⟪A w, Ψp ψ⟫ = 0` — the paper's two conclusions that `|Ψ^⊥⟩` is
   orthogonal to `|Ψ⟩ = A ψ` and that `Π|Ψ^⊥⟩ = 0`.  The projection `Π` is the
   orthogonal projection onto `range A`, so `Π|Ψ^⊥⟩ = 0` is equivalent to
   `A†|Ψ^⊥⟩ = 0`, i.e. to orthogonality of `|Ψ^⊥⟩` against every `A w`.  This
   also yields the orthogonality to `|Ψ⟩` by taking `w = ψ`.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators InnerProductSpace

namespace Qatlib.Papers.SparseHamSim13.MainResults

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Lemma 3.7 (2D Subspace Lemma), arXiv:1312.1414 p. 9, Eqs. (8)–(11).

If `U` and `V` are unitary, `A` is the isometry embedding the data register,
`p ∈ (0,1)`, and `U(A ψ) = √p · A(V ψ) + √(1-p) · Φ ψ` with `Φ`-range orthogonal
to `A`-range, then the state `Ψp ψ` of Eq. (9) satisfies
`U(√p · A ψ + √(1-p) · Ψp ψ) = A(V ψ)` and is orthogonal to the whole embedded
data subspace (the paper's `Π|Ψ^⊥⟩ = 0`). -/
theorem twoD_subspace_lemma
    (A : E →ₗᵢ[ℂ] H) (U : H ≃ₗᵢ[ℂ] H) (V : E ≃ₗᵢ[ℂ] E)
    (Φ : E →ₗ[ℂ] H) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hU : ∀ ψ, U (A ψ) =
      (Real.sqrt p : ℂ) • A (V ψ) + (Real.sqrt (1 - p) : ℂ) • Φ ψ)
    (horth : ∀ ψ w, ⟪A w, Φ ψ⟫_ℂ = 0)
    (hPhiIso : ∀ ψ w, ⟪Φ ψ, Φ w⟫_ℂ = ⟪ψ, w⟫_ℂ) :
    (∀ ψ, U ((Real.sqrt p : ℂ) • A ψ + (Real.sqrt (1 - p) : ℂ) •
        U.symm ((Real.sqrt (1 - p) : ℂ) • A (V ψ) - (Real.sqrt p : ℂ) • Φ ψ)) =
          A (V ψ)) ∧
    (∀ ψ w, ⟪A w, U.symm ((Real.sqrt (1 - p) : ℂ) • A (V ψ) -
        (Real.sqrt p : ℂ) • Φ ψ)⟫_ℂ = 0) := by
  set s : ℂ := (Real.sqrt p : ℂ) with hs_def
  set c : ℂ := (Real.sqrt (1 - p) : ℂ) with hc_def
  have hs : s * s = (p : ℂ) := by
    rw [hs_def, ← Complex.ofReal_mul, Real.mul_self_sqrt hp0.le]
  have hc : c * c = ((1 - p : ℝ) : ℂ) := by
    rw [hc_def, ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  constructor
  · intro ψ
    have h1 : U (A ψ) = s • A (V ψ) + c • Φ ψ := hU ψ
    have h2 : U (U.symm (c • A (V ψ) - s • Φ ψ)) = c • A (V ψ) - s • Φ ψ :=
      LinearIsometryEquiv.apply_symm_apply U _
    calc U (s • A ψ + c • U.symm (c • A (V ψ) - s • Φ ψ))
        = s • U (A ψ) + c • U (U.symm (c • A (V ψ) - s • Φ ψ)) := by
          rw [map_add, map_smul, map_smul]
      _ = s • (s • A (V ψ) + c • Φ ψ) + c • (c • A (V ψ) - s • Φ ψ) := by
          rw [h1, h2]
      _ = A (V ψ) := by
          rw [smul_add, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]
          rw [hs, hc, mul_comm c s]
          module
  · intro ψ w
    have hUw : U (A w) = s • A (V w) + c • Φ w := hU w
    have hX : ⟪A (V w), A (V ψ)⟫_ℂ = ⟪w, ψ⟫_ℂ := by
      rw [LinearIsometry.inner_map_map, LinearIsometryEquiv.inner_map_map]
    have hYX : ⟪Φ w, A (V ψ)⟫_ℂ = 0 := by
      rw [← inner_conj_symm]
      rw [horth w (V ψ), map_zero]
    have hXY : ⟪A (V w), Φ ψ⟫_ℂ = 0 := horth ψ (V w)
    have hYY : ⟪Φ w, Φ ψ⟫_ℂ = ⟪w, ψ⟫_ℂ := hPhiIso w ψ
    have e1 : ⟪U (A w), A (V ψ)⟫_ℂ = s * ⟪w, ψ⟫_ℂ := by
      rw [hUw, inner_add_left, inner_smul_left, inner_smul_left, hX, hYX]
      simp only [mul_zero, add_zero]
      rw [hs_def, Complex.conj_ofReal]
    have e2 : ⟪U (A w), Φ ψ⟫_ℂ = c * ⟪w, ψ⟫_ℂ := by
      rw [hUw, inner_add_left, inner_smul_left, inner_smul_left, hXY, hYY]
      simp only [mul_zero, zero_add]
      rw [hc_def, Complex.conj_ofReal]
    calc ⟪A w, U.symm (c • A (V ψ) - s • Φ ψ)⟫_ℂ
        = ⟪U (A w), U (U.symm (c • A (V ψ) - s • Φ ψ))⟫_ℂ := by
          rw [LinearIsometryEquiv.inner_map_map]
      _ = ⟪U (A w), c • A (V ψ) - s • Φ ψ⟫_ℂ := by
          rw [LinearIsometryEquiv.apply_symm_apply]
      _ = c * ⟪U (A w), A (V ψ)⟫_ℂ - s * ⟪U (A w), Φ ψ⟫_ℂ := by
          rw [inner_sub_right, inner_smul_right, inner_smul_right]
      _ = 0 := by
          rw [e1, e2]
          ring

end Qatlib.Papers.SparseHamSim13.MainResults
