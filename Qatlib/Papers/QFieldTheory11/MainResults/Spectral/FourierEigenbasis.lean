/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section


/-!
# Fourier eigenvector transport with an explicit operator bridge

The previous encoding omitted the defining relation between the Fourier
transform and the operators. Its source attribution to arXiv:1111.3633v1,
Proposition 1, was inaccurate: the numbered proposition occurs in the v2
supplement, section A.4. The v1 main text states the eigenbasis relationship.
Preserving inner products alone cannot identify a Fourier transform.
Here the operator identity `p (F ψ) = c • F (q ψ)` is an explicit premise.
The result transports eigenvectors through that identity; it does not construct
a Fourier transform or establish uniqueness of a canonical representation.

The counterexample below verifies that the omitted bridge is necessary for the
previous signature: arbitrary functions satisfying its commutator relation need
not preserve zero. With `F = id`, `c = 1`, and `e = 0`, its conclusion fails.
No assertion of a Hilbert-space basis or nonzero eigenvectors is encoded.
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexInnerProductSpace

namespace Qatlib.Papers.QFieldTheory11.MainResults.Spectral

/-- A concrete obstruction to eigenvector transport without an operator bridge. -/
private theorem missing_bridge :
    ∃ (p q : ℂ → ℂ) (e : ℝ → ℂ),
      (∀ ψ : ℂ, p (q ψ) - q (p ψ) = Complex.I • ψ) ∧
      (∀ x : ℝ, q (e x) = (x : ℂ) • e x) ∧
      ¬ (∀ x : ℝ, p (e x) = (x : ℂ) • e x) := by
  refine ⟨fun z => z + 1, fun z => z - Complex.I / 2 * z * (z - 1),
    fun _ => 0, ?_, ?_, ?_⟩
  · intro ψ
    simp only [smul_eq_mul]
    ring
  · intro x
    simp
  · intro h
    have hz := h 0
    norm_num at hz

/-- Fourier eigenvector transport under inner-product preservation and the defining
operator intertwining identity. No commutator or nonzero scaling premise is needed. -/
theorem prop1_fourier_eigenbasis_continuous
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (p q : H → H) (F : H → H) (e : ℝ → H) (c : ℝ)
    (hF_unitary : ∀ u v : H, ⟪F u, F v⟫ = ⟪u, v⟫)
    (hq_eig : ∀ x : ℝ, q (e x) = (x : ℂ) • e x)
    (hFourier : ∀ ψ : H, p (F ψ) = (c : ℂ) • F (q ψ)) :
    ∀ x : ℝ, p (F (e x)) = ((c * x : ℝ) : ℂ) • F (e x) := by
  have hsmul (a : ℂ) (v : H) : F (a • v) = a • F v := by
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hF_unitary]
    ring
  intro x
  rw [hFourier, hq_eig, hsmul, smul_smul, Complex.ofReal_mul]

end Qatlib.Papers.QFieldTheory11.MainResults.Spectral
