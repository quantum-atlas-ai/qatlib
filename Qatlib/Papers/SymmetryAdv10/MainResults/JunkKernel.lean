/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SymmetryAdv10.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 11 of arXiv:1012.2112v1 (p. 10): vanishing of the junk kernel

The paper states

`tr[Γ̃(ρ⊙ ∘ M)] = 0 for any matrix M  ↔  Γ̃_{ff'} = 0 for all f, f' with P(f) = P(f')`.

This is the statement for *all* matrices `M` (not only junk matrices); the
paper's proof uses the single-entry test matrix, and we formalise exactly that.

Assumptions used by the paper and made explicit here:

* `hunit : P(f) = P(f') → ⟨P(f)|P(f')⟩ = 1` (the target state depends only on
  the classical output `P(f)`, so equal outputs give overlap one);
* `horth : P(f) ≠ P(f') → ⟨P(f)|P(f')⟩ = 0` (distinct outputs give orthogonal
  target states; this is the classical/coherent state-generation setting of
  Theorem 10, where the target states are the projectors `Π_z`).

With these, both directions are proved completely; the only reason `horth`
appears is the "only if" direction, exactly as in the paper's displayed
computation `tr[Γ̃(ρ⊙∘M)] = |F|⁻¹ ∑ Γ̃_{ff'} ⟨P(f)|P(f')⟩ M_{ff'}`.
-/

set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.SymmetryAdv10.MainResults.JunkKernel

noncomputable section

variable (P : Problem)

/-- The trace of `Γ * (ρ⊙ ⊙ M)` as a double sum over entries. -/
theorem trace_mul_hadamard_apply (Γ M : Matrix P.F P.F ℂ) :
    (Γ * Matrix.hadamard P.rhoDot M).trace =
      ∑ a, ∑ b, Γ a b * (P.rhoDot b a * M b a) := by
  rfl

/-- The single-entry test matrix computation of Lemma 11's proof:
`ρ⊙ ⊙ `single g f 1` is the single-entry matrix with value `ρ⊙_gf`, and the
trace against `Γ` reads off `Γ_fg ρ⊙_gf`. -/
theorem trace_mul_hadamard_single (Γ : Matrix P.F P.F ℂ) (g f : P.F) :
    (Γ * Matrix.hadamard P.rhoDot (Matrix.single g f 1)).trace =
      Γ f g * P.rhoDot g f := by
  have hsingle : Matrix.hadamard P.rhoDot (Matrix.single g f (1 : ℂ)) =
      Matrix.single g f (P.rhoDot g f) := by
    ext i j
    by_cases hij : i = g ∧ j = f
    · obtain ⟨hi, hj⟩ := hij
      subst hi; subst hj
      simp
    · have h' : ¬ (g = i ∧ f = j) := by tauto
      simp [Matrix.hadamard_apply, h']
  rw [hsingle, Matrix.trace_mul_single]
  simp

/-- **Lemma 11 (arXiv:1012.2112v1, p. 10).** For an additive adversary matrix
`Γ̃`, `tr[Γ̃(ρ⊙ ∘ M)] = 0` for every matrix `M` if and only if
`Γ̃_{ff'} = 0` whenever `P(f) = P(f')`. -/
theorem junk_trace_zero_iff
    (Γ : Matrix P.F P.F ℂ)
    (hunit : ∀ f g : P.F, P.funMap f = P.funMap g → P.targetGram f g = 1)
    (horth : ∀ f g : P.F, P.funMap f ≠ P.funMap g → P.targetGram f g = 0) :
    (∀ M : Matrix P.F P.F ℂ,
        (Γ * Matrix.hadamard P.rhoDot M).trace = 0) ↔
      (∀ f g : P.F, P.funMap f = P.funMap g → Γ f g = 0) := by
  constructor
  · intro h f g hfg
    have hval : Γ f g * P.rhoDot g f = 0 := by
      have hM := h (Matrix.single g f 1)
      rwa [trace_mul_hadamard_single] at hM
    have hcard : (Fintype.card P.F : ℂ) ≠ 0 := by
      have hpos : 0 < Fintype.card P.F := Fintype.card_pos_iff.mpr ⟨f⟩
      exact_mod_cast ne_of_gt hpos
    have hrho : P.rhoDot g f = ((Fintype.card P.F : ℂ))⁻¹ := by
      simp [Problem.rhoDot, hunit f g hfg]
    rw [hrho] at hval
    exact (mul_eq_zero.mp hval).resolve_right (inv_ne_zero hcard)
  · intro h M
    rw [trace_mul_hadamard_apply]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    by_cases hab : P.funMap a = P.funMap b
    · simp [h a b hab]
    · have hz : P.targetGram a b = 0 := horth a b hab
      simp [Problem.rhoDot, hz]

end

end JunkKernel
