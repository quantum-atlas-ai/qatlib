/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryIteration
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels

set_option backward.isDefEq.respectTransparency false

/-!
# AdversaryIteration — paper Lemma 1 (adversary power under composition)

Kimmel, *Quantum Adversary (Upper) Bound*, fixed arXiv:1101.0797v5 (16 May 2013).
Lemma 1, Eq. (1), p. 2 and Appendix A pp. 9–12.

The paper proves `ADV±(f^d) ≥ (ADV±(f))^d` for a (possibly partial) Boolean `f`.
The shared library represents the bounded-error general adversary bound by the
real-symmetric masked spectral-norm supremum `sourceAdversary` (the printed
`ADV±` of Definition 3.3/Theorem 3.4 of arXiv:1011.3020v2), and the `d`-fold
composition `f^d = f ∘ (f^{d-1}, …, f^{d-1})` by the flat total iteration
`iterateTotal f d` on `Fin (n^d) → Bool` (with `iterateTotal f 1 = f`).

The proof below is the paper's Appendix-A route: an actual dual solution
`(W, Ω)` is normalized, then the composition construction `weightedAdvGamma`
(Lemma 6, Eq. (14)–(20)) is iterated at every depth, preserving Hermitian
symmetry, real entries, same-output vanishing and unit filtered norms, while
multiplying the spectral norm by `‖Γ‖` per level. The final value is the
source supremum over actual witnesses, so no optimum, `d`-th root or numerical
solver is an input.

Boundary: this module covers the total Boolean case of Lemma 1 (all inputs of
`f` are defined, so `x̃ ∈ S` is automatic). The partial-domain case needs the
primed-matrix extension of Appendix A (Lemmas 4–6); see
`DualSolution/SourceLemma6.lean` for the composition identity in the shared
domain model.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

namespace Qatlib.Papers.QAdversary11.PartialCompose.AdversaryIteration

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.FilteredNorm

/-- The Boolean word input map `x ↦ (sourceBooleanSymbol (x j))_j`, i.e. the
alphabet-`Fin 2` presentation of a Boolean query word. -/
def booleanInput {n : ℕ} : (Fin n → Bool) → Fin n → Fin 2 :=
  fun w j => sourceBooleanSymbol (w j)

/-- `sourceBooleanSymbol` is injective. -/
theorem sourceBooleanSymbol_injective : Function.Injective sourceBooleanSymbol := by
  intro a b h
  cases a <;> cases b <;> simp_all [sourceBooleanSymbol]

/-- `sourceBooleanSymbol` reflects inequality. -/
theorem sourceBooleanSymbol_ne {a b : Bool} (h : a ≠ b) :
    sourceBooleanSymbol a ≠ sourceBooleanSymbol b :=
  fun he => h (sourceBooleanSymbol_injective he)

/-- The alphabet delta of the Boolean presentation is the differing-bit mask. -/
theorem sourceAlphabetDelta_boolean (n : ℕ) (j : Fin n) :
    sourceAlphabetDelta (booleanInput (n := n)) j =
      fun x y => if x j ≠ y j then (1 : ℂ) else 0 := by
  ext x y
  simp only [sourceAlphabetDelta, booleanInput]
  by_cases h : x j = y j
  · rw [if_pos (congrArg sourceBooleanSymbol h), if_neg (by simpa [h] using h)]
  · rw [if_neg (sourceBooleanSymbol_ne h), if_pos h]

/-- The Boolean query filter `genAdvFilter` is the Hadamard product with the
alphabet mask `sourceAlphabetDelta`. -/
theorem genAdvFilter_boolean_eq_hadamard {n : ℕ}
    (G : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (j : Fin n) :
    genAdvFilter (fun w : Fin n → Bool => w) G j =
      G ⊙ sourceAlphabetDelta (booleanInput (n := n)) j := by
  ext x y
  simp only [genAdvFilter, Matrix.hadamard_apply, sourceAlphabetDelta_boolean]
  split_ifs <;> simp_all

/-- A finite product of complex numbers with vanishing imaginary parts has
vanishing imaginary part. -/
theorem im_prod_zero {ι : Type} (s : Finset ι) (g : ι → ℂ)
    (hg : ∀ i ∈ s, (g i).im = 0) : (s.prod g).im = 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Complex.mul_im]
    have ha' : (g a).im = 0 := hg a (Finset.mem_insert_self a s)
    have hs' : ∀ i ∈ s, (g i).im = 0 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [ha', ih hs']
    ring

/-- Real scalar multiplication preserves vanishing imaginary part. -/
theorem im_real_smul_zero (r : ℝ) {z : ℂ} (hz : z.im = 0) : (r • z).im = 0 := by
  rw [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hz]
  ring

/-- Real-entry matrices stay real-entry under the weighted composition
`weightedAdvGamma` (Definition 6 of quant-ph/0611054v2). -/
theorem weightedAdvGamma_im_zero {k : ℕ} {X : Fin k → Type}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (g : (i : Fin k) → X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : (i : Fin k) → Matrix (X i) (X i) ℂ)
    (hGf : ∀ x y, (Gf x y).im = 0) (hGg : ∀ i x y, (Gg i x y).im = 0) :
    ∀ x y, (Qatlib.Concepts.AdversaryBounds.WeightedAdvComp.weightedAdvGamma
      g f Gf Gg x y).im = 0 := by
  intro x y
  unfold Qatlib.Concepts.AdversaryBounds.WeightedAdvComp.weightedAdvGamma
  rw [Complex.mul_im]
  have hf0 : (Gf (fun i => g i (x i)) (fun i => g i (y i))).im = 0 := hGf _ _
  have hprod : (∏ i, (Matrix.diagonal (fun _ : X i => (‖Gg i‖ : ℂ)) + Gg i) (x i) (y i)).im
      = 0 := by
    refine im_prod_zero Finset.univ (fun i => (Matrix.diagonal (fun _ : X i => (‖Gg i‖ : ℂ))
      + Gg i) (x i) (y i)) ?_
    intro i _
    change ((Matrix.diagonal (fun _ : X i => (‖Gg i‖ : ℂ)) + Gg i) (x i) (y i)).im = 0
    rw [Matrix.add_apply, Complex.add_im]
    have hdiag : (Matrix.diagonal (fun _ : X i => (‖Gg i‖ : ℂ)) (x i) (y i)).im = 0 := by
      simp only [Matrix.diagonal_apply]
      split_ifs <;> simp
    rw [hdiag, hGg i]
    simp
  rw [hf0, hprod]
  ring

/-- Real-entry witnesses stay real-entry under one normalized composition step
`iteratedAdversaryStep`. -/
theorem iteratedAdversaryStep_im_zero {n : ℕ} (f : (Fin n → Bool) → Bool)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (d : ℕ)
    (B : Matrix (Fin (n^d) → Bool) (Fin (n^d) → Bool) ℂ)
    (hA : ∀ x y, (A x y).im = 0) (hB : ∀ x y, (B x y).im = 0) :
    ∀ x y, (iteratedAdversaryStep f A d B x y).im = 0 := by
  intro x y
  rw [iteratedAdversaryStep, Matrix.smul_apply, Matrix.submatrix_apply]
  exact im_real_smul_zero _
    (weightedAdvGamma_im_zero (fun _ : Fin n => iterateTotal f d) f A (fun _ => B)
      hA (fun _ => hB) _ _)

/-- Real-entry witnesses stay real-entry at every depth of the flat iteration
(`zeroDepthGamma` and the normalized `iteratedAdversaryStep`). -/
theorem iteratedAdversaryGamma_im_zero {n : ℕ} (f : (Fin n → Bool) → Bool)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (hA : ∀ x y, (A x y).im = 0) :
    ∀ (d : ℕ) (x y : Fin (n^d) → Bool),
      (iteratedAdversaryGamma f A d x y).im = 0 := by
  intro d
  induction d with
  | zero =>
    intro x y
    rw [show iteratedAdversaryGamma f A 0 = zeroDepthGamma n from rfl]
    simp only [zeroDepthGamma, booleanQueryGamma, Matrix.submatrix_apply]
    split_ifs <;> simp
  | succ d ih =>
    exact iteratedAdversaryStep_im_zero f A d (iteratedAdversaryGamma f A d) hA ih

/-- Paper Lemma 1, Eq. (1) (arXiv:1101.0797v5, p. 2; proof Appendix A, pp. 9–12):
for a total Boolean function `f` on `n` bits and every natural `d`,
`(ADV± f)^d ≤ ADV±(f^d)`.

The `d`-fold composition `f^d` is the library's flat iteration `iterateTotal f d`
on `Fin (n^d) → Bool`, and `ADV±` is `sourceAdversary` with the Boolean
alphabet-delta filters. The proof normalizes each actual witness and iterates
the composition witness construction, so the supremum is over realized
witnesses only. -/
theorem advPm_pow_le_advPm_iterateTotal {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool)
    (d : ℕ) :
    sourceAdversary (sourceAlphabetDelta (booleanInput (n := n))) f ^ d ≤
      sourceAdversary (sourceAlphabetDelta (booleanInput (n := n^d))) (iterateTotal f d) := by
  classical
  by_cases hd : d = 0
  · subst d
    rw [pow_zero]
    -- the depth-zero (projection) adversary is at least one, witnessed by its
    -- actual query matrix `zeroDepthGamma`.
    have hz := zeroDepthGamma_facts f
    have hReal : ∀ x y, (zeroDepthGamma n x y).im = 0 :=
      iteratedAdversaryGamma_im_zero f (0 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
        (by intro x y; simp) 0
    have hmem : ∀ j, ‖zeroDepthGamma n ⊙ sourceAlphabetDelta (booleanInput (n := n^0)) j‖
        ≤ 1 := by
      intro j
      rw [← genAdvFilter_boolean_eq_hadamard]
      exact hz.2.2.2 j
    have hle : ENNReal.ofReal ‖zeroDepthGamma n‖ ≤
        sourceAdversary (sourceAlphabetDelta (booleanInput (n := n^0))) (iterateTotal f 0) :=
      le_iSup_of_le ⟨zeroDepthGamma n, hz.1, hReal, hz.2.2.1, hmem⟩ le_rfl
    simpa only [hz.2.1, ENNReal.ofReal_one] using hle
  · unfold sourceAdversary
    rw [ENNReal.iSup_pow_of_ne_zero hd]
    apply iSup_le
    intro G
    by_cases hN0 : ‖G.val‖ = 0
    · -- the zero-norm witness contributes `0`, not a hidden normalization step
      rw [hN0, ENNReal.ofReal_zero, zero_pow hd]
      exact zero_le
    · have hN : 0 < ‖G.val‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hN0)
      have hfA : ∀ i, ‖genAdvFilter (fun w : Fin n → Bool => w) G.val i‖ ≤ 1 := by
        intro i
        rw [genAdvFilter_boolean_eq_hadamard]
        exact G.property.2.2.2 i
      obtain ⟨hHerm, hZero, hNorm, hFilt⟩ :=
        iteratedAdversaryGamma_facts hn f G.val G.property.1 G.property.2.2.1 hfA hN d
      have hReal := iteratedAdversaryGamma_im_zero f G.val G.property.2.1 d
      have hmem : ∀ j, ‖iteratedAdversaryGamma f G.val d ⊙
          sourceAlphabetDelta (booleanInput (n := n^d)) j‖ ≤ 1 := by
        intro j
        rw [← genAdvFilter_boolean_eq_hadamard]
        exact hFilt j
      have hle : ENNReal.ofReal ‖iteratedAdversaryGamma f G.val d‖ ≤
          sourceAdversary (sourceAlphabetDelta (booleanInput (n := n^d))) (iterateTotal f d) :=
        le_iSup_of_le ⟨iteratedAdversaryGamma f G.val d, hHerm, hReal, hZero, hmem⟩ le_rfl
      rw [hNorm] at hle
      rwa [ENNReal.ofReal_pow (norm_nonneg _)] at hle

end Qatlib.Papers.QAdversary11.PartialCompose.AdversaryIteration
