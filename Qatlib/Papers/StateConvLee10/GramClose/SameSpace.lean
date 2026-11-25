/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StateConvLee10.GramClose.SourceGramValueBridge
public import Qatlib.Concepts.GramQueryCore.GramRealization.GramQueryRealization

@[expose] public section

/-!
# Same-space transport for Gram-close state families

The second bullet of Lemma 4.8 asks for a unitary `U` on the *same* space `H` with real overlap
`1 - sqrt (2ε)` against the target family. The locked development
`Qatlib.Papers.StateConvLee10.GramClose.source_padded_unitary_overlap` produces `U` only on the
enlarged space `H ⊕ K`, so the literal same-space statement is still open. This module records the
two ingredients that are available inside the source boundary:

* `source_gram_entry_close_of_unfiltered_le`: an unfiltered `γ₂` budget `ε` for the Gram difference
  bounds every entry of that difference by `ε`. This is the quantitative output of the certificate
  witness, obtained by Cauchy–Schwarz on the two witness families.
* `source_same_space_unitary_of_gram_eq`: exactly equal Gram matrices are realized by a unitary on
  `H` itself, which is the `ε = 0` endpoint of the same-space bullet.

The approximate same-space statement at positive `ε` is not delivered here: it needs a Lipschitz
bound for the matrix square root (`‖sqrt A - sqrt B‖ ≤ sqrt ‖A - B‖`) plus a polar decomposition of
the transported frame, neither of which is available in the locked `Qatlib` cache.

Paper: [arXiv:1011.3020v2](https://arxiv.org/abs/1011.3020), printed p.9 Lemma 4.8, second bullet.
-/

set_option autoImplicit false
noncomputable section

open Matrix

open scoped Classical ENNReal

namespace Qatlib.Papers.StateConvLee10.GramClose

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath

/-- If the unfiltered `γ₂` value of the Gram difference of two families is at most `ε`, then every
entry of that difference has complex norm at most `ε` [LeeEtAl2011]. -/
theorem source_gram_entry_close_of_unfiltered_le {H X : Type} [Fintype H]
    [Fintype X] [DecidableEq X] {ε : ℝ} (hε : 0 ≤ ε) (ρ σ : X → QState H)
    (hval : sourceUnfiltered (gramStateMatrix ρ - gramStateMatrix σ) ≤ ENNReal.ofReal ε) :
    ∀ x y, ‖(gramStateMatrix ρ - gramStateMatrix σ) x y‖ ≤ ε := by
  obtain ⟨Q, _, u, v, hu, hv, huv⟩ :=
    Qatlib.Papers.StateConvLee10.GramClose.gramFilteredCert_of_sourceUnfiltered_le (X := X) hε hval
  intro x y
  have hxy : (gramStateMatrix ρ - gramStateMatrix σ) x y = star (u 0 x) ⬝ᵥ v 0 y := by
    simpa [Fin.sum_univ_one, gramFilterAllOnes] using huv x y
  have hux : ∑ q, ‖u 0 x q‖ ^ 2 ≤ ε := by
    simpa [Fin.sum_univ_one, Complex.normSq_eq_norm_sq] using hu x
  have hvy : ∑ q, ‖v 0 y q‖ ^ 2 ≤ ε := by
    simpa [Fin.sum_univ_one, Complex.normSq_eq_norm_sq] using hv y
  rw [hxy]
  calc ‖star (u 0 x) ⬝ᵥ v 0 y‖
      ≤ ∑ q, ‖u 0 x q‖ * ‖v 0 y q‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun q _ => by
          simp only [Pi.star_apply, norm_mul, norm_star]
    _ ≤ Real.sqrt (∑ q, ‖u 0 x q‖ ^ 2) * Real.sqrt (∑ q, ‖v 0 y q‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt ε * Real.sqrt ε :=
        mul_le_mul (Real.sqrt_le_sqrt hux) (Real.sqrt_le_sqrt hvy)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = ε := Real.mul_self_sqrt hε

/-- The Gram matrix of a state family is the Gram matrix `Vᴴ * V` of the matrix whose columns are
the family's state vectors. -/
theorem gramStateMatrix_eq_conjTranspose_mul {H X : Type} [Fintype H]
    (ρ : X → QState H) :
    (Matrix.of (fun i x => ρ x i) : Matrix H X ℂ)ᴴ * Matrix.of (fun i x => ρ x i) =
      gramStateMatrix ρ := by
  ext x y
  rw [show gramStateMatrix ρ x y = Inner (ρ x) (ρ y) from rfl]
  rw [Qatlib.Foundations.PureStateMath.inner_apply]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- State families with equal Gram matrices are related by a unitary on the ambient space itself:
the transported frame agrees with the target family pointwise [LeeEtAl2011]. -/
theorem source_same_space_unitary_of_gram_eq {H X : Type} [Fintype H] [DecidableEq H]
    [Fintype X] [DecidableEq X] (ρ σ : X → QState H)
    (hGram : gramStateMatrix ρ = gramStateMatrix σ) :
    ∃ U : Matrix H H ℂ, U ∈ Matrix.unitaryGroup H ℂ ∧ ∀ x, ApplyGate U (ρ x) = σ x := by
  let V : Matrix H X ℂ := Matrix.of (fun i x => ρ x i)
  let W : Matrix H X ℂ := Matrix.of (fun i x => σ x i)
  have hmat : Vᴴ * V = Wᴴ * W := by
    have hV : V = Matrix.of (fun i x => ρ x i) := rfl
    have hW : W = Matrix.of (fun i x => σ x i) := rfl
    rw [hV, hW, gramStateMatrix_eq_conjTranspose_mul, gramStateMatrix_eq_conjTranspose_mul, hGram]
  obtain ⟨U, hU, hUV⟩ := gram_equal_actual_unitary_transport H X V W hmat
  have hVx : ∀ x : X, V *ᵥ Ket x = ρ x := by
    intro x
    ext i
    simp [V, Matrix.mulVec, dotProduct, Ket]
  have hWx : ∀ x : X, W *ᵥ Ket x = σ x := by
    intro x
    ext i
    simp [W, Matrix.mulVec, dotProduct, Ket]
  refine ⟨U, hU, fun x => ?_⟩
  have hstep : U *ᵥ (V *ᵥ Ket x) = W *ᵥ Ket x := by
    rw [Matrix.mulVec_mulVec, hUV]
  rw [hVx x, hWx x] at hstep
  simpa [ApplyGate] using hstep

/-- Exactly equal Gram matrices give the `ε = 0` case of the same-space bullet of Lemma 4.8: a
unitary on `H` whose real overlap with the target family is `1` for every input
[LeeEtAl2011]. -/
theorem source_same_space_overlap_of_gram_eq {H X : Type} [Fintype H] [DecidableEq H]
    [Fintype X] [DecidableEq X] (ρ σ : X → QState H)
    (hσ : ∀ x, Normalized (σ x))
    (hGram : gramStateMatrix ρ = gramStateMatrix σ) :
    ∃ U : Matrix H H ℂ, U ∈ Matrix.unitaryGroup H ℂ ∧
      ∀ x, 1 - Real.sqrt (2 * 0) ≤ (Inner (ApplyGate U (ρ x)) (σ x)).re := by
  obtain ⟨U, hU, hUσ⟩ := source_same_space_unitary_of_gram_eq ρ σ hGram
  refine ⟨U, hU, fun x => ?_⟩
  rw [hUσ x]
  have hnorm : Inner (σ x) (σ x) = 1 := (normalized_iff_inner_self (σ x)).mp (hσ x)
  rw [hnorm]
  norm_num

/-- The zero-budget case of Lemma 4.8's second bullet in the source's own hypothesis shape: an
unfiltered `γ₂` distance of `0` between the Gram matrices yields a unitary on `H` with overlap `1`
[LeeEtAl2011]. -/
theorem source_same_space_overlap_of_unfiltered_eq_zero {H X : Type} [Fintype H] [DecidableEq H]
    [Fintype X] [DecidableEq X] (ρ σ : X → QState H) (hσ : ∀ x, Normalized (σ x))
    (hval : sourceUnfiltered (gramStateMatrix ρ - gramStateMatrix σ) = 0) :
    ∃ U : Matrix H H ℂ, U ∈ Matrix.unitaryGroup H ℂ ∧
      ∀ x, 1 - Real.sqrt (2 * 0) ≤ (Inner (ApplyGate U (ρ x)) (σ x)).re := by
  have hbound : sourceUnfiltered (gramStateMatrix ρ - gramStateMatrix σ) ≤ ENNReal.ofReal 0 := by
    rw [hval]
    simp
  have hentry := source_gram_entry_close_of_unfiltered_le (H := H) (X := X) le_rfl ρ σ hbound
  have hGram : gramStateMatrix ρ = gramStateMatrix σ := by
    ext x y
    have h0 : ‖(gramStateMatrix ρ - gramStateMatrix σ) x y‖ ≤ 0 := by
      simpa using hentry x y
    have hz : (gramStateMatrix ρ - gramStateMatrix σ) x y = 0 := norm_le_zero_iff.mp h0
    exact sub_eq_zero.mp hz
  exact source_same_space_overlap_of_gram_eq ρ σ hσ hGram

end Qatlib.Papers.StateConvLee10.GramClose
