/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound.PartialUnitaryPrecision

@[expose] public section

/-!
# Finite-length precision for chains of partial unitary operators

Fixed source: [Kitaev 1995, Abelian Stabilizer Problem](https://arxiv.org/abs/quant-ph/9511026),
the paragraph after Lemma 5 (printed p. 12).  `chainApplyLM` composes a finite chain of
`PartialOp` steps along compatible legal subspaces, and `partialChain_error` shows the
accumulated deviation of an implemented chain from the ideal chain is at most the sum of the
step precisions times the input norm.  The uniform constant `1` is placed outside all
quantifiers; this is the finite-length list iteration the source leaves implicit.  Norms are
the true inner-product-space norms of the ambient space and its legal subspaces.

## Main statements

* `chainApplyLM`: the composed chain as a linear map into the ambient space.
* `chainApplyLM_norm`: the chain preserves the norm of every legal input.
* `partialChain_error`: the uniform accumulated error bound over chains of any length.

## References

* [Kitaev1995], paragraph after Lemma 5
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.AbelianStabil95.PrecisionExt.PartialChain

open scoped BigOperators

open Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The zero index commutes with `Fin.castSucc`, expressed with a numeral-free proof so it can
rewrite submodules indexed by the first chain step. -/
theorem zero_castSucc (L : ℕ) :
    ((0 : Fin (L + 1)).castSucc : Fin (L + 2)) = (0 : Fin (L + 2)) := by
  ext
  rfl

/-- Compatibility of the first two steps of a chain: the first codomain is contained in the
legal domain of the successor of zero. -/
theorem cod_le_zero {L : ℕ} {step : Fin (L + 2) → PartialOp E}
    (hchain : ∀ i : Fin (L + 1), (step i.castSucc).cod ≤ (step i.succ).dom) :
    (step (0 : Fin (L + 2))).cod ≤ (step ((0 : Fin (L + 1)).succ)).dom := by
  have h := hchain 0
  rwa [zero_castSucc] at h

/-- Compatibility of the tail chain obtained by dropping the first step: successors commute
with `Fin.castSucc`. -/
theorem cod_le_succ {L : ℕ} {step : Fin (L + 2) → PartialOp E}
    (hchain : ∀ i : Fin (L + 1), (step i.castSucc).cod ≤ (step i.succ).dom) (i : Fin L) :
    (step (i.castSucc).succ).cod ≤ (step (i.succ).succ).dom := by
  rw [Fin.succ_castSucc]
  exact hchain i.succ

/-- Compose a chain of partial unitary operators along compatible legal subspaces.  The linear
map sends an input in the first legal domain through each linear isometric step in turn,
coercing the intermediate value into the next legal domain at every link. -/
noncomputable def chainApplyLM : {L : ℕ} → (step : Fin (L + 1) → PartialOp E) →
    (∀ i : Fin L, (step i.castSucc).cod ≤ (step i.succ).dom) → (step 0).dom →ₗ[ℂ] E
  | 0, step, _ => (step 0).cod.subtype.comp (step 0).iso.toLinearMap
  | L + 1, step, hchain =>
      (chainApplyLM (fun i : Fin (L + 1) => step i.succ) (cod_le_succ hchain)).comp
        (LinearMap.codRestrict ((step ((0 : Fin (L + 1)).succ)).dom)
          ((step (0 : Fin (L + 2))).cod.subtype.comp (step (0 : Fin (L + 2))).iso.toLinearMap)
          fun ξ => cod_le_zero hchain ((step (0 : Fin (L + 2))).iso ξ).2)

/-- The chain of length one is the single step's isometry itself. -/
theorem chainApplyLM_zero_apply (step : Fin 1 → PartialOp E)
    (hchain : ∀ i : Fin 0, (step i.castSucc).cod ≤ (step i.succ).dom) (ξ : (step 0).dom) :
    chainApplyLM step hchain ξ = ((step 0).iso ξ : E) := rfl

/-- One unfolding step of `chainApplyLM`: the chain through `L + 2` steps applies the tail
chain through the successor steps to the first step's isometric image. -/
theorem chainApplyLM_succ_apply {L : ℕ} (step : Fin (L + 2) → PartialOp E)
    (hchain : ∀ i : Fin (L + 1), (step i.castSucc).cod ≤ (step i.succ).dom)
    (ξ : (step 0).dom) :
    chainApplyLM step hchain ξ =
      chainApplyLM (fun i : Fin (L + 1) => step i.succ) (cod_le_succ hchain)
        ⟨(step (0 : Fin (L + 2))).iso ξ, cod_le_zero hchain ((step (0 : Fin (L + 2))).iso ξ).2⟩ :=
  rfl

/-- Every chain preserves the norm of its legal input: each step is a linear isometry and each
coercion between legal subspaces is norm-preserving. -/
theorem chainApplyLM_norm : ∀ {L : ℕ} (step : Fin (L + 1) → PartialOp E)
    (hchain : ∀ i : Fin L, (step i.castSucc).cod ≤ (step i.succ).dom) (ξ : (step 0).dom),
    ‖chainApplyLM step hchain ξ‖ = ‖ξ‖
  | 0, step, _, ξ => by
      rw [chainApplyLM_zero_apply]
      exact (step 0).iso.norm_map ξ
  | L + 1, step, hchain, ξ => by
      rw [chainApplyLM_succ_apply]
      rw [chainApplyLM_norm (fun i : Fin (L + 1) => step i.succ) (cod_le_succ hchain)]
      exact (step 0).iso.norm_map ξ

/-- The accumulated deviation of an implemented chain of partial unitary operators from the
ideal chain, measured on the original legal domain, is at most the sum of the step precisions
times the input norm. -/
theorem partialChain_error_aux : ∀ {L : ℕ} (step step' : Fin (L + 1) → PartialOp E)
    (δ : Fin (L + 1) → ℝ),
    (hrep : ∀ i, PartialOp.Represents (step i) (step' i) (δ i)) →
    (hstep : ∀ i : Fin L, (step i.castSucc).cod ≤ (step i.succ).dom) →
    (hstep' : ∀ i : Fin L, (step' i.castSucc).cod ≤ (step' i.succ).dom) →
    ∀ ξ : (step 0).dom,
      ‖chainApplyLM step (hstep) ξ -
          chainApplyLM step' (hstep') ⟨ξ.1, (hrep 0).dom_le ξ.2⟩‖
        ≤ (∑ i, δ i) * ‖ξ.1‖
  | 0, step, step', δ, hrep, _, _, ξ => by
      rw [chainApplyLM_zero_apply, chainApplyLM_zero_apply]
      rw [Fin.sum_univ_one]
      exact (hrep 0).error ξ
  | L + 1, step, step', δ, hrep, hstep, hstep', ξ => by
      rw [chainApplyLM_succ_apply step hstep, chainApplyLM_succ_apply step' hstep']
      set ξ₁ : (step ((0 : Fin (L + 1)).succ)).dom :=
        ⟨(step (0 : Fin (L + 2))).iso ξ,
          cod_le_zero hstep ((step (0 : Fin (L + 2))).iso ξ).2⟩ with hξ₁
      set ξ₁' : (step' ((0 : Fin (L + 1)).succ)).dom :=
        ⟨(step' (0 : Fin (L + 2))).iso ⟨(ξ.1 : E), (hrep 0).dom_le ξ.2⟩,
          cod_le_zero hstep' ((step' (0 : Fin (L + 2))).iso ⟨(ξ.1 : E), (hrep 0).dom_le ξ.2⟩).2⟩
        with hξ₁'
      set chi1c : (step' ((0 : Fin (L + 1)).succ)).dom :=
        ⟨ξ₁.1, (hrep ((0 : Fin (L + 1)).succ)).dom_le ξ₁.2⟩ with hchi1c
      have hleg1 : ‖chainApplyLM (fun i : Fin (L + 1) => step i.succ) (cod_le_succ hstep) ξ₁ -
          chainApplyLM (fun i : Fin (L + 1) => step' i.succ) (cod_le_succ hstep') chi1c‖
          ≤ (∑ i : Fin (L + 1), δ i.succ) * ‖ξ.1‖ := by
        have hih := partialChain_error_aux (fun i : Fin (L + 1) => step i.succ)
          (fun i : Fin (L + 1) => step' i.succ) (fun i : Fin (L + 1) => δ i.succ)
          (fun i => hrep i.succ) (cod_le_succ hstep) (cod_le_succ hstep') ξ₁
        have hξ₁norm : ‖ξ₁.1‖ = ‖ξ.1‖ := by
          simp only [hξ₁, Submodule.norm_coe, LinearIsometryEquiv.norm_map]
        rw [hξ₁norm] at hih
        exact hih
      have hleg2 : ‖chainApplyLM (fun i : Fin (L + 1) => step' i.succ) (cod_le_succ hstep') chi1c -
          chainApplyLM (fun i : Fin (L + 1) => step' i.succ) (cod_le_succ hstep') ξ₁'‖
          ≤ δ 0 * ‖ξ.1‖ := by
        rw [← map_sub
          (chainApplyLM (fun i : Fin (L + 1) => step' i.succ) (cod_le_succ hstep')) chi1c ξ₁']
        rw [chainApplyLM_norm (fun i : Fin (L + 1) => step' i.succ) (cod_le_succ hstep')
          (chi1c - ξ₁')]
        have hsubnorm : ‖(chi1c - ξ₁' : (step' ((0 : Fin (L + 1)).succ)).dom)‖
            = ‖((step (0 : Fin (L + 2))).iso ξ : E) -
                ((step' (0 : Fin (L + 2))).iso ⟨(ξ.1 : E), (hrep 0).dom_le ξ.2⟩ : E)‖ := by
          simp only [← Submodule.norm_coe, Submodule.coe_sub, hchi1c, hξ₁, hξ₁']
        rw [hsubnorm]
        exact (hrep 0).error ξ
      have hsplit := norm_add_le
        (chainApplyLM (fun i : Fin (L + 1) => step i.succ) (cod_le_succ hstep) ξ₁ -
          chainApplyLM (fun i : Fin (L + 1) => step' i.succ) (cod_le_succ hstep') chi1c)
        (chainApplyLM (fun i : Fin (L + 1) => step' i.succ) (cod_le_succ hstep') chi1c -
          chainApplyLM (fun i : Fin (L + 1) => step' i.succ) (cod_le_succ hstep') ξ₁')
      calc ‖chainApplyLM (fun i : Fin (L + 1) => step i.succ) (cod_le_succ hstep) ξ₁ -
              chainApplyLM (fun i : Fin (L + 1) => step' i.succ) (cod_le_succ hstep') ξ₁'‖
          = ‖(chainApplyLM (fun i : Fin (L + 1) => step i.succ) (cod_le_succ hstep) ξ₁ -
                chainApplyLM (fun i : Fin (L + 1) => step' i.succ) (cod_le_succ hstep') chi1c)
              + (chainApplyLM (fun i : Fin (L + 1) => step' i.succ) (cod_le_succ hstep') chi1c -
                chainApplyLM (fun i : Fin (L + 1) => step' i.succ) (cod_le_succ hstep') ξ₁')‖ := by
            congr 1
            abel
        _ ≤ ‖chainApplyLM (fun i : Fin (L + 1) => step i.succ) (cod_le_succ hstep) ξ₁ -
              chainApplyLM (fun i : Fin (L + 1) => step' i.succ) (cod_le_succ hstep') chi1c‖
            + ‖chainApplyLM (fun i : Fin (L + 1) => step' i.succ) (cod_le_succ hstep') chi1c -
              chainApplyLM (fun i : Fin (L + 1) => step' i.succ) (cod_le_succ hstep') ξ₁'‖ := hsplit
        _ ≤ (∑ i : Fin (L + 1), δ i.succ) * ‖ξ.1‖ + δ 0 * ‖ξ.1‖ :=
            add_le_add hleg1 hleg2
        _ = (∑ i : Fin (L + 1 + 1), δ i) * ‖ξ.1‖ := by
            rw [Fin.sum_univ_succ (fun i : Fin (L + 1 + 1) => δ i)]
            ring

/-- The finite-length form of the paragraph after Lemma 5 in [Kitaev1995]: for
nonempty finite chains, a uniform constant `1` outside all quantifiers bounds the
accumulated deviation of an implemented chain of partial unitary operators from the ideal
chain by the sum of the step precisions times the input norm.  The estimate holds on the
original legal domain of the first step; the ambient space is an arbitrary complex inner
product space, so the statement covers every non-degenerate finite-dimensional instance used
by the paper's register models. -/
theorem partialChain_error :
    ∃ uniformConstant : ℝ, 0 < uniformConstant ∧
      ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
        (L : ℕ) (step step' : Fin (L + 1) → PartialOp E) (δ : Fin (L + 1) → ℝ),
        (hrep : ∀ i, PartialOp.Represents (step i) (step' i) (δ i)) →
        (hstep : ∀ i : Fin L, (step i.castSucc).cod ≤ (step i.succ).dom) →
        (hstep' : ∀ i : Fin L, (step' i.castSucc).cod ≤ (step' i.succ).dom) →
        ∀ ξ : (step 0).dom,
          ‖chainApplyLM step (hstep) ξ -
              chainApplyLM step' (hstep') ⟨ξ.1, (hrep 0).dom_le ξ.2⟩‖
            ≤ uniformConstant * (∑ i, δ i) * ‖ξ.1‖ := by
  refine ⟨1, one_pos, fun {E} _ _ L step step' δ hrep hstep hstep' ξ => ?_⟩
  rw [one_mul]
  exact partialChain_error_aux step step' δ hrep hstep hstep' ξ

end Qatlib.Papers.AbelianStabil95.PrecisionExt.PartialChain
