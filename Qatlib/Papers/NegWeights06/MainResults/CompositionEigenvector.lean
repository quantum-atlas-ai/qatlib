/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AdversaryBounds.WeightedAdvComposition

/-!
# Product eigenvector of a composed adversary matrix

For [HoyerLeeSpalek2007], Lemma 16, the principal eigenvector of the composed
adversary can be chosen in the product form specified in the paper. Both
output fibers of every inner function are inhabited. A zero inner matrix
admits the all-ones vector as a principal eigenvector, so the construction
also produces a nonzero vector when the product of norms is zero.

See the [fixed preprint](https://arxiv.org/abs/quant-ph/0611054v2), §6.
-/

@[expose] public section

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Qatlib.Concepts.AdversaryBounds.WeightedAdvComposition
open Qatlib.Foundations.PureStateMath (QState)

namespace Qatlib.Papers.NegWeights06.MainResults

/-- The product of the outer and inner principal eigenvectors gives a nonzero principal
eigenvector of the composed matrix, including zero inner matrices on two inhabited fibers. -/
theorem composed_adversary_has_principal_product_eigenvector
    {k : ℕ} {X : Fin k → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (g : ∀ i, X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ) (Gg : ∀ i, Matrix (X i) (X i) ℂ)
    (hGf : Gf.IsHermitian) (hGg : ∀ i, (Gg i).IsHermitian)
    (hzf : ∀ u v, f u = f v → Gf u v = 0)
    (hzg : ∀ i u v, g i u = g i v → Gg i u v = 0)
    (hg : ∀ i, Function.Surjective (g i)) :
    ∃ (δf : QState (Fin k → Bool)) (δg : ∀ i, QState (X i)),
      δf ≠ 0 ∧ Gf *ᵥ δf = (‖Gf‖ : ℂ) • δf ∧
      (∀ i, δg i ≠ 0 ∧ Gg i *ᵥ δg i = (‖Gg i‖ : ℂ) • δg i) ∧
      let δh : QState ((i : Fin k) → X i) := fun x => δf (fun i => g i (x i)) * ∏ i, δg i (x i)
      δh ≠ 0 ∧ weightedAdvGamma g f Gf Gg *ᵥ δh = (‖weightedAdvGamma g f Gf Gg‖ : ℂ) • δh := by
  classical
  let : ∀ i, Nonempty (X i) := fun i => ⟨(hg i false).choose⟩
  obtain ⟨δf, hfne, hfe⟩ := weightedAdv_positive_eigenvector f Gf hGf hzf
  have innerVector (i : Fin k) : ∃ δ : QState (X i),
      δ ≠ 0 ∧ Gg i *ᵥ δ = (‖Gg i‖ : ℂ) • δ ∧ ∀ b, ∃ y, g i y = b ∧ δ y ≠ 0 := by
    by_cases hz : Gg i = 0
    · obtain ⟨y, _⟩ := hg i false
      refine ⟨fun _ => 1, fun h => one_ne_zero (congrFun h y), by simp [hz], fun b => ?_⟩
      obtain ⟨u, hu⟩ := hg i b
      exact ⟨u, hu, one_ne_zero⟩
    · obtain ⟨δ, hδ, he⟩ := weightedAdv_positive_eigenvector (g i) (Gg i) (hGg i) (hzg i)
      exact ⟨δ, hδ, he, weightedAdv_bipartite_fiber_nonzero (g i) (Gg i) (hzg i) δ hδ
        (‖Gg i‖ : ℂ) (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)) he⟩
  choose δg hne he hfiber using innerVector
  let e (x : (i : Fin k) → X i) : Fin k → Bool := fun i => g i (x i)
  let δh (x : (i : Fin k) → X i) : ℂ := δf (e x) * ∏ i, δg i (x i)
  refine ⟨δf, δg, hfne, hfe, fun i => ⟨hne i, he i⟩, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := Function.ne_iff.mp hfne
    choose x hx hδx using fun i => hfiber i (s i)
    have hex : e x = s := funext hx
    intro hz
    have h := congrFun hz x
    change δf (e x) * (∏ i, δg i (x i)) = 0 at h
    rw [hex] at h
    exact (mul_ne_zero hs (Finset.prod_ne_zero_iff.mpr fun i _ => hδx i)) h
  · rw [weightedAdvGamma_norm_eq g f Gf Gg hGf hGg hzg]
    funext x
    change (weightedAdvGamma g f Gf Gg *ᵥ δh) x = _
    let A (i : Fin k) : Matrix (X i) (X i) ℂ := Matrix.diagonal (fun _ => (‖Gg i‖ : ℂ)) + Gg i
    calc
      (weightedAdvGamma g f Gf Gg *ᵥ δh) x =
          ∑ y, (Gf (e x) (e y) * δf (e y)) * ∏ i, A i (x i) (y i) * δg i (y i) := by
        apply Finset.sum_congr rfl
        intro y _
        change Gf (e x) (e y) * (∏ i, A i (x i) (y i)) *
          (δf (e y) * ∏ i, δg i (y i)) = _
        rw [Finset.prod_mul_distrib]
        ring
      _ = ∑ s, (Gf (e x) s * δf s) * ∏ i, (‖Gg i‖ : ℂ) * δg i (x i) := by
        rw [weightedAdv_sum_by_outputs g (fun s => Gf (e x) s * δf s)
          (fun i y => A i (x i) y * δg i y)]
        simp_rw [A, weightedAdv_factor_fiber_action (g _) (Gg _) (hzg _) (δg _) (he _)]
      _ = (‖Gf‖ : ℂ) * δf (e x) * ∏ i, (‖Gg i‖ : ℂ) * δg i (x i) := by
        exact (Finset.sum_mul _ _ _).symm.trans
          (congrArg (fun z : ℂ => z * _) (congrFun hfe (e x)))
      _ = _ := by
        change _ = (↑(‖Gf‖ * ∏ i, ‖Gg i‖) : ℂ) * δh x
        simp only [δh, Complex.ofReal_mul, Complex.ofReal_prod, Finset.prod_mul_distrib]
        ring

end Qatlib.Papers.NegWeights06.MainResults
