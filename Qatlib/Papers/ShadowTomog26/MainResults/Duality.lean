/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ShadowTomog26.MainResults.Core
import Qatlib.Foundations.GraphFraction.CoverLP.MinimaxDual

/-!
# Fractional-cover duality for graph-body minima

This module identifies the finite-set cover definitions used in the shadow-tomography framework
of [XuEtAl2026] with the foundational cover linear program. Restriction to independent-set
contexts and extension by zero preserve both feasibility and objective values, allowing the
minimax duality theorem to compute `alphaMin`.

## Main statements

* `fractionalChromatic_eq_coverValue` equates the two cover objectives.
* `weightedIndepNum_eq_support` identifies the corresponding independent-set support functions.
* `alphaMin_eq_inverse_fractionalChromatic` computes the simplex minimum as a reciprocal
  fractional chromatic number.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ShadowTomog26.MainResults
open scoped Classical BigOperators
namespace LP
open Qatlib.Foundations.GraphFraction.CoverLP
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If a finite-set function vanishes on sets that are not independent in `G`, summing it over
independent-set contexts equals summing it over all finite vertex sets. -/
theorem supported_sum (G : SimpleGraph V) (f : Finset V → ℝ)
    (hf : ∀ I : Finset V, ¬G.IsIndepSet (I : Set V) → f I=0) :
    (∑ I : Context G,f I.val) = ∑ I : Finset V,f I := by
  have h := Fintype.sum_subtype_add_sum_subtype
    (fun I : Finset V => G.IsIndepSet (I : Set V)) f
  have hz : (∑ I : {I : Finset V // ¬G.IsIndepSet (I : Set V)},f I.val)=0 := by
    apply Finset.sum_eq_zero
    intro I _
    exact hf I.val I.property
  rw [hz,add_zero] at h
  exact h

/-- Restricting a `FracCover` to independent-set contexts yields a feasible foundational cover
with constant demand one. The restriction preserves the total cover weight. -/
theorem restrict_cover (G : SimpleGraph V) (x : Finset V → ℝ) (hx : FracCover G x) :
    Feasible G (fun _ => 1) (fun I => x I.val) ∧
      (∑ I : Context G,x I.val)=(∑ I : Finset V,x I) := by
  refine ⟨⟨fun I => hx.1 I.val I.property,?_⟩,supported_sum G x hx.2.1⟩
  intro i
  have hs := supported_sum G (fun I => x I*(if i∈I then (1:ℝ) else 0))
    (by intro I hI;simp only [hx.2.1 I hI,zero_mul])
  change 1 ≤ ∑ I : Context G,x I.val*(if i∈I.val then (1:ℝ) else 0)
  rw [hs]
  exact hx.2.2 i

/-- Extend a real weight function on independent-set contexts to all finite vertex sets by
assigning zero to sets that are not independent. -/
def extend (G : SimpleGraph V) (x : Context G → ℝ) (I : Finset V) : ℝ :=
  if h : G.IsIndepSet (I : Set V) then x ⟨I,h⟩ else 0

/-- Extension by zero from independent-set contexts preserves the sum of the weights. -/
theorem extend_sum (G : SimpleGraph V) (x : Context G → ℝ) :
    (∑ I : Finset V,extend G x I) = ∑ I : Context G,x I := by
  rw [← supported_sum G (extend G x) (by intro I hI;simp [extend,hI])]
  apply Finset.sum_congr rfl
  intro I _
  simp [extend,I.property]

/-- A feasible context cover with constant demand one extends by zero to a `FracCover` on all
finite vertex sets. -/
theorem extend_cover (G : SimpleGraph V) (x : Context G → ℝ)
    (hx : Feasible G (fun _ => 1) x) : FracCover G (extend G x) := by
  refine ⟨fun I hI => by simpa [extend,hI] using hx.1 ⟨I,hI⟩,
    fun I hI => by simp [extend,hI],?_⟩
  intro i
  have hs := supported_sum G (fun I => extend G x I*(if i∈I then (1:ℝ) else 0))
    (by intro I hI;simp [extend,hI])
  rw [← hs]
  have he (I : Context G) : extend G x I.val=x I := dif_pos I.property
  simp_rw [he]
  exact hx.2 i

/-- The fractional chromatic number defined using `FracCover` equals the foundational cover
value with constant vertex demand one. -/
theorem fractionalChromatic_eq_coverValue (G : SimpleGraph V) :
    fractionalChromatic G=coverValue G (fun _ => 1) := by
  unfold fractionalChromatic coverValue
  congr 1
  ext s
  constructor
  · rintro ⟨x,hx,hs⟩
    obtain ⟨hy,hm⟩ := restrict_cover G x hx
    exact ⟨fun I => x I.val,hy,hm.trans hs.symm⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨extend G x,extend_cover G x hx,(extend_sum G x).symm⟩

omit [Fintype V] [DecidableEq V] in

/-- The weighted independence number defined using finite independent sets equals the
foundational independent-set support function. -/
theorem weightedIndepNum_eq_support (G : SimpleGraph V) (w : V → ℝ) :
    weightedIndepNum G w=independentSupport G w := by
  unfold weightedIndepNum independentSupport
  congr 1
  ext s
  constructor
  · rintro ⟨I,hI,rfl⟩
    exact ⟨⟨I,hI⟩,rfl⟩
  · rintro ⟨I,rfl⟩
    exact ⟨I.val,I.property,rfl⟩

/-- For a graph-body system on a nonempty finite vertex type, the simplex infimum of its
weighted independence number equals the reciprocal fractional chromatic number [XuEtAl2026]. -/
theorem alphaMin_eq_inverse_fractionalChromatic [Nonempty V] (B : GraphBodies V) :
    alphaMin B=1/fractionalChromatic B.G := by
  rw [fractionalChromatic_eq_coverValue]
  rw [← support_min_eq_inverse_cover]
  unfold alphaMin alpha
  simp_rw [weightedIndepNum_eq_support]
  change sInf ((independentSupport B.G) '' stdSimplex ℝ V) = _
  change _ = sInf (Set.range (fun w : stdSimplex ℝ V => independentSupport B.G w))
  congr 1
  ext r
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨w,hw⟩,rfl⟩
  · rintro ⟨w,rfl⟩
    exact ⟨w,w.2,rfl⟩

end LP
end Qatlib.Papers.ShadowTomog26.MainResults
