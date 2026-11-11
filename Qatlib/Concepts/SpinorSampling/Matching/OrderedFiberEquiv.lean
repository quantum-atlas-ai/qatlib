/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.OrderedEnumerationCount

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Ordered Fiber Equiv

Ordered Fiber Equiv constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators

variable {S : Type} [DecidableEq S]

/-- Construction for ordered Fiber in the ordered fiber equiv model. -/
def orderedFiber (A : Finset S) (k : ℕ) :=
  {ω : Fin k → S // Function.Injective ω ∧ occupiedSites ω=A}

/-- Construction for fiber To Equiv in the ordered fiber equiv model. -/
def fiberToEquiv {A : Finset S} {k : ℕ} (z : orderedFiber A k) : Fin k ≃ A := by
  let e : Fin k → A := fun i => ⟨z.1 i, by
    have hi : z.1 i ∈ occupiedSites z.1 :=
      Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
    simpa [z.2.2] using hi⟩
  have hinj : Function.Injective e := by
    intro i j h
    exact z.2.1 (Subtype.ext_iff.mp h)
  have hsurj : Function.Surjective e := by
    intro x
    have hx : (x : S) ∈ occupiedSites z.1 := by
      rw [z.2.2]
      exact x.property
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
    exact ⟨i,Subtype.ext hi⟩
  exact Equiv.ofBijective e ⟨hinj,hsurj⟩

/-- Construction for equiv To Fiber in the ordered fiber equiv model. -/
def equivToFiber {A : Finset S} {k : ℕ} (e : Fin k ≃ A) : orderedFiber A k :=
  ⟨fun i => e i,
    (by
      intro i j h
      apply e.injective
      exact Subtype.ext h),
    by
      ext x
      simp only [occupiedSites,Finset.mem_image,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨i,rfl⟩
        exact (e i).property
      · intro hx
        obtain ⟨i,hi⟩ := e.surjective ⟨x,hx⟩
        exact ⟨i,congrArg Subtype.val hi⟩⟩

/-- Construction for ordered Fiber Equiv in the ordered fiber equiv model. -/
def orderedFiberEquiv (A : Finset S) (k : ℕ) : orderedFiber A k ≃ (Fin k ≃ A) where
  toFun := fiberToEquiv
  invFun := equivToFiber
  left_inv z := by
    apply Subtype.ext
    funext i
    rfl
  right_inv e := by
    apply Equiv.ext
    intro i
    rfl

/-- Typeclass instance for ordered Fiber Fintype in the ordered fiber equiv model. -/
instance orderedFiberFintype (A : Finset S) (k : ℕ) : Fintype (orderedFiber A k) :=
  Fintype.ofEquiv (Fin k ≃ A) (orderedFiberEquiv A k).symm

/-- Complete original `ordered_fiber_card` guarantee for `OrderedFiberEquiv`; all source hypotheses and output obligations are retained. -/
theorem ordered_fiber_card (A : Finset S) (k : ℕ) :
    Fintype.card (orderedFiber A k)=
      Fintype.card (Fin k ≃ A) :=
  Fintype.card_congr (orderedFiberEquiv A k)

/-- Complete original `ordered_fiber_card_factorial` guarantee for `OrderedFiberEquiv`; all source hypotheses and output obligations are retained. -/
theorem ordered_fiber_card_factorial (A : Finset S) {k : ℕ} (hcard : A.card = k) :
    Fintype.card (orderedFiber A k) = Nat.factorial k := by
  rw [ordered_fiber_card, finset_ordered_enumeration_count A hcard]

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.fiberToEquiv
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.equivToFiber
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.orderedFiberEquiv
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.ordered_fiber_card

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.ordered_fiber_card_factorial
