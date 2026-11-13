/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates

/-!
# Products of purification vectors

Defines `PurificationProduct` by multiplying the amplitudes of a finite family of bipartite
vectors, grouping all system indices and all environment indices. It proves factorization of
inner products and preservation of normalization.

The partial trace of the product outer product is the entrywise product formula for the
component reduced matrices. The tensor-product and purification setting is described in
[NielsenChuang2010].

## Main statements

* `inner_purificationProduct`: inner products factor across components.
* `normalized_purificationProduct`: normalized components give a normalized product.
* `traceRight_purificationProduct`: partial trace factors across components.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S E : ι → Type*} [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)]
    [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]

/-- The vector obtained by multiplying component purification amplitudes, with system and
environment coordinates grouped separately. -/
noncomputable def PurificationProduct (ψ : (j : ι) → QState (S j × E j)) :
    QState (((j : ι) → S j) × ((j : ι) → E j)) :=
  fun p => ∏ j, ψ j (p.1 j, p.2 j)

/-- A finite sum of products over dependent function indices factors as the product of the
component sums. -/
private theorem sum_pi_prod {A : ι → Type*} [∀ j, Fintype (A j)]
    (f : (j : ι) → A j → ℂ) :
    (∑ x : (j : ι) → A j, ∏ j, f j (x j)) = ∏ j, ∑ a, f j a := by
  have h := Finset.prod_univ_sum (fun j => (Finset.univ : Finset (A j))) f
  rw [Fintype.piFinset_univ] at h
  exact h.symm

/-- The inner product of two purification products equals the product of their component inner
products. -/
theorem inner_purificationProduct (ψ φ : (j : ι) → QState (S j × E j)) :
    Inner (PurificationProduct ψ) (PurificationProduct φ) =
      ∏ j, Inner (ψ j) (φ j) := by
  rw [inner_apply]
  simp only [Fintype.sum_prod_type, PurificationProduct, map_prod,
    ← Finset.prod_mul_distrib]
  calc
    (∑ s : (j : ι) → S j, ∑ e : (j : ι) → E j,
        ∏ j, (starRingEnd ℂ) (ψ j (s j, e j)) * φ j (s j, e j)) =
        ∑ s : (j : ι) → S j, ∏ j, ∑ e : E j,
          (starRingEnd ℂ) (ψ j (s j, e)) * φ j (s j, e) := by
      apply Finset.sum_congr rfl
      intro s _
      exact sum_pi_prod (A := E) (fun j e =>
        (starRingEnd ℂ) (ψ j (s j, e)) * φ j (s j, e))
    _ = ∏ j, ∑ s : S j, ∑ e : E j,
          (starRingEnd ℂ) (ψ j (s, e)) * φ j (s, e) :=
      sum_pi_prod (A := S) (fun j s =>
        ∑ e : E j, (starRingEnd ℂ) (ψ j (s, e)) * φ j (s, e))
    _ = ∏ j, Inner (ψ j) (φ j) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [inner_apply, Fintype.sum_prod_type]

/-- A product of normalized purification vectors is normalized. -/
theorem normalized_purificationProduct {ψ : (j : ι) → QState (S j × E j)}
    (hψ : ∀ j, Normalized (ψ j)) : Normalized (PurificationProduct ψ) := by
  rw [normalized_iff_inner_self, inner_purificationProduct]
  apply Finset.prod_eq_one
  intro j _
  exact (normalized_iff_inner_self _).mp (hψ j)

omit [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)] [∀ j, DecidableEq (E j)] in

/-- Tracing out all environment coordinates of a purification product gives the product of the
component reduced-matrix entries. -/
theorem traceRight_purificationProduct (ψ : (j : ι) → QState (S j × E j)) :
    Matrix.traceRight (outerProduct (PurificationProduct ψ)) =
      fun s t => ∏ j, Matrix.traceRight (outerProduct (ψ j)) (s j) (t j) := by
  ext s t
  simp only [Matrix.traceRight, outerProduct_apply, PurificationProduct, map_prod,
    ← Finset.prod_mul_distrib]
  exact sum_pi_prod (A := E) (fun j e =>
    ψ j (s j, e) * (starRingEnd ℂ) (ψ j (t j, e)))

end Qatlib.Concepts.MbqcFlow.FlowDecision
