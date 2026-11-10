/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
open Qatlib.Foundations.PureStateMath
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S E : ι → Type*} [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)]
    [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]

noncomputable def PurificationProduct (ψ : (j : ι) → QState (S j × E j)) :
    QState (((j : ι) → S j) × ((j : ι) → E j)) :=
  fun p => ∏ j, ψ j (p.1 j, p.2 j)

private theorem sum_pi_prod {A : ι → Type*} [∀ j, Fintype (A j)]
    (f : (j : ι) → A j → ℂ) :
    (∑ x : (j : ι) → A j, ∏ j, f j (x j)) = ∏ j, ∑ a, f j a := by
  have h := Finset.prod_univ_sum (fun j => (Finset.univ : Finset (A j))) f
  rw [Fintype.piFinset_univ] at h
  exact h.symm

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

theorem normalized_purificationProduct {ψ : (j : ι) → QState (S j × E j)}
    (hψ : ∀ j, Normalized (ψ j)) : Normalized (PurificationProduct ψ) := by
  rw [normalized_iff_inner_self, inner_purificationProduct]
  apply Finset.prod_eq_one
  intro j _
  exact (normalized_iff_inner_self _).mp (hψ j)

omit [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)] [∀ j, DecidableEq (E j)] in

theorem traceRight_purificationProduct (ψ : (j : ι) → QState (S j × E j)) :
    Matrix.traceRight (outerProduct (PurificationProduct ψ)) =
      fun s t => ∏ j, Matrix.traceRight (outerProduct (ψ j)) (s j) (t j) := by
  ext s t
  simp only [Matrix.traceRight, outerProduct_apply, PurificationProduct, map_prod,
    ← Finset.prod_mul_distrib]
  exact sum_pi_prod (A := E) (fun j e =>
    ψ j (s j, e) * (starRingEnd ℂ) (ψ j (t j, e)))

end Qatlib.Concepts.MbqcFlow.FlowDecision
