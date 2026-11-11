/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchPrimitive.SampledLaw

/-!
# First-success laws for optional results

`firstBind` keeps a successful optional result and otherwise samples a fallback law;
`firstResult` iterates this operation over a schedule. Point and success probabilities obey
additive recurrences, preserving any common factor between point mass and total success mass.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `firstBind_factor`: If a fixed point mass is the same multiple of success probability in both
  laws, that factor is preserved by `firstBind`.
* `firstResult_factor`: A common factor between a point mass and total success probability in
  every stage is preserved by `firstResult`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
namespace Qatlib.Papers.QAOAScaling23.SearchPrimitive

/-- For a finite optional-result law, the probability of a present result is the sum of the
masses of all `some i`. -/
theorem event_isSome {I : Type} [Fintype I] (p : PMF (Option I)) :
    event p (fun x=>x.isSome)=∑i,p (some i) := by
  simp [event,expectation,tsum_fintype,Fintype.sum_option]

/-- Samples `p`, retaining a present result and using `q` when the first result is `none`. -/
def firstBind {I : Type} (p q : PMF (Option I)) : PMF (Option I) :=
  p.bind fun x=>match x with | none=>q | some i=>PMF.pure (some i)

/-- The mass at `some i` after `firstBind` is its mass under `p` plus the mass of `none` under
`p` times its mass under `q`. -/
theorem firstBind_point {I : Type} [Fintype I] [DecidableEq I]
    (p q : PMF (Option I)) (i : I) :
    firstBind p q (some i)=p (some i)+p none*q (some i) := by
  simp [firstBind,PMF.bind_apply,tsum_fintype,Fintype.sum_option,add_comm]

/-- Success probability after `firstBind` is first-law success plus first-law failure times
fallback success. -/
theorem firstBind_success {I : Type} [Fintype I] [DecidableEq I]
    (p q : PMF (Option I)) :
    event (firstBind p q) (fun x=>x.isSome)=event p (fun x=>x.isSome)+p none*event q (fun x=>x.isSome) := by
  simp only [event_isSome,firstBind_point,Finset.sum_add_distrib,Finset.mul_sum]

/-- If a fixed point mass is the same multiple of success probability in both laws, that factor
is preserved by `firstBind`. -/
theorem firstBind_factor {I : Type} [Fintype I] [DecidableEq I]
    (p q : PMF (Option I)) (i : I) (c : ℝ≥0∞)
    (hp : p (some i)=event p (fun x=>x.isSome)*c)
    (hq : q (some i)=event q (fun x=>x.isSome)*c) :
    firstBind p q (some i)=event (firstBind p q) (fun x=>x.isSome)*c := by
  rw [firstBind_point,firstBind_success,hp,hq]
  ring

/-- Combines optional-result laws along a schedule by retaining the first present result,
returning `none` for an empty schedule. -/
def firstResult {I : Type} (F : ℕ→PMF (Option I)) : List ℕ→PMF (Option I)
  | []=>PMF.pure none
  | m::ms=>firstBind (F m) (firstResult F ms)

/-- A common factor between a point mass and total success probability in every stage is
preserved by `firstResult`. -/
theorem firstResult_factor {I : Type} [Fintype I] [DecidableEq I]
    (F : ℕ→PMF (Option I)) (ms : List ℕ) (i : I) (c : ℝ≥0∞)
    (hF : ∀m,F m (some i)=event (F m) (fun x=>x.isSome)*c) :
    firstResult F ms (some i)=event (firstResult F ms) (fun x=>x.isSome)*c := by
  induction ms with
  | nil => simp [firstResult,event,expectation]
  | cons m ms ih => exact firstBind_factor (F m) (firstResult F ms) i c (hF m) ih
end Qatlib.Papers.QAOAScaling23.SearchPrimitive
