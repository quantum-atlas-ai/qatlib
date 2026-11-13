/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Finite tensor products of pure states

This module defines `PiTensorState` by multiplying amplitudes over a finite family of state
factors. It proves factorization of Born probabilities, preservation of normalization, and the
constant basis state identity, providing the finite tensor product calculations described in
[NielsenChuang2010].

## Main statements

* `bornProb_piTensorState`: basis outcome probabilities factor over the component states.
* `normalized_piTensorState`: normalized factors give a normalized tensor state.
* `piTensorState_const_ket`: identical basis state factors give a constant tuple basis state.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Concepts.QueryComplexity.Amplification

set_option autoImplicit false

variable {I : Type*} [Fintype I] [DecidableEq I]

section PiTensorState

variable {ι : Type*} [Fintype ι]

/-- The finite tensor state whose amplitude at a tuple is the product of the component state
amplitudes. -/
noncomputable def PiTensorState (ψ : ι → QState I) : QState (ι → I) :=
  fun ω => ∏ j, ψ j (ω j)

omit [Fintype I] [DecidableEq I] in

/-- The amplitude of a finite tensor state is the product of its factor amplitudes. -/
@[simp] theorem piTensorState_apply (ψ : ι → QState I) (ω : ι → I) :
    PiTensorState ψ ω = ∏ j, ψ j (ω j) := rfl

omit [Fintype I] [DecidableEq I] in

/-- The Born probability of a tensor basis outcome is the product of the corresponding factor
Born probabilities. -/
theorem bornProb_piTensorState {ι : Type*} [Fintype ι] (ψ : ι → QState I) (ω : ι → I) :
    BornProb (PiTensorState ψ) ω = ∏ j, BornProb (ψ j) (ω j) := by
  simp only [BornProb, piTensorState_apply]
  rw [Complex.norm_prod, ← Finset.prod_pow]

/-- A finite tensor product of normalized states is normalized. -/
theorem normalized_piTensorState {ι : Type*} [Fintype ι] [DecidableEq ι] {ψ : ι → QState I}
    (hψ : ∀ j, Normalized (ψ j)) : Normalized (PiTensorState ψ) := by
  have hswap : (∏ j : ι, ∑ i : I, BornProb (ψ j) i)
      = ∑ ω ∈ Fintype.piFinset (fun (_ : ι) => (Finset.univ : Finset I)),
          ∏ j, BornProb (ψ j) (ω j) :=
    Finset.prod_univ_sum (fun (_ : ι) => (Finset.univ : Finset I))
      (fun (j : ι) (i : I) => BornProb (ψ j) i)
  rw [Fintype.piFinset_univ] at hswap
  show ∑ ω : ι → I, BornProb (PiTensorState ψ) ω = 1
  rw [Finset.sum_congr rfl fun ω _ => bornProb_piTensorState ψ ω, ← hswap]
  exact Finset.prod_eq_one fun j _ => hψ j

omit [Fintype I] in

/-- The tensor product of copies of one basis state is the basis state at the corresponding
constant tuple. -/
theorem piTensorState_const_ket {ι : Type*} [Fintype ι] (i : I) :
    PiTensorState (fun _ : ι => Ket i) = Ket (fun _ => i) := by
  funext ω
  simp only [piTensorState_apply, ket_apply]
  by_cases h : ∀ j, ω j = i
  · rw [ite_eq_left (funext h), Finset.prod_eq_one]
    intro j _
    exact ite_eq_left (h j)
  · push Not at h
    obtain ⟨j₀, hj₀⟩ := h
    rw [ite_eq_right (fun hcon => hj₀ (congrFun hcon j₀)),
      Finset.prod_eq_zero (Finset.mem_univ j₀) (ite_eq_right hj₀)]

end PiTensorState

end Qatlib.Concepts.QueryComplexity.Amplification
