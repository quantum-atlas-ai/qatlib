/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Tensor
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Concepts.QueryComplexity.Amplification

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

section PiTensorState

variable {ι : Type*} [Fintype ι]

noncomputable def PiTensorState (ψ : ι → QState I) : QState (ι → I) :=
  fun ω => ∏ j, ψ j (ω j)

@[simp] theorem piTensorState_apply (ψ : ι → QState I) (ω : ι → I) :
    PiTensorState ψ ω = ∏ j, ψ j (ω j) := rfl

theorem bornProb_piTensorState {ι : Type*} [Fintype ι] (ψ : ι → QState I) (ω : ι → I) :
    BornProb (PiTensorState ψ) ω = ∏ j, BornProb (ψ j) (ω j) := by
  simp only [BornProb, piTensorState_apply]
  rw [Complex.norm_prod, ← Finset.prod_pow]

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

theorem piTensorState_const_ket {ι : Type*} [Fintype ι] (i : I) :
    PiTensorState (fun _ : ι => Ket i) = Ket (fun _ => i) := by
  funext ω
  simp only [piTensorState_apply, ket_apply]
  by_cases h : ∀ j, ω j = i
  · rw [if_pos (funext h), Finset.prod_eq_one]
    intro j _
    exact if_pos (h j)
  · push Not at h
    obtain ⟨j₀, hj₀⟩ := h
    rw [if_neg (fun hcon => hj₀ (congrFun hcon j₀)),
      Finset.prod_eq_zero (Finset.mem_univ j₀) (if_neg hj₀)]

end PiTensorState

end Qatlib.Concepts.QueryComplexity.Amplification
