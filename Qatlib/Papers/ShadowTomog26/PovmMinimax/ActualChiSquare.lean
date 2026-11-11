/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.HardBornChi
import Qatlib.Concepts.ShadowModels.ProductPOVM.PauliInvolution
import Qatlib.Concepts.ShadowModels.ProductPOVM.PauliScoreEquality

/-!
# Born chi-square identities for Pauli hard states

This module realizes the hard-state chi-square functional in [XuEtAl2026] with actual Pauli
density operators and POVM outcome distributions. `pauliHardDensity` is the normalized
perturbation of the maximally mixed state in a nonidentity Pauli direction, with perturbation
parameter between zero and one third.

## Main statements

* `source_actual_chi_square` proves support containment and the trace formula for the outcome
  chi-square divergence.
* `source_actual_weighted_chi_square` identifies weighted divergences with `9 * ε^2` times
  `measurementScore`.
* `source_normalized_actual_chi_square` cancels this factor when `ε` is positive.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ShadowTomog26.PovmMinimax
open scoped Classical BigOperators RealInnerProductSpace
open Qatlib.Concepts.ShadowModels.ProductPOVM
open Qatlib.Foundations.FiniteStats.BornEstimator
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Foundations.PureStateMath
variable {Ω V : Type*} [Fintype Ω] [Fintype V]

/-- For a nonidentity Pauli word and `0 ≤ ε ≤ 1/3`, the density state with matrix `(I + 3 * ε *
S) / 2^n`, where `S` is its Pauli observable. -/
def pauliHardDensity (n : ℕ) (word : PauliWord n) (hn : word≠fun _ => .I)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε3 : ε ≤ 1/3) : MState (Reg n) :=
  hardDensity (pauliObservable n word) (pauliObservable_square n word)
    (pauliObservable_trace_zero n word hn) ε hε0 hε3

/-- For a nonidentity Pauli perturbation with `0 ≤ ε ≤ 1/3`, its POVM outcome distribution
vanishes wherever the maximally mixed outcome distribution vanishes. The chi-square
divergence is `9 * ε^2` times the sum of squared effect-Pauli inner products divided by
`qubitDimension n` times each effect trace [XuEtAl2026]. -/
theorem source_actual_chi_square (n : ℕ) (word : PauliWord n) (hn : word≠fun _ => .I)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε3 : ε ≤ 1/3) (P : POVM Ω (Reg n)) :
    (∀ s,((P.measure (referenceDensity : MState (Reg n))) s:ℝ)=0 →
      ((P.measure (pauliHardDensity n word hn ε hε0 hε3)) s:ℝ)=0) ∧
    finiteChiSquare (fun s => ((P.measure (pauliHardDensity n word hn ε hε0 hε3)) s:ℝ))
      (fun s => ((P.measure (referenceDensity : MState (Reg n))) s:ℝ))=
      9*ε^2*(∑ s,⟪P.mats s,pauliObservable n word⟫^2/(qubitDimension n*(P.mats s).trace)) := by
  constructor
  · exact hardBorn_support P _ (pauliObservable_square n word)
      (pauliObservable_trace_zero n word hn) ε hε0 hε3
  · simpa only [card_qubitRegister] using!
      hardBorn_chiSquare P _ (pauliObservable_square n word) (pauliObservable_trace_zero n word hn) ε hε0 hε3

/-- For nonidentity target Pauli words and `0 ≤ ε ≤ 1/3`, the weighted sum of hard-state outcome
chi-square divergences from the maximally mixed outcomes equals `9 * ε^2 *
measurementScore`. -/
theorem source_actual_weighted_chi_square (n : ℕ) (words : V → PauliWord n)
    (hn : ∀ i,words i≠fun _ => .I) (w : V → ℝ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε3 : ε ≤ 1/3) (P : POVM Ω (Reg n)) :
    (∑ i,w i*finiteChiSquare
      (fun s => ((P.measure (pauliHardDensity n (words i) (hn i) ε hε0 hε3)) s:ℝ))
      (fun s => ((P.measure (referenceDensity : MState (Reg n))) s:ℝ)))=
      9*ε^2*measurementScore (fun i => pauliObservable n (words i)) w P := by
  have he (i : V) := hardBorn_chiSquare P (pauliObservable n (words i)) (pauliObservable_square n (words i))
    (pauliObservable_trace_zero n (words i) (hn i)) ε hε0 hε3
  change (∑ i,w i*finiteChiSquare
      (fun s => ((P.measure (hardDensity (pauliObservable n (words i)) (pauliObservable_square n (words i))
        (pauliObservable_trace_zero n (words i) (hn i)) ε hε0 hε3)) s:ℝ))
      (fun s => ((P.measure (referenceDensity : MState (Reg n))) s:ℝ)))=_
  simp_rw [he]
  unfold measurementScore
  simp only [Finset.mul_sum,Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- For nonidentity target Pauli words and `0 < ε ≤ 1/3`, dividing the weighted sum of
hard-state outcome chi-square divergences by `9 * ε^2` gives `measurementScore`
[XuEtAl2026]. -/
theorem source_normalized_actual_chi_square (n : ℕ) (words : V → PauliWord n)
    (hn : ∀ i,words i≠fun _ => .I) (w : V → ℝ)
    (ε : ℝ) (hε0 : 0<ε) (hε3 : ε ≤ 1/3) (P : POVM Ω (Reg n)) :
    (∑ i,w i*finiteChiSquare
      (fun s => ((P.measure (pauliHardDensity n (words i) (hn i) ε hε0.le hε3)) s:ℝ))
      (fun s => ((P.measure (referenceDensity : MState (Reg n))) s:ℝ)))/(9*ε^2)=
      measurementScore (fun i => pauliObservable n (words i)) w P := by
  rw [source_actual_weighted_chi_square]
  have hs : 9*ε^2≠0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hε0.ne')
  exact mul_div_cancel_left₀ _ hs

end Qatlib.Papers.ShadowTomog26.PovmMinimax
