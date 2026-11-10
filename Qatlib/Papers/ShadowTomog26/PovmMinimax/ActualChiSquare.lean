/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.HardBornChi
import Qatlib.Concepts.ShadowModels.ProductPOVM.PauliInvolution
import Qatlib.Concepts.ShadowModels.ProductPOVM.PauliScoreEquality
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

def pauliHardDensity (n : ℕ) (word : PauliWord n) (hn : word≠fun _ => .I)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε3 : ε ≤ 1/3) : MState (Reg n) :=
  hardDensity (pauliObservable n word) (pauliObservable_square n word)
    (pauliObservable_trace_zero n word hn) ε hε0 hε3

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
