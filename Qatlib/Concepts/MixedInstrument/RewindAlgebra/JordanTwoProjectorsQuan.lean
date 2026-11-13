/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.RewindAlgebra.JordanTwoProjectorsStat
import Qatlib.Concepts.MixedInstrument.RewindAlgebra.RejectionOriginalContracts
import Qatlib.Concepts.WalkSearch.Spectral.CompleteCSDecomposition
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

/-!
# Jordan decomposition for two projectors

This module proves `jordanTwoProjectors`, decomposing two orthogonal projectors into one and two
dimensional invariant pieces with zero companion vectors at endpoint eigenvalues. It also
refutes the legacy formulation and supplies normalized coordinates for states in the range of
the first projector. This is the two projector framework used in amplification
[NagajWocjanZhang2009].

## Main statements

* `jordanTwoProjectors_false`: The legacy two projector proposition requiring all companion
  vectors to be normalized is false.
* `jordanTwoProjectors`: Two orthogonal projectors possess the decomposition specified by
  `JordanTwoProjectors`, with normalized companion vectors only for interior eigenvalues; see
  [NagajWocjanZhang2009].
* `jordan_range_state_coordinates`: A normalized vector fixed by `P` has an expansion in a
  finite orthonormal family with squared coordinate norms summing to one, under the stated
  projector hypotheses.

## References

* [Nagaj, Wocjan, and Zhang, 2009][NagajWocjanZhang2009]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.MixedInstrument.RewindAlgebra
open Matrix

/-- The legacy two projector proposition requiring all companion vectors to be normalized is
false. -/
theorem jordanTwoProjectors_false : ¬ JordanTwoProjectorsLegacy := by
  classical
  intro h
  obtain ⟨k,u,v,_d,_W,_hd,hu,hv,huv,_hW,_hWi,_hWQ,_hfull,hP,_hQu,_hQv⟩ :=
    h 1 1 0 (by simp) (by simp) (by simp) (by simp)
  cases k with
  | zero =>
    have he := congrFun (hP (fun _ => 1)) 0
    simp at he
  | succ k =>
    have huu := hu 0 0
    have hvv := hv 0 0
    have huv0 := huv 0 0
    simp only [inner_apply, Fin.sum_univ_one, if_true] at huu hvv huv0
    have hune : (starRingEnd ℂ) (u 0 0) ≠ 0 := by
      intro hz
      rw [hz,zero_mul] at huu
      exact zero_ne_one huu
    have hvzero := (mul_eq_zero.mp huv0).resolve_left hune
    rw [hvzero,map_zero,zero_mul] at hvv
    exact zero_ne_one hvv

end Qatlib.Concepts.MixedInstrument.RewindAlgebra

namespace Qatlib.Concepts.MixedInstrument.RewindAlgebra.Temme2011
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical BigOperators

/-- The inner product of columns `i` and `j` of two matrices is entry `(i, j)` of their
conjugate transpose product. -/
private theorem column_inner {H J : Type} [Fintype H] [DecidableEq H]
    [Fintype J] (A B : Matrix H J ℂ) (i j : J) :
    Qatlib.Foundations.PureStateMath.Inner (fun h => A h i) (fun h => B h j) = (Aᴴ*B) i j := rfl

/-- The action of `A * Aᴴ` is the sum of the columns of `A` weighted by their inner products
with the input vector. -/
private theorem column_resolution {H J : Type} [Fintype H] [DecidableEq H]
    [Fintype J] (A : Matrix H J ℂ) (x : QState H) :
    (A*Aᴴ)*ᵥx = ∑ i, Qatlib.Foundations.PureStateMath.Inner (fun h => A h i) x • (fun h => A h i) := by
  rw [← Matrix.mulVec_mulVec]
  funext h
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Qatlib.Foundations.PureStateMath.Inner,
    Pi.star_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Two orthogonal projectors possess the decomposition specified by `JordanTwoProjectors`, with
normalized companion vectors only for interior eigenvalues; see [NagajWocjanZhang2009]. -/
theorem jordanTwoProjectors : JordanTwoProjectors := by
  classical
  intro D P Q hPs hPi hQs hQi
  have hP : IsOrthogonalProjector P := ⟨hPi,hPs⟩
  have hQ : IsOrthogonalProjector Q := ⟨hQi,hQs⟩
  obtain ⟨A,t,hb,hA,hAP,ht⟩ := cs_projector_compressed_eigenframe P Q hP hQ
  let J := CSProjectorSupport P hP
  let e := (Fintype.equivFin J).symm
  let B := csCrossNormalized Q A t
  let T := A*Aᴴ+B*Bᴴ
  let W := 1-T
  let u := fun i : Fin (Fintype.card J) => fun h => A h (e i)
  let v := fun i : Fin (Fintype.card J) => fun h => B h (e i)
  let d := fun i : Fin (Fintype.card J) => t (e i)
  have hg := cs_cross_normalized_grams Q hQ A t hA ht hb
  have hT := cs_busy_sum_isProjector_and_commutes Q hQ A t hA ht hb
  have hW : IsOrthogonalProjector W := isOrthogonalProjector_compl hT.1
  have hsum (C : Matrix (Fin D) J ℂ) (x : QState (Fin D)) :
      (C*Cᴴ)*ᵥx = ∑ i : Fin (Fintype.card J),
        Qatlib.Foundations.PureStateMath.Inner (fun h => C h (e i)) x • (fun h => C h (e i)) := by
    rw [column_resolution]
    exact (e.sum_comp (fun j => Qatlib.Foundations.PureStateMath.Inner (fun h => C h j) x • (fun h => C h j))).symm
  have hQaction := cs_cross_Q_actions Q hQ A t hA ht hb
  have hQa : Q*A=A*(diagonal (fun i => (t i : ℂ))) +
      B*(diagonal (fun i => (Real.sqrt (t i*(1-t i)) : ℂ))) := hQaction.1
  have hQb : Q*B=A*(diagonal (fun i => (Real.sqrt (t i*(1-t i)) : ℂ))) +
      B*(diagonal (fun i => ((1-t i : ℝ) : ℂ))) := hQaction.2
  refine ⟨Fintype.card J,u,v,d,W,(fun i => hb (e i)),?_,?_,?_,hW.2,hW.1,?_,?_,?_,?_,?_⟩
  · intro i j
    rw [column_inner, show Aᴴ*A=1 from hA]
    simp only [Matrix.one_apply, e.injective.eq_iff]
  · intro i j
    rw [column_inner, hg.2]
    simp only [Matrix.diagonal_apply, e.injective.eq_iff]
    rfl
  · intro i j
    rw [column_inner]
    have hAB : Aᴴ*B=0 := hg.1
    rw [hAB]
    rfl
  · change (1-T)*Q=Q*(1-T)
    rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one]
    exact congrArg (fun X => Q-X) hT.2.1.symm
  · intro x
    rw [← hsum A x, ← hsum B x]
    change ((A*Aᴴ)*ᵥx + (B*Bᴴ)*ᵥx) + (1-(A*Aᴴ+B*Bᴴ))*ᵥx = x
    rw [Matrix.sub_mulVec,Matrix.add_mulVec,Matrix.one_mulVec]
    module
  · intro x
    rw [← hsum A x, hAP]
  · intro i
    funext h
    have he := congrFun (congrFun hQa h) (e i)
    simp only [Matrix.add_apply, Matrix.mul_diagonal] at he
    simpa only [Matrix.mul_apply,
      Matrix.mulVec, dotProduct, u, v, d, B, Pi.add_apply, Pi.smul_apply,
      Complex.real_smul, smul_eq_mul, mul_comm] using he
  · intro i
    funext h
    have he := congrFun (congrFun hQb h) (e i)
    simp only [Matrix.add_apply, Matrix.mul_diagonal] at he
    simpa only [Matrix.mul_apply,
      Matrix.mulVec, dotProduct, u, v, d, B, Pi.add_apply, Pi.smul_apply,
      Complex.real_smul, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_one, mul_comm] using he

/-- A normalized vector fixed by `P` has an expansion in a finite orthonormal family with
squared coordinate norms summing to one, under the stated projector hypotheses. -/
theorem jordan_range_state_coordinates (D : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (ψ : QState (Fin D)) (hψ : P*ᵥψ=ψ) (hnorm : Qatlib.Foundations.PureStateMath.Inner ψ ψ=1) :
    ∃ (k : ℕ) (u : Fin k → QState (Fin D)),
      (∀ i j, Qatlib.Foundations.PureStateMath.Inner (u i) (u j) = if i=j then 1 else 0) ∧
      ψ = ∑ i, Qatlib.Foundations.PureStateMath.Inner (u i) ψ • u i ∧ (∑ i, ‖Qatlib.Foundations.PureStateMath.Inner (u i) ψ‖^2)=1 := by
  obtain ⟨k,u,_v,_d,_W,_hb,hu,_hv,_huv,_hWH,_hWi,_hWQ,_hfull,hP,_hQu,_hQv⟩ :=
    jordanTwoProjectors D P Q hPs hPi hQs hQi
  have he : ψ = ∑ i, Qatlib.Foundations.PureStateMath.Inner (u i) ψ • u i :=
      hψ.symm.trans (hP ψ)
  refine ⟨k,u,hu,he,?_⟩
  have hn : Normalized ψ := (normalized_iff_inner_self ψ).mpr hnorm
  unfold Normalized at hn
  rw [he, sum_norm_sq_orthonormal u (fun i => Qatlib.Foundations.PureStateMath.Inner (u i) ψ) (fun i j => by
    by_cases h : i=j
    · simpa only [if_pos h] using hu i j
    · simpa only [if_neg h] using hu i j)] at hn
  exact hn
end Qatlib.Concepts.MixedInstrument.RewindAlgebra.Temme2011
