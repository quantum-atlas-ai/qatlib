/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalQuantum
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PeriodFour

set_option backward.isDefEq.respectTransparency false

/-!
# Dense Family

The original selected-axis double shift exchanges the two side classes at every site.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder MatrixOrder

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseFamily
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridMatching
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridLossBridge
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- The original selected-axis double shift exchanges the two side classes at every site. -/
theorem graph_zero_side (d K : ℕ) [NeZero (K*4)]
    (a : ((Fin K × Bool) × (Fin d → Fin (K*4))) × Bool) :
    (doubleGraph d K 0 a).2=!(a.2) := by
  rcases a with ⟨e,t⟩
  cases t
  · rw [doubleGraph_matched]
    rfl
  · cases ht : (doubleGraph d K 0 (e,true)).2 with
    | false => rfl
    | true =>
      exfalso
      have he : doubleGraph d K 0 (e,true)=doubleGraph d K 0 ((doubleGraph d K 0 (e,true)).1,false) := by
        rw [doubleGraph_matched]
        exact Prod.ext rfl ht
      have hs := congrArg Prod.snd ((doubleGraph d K 0).injective he)
      exact Bool.noConfusion hs

/-- Transverse original double shifts retain the selected-axis side coordinate literally. -/
theorem graph_succ_side (d K : ℕ) [NeZero (K*4)] (j : Fin d)
    (a : ((Fin K × Bool) × (Fin d → Fin (K*4))) × Bool) :
    (doubleGraph d K j.succ a).2=a.2 := by
  have hz : (grid d K).symm (doubleGraph d K j.succ a) 0=(grid d K).symm a 0 := by
    rw [doubleGraph_inverse]
    apply (ZMod.finEquiv (K*4)).injective
    rw [periodic_double_shift_coordinates]
    simp only [ite_eq_right (Ne.symm (Fin.succ_ne_zero j)),add_zero]
  rw [grid_zero,grid_zero] at hz
  exact congrArg (fun z : (Fin K × Bool) × Bool => z.2) ((coordinate K).symm.injective hz)

/-- The literal first positive/second negative sign pair is the original dense real witness within the same weak-input family. -/
theorem sign_one {E : Type*} (a : E × Bool) : siteSign (fun _ : E => (1 : Fin 4)) a=if a.2 then -1 else 1 := by
  rcases a with ⟨e,t⟩
  cases t <;> rfl

/-- The literal fourth pair state is the original constant positive-sign witness in that same family. -/
theorem sign_three {E : Type*} (a : E × Bool) : siteSign (fun _ : E => (3 : Fin 4)) a=1 := by
  rcases a with ⟨e,t⟩
  cases t <;> rfl

/-- The original dense sign field is an actual single fixed assignment of the same pair variables. -/
def denseSign (d N : ℕ) (h4 : 4∣N) (x : Fin (d+1) → Fin N) : ℝ :=
  siteSign (fun _ : PairLabels d N => (1 : Fin 4)) (originalGrid d N h4 x)

/-- Every sign in the actual dense original field has unit magnitude. -/
theorem denseSign_unit (d N : ℕ) (h4 : 4∣N) (x : Fin (d+1) → Fin N) : (denseSign d N h4 x)^2=1 :=
  siteSign_unit _ _

/-- The actual dense original field is balanced on the complete original grid. -/
theorem denseSign_sum (d N : ℕ) (h4 : 4∣N) : (∑ x : Fin (d+1) → Fin N,denseSign d N h4 x)=0 := by
  calc
    _ = ∑ a : PairLabels d N × Bool,siteSign (fun _ : PairLabels d N => (1 : Fin 4)) a :=
      Equiv.sum_comp (originalGrid d N h4) _
    _ = 0 := by
      simp only [Fintype.sum_prod_type,Fintype.sum_bool,sign_one,ite_true,Bool.false_eq_true,ite_false,neg_add_cancel,Finset.sum_const_zero]

/-- The dense family field flips in precisely the first original double-shift direction. -/
theorem denseSign_double_shift (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N) (j : Fin (d+1))
    (x : Fin (d+1) → Fin N) :
    denseSign d N h4 (periodicDoubleShift (d+1) N j x)=
      if j=0 then -denseSign d N h4 x else denseSign d N h4 x := by
  have hK := original_block_range N hN h4
  let : NeZero ((N/4)*4) := ⟨by omega⟩
  have he : originalGrid d N h4 (periodicDoubleShift (d+1) N j x)=originalGraph d N h4 j (originalGrid d N h4 x) := by
    simp only [originalGraph,Equiv.trans_apply,Equiv.symm_apply_apply]
  unfold denseSign
  rw [he,originalGraph_eq]
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [ite_true,sign_one,graph_zero_side]
    cases (originalGrid d N h4 x).2 <;> norm_num
  · simp only [ite_eq_right (Fin.succ_ne_zero k),sign_one,graph_succ_side]

/-- Zero source phase means exactly the real physical weak field in the original supplied-state coordinates. -/
theorem original_field_zero_phase (d N : ℕ) (h4 : 4∣N) (b : ℝ) (κ : PairLabels d N → Fin 4) (Q : ℕ) :
    originalField d N h4 b κ Q (fun _ => 0)=(fun x => pairedWeakSpin b κ (originalGrid d N h4 x)) := by
  funext x s
  change rootPhase Q 0*pairedWeakSpin b κ (originalGrid d N h4 x) s=_
  simp only [rootPhase,Fin.val_zero,pow_zero,one_mul]

/-- The actual dense field has the exact original Bell value in every physical grid direction. -/
theorem dense_bell (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N) (j : Fin (d+1))
    (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1) (x : Fin (d+1) → Fin N) :
    bellProbability (weakSpin b (denseSign d N h4 x))
      (weakSpin b (denseSign d N h4 (periodicDoubleShift (d+1) N j x)))=
        if j=0 then 2*b*(1-b) else 0 := by
  rw [weakSpin_bell_exact b _ _ hb0 hb1,denseSign_double_shift d N hN h4 j x]
  by_cases hj : j=0
  · rw [ite_eq_left hj,ite_eq_left hj]
    calc
      _ = 2*b*(1-b)*(denseSign d N h4 x)^2 := by ring
      _ = _ := by rw [denseSign_unit,mul_one]
  · simp only [ite_eq_right hj,sub_self,zero_pow (by decide : (2 : ℕ)≠0),mul_zero,zero_div]

/-- The dense Bell probabilities give the exact full original directional mean. -/
theorem dense_bell_mean (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N) (j : Fin (d+1))
    (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1) :
    bellMean (real0 (fun x => weakSpin b (denseSign d N h4 x)))
      (imag0 (fun x => weakSpin b (denseSign d N h4 x)))
      (real1 (fun x => weakSpin b (denseSign d N h4 x)))
      (imag1 (fun x => weakSpin b (denseSign d N h4 x))) (periodicDoubleShift (d+1) N j)=
        if j=0 then 2*b*(1-b) else 0 := by
  unfold bellMean
  simp_rw [complexSpinor_parts,dense_bell d N hN h4 j b hb0 hb1]
  exact site_mean_const _

/-- The actual dense original-family member has exactly the source's full loss, with its real current identically zero. -/
theorem dense_family_full_loss (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N) (b : ℝ)
    (hb0 : 0≤b) (hb1 : b≤1) (Q : ℕ) (h lam : ℝ) (hh : h≠0) :
    originalFieldLoss d N h4 b (fun _ => 1) Q (fun _ => 0) h lam=(2*lam^2/h^2)*(2*b*(1-b)) := by
  unfold originalFieldLoss
  rw [original_field_zero_phase]
  change spinorDiscreteLoss (real0 (fun x => weakSpin b (denseSign d N h4 x)))
    (imag0 (fun x => weakSpin b (denseSign d N h4 x)))
    (real1 (fun x => weakSpin b (denseSign d N h4 x)))
    (imag1 (fun x => weakSpin b (denseSign d N h4 x)))
    (fun _ _ => 0) (periodicUnitShift (d+1) N) h 1 lam=_
  rw [PeriodFour.real_weak_loss_bell b (denseSign d N h4) hb0 hb1 (denseSign_unit d N h4) _ h lam hh]
  simp only [periodic_unit_shift_square,dense_bell_mean d N hN h4 _ b hb0 hb1,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- The constant original-family member has exactly zero complete physical loss. -/
theorem constant_family_full_loss (d N : ℕ) [NeZero N] (h4 : 4∣N) (b : ℝ)
    (hb0 : 0≤b) (hb1 : b≤1) (Q : ℕ) (h lam : ℝ) (hh : h≠0) :
    originalFieldLoss d N h4 b (fun _ => 3) Q (fun _ => 0) h lam=0 := by
  unfold originalFieldLoss
  rw [original_field_zero_phase]
  have hv : (fun x => pairedWeakSpin b (fun _ : PairLabels d N => 3) (originalGrid d N h4 x))=
      (fun _x : Fin (d+1) → Fin N => weakSpin b 1) := by
    funext x
    change weakSpin b (siteSign (fun _ => 3) (originalGrid d N h4 x))=_
    rw [sign_three]
  rw [hv]
  exact PeriodFour.constant_full_loss _ b hb0 hb1 h lam hh

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseFamily
