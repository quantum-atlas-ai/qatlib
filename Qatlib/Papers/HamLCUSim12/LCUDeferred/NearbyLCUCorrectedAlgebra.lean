/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedDefinitions
import Qatlib.Concepts.CoherentSim.ResetDiscard.Theorem13CorrectedHami
import Qatlib.Concepts.BlockEncoding.Postselection

/-!
# Output fibers of the corrected two-unitary circuit

This module identifies `lemma2CircuitCorrected` with the relabeled prepare-select-unprepare
circuit of Figure 3 in [ChildsWiebe2012]. It proves unitarity of `vKappaSource` and computes
both ancilla output fibers, including the failure fiber proportional to `Ub - Ua`.

`lemma2FailureProbCorrected_formula` expresses failure mass through the squared norm of the
unitary difference. `nearby_unitary_difference_sq` bounds this quantity by four on normalized
inputs.

## Main statements

* `lemma2CircuitCorrected_fig3`: identifies the corrected circuit with the Figure 3
  construction.
* `lemma2OutputCorrected_formula`: computes the success and failure fibers.
* `lemma2FailureProbCorrected_formula`: gives the exact failure-mass formula.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false

open Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel

open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.CoherentSim.ResetDiscard

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.LCUDeferred
open Matrix
open scoped Classical Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Identifies a single Boolean ancilla together with a system index with a `Fin 2` ancilla and
the same system index. -/
def oneLCUBitEquiv : ((Fin 1→Bool)×I) ≃ (Fin 2×I) where
  toFun p := (boolEquivFin2 (p.1 0),p.2)
  invFun p := ((fun _=>boolEquivFin2.symm p.1),p.2)
  left_inv := by
    rintro ⟨z,x⟩
    change ((fun _=>boolEquivFin2.symm (boolEquivFin2 (z 0))),x)=(z,x)
    apply Prod.ext
    · funext j
      have hj : j=0 := Subsingleton.elim _ _
      subst j
      simp
    · rfl
  right_inv := by rintro ⟨b,x⟩; simp

omit [Fintype I] in

/-- For one ancilla, the corrected rotation is the relabeled tensor product of `V` with the
system identity. -/
private theorem oneBit_rot_eq (V : Matrix (Fin 2) (Fin 2) ℂ) :
    rotGateCorrected (I := I) 1 0 V = relabelGate (oneLCUBitEquiv (I := I)).symm (TensorGate V 1) := by
  letI : IsEmpty {j : Fin 1 // j≠0} := ⟨by rintro ⟨j,hj⟩; exact hj (Subsingleton.elim _ _)⟩
  ext ⟨z,x⟩ ⟨w,y⟩
  have hr : (fun j : {j : Fin 1 // j≠0} => z j)=(fun j : {j : Fin 1 // j≠0} => w j) :=
    Subsingleton.elim _ _
  change V (boolEquivFin2 (z 0)) (boolEquivFin2 (w 0))*
    (if ((fun j : {j : Fin 1 // j≠0}=>z j),x)=((fun j : {j : Fin 1 // j≠0}=>w j),y) then 1 else 0) =
    V (boolEquivFin2 (z 0)) (boolEquivFin2 (w 0))*(if x=y then 1 else 0)
  simp only [Prod.mk.injEq,hr,true_and]

omit [Fintype I] [DecidableEq I] in

/-- For one ancilla, the corrected control of lifted system matrices is the relabeled selection
matrix for `Ua` and `Ub`. -/
private theorem oneBit_ctrl_eq (Ua Ub : Matrix I I ℂ) :
    ctrlGateCorrected 1 0 (liftSys 1 Ua) (liftSys 1 Ub) =
      relabelGate (oneLCUBitEquiv (I := I)).symm (Select (fun b : Fin 2=>if b=0 then Ua else Ub)) := by
  ext ⟨z,x⟩ ⟨w,y⟩
  have he : z=w ↔ z 0=w 0 := by
    constructor
    · intro h; rw [h]
    · intro h; funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; exact h
  cases hz : z 0 <;> cases hw : w 0 <;>
    simp [ctrlGateCorrected,liftSys,relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,
      oneLCUBitEquiv,Select,boolEquivFin2,he,hz,hw]

/-- The corrected two-unitary circuit equals the relabeled Figure 3 circuit with preparation
`vKappaSource κ` and its adjoint as unpreparation [ChildsWiebe2012]. -/
theorem lemma2CircuitCorrected_fig3 (κ : ℝ) (Ua Ub : Matrix I I ℂ) :
    lemma2CircuitCorrected κ Ua Ub = relabelGate (oneLCUBitEquiv (I := I)).symm
      (Fig3Circuit (fun b : Fin 2=>if b=0 then Ua else Ub) (vKappaSource κ) (vKappaSource κ)ᴴ) := by
  simp only [lemma2CircuitCorrected,lcuLevelGateCorrected,oneBit_rot_eq,oneBit_ctrl_eq,
    Fig3Circuit,Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul]

/-- The source-convention preparation matrix `vKappaSource κ` is unitary when `κ` is
nonnegative. -/
theorem vKappaSource_unitary (κ : ℝ) (hκ : 0≤κ) :
    vKappaSource κ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hp : 0<κ+1 := by linarith
  have ha : (Real.sqrt (κ/(κ+1)))^2=κ/(κ+1) := Real.sq_sqrt (div_nonneg hκ hp.le)
  have hb : (Real.sqrt (κ+1))^2=κ+1 := Real.sq_sqrt hp.le
  have hs : Real.sqrt (κ+1)≠0 := by positivity
  have he : (Real.sqrt (κ/(κ+1)))^2+(Real.sqrt (κ+1))⁻¹^2=1 := by
    rw [ha,inv_pow,hb]
    field_simp
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply,vKappaSource]
  all_goals
    have hc := congrArg Complex.ofReal he
    push_cast at hc
    ring_nf at hc ⊢
    all_goals exact hc

omit [Fintype I] [DecidableEq I] in

/-- The constant false one-bit ancilla input is the relabeling of the `Fin 2` zero-ancilla
input. -/
private theorem oneBit_input (ψ : QState I) :
    TensorState (Ket (fun _=>false)) ψ =
      relabelState (oneLCUBitEquiv (I := I)).symm (TensorState (Ket (0 : Fin 2)) ψ) := by
  ext ⟨z,x⟩
  have he : z=(fun _=>false) ↔ z 0=false := by
    constructor
    · intro h; rw [h]
    · intro h; funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; exact h
  cases hz : z 0 <;> simp [TensorState,Ket,relabelState,oneLCUBitEquiv,boolEquivFin2,he,hz]

/-- Each corrected output fiber is the sum of the two selected system outputs weighted by the
corresponding preparation and adjoint entries. -/
theorem lemma2OutputCorrected_branches (κ : ℝ) (Ua Ub : Matrix I I ℂ) (ψ : QState I)
    (b : Bool) (x : I) :
    lemma2OutputCorrected κ Ua Ub ψ (fun _=>b,x) =
      ∑ j : Fin 2,(vKappaSource κ)ᴴ (boolEquivFin2 b) j * vKappaSource κ j 0 *
        ((if j=0 then Ua else Ub)*ᵥψ) x := by
  unfold lemma2OutputCorrected
  rw [lemma2CircuitCorrected_fig3,oneBit_input,applyGate_relabelGate]
  exact fig3Fiber _ _ _ _ _ _ _

/-- For nonnegative `κ`, the false-ancilla fiber applies `(κ * Ua + Ub) / (κ + 1)`, and the
true-ancilla fiber applies `sqrt κ / (κ + 1)` times `Ub - Ua`. These are the corrected Lemma
2 fibers of [ChildsWiebe2012]. -/
theorem lemma2OutputCorrected_formula (κ : ℝ) (hκ : 0≤κ) (Ua Ub : Matrix I I ℂ) (ψ : QState I) :
    (∀ x : I, lemma2OutputCorrected κ Ua Ub ψ (fun _=>false,x) =
      ((((κ:ℂ)/(κ+1)) • Ua+((1:ℂ)/(κ+1)) • Ub)*ᵥψ) x) ∧
    (∀ x : I, lemma2OutputCorrected κ Ua Ub ψ (fun _=>true,x) =
      (((((Real.sqrt κ/(κ+1):ℝ):ℂ)) • (Ub-Ua))*ᵥψ) x) := by
  have hp : 0<κ+1 := by linarith
  have hs : Real.sqrt (κ+1)≠0 := by positivity
  have ha := Real.sq_sqrt (div_nonneg hκ hp.le)
  have hb := Real.sq_sqrt hp.le
  have haC : (Real.sqrt (κ/(κ+1)):ℂ)^2=(κ:ℂ)/(κ+1) := by exact_mod_cast ha
  have hbC : (Real.sqrt (κ+1):ℂ)⁻¹^2=(1:ℂ)/(κ+1) := by
    have hh : (Real.sqrt (κ+1))⁻¹^2=(1:ℝ)/(κ+1) := by rw [inv_pow,hb,one_div]
    exact_mod_cast hh
  have hab : Real.sqrt (κ/(κ+1))*(Real.sqrt (κ+1))⁻¹=Real.sqrt κ/(κ+1) := by
    rw [Real.sqrt_div hκ]
    field_simp [hs]
    linear_combination -(Real.sqrt κ)*hb
  have habC : (Real.sqrt (κ/(κ+1)):ℂ)*(Real.sqrt (κ+1):ℂ)⁻¹=((Real.sqrt κ/(κ+1):ℝ):ℂ) := by
    exact_mod_cast hab
  push_cast at habC
  constructor
  · intro x
    rw [lemma2OutputCorrected_branches]
    simp [vKappaSource,Matrix.conjTranspose_apply,Fin.sum_univ_two,boolEquivFin2,
      Matrix.add_mulVec,Matrix.smul_mulVec]
    linear_combination ((Ua*ᵥψ) x)*haC+((Ub*ᵥψ) x)*hbC
  · intro x
    rw [lemma2OutputCorrected_branches]
    simp [vKappaSource,Matrix.conjTranspose_apply,Fin.sum_univ_two,boolEquivFin2,
      Matrix.sub_mulVec,Matrix.smul_mulVec]
    linear_combination (((Ub*ᵥψ) x)-((Ua*ᵥψ) x))*habC

/-- For nonnegative `κ`, the corrected failure mass equals `κ / (κ + 1) ^ 2` times the sum of
squared coordinate norms of `(Ua - Ub) *ᵥ ψ`. -/
theorem lemma2FailureProbCorrected_formula (κ : ℝ) (hκ : 0≤κ)
    (Ua Ub : Matrix I I ℂ) (ψ : QState I) :
    lemma2FailureProbCorrected κ Ua Ub ψ =
      κ/(κ+1)^2*(∑ x : I,‖((Ua-Ub)*ᵥψ) x‖^2) := by
  unfold lemma2FailureProbCorrected MeasureProb
  rw [Finset.sum_product]
  simp only [lemma2FailSet,Finset.sum_singleton]
  have hc : (Real.sqrt κ/(κ+1))^2=κ/(κ+1)^2 := by
    rw [div_pow,Real.sq_sqrt hκ]
  have he (x : I) : BornProb (lemma2OutputCorrected κ Ua Ub ψ) (fun _=>true,x) =
      κ/(κ+1)^2*‖((Ua-Ub)*ᵥψ) x‖^2 := by
    rw [BornProb,(lemma2OutputCorrected_formula κ hκ Ua Ub ψ).2]
    simp only [Matrix.smul_mulVec,Pi.smul_apply,smul_eq_mul,norm_mul,mul_pow,
      Complex.norm_real,Real.norm_eq_abs,sq_abs,hc]
    rw [Matrix.sub_mulVec,Matrix.sub_mulVec,Pi.sub_apply,Pi.sub_apply,norm_sub_rev]
  simp_rw [he]
  rw [Finset.mul_sum]

/-- The sum of squared coordinate norms of the difference of two unitary outputs is at most four
for a normalized input. -/
theorem nearby_unitary_difference_sq (Ua Ub : Matrix I I ℂ)
    (hUa : Ua∈Matrix.unitaryGroup I ℂ) (hUb : Ub∈Matrix.unitaryGroup I ℂ)
    (ψ : QState I) (hψ : Normalized ψ) :
    (∑ x : I,‖((Ua-Ub)*ᵥψ) x‖^2)≤4 := by
  have ha : ‖stateVector (Ua*ᵥψ)‖=1 :=
    (normalized_iff_stateVector_norm _).mp (normalized_applyGate hUa hψ)
  have hb : ‖stateVector (Ub*ᵥψ)‖=1 :=
    (normalized_iff_stateVector_norm _).mp (normalized_applyGate hUb hψ)
  have hd : ‖stateVector ((Ua-Ub)*ᵥψ)‖≤2 := by
    rw [Matrix.sub_mulVec]
    change ‖stateVector (Ua*ᵥψ)-stateVector (Ub*ᵥψ)‖≤2
    calc _≤‖stateVector (Ua*ᵥψ)‖+‖stateVector (Ub*ᵥψ)‖ := norm_sub_le _ _
      _=2 := by rw [ha,hb]; norm_num
  change MeasureProb ((Ua-Ub)*ᵥψ) Finset.univ≤4
  rw [← stateVector_norm_sq]
  nlinarith [norm_nonneg (stateVector ((Ua-Ub)*ᵥψ))]

end Qatlib.Papers.HamLCUSim12.LCUDeferred
