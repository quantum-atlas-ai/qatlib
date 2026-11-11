/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedStatistics

/-!
# Zero ancilla fibers of corrected LCU levels

This module isolates a selected ancilla bit and relates a corrected LCU level to the Figure 3
circuit of [ChildsWiebe2012]. `splitLCUBranch` restricts each branch to a fixed value of that
bit, and `lcuLevelGateCorrected_fig3` identifies the full circuit after relabeling the register.

The resulting zero ancilla amplitude is a sum over the two branch fibers. For nonnegative `κ`,
the source rotation contributes weights `κ / (κ + 1)` and `1 / (κ + 1)`;
`lcuLevelGateCorrected_zero_corner` combines these when the second branch is invariant under the
simultaneous control-bit flip.

## Main statements

* `ctrlGateCorrected_split` and `lcuLevelGateCorrected_fig3` give the relabeled controlled and
  Figure 3 descriptions.
- `splitLCU_zero_input` expresses the all-zero input in the split register.
- `vKappaSource_zero_coeff` and `vKappaSource_one_coeff` compute the two success weights.
* `lcuLevelGateCorrected_zero_corner` gives the weighted sum of branch amplitudes on the
  all-zero fiber.

## References

- [Childs and Wiebe, 2012][ChildsWiebe2012], Lemma 2 and Figure 3.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel

open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.CoherentSim.ResetDiscard

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.LCUDeferred
open Matrix
open scoped Classical Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Restricts `Cx` to the control-zero block and `Cy` to the control-one block after splitting
off ancilla bit `i`. -/
def splitLCUBranch {k : ℕ} (i : Fin k)
    (Cx Cy : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) (b : Fin 2) :
    Matrix (({j : Fin k //j≠i}→Bool)×I) (({j : Fin k //j≠i}→Bool)×I) ℂ :=
  (if b=0 then Cx else Cy).submatrix
    (fun p=> (splitLCUBit (I := I) i).symm (b,p))
    (fun p=> (splitLCUBit (I := I) i).symm (b,p))

omit [Fintype I] [DecidableEq I] in

/-- The corrected controlled gate is the relabeling of `Select` applied to the two restricted
branches obtained by splitting off its control bit. -/
theorem ctrlGateCorrected_split {k : ℕ} (i : Fin k)
    (Cx Cy : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) :
    ctrlGateCorrected k i Cx Cy=relabelGate (splitLCUBit (I := I) i).symm
      (Select (splitLCUBranch i Cx Cy)) := by
  let e := splitLCUBit (I := I) i
  ext p q
  change (if p.1 i=q.1 i then (if p.1 i then Cy else Cx) p q else 0)=
    (if (e p).1=(e q).1 then splitLCUBranch i Cx Cy (e q).1 (e p).2 (e q).2 else 0)
  have he : (e p).1=(e q).1 ↔ p.1 i=q.1 i := boolEquivFin2.injective.eq_iff
  by_cases h : p.1 i=q.1 i
  · rw [if_pos h,if_pos (he.mpr h)]
    rw [← he.mpr h]
    change (if p.1 i then Cy else Cx) p q =
      (if (e p).1=0 then Cx else Cy) (e.symm ((e p).1,(e p).2)) (e.symm ((e p).1,(e q).2))
    have hp : e.symm ((e p).1,(e p).2)=p := e.symm_apply_apply p
    have hq : e.symm ((e p).1,(e q).2)=q := by rw [he.mpr h];exact e.symm_apply_apply q
    rw [hp,hq]
    change (if p.1 i then Cy else Cx) p q=(if boolEquivFin2 (p.1 i)=0 then Cx else Cy) p q
    cases hb : p.1 i <;> simp [boolEquivFin2]
  · rw [if_neg h,if_neg (fun hh=>h (he.mp hh))]

/-- A corrected LCU level equals the relabeled Figure 3 circuit with the restricted branches,
preparation matrix `V`, and final matrix `Vᴴ`, in the notation of [ChildsWiebe2012]. -/
theorem lcuLevelGateCorrected_fig3 {k : ℕ} (i : Fin k) (V : Matrix (Fin 2) (Fin 2) ℂ)
    (Cx Cy : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) :
    lcuLevelGateCorrected k i V Cx Cy = relabelGate (splitLCUBit (I := I) i).symm
      (Fig3Circuit (splitLCUBranch i Cx Cy) V Vᴴ) := by
  simp only [lcuLevelGateCorrected,rotGateCorrected,ctrlGateCorrected_split,Fig3Circuit,
    Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul]

omit [Fintype I] [DecidableEq I] in

/-- Splitting off any ancilla bit rewrites the all-zero ancilla input as a zero control qubit
tensored with the remaining zero ancillas and `ψ`. -/
theorem splitLCU_zero_input {k : ℕ} (i : Fin k) (ψ : QState I) :
    TensorState (Ket (fun _ : Fin k=>false)) ψ = relabelState (splitLCUBit (I := I) i).symm
      (TensorState (Ket (0 : Fin 2)) (TensorState (Ket (fun _ : {j : Fin k //j≠i}=>false)) ψ)) := by
  ext p
  change ((if p.1=(fun _=>false) then 1 else 0)*ψ p.2)=
    (if boolEquivFin2 (p.1 i)=0 then 1 else 0)*
      ((if (fun j : {j : Fin k //j≠i}=>p.1 j)=(fun _=>false) then 1 else 0)*ψ p.2)
  have he : p.1=(fun _=>false) ↔
      p.1 i=false ∧ (fun j : {j : Fin k //j≠i}=>p.1 j)=(fun _=>false) := by
    constructor
    · intro h; simp [h]
    · rintro ⟨hi,hr⟩
      funext j
      by_cases hj : j=i
      · subst j;exact hi
      · exact congrFun hr ⟨j,hj⟩
  cases hb : p.1 i <;> by_cases hr : (fun j : {j : Fin k //j≠i}=>p.1 j)=(fun _=>false) <;>
    simp [he,hb,hr,boolEquivFin2]
omit [Fintype I] [DecidableEq I] in

/-- Rejoining a zero control bit with the remaining all-zero ancillas gives the full all-zero
ancilla string and the same system index. -/
theorem splitLCUBit_zero_inv {k : ℕ} (i : Fin k) (x : I) :
    (splitLCUBit (I := I) i).symm (0,((fun _ : {j : Fin k //j≠i}=>false),x))=
      ((fun _ : Fin k=>false),x) := by
  have h : splitLCUBit (I := I) i ((fun _ : Fin k=>false),x)=
      (0,((fun _ : {j : Fin k //j≠i}=>false),x)) := rfl
  rw [← h,Equiv.symm_apply_apply]

omit [Fintype I] [DecidableEq I] in

/-- Rejoining a one control bit with the remaining all-zero ancillas gives the string obtained
by flipping only that bit in the full zero string. -/
theorem splitLCUBit_one_inv {k : ℕ} (i : Fin k) (x : I) :
    (splitLCUBit (I := I) i).symm (1,((fun _ : {j : Fin k //j≠i}=>false),x))=
      flipLCUBit i ((fun _ : Fin k=>false),x) := by
  apply (splitLCUBit (I := I) i).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · change (1 : Fin 2)=boolEquivFin2 (Function.update (fun _ : Fin k=>false) i true i)
    simp [boolEquivFin2]
  · apply Prod.ext
    · funext j
      change false=Function.update (fun _ : Fin k=>false) i true j
      simp [j.property]
    · rfl

omit [DecidableEq I] in

/-- For an all-zero ancilla input, the output amplitude on the all-zero fiber is the
system-index sum of the corresponding zero-to-zero matrix entries times `ψ`. -/
theorem mask_zero_corner {k : ℕ}
    (A : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) (ψ : QState I) (x : I) :
    (A*ᵥTensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x)=
      ∑ y : I,A (fun _=>false,x) (fun _=>false,y)*ψ y := by
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,TensorState,Ket]

omit [DecidableEq I] in

/-- Evaluates a restricted branch on the remaining all-zero ancillas by summing the original
branch entries with the selected control value reinserted. -/
theorem splitLCUBranch_corner {k : ℕ} (i : Fin k)
    (Cx Cy : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ)
    (b : Fin 2) (ψ : QState I) (x : I) :
    (splitLCUBranch i Cx Cy b*ᵥTensorState (Ket (fun _ : {j : Fin k //j≠i}=>false)) ψ)
      (fun _=>false,x) = ∑ y : I,
        (if b=0 then Cx else Cy)
          ((splitLCUBit (I := I) i).symm (b,((fun _=>false),x)))
          ((splitLCUBit (I := I) i).symm (b,((fun _=>false),y)))*ψ y := by
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,TensorState,Ket,splitLCUBranch]

/-- The zero ancilla amplitude of a corrected LCU level is the sum of the two restricted branch
amplitudes, weighted by `(vKappaSource κ)ᴴ 0 b * vKappaSource κ b 0`. -/
theorem lcuLevelGateCorrected_zero_branches {k : ℕ} (i : Fin k) (κ : ℝ)
    (Cx Cy : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ) (ψ : QState I) (x : I) :
    (lcuLevelGateCorrected k i (vKappaSource κ) Cx Cy*ᵥ
      TensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x) =
      ∑ b : Fin 2,(vKappaSource κ)ᴴ 0 b*vKappaSource κ b 0*
        ((splitLCUBranch i Cx Cy b)*ᵥ
          TensorState (Ket (fun _ : {j : Fin k //j≠i}=>false)) ψ) (fun _=>false,x) := by
  change ApplyGate (lcuLevelGateCorrected k i (vKappaSource κ) Cx Cy)
    (TensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x)=_
  rw [lcuLevelGateCorrected_fig3,splitLCU_zero_input,applyGate_relabelGate]
  exact fig3Fiber _ _ _ _ _ _ _

/-- For nonnegative `κ`, the control-zero contribution of the source rotation and its adjoint is
`κ / (κ + 1)`. -/
theorem vKappaSource_zero_coeff (κ : ℝ) (hκ : 0≤κ) :
    (vKappaSource κ)ᴴ 0 0*vKappaSource κ 0 0=(κ:ℂ)/(κ+1) := by
  have hp : 0<κ+1 := by linarith
  have hh := congrArg Complex.ofReal (Real.sq_sqrt (div_nonneg hκ hp.le))
  push_cast at hh
  simp [vKappaSource,Matrix.conjTranspose_apply]
  linear_combination hh

/-- For nonnegative `κ`, the control-one contribution of the source rotation and its adjoint is
`1 / (κ + 1)`. -/
theorem vKappaSource_one_coeff (κ : ℝ) (hκ : 0≤κ) :
    (vKappaSource κ)ᴴ 0 1*vKappaSource κ 1 0=(1:ℂ)/(κ+1) := by
  have hp : 0<κ+1 := by linarith
  have hh : (Real.sqrt (κ+1))⁻¹^2=(1:ℝ)/(κ+1) := by
    rw [inv_pow,Real.sq_sqrt hp.le,one_div]
  have hc := congrArg Complex.ofReal hh
  push_cast at hc
  simp [vKappaSource,Matrix.conjTranspose_apply]
  linear_combination hc

/-- For nonnegative `κ` and a second branch invariant under simultaneous control-bit flips, the
corrected level's zero ancilla amplitude is `κ / (κ + 1)` times the first branch amplitude
plus `1 / (κ + 1)` times the second branch amplitude. This is the weighted success-fiber
identity behind the two-term LCU construction of [ChildsWiebe2012]. -/
theorem lcuLevelGateCorrected_zero_corner {k : ℕ} (i : Fin k) (κ : ℝ) (hκ : 0≤κ)
    (Cx Cy : Matrix ((Fin k→Bool)×I) ((Fin k→Bool)×I) ℂ)
    (hy : IndependentLCUBit i Cy) (ψ : QState I) (x : I) :
    (lcuLevelGateCorrected k i (vKappaSource κ) Cx Cy*ᵥ
      TensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x) =
      ((κ:ℂ)/(κ+1))*(Cx*ᵥTensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x)+
      ((1:ℂ)/(κ+1))*(Cy*ᵥTensorState (Ket (fun _ : Fin k=>false)) ψ) (fun _=>false,x) := by
  rw [lcuLevelGateCorrected_zero_branches,Fin.sum_univ_two,vKappaSource_zero_coeff κ hκ,
    vKappaSource_one_coeff κ hκ,splitLCUBranch_corner,splitLCUBranch_corner]
  simp only [show (1 : Fin 2)≠0 by decide,if_true,if_false,splitLCUBit_zero_inv,splitLCUBit_one_inv]
  have hs : (∑ y : I,Cy (flipLCUBit i ((fun _ : Fin k=>false),x))
      (flipLCUBit i ((fun _ : Fin k=>false),y))*ψ y)=
      ∑ y : I,Cy ((fun _ : Fin k=>false),x) ((fun _ : Fin k=>false),y)*ψ y := by
    apply Finset.sum_congr rfl
    intro y _
    rw [hy ((fun _ : Fin k=>false),x) ((fun _ : Fin k=>false),y)]
  rw [hs]
  rw [mask_zero_corner,mask_zero_corner]
end Qatlib.Papers.HamLCUSim12.LCUDeferred
