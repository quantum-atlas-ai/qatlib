/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle

/-!
# Workspace cleanup for the inner term preparation

This module proves basis-state identities for the selected computations used by the inner Monte
Carlo preparation of [KanekoEtAl2020]. `body_cleanup_basis` shows that computing a term,
rotating the flag, and reversing the computation restores the data workspace while retaining the
term-dependent flag state.

## Main statements

* `select_basis`: describes the action of a selected matrix on a basis state.
* `body_cleanup_basis`: restores the workspace after the term-dependent rotation.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedBorn
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
open Qatlib.Papers.MonteCarloInt20.MainResults.FlagRotation
open Qatlib.Papers.MonteCarloInt20.MainResults.TermCode

namespace Qatlib.Papers.MonteCarloInt20.MainResults.Cleanup

/-- On a basis state `(i, w)`, the selected matrix leaves the index `i` fixed and applies `U i`
to `w`. -/
theorem select_basis {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (U : I → Matrix W W ℂ) (i : I) (w : W) :
    ApplyGate (select U) (Ket (i,w))=TensorState (Ket i) (ApplyGate (U i) (Ket w)) := by
  funext p
  obtain ⟨k,v⟩ := p
  rw [apply_ket_column]
  simp only [TensorState]
  rw [apply_ket_column]
  by_cases hk : k=i
  · subst k
    simp [select,Qatlib.Foundations.PureStateMath.Ket]
  · simp [select,Qatlib.Foundations.PureStateMath.Ket,hk]

/-- For positive coordinate width, term computation followed by flag rotation and uncomputation
restores the indexed data seed and leaves the flag in the state determined by the decoded
term value [KanekoEtAl2020]. -/
theorem body_cleanup_basis {n s d p : ℕ} (hd : 0<d)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (termCode : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (j : Reg s) (i : Reg d) :
    let C := select (dataCompute a c seed termCode j)
    let f := fun v : Reg d × Data n (s+d+1) p => decodeCode p v.2.2
    ApplyGate (TensorGate C.conjTranspose 1*Qatlib.Concepts.AmplitudeCore.PayoffMedian.payoffRotation f*TensorGate C 1)
      (Ket ((i,dataSeed n s d p seed),false))=
      TensorState (Ket (i,dataSeed n s d p seed))
        (flagState (((termCode j i (residue a c seed j i)).val:ℝ)/(2:ℝ)^p)) := by
  (try dsimp only)
  have hb : ApplyGate (select (dataCompute a c seed termCode j)) (Ket (i,dataSeed n s d p seed))=
      Ket (i,computedData a c seed termCode j i) := by
    rw [select_basis,dataCompute_basis hd,tensorState_ket_ket]
  have h := compute_rotate_uncompute_basis (select (dataCompute a c seed termCode j))
    (select_unitary _ (dataCompute_unitary a c seed termCode j))
    (i,dataSeed n s d p seed) (i,computedData a c seed termCode j i) hb
    (fun v : Reg d × Data n (s+d+1) p => decodeCode p v.2.2)
  simpa only [computedData,decodeCode_codeBits] using! h

end Qatlib.Papers.MonteCarloInt20.MainResults.Cleanup
