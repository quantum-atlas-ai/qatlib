/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.LabelProgress.PureState
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Concepts.AdversaryBounds.LabelProgress
variable {I A : Type*} [Fintype I] [Fintype A]

def inputRelabel (e : Equiv.Perm I) : (I → ℂ) ≃ₗ[ℂ] (I → ℂ) :=
  LinearEquiv.piCongrLeft' ℂ (fun _ : I => ℂ) e
omit [Fintype I] in

theorem inputRelabel_apply (e : Equiv.Perm I) (v : I → ℂ) (i : I) :
    inputRelabel e v i=v (e.symm i) := rfl
omit [Fintype I] in

theorem reducedInput_reindex (C : Matrix I A ℂ) (e : Equiv.Perm I) (i j : I) :
    reducedInput (fun i a => C (e.symm i) a) i j=reducedInput C (e.symm i) (e.symm j) := rfl

theorem invariant_of_entries (Q : Matrix I I ℂ) (e : Equiv.Perm I)
    (he : ∀ i j, Q (e i) (e j)=Q i j) :
    Q.mulVecLin.comp (inputRelabel e).toLinearMap=(inputRelabel e).toLinearMap.comp Q.mulVecLin := by
  apply LinearMap.ext
  intro v
  funext i
  change (∑ j, Q i j*v (e.symm j))=∑ j, Q (e.symm i) j*v j
  apply Fintype.sum_equiv e.symm
  intro j
  have h := he (e.symm i) (e.symm j)
  simp only [e.apply_symm_apply] at h
  rw [h]

theorem invariant_of_equal_rows (C : Matrix I A ℂ) (e : Equiv.Perm I)
    (he : ∀ i, C (e i)=C i) :
    (reducedInput C).mulVecLin.comp (inputRelabel e).toLinearMap=
      (inputRelabel e).toLinearMap.comp (reducedInput C).mulVecLin := by
  apply invariant_of_entries
  intro i j
  simp only [reducedInput_entry,he]
end Qatlib.Concepts.AdversaryBounds.LabelProgress
