/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GramQueryCore.QfiCompletion.MqfiSeparableOfCompletionStat
public import Qatlib.Concepts.GramQueryCore.QfiCompletion.MqfiCompletionTools
public import Qatlib.Concepts.MixedFidelity.FidelityMetric.SimultaneousDiagonalization

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.GramQueryCore.QfiCompletion.MqfiNPHard2026

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Qatlib.Concepts.GramQueryCore.QfiCompletion
open scoped Classical BigOperators Matrix

/-- An MQFI completion implies real separability of the associated MQFI blocks. -/
theorem mqfiSeparableOfCompletion : MqfiSeparableOfCompletion := by
  intro p r q B h
  obtain ⟨n,K,hK,hComm⟩ := h
  let J := Fin r ⊕ Fin (q+n)
  let C := fun a : Fin p => mqfiCompletion B K a
  have hHerm (a : Fin p) : (C a).IsHermitian := mqfiCompletion_isHermitian B K hK a
  obtain ⟨U,diag,_,hU,hdiag⟩ :=
      Qatlib.Concepts.MixedFidelity.FidelityMetric.exists_simultaneous_unitary_diagonalization_index C hHerm hComm
  let L := Fin (Fintype.card J)
  have hreal (a b : Fin p) (s t : Fin r) :
      mqfiBlocks B (a,s) (b,t)=∑ j : L,diag a j*diag b j*
        ((U (Sum.inl s) j).re*(U (Sum.inl t) j).re+
          (U (Sum.inl s) j).im*(U (Sum.inl t) j).im) := by
    have he : (C a*C b) (Sum.inl s) (Sum.inl t)=
        ∑ j : L,U (Sum.inl s) j*((diag a j*diag b j : ℝ) : ℂ)*star (U (Sum.inl t) j) := by
      rw [hdiag a,hdiag b]
      exact mqfi_spectral_product_entry U hU (diag a) (diag b) (Sum.inl s) (Sum.inl t)
    rw [mqfiCompletion_product_top B K a b s t] at he
    have h := congrArg Complex.re he
    simp only [Complex.ofReal_re] at h
    rw [← Complex.coe_reAddGroupHom,map_sum] at h
    simp only [Complex.coe_reAddGroupHom] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
      Complex.ofReal_re,Complex.ofReal_im]
    ring
  let m := Fintype.card (L × Bool)
  let E : Fin m ≃ L × Bool := (Fintype.equivFin (L × Bool)).symm
  let z := fun i : Fin m => fun a : Fin p => diag a (E i).1
  let w := fun i : Fin m => fun s : Fin r =>
    if (E i).2 then (U (Sum.inl s) (E i).1).im else (U (Sum.inl s) (E i).1).re
  refine ⟨m,(fun _ => 1),z,w,(fun _ => by norm_num),?_⟩
  intro x y
  rw [hreal x.1 y.1 x.2 y.2]
  simp only [one_mul]
  change _=∑ i : Fin m,(diag x.1 (E i).1*diag y.1 (E i).1)*
    ((if (E i).2 then (U (Sum.inl x.2) (E i).1).im else (U (Sum.inl x.2) (E i).1).re)*
      (if (E i).2 then (U (Sum.inl y.2) (E i).1).im else (U (Sum.inl y.2) (E i).1).re))
  rw [Equiv.sum_comp E (fun j : L × Bool => (diag x.1 j.1*diag y.1 j.1)*
    ((if j.2 then (U (Sum.inl x.2) j.1).im else (U (Sum.inl x.2) j.1).re)*
      (if j.2 then (U (Sum.inl y.2) j.1).im else (U (Sum.inl y.2) j.1).re))),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fintype.sum_bool,Bool.false_eq_true,ite_true,ite_false]
  ring
end Qatlib.Concepts.GramQueryCore.QfiCompletion
