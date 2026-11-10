/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessNativeOutput
import Qatlib.Concepts.TensorRegisters.RegisterModel.QmaCompletenessLocalEnergy
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib Matrix
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.TensorRegisters.RegisterModel
open scoped Classical
set_option autoImplicit false
noncomputable section

theorem value_fill {N : ℕ} (b : ℕ) (t : IntegerLocalTerm N)
    (u v : Reg t.support.card) :
    value b t (fill t.support u) (fill t.support v)=dyadicValue b (t.re u v) (t.im u v) := by
  simp only [value,partitionLift_apply,mask_fill,outside_fill,ite_true]

theorem local_table_lower {m n : ℕ} (b : ℕ) (t : IntegerLocalTerm (m+n))
    (H : Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ)
    (ht : t.support.card ≤ 5)
    (hv : value b t=Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm H)
    (hH : ∀p q,‖H p q‖ ≤ 1) (ψ : QState (Clock m×Reg n)) :
    -(32:ℝ)*mass ψ ≤ energy H ψ := by
  have hn : ∀u v : Reg t.support.card,‖dyadicValue b (t.re u v) (t.im u v)‖ ≤ 1 := by
    intro u v
    have he:=congrArg (fun M : Matrix (Reg (m+n)) (Reg (m+n)) ℂ =>
      M (fill t.support u) (fill t.support v)) hv

    rw [value_fill] at he
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm] at he
    rw [he]
    exact hH _ _
  have hl:=partitionLift_five_qubit_energy_lower t.support.card ht (split t.support)
    (fun u v => dyadicValue b (t.re u v) (t.im u v)) hn
    (fun x : Reg (m+n) => ψ (flattenEquiv m n x))
  change -(32:ℝ)*mass (fun x => ψ (flattenEquiv m n x)) ≤
    energy (value b t) (fun x => ψ (flattenEquiv m n x)) at hl
  rw [hv] at hl
  have he:=energy_reindex (flattenEquiv m n).symm H ψ
  have hm:=mass_reindex (flattenEquiv m n).symm ψ
  change energy (Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm H)
    (fun x => ψ (flattenEquiv m n x))=energy H ψ at he
  change mass (fun x => ψ (flattenEquiv m n x))=mass ψ at hm
  rw [he,hm] at hl
  exact hl

end
end Qatlib.Concepts.QueryComplexity.DegreeMethod
