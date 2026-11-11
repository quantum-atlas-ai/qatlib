/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.ModelSemantics.AlphabetWordSemanticsStat
import Qatlib.Concepts.HspRecovery.RecordExtract.ExecutionSemantics
import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Unitary semantics of alphabet query words

Proves that the padded alphabet shift and every legal word evaluated at a unitary oracle are
unitary. It also checks that clean tagged embeddings preserve normalization.

These results establish the discrete alphabet query semantics underlying the state conversion
model in [LeeEtAl2011].

## Main statements

* `sourceAlphabetOracle_unitary`: the padded alphabet oracle is unitary.
* `sourceWordMatrix_unitary`: legal words preserve unitarity.
* `alphabetWordSemantics`: proves the complete semantic specification.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.GramQueryCore.ModelSemantics
open Matrix
open scoped Classical BigOperators

/-- The padded alphabet shift is injective because addition of the input symbol is cancellable. -/
theorem sourceAlphabetShift_injective {X S : Type} {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    Function.Injective (fun p : ((Fin (n+1) × Fin (q+1)) × S) =>
      ((p.1.1,p.1.2+sourcePaddedSymbol input x p.1.1),p.2)) := by
  intro p t he
  have ha := congrArg (fun u => u.1.1) he
  have hb := congrArg (fun u => u.1.2) he
  have hs := congrArg Prod.snd he
  (try dsimp only at ha hb hs)
  rw [ha] at hb
  exact Prod.ext (Prod.ext ha (add_right_cancel hb)) hs

/-- The padded alphabet oracle is a unitary permutation matrix. -/
theorem sourceAlphabetOracle_unitary {X S : Type} [Fintype S] [DecidableEq S]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (x : X) :
    sourceAlphabetOracle (W:=S) input x ∈ Matrix.unitaryGroup _ ℂ :=
  permMatrix_unitary_of_injective (sourceAlphabetShift_injective input x)

/-- A legal source word evaluated at a unitary oracle has a unitary matrix. -/
theorem sourceWordMatrix_unitary {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (hO : O ∈ Matrix.unitaryGroup S ℂ)
    (C : SourceWord S) (hC : sourceWordLegal C) :
    sourceWordMatrix O C ∈ Matrix.unitaryGroup S ℂ := by
  have hOadj : Oᴴ ∈ Matrix.unitaryGroup S ℂ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hO
  induction C with
  | nil => simp [sourceWordMatrix]
  | cons s C ih =>
    have ht : sourceWordLegal C := fun t ht => hC t (List.mem_cons_of_mem s ht)
    have hs := hC s List.mem_cons_self
    simp only [sourceWordMatrix,List.map_cons,List.reverse_cons,List.prod_append,
      List.prod_cons,List.prod_nil,mul_one]
    apply (Matrix.unitaryGroup S ℂ).mul_mem (ih ht)
    cases s with
    | inl U => exact hs
    | inr adj => cases adj <;> simp_all

/-- The clean tagged source embedding of a normalized state is normalized. -/
theorem sourceClean_normalized {H : Type} [Fintype H] [DecidableEq H]
    (n q r : ℕ) (hr : 0<r) (tag : Bool) (ψ : QState H) (hψ : Normalized ψ) :
    Normalized (sourceClean n q r hr tag ψ) :=
  normalized_tensorState (normalized_ket _) (normalized_tensorState
    (normalized_tensorState (normalized_ket _) hψ) (normalized_ket _))

/-- Proves the unitarity and clean-state normalization properties of the alphabet word model
used in [LeeEtAl2011]. -/
theorem alphabetWordSemantics : AlphabetWordSemantics := by
  intro X S _ _ n q input x
  exact ⟨sourceAlphabetOracle_unitary input x,
    fun C hC => sourceWordMatrix_unitary _ (sourceAlphabetOracle_unitary input x) C hC,
    fun H _ _ r hr tag ψ hψ => sourceClean_normalized n q r hr tag ψ hψ⟩

end Qatlib.Concepts.GramQueryCore.ModelSemantics
