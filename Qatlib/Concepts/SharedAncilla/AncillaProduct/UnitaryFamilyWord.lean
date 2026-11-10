/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SharedAncilla.AncillaProduct.SharedAncillaUnitaryProduct
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Concepts.SharedAncilla.AncillaProduct
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator

def unitaryFamilyQueries {m : ℕ} (cs : List (Fin m)) : ℕ := cs.length

theorem unitaryFamilyEvaluate_append {H : Type} [Fintype H] [DecidableEq H] {m : ℕ}
    (U : Fin m → Matrix H H ℂ) (cs ds : List (Fin m)) :
    unitaryFamilyEvaluate U (cs++ds) = unitaryFamilyEvaluate U cs * unitaryFamilyEvaluate U ds := by
  induction cs with
  | nil => simp [unitaryFamilyEvaluate]
  | cons i cs ih => simp [unitaryFamilyEvaluate,ih,Matrix.mul_assoc]

theorem unitaryFamilyEvaluate_reverse_adjoint {H : Type} [Fintype H] [DecidableEq H] {m : ℕ}
    (U : Fin m → Matrix H H ℂ) (cs : List (Fin m)) :
    unitaryFamilyEvaluate (fun i => (U i)ᴴ) cs.reverse = (unitaryFamilyEvaluate U cs)ᴴ := by
  induction cs with
  | nil => simp [unitaryFamilyEvaluate]
  | cons i cs ih => simp [List.reverse_cons,unitaryFamilyEvaluate_append,unitaryFamilyEvaluate,
      ih,Matrix.conjTranspose_mul]

theorem shared_ancilla_word_common_error_and_paid_inverse :
∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
 (m : ℕ) (A : Fin m→Matrix I I ℂ) (U : Fin m→Matrix H H ℂ) (F : Matrix H I ℂ) (ε : ℝ),
 IsIsometry F → (∀i,A i∈Matrix.unitaryGroup I ℂ ∧ BlockEncoding (A i) (U i) F F 1 ε) →
 BlockEncoding (unitaryFamilyEvaluate A (unitaryFamilyWord m))
  (unitaryFamilyEvaluate U (unitaryFamilyWord m)) F F 1 ((m:ℝ)^2*ε) ∧
 unitaryFamilyQueries (unitaryFamilyWord m)=m ∧
 unitaryFamilyQueries ((unitaryFamilyWord m).reverse)=m ∧
 unitaryFamilyEvaluate (fun i=>(U i)ᴴ) ((unitaryFamilyWord m).reverse)=
  (unitaryFamilyEvaluate U (unitaryFamilyWord m))ᴴ := by
  intro H I _ _ _ _ m A U F ε hF hs
  have h := shared_ancilla_heterogeneous_word_encoding H I m A U F (fun _ => ε) hF hs
  have he : sharedAncillaWordError (fun _ : Fin m => ε) = (m:ℝ)^2*ε := by
    by_cases hm : m = 0
    · subst m; simp [sharedAncillaWordError]
    · have hε : 0 ≤ ε := (hs ⟨0,Nat.pos_of_ne_zero hm⟩).2.error_nonneg
      simp [sharedAncillaWordError,mul_pow,Real.sq_sqrt hε]
  refine ⟨by simpa only [he] using h,?_,?_,unitaryFamilyEvaluate_reverse_adjoint U _⟩
  · simp [unitaryFamilyQueries,unitaryFamilyWord]
  · simp [unitaryFamilyQueries,unitaryFamilyWord]

end Qatlib.Concepts.SharedAncilla.AncillaProduct
