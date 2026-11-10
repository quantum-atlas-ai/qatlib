/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemidirectHSP05.MainResults.MatrixSumCount.AppendixB
import Qatlib.Papers.SemidirectHSP05.MainResults.SuccessProbability.Lemma2
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP05.MainResults

open scoped Classical BigOperators

theorem theorem6_success_ge_sixteenth (p r : ℕ) (hp : p.Prime) [NeZero p] :
    (1 / 16 : ℝ) ≤
      SuccessProbability.pgmSuccess p r
        (fun x w => (MatrixSumCount.solutions p r x w).card) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩

  have hcount : ∀ x : Fin r → Fin r → ZMod p,
      ∑ w : Fin r → ZMod p, (MatrixSumCount.solutions p r x w).card = p ^ r := by
    intro x
    rw [MatrixSumCount.solutions_sum_card, Fintype.card_fun, Fintype.card_fin, ZMod.card]

  have hcardprod : (Fintype.card ((Fin r → Fin r → ZMod p) × (Fin r → ZMod p)) : ℝ)
      = (Fintype.card (Fin r → ZMod p) : ℝ) ^ r *
          (Fintype.card (Fin r → ZMod p) : ℝ) := by
    rw [Fintype.card_prod, Nat.cast_mul, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

  have hsum_eq :
      (∑ x : Fin r → Fin r → ZMod p, ∑ w : Fin r → ZMod p,
          (if ((MatrixSumCount.solutions p r x w).card = 1 ∨
              (MatrixSumCount.solutions p r x w).card = 2) then (1 : ℝ) else 0))
        = ((Finset.univ.filter (fun xw : (Fin r → Fin r → ZMod p) × (Fin r → ZMod p) =>
            (MatrixSumCount.solutions p r xw.1 xw.2).card = 1 ∨
              (MatrixSumCount.solutions p r xw.1 xw.2).card = 2)).card : ℝ) := by
    rw [← Fintype.sum_prod_type'
      (fun x w => if ((MatrixSumCount.solutions p r x w).card = 1 ∨
          (MatrixSumCount.solutions p r x w).card = 2) then (1 : ℝ) else 0)]
    rw [Finset.sum_boole]

  have hmany :
      (1 / 4 : ℝ) * ((Fintype.card (Fin r → ZMod p) : ℝ) ^ r *
          (Fintype.card (Fin r → ZMod p) : ℝ)) ≤
        ∑ x : Fin r → Fin r → ZMod p, ∑ w : Fin r → ZMod p,
          (if ((MatrixSumCount.solutions p r x w).card = 1 ∨
              (MatrixSumCount.solutions p r x w).card = 2) then (1 : ℝ) else 0) := by
    rw [hsum_eq, ← hcardprod]
    linarith [MatrixSumCount.lemma5 (p := p) (r := r)]
  exact SuccessProbability.success_ge_sixteenth p r hp
    (fun x w => (MatrixSumCount.solutions p r x w).card) hcount hmany

end Qatlib.Papers.SemidirectHSP05.MainResults
