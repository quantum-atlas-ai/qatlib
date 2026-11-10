/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Foundations.OrderPrimality.GeneratorCount
import Mathlib.Probability.Distributions.Uniform

set_option autoImplicit false
noncomputable section
open scoped Finset ENNReal
namespace Qatlib.Concepts.OrderPrimality.UniformTrial
open Qatlib.Foundations.OrderPrimality.GeneratorCount

def candidates (N : ℕ) [NeZero N] : Finset (ZMod N)ˣ := Finset.univ.erase 1

theorem candidates_card {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) :
    (candidates N).card = N-2 := by
  unfold candidates
  rw [Finset.card_erase_of_mem (Finset.mem_univ 1),Finset.card_univ,
    ZMod.card_units_eq_totient,Nat.totient_prime hp]
  omega

theorem candidates_nonempty {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) :
    (candidates N).Nonempty := by
  apply Finset.card_pos.mp
  rw [candidates_card hp hN]
  omega

theorem candidates_good_card {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) :
    ((candidates N).filter (fun a => orderOf a=N-1)).card = Nat.totient (N-1) := by
  have hs : (candidates N).filter (fun a => orderOf a=N-1) =
      Finset.univ.filter (fun a : (ZMod N)ˣ => orderOf a=N-1) := by
    ext a
    simp only [Finset.mem_filter,candidates,Finset.mem_erase,Finset.mem_univ,
      and_true,true_and]
    constructor
    · exact And.right
    · intro ho
      refine ⟨?_,ho⟩
      intro ha
      subst a
      simp only [orderOf_one] at ho
      omega
  rw [hs]
  exact card_order_pred_eq_totient hp

def sample {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) : PMF (ZMod N)ˣ :=
  PMF.uniformOfFinset (candidates N) (candidates_nonempty hp hN)

theorem sample_success_mass {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) :
    (sample hp hN).toOuterMeasure {a | orderOf a=N-1} =
      (Nat.totient (N-1) : ℝ≥0∞)/(N-2 : ℕ) := by
  rw [sample,PMF.toOuterMeasure_uniformOfFinset'_apply]
  simp only [Set.mem_setOf_eq]
  rw [candidates_good_card hp hN,candidates_card hp hN]

def successProb {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) : ℝ :=
  ((sample hp hN).toOuterMeasure {a | orderOf a=N-1}).toReal

theorem successProb_eq {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) :
    successProb hp hN = (Nat.totient (N-1) : ℝ)/(N-2 : ℕ) := by
  simp only [successProb,sample_success_mass,ENNReal.toReal_div,ENNReal.toReal_natCast]

theorem successProb_pos {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) :
    0 < successProb hp hN := by
  rw [successProb_eq]
  apply div_pos
  · exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < N-1)
  · exact_mod_cast (by omega : 0 < N-2)

theorem all_units_fraction_le {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3 ≤ N) :
    (Nat.totient (N-1) : ℝ)/(N-1 : ℕ) ≤ successProb hp hN := by
  rw [successProb_eq]
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast (by omega : 0<N-2))
  exact_mod_cast (by omega : N-2 ≤ N-1)

end Qatlib.Concepts.OrderPrimality.UniformTrial
