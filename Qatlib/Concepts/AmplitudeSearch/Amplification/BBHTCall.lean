/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.SortedTable
import Qatlib.Concepts.AmplitudeSearch.Amplification.ClockEnvelope
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchQueryCost
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable

open Qatlib.Concepts.AmplitudeSearch.InterruptMin

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib
abbrev SearchTrace (N : ℕ) := TerminalTrace (Fin N) (ExponentialSizes N)

def rankMarked {N : ℕ} (e : Fin N ≃ Fin N) (t : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => (e.symm i).val < t)

def rankMarkedEquiv {N t : ℕ} (e : Fin N ≃ Fin N) (htN : t ≤ N) :
    Fin t ≃ {i : Fin N // (e.symm i).val < t} where
  toFun k := ⟨e ⟨k.val, lt_of_lt_of_le k.isLt htN⟩, by simp [k.isLt]⟩
  invFun j := ⟨(e.symm j.val).val, j.property⟩
  left_inv k := by apply Fin.ext; simp
  right_inv j := by apply Subtype.ext; exact e.apply_symm_apply j.val

theorem rankMarked_card {N : ℕ} (e : Fin N ≃ Fin N) (t : ℕ) (htN : t ≤ N) :
    (rankMarked e t).card = t := by
  simpa only [rankMarked, Fintype.card_fin, Fintype.card_subtype] using
    (Fintype.card_congr (rankMarkedEquiv e htN)).symm

theorem rankMarked_eq_strict_values {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (y : Fin N) :
    rankMarked T.indexOfRank (T.lowerCut y).val =
      Finset.univ.filter (fun i => T.value i < T.value (T.indexOfRank y)) := by
  ext i
  simp only [rankMarked, Finset.mem_filter, Finset.mem_univ, true_and]
  have h := T.smaller_iff_lowerCut y (T.indexOfRank.symm i)
  simpa using h.symm

theorem bbht_prefix_law {N : ℕ} (e : Fin N ≃ Fin N) (t : ℕ)
    (ht : 0 < t) (htN : t < N) :
    HasSum (TerminalMass (rankMarked e t) (ExponentialSizes N)) 1 ∧
      ∀ x : SearchTrace N, 0 ≤ TerminalMass (rankMarked e t) (ExponentialSizes N) x ∧
        (¬ (e.symm (TerminalOutput x)).val < t →
          TerminalMass (rankMarked e t) (ExponentialSizes N) x = 0) := by
  have hc := rankMarked_card e t htN.le
  have h := search_terminal_law (rankMarked e t) (by omega)
    (by simpa only [Fintype.card_fin, hc] using htN)
  generalize hM : Fintype.card (Fin N) = M at h
  have hMN : M = N := hM.symm.trans (Fintype.card_fin N)
  clear hM
  subst M
  simpa only [rankMarked, Finset.mem_filter, Finset.mem_univ, true_and] using h

theorem bbht_prefix_output {N : ℕ} (e : Fin N ≃ Fin N) (t : ℕ)
    (ht : 0 < t) (htN : t < N) (i : Fin N) :
    HasSum (fun x : SearchTrace N => if e.symm (TerminalOutput x) = i then
      TerminalMass (rankMarked e t) (ExponentialSizes N) x else 0)
      (if i.val < t then 1 / (t : ℝ) else 0) := by
  have hc := rankMarked_card e t htN.le
  have h := search_terminal_output (rankMarked e t) (by omega)
    (by simpa only [Fintype.card_fin, hc] using htN) (e i)
  generalize hM : Fintype.card (Fin N) = M at h
  have hMN : M = N := hM.symm.trans (Fintype.card_fin N)
  clear hM
  subst M
  rw [hc] at h
  simpa only [rankMarked, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.symm_apply_eq, Equiv.symm_apply_apply] using h

noncomputable def bbhtJointLaw {N : ℕ} (e : Fin N ≃ Fin N)
    (duration : SearchTrace N → ℝ) (hd : ∀ x, 0 ≤ duration x) : RankedCallLaw N (SearchTrace N) where
  mass t x := if 0 < t ∧ t < N then TerminalMass (rankMarked e t) (ExponentialSizes N) x else 0
  outputRank x := e.symm (TerminalOutput x)
  duration := duration
  duration_nonneg := hd
  mass_nonneg := by
    intro t htN x
    by_cases ht : 0 < t
    · simpa only [if_pos (show 0 < t ∧ t < N from ⟨ht, htN⟩)] using
        (bbht_prefix_law e t ht htN).2 x |>.1
    · simp [ht]
  normalized := by
    intro t ht htN
    simpa only [if_pos (show 0 < t ∧ t < N from ⟨ht, htN⟩)] using (bbht_prefix_law e t ht htN).1
  lower_support := by
    intro t ht htN x hx
    simpa only [if_pos (show 0 < t ∧ t < N from ⟨ht, htN⟩)] using
        (bbht_prefix_law e t ht htN).2 x |>.2 hx
  output_uniform := by
    intro t ht htN i
    simpa only [if_pos (show 0 < t ∧ t < N from ⟨ht, htN⟩)] using bbht_prefix_output e t ht htN i

noncomputable def sourceBBHTLaw {N : ℕ} (e : Fin N ≃ Fin N) (hN : 0 < N) :
    RankedCallLaw N (SearchTrace N) :=
  bbhtJointLaw e (fun x => (TerminalCost (ExponentialSizes N) x : ℝ) + binaryLog N)
    (fun _ => add_nonneg (Nat.cast_nonneg _) (div_nonneg
      (Real.log_nonneg (by exact_mod_cast hN)) (Real.log_pos (by norm_num)).le))

theorem sourceBBHTLaw_moment {N : ℕ} (e : Fin N ≃ Fin N) (hN : 0 < N)
    (t : ℕ) (ht : 0 < t) (htN : t < N) :
    ∃ q, HasSum (fun x => (sourceBBHTLaw e hN).mass t x *
      (sourceBBHTLaw e hN).duration x) q ∧ q ≤ sourceCallEnvelope N t := by
  have hc := rankMarked_card e t htN.le
  have h := search_terminal_cost (rankMarked e t) (by omega)
    (by simpa only [Fintype.card_fin, hc] using htN)
  generalize hM : Fintype.card (Fin N) = M at h
  have hMN : M = N := hM.symm.trans (Fintype.card_fin N)
  clear hM
  subst M
  rw [hc] at h
  obtain ⟨q, hq, _, _, hqb⟩ := h
  refine ⟨q + binaryLog N, ?_, ?_⟩
  · have hs := hq.add ((bbht_prefix_law e t ht htN).1.mul_right (binaryLog N))
    convert! hs using 1
    · funext x
      simp only [sourceBBHTLaw, bbhtJointLaw, if_pos (show 0 < t ∧ t < N from ⟨ht, htN⟩)]
      ring
    · ring
  · rw [sourceCallEnvelope, if_neg (Nat.ne_of_gt ht)]
    rw [Real.sqrt_div (Nat.cast_nonneg N)] at hqb
    convert! add_le_add hqb (le_refl (binaryLog N)) using 1
    ring

theorem bbht_source_attainment_moment {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hN : 0 < N) :
    ∃ q, HasSum (fun x : Fin N × List (SearchTrace N) =>
      (sourceBBHTLaw T.indexOfRank hN).initialMass T.skip x *
        (sourceBBHTLaw T.indexOfRank hN).runClock x.2) q ∧
      0 ≤ q ∧ q ≤ sourceMeanBudget N := by
  exact initialClock_le_sourceMeanBudget (sourceBBHTLaw T.indexOfRank hN) T.skip hN
    (sourceBBHTLaw_moment T.indexOfRank hN)

end Qatlib.Concepts.AmplitudeSearch.Amplification
