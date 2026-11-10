/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.TapeCompilation.ClassicalProbabilisticDefs
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Mathlib.Data.List.TakeWhile
import Qatlib.Concepts.ClassicalTape.TapeCompilation.ClassicalProbabilistic
import Qatlib.Concepts.ClassicalTape.FairCoinTape
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Turing

namespace Qatlib.Concepts.ClassicalTape.TapeBoundary
open Turing

theorem orRun_run_aux (T : Turing.Tape (Tracks 2)) (c0 c1 : Bool) :
    (coinTapeRunAux orRunTable orRunAccept [c0, c1]
      (⟨.read1, T⟩ : Turing.TM0.Cfg (Tracks 2) OrRunCtrl)).1 = some (c0 || c1) := by
  have hc0 : coinHalt orRunTable (⟨.read1, T⟩ : Turing.TM0.Cfg (Tracks 2) OrRunCtrl) = false := rfl
  have hst0 : Turing.TM0.step (orRunTable c0) (⟨.read1, T⟩ : Turing.TM0.Cfg (Tracks 2) OrRunCtrl)
      = some (⟨.read2 c0, T⟩ : Turing.TM0.Cfg (Tracks 2) OrRunCtrl) := rfl
  rw [coinTapeRunAux_cons_of_step_some orRunTable orRunAccept c0 [c1]
    (⟨.read1, T⟩ : Turing.TM0.Cfg (Tracks 2) OrRunCtrl)
    (⟨.read2 c0, T⟩ : Turing.TM0.Cfg (Tracks 2) OrRunCtrl) hc0 hst0]
  show (coinTapeRunAux orRunTable orRunAccept [c1]
    (⟨.read2 c0, T⟩ : Turing.TM0.Cfg (Tracks 2) OrRunCtrl)).1 = _
  have hc1 : coinHalt orRunTable (⟨.read2 c0, T⟩ : Turing.TM0.Cfg (Tracks 2) OrRunCtrl) = false :=
      rfl
  have hst1 : Turing.TM0.step (orRunTable c1) (⟨.read2 c0, T⟩ : Turing.TM0.Cfg (Tracks 2) OrRunCtrl)
      = some (⟨.outC (c0 || c1), T⟩ : Turing.TM0.Cfg (Tracks 2) OrRunCtrl) := rfl
  rw [coinTapeRunAux_cons_of_step_some orRunTable orRunAccept c1 []
    (⟨.read2 c0, T⟩ : Turing.TM0.Cfg (Tracks 2) OrRunCtrl)
    (⟨.outC (c0 || c1), T⟩ : Turing.TM0.Cfg (Tracks 2) OrRunCtrl) hc1 hst1]
  show (coinTapeRunAux orRunTable orRunAccept []
    (⟨.outC (c0 || c1), T⟩ : Turing.TM0.Cfg (Tracks 2) OrRunCtrl)).1 = _
  have hc2 :
      coinHalt orRunTable (⟨.outC (c0 || c1), T⟩ : Turing.TM0.Cfg (Tracks 2) OrRunCtrl) = true :=
      rfl
  rw [coinTapeRunAux_of_coinHalt orRunTable orRunAccept []
    (⟨.outC (c0 || c1), T⟩ : Turing.TM0.Cfg (Tracks 2) OrRunCtrl) hc2]
  rfl

theorem orRun_run (input : List (Tracks 2)) (c0 c1 : Bool) :
    (coinTapeRun orRunTable orRunAccept input [c0, c1]).1 = some (c0 || c1) := by
  unfold coinTapeRun
  have hin : (Turing.TM0.init input : Turing.TM0.Cfg (Tracks 2) OrRunCtrl)
      = (⟨.read1, (Turing.TM0.init input : Turing.TM0.Cfg (Tracks 2) OrRunCtrl).Tape⟩ :
          Turing.TM0.Cfg (Tracks 2) OrRunCtrl) := rfl
  rw [hin]
  exact orRun_run_aux _ c0 c1

theorem naive_fake_fst (r : ℕ) (v : Bool) :
    ∀ (m j : ℕ) (hm : 1 ≤ m) (hj : j + m = 2 * r)
      (t : Turing.Tape (Tracks 2)) (ht : t.head 1 = some v)
      (cs : List Bool), 2 * m ≤ cs.length →
      (coinTapeRunAux (naiveMajorityTable r) (naiveMajorityAccept r) cs
        (⟨.fake j v false, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))).1 = some v := by
  intro m
  induction m with
  | zero =>
    intro j hm hj t ht cs hlen
    omega
  | succ m ih =>
    intro j hm hj t ht cs hlen
    have htabF0 : ∀ c : Bool, naiveMajorityTable r c (.fake j v false) t.head =
        match t.head 1 with
        | some w => some (.fake j w true, .write t.head)
        | none => some (.fake j false true, .write t.head) := fun c => rfl
    have htabF : ∀ c : Bool,
        naiveMajorityTable r c (.fake j v false) t.head
          = some (.fake j v true, .write t.head) := by
      intro c
      rw [htabF0 c, ht]
    have htabT : ∀ c : Bool, naiveMajorityTable r c (.fake j v true) t.head
        = if j + 1 < 2 * r then some (.fake (j + 1) v false, .write t.head)
          else some (.outC v, .write t.head) := fun c => rfl
    have hcF : coinHalt (naiveMajorityTable r)
        (⟨.fake j v false, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) = false := by
      simp only [coinHalt, htabF]
      rfl
    have hcT : coinHalt (naiveMajorityTable r)
        (⟨.fake j v true, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) = false := by
      simp only [coinHalt, htabT]
      split_ifs <;> rfl
    have hstF : Turing.TM0.step (naiveMajorityTable r true)
        (⟨.fake j v false, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))
        = some (⟨.fake j v true, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) := by
      rw [TM0_step_apply, htabF]
      rfl
    obtain ⟨c, cs1, rfl⟩ : ∃ c cs1, cs = c :: cs1 :=
      List.exists_cons_of_ne_nil (fun h => by simp [h] at hlen)
    simp only [List.length_cons] at hlen
    rw [coinTapeRunAux_cons_of_step_some (naiveMajorityTable r) (naiveMajorityAccept r) c cs1
      (⟨.fake j v false, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))
      (⟨.fake j v true, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) hcF hstF]
    show (coinTapeRunAux (naiveMajorityTable r) (naiveMajorityAccept r) cs1
      (⟨.fake j v true, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))).1 = _
    have hlen1 : 2 * m ≤ cs1.length := by omega
    obtain ⟨c', cs2, rfl⟩ : ∃ c' cs2, cs1 = c' :: cs2 :=
      List.exists_cons_of_ne_nil (fun h => by simp [h] at hlen; omega)
    simp only [List.length_cons] at hlen hlen1
    by_cases hj2 : j + 1 < 2 * r
    · have hstT : Turing.TM0.step (naiveMajorityTable r true)
          (⟨.fake j v true, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))
          = some (⟨.fake (j + 1) v false, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) := by
        rw [TM0_step_apply, htabT, if_pos hj2]
        rfl
      rw [coinTapeRunAux_cons_of_step_some (naiveMajorityTable r) (naiveMajorityAccept r) c' cs2
        (⟨.fake j v true, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))
        (⟨.fake (j + 1) v false, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) hcT hstT]
      have hlen2 : 2 * m ≤ cs2.length := by omega
      have hm1 : 1 ≤ m := by omega
      have hjm : (j + 1) + m = 2 * r := by omega
      exact ih (j + 1) hm1 hjm t ht cs2 hlen2
    · have hstT : Turing.TM0.step (naiveMajorityTable r true)
          (⟨.fake j v true, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))
          = some (⟨.outC v, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) := by
        rw [TM0_step_apply, htabT, if_neg hj2]
        rfl
      rw [coinTapeRunAux_cons_of_step_some (naiveMajorityTable r) (naiveMajorityAccept r) c' cs2
        (⟨.fake j v true, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))
        (⟨.outC v, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) hcT hstT]
      have hcO : coinHalt (naiveMajorityTable r)
          (⟨.outC v, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) = true := rfl
      rw [coinTapeRunAux_of_coinHalt (naiveMajorityTable r) (naiveMajorityAccept r) cs2
        (⟨.outC v, t⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) hcO]
      rfl

theorem naive_run_aux (r : ℕ) (hr : 0 < r) (T : Turing.Tape (Tracks 2)) (c0 c1 c2 : Bool)
    (cs : List Bool) (hlen : 4 * r ≤ cs.length) :
    (coinTapeRunAux (naiveMajorityTable r) (naiveMajorityAccept r) (c0 :: c1 :: c2 :: cs)
      (⟨.read1, T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))).1 = some (c0 || c1) := by
  have hc0 : coinHalt (naiveMajorityTable r)
      (⟨.read1, T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) = false := rfl
  have hst0 : Turing.TM0.step (naiveMajorityTable r c0)
      (⟨.read1, T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))
      = some (⟨.read2 c0, T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) := rfl
  rw [coinTapeRunAux_cons_of_step_some (naiveMajorityTable r) (naiveMajorityAccept r) c0
    (c1 :: c2 :: cs) (⟨.read1, T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))
    (⟨.read2 c0, T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) hc0 hst0]
  show (coinTapeRunAux (naiveMajorityTable r) (naiveMajorityAccept r) (c1 :: c2 :: cs)
    (⟨.read2 c0, T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))).1 = _
  have hc1 : coinHalt (naiveMajorityTable r)
      (⟨.read2 c0, T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) = false := rfl
  have hst1 : Turing.TM0.step (naiveMajorityTable r c1)
      (⟨.read2 c0, T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))
      = some (⟨.settle (c0 || c1), T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) := rfl
  rw [coinTapeRunAux_cons_of_step_some (naiveMajorityTable r) (naiveMajorityAccept r) c1
    (c2 :: cs) (⟨.read2 c0, T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))
    (⟨.settle (c0 || c1), T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) hc1 hst1]
  show (coinTapeRunAux (naiveMajorityTable r) (naiveMajorityAccept r) (c2 :: cs)
    (⟨.settle (c0 || c1), T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))).1 = _
  have hcS : coinHalt (naiveMajorityTable r)
      (⟨.settle (c0 || c1), T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) = false := rfl
  have hstS : Turing.TM0.step (naiveMajorityTable r c2)
      (⟨.settle (c0 || c1), T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))
      = some (⟨.fake 0 (c0 || c1) false,
          T.write (fun k => if k.val = 1 then some (c0 || c1) else T.head k)⟩ :
        Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) := rfl
  rw [coinTapeRunAux_cons_of_step_some (naiveMajorityTable r) (naiveMajorityAccept r) c2 cs
    (⟨.settle (c0 || c1), T⟩ : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))
    (⟨.fake 0 (c0 || c1) false,
      T.write (fun k => if k.val = 1 then some (c0 || c1) else T.head k)⟩ :
      Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) hcS hstS]
  show (coinTapeRunAux (naiveMajorityTable r) (naiveMajorityAccept r) cs
    (⟨.fake 0 (c0 || c1) false,
      T.write (fun k => if k.val = 1 then some (c0 || c1) else T.head k)⟩ :
      Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))).1 = _
  have hnew : (T.write (fun k => if k.val = 1 then some (c0 || c1) else T.head k)).head 1
      = some (c0 || c1) := rfl
  have hm2 : 1 ≤ 2 * r := by omega
  have hj2 : 0 + 2 * r = 2 * r := by omega
  have hlen2 : 2 * (2 * r) ≤ cs.length := by omega
  exact naive_fake_fst r (c0 || c1) (2 * r) 0 hm2 hj2
    (T.write (fun k => if k.val = 1 then some (c0 || c1) else T.head k)) hnew cs hlen2

theorem naive_run (r : ℕ) (hr : 0 < r) (input : List (Tracks 2)) (c0 c1 c2 : Bool)
    (cs : List Bool) (hlen : 4 * r ≤ cs.length) :
    (coinTapeRunAux (naiveMajorityTable r) (naiveMajorityAccept r) (c0 :: c1 :: c2 :: cs)
      (Turing.TM0.init input)).1 = some (c0 || c1) := by
  have hin : (Turing.TM0.init input : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r))
      = (⟨.read1, (Turing.TM0.init input : Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)).Tape⟩ :
          Turing.TM0.Cfg (Tracks 2) (NaiveCtrl r)) := rfl
  rw [hin]
  exact naive_run_aux r hr _ c0 c1 c2 cs hlen

theorem snoc_at_zero (m : ℕ) (u : Fin (m + 2) → Bool) (b : Bool) :
    (Fin.snoc u b : Fin (m + 3) → Bool) 0 = u 0 := by
  rw [show (0 : Fin (m + 3)) = Fin.castSucc (0 : Fin (m + 2)) by simp, Fin.snoc_castSucc]

theorem snoc_at_one (m : ℕ) (u : Fin (m + 2) → Bool) (b : Bool) :
    (Fin.snoc u b : Fin (m + 3) → Bool) 1 = u 1 := by
  rw [show (1 : Fin (m + 3)) = Fin.castSucc (1 : Fin (m + 2)) by simp, Fin.snoc_castSucc]

theorem sum_or_two :
    (∑ ω : Fin 2 → Bool, if (ω 0 || ω 1) = false then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_boole]
  have hcard : (Finset.univ.filter (fun ω : Fin 2 → Bool => (ω 0 || ω 1) = false)).card = 1 := by
    decide
  rw [hcard]
  norm_num

theorem sum_snoc_last {n : ℕ} (g : (Fin (n + 1) → Bool) → ℝ)
    (hg : ∀ (u : Fin n → Bool) (b : Bool), g (Fin.snoc u b) = g (Fin.snoc u false)) :
    (∑ ω : Fin (n + 1) → Bool, g ω) = 2 * ∑ u : Fin n → Bool, g (Fin.snoc u false) := by
  rw [← Equiv.sum_comp (finBoolSnocEquiv n) g]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  have h2 : ∀ (u : Fin n → Bool), (∑ b : Bool, g (Fin.snoc u b)) = 2 * g (Fin.snoc u false) := by
    intro u
    rw [Fintype.sum_bool, hg, ← two_mul]
  show ∑ x : Fin n → Bool, ∑ y : Bool, g (Fin.snoc x y) = _
  rw [Finset.sum_congr rfl (fun u _ => h2 u)]
  rw [← Finset.mul_sum]

theorem sum_or_snoc (m : ℕ) :
    (∑ ω : Fin (m + 3) → Bool, if (ω 0 || ω 1) = false then (1 : ℝ) else 0)
      = 2 * ∑ u : Fin (m + 2) → Bool, if (u 0 || u 1) = false then (1 : ℝ) else 0 := by
  rw [← Equiv.sum_comp (finBoolSnocEquiv (m + 2))
    (fun ω : Fin (m + 3) → Bool => if (ω 0 || ω 1) = false then (1 : ℝ) else 0)]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  show ∑ x : Fin (m + 2) → Bool, ∑ y : Bool,
      (fun ω : Fin (m + 3) → Bool => if (ω 0 || ω 1) = false then (1 : ℝ) else 0)
        (Fin.snoc x y) = _
  have h2 : ∀ (u : Fin (m + 2) → Bool),
      (∑ b : Bool, (fun ω : Fin (m + 3) → Bool => if (ω 0 || ω 1) = false then (1 : ℝ) else 0)
        (Fin.snoc u b)) = 2 * (if (u 0 || u 1) = false then (1 : ℝ) else 0) := by
    intro u
    have key : ∀ b : Bool,
        (fun ω : Fin (m + 3) → Bool => if (ω 0 || ω 1) = false then (1 : ℝ) else 0) (Fin.snoc u b)
          = if (u 0 || u 1) = false then (1 : ℝ) else 0 := by
      intro b
      show (if ((Fin.snoc u b : Fin (m + 3) → Bool) 0
            || (Fin.snoc u b : Fin (m + 3) → Bool) 1) = false then (1 : ℝ) else 0) = _
      rw [snoc_at_zero m u b, snoc_at_one m u b]
    have h2' : (∑ b : Bool, (fun ω : Fin (m + 3) → Bool => if (ω 0 || ω 1) = false then (1 : ℝ) else 0)
        (Fin.snoc u b)) = ∑ _b : Bool, if (u 0 || u 1) = false then (1 : ℝ) else 0 :=
      Finset.sum_congr rfl (fun b _ => key b)
    rw [h2']
    simp [Finset.sum_const, Fintype.card_bool]
  rw [Finset.sum_congr rfl (fun u _ => h2 u)]
  rw [← Finset.mul_sum]

theorem sum_or_pow (m : ℕ) :
    (∑ ω : Fin (m + 2) → Bool, if (ω 0 || ω 1) = false then (1 : ℝ) else 0) = 2 ^ m := by
  induction m with
  | zero => exact sum_or_two
  | succ m ih =>
    rw [sum_or_snoc m, ih]
    rw [pow_succ, mul_comm]

theorem orRun_ofFn (input : List (Tracks 2)) (ω : Fin 2 → Bool) :
    (coinTapeRun orRunTable orRunAccept input (List.ofFn ω)).1 = some (ω 0 || ω 1) := by
  have h : List.ofFn ω = [ω 0, ω 1] := by simp [List.ofFn_succ]
  rw [h]
  exact orRun_run input (ω 0) (ω 1)

theorem orRun_false_mass (input : List (Tracks 2)) :
    fairTapeSuccess orRunTable orRunAccept input 2 false = 1 / 4 := by
  unfold fairTapeSuccess
  have hpt : ∀ ω : Fin 2 → Bool,
      (if (coinTapeRun orRunTable orRunAccept input (List.ofFn ω)).1 = some false
        then (1 : ℝ) else 0)
        = if (ω 0 || ω 1) = false then (1 : ℝ) else 0 := by
    intro ω
    simp only [orRun_ofFn input ω, Option.some.injEq]
  rw [Finset.sum_congr rfl (fun ω _ => hpt ω)]
  rw [sum_or_two]
  norm_num

theorem naive_ofFn12 (input : List (Tracks 2)) (ω : Fin 51 → Bool) :
    (coinTapeRunAux (naiveMajorityTable 12) (naiveMajorityAccept 12) (List.ofFn ω)
      (Turing.TM0.init input)).1 = some (ω 0 || ω 1) := by
  have h : List.ofFn ω = ω 0 :: ω 1 :: ω 2 :: (List.ofFn ω).drop 3 := by
    simp [List.ofFn_succ]
  rw [h]
  have hlen : 4 * 12 ≤ ((List.ofFn ω).drop 3).length := by
    simp [List.length_ofFn]
  exact naive_run 12 (by norm_num) input (ω 0) (ω 1) (ω 2) ((List.ofFn ω).drop 3) hlen

theorem naive_run_ne_none (input : List (Tracks 2)) (ω : Fin 51 → Bool) :
    (coinTapeRun (naiveMajorityTable 12) (naiveMajorityAccept 12) input (List.ofFn ω)).1 ≠ none := by
  unfold coinTapeRun
  rw [naive_ofFn12 input ω]
  exact Option.some_ne_none _

theorem naive_false_mass (input : List (Tracks 2)) :
    fairTapeSuccess (naiveMajorityTable 12) (naiveMajorityAccept 12) input
      (naiveBudget 12) false = 1 / 4 := by
  show fairTapeSuccess (naiveMajorityTable 12) (naiveMajorityAccept 12) input 51 false = 1 / 4
  unfold fairTapeSuccess
  have hpt : ∀ ω : Fin 51 → Bool,
      (if (coinTapeRun (naiveMajorityTable 12) (naiveMajorityAccept 12) input (List.ofFn ω)).1
          = some false then (1 : ℝ) else 0)
        = if (ω 0 || ω 1) = false then (1 : ℝ) else 0 := by
    intro ω
    unfold coinTapeRun
    simp only [naive_ofFn12 input ω, Option.some.injEq]
  rw [Finset.sum_congr rfl (fun ω _ => hpt ω)]
  have h := sum_or_pow 49
  rw [h]
  norm_num

theorem boundary_eight_nine : (8 / 9 : ℝ) ^ 12 < 1 / 4 := by norm_num

theorem boundary_neg :
    ¬ (∀ input : List Bool,
        fairTapeSuccess orRunTable orRunAccept (twoTrackBitEncode input) 2 false ≤ 1 / 3 →
          fairTapeSuccess (naiveMajorityTable 12) (naiveMajorityAccept 12)
            (twoTrackBitEncode input) (naiveBudget 12) false ≤ (8 / 9 : ℝ) ^ 12) := by
  intro hall
  have h1 : fairTapeSuccess orRunTable orRunAccept (twoTrackBitEncode []) 2 false = 1 / 4 :=
    orRun_false_mass _
  have h2 : fairTapeSuccess (naiveMajorityTable 12) (naiveMajorityAccept 12)
      (twoTrackBitEncode []) (naiveBudget 12) false = 1 / 4 := naive_false_mass _
  have hprem : fairTapeSuccess orRunTable orRunAccept (twoTrackBitEncode []) 2 false ≤ 1 / 3 := by
    rw [h1]; norm_num
  have hcon := hall [] hprem
  rw [h2] at hcon
  have hlt : (8 / 9 : ℝ) ^ 12 < 1 / 4 := boundary_eight_nine
  linarith
open Turing
open scoped Classical

theorem median_block : ∀ (X : Type) [Fintype X] (L M : ℕ) (p : FinDist X) (f : X → ℝ),
    0 < L → 0 < M → ∀ ε : ℝ, 0 < ε →
      4 * p.variance f ≤ (L : ℝ) * ε ^ 2 →
      ∑ ω ∈ Finset.univ.filter
          (fun ω : Fin M → Fin L → X => ε < |p.medianOfMeans f ω - p.expect f|),
        ∏ m, p.probOf (ω m) ≤ 3 ^ (M / 2) / 2 ^ M := by
  intro X _ L M p f hL hM ε hε hvar
  exact Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.median_of_means_concentration p f hL hM ε hε hvar

theorem g4 :

  (∀ input : List Bool,
    ∃ final : Turing.TM2.Cfg tm2StackΓ TM2CopyLabel (Option Bool),
      tm2Run tm2Copy (2 * input.length + 2) (tm2InitCopy input) = some final ∧
        final.l = none ∧
        final.stk TM2Stack.input = input ∧
        final.stk TM2Stack.work = input ∧
        final.stk TM2Stack.aux = []) ∧

  (∀ input work : List Bool,
    ∃ final : Turing.TM2.Cfg tm2StackΓ TM2ResetLabel (Option Bool),
      tm2Run tm2Reset (work.length + 1) (tm2InitReset input work) = some final ∧
        final.l = none ∧
        final.stk TM2Stack.work = [] ∧
        final.stk TM2Stack.input = input) ∧

  (Function.Injective standardBitEncode ∧
    Function.Injective twoTrackBitEncode ∧
    Function.Injective delimitedPairEncode ∧
      ∀ input : List Bool, (delimitedPairEncode input).length = input.length + 1) ∧

  (∀ (X : Type) [Fintype X] (L M : ℕ) (p : FinDist X) (f : X → ℝ),
    0 < L → 0 < M → ∀ ε : ℝ, 0 < ε →
      4 * p.variance f ≤ (L : ℝ) * ε ^ 2 →
      ∑ ω ∈ Finset.univ.filter
          (fun ω : Fin M → Fin L → X => ε < |p.medianOfMeans f ω - p.expect f|),
        ∏ m, p.probOf (ω m) ≤ 3 ^ (M / 2) / 2 ^ M) ∧

  ((∀ input : List Bool,
      fairTapeSuccess orRunTable orRunAccept (twoTrackBitEncode input) 2 false = 1 / 4 ∧
        1 / 4 ≤ 1 / 3 ∧
        (∀ ω : Fin (naiveBudget 12) → Bool,
          (coinTapeRun (naiveMajorityTable 12) (naiveMajorityAccept 12)
            (twoTrackBitEncode input) (List.ofFn ω)).1 ≠ none) ∧
        fairTapeSuccess (naiveMajorityTable 12) (naiveMajorityAccept 12)
          (twoTrackBitEncode input) (naiveBudget 12) false = 1 / 4) ∧
    (8 / 9 : ℝ) ^ 12 < 1 / 4 ∧
    ¬ (∀ input : List Bool,
        fairTapeSuccess orRunTable orRunAccept (twoTrackBitEncode input) 2 false ≤ 1 / 3 →
          fairTapeSuccess (naiveMajorityTable 12) (naiveMajorityAccept 12)
            (twoTrackBitEncode input) (naiveBudget 12) false ≤ (8 / 9 : ℝ) ^ 12))
 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro input
    exact ⟨(⟨none, none, copyStk input input []⟩ : Turing.TM2.Cfg tm2StackΓ TM2CopyLabel (Option Bool)),
      tm2Copy_run input, rfl, rfl, rfl, rfl⟩
  · intro input work
    exact ⟨(⟨none, none, copyStk input [] []⟩ : Turing.TM2.Cfg tm2StackΓ TM2ResetLabel (Option Bool)),
      tm2Reset_run input work, rfl, rfl, rfl⟩
  · exact ⟨standardBitEncode_injective, twoTrackBitEncode_injective,
      delimitedPairEncode_injective, delimitedPairEncode_length⟩
  · intro X _ L M p f hL hM ε hε hvar
    exact Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.median_of_means_concentration p f hL hM ε hε hvar
  · refine ⟨?_, boundary_eight_nine, boundary_neg⟩
    intro input
    exact ⟨orRun_false_mass (twoTrackBitEncode input), by norm_num,
      fun ω => naive_run_ne_none (twoTrackBitEncode input) ω,
      naive_false_mass (twoTrackBitEncode input)⟩
end Qatlib.Concepts.ClassicalTape.TapeBoundary
