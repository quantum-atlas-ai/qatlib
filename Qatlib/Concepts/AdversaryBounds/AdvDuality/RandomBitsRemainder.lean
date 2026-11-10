/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsRemainderDefs
import Qatlib.Concepts.GibbsMetropolis.RationalBath.RationalRejectionTermination
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution

open Qatlib.Concepts.AdversaryBounds.AdvDuality.CoinCode
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped ENNReal

namespace CoinCode

variable {α β : Type}

@[simp] theorem run_ret (bs : List Bool) (a : α) : run bs (.ret a) = (.ret a, 0) := by
  cases bs <;> rfl

theorem run_append (xs ys : List Bool) (p : CoinCode α) :
    p.run (xs ++ ys) =
      let z := p.run xs
      let z' := z.1.run ys
      (z'.1, z.2 + z'.2) := by
  induction xs generalizing p with
  | nil => simp [run]
  | cons b xs ih =>
      cases p with
      | ret a => simp [run]
      | bit p q => simp only [List.cons_append, run]; rw [ih]; simp [Nat.add_assoc]

theorem run_reads_le (bs : List Bool) (p : CoinCode α) :
    (p.run bs).2 ≤ bs.length := by
  induction bs generalizing p with
  | nil => simp [run]
  | cons b bs ih =>
      cases p with
      | ret a => simp [run]
      | bit p q =>
          have h := ih (if b then q else p)
          simp only [run, List.length_cons]
          omega

theorem run_reads_le_depth (bs : List Bool) (p : CoinCode α) :
    (p.run bs).2 ≤ p.depth := by
  induction bs generalizing p with
  | nil => exact Nat.zero_le _
  | cons b bs ih =>
      cases p with
      | ret a => rfl
      | bit p q =>
          have h := ih (if b then q else p)
          cases b <;> simp only [run, depth, Bool.false_eq_true, ↓reduceIte] at * <;> omega

theorem run_complete (bs : List Bool) (p : CoinCode α) (h : p.depth ≤ bs.length) :
    ∃ a, (p.run bs).1 = .ret a := by
  induction bs generalizing p with
  | nil => cases p <;> simp_all [depth, run]
  | cons b bs ih =>
      cases p with
      | ret a => exact ⟨a, rfl⟩
      | bit p q =>
          simp only [depth, List.length_cons] at h
          have h' : (if b then q else p).depth ≤ bs.length := by
            cases b <;> simp <;> omega
          simpa [run] using ih (if b then q else p) h'

theorem depth_bind_le (p : CoinCode α) (f : α → CoinCode β) (c : ℕ)
    (h : ∀ a, (f a).depth ≤ c) : (p.bind f).depth ≤ p.depth + c := by
  induction p with
  | ret a => simpa only [bind, depth, Nat.zero_add] using h a
  | bit p q hp hq =>
      simp only [bind, depth]
      omega

theorem tapeLaw_eq_law (p : CoinCode α) (n : ℕ) (h : p.depth ≤ n) :
    tapeLaw n p = p.law.map (fun z => (some z.1, z.2)) := by
  induction p generalizing n with
  | ret a =>
      simp only [tapeLaw, run_ret, output, law,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_map]
      exact PMF.map_const _ _
  | bit p q hp hq =>
      cases n with
      | zero => simp [depth] at h
      | succ n =>
          have hp' := hp n (by simp only [depth] at h; omega)
          have hq' := hq n (by simp only [depth] at h; omega)
          simp only [tapeLaw, freshTape, PMF.map_bind, PMF.map_comp,
            Function.comp_def, run, law]
          congr 1
          funext b
          cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
          · calc
              _ = (tapeLaw n p).map (fun z => (z.1, 1 + z.2)) :=
                (PMF.map_comp _ _ _).symm
              _ = _ := by
                rw [hp']
                simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge, PMF.map_comp,
                    Function.comp_def]
          · calc
              _ = (tapeLaw n q).map (fun z => (z.1, 1 + z.2)) :=
                (PMF.map_comp _ _ _).symm
              _ = _ := by
                rw [hq']
                simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge, PMF.map_comp,
                    Function.comp_def]

theorem law_bind (p : CoinCode α) (f : α → CoinCode β) :
    (p.bind f).law = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind p.law (fun a => (f a).law) := by
  induction p with
  | ret a => simp [bind, law]
  | bit p q hp hq =>
      simp only [bind, law, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind, PMF.bind_bind]
      congr 1
      funext b
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [hp]
        exact (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_bind 1 p.law (fun a => (f a).law)).symm
      · rw [hq]
        exact (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_bind 1 q.law (fun a => (f a).law)).symm

theorem law_bind_ret (p : CoinCode α) (f : α → β) :
    (p.bind (fun a => .ret (f a))).law = p.law.map (fun z => (f z.1, z.2)) := by
  rw [law_bind]
  simp only [law, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret]
  exact PMF.bind_pure_comp _ _

theorem block_law (n : ℕ) : (block n).law = fairBitsCosted n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [block, law_bind, ih, fairBitsCosted]
      congr 1
      funext ω
      simp only [law]
      rw [← PMF.bind_pure_comp]
      congr 1
      funext b
      cases b <;> simp

theorem block_depth_le (n : ℕ) : (block n).depth ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h := depth_bind_le (block n) (fun ω =>
        .bit (.ret ((regSuccEquiv n).symm (ω, false)))
          (.ret ((regSuccEquiv n).symm (ω, true)))) 1 (by intro ω; rfl)
      exact h.trans (by omega)

theorem block_law_uniform (b : ℕ) :
    (block b).law = (PMF.uniformOfFintype' (Reg b)).map (fun ω => (ω, b)) := by
  rw [block_law]
  ext z
  rcases z with ⟨ω, k⟩
  rw [fair_bit_program_joint_distribution, PMF.map_apply, tsum_fintype]
  by_cases hk : k = b
  · subst k; simp
  · simp [hk]

private theorem uniform_bits_split {B : Type} (n : ℕ) (f : Reg (n + 1) → B) :
    (PMF.uniformOfFintype' (Reg (n + 1))).map f =
      (PMF.uniformOfFintype' Bool).bind (fun b =>
        (PMF.uniformOfFintype' (Reg n)).map (fun ω => f (Fin.cons b ω))) := by
  classical
  ext y
  simp only [PMF.map_apply, PMF.bind_apply, tsum_fintype, PMF.uniformOfFintype'_apply]
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp only [Reg, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, pow_succ]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  change (if y = f (Fin.cons b ω) then _ else 0) = _
  split_ifs <;> simp_all [ENNReal.mul_inv, mul_comm]

theorem freshTape_uniform (n : ℕ) :
    freshTape n = (PMF.uniformOfFintype' (Reg n)).map List.ofFn := by
  induction n with
  | zero =>
      simp only [freshTape]
      exact (PMF.map_const _ _).symm
  | succ n ih =>
      rw [freshTape, ih, uniform_bits_split]
      simp only [PMF.map_comp, Function.comp_def, List.ofFn_cons]

@[simp] theorem atPosition_root (p : CoinCode α) : p.atPosition p.root = p := by
  cases p <;> rfl

theorem positions_card (p : CoinCode α) : Fintype.card p.Positions = p.nodes := by
  induction p with
  | ret a => rfl
  | bit p q hp hq =>
      change Fintype.card (Unit ⊕ (p.Positions ⊕ q.Positions)) = 1 + p.nodes + q.nodes
      simp only [Fintype.card_sum, Fintype.card_unit, hp, hq]
      omega

theorem nextPosition_spec (p : CoinCode α) (b : Bool) (i : p.Positions) :
    (p.nextPosition b i).map p.atPosition =
      match p.atPosition i with
      | .ret _ => none
      | .bit q r => some (if b then r else q) := by
  induction p with
  | ret a => rfl
  | bit p q hp hq =>
      rcases i with _ | (i | i)
      · cases b <;> simp [nextPosition, atPosition]
      · simpa only [nextPosition, Option.map_map, Function.comp_def, atPosition] using hp i
      · simpa only [nextPosition, Option.map_map, Function.comp_def, atPosition] using hq i

theorem nextPosition_none_of_ret (p : CoinCode α) (i : p.Positions) (a : α)
    (h : p.atPosition i = .ret a) (b : Bool) : p.nextPosition b i = none := by
  have hs := nextPosition_spec p b i
  rw [h] at hs
  exact Option.map_eq_none_iff.mp hs

theorem nextPosition_some_of_bit (p : CoinCode α) (i : p.Positions) (q r : CoinCode α)
    (h : p.atPosition i = .bit q r) (b : Bool) :
    ∃ j, p.nextPosition b i = some j ∧ p.atPosition j = if b then r else q := by
  have hs := nextPosition_spec p b i
  rw [h] at hs
  exact Option.map_eq_some_iff.mp hs

theorem native_step (p : CoinCode α) (b : Bool) (i : p.Positions)
    (T : Turing.Tape (Option Bool)) :
    Turing.TM0.step (p.nativeTable b) ⟨i, T⟩ =
      (p.nextPosition b i).map (fun j => (⟨j, T⟩ : Turing.TM0.Cfg _ _)) := by
  rw [TM0_step_apply]
  simp only [nativeTable, Option.map_map, Function.comp_def, TM0StmtApply, Turing.Tape.write_self]

theorem native_run (p : CoinCode α) (f : α → Bool) (bs : List Bool)
    (i : p.Positions) (T : Turing.Tape (Option Bool)) :
    coinTapeRunAux p.nativeTable (p.nativeAccept f) bs ⟨i, T⟩ =
      (((p.atPosition i).run bs).1.output.map f, ((p.atPosition i).run bs).2) := by
  induction bs generalizing i T with
  | nil =>
      cases h : p.atPosition i with
      | ret a =>
          have hn := nextPosition_none_of_ret p i a h
          simp [coinTapeRunAux, coinHalt, nativeTable, hn, nativeAccept, h, run, output]
      | bit q r =>
          obtain ⟨j, hj, _⟩ := nextPosition_some_of_bit p i q r h false
          simp [coinTapeRunAux, coinHalt, nativeTable, hj, run, output]
  | cons b bs ih =>
      cases h : p.atPosition i with
      | ret a =>
          have hn := nextPosition_none_of_ret p i a h
          simp [coinTapeRunAux, coinHalt, nativeTable, hn, nativeAccept, h, run, output]
      | bit q r =>
          obtain ⟨j0, hj0, _⟩ := nextPosition_some_of_bit p i q r h false
          obtain ⟨j, hj, hat⟩ := nextPosition_some_of_bit p i q r h b
          have hh : coinHalt p.nativeTable ⟨i, T⟩ = false := by
            simp [coinHalt, nativeTable, hj0]
          rw [coinTapeRunAux, if_neg (by simp [hh]), native_step, hj]
          simp only [Option.map_some, ih, hat, run, Prod.map, id_eq, Nat.add_comm 1]

theorem native_run_root (p : CoinCode α) (f : α → Bool) (bs : List Bool)
    (T : Turing.Tape (Option Bool)) :
    coinTapeRunAux p.nativeTable (p.nativeAccept f) bs ⟨p.root, T⟩ =
      ((p.run bs).1.output.map f, (p.run bs).2) := by
  simpa only [atPosition_root] using native_run p f bs p.root T

theorem native_halt_shared (p : CoinCode α) (i : p.Positions) (γ : Option Bool) :
    p.nativeTable false i γ = none ↔ p.nativeTable true i γ = none := by
  cases h : p.atPosition i with
  | ret a => simp [nativeTable, nextPosition_none_of_ret p i a h]
  | bit q r =>
      obtain ⟨j0, hj0, _⟩ := nextPosition_some_of_bit p i q r h false
      obtain ⟨j1, hj1, _⟩ := nextPosition_some_of_bit p i q r h true
      simp [nativeTable, hj0, hj1]

theorem native_coinTapeRun (p : CoinCode α) (f : α → Bool) (input bs : List Bool) :
    coinTapeRun p.nativeTable (p.nativeAccept f) (input.map some) bs =
      ((p.run bs).1.output.map f, (p.run bs).2) := by
  exact native_run_root p f bs _

theorem native_transition_count (p : CoinCode α) (bs : List Bool) (i : p.Positions)
    (T : Turing.Tape (Option Bool)) :
    coinTapeTransitionCountAux p.nativeTable bs ⟨i, T⟩ = ((p.atPosition i).run bs).2 := by
  induction bs generalizing i T with
  | nil => rfl
  | cons b bs ih =>
      cases h : p.atPosition i with
      | ret a =>
          have hn := nextPosition_none_of_ret p i a h
          simp [coinTapeTransitionCountAux, coinHalt, nativeTable, hn, run]
      | bit q r =>
          obtain ⟨j0, hj0, _⟩ := nextPosition_some_of_bit p i q r h false
          obtain ⟨j, hj, hat⟩ := nextPosition_some_of_bit p i q r h b
          have hh : coinHalt p.nativeTable ⟨i, T⟩ = false := by
            simp [coinHalt, nativeTable, hj0]
          rw [coinTapeTransitionCountAux, if_neg (by simp [hh]), native_step, hj]
          simp only [Option.map_some, ih, hat, run, Nat.add_comm 1]

theorem native_uniform_prefix_law (p : CoinCode α) (f : α → Bool) (input : List Bool)
    (n : ℕ) :
    (PMF.uniformOfFintype' (Reg n)).map
        (fun ω => coinTapeRun p.nativeTable (p.nativeAccept f) (input.map some) (List.ofFn ω)) =
      (tapeLaw n p).map (fun z => (z.1.map f, z.2)) := by
  rw [tapeLaw, freshTape_uniform, PMF.map_comp, PMF.map_comp]
  congr 1
  funext ω
  exact native_coinTapeRun p f input (List.ofFn ω)

theorem native_uniform_law (p : CoinCode α) (f : α → Bool) (input : List Bool)
    (n : ℕ) (h : p.depth ≤ n) :
    (PMF.uniformOfFintype' (Reg n)).map
        (fun ω => coinTapeRun p.nativeTable (p.nativeAccept f) (input.map some) (List.ofFn ω)) =
      p.law.map (fun z => (some (f z.1), z.2)) := by
  rw [native_uniform_prefix_law, tapeLaw_eq_law p n h, PMF.map_comp]
  rfl

end CoinCode

theorem weightedTrial_law {N : ℕ} (w : Fin N → ℕ) (b : ℕ) :
    (weightedTrial w b).law = (fairBitsCosted b).map
      (fun z => (weightDecodeCounted w (bitVecEquiv b z.1).val, z.2)) := by
  rw [weightedTrial, CoinCode.law_bind_ret, CoinCode.block_law]

theorem weightedTrial_depth_le {N : ℕ} (w : Fin N → ℕ) (b : ℕ) :
    (weightedTrial w b).depth ≤ b := by
  exact (CoinCode.depth_bind_le _ _ 0 (by intro a; rfl)).trans
    (by simpa using CoinCode.block_depth_le b)

theorem weightedSampler_depth_le {N : ℕ} (w : Fin N → ℕ) (b fuel : ℕ) :
    (weightedSampler w b fuel).depth ≤ b * fuel := by
  suffices h : ∀ cfg, (countedLoop w b fuel cfg).depth ≤ b * fuel from h _
  induction fuel with
  | zero => intro cfg; rfl
  | succ fuel ih =>
      intro cfg
      cases cfg with
      | inl out => exact Nat.zero_le _
      | inr BD =>
          apply le_trans (CoinCode.depth_bind_le _ _ (b * fuel) ?_)
          · have h := CoinCode.block_depth_le b
            simp only [Nat.mul_succ]
            omega
          · intro ω
            exact (CoinCode.depth_bind_le _ _ 0 (by intro y; rfl)).trans
              (by simpa using ih (countedTrialResult w b BD ω))

theorem countedTrialResult_law {N : ℕ} (w : Fin N → ℕ) (b : ℕ) (BD : ℕ × ℕ) :
    (PMF.uniformOfFintype' (Reg b)).map (countedTrialResult w b BD) =
      rationalCountedNext w b BD := by
  have h := CoinCode.block_law_uniform b
  rw [CoinCode.block_law] at h
  rw [rationalCountedNext, h, PMF.map_comp]
  rfl

theorem countedLoop_law {N : ℕ} (w : Fin N → ℕ) (b fuel : ℕ)
    (cfg : Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ)) :
    (countedLoop w b fuel cfg).law =
      (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.runFor (rationalCountedNext w b) fuel cfg).map
        (fun z => (z, b * z.2)) := by
  induction fuel generalizing cfg with
  | zero => simp [countedLoop, CoinCode.law, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.runFor, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret,
      PMF.pure_map]
  | succ fuel ih =>
      cases cfg with
      | inl out =>
          simp [countedLoop, CoinCode.law, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.runFor_halted,
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_map]
      | inr BD =>
          rw [countedLoop, CoinCode.law_bind, CoinCode.block_law_uniform]
          simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind, PMF.bind_map,
              Function.comp_def]
          simp only [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.runFor, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.tick,
            ← countedTrialResult_law, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind, PMF.bind_map, PMF.map_bind,
            Function.comp_def]
          congr 1
          funext ω
          rw [CoinCode.law_bind_ret, ih]
          simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge, PMF.map_comp,
              Function.comp_def]
          congr 1
          funext z
          simp [Nat.mul_add, Nat.add_comm]

theorem weightedSampler_law {N : ℕ} (w : Fin N → ℕ) (b fuel : ℕ) :
    (weightedSampler w b fuel).law = (rationalRejectionRun w b fuel).map
      (fun z => (z, b * z.2)) :=
  countedLoop_law w b fuel _

theorem weightedSampler_tapeLaw {N : ℕ} (w : Fin N → ℕ) (b fuel n : ℕ)
    (h : b * fuel ≤ n) :
    CoinCode.tapeLaw n (weightedSampler w b fuel) =
      (rationalRejectionRun w b fuel).map (fun z => (some z, b * z.2)) := by
  rw [CoinCode.tapeLaw_eq_law _ _ ((weightedSampler_depth_le w b fuel).trans h),
    weightedSampler_law, PMF.map_comp]
  rfl

theorem weightedSampler_native_law {N : ℕ} (w : Fin N → ℕ) (b fuel n : ℕ)
    (h : b * fuel ≤ n) (input : List Bool)
    (f : (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) × ℕ) → Bool) :
    (PMF.uniformOfFintype' (Reg n)).map (fun ω =>
        coinTapeRun (weightedSampler w b fuel).nativeTable
          ((weightedSampler w b fuel).nativeAccept f) (input.map some) (List.ofFn ω)) =
      (rationalRejectionRun w b fuel).map (fun z => (some (f z), b * z.2)) := by
  rw [CoinCode.native_uniform_law _ _ _ _ ((weightedSampler_depth_le w b fuel).trans h),
    weightedSampler_law, PMF.map_comp]
  rfl

theorem weightedSampler_run_bound {N : ℕ} (w : Fin N → ℕ) (b fuel : ℕ) (bs : List Bool) :
    ((weightedSampler w b fuel).run bs).2 ≤ min bs.length (b * fuel) :=
  le_min (CoinCode.run_reads_le _ _)
    ((CoinCode.run_reads_le_depth _ _).trans (weightedSampler_depth_le w b fuel))

theorem weightedSampler_timeout {N : ℕ} (w : Fin N → ℕ) (b fuel : ℕ)
    (hb : weightTotal w ≤ 2 ^ b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (weightedSampler w b fuel).law
      (fun z => rejectionOutcome z.1.1 = .inr ()) = rationalRejectMass w b ^ fuel := by
  rw [weightedSampler_law, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  exact rational_pending_mass w b fuel hb

theorem weightedSampler_return {N : ℕ} (w : Fin N → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) (j : Fin N) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (weightedSampler w b fuel).law
      (fun z => rejectionOutcome z.1.1 = .inl j) =
      (w j : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) * (1 - rationalRejectMass w b ^ fuel) := by
  rw [weightedSampler_law, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  exact (rational_finite_return_pending_and_first_stop N w b fuel hW hb).2.1 j

theorem weightedSampler_paths {N : ℕ} (w : Fin N → ℕ) (b fuel : ℕ)
    (z : (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) × ℕ) × ℕ)
    (hz : z ∈ (weightedSampler w b fuel).law.support) :
    z.1.2 ≤ fuel ∧ z.2 = b * z.1.2 ∧ rejectionBits z.1.1 = z.2 ∧
      rejectionComparisons z.1.1 ≤ N * z.1.2 := by
  rw [weightedSampler_law] at hz
  obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
  obtain ⟨ht, hb, hc, _, _⟩ := (rational_counted_run_projection_and_paths N w b fuel).2 y hy
  exact ⟨ht, rfl, hb, hc⟩

theorem weightedSampler_expectations {N : ℕ} (w : Fin N → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (weightedSampler w b fuel).law =
      (b : ℝ≥0∞) * ∑ t ∈ Finset.range fuel, rationalRejectMass w b ^ t ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (weightedSampler w b fuel).law
      (fun z => (rejectionComparisons z.1.1 : ℝ≥0∞)) =
      rationalMeanComparisons w b * ∑ t ∈ Finset.range fuel, rationalRejectMass w b ^ t := by
  have h := rational_finite_three_resource_expectations N w b fuel hW hb
  constructor
  · rw [weightedSampler_law, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    calc
      _ = (b : ℝ≥0∞) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (rationalRejectionRun w b fuel) := by
        simp only [Nat.cast_mul]
        exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul _ _ _
      _ = _ := by rw [h.1]
  · rw [weightedSampler_law, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    exact h.2.2.1

theorem weightedSampler_timeout_tendsto_zero {N : ℕ} (w : Fin N → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    Filter.Tendsto (fun fuel => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (weightedSampler w b fuel).law
      (fun z => rejectionOutcome z.1.1 = .inr ())) Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  simpa only [weightedSampler_law, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map] using
    (rational_unbounded_actual_first_stop_law N w b hW hb).2.2.2.1

noncomputable def weightedSamplerNever {N : ℕ} (w : Fin N → ℕ) (b : ℕ) : ℝ≥0∞ :=
  ⨅ fuel, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (weightedSampler w b fuel).law
    (fun z => rejectionOutcome z.1.1 = .inr ())

theorem weightedSamplerNever_eq_zero {N : ℕ} (w : Fin N → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    weightedSamplerNever w b = 0 := by
  apply le_antisymm ?_ bot_le
  exact ge_of_tendsto (weightedSampler_timeout_tendsto_zero w b hW hb)
    (Filter.Eventually.of_forall fun fuel => iInf_le _ fuel)

theorem weightedSampler_expected_reads_limit {N : ℕ} (w : Fin N → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    Filter.Tendsto (fun fuel => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (weightedSampler w b fuel).law)
      Filter.atTop (nhds ((b : ℝ≥0∞) / (1 - rationalRejectMass w b))) ∧
    (b : ℝ≥0∞) / (1 - rationalRejectMass w b) < ⊤ := by
  have h := rational_unbounded_expected_resources_and_limits N w b hW hb
  refine ⟨?_, h.2.2.2.1⟩
  have heq : (fun fuel => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (weightedSampler w b fuel).law) =
      (fun fuel => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalRejectionRun w b fuel)
        (fun z => (rejectionBits z.1 : ℝ≥0∞))) := by
    funext fuel
    rw [(weightedSampler_expectations w b fuel hW hb).1,
      (rational_finite_three_resource_expectations N w b fuel hW hb).2.1]
  rw [heq]
  exact h.2.2.2.2.2.2.1

theorem zeroWeight_zeroBit_loop (fuel : ℕ) (BD : ℕ × ℕ) :
    countedLoop (fun _ : Fin 1 => 0) 0 fuel (.inr BD) =
      .ret (.inr (BD.1, BD.2 + fuel), fuel) := by
  induction fuel generalizing BD with
  | zero => simp [countedLoop]
  | succ fuel ih =>
      have ht : countedTrialResult (fun _ : Fin 1 => 0) 0 BD (ZeroStr 0) =
          .inr (BD.1, BD.2 + 1) := rfl
      simp only [countedLoop, CoinCode.block, CoinCode.bind, ht, ih]
      simp [Nat.add_assoc, Nat.add_comm 1]

theorem zeroWeight_zeroBit_never :
    weightedSamplerNever (fun _ : Fin 1 => 0) 0 = 1 := by
  unfold weightedSamplerNever
  simp only [weightedSampler, zeroWeight_zeroBit_loop, CoinCode.law, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, rejectionOutcome, ite_true, iInf_const]

theorem feedbackTrial_law {S E : Type} {N : ℕ} (weights : S → Fin N → ℕ)
    (update : S → Fin N → S) (b : ℕ) (s : S) (env : E) :
    (feedbackTrial weights update b s env).law =
      (fairBitsCosted b).map (fun z =>
        let d := weightDecodeCounted (weights s) (bitVecEquiv b z.1).val
        ((d.1.elim s (update s), env, d.1, d.2), z.2)) := by
  rw [feedbackTrial, CoinCode.law_bind_ret, weightedTrial_law, PMF.map_comp]
  rfl

theorem sqrtWeight_interval (s a : ℕ) :
    (sqrtWeight s a : ℝ) ≤ (s : ℝ) * Real.sqrt a ∧
      (s : ℝ) * Real.sqrt a < (sqrtWeight s a : ℝ) + 1 := by
  have hlo : (sqrtWeight s a : ℝ) ^ 2 ≤ (a : ℝ) * (s : ℝ) ^ 2 := by
    exact_mod_cast Nat.sqrt_le' (a * s ^ 2)
  have hhi : (a : ℝ) * (s : ℝ) ^ 2 < ((sqrtWeight s a : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' (a * s ^ 2)
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  have hsq : ((s : ℝ) * Real.sqrt a) ^ 2 = (a : ℝ) * (s : ℝ) ^ 2 := by
    rw [mul_pow, hsqrt]; ring
  have hnon : 0 ≤ (s : ℝ) * Real.sqrt a := by positivity
  constructor <;> nlinarith [sq_nonneg ((sqrtWeight s a : ℝ) - (s : ℝ) * Real.sqrt a)]

theorem sqrtWeight_error (s a : ℕ) (hs : 0 < s) :
    0 ≤ Real.sqrt a - (sqrtWeight s a : ℝ) / s ∧
      Real.sqrt a - (sqrtWeight s a : ℝ) / s < 1 / (s : ℝ) := by
  have h := sqrtWeight_interval s a
  have hp : (0 : ℝ) < s := by exact_mod_cast hs
  constructor
  · apply sub_nonneg.mpr
    exact (div_le_iff₀ hp).mpr (by simpa [mul_comm] using h.1)
  · apply (lt_div_iff₀ hp).mpr
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hp)]
    nlinarith [h.2]

theorem sqrtWeight_positive (s a : ℕ) (hs : 0 < s) (ha : 0 < a) : 0 < sqrtWeight s a := by
  apply Nat.sqrt_pos.mpr
  exact Nat.mul_pos ha (Nat.pow_pos hs)

theorem normalized_subweight_event_error (u v U W : ℝ)
    (hU : 0 < U) (hUW : U ≤ W) (hu : 0 ≤ u) (huU : u ≤ U)
    (huv : u ≤ v) (hdiff : v - u ≤ W - U) :
    |u / U - v / W| ≤ (W - U) / W := by
  have hW : 0 < W := lt_of_lt_of_le hU hUW
  have hq : 0 ≤ W - U := sub_nonneg.mpr hUW
  have hnum : |u * W - v * U| ≤ U * (W - U) := by
    apply abs_le.mpr
    constructor
    · nlinarith [mul_nonneg hu hq, mul_le_mul_of_nonneg_left hdiff hU.le]
    · nlinarith [mul_nonneg hU.le (sub_nonneg.mpr huv),
        mul_le_mul_of_nonneg_right huU hq]
  calc
    |u / U - v / W| = |u * W - v * U| / (U * W) := by
      rw [div_sub_div _ _ (ne_of_gt hU) (ne_of_gt hW), abs_div, abs_of_pos (mul_pos hU hW),
          mul_comm U v]
    _ ≤ (U * (W - U)) / (U * W) := div_le_div_of_nonneg_right hnum (mul_pos hU hW).le
    _ = (W - U) / W := by field_simp

theorem normalized_underapprox_event_bound {N : ℕ} (u v : Fin N → ℝ) (δ : ℝ)
    (F : Finset (Fin N)) (hu : ∀ i, 0 ≤ u i) (huv : ∀ i, u i ≤ v i)
    (hδ : ∀ i, v i - u i ≤ δ) (hU : 1 ≤ ∑ i, u i) :
    |(∑ i ∈ F, u i) / (∑ i, u i) - (∑ i ∈ F, v i) / (∑ i, v i)| ≤ (N : ℝ) * δ := by
  have hUW : (∑ i, u i) ≤ ∑ i, v i := Finset.sum_le_sum fun i _ => huv i
  have hup : (0 : ℝ) < ∑ i, u i := lt_of_lt_of_le zero_lt_one hU
  have hwp : (0 : ℝ) < ∑ i, v i := lt_of_lt_of_le hup hUW
  have huf : 0 ≤ ∑ i ∈ F, u i := Finset.sum_nonneg fun i _ => hu i
  have hufU : (∑ i ∈ F, u i) ≤ ∑ i, u i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F) (fun i _ _ => hu i)
  have hufvf : (∑ i ∈ F, u i) ≤ ∑ i ∈ F, v i := Finset.sum_le_sum fun i _ => huv i
  have hd : (∑ i ∈ F, v i) - (∑ i ∈ F, u i) ≤ (∑ i, v i) - (∑ i, u i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
      (fun i _ _ => sub_nonneg.mpr (huv i))
  have herr : (∑ i, v i) - (∑ i, u i) ≤ (N : ℝ) * δ := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ _ : Fin N, δ := Finset.sum_le_sum fun i _ => hδ i
      _ = _ := by simp
  calc
    _ ≤ ((∑ i, v i) - (∑ i, u i)) / (∑ i, v i) :=
      normalized_subweight_event_error _ _ _ _ hup hUW huf hufU hufvf hd
    _ ≤ (∑ i, v i) - (∑ i, u i) := by
      apply (div_le_iff₀ hwp).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hUW) (sub_nonneg.mpr (hU.trans hUW))]
    _ ≤ _ := herr

theorem sqrtWeight_ge_scale (s a : ℕ) (ha : 0 < a) : s ≤ sqrtWeight s a := by
  apply Nat.le_sqrt'.mpr
  have h : 1 ≤ a := ha
  nlinarith [Nat.mul_le_mul_right (s ^ 2) h]

theorem sqrtWeight_event_error {N : ℕ} (a : Fin N → ℕ) (s : ℕ) (hs : 0 < s)
    (ha : ∃ i, 0 < a i) (F : Finset (Fin N)) :
    |(∑ i ∈ F, (sqrtWeight s (a i) : ℝ)) / (∑ i, (sqrtWeight s (a i) : ℝ)) -
      (∑ i ∈ F, Real.sqrt (a i)) / (∑ i, Real.sqrt (a i))| ≤ (N : ℝ) / s := by
  have hsp : (0 : ℝ) < s := by exact_mod_cast hs
  have hU : 1 ≤ ∑ i, (sqrtWeight s (a i) : ℝ) / s := by
    obtain ⟨i, hi⟩ := ha
    have hlo := sqrtWeight_ge_scale s (a i) hi
    calc
      1 ≤ (sqrtWeight s (a i) : ℝ) / s := by
        apply (le_div_iff₀ hsp).mpr
        simpa only [one_mul] using (show (s : ℝ) ≤ sqrtWeight s (a i) by exact_mod_cast hlo)
      _ ≤ _ := Finset.single_le_sum (f := fun j : Fin N => (sqrtWeight s (a j) : ℝ) / s)
        (fun j _ => div_nonneg (Nat.cast_nonneg _) hsp.le) (Finset.mem_univ i)
  have h := normalized_underapprox_event_bound
    (fun i => (sqrtWeight s (a i) : ℝ) / s) (fun i => Real.sqrt (a i)) (1 / (s : ℝ)) F
    (fun i => div_nonneg (Nat.cast_nonneg _) hsp.le)
    (fun i => sub_nonneg.mp (sqrtWeight_error s (a i) hs).1)
    (fun i => (sqrtWeight_error s (a i) hs).2.le) hU
  simp only [← Finset.sum_div] at h
  rw [div_div_div_cancel_right₀ (ne_of_gt hsp)] at h
  simpa only [mul_one_div] using h

theorem sqrtWeight_precision_event_error {N : ℕ} (a : Fin N → ℕ) (k : ℕ)
    (ha : ∃ i, 0 < a i) (F : Finset (Fin N)) :
    |(∑ i ∈ F, (sqrtWeight (sqrtPrecisionScale N k) (a i) : ℝ)) /
        (∑ i, (sqrtWeight (sqrtPrecisionScale N k) (a i) : ℝ)) -
      (∑ i ∈ F, Real.sqrt (a i)) / (∑ i, Real.sqrt (a i))| ≤ 1 / (2 : ℝ) ^ k := by
  have hs : 0 < sqrtPrecisionScale N k := by unfold sqrtPrecisionScale; positivity
  apply le_trans (sqrtWeight_event_error a _ hs ha F)
  unfold sqrtPrecisionScale
  push_cast
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]

theorem weightedSampler_set_return {N : ℕ} (w : Fin N → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) (F : Finset (Fin N)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (weightedSampler w b fuel).law (fun z => acceptedIn F z.1.1) =
      ((∑ j ∈ F, w j : ℕ) : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) *
        (1 - rationalRejectMass w b ^ fuel) := by
  have he : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (weightedSampler w b fuel).law (fun z => acceptedIn F z.1.1) =
      ∑ j ∈ F, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (weightedSampler w b fuel).law
        (fun z => rejectionOutcome z.1.1 = .inl j) := by
    unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
    rw [← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_sum]
    apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
    intro z
    rcases z with ⟨⟨out | pending, t⟩, reads⟩
    · simp [acceptedIn, rejectionOutcome, eq_comm]
    · simp [acceptedIn, rejectionOutcome]
  rw [he]
  simp only [weightedSampler_return w b fuel hW hb]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Nat.cast_sum]

theorem weightedSampler_set_return_real {N : ℕ} (w : Fin N → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) (F : Finset (Fin N)) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (weightedSampler w b fuel).law (fun z => acceptedIn F z.1.1)).toReal =
      ((∑ j ∈ F, w j : ℕ) : ℝ) / (weightTotal w : ℝ) *
        (1 - (rationalRejectMass w b).toReal ^ fuel) := by
  have hq : rationalRejectMass w b ^ fuel ≤ 1 := by
    rw [← weightedSampler_timeout w b fuel hb]
    exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _
  rw [weightedSampler_set_return w b fuel hW hb F, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_sub_of_le hq (by simp), ENNReal.toReal_pow]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_one]

theorem sqrtWeights_total_pos {N : ℕ} (a : Fin N → ℕ) (k : ℕ)
    (ha : ∃ i, 0 < a i) : 0 < weightTotal (sqrtWeights a k) := by
  obtain ⟨i, hi⟩ := ha
  have hs : 0 < sqrtPrecisionScale N k := by unfold sqrtPrecisionScale; positivity
  have hp : 0 < sqrtWeights a k i := sqrtWeight_positive _ _ hs hi
  exact lt_of_lt_of_le hp (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i))

theorem sqrtSampler_event_bias {N : ℕ} (a : Fin N → ℕ) (k fuel : ℕ)
    (ha : ∃ i, 0 < a i) (F : Finset (Fin N)) :
    |(Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sqrtSampler a k fuel).law (fun z => acceptedIn F z.1.1)).toReal -
        (∑ i ∈ F, Real.sqrt (a i)) / (∑ i, Real.sqrt (a i))| ≤
      1 / (2 : ℝ) ^ k + 1 / (2 : ℝ) ^ fuel := by
  let w := sqrtWeights a k
  let b := Nat.clog 2 (weightTotal w)
  have hW : 0 < weightTotal w := sqrtWeights_total_pos a k ha
  have hcap := finite_coin_effective_cutoff (weightTotal w) fuel hW
  have hb : weightTotal w ≤ 2 ^ b := hcap.1
  have hq : rationalRejectMass w b ≤ (1 : ℝ≥0∞) / 2 := hcap.2.1
  have hqr : (rationalRejectMass w b).toReal ≤ (1 : ℝ) / 2 := by
    have h := ENNReal.toReal_mono (by simp : (1 / 2 : ℝ≥0∞) ≠ ⊤) hq
    simpa using h
  let r : ℝ := (∑ i ∈ F, (w i : ℝ)) / (weightTotal w : ℝ)
  let v : ℝ := (∑ i ∈ F, Real.sqrt (a i)) / (∑ i, Real.sqrt (a i))
  let t : ℝ := (rationalRejectMass w b).toReal ^ fuel
  have ht : 0 ≤ t := pow_nonneg ENNReal.toReal_nonneg _
  have ht_bound : t ≤ 1 / (2 : ℝ) ^ fuel := by
    have h := pow_le_pow_left₀ ENNReal.toReal_nonneg hqr fuel
    simpa only [div_pow, one_pow] using h
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hW : (0 : ℝ) < weightTotal w)).mpr
    rw [weightTotal, Nat.cast_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
      (fun i _ _ => Nat.cast_nonneg _)
  have happ : |r - v| ≤ 1 / (2 : ℝ) ^ k := by
    simpa only [r, v, w, sqrtWeights, weightTotal, Nat.cast_sum] using
      sqrtWeight_precision_event_error a k ha F
  have he : (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sqrtSampler a k fuel).law
      (fun z => acceptedIn F z.1.1)).toReal = r * (1 - t) := by
    simpa only [sqrtSampler, r, w, b, t, Nat.cast_sum] using
      weightedSampler_set_return_real w b fuel hW hb F
  rw [he]
  change |r * (1 - t) - v| ≤ _
  have habs : |r * (1 - t) - r| = r * t := by
    rw [abs_of_nonpos (by nlinarith [mul_nonneg hr0 ht])]
    ring
  calc
    _ ≤ |r * (1 - t) - r| + |r - v| := abs_sub_le _ _ _
    _ = r * t + |r - v| := by rw [habs]
    _ ≤ t + 1 / (2 : ℝ) ^ k := add_le_add (mul_le_of_le_one_left ht hr1) happ
    _ ≤ _ := by linarith

theorem countedLoop_empty_zeroBit (fuel : ℕ) (BD : ℕ × ℕ) :
    countedLoop (fun _ : Fin 0 => 1) 0 fuel (.inr BD) = .ret (.inr BD,fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [countedLoop,CoinCode.block,CoinCode.bind]
      have hd : countedTrialResult (fun _ : Fin 0 => 1) 0 BD (ZeroStr 0) = .inr BD := by
        rcases BD with ⟨b,d⟩
        rfl
      rw [hd,ih]
      simp [CoinCode.bind,Nat.add_comm]

theorem weightedSampler_empty_zeroBit (cap : ℕ) :
    weightedSampler (fun _ : Fin 0 => 1) (Nat.clog 2 0) cap = .ret (.inr (0,0),cap) := by
  have hw : Nat.clog 2 0 = 0 := by decide +kernel
  rw [weightedSampler,hw,countedLoop_empty_zeroBit]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
