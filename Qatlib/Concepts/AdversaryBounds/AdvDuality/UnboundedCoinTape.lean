/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralUnboundedExecution
import Qatlib.Concepts.ClassicalTape.FairCoinTape
import Mathlib.Probability.Distributions.Uniform
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.RealMass
set_option warningAsError false

open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.StoppingCore.BranchCostCore

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal Classical

def coinTapeNormalize (q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q+1)))
    (accept : Fin (q+1) → Bool) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q+1))) :
    Bool ⊕ Turing.TM0.Cfg (Option Bool) (Fin (q+1)) :=
  if coinHalt M cfg then Sum.inl (accept cfg.q) else Sum.inr cfg

def coinTapeSelected (q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q+1)))
    (accept : Fin (q+1) → Bool) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q+1)))
    (c : Bool) : Bool ⊕ Turing.TM0.Cfg (Option Bool) (Fin (q+1)) :=
  match Turing.TM0.step (M c) cfg with
  | none => Sum.inl (accept cfg.q)
  | some cfg' => coinTapeNormalize q M accept cfg'

noncomputable def coinTapeKernel (q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q+1)))
    (accept : Fin (q+1) → Bool) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q+1))) :
    PMF (Bool ⊕ Turing.TM0.Cfg (Option Bool) (Fin (q+1))) :=
  (PMF.bernoulli (1/2) (by norm_num)).map (coinTapeSelected q M accept cfg)

def coinTapeObserve {q : ℕ}
    (x : (Bool ⊕ Turing.TM0.Cfg (Option Bool) (Fin (q+1))) × ℕ) : Option Bool × ℕ :=
  (match x.1 with | Sum.inl b => some b | Sum.inr _ => none, x.2)

private theorem fairBit_uniform :
    PMF.bernoulli (1/2) (by norm_num) = PMF.uniformOfFintype' Bool := by
  ext b
  cases b <;> norm_num [PMF.bernoulli_apply, PMF.uniformOfFintype'_apply]

private theorem uniform_bits_cons (n : ℕ) :
    PMF.uniformOfFintype' (Fin (n+1) → Bool) =
      (PMF.bernoulli (1/2) (by norm_num)).bind
        (fun c => (PMF.uniformOfFintype' (Fin n → Bool)).map (Fin.cons c)) := by
  ext w
  rw [PMF.bind_apply, fairBit_uniform]
  simp_rw [PMF.map_apply]
  have he : ∀ c v, w = Fin.cons c v ↔ w 0 = c ∧ Fin.tail w = v := by
    intro c v
    conv_lhs => rw [← Fin.cons_self_tail w, Fin.cons_inj]
  simp_rw [he]
  cases w 0 <;> simp [PMF.uniformOfFintype'_apply, pow_succ,
    ENNReal.mul_inv, mul_comm]

private theorem observe_charge {q : ℕ}
    (p : CostedLaw (Bool ⊕ Turing.TM0.Cfg (Option Bool) (Fin (q+1)))) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 p).map coinTapeObserve =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (p.map coinTapeObserve) := by
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge, PMF.map_comp]
  rfl

theorem coinTape_observed_law (q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q+1)))
    (accept : Fin (q+1) → Bool) (n : ℕ)
    (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q+1))) :
    (runFor (coinTapeKernel q M accept) n (coinTapeNormalize q M accept cfg)).map
      coinTapeObserve = (PMF.uniformOfFintype' (Fin n → Bool)).map
        (fun w => coinTapeRunAux M accept (List.ofFn w) cfg) := by
  induction n generalizing cfg with
  | zero =>
    have hconst : ∀ w : Fin 0 → Bool, List.ofFn w = [] := fun _ => rfl
    simp only [hconst, coinTapeRunAux, coinTapeNormalize]
    split <;> simp only [runFor_zero, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_map, coinTapeObserve]
      <;> exact (PMF.map_const _ _).symm
  | succ n ih =>
    by_cases hh : coinHalt M cfg = true
    · simp only [coinTapeNormalize, hh, if_true, runFor_halted, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret,
        PMF.pure_map, coinTapeObserve]
      simp only [coinTapeRunAux_of_coinHalt M accept _ cfg hh]
      exact (PMF.map_const _ _).symm
    · rw [coinTapeNormalize, if_neg hh, runFor]
      have hstep : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (tick (coinTapeKernel q M accept) (Sum.inr cfg))
          (runFor (coinTapeKernel q M accept) n) =
          (PMF.bernoulli (1/2) (by norm_num)).bind (fun c =>
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (runFor (coinTapeKernel q M accept) n
              (coinTapeSelected q M accept cfg c))) := by
        simp [tick, coinTapeKernel, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind,
            PMF.bind_map, Function.comp_def]
      rw [hstep, PMF.map_bind, uniform_bits_cons, PMF.map_bind]
      congr 1
      funext c
      rw [PMF.map_comp]
      cases hs : Turing.TM0.step (M c) cfg with
      | none =>
        simp [coinTapeSelected, hs, runFor_halted, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret,
          PMF.pure_map, coinTapeObserve, Function.comp_def, coinTapeRunAux, hh]
        exact (PMF.map_const _ _).symm
      | some cfg' =>
        simp only [coinTapeSelected, hs]
        rw [observe_charge, ih]
        simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge, PMF.map_comp, Function.comp_def, List.ofFn_cons,
          coinTapeRunAux, if_neg hh, hs]
        congr 1
        funext w
        simp [Prod.map, Nat.add_comm]

private theorem uniform_bits_expectation (T : ℕ) (f : (Fin T → Bool) → ℝ)
    (hf : ∀ w, 0 ≤ f w) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (PMF.uniformOfFintype' (Fin T → Bool))
      (fun w => ENNReal.ofReal (f w)) = ENNReal.ofReal ((∑ w, f w) / (2 : ℝ)^T) := by
  rw [Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw.expectation_ofReal_fintype _ _ hf]
  congr 1
  simp only [PMF.uniformOfFintype'_apply, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, div_eq_mul_inv]
  rw [← Finset.mul_sum]
  ring

private theorem uniform_bits_event (T : ℕ) (E : (Fin T → Bool) → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (PMF.uniformOfFintype' (Fin T → Bool)) E =
      ENNReal.ofReal ((∑ w, if E w then (1 : ℝ) else 0) / (2 : ℝ)^T) := by
  classical
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq]
  have h : (fun w => if E w then (1 : ℝ≥0∞) else 0) =
      (fun w => ENNReal.ofReal (if E w then (1 : ℝ) else 0)) := by
    funext w
    split_ifs <;> simp
  rw [h]
  exact uniform_bits_expectation T _ (fun w => by split_ifs <;> norm_num)

theorem coinTape_observe_point {q : ℕ}
    (p : CostedLaw (Bool ⊕ Turing.TM0.Cfg (Option Bool) (Fin (q+1)))) (b : Bool) (k : ℕ) :
    (p.map coinTapeObserve) (some b, k) = p (Sum.inl b, k) := by
  rw [← event_point_mass, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map,
      ← event_point_mass p]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr
  rintro ⟨c, j⟩
  cases c <;> simp [coinTapeObserve]

theorem unbounded_coin_tape_actual_finite_coin_bridge :
    ∀ (q : ℕ) (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q+1)))
      (accept : Fin (q+1) → Bool) (input : List Bool) (T : ℕ),
      (∀ ql γ, (M false ql γ = none) ↔ (M true ql γ = none)) →
      let next := coinTapeKernel q M accept
      let cfg := coinTapeNormalize q M accept (Turing.TM0.init (input.map some))
      (∀ (b : Bool) (k : ℕ), runFor next T cfg (Sum.inl b,k) =
        ENNReal.ofReal ((∑ w : Fin T → Bool,
          if coinTapeRun M accept (input.map some) (List.ofFn w) = (some b,k)
          then (1 : ℝ) else 0) / (2 : ℝ)^T)) ∧
      generalPendingMass next cfg T = ENNReal.ofReal
        (1 - fairTapeSuccess M accept (input.map some) T true -
          fairTapeSuccess M accept (input.map some) T false) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (runFor next T cfg) = ENNReal.ofReal
        ((∑ w : Fin T → Bool,
          ((coinTapeRun M accept (input.map some) (List.ofFn w)).2 : ℝ)) / (2 : ℝ)^T) := by
  classical
  intro q M accept input T _
  (try dsimp only)
  let p := runFor (coinTapeKernel q M accept) T
    (coinTapeNormalize q M accept (Turing.TM0.init (input.map some)))
  have hlaw : p.map coinTapeObserve = (PMF.uniformOfFintype' (Fin T → Bool)).map
      (fun w => coinTapeRun M accept (input.map some) (List.ofFn w)) :=
    coinTape_observed_law q M accept T _
  refine ⟨?_, ?_, ?_⟩
  · intro b k
    rw [← coinTape_observe_point p b k, hlaw, ← event_point_mass, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map,
      uniform_bits_event]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    simp [eq_comm]
  · have hpend : generalPendingMass (coinTapeKernel q M accept)
        (coinTapeNormalize q M accept (Turing.TM0.init (input.map some))) T =
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (p.map coinTapeObserve) (fun z => z.1 = none) := by
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
      apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr
      rintro ⟨c,j⟩
      cases c <;> simp [coinTapeObserve]
    rw [hpend, hlaw, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map,
        uniform_bits_event]
    congr 1
    let r := fun w : Fin T → Bool => coinTapeRun M accept (input.map some) (List.ofFn w)
    calc
      _ = (∑ w : Fin T → Bool, (1 -
          (if (r w).1 = some true then (1 : ℝ) else 0) -
          (if (r w).1 = some false then (1 : ℝ) else 0))) / 2^T := by
        congr 1
        apply Finset.sum_congr rfl
        intro w _
        cases ho : (coinTapeRun M accept (input.map some) (List.ofFn w)).1 with
        | none => simp
        | some b => cases b <;> simp
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_one]
        unfold fairTapeSuccess
        dsimp [r]
        have hp : (2 : ℝ)^T ≠ 0 := pow_ne_zero _ (by norm_num)
        field_simp
  · have he : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost p = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (p.map coinTapeObserve) := by
      simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map, coinTapeObserve]
    rw [he, hlaw, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    convert uniform_bits_expectation T
      (fun w => ((coinTapeRun M accept (input.map some) (List.ofFn w)).2 : ℝ))
      (fun _ => Nat.cast_nonneg _) using 1
    simp

theorem coinTape_success_mass (q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q+1)))
    (accept : Fin (q+1) → Bool) (input : List Bool) (T : ℕ) (b : Bool) :
    (∑ k ∈ Finset.range (T+1), haltJoint (coinTapeKernel q M accept)
      (coinTapeNormalize q M accept (Turing.TM0.init (input.map some))) b k) =
      ENNReal.ofReal (fairTapeSuccess M accept (input.map some) T b) := by
  rw [← general_finite_output_mass]
  have h : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      ((runFor (coinTapeKernel q M accept) T
        (coinTapeNormalize q M accept (Turing.TM0.init (input.map some)))).map coinTapeObserve)
      (fun z => z.1 = some b) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (coinTapeKernel q M accept) T
        (coinTapeNormalize q M accept (Turing.TM0.init (input.map some))))
        (fun z => z.1 = Sum.inl b) := by
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
    apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr
    rintro ⟨c,j⟩
    cases c <;> simp [coinTapeObserve]
  rw [← h, coinTape_observed_law, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map,
      uniform_bits_event]
  unfold fairTapeSuccess coinTapeRun
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  by_cases hx : (coinTapeRunAux M accept (List.ofFn w) (Turing.TM0.init (input.map some))).1 = some b
  · simp [hx]
  · simp [hx]

theorem coinTape_zero_pending (q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q+1)))
    (accept : Fin (q+1) → Bool) (input : List Bool) (T : ℕ)
    (h : ∀ w : Fin T → Bool,
      (coinTapeRun M accept (input.map some) (List.ofFn w)).1 ≠ none) :
    generalPendingMass (coinTapeKernel q M accept)
      (coinTapeNormalize q M accept (Turing.TM0.init (input.map some))) T = 0 := by
  have he : generalPendingMass (coinTapeKernel q M accept)
      (coinTapeNormalize q M accept (Turing.TM0.init (input.map some))) T =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        ((runFor (coinTapeKernel q M accept) T
          (coinTapeNormalize q M accept (Turing.TM0.init (input.map some)))).map coinTapeObserve)
        (fun z => z.1 = none) := by
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
    apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr
    rintro ⟨c,j⟩
    cases c <;> simp [coinTapeObserve]
  rw [he, coinTape_observed_law, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_zero _ _ h

theorem coinTapeNormalize_running (q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q+1)))
    (accept : Fin (q+1) → Bool) (cfg cfg' : Turing.TM0.Cfg (Option Bool) (Fin (q+1)))
    (h : coinTapeNormalize q M accept cfg = Sum.inr cfg') : coinHalt M cfg' = false := by
  unfold coinTapeNormalize at h
  split at h
  · cases h
  · have he : cfg = cfg' := Sum.inr.inj h
    subst cfg'
    exact Bool.eq_false_iff.mpr ‹¬coinHalt M cfg = true›

theorem coinTapeKernel_running (q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q+1)))
    (accept : Fin (q+1) → Bool) (cfg cfg' : Turing.TM0.Cfg (Option Bool) (Fin (q+1)))
    (h : Sum.inr cfg' ∈ (coinTapeKernel q M accept cfg).support) : coinHalt M cfg' = false := by
  obtain ⟨c,_,hc⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  unfold coinTapeSelected at hc
  cases hs : Turing.TM0.step (M c) cfg with
  | none => simp [hs] at hc
  | some cfg'' =>
    simp only [hs] at hc
    exact coinTapeNormalize_running q M accept cfg'' cfg' hc

theorem coinTapeRun_running (q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q+1)))
    (accept : Fin (q+1) → Bool) (T : ℕ)
    (cfg cfg' : Turing.TM0.Cfg (Option Bool) (Fin (q+1))) (k : ℕ)
    (h : (Sum.inr cfg',k) ∈
      (runFor (coinTapeKernel q M accept) T (coinTapeNormalize q M accept cfg)).support) :
    coinHalt M cfg' = false := by
  have hinv : ∀ (n : ℕ) (c : Bool ⊕ Turing.TM0.Cfg (Option Bool) (Fin (q+1))),
      (∀ s, c = Sum.inr s → coinHalt M s = false) →
      ∀ s j, (Sum.inr s,j) ∈ (runFor (coinTapeKernel q M accept) n c).support →
        coinHalt M s = false := by
    intro n
    induction n with
    | zero =>
      intro c hc s j hs
      have he : (Sum.inr s,j) = (c,0) := (PMF.mem_support_pure_iff _ _).mp hs
      exact hc s (congrArg Prod.fst he).symm
    | succ n ih =>
      intro c hc s j hs
      cases c with
      | inl b => simp [runFor_halted, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret] at hs
      | inr state =>
        change (Sum.inr s,j) ∈ (PMF.bind (tick (coinTapeKernel q M accept) (Sum.inr state))
          (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor (coinTapeKernel q M accept) n x.1))).support at hs
        obtain ⟨x,hx,hcont⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
        obtain ⟨d,hd,hxd⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
        subst x
        obtain ⟨y,hy,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hcont
        have he1 : y.1 = Sum.inr s := congrArg Prod.fst he
        have hi : ∀ t, d = Sum.inr t → coinHalt M t = false := by
          intro t ht
          exact coinTapeKernel_running q M accept state t (ht ▸ hd)
        have hy' : (Sum.inr s,y.2) ∈ (runFor (coinTapeKernel q M accept) n d).support :=
          he1 ▸ hy
        exact ih d hi s y.2 hy'
  exact hinv T _ (fun s hs => coinTapeNormalize_running q M accept cfg s hs) cfg' k h

theorem coinTape_step_none_common (q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q+1)))
    (hcommon : ∀ ql γ, (M false ql γ = none) ↔ (M true ql γ = none))
    (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q+1))) (c : Bool)
    (hs : Turing.TM0.step (M c) cfg = none) : coinHalt M cfg = true := by
  have hm := (TM0_step_eq_none (M c) cfg).mp hs
  have hf : M false cfg.q cfg.Tape.head = none := by
    cases c
    · exact hm
    · exact (hcommon _ _).mpr hm
  have ht := (hcommon _ _).mp hf
  simp [coinHalt, hf, ht]

theorem coinTape_transitionCount_eq_reads (q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q+1)))
    (accept : Fin (q+1) → Bool)
    (hcommon : ∀ ql γ, (M false ql γ = none) ↔ (M true ql γ = none)) :
    ∀ (coins : List Bool) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q+1))),
      coinTapeTransitionCountAux M coins cfg = (coinTapeRunAux M accept coins cfg).2 := by
  intro coins
  induction coins with
  | nil => intro cfg; simp [coinTapeTransitionCountAux, coinTapeRunAux]; split <;> rfl
  | cons c coins ih =>
    intro cfg
    by_cases hh : coinHalt M cfg = true
    · simp [coinTapeTransitionCountAux, coinTapeRunAux, hh]
    · cases hs : Turing.TM0.step (M c) cfg with
      | none => exact False.elim (hh (coinTape_step_none_common q M hcommon cfg c hs))
      | some cfg' =>
        simp [coinTapeTransitionCountAux, coinTapeRunAux, hh, hs, Prod.map, ih cfg']

end Qatlib.Concepts.AdversaryBounds.AdvDuality
