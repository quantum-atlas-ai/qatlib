/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.RationalReject.CountedWeightedDecoder
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
set_option warningAsError false
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline

namespace Qatlib.Concepts.FairRandomBits.RationalReject

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal Classical

section Helpers

variable {N : ℕ}

private theorem card_interval (M a len : ℕ) (h : a + len ≤ M) :
    (Finset.univ.filter (fun u : Fin M => a ≤ u.val ∧ u.val < a + len)).card = len := by
  refine Finset.card_eq_of_bijective
    (s := Finset.univ.filter fun u : Fin M => a ≤ u.val ∧ u.val < a + len) (n := len)
    (fun i hi => ⟨a + i, by omega⟩) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine ⟨u.val - a, by omega, ?_⟩
    exact Fin.ext (by simp; omega)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro i j _ _ hij
    have h := congrArg Fin.val hij
    simp only at h
    omega

private theorem card_filter_ge (M k : ℕ) (hk : k ≤ M) :
    (Finset.univ.filter (fun u : Fin M => k ≤ u.val)).card = M - k := by
  refine Finset.card_eq_of_bijective
    (s := Finset.univ.filter fun u : Fin M => k ≤ u.val) (n := M - k)
    (fun i hi => ⟨k + i, by omega⟩) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine ⟨u.val - k, by omega, ?_⟩
    exact Fin.ext (by simp; omega)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro i j _ _ hij
    have h := congrArg Fin.val hij
    simp only at h
    omega

private theorem tsum_eq_filter_sum {α : Type} [Fintype α] (F : α → ℝ≥0∞) (P : α → Prop)
    [DecidablePred P] (h0 : ∀ x, ¬ P x → F x = 0) :
    ∑' x : α, F x = ∑ x ∈ Finset.univ.filter P, F x := by
  classical
  rw [tsum_fintype]
  have hU : ((Finset.univ.filter P) ∪ (Finset.univ.filter fun x => ¬ P x)) = Finset.univ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_union, true_and]
    by_cases hP : P x <;> simp [hP]
  have hD : Disjoint (Finset.univ.filter P) (Finset.univ.filter fun x => ¬ P x) := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha1 ha2
    exact ha2 ha1
  calc ∑ x ∈ Finset.univ, F x
      = ∑ x ∈ (Finset.univ.filter P ∪ Finset.univ.filter fun x => ¬ P x), F x := by rw [hU]
    _ = ∑ x ∈ Finset.univ.filter P, F x + ∑ x ∈ Finset.univ.filter fun x => ¬ P x, F x :=
      Finset.sum_union hD
    _ = ∑ x ∈ Finset.univ.filter P, F x + 0 := by
        congr 1
        refine Finset.sum_eq_zero fun x hx => h0 x ?_
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx
    _ = _ := by rw [add_zero]

private theorem event_or {α : Type} (p : PMF α) (A B : α → Prop)
    (hd : ∀ x, ¬ (A x ∧ B x)) :
    CostedLaw.event p (fun x => A x ∨ B x) = CostedLaw.event p A + CostedLaw.event p B := by
  rw [CostedLaw.event_eq, CostedLaw.event_eq, CostedLaw.event_eq]
  refine Eq.trans (CostedLaw.expectation_congr fun x => ?_) (CostedLaw.expectation_add p _ _)
  by_cases hA : A x
  · have hB : ¬ B x := fun hb => hd x ⟨hA, hb⟩
    simp [hA, hB]
  · by_cases hB : B x
    · simp [hA, hB]
    · simp [hA, hB]

private theorem event_support_zero {α : Type} (p : PMF α) (E : α → Prop)
    (h : ∀ x ∈ p.support, ¬ E x) : CostedLaw.event p E = 0 := by
  classical
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  show p x * (if E x then (1 : ℝ≥0∞) else 0) = 0
  by_cases hx : E x
  · by_cases hp0 : p x = 0
    · rw [hp0, zero_mul]
    · exact (h x ((PMF.mem_support_iff p x).mpr hp0) hx).elim
  · simp [hx]

private theorem costedCharge_bind_pmf (n : ℕ) {α β : Type} (p : PMF α)
    (q : α → PMF (β × ℕ)) :
    CostedLaw.charge n (PMF.bind p q) = PMF.bind p (fun a => CostedLaw.charge n (q a)) := by
  show (PMF.bind p q).map (fun y => (y.1, n + y.2)) = _
  rw [PMF.map_bind]
  exact congrArg _ (funext fun a => rfl)

private theorem costedCharge_bind (n : ℕ) {α β : Type} (p : CostedLaw α)
    (f : α → CostedLaw β) :
    CostedLaw.charge n (CostedLaw.bind p f) =
      CostedLaw.bind p (fun a => CostedLaw.charge n (f a)) := by
  show CostedLaw.charge n (PMF.bind p (fun x => CostedLaw.charge x.2 (f x.1))) = _
  rw [costedCharge_bind_pmf]
  exact congrArg _ (funext fun x => by
    rw [CostedLaw.charge_charge, CostedLaw.charge_charge, Nat.add_comm])

private theorem map_charge_shift {α β : Type} (q : PMF (α × ℕ)) (f : α → β) (n : ℕ) :
    q.map (fun y => (f y.1, n + y.2)) = CostedLaw.charge n (q.map fun y => (f y.1, y.2)) := by
  rw [CostedLaw.charge, PMF.map_comp]
  rfl

private theorem pmf_map_congr_support {α β : Type} {p : PMF α} {f g : α → β}
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  refine PMF.ext fun z => ?_
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun x => ?_
  by_cases hp : p x = 0
  · simp [hp]
  · rw [h x ((PMF.mem_support_iff p x).mpr hp)]

private theorem card_filter_reg {b : ℕ} (P : Reg b → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun u : Fin (2 ^ b) => P ((bitVecEquiv b).symm u))).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.subtypeEquiv (bitVecEquiv b) fun a => by
    simp)

end Helpers

section OneTrial

variable {N : ℕ}

private def weightStep (w : Fin N → ℕ) (b : ℕ) (bits : Reg b) :
    RandomizedExecution.Configuration Unit (Fin N) :=
  match (weightDecodeCounted w (bitVecEquiv b bits).val).1 with
  | some j => Sum.inl j
  | none => Sum.inr ()

private theorem weightStep_inl {N : ℕ} (w : Fin N → ℕ) (b : ℕ) (bits : Reg b) (j : Fin N) :
    weightStep w b bits = Sum.inl j ↔
      (weightDecodeCounted w (bitVecEquiv b bits).val).1 = some j := by
  show (match (weightDecodeCounted w (bitVecEquiv b bits).val).1 with
      | some i => Sum.inl i
      | none => Sum.inr ()) = Sum.inl j ↔
    (weightDecodeCounted w (bitVecEquiv b bits).val).1 = some j
  cases hd : (weightDecodeCounted w (bitVecEquiv b bits).val).1 with
  | some i => simp
  | none => simp

private theorem weightStep_inr {N : ℕ} (w : Fin N → ℕ) (b : ℕ) (bits : Reg b) :
    weightStep w b bits = Sum.inr () ↔
      (weightDecodeCounted w (bitVecEquiv b bits).val).1 = none := by
  show (match (weightDecodeCounted w (bitVecEquiv b bits).val).1 with
      | some i => Sum.inl i
      | none => Sum.inr ()) = Sum.inr () ↔
    (weightDecodeCounted w (bitVecEquiv b bits).val).1 = none
  cases hd : (weightDecodeCounted w (bitVecEquiv b bits).val).1 with
  | some i => simp
  | none => simp

noncomputable def rationalRejectMass (w : Fin N → ℕ) (b : ℕ) : ℝ≥0∞ :=
  coinRejectMass b (weightTotal w)

noncomputable def rationalRejectionNext (w : Fin N → ℕ) (b : ℕ) :
    Unit → PMF (RandomizedExecution.Configuration Unit (Fin N)) :=
  fun _ => ((fairBitsCosted b).map Prod.fst).map (weightStep w b)

theorem rationalRejectionNext_eq (w : Fin N → ℕ) (b : ℕ) :
    rationalRejectionNext w b () = (PMF.uniformOfFintype' (Reg b)).map (weightStep w b) := by
  simp only [rationalRejectionNext, fairBitsCosted_output]

theorem rational_fair_bit_step_distribution :
    ∀ (N : ℕ) (w : Fin N → ℕ) (b : ℕ), weightTotal w ≤ 2 ^ b →
      (∀ j : Fin N, (Finset.univ.filter (fun bits : Reg b =>
        (weightDecodeCounted w (bitVecEquiv b bits).val).1 = some j)).card = w j) ∧
      (Finset.univ.filter (fun bits : Reg b =>
        (weightDecodeCounted w (bitVecEquiv b bits).val).1 = none)).card = 2^b - weightTotal w ∧
      (∀ j : Fin N, rationalRejectionNext w b () (Sum.inl j) =
        (w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)) ∧
      rationalRejectionNext w b () (Sum.inr ()) = rationalRejectMass w b := by
  intro N w b hb
  have hu : ∀ bits : Reg b, (PMF.uniformOfFintype' (Reg b)) bits
      = ((2^b : ℕ) : ℝ≥0∞)⁻¹ := fun bits => by
    rw [PMF.uniformOfFintype'_apply, card_reg]
  have fiberSome : ∀ j : Fin N,
      (Finset.univ.filter (fun bits : Reg b =>
        (weightDecodeCounted w (bitVecEquiv b bits).val).1 = some j)).card = w j := by
    intro j
    have hj : weightPrefix w j + w j ≤ 2 ^ b := by
      have h1 := weightPrefix_add_le w j
      omega
    rw [card_filter_reg]
    rw [Finset.filter_congr (fun (u : Fin (2 ^ b)) (_ : u ∈ Finset.univ) => by
      simp only [Equiv.apply_symm_apply]
      exact weightDecodeCounted_some_iff w u.val j)]
    rw [card_interval (2 ^ b) (weightPrefix w j) (w j) hj]
  have fiberNone :
      (Finset.univ.filter (fun bits : Reg b =>
        (weightDecodeCounted w (bitVecEquiv b bits).val).1 = none)).card
        = 2^b - weightTotal w := by
    rw [card_filter_reg]
    rw [Finset.filter_congr (fun (u : Fin (2 ^ b)) (_ : u ∈ Finset.univ) => by
      simp only [Equiv.apply_symm_apply]
      exact weightDecodeCounted_none_iff w u.val)]
    rw [card_filter_ge (2 ^ b) (weightTotal w) hb]
  refine ⟨fiberSome, fiberNone, ?_, ?_⟩
  · intro j
    rw [rationalRejectionNext_eq, PMF.map_apply]
    rw [tsum_congr (g := fun bits : Reg b =>
      ((2^b : ℕ) : ℝ≥0∞)⁻¹ * (if weightStep w b bits = Sum.inl j then (1 : ℝ≥0∞) else 0))
      (fun bits => by
        beta_reduce
        have hun := hu bits
        by_cases hc : weightStep w b bits = Sum.inl j
        · rw [if_pos (show Sum.inl j = weightStep w b bits from hc.symm), hun, if_pos hc,
            mul_one]
        · rw [if_neg (fun h => hc h.symm), if_neg hc, mul_zero])]
    rw [ENNReal.tsum_mul_left]
    rw [tsum_eq_filter_sum (fun bits => (if weightStep w b bits = Sum.inl j then (1 : ℝ≥0∞) else 0))
      (fun bits => (weightDecodeCounted w (bitVecEquiv b bits).val).1 = some j)]
    · rw [Finset.sum_congr rfl (fun bits hbits => if_pos
        ((weightStep_inl w b bits j).mpr (by
          simp [Finset.mem_filter, Finset.mem_univ] at hbits; exact hbits))),
        Finset.sum_const, fiberSome j, Nat.smul_one_eq_cast, div_eq_mul_inv, mul_comm]
    · intro bits hnot
      rw [if_neg fun hc => hnot ((weightStep_inl w b bits j).mp hc)]
  · rw [rationalRejectionNext_eq, PMF.map_apply]
    rw [tsum_congr (g := fun bits : Reg b =>
      ((2^b : ℕ) : ℝ≥0∞)⁻¹ * (if weightStep w b bits = Sum.inr () then (1 : ℝ≥0∞) else 0))
      (fun bits => by
        beta_reduce
        have hun := hu bits
        by_cases hc : weightStep w b bits = Sum.inr ()
        · rw [if_pos (show Sum.inr () = weightStep w b bits from hc.symm), hun, if_pos hc,
            mul_one]
        · rw [if_neg (fun h => hc h.symm), if_neg hc, mul_zero])]
    rw [ENNReal.tsum_mul_left]
    rw [tsum_eq_filter_sum (fun bits => (if weightStep w b bits = Sum.inr () then (1 : ℝ≥0∞) else 0))
      (fun bits => (weightDecodeCounted w (bitVecEquiv b bits).val).1 = none)]
    · rw [Finset.sum_congr rfl (fun bits hbits => if_pos
        ((weightStep_inr w b bits).mpr (by
          simp [Finset.mem_filter, Finset.mem_univ] at hbits; exact hbits))),
        Finset.sum_const, fiberNone, Nat.smul_one_eq_cast,
        rationalRejectMass, coinRejectMass, div_eq_mul_inv, mul_comm]
    · intro bits hnot
      rw [if_neg fun hc => hnot ((weightStep_inr w b bits).mp hc)]

end OneTrial

section RunHelpers

variable {S O : Type}

private theorem pmf_map_map {α β γ : Type} (r : PMF α) (g : α → β) (h : β → γ) :
    (r.map g).map h = r.map (fun a => h (g a)) := by
  rw [PMF.map_comp g r h, Function.comp_def]

private theorem charge_map_comm (r : PMF (S × ℕ)) (f : S → O) (c : ℕ) :
    (CostedLaw.charge c r).map (fun y => (f y.1, y.2)) =
      CostedLaw.charge c (r.map fun y => (f y.1, y.2)) := by
  show (r.map (fun y => (y.1, c + y.2))).map (fun y => (f y.1, y.2)) = _
  rw [CostedLaw.charge,
    pmf_map_map r (fun y => (y.1, c + y.2)) (fun y => (f y.1, y.2)),
    pmf_map_map r (fun y => (f y.1, y.2)) (fun x => (x.1, c + x.2))]

private theorem expectation_runFor_succ (n : S → PMF (Configuration S O)) (fuel : ℕ)
    (cfg : Configuration S O) (F : Configuration S O × ℕ → ℝ≥0∞) :
    CostedLaw.expectation (runFor n (fuel + 1) cfg) F =
      CostedLaw.expectation (tick n cfg)
        (fun x => CostedLaw.expectation (runFor n fuel x.1) (fun z => F (z.1, x.2 + z.2))) := by
  show CostedLaw.expectation (CostedLaw.bind (tick n cfg) (runFor n fuel)) F = _
  rw [CostedLaw.bind, CostedLaw.expectation_bind]
  exact congrArg _ (funext fun x => by
    show CostedLaw.expectation (CostedLaw.charge x.2 (runFor n fuel x.1)) F = _
    rw [CostedLaw.charge, CostedLaw.expectation_map])

private theorem tsum_eq_range_sum_aux : ∀ (fuel : ℕ) (F : ℕ → ℝ≥0∞),
    (∀ k, fuel ≤ k → F k = 0) → ∑' k : ℕ, F k = ∑ k ∈ Finset.range fuel, F k := by
  intro fuel
  induction fuel with
  | zero =>
      intro F h
      rw [Finset.sum_range_zero]
      exact ENNReal.tsum_eq_zero.mpr fun k => h k (Nat.zero_le k)
  | succ fuel ih =>
      intro F h
      have ih' : ∑' k : ℕ, F (k + 1) = ∑ k ∈ Finset.range fuel, F (k + 1) :=
        ih (fun k => F (k + 1)) fun k hk => h (k + 1) (by omega)
      calc ∑' k : ℕ, F k = F 0 + ∑' k : ℕ, F (k + 1) :=
          tsum_eq_zero_add' ENNReal.summable
        _ = F 0 + ∑ k ∈ Finset.range fuel, F (k + 1) := by rw [ih']
        _ = ∑ k ∈ Finset.range (fuel + 1), F k := by rw [Finset.sum_range_succ', add_comm]

private theorem tsum_eq_range_sum (F : ℕ → ℝ≥0∞) (fuel : ℕ) (h0 : ∀ k, fuel ≤ k → F k = 0) :
    ∑' k : ℕ, F k = ∑ k ∈ Finset.range fuel, F k :=
  tsum_eq_range_sum_aux fuel F h0

private theorem event_point {α : Type} (p : PMF α) (a : α) :
    CostedLaw.event p (fun z => z = a) = p a := by
  show ∑' z, p z * (if z = a then (1 : ℝ≥0∞) else 0) = p a
  rw [tsum_eq_single a (fun z hz => by rw [if_neg hz, mul_zero])]
  simp

end RunHelpers

section Counted

variable {N : ℕ}

private def trialStep (w : Fin N → ℕ) (b : ℕ) (BD : ℕ × ℕ) (ω : Reg b × ℕ) :
    RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) :=
  let decoded := weightDecodeCounted w (bitVecEquiv b ω.1).val
  match decoded.1 with
  | some j => Sum.inl (j, BD.1 + ω.2, BD.2 + decoded.2)
  | none => Sum.inr (BD.1 + ω.2, BD.2 + decoded.2)

private theorem trialStep_inl (w : Fin N → ℕ) (b : ℕ) (BD : ℕ × ℕ) (ω : Reg b × ℕ) (j : Fin N)
    (hj : (weightDecodeCounted w (bitVecEquiv b ω.1).val).1 = some j) :
    trialStep w b BD ω = Sum.inl (j, BD.1 + ω.2, BD.2 + (j.val + 1)) := by
  dsimp only [trialStep]
  rw [hj, (weightDecodeCounted_bounds w (bitVecEquiv b ω.1).val).2.2 j hj]

private theorem trialStep_inr (w : Fin N → ℕ) (b : ℕ) (BD : ℕ × ℕ) (ω : Reg b × ℕ)
    (hj : (weightDecodeCounted w (bitVecEquiv b ω.1).val).1 = none) :
    trialStep w b BD ω = Sum.inr (BD.1 + ω.2, BD.2 + N) := by
  dsimp only [trialStep]
  rw [hj, (weightDecodeCounted_bounds w (bitVecEquiv b ω.1).val).2.1 hj]

noncomputable def rationalCountedNext (w : Fin N → ℕ) (b : ℕ) (BD : ℕ × ℕ) :
    PMF (RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ)) :=
  (fairBitsCosted b).map (trialStep w b BD)

def rejectionOutcome
    (z : RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ)) :
    RandomizedExecution.Configuration Unit (Fin N) :=
  match z with
  | Sum.inl t => Sum.inl t.1
  | Sum.inr _ => Sum.inr ()

def rejectionBits
    (z : RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ)) : ℕ :=
  match z with
  | Sum.inl t => t.2.1
  | Sum.inr s => s.1

def rejectionComparisons
    (z : RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ)) : ℕ :=
  match z with
  | Sum.inl t => t.2.2
  | Sum.inr s => s.2

noncomputable def rationalRejectionRun (w : Fin N → ℕ) (b : ℕ) (fuel : ℕ) :
    CostedLaw (RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ)) :=
  runFor (rationalCountedNext w b) fuel (Sum.inr (0, 0))

noncomputable def rationalMeanComparisons (w : Fin N → ℕ) (b : ℕ) : ℝ≥0∞ :=
  ((∑ j : Fin N, w j * (j.val + 1)) + (2 ^ b - weightTotal w) * N : ℕ) /
    ((2 ^ b : ℕ) : ℝ≥0∞)

noncomputable def rationalFirstStop (w : Fin N → ℕ) (b : ℕ) (t : ℕ) (j : Fin N) : ℝ≥0∞ :=
  CostedLaw.event (rationalRejectionRun w b (t + 1))
    (fun z => rejectionOutcome z.1 = Sum.inl j ∧ z.2 = t + 1)

end Counted

section KernelFacts

variable {N : ℕ}

private theorem expectation_fairBitsCosted {b : ℕ} (G : Reg b × ℕ → ℝ≥0∞) :
    CostedLaw.expectation (fairBitsCosted b) G =
      ∑' ω : Reg b, ((2^b : ℕ) : ℝ≥0∞)⁻¹ * G (ω, b) := by
  show ∑' x, fairBitsCosted b x * G x = _
  rw [tsum_prod_type' (F := fun x : Reg b × ℕ => fairBitsCosted b x * G x)]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single b (fun n hn => by
    rw [fair_bit_program_joint_distribution b n ω, if_neg hn, zero_mul])]
  rw [fair_bit_program_joint_distribution b b ω, if_pos rfl,
    PMF.uniformOfFintype'_apply, card_reg]

private theorem event_fst_point {X : Type} (p : PMF (X × ℕ)) (a : X) :
    CostedLaw.event p (fun z => z.1 = a) = ∑' k : ℕ, p (a, k) := by
  show ∑' z, p z * (if z.1 = a then (1 : ℝ≥0∞) else 0) = _
  rw [tsum_prod_type' (F := fun z : X × ℕ => p z * (if z.1 = a then (1 : ℝ≥0∞) else 0))]
  rw [tsum_congr (g := fun x : X => if x = a then (∑' k : ℕ, p (a, k)) else (0 : ℝ≥0∞))
    (fun x => by
      by_cases h : x = a
      · rw [h]
        beta_reduce
        rw [if_pos rfl]
        rw [tsum_congr (g := fun k : ℕ => p (a, k)) (fun k => by simp)]
      · beta_reduce
        rw [if_neg h]
        rw [tsum_congr (g := fun _ : ℕ => (0 : ℝ≥0∞)) (fun k => by simp [h])]
        exact tsum_zero),
    tsum_eq_single a (fun x hx => by rw [if_neg hx]), if_pos rfl]

private theorem expectation_congr_support {α : Type} (p : PMF α) (f g : α → ℝ≥0∞)
    (h : ∀ a ∈ p.support, f a = g a) :
    CostedLaw.expectation p f = CostedLaw.expectation p g := by
  show ∑' a, p a * f a = ∑' a, p a * g a
  refine tsum_congr fun a => ?_
  by_cases hp : p a = 0
  · rw [hp, zero_mul, zero_mul]
  · rw [h a ((PMF.mem_support_iff p a).mpr hp)]

private theorem expectation_config_split
    (p : PMF (RandomizedExecution.Configuration Unit (Fin N)))
    (F : RandomizedExecution.Configuration Unit (Fin N) → ℝ≥0∞) :
    CostedLaw.expectation p F =
      (∑ j : Fin N, p (Sum.inl j) * F (Sum.inl j))
        + p (Sum.inr ()) * F (Sum.inr ()) := by
  show ∑' z, p z * F z = _
  rw [tsum_sum_type', tsum_fintype, tsum_fintype]
  simp

private theorem fiberSome_card (w : Fin N → ℕ) (b : ℕ) (hb : weightTotal w ≤ 2 ^ b)
    (j : Fin N) :
    (Finset.univ.filter (fun bits : Reg b =>
      (weightDecodeCounted w (bitVecEquiv b bits).val).1 = some j)).card = w j :=
  (rational_fair_bit_step_distribution N w b hb).1 j

private theorem fiberNone_card (w : Fin N → ℕ) (b : ℕ) (hb : weightTotal w ≤ 2 ^ b) :
    (Finset.univ.filter (fun bits : Reg b =>
      (weightDecodeCounted w (bitVecEquiv b bits).val).1 = none)).card = 2^b - weightTotal w :=
  (rational_fair_bit_step_distribution N w b hb).2.1

theorem next_inl_mass (w : Fin N → ℕ) (b : ℕ) (hb : weightTotal w ≤ 2 ^ b)
    (j : Fin N) :
    rationalRejectionNext w b () (Sum.inl j) = (w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞) :=
  (rational_fair_bit_step_distribution N w b hb).2.2.1 j

theorem next_inr_mass (w : Fin N → ℕ) (b : ℕ) (hb : weightTotal w ≤ 2 ^ b) :
    rationalRejectionNext w b () (Sum.inr ()) = rationalRejectMass w b :=
  (rational_fair_bit_step_distribution N w b hb).2.2.2

theorem rational_rejection_kernel_normalized (w : Fin N → ℕ) (b : ℕ)
    (hb : weightTotal w ≤ 2 ^ b) :
    (∑ j : Fin N, rationalRejectionNext w b () (Sum.inl j))
      + rationalRejectionNext w b () (Sum.inr ()) = 1 := by
  have hmass : ∀ j : Fin N, rationalRejectionNext w b () (Sum.inl j)
      = (w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞) := fun j => next_inl_mass w b hb j
  have hcast : ((∑ j : Fin N, w j : ℕ) : ℝ≥0∞) = (weightTotal w : ℝ≥0∞) := by
    simp [weightTotal]
  have hwt : weightTotal w + (2 ^ b - weightTotal w) = 2 ^ b := by omega
  rw [Finset.sum_congr rfl (fun j _ => by rw [hmass j, div_eq_mul_inv]),
    next_inr_mass w b hb, rationalRejectMass, coinRejectMass, div_eq_mul_inv,
    ← Finset.sum_mul, ← Nat.cast_sum, hcast, ← add_mul, ← Nat.cast_add, hwt,
    ENNReal.mul_inv_cancel (by positivity) (by simp)]

theorem rational_mean_comparisons_kernel (w : Fin N → ℕ) (b : ℕ) (hb : weightTotal w ≤ 2 ^ b) :
    (∑ j : Fin N, rationalRejectionNext w b () (Sum.inl j) * (((j.val + 1 : ℕ) : ℝ≥0∞)))
      + rationalRejectionNext w b () (Sum.inr ()) * ((N : ℕ) : ℝ≥0∞)
      = rationalMeanComparisons w b := by
  have hmass : ∀ j : Fin N, rationalRejectionNext w b () (Sum.inl j)
      = (w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞) := fun j => next_inl_mass w b hb j
  have h1 : ∑ j : Fin N, rationalRejectionNext w b () (Sum.inl j) * (((j.val + 1 : ℕ) : ℝ≥0∞))
      = (∑ j : Fin N, ((w j * (j.val + 1) : ℕ) : ℝ≥0∞)) * ((2^b : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hmass j, div_eq_mul_inv, Nat.cast_mul, mul_right_comm]
  have h2 : rationalRejectionNext w b () (Sum.inr ()) * ((N : ℕ) : ℝ≥0∞)
      = (((2^b - weightTotal w) * N : ℕ) : ℝ≥0∞) * ((2^b : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [next_inr_mass w b hb, rationalRejectMass, coinRejectMass, div_eq_mul_inv,
      Nat.cast_mul, mul_right_comm]
  rw [rationalMeanComparisons, div_eq_mul_inv, Nat.cast_add, h1, h2, ← add_mul,
    ← Nat.cast_sum, ← Nat.cast_add]

end KernelFacts

section Projection

variable {N : ℕ}

private theorem countedNext_map_outcome (w : Fin N → ℕ) (b : ℕ) (s : ℕ × ℕ) :
    (rationalCountedNext w b s).map (fun c => c.map (fun t => t.1) (fun _ => ())) =
      rationalRejectionNext w b () := by
  have hfun : ∀ ω : Reg b × ℕ,
      (trialStep w b s ω).map (fun t => t.1) (fun _ => ()) = weightStep w b ω.1 := by
    intro ω
    cases hd : (weightDecodeCounted w (bitVecEquiv b ω.1).val).1 with
    | some j =>
        rw [trialStep_inl w b s ω j hd]
        simp [weightStep, hd]
    | none =>
        rw [trialStep_inr w b s ω hd]
        simp [weightStep, hd]
  rw [rationalCountedNext, pmf_map_map, rationalRejectionNext, pmf_map_map]
  exact congrArg (fun F => PMF.map F (fairBitsCosted b)) (funext fun ω => hfun ω)

private theorem tick_map_outcome (w : Fin N → ℕ) (b : ℕ)
    (z : RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ)) :
    (tick (rationalCountedNext w b) z).map (fun y => (rejectionOutcome y.1, y.2)) =
      tick (rationalRejectionNext w b) (rejectionOutcome z) := by
  cases z with
  | inl t =>
      show (CostedLaw.ret (Sum.inl t)).map (fun y => (rejectionOutcome y.1, y.2)) =
        CostedLaw.ret (Sum.inl t.1)
      simp [CostedLaw.ret, rejectionOutcome, PMF.pure_map]
  | inr s =>
      have hpt : ∀ c : RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ),
          rejectionOutcome c = c.map (fun t => t.1) (fun _ => ()) := by
        intro c; cases c <;> rfl
      have key : PMF.map (fun y => (rejectionOutcome y.1, y.2))
          (PMF.map (fun c => (c, (1 : ℕ))) (rationalCountedNext w b s))
          = PMF.map (fun c => (c, (1 : ℕ))) (rationalRejectionNext w b ()) := by
        have e1 : PMF.map (fun y => (rejectionOutcome y.1, y.2))
            (PMF.map (fun c => (c, (1 : ℕ))) (rationalCountedNext w b s))
            = PMF.map (fun c => (c.map (fun t => t.1) (fun _ => ()), (1 : ℕ)))
                (rationalCountedNext w b s) := by
          rw [pmf_map_map (rationalCountedNext w b s) (fun c => (c, (1 : ℕ)))
            (fun y => (rejectionOutcome y.1, y.2))]
          exact congrArg (fun F => PMF.map F (rationalCountedNext w b s))
            (funext fun c => by
              show (rejectionOutcome c, (1 : ℕ))
                = (c.map (fun t => t.1) (fun _ => ()), (1 : ℕ))
              rw [hpt c])
        have e2 : PMF.map (fun c => (c.map (fun t => t.1) (fun _ => ()), (1 : ℕ)))
            (rationalCountedNext w b s)
            = PMF.map (fun c => (c, (1 : ℕ))) (rationalRejectionNext w b ()) := by
          have e2a : PMF.map (fun c => (c.map (fun t => t.1) (fun _ => ()), (1 : ℕ)))
              (rationalCountedNext w b s)
              = PMF.map (fun c => (c, (1 : ℕ)))
                  ((rationalCountedNext w b s).map (fun c => c.map (fun t => t.1)
                    (fun _ => ()))) :=
            (pmf_map_map (rationalCountedNext w b s)
              (fun c => c.map (fun t => t.1) (fun _ => ())) (fun c => (c, (1 : ℕ)))).symm
          rw [e2a, countedNext_map_outcome]
        rw [e1, e2]
      show PMF.map (fun y => (rejectionOutcome y.1, y.2))
          (PMF.map (fun c => (c, (1 : ℕ))) (rationalCountedNext w b s)) =
        PMF.map (fun c => (c, (1 : ℕ))) (rationalRejectionNext w b ())
      rw [key]

private theorem runFor_map_outcome (w : Fin N → ℕ) (b : ℕ) :
    ∀ (fuel : ℕ) (z : RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ)),
      (runFor (rationalCountedNext w b) fuel z).map (fun y => (rejectionOutcome y.1, y.2)) =
        runFor (rationalRejectionNext w b) fuel (rejectionOutcome z) := by
  intro fuel
  induction fuel with
  | zero =>
      intro z
      show (CostedLaw.ret z).map (fun y => (rejectionOutcome y.1, y.2)) =
        CostedLaw.ret (rejectionOutcome z)
      simp [CostedLaw.ret, PMF.pure_map]
  | succ fuel ih =>
      intro z
      have step : PMF.map (fun y => (rejectionOutcome y.1, y.2))
          (CostedLaw.bind (tick (rationalCountedNext w b) z)
            (runFor (rationalCountedNext w b) fuel))
          = PMF.bind (tick (rationalRejectionNext w b) (rejectionOutcome z))
              (fun y => CostedLaw.charge y.2
                (runFor (rationalRejectionNext w b) fuel y.1)) := by
        simp only [CostedLaw.bind]
        rw [PMF.map_bind]
        have hper : ∀ a : (RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ)) × ℕ,
            PMF.map (fun y => (rejectionOutcome y.1, y.2))
                (CostedLaw.charge a.2 (runFor (rationalCountedNext w b) fuel a.1))
              = CostedLaw.charge a.2
                  (runFor (rationalRejectionNext w b) fuel (rejectionOutcome a.1)) := by
          intro a
          rw [charge_map_comm, ih]
        rw [congrArg (PMF.bind (tick (rationalCountedNext w b) z)) (funext hper),
          ← tick_map_outcome, PMF.bind_map]
        exact congrArg (PMF.bind (tick (rationalCountedNext w b) z))
          (funext fun x => rfl)
      show PMF.map (fun y => (rejectionOutcome y.1, y.2))
          (CostedLaw.bind (tick (rationalCountedNext w b) z)
            (runFor (rationalCountedNext w b) fuel)) = _
      rw [step]
      rfl

end Projection

section Invariant

variable {N : ℕ}

private theorem fairBits_cost_mem {b : ℕ} {ω : Reg b × ℕ}
    (h : ω ∈ (fairBitsCosted b).support) : ω.2 = b := by
  by_contra hne
  exact absurd (show fairBitsCosted b ω = 0 from by
    rw [fair_bit_program_joint_distribution b ω.2 ω.1]; exact if_neg hne)
    ((PMF.mem_support_iff _ _).mp h)

private theorem counted_support_invariant (w : Fin N → ℕ) (b : ℕ) :
    ∀ (fuel : ℕ) (BD : ℕ × ℕ)
        (z : RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) × ℕ),
      z ∈ (runFor (rationalCountedNext w b) fuel (Sum.inr BD)).support →
        z.2 ≤ fuel ∧
        rejectionBits z.1 = BD.1 + b * z.2 ∧
        rejectionComparisons z.1 ≤ BD.2 + N * z.2 ∧
        (rejectionOutcome z.1 = Sum.inr () → rejectionComparisons z.1 = BD.2 + N * z.2) ∧
        (∀ j : Fin N, rejectionOutcome z.1 = Sum.inl j →
          1 ≤ z.2 ∧ rejectionComparisons z.1 = BD.2 + N * (z.2 - 1) + j.val + 1) ∧
        (rejectionOutcome z.1 = Sum.inr () → z.2 = fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro BD z hz
      have hz' : z = ((Sum.inr BD :
          RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ)), 0) := by
        simpa [runFor, CostedLaw.ret] using hz
      subst hz'
      refine ⟨by omega, by simp [rejectionBits], by simp [rejectionComparisons],
        fun _ => by simp [rejectionComparisons],
        fun j hj => absurd hj (by simp [rejectionOutcome]), fun _ => rfl⟩
  | succ fuel ih =>
      intro BD z hz
      obtain ⟨x, hx, hzx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
      have hxm : x ∈ (PMF.map (fun c => (c, (1 : ℕ))) (rationalCountedNext w b BD)).support :=
        hx
      obtain ⟨c, hc, hxc⟩ := (PMF.mem_support_map_iff _ _ _).mp hxm
      have hxc' : x = (c, 1) := hxc.symm
      have hcm : c ∈ (PMF.map (trialStep w b BD) (fairBitsCosted b)).support := hc
      obtain ⟨ω, hω, hcx⟩ := (PMF.mem_support_map_iff _ _ _).mp hcm
      have hωb : ω.2 = b := fairBits_cost_mem hω
      have hz2 : z ∈ (CostedLaw.charge x.2
          (runFor (rationalCountedNext w b) fuel x.1)).support := hzx
      have hx11 : x.1 = c ∧ x.2 = 1 := by rw [hxc']; exact ⟨rfl, rfl⟩
      rw [hx11.1, hx11.2] at hz2
      have hz3 : z ∈ (PMF.map (fun y => (y.1, (1 : ℕ) + y.2))
          (runFor (rationalCountedNext w b) fuel c)).support := hz2
      obtain ⟨y, hy, hzy⟩ := (PMF.mem_support_map_iff _ _ _).mp hz3
      have hz4 : z = (y.1, (1 : ℕ) + y.2) := hzy.symm
      subst hz4
      (try dsimp only)
      cases hd : (weightDecodeCounted w (bitVecEquiv b ω.1).val).1 with
      | some j =>
          rw [← hcx, trialStep_inl w b BD ω j hd, hωb] at hy
          rw [runFor_halted] at hy
          have hy' : y = ((Sum.inl (j, BD.1 + b, BD.2 + (j.val + 1)) :
              RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ)), 0) := by
            simpa [CostedLaw.ret] using hy
          subst hy'
          have hjN : j.val + 1 ≤ N := by omega
          refine ⟨by omega, by simp [rejectionBits],
            by simp only [rejectionComparisons]; omega,
            fun hpend => absurd hpend (by simp [rejectionOutcome]), ?_,
            fun hpend => absurd hpend (by simp [rejectionOutcome])⟩
          intro j' hj'
          have hj'v : j' = j := by
            simp only [rejectionOutcome, Sum.inl.injEq] at hj'
            simpa using hj'.symm
          subst hj'v
          exact ⟨by omega, by simp only [rejectionComparisons]; omega⟩
      | none =>
          rw [← hcx, trialStep_inr w b BD ω hd, hωb] at hy
          obtain ⟨hle', hbits', hcmp', hpend', hhalt', hstop'⟩ :=
            ih (BD.1 + b, BD.2 + N) y hy
          have hle2 : (BD.2 + N) + N * y.2 ≤ BD.2 + N * (1 + y.2) := by
            rw [mul_add, mul_one]
            omega
          have g1 : ((1 : ℕ) + y.2) ≤ fuel + 1 := by omega
          have g2 : rejectionBits y.1 = BD.1 + b * (1 + y.2) := by rw [hbits']; ring
          refine ⟨g1, g2, hcmp'.trans hle2, ?_, ?_, ?_⟩
          · intro hpend
            rw [hpend' hpend]
            ring
          · intro j' hj'
            obtain ⟨h1', hc'⟩ := hhalt' j' hj'
            have hy2 : (1 : ℕ) + y.2 - 1 = y.2 := by omega
            have hN : N * y.2 = N + N * (y.2 - 1) := by
              have h1 : y.2 = (y.2 - 1) + 1 := by omega
              have h2 : N * y.2 = N * ((y.2 - 1) + 1) := by
                conv =>
                  lhs
                  rw [h1]
              rw [h2, mul_add, mul_one, add_comm]
            refine ⟨by omega, ?_⟩
            rw [hc', hy2, hN]
            all_goals omega
          · intro hp
            have hp' : rejectionOutcome y.1 = Sum.inr () := by
              simpa [rejectionOutcome] using hp
            have hstop := hstop' hp'
            omega

theorem rational_counted_run_projection_and_paths (N : ℕ) (w : Fin N → ℕ) (b fuel : ℕ) :
    (rationalRejectionRun w b fuel).map (fun z => (rejectionOutcome z.1, z.2)) =
      RandomizedExecution.runFor (rationalRejectionNext w b) fuel (Sum.inr ()) ∧
    (∀ z ∈ (rationalRejectionRun w b fuel).support,
      z.2 ≤ fuel ∧ rejectionBits z.1 = b * z.2 ∧
      rejectionComparisons z.1 ≤ N * z.2 ∧
      (rejectionOutcome z.1 = Sum.inr () → rejectionComparisons z.1 = N * z.2) ∧
      (∀ j : Fin N, rejectionOutcome z.1 = Sum.inl j →
        1 ≤ z.2 ∧ rejectionComparisons z.1 = N * (z.2 - 1) + j.val + 1)) := by
  refine ⟨runFor_map_outcome w b fuel (Sum.inr (0, 0)), ?_⟩
  intro z hz
  obtain ⟨hle, hbits, hcmp, hpend, hhalt, _⟩ :=
    counted_support_invariant w b fuel (0, 0) z hz
  have hb : rejectionBits z.1 = b * z.2 := by rw [hbits]; omega
  have hc2 : rejectionComparisons z.1 ≤ N * z.2 := le_trans hcmp (by omega)
  have hp : rejectionOutcome z.1 = Sum.inr () → rejectionComparisons z.1 = N * z.2 :=
    fun hp0 => by rw [hpend hp0]; omega
  refine ⟨hle, hb, hc2, hp, ?_⟩
  intro j hj
  obtain ⟨h1, hc⟩ := hhalt j hj
  refine ⟨h1, ?_⟩
  rw [hc]
  omega

end Invariant

section PlainMasses

variable {N : ℕ}

private theorem nat_smul_ennreal (n : ℕ) (x : ℝ≥0∞) : n • x = (n : ℝ≥0∞) * x :=
  nsmul_eq_mul n x

private theorem geom_tails_mul (q : ℝ≥0∞) (hq : q ≤ 1) (fuel : ℕ) :
    (∑ t ∈ Finset.range fuel, q ^ t) * (1 - q) + q ^ fuel = 1 := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      have hsplit : (∑ t ∈ Finset.range (fuel + 1), q ^ t) * (1 - q)
          = (∑ t ∈ Finset.range fuel, q ^ t) * (1 - q) + q ^ fuel * (1 - q) := by
        rw [Finset.sum_range_succ, add_mul]
      have hstep : q ^ fuel * (1 - q) + q ^ (fuel + 1) = q ^ fuel := by
        rw [pow_succ, ← mul_add, tsub_add_cancel_of_le hq, mul_one]
      calc (∑ t ∈ Finset.range (fuel + 1), q ^ t) * (1 - q) + q ^ (fuel + 1)
          = (∑ t ∈ Finset.range fuel, q ^ t) * (1 - q)
              + (q ^ fuel * (1 - q) + q ^ (fuel + 1)) := by
            rw [hsplit, add_assoc]
        _ = (∑ t ∈ Finset.range fuel, q ^ t) * (1 - q) + q ^ fuel := by rw [hstep]
        _ = 1 := ih

private theorem tails_succ (q : ℝ≥0∞) (fuel : ℕ) :
    (∑ t ∈ Finset.range (fuel + 1), q ^ t) = 1 + q * (∑ t ∈ Finset.range fuel, q ^ t) := by
  rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero]
  rw [Finset.sum_congr rfl (fun t _ => (pow_succ' q t).symm), add_comm]

private theorem reject_le_one (w : Fin N → ℕ) (b : ℕ) :
    rationalRejectMass w b ≤ 1 := by
  have hmul : rationalRejectMass w b * ((2 ^ b : ℕ) : ℝ≥0∞)
      = ((2 ^ b - weightTotal w : ℕ) : ℝ≥0∞) := by
    rw [rationalRejectMass, coinRejectMass, div_eq_mul_inv, mul_assoc,
      ENNReal.inv_mul_cancel
        (by exact ne_of_gt (by exact_mod_cast Nat.two_pow_pos b)) (by simp), mul_one]
  have hle : rationalRejectMass w b * ((2 ^ b : ℕ) : ℝ≥0∞)
      ≤ 1 * ((2 ^ b : ℕ) : ℝ≥0∞) := by
    rw [hmul, one_mul]
    exact Nat.cast_le.mpr (Nat.sub_le _ _)
  calc rationalRejectMass w b
      = ((2 ^ b - weightTotal w : ℕ) : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) := by
        rw [rationalRejectMass, coinRejectMass]
    _ ≤ ((2 ^ b : ℕ) : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞) :=
        ENNReal.div_le_div (Nat.cast_le.mpr (Nat.sub_le _ _)) le_rfl
    _ = 1 := by
        rw [div_eq_mul_inv, ENNReal.mul_inv_cancel
          (by exact ne_of_gt (by exact_mod_cast Nat.two_pow_pos b)) (by simp)]

private theorem one_sub_reject (w : Fin N → ℕ) (b : ℕ) (hb : weightTotal w ≤ 2 ^ b) :
    1 - rationalRejectMass w b = (weightTotal w : ℝ≥0∞) * ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹ := by
  have htop : ((2 ^ b : ℕ) : ℝ≥0∞) ≠ ⊤ := by simp
  have hadd : (weightTotal w : ℝ≥0∞) * ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹
      + rationalRejectMass w b = 1 := by
    rw [rationalRejectMass, coinRejectMass, div_eq_mul_inv, ← add_mul, ← Nat.cast_add]
    have hw : ((weightTotal w + (2 ^ b - weightTotal w : ℕ) : ℕ) : ℝ≥0∞)
        = ((2 ^ b : ℕ) : ℝ≥0∞) := by
      congr 1
      omega
    rw [hw, ENNReal.mul_inv_cancel (a := ((2 ^ b : ℕ) : ℝ≥0∞))
      (Nat.cast_ne_zero.mpr (ne_of_gt (Nat.two_pow_pos b))) htop]
  have hqtop : rationalRejectMass w b ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (reject_le_one w b) (by simp))
  exact (ENNReal.eq_sub_of_add_eq hqtop hadd).symm

private theorem plain_pending_mass (w : Fin N → ℕ) (b : ℕ) (hb : weightTotal w ≤ 2 ^ b) :
    ∀ fuel : ℕ,
      CostedLaw.event (runFor (rationalRejectionNext w b) fuel (Sum.inr ()))
        (fun z => z.1 = Sum.inr ()) = (rationalRejectMass w b) ^ fuel := by
  intro fuel
  induction fuel with
  | zero =>
      show CostedLaw.event (CostedLaw.ret (Sum.inr ())) (fun z => z.1 = Sum.inr ()) = _
      rw [CostedLaw.event_ret, if_pos rfl, pow_zero]
  | succ fuel ih =>
      have hstep : CostedLaw.event (runFor (rationalRejectionNext w b) (fuel + 1)
          (Sum.inr ())) (fun z => z.1 = Sum.inr ())
        = CostedLaw.expectation (rationalRejectionNext w b ())
            (fun c => CostedLaw.event (runFor (rationalRejectionNext w b) fuel c)
              (fun y => y.1 = Sum.inr ())) := by
        show CostedLaw.event
            (PMF.bind (tick (rationalRejectionNext w b) (Sum.inr ()))
              fun x => CostedLaw.charge x.2 (runFor (rationalRejectionNext w b) fuel x.1))
            _ = _
        rw [CostedLaw.event_bind_general,
          show tick (rationalRejectionNext w b) (Sum.inr ())
            = PMF.map (fun c => (c, (1 : ℕ))) (rationalRejectionNext w b ()) from rfl,
          CostedLaw.expectation_map]
        exact CostedLaw.expectation_congr fun c =>
          CostedLaw.event_charge_general 1 _ _
      rw [hstep, expectation_config_split]
      have hhalt : ∀ j' : Fin N, CostedLaw.event (runFor (rationalRejectionNext w b) fuel
          (Sum.inl j')) (fun y => y.1 = Sum.inr ()) = 0 := by
        intro j'
        rw [runFor_halted]
        exact CostedLaw.event_ret_zero _ (by simp)
      rw [Finset.sum_eq_zero (fun j' _ => by rw [hhalt j']; ring), ih, pow_succ,
        next_inr_mass w b hb, mul_comm, zero_add]

private theorem plain_halt_mass (w : Fin N → ℕ) (b : ℕ) (hb : weightTotal w ≤ 2 ^ b) :
    ∀ (fuel k : ℕ) (j : Fin N),
      CostedLaw.event (runFor (rationalRejectionNext w b) fuel (Sum.inr ()))
        (fun z => z = (Sum.inl j, k)) =
        (if 1 ≤ k ∧ k ≤ fuel then (rationalRejectMass w b) ^ (k - 1)
          * ((w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)) else 0) := by
  intro fuel
  induction fuel with
  | zero =>
      intro k j
      show CostedLaw.event (CostedLaw.ret (Sum.inr ())) (fun z => z = (Sum.inl j, k)) = _
      rw [CostedLaw.event_ret, if_neg (t := (1 : ℝ≥0∞)) (e := (0 : ℝ≥0∞)) (by simp)]
      split
      · rename_i hk; exact absurd hk.2 (by omega)
      · rfl
  | succ fuel ih =>
      intro k j
      have hstep : CostedLaw.event (runFor (rationalRejectionNext w b) (fuel + 1)
          (Sum.inr ())) (fun z => z = (Sum.inl j, k))
        = CostedLaw.expectation (rationalRejectionNext w b ())
            (fun c => CostedLaw.event (runFor (rationalRejectionNext w b) fuel c)
              (fun y => (y.1, 1 + y.2) = (Sum.inl j, k))) := by
        show CostedLaw.event
            (PMF.bind (tick (rationalRejectionNext w b) (Sum.inr ()))
              fun x => CostedLaw.charge x.2 (runFor (rationalRejectionNext w b) fuel x.1))
            _ = _
        rw [CostedLaw.event_bind_general,
          show tick (rationalRejectionNext w b) (Sum.inr ())
            = PMF.map (fun c => (c, (1 : ℕ))) (rationalRejectionNext w b ()) from rfl,
          CostedLaw.expectation_map]
        exact CostedLaw.expectation_congr fun c =>
          CostedLaw.event_charge_general 1 _ _
      rw [hstep, expectation_config_split]
      have hhalt_one : ∀ j' : Fin N, j' = j → k = 1 →
          CostedLaw.event (runFor (rationalRejectionNext w b) fuel (Sum.inl j'))
            (fun y => (y.1, 1 + y.2) = (Sum.inl j, k)) = (1 : ℝ≥0∞) := by
        intro j' hj' hk1
        subst hj'
        subst hk1
        rw [runFor_halted, CostedLaw.event_ret,
          if_pos (t := (1 : ℝ≥0∞)) (e := (0 : ℝ≥0∞)) (by simp)]
      have hhalt_zero : ∀ j' : Fin N, ¬(j' = j ∧ k = 1) →
          CostedLaw.event (runFor (rationalRejectionNext w b) fuel (Sum.inl j'))
            (fun y => (y.1, 1 + y.2) = (Sum.inl j, k)) = (0 : ℝ≥0∞) := by
        intro j' h
        rw [runFor_halted, CostedLaw.event_ret,
          if_neg (t := (1 : ℝ≥0∞)) (e := (0 : ℝ≥0∞)) (by
            intro hc
            exact h ⟨by simpa using (Prod.ext_iff.mp hc).1, by
              have h2 := (Prod.ext_iff.mp hc).2; simp only [add_zero] at h2; omega⟩)]
      have hzero : CostedLaw.event (runFor (rationalRejectionNext w b) fuel (Sum.inr ()))
          (fun y => (y.1, 1 + y.2) = (Sum.inl j, 0)) = 0 := by
        refine CostedLaw.event_zero _ _ fun y hy => ?_
        rw [Prod.ext_iff] at hy
        omega
      have hpend : ∀ k1 : ℕ, 1 ≤ k1 → CostedLaw.event
          (runFor (rationalRejectionNext w b) fuel (Sum.inr ()))
          (fun y => (y.1, 1 + y.2) = (Sum.inl j, k1))
          = CostedLaw.event (runFor (rationalRejectionNext w b) fuel (Sum.inr ()))
            (fun y => y = (Sum.inl j, k1 - 1)) := by
        intro k1 hk1
        refine CostedLaw.event_congr fun y => ?_
        show ((y.1, 1 + y.2) = (Sum.inl j, k1)) ↔ (y = (Sum.inl j, k1 - 1))
        rw [Prod.ext_iff, Prod.ext_iff]
        (try dsimp only)
        constructor
        · intro h; exact ⟨h.1, by omega⟩
        · intro h; exact ⟨h.1, by omega⟩
      by_cases hk : k = 0
      · subst hk
        rw [Finset.sum_congr rfl (fun j' _ => by
          rw [hhalt_zero j' (fun hc => absurd hc.2 (by norm_num)), mul_zero]),
          Finset.sum_const_zero, hzero, mul_zero, add_zero]
        split
        · rename_i hk0; exact absurd hk0.1 (by simp)
        · rfl
      · by_cases hk1 : k = 1
        · subst hk1
          have hz0 : CostedLaw.event (runFor (rationalRejectionNext w b) fuel (Sum.inr ()))
              (fun y => y = (Sum.inl j, (0:ℕ))) = 0 := by
            have h1 : CostedLaw.event (runFor (rationalRejectionNext w b) fuel (Sum.inr ()))
                (fun z => z = (Sum.inl j, (0:ℕ)))
              ≤ CostedLaw.event (runFor (rationalRejectionNext w b) fuel (Sum.inr ()))
                (fun z => (∃ a, z.1 = Sum.inl a) ∧ z.2 = (0:ℕ)) := by
              rw [CostedLaw.event_eq, CostedLaw.event_eq]
              refine ENNReal.tsum_le_tsum fun z => ?_
              (try dsimp only)
              by_cases hz : z = (Sum.inl j, (0:ℕ))
              · rw [if_pos hz, if_pos (by rw [hz]; exact ⟨⟨j, rfl⟩, rfl⟩)]
              · rw [if_neg hz, mul_zero]
                exact zero_le
            exact le_antisymm (le_trans h1
              (le_of_eq (runFor_no_halt_at_cost_zero _ fuel ()))) (by simp)
          rw [Finset.sum_eq_single j
              (fun j' _ hj' => by
                rw [hhalt_zero j' (fun hc => absurd hc.1 hj'), mul_zero]) (by simp),
            hhalt_one j rfl rfl, hpend 1 (by omega), Nat.sub_self, hz0, mul_zero,
            add_zero, mul_one]
          split
          · rename_i hk0
            rw [pow_zero, one_mul, next_inl_mass w b hb]
          · rename_i hk0; exact absurd (by simp) hk0
        · rw [Finset.sum_congr rfl (fun j' _ => by
              rw [hhalt_zero j' (fun hc => absurd hc.2 hk1), mul_zero]),
            Finset.sum_const_zero, zero_add, next_inr_mass w b hb,
            hpend k (by omega), ih (k - 1) j]
          by_cases hk0 : 1 ≤ k - 1 ∧ k - 1 ≤ fuel
          · rw [if_pos (t := (rationalRejectMass w b ^ (k - 1 - 1) *
                ((w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)))) (e := (0 : ℝ≥0∞)) hk0]
            by_cases hk2 : 1 ≤ k ∧ k ≤ fuel + 1
            · rw [if_pos (t := (rationalRejectMass w b ^ (k - 1) *
                  ((w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)))) (e := (0 : ℝ≥0∞)) hk2]
              have hexp : (k - 1 : ℕ) = (k - 2) + 1 := by omega
              rw [hexp, Nat.add_sub_cancel, pow_succ', mul_assoc]
            · exact absurd hk2 (by omega)
          · rw [if_neg (t := (rationalRejectMass w b ^ (k - 1 - 1) *
                ((w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)))) (e := (0 : ℝ≥0∞)) hk0]
            by_cases hk2 : 1 ≤ k ∧ k ≤ fuel + 1
            · rw [if_pos (t := (rationalRejectMass w b ^ (k - 1) *
                  ((w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)))) (e := (0 : ℝ≥0∞)) hk2]
              exact absurd (show 1 ≤ k - 1 ∧ k - 1 ≤ fuel from by omega) hk0
            · rw [if_neg (t := (rationalRejectMass w b ^ (k - 1) *
                  ((w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)))) (e := (0 : ℝ≥0∞)) hk2, mul_zero]

end PlainMasses

section GeomMean

private theorem tails_arith (q : ℝ≥0∞) (hq : q ≤ 1) (fuel : ℕ) :
    (1 - q) * (∑ t ∈ Finset.range fuel, t * q ^ t) + (fuel : ℝ≥0∞) * q ^ fuel
      = q * (∑ t ∈ Finset.range fuel, q ^ t) := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      have hsplit : (∑ t ∈ Finset.range (fuel + 1), t * q ^ t)
          = (∑ t ∈ Finset.range fuel, t * q ^ t) + fuel * q ^ fuel := by
        rw [Finset.sum_range_succ]
      have hstep : (1 - q) * (fuel * q ^ fuel) + ((fuel + 1 : ℕ) : ℝ≥0∞) * q ^ (fuel + 1)
          = fuel * q ^ fuel + q ^ (fuel + 1) := by
        have h1 : ((fuel + 1 : ℕ) : ℝ≥0∞) * q ^ (fuel + 1)
            = fuel * q ^ (fuel + 1) + q ^ (fuel + 1) := by
          rw [Nat.cast_add, add_mul, Nat.cast_one, one_mul]
        have hsub : fuel * q ^ fuel
            = (1 - q) * (fuel * q ^ fuel) + fuel * q ^ (fuel + 1) := by
          rw [pow_succ (q : ℝ≥0∞) fuel, ← mul_assoc (fuel : ℝ≥0∞) (q ^ fuel) q,
            mul_comm (1 - q) (fuel * q ^ fuel),
            ← mul_add (fuel * q ^ fuel) (1 - q) q, tsub_add_cancel_of_le hq, mul_one]
        rw [h1, ← add_assoc, ← hsub]
      calc (1 - q) * ∑ t ∈ Finset.range (fuel + 1), t * q ^ t
              + ((fuel + 1 : ℕ) : ℝ≥0∞) * q ^ (fuel + 1)
            = (1 - q) * ((∑ t ∈ Finset.range fuel, t * q ^ t) + fuel * q ^ fuel)
                + ((fuel + 1 : ℕ) : ℝ≥0∞) * q ^ (fuel + 1) := by rw [hsplit]
        _ = (1 - q) * ∑ t ∈ Finset.range fuel, t * q ^ t
                + ((1 - q) * (fuel * q ^ fuel) + ((fuel + 1 : ℕ) : ℝ≥0∞) * q ^ (fuel + 1)) := by
              rw [mul_add, add_assoc]
        _ = (1 - q) * ∑ t ∈ Finset.range fuel, t * q ^ t
                + (fuel * q ^ fuel + q ^ (fuel + 1)) := by rw [hstep]
        _ = q * ∑ t ∈ Finset.range fuel, q ^ t + q ^ (fuel + 1) := by
              rw [← ih, add_assoc]
        _ = q * ∑ t ∈ Finset.range (fuel + 1), q ^ t := by
              rw [Finset.sum_range_succ, mul_add, pow_succ, mul_comm q (q ^ fuel)]

end GeomMean

section Finite

variable {N : ℕ}

private theorem event_counted_eq_plain_pending (w : Fin N → ℕ) (b : ℕ) (fuel : ℕ)
    (BD : ℕ × ℕ) :
    CostedLaw.event (runFor (rationalRejectionNext w b) fuel (Sum.inr ()))
        (fun z => z.1 = Sum.inr ()) =
      CostedLaw.event (runFor (rationalCountedNext w b) fuel (Sum.inr BD))
        (fun z => rejectionOutcome z.1 = Sum.inr ()) := by
  have h := CostedLaw.event_map (p := runFor (rationalCountedNext w b) fuel (Sum.inr BD))
    (g := fun z => (rejectionOutcome z.1, z.2)) (E := fun w => w.1 = Sum.inr ())
  rw [runFor_map_outcome w b fuel (Sum.inr BD), rejectionOutcome] at h
  simp only [] at h
  exact h

private theorem event_counted_eq_plain_inl (w : Fin N → ℕ) (b : ℕ) (fuel : ℕ)
    (BD : ℕ × ℕ) (j : Fin N) :
    CostedLaw.event (runFor (rationalRejectionNext w b) fuel (Sum.inr ()))
        (fun z => z.1 = Sum.inl j) =
      CostedLaw.event (runFor (rationalCountedNext w b) fuel (Sum.inr BD))
        (fun z => rejectionOutcome z.1 = Sum.inl j) := by
  have h := CostedLaw.event_map (p := runFor (rationalCountedNext w b) fuel (Sum.inr BD))
    (g := fun z => (rejectionOutcome z.1, z.2)) (E := fun w => w.1 = Sum.inl j)
  rw [runFor_map_outcome w b fuel (Sum.inr BD), rejectionOutcome] at h
  simp only [] at h
  exact h

private theorem event_counted_eq_plain_inl_cost (w : Fin N → ℕ) (b : ℕ) (fuel : ℕ)
    (BD : ℕ × ℕ) (j : Fin N) (t : ℕ) :
    CostedLaw.event (runFor (rationalRejectionNext w b) fuel (Sum.inr ()))
        (fun z => z.1 = Sum.inl j ∧ z.2 = t + 1) =
      CostedLaw.event (runFor (rationalCountedNext w b) fuel (Sum.inr BD))
        (fun z => rejectionOutcome z.1 = Sum.inl j ∧ z.2 = t + 1) := by
  have h := CostedLaw.event_map (p := runFor (rationalCountedNext w b) fuel (Sum.inr BD))
    (g := fun z => (rejectionOutcome z.1, z.2))
    (E := fun w => w.1 = Sum.inl j ∧ w.2 = t + 1)
  rw [runFor_map_outcome w b fuel (Sum.inr BD), rejectionOutcome] at h
  simp only [] at h
  exact h

private theorem plain_pending_support_cost (w : Fin N → ℕ) (b fuel : ℕ) {k : ℕ}
    (hz : (Sum.inr (), k) ∈
      (runFor (rationalRejectionNext w b) fuel (Sum.inr ())).support) : k = fuel := by
  have hproj := runFor_map_outcome w b fuel (Sum.inr (0, 0))
  have hproj' : (runFor (rationalCountedNext w b) fuel (Sum.inr (0, 0))).map
      (fun z => (rejectionOutcome z.1, z.2)) =
      runFor (rationalRejectionNext w b) fuel (Sum.inr ()) := by
    simpa [rejectionOutcome] using hproj
  rw [← hproj'] at hz
  obtain ⟨z, hzs, hzeq⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
  have hout : rejectionOutcome z.1 = Sum.inr () := congrArg Prod.fst hzeq
  have hcount := (counted_support_invariant w b fuel (0, 0) z hzs).2.2.2.2.2 hout
  exact (congrArg Prod.snd hzeq).symm.trans hcount

private theorem plain_pending_point (w : Fin N → ℕ) (b fuel k : ℕ)
    (hb : weightTotal w ≤ 2 ^ b) :
    (runFor (rationalRejectionNext w b) fuel (Sum.inr ())) (Sum.inr (), k) =
      if k = fuel then (rationalRejectMass w b) ^ fuel else 0 := by
  classical
  let p := runFor (rationalRejectionNext w b) fuel (Sum.inr ())
  by_cases hk : k = fuel
  · subst k
    have hev : CostedLaw.event p (fun z => z = (Sum.inr (), fuel)) =
        CostedLaw.event p (fun z => z.1 = Sum.inr ()) := by
      rw [CostedLaw.event_eq, CostedLaw.event_eq]
      exact expectation_congr_support p
        (fun z => @ite ℝ≥0∞ (z = (Sum.inr (), fuel)) (Classical.propDecidable _) 1 0)
        (fun z => @ite ℝ≥0∞ (z.1 = Sum.inr ()) (Classical.propDecidable _) 1 0) (by
          intro z hz
          by_cases hp : z.1 = Sum.inr ()
          · have heqz : z = (Sum.inr (), z.2) := Prod.ext hp rfl
            have hz' : (Sum.inr (), z.2) ∈ p.support := by
              rw [← heqz]
              exact hz
            have hcost : z.2 = fuel := plain_pending_support_cost w b fuel hz'
            have heq : z = (Sum.inr (), fuel) := Prod.ext hp hcost
            (try dsimp only)
            simp [heq]
          · have hne : z ≠ (Sum.inr (), fuel) := by
              intro heq
              exact hp (congrArg Prod.fst heq)
            (try dsimp only)
            simp [hne, hp])
    rw [← event_point p (Sum.inr (), fuel), hev,
      plain_pending_mass w b hb fuel]
    simp
  · have hzero : p (Sum.inr (), k) = 0 := by
      by_contra hne
      have hz : (Sum.inr (), k) ∈ p.support := (PMF.mem_support_iff _ _).mpr hne
      exact hk (plain_pending_support_cost w b fuel hz)
    simp only [if_neg hk]
    simpa [p] using hzero

private theorem counted_pending_mass (w : Fin N → ℕ) (b : ℕ) (hb : weightTotal w ≤ 2 ^ b) :
    ∀ f : ℕ,
      CostedLaw.event (rationalRejectionRun w b f) (fun z => rejectionOutcome z.1 = Sum.inr ())
        = (rationalRejectMass w b) ^ f := by
  intro f
  rw [show rationalRejectionRun w b f
      = runFor (rationalCountedNext w b) f (Sum.inr (0, 0)) from rfl,
    ← event_counted_eq_plain_pending w b f (0, 0)]
  exact plain_pending_mass w b hb f

private theorem counted_return_mass (w : Fin N → ℕ) (b : ℕ) (hW : 0 < weightTotal w)
    (hb : weightTotal w ≤ 2 ^ b) (fuel : ℕ) (j : Fin N) :
    CostedLaw.event (rationalRejectionRun w b fuel) (fun z => rejectionOutcome z.1 = Sum.inl j)
      = (w j : ℝ≥0∞)/(weightTotal w : ℝ≥0∞) * (1 - (rationalRejectMass w b) ^ fuel) := by
  have hpt : ∀ (f : ℕ) (t : ℕ) (j : Fin N),
      CostedLaw.event (runFor (rationalRejectionNext w b) f (Sum.inr ()))
        (fun z => z.1 = Sum.inl j ∧ z.2 = t + 1) =
      CostedLaw.event (runFor (rationalRejectionNext w b) f (Sum.inr ()))
        (fun z => z = (Sum.inl j, t + 1)) := fun f t j => CostedLaw.event_congr fun z => by
      constructor
      · rintro ⟨h1, h2⟩
        exact Prod.ext h1 h2
      · intro h
        rw [h]
        exact ⟨rfl, rfl⟩
  have hqtop : rationalRejectMass w b ≠ ⊤ :=
    ne_top_of_lt (lt_of_le_of_lt (reject_le_one w b) (by simp : (1 : ℝ≥0∞) < ⊤))
  have htail : (∑ t ∈ Finset.range fuel, (rationalRejectMass w b) ^ t)
      * (1 - rationalRejectMass w b) = 1 - (rationalRejectMass w b) ^ fuel :=
    ENNReal.eq_sub_of_add_eq (WithTop.pow_ne_top hqtop)
      (geom_tails_mul _ (reject_le_one w b) fuel)
  have hWne : (weightTotal w : ℝ≥0∞) ≠ 0 := by positivity
  have hWtop : (weightTotal w : ℝ≥0∞) ≠ ⊤ := by simp
  have key : (∑ t ∈ Finset.range fuel, (rationalRejectMass w b) ^ t)
      * ((weightTotal w : ℝ≥0∞) * ((2^b : ℕ) : ℝ≥0∞)⁻¹)
      = 1 - (rationalRejectMass w b) ^ fuel := by
    rw [← one_sub_reject w b hb]; exact htail
  have hinv : (∑ t ∈ Finset.range fuel, (rationalRejectMass w b) ^ t)
      * ((2^b : ℕ) : ℝ≥0∞)⁻¹
      = (1 - (rationalRejectMass w b) ^ fuel) / (weightTotal w : ℝ≥0∞) := by
    refine (ENNReal.eq_div_iff hWne hWtop).mpr ?_
    rw [mul_comm (weightTotal w : ℝ≥0∞)
      ((∑ t ∈ Finset.range fuel, (rationalRejectMass w b) ^ t) * ((2^b : ℕ) : ℝ≥0∞)⁻¹),
      mul_assoc (∑ t ∈ Finset.range fuel, (rationalRejectMass w b) ^ t)
        ((2^b : ℕ) : ℝ≥0∞)⁻¹ (weightTotal w : ℝ≥0∞),
      mul_comm ((2^b : ℕ) : ℝ≥0∞)⁻¹ (weightTotal w : ℝ≥0∞)]
    exact key
  have hswap : (∑ t ∈ Finset.range fuel, (rationalRejectMass w b) ^ t
        * ((w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)))
    = (∑ t ∈ Finset.range fuel, (rationalRejectMass w b) ^ t)
        * ((w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)) := by
    rw [Finset.sum_mul]
  rw [show rationalRejectionRun w b fuel
        = runFor (rationalCountedNext w b) fuel (Sum.inr (0, 0)) from rfl,
    ← event_counted_eq_plain_inl w b fuel (0, 0) j, event_fst_point,
    tsum_eq_zero_add' ENNReal.summable,
    ← event_point (p := runFor (rationalRejectionNext w b) fuel (Sum.inr ())),
    plain_halt_mass w b hb fuel 0 j, if_neg (by simp)]
  rw [tsum_congr (g := fun t : ℕ => if t < fuel then
    (rationalRejectMass w b) ^ t * ((w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)) else 0)
    (fun t => by
      rw [← event_point (p := runFor (rationalRejectionNext w b) fuel (Sum.inr ())),
        plain_halt_mass w b hb fuel (t + 1) j]
      show ((if 1 ≤ t + 1 ∧ t + 1 ≤ fuel then (rationalRejectMass w b) ^ (t + 1 - 1) *
        ((w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)) else 0) =
        (if t < fuel then (rationalRejectMass w b) ^ t *
          ((w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞)) else 0))
      by_cases ht : t < fuel
      · rw [if_pos (c := (1 ≤ t + 1 ∧ t + 1 ≤ fuel)) (by omega),
          if_pos (c := (t < fuel)) (by omega), Nat.add_sub_cancel]
      · rw [if_neg (c := (1 ≤ t + 1 ∧ t + 1 ≤ fuel)) (by omega),
          if_neg (c := (t < fuel)) (by omega)]),
    tsum_eq_range_sum _ _ (by
      intro k hk
      have hnf : ¬ k < fuel := Nat.not_lt_of_ge hk
      simp [hnf]),
    Finset.sum_congr rfl (fun t hmem => by
      have ht : t < fuel := Finset.mem_range.mp hmem
      rw [if_pos ht]),
    hswap]
  rw [div_eq_mul_inv, mul_comm (∑ t ∈ Finset.range fuel, (rationalRejectMass w b) ^ t)
        ((w j : ℝ≥0∞) * ((2^b : ℕ) : ℝ≥0∞)⁻¹)]
  simp only [mul_assoc, mul_comm ((2^b : ℕ) : ℝ≥0∞)⁻¹
    (∑ t ∈ Finset.range fuel, (rationalRejectMass w b) ^ t)]
  rw [hinv, div_eq_mul_inv]
  simp only [mul_comm (1 - rationalRejectMass w b ^ fuel) ((weightTotal w : ℝ≥0∞)⁻¹),
    ← mul_assoc, ← div_eq_mul_inv, zero_add]

private theorem counted_first_stop (w : Fin N → ℕ) (b : ℕ) (hb : weightTotal w ≤ 2 ^ b)
    (fuel : ℕ) (t : ℕ) (j : Fin N) (ht : t < fuel) :
    CostedLaw.event (rationalRejectionRun w b fuel)
        (fun z => rejectionOutcome z.1 = Sum.inl j ∧ z.2 = t + 1)
      = (rationalRejectMass w b) ^ t * (w j : ℝ≥0∞) / ((2^b : ℕ) : ℝ≥0∞) := by
  have hpt : CostedLaw.event (runFor (rationalRejectionNext w b) fuel (Sum.inr ()))
        (fun z => z.1 = Sum.inl j ∧ z.2 = t + 1) =
      CostedLaw.event (runFor (rationalRejectionNext w b) fuel (Sum.inr ()))
        (fun z => z = (Sum.inl j, t + 1)) :=
    CostedLaw.event_congr fun z => by
      constructor
      · rintro ⟨h1, h2⟩
        exact Prod.ext h1 h2
      · intro h
        rw [h]
        exact ⟨rfl, rfl⟩
  rw [show rationalRejectionRun w b fuel
        = runFor (rationalCountedNext w b) fuel (Sum.inr (0, 0)) from rfl,
    ← event_counted_eq_plain_inl_cost w b fuel (0, 0) j t, hpt,
    plain_halt_mass w b hb fuel (t + 1) j, if_pos (by omega), Nat.add_sub_cancel,
    mul_div_assoc]

theorem rational_pending_mass (w : Fin N → ℕ) (b fuel : ℕ)
    (hb : weightTotal w ≤ 2^b) :
    CostedLaw.event (rationalRejectionRun w b fuel)
      (fun z => rejectionOutcome z.1 = Sum.inr ()) = (rationalRejectMass w b)^fuel :=
  counted_pending_mass w b hb fuel

theorem rationalFirstStop_eq (w : Fin N → ℕ) (b t : ℕ) (j : Fin N)
    (hb : weightTotal w ≤ 2^b) :
    rationalFirstStop w b t j = (rationalRejectMass w b)^t *
      (w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞) :=
  counted_first_stop w b hb (t+1) t j (by omega)

theorem rational_finite_return_pending_and_first_stop (N : ℕ) (w : Fin N → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    CostedLaw.event (rationalRejectionRun w b fuel)
        (fun z => rejectionOutcome z.1 = Sum.inr ()) =
      (rationalRejectMass w b) ^ fuel ∧
    (∀ j : Fin N, CostedLaw.event (rationalRejectionRun w b fuel)
        (fun z => rejectionOutcome z.1 = Sum.inl j) =
      (w j : ℝ≥0∞)/(weightTotal w : ℝ≥0∞) * (1 - (rationalRejectMass w b) ^ fuel)) ∧
    (∀ (t : ℕ) (j : Fin N), rationalFirstStop w b t j =
        (rationalRejectMass w b) ^ t * (w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞) ∧
      (t < fuel → CostedLaw.event (rationalRejectionRun w b fuel)
        (fun z => rejectionOutcome z.1 = Sum.inl j ∧ z.2 = t + 1) =
          rationalFirstStop w b t j)) := by
  refine ⟨counted_pending_mass w b hb fuel, counted_return_mass w b hW hb fuel, ?_⟩
  intro t j
  refine ⟨counted_first_stop w b hb (t + 1) t j (by omega), fun ht => ?_⟩
  rw [counted_first_stop w b hb fuel t j ht]
  exact (counted_first_stop w b hb (t + 1) t j (by omega)).symm

end Finite

section FiniteExp

private def compsOf {N : ℕ} :
    RandomizedExecution.Configuration Unit (Fin N) → ℕ → ℝ≥0∞
  | Sum.inl j, k => ((N * (k - 1) + j.val + 1 : ℕ) : ℝ≥0∞)
  | Sum.inr (), k => ((N * k : ℕ) : ℝ≥0∞)

theorem rational_finite_three_resource_expectations (N : ℕ) (w : Fin N → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    let tails := ∑ t ∈ Finset.range fuel, (rationalRejectMass w b) ^ t
    CostedLaw.expectedCost (rationalRejectionRun w b fuel) = tails ∧
    CostedLaw.expectation (rationalRejectionRun w b fuel)
        (fun z => (rejectionBits z.1 : ℝ≥0∞)) = (b : ℝ≥0∞) * tails ∧
    CostedLaw.expectation (rationalRejectionRun w b fuel)
        (fun z => (rejectionComparisons z.1 : ℝ≥0∞)) = rationalMeanComparisons w b * tails ∧
    (∀ z ∈ (rationalRejectionRun w b fuel).support,
      rejectionBits z.1 ≤ b * fuel ∧ rejectionComparisons z.1 ≤ N * fuel) := by
  have hq1 := reject_le_one w b
  have hqtop : rationalRejectMass w b ≠ ⊤ :=
    ne_top_of_lt (lt_of_le_of_lt hq1 (by simp : (1 : ℝ≥0∞) < ⊤))
  have hWne : (weightTotal w : ℝ≥0∞) ≠ 0 := by positivity
  have hWtop : (weightTotal w : ℝ≥0∞) ≠ ⊤ := by simp
  have hm := rational_mean_comparisons_kernel w b hb
  have hk := rational_rejection_kernel_normalized w b hb
  have hpaths : ∀ z ∈ (rationalRejectionRun w b fuel).support,
      z.2 ≤ fuel ∧ rejectionBits z.1 = b * z.2 ∧
      rejectionComparisons z.1 ≤ N * z.2 ∧
      (rejectionOutcome z.1 = Sum.inr () → rejectionComparisons z.1 = N * z.2) ∧
      (∀ j : Fin N, rejectionOutcome z.1 = Sum.inl j →
        1 ≤ z.2 ∧ rejectionComparisons z.1 = N * (z.2 - 1) + j.val + 1) := fun z hz => by
    obtain ⟨hle, hbits, hcmp, hpend, hhalt, _⟩ :=
      counted_support_invariant w b fuel (0, 0) z hz
    refine ⟨hle, by simp [hbits], hcmp.trans (by omega), fun hp => by rw [hpend hp]; omega,
      fun j hj => ?_⟩
    obtain ⟨h1, hc2⟩ := hhalt j hj
    exact ⟨h1, by rw [hc2]; omega⟩
  have hfs : ∀ (f : ℕ) (BD : ℕ × ℕ),
      finiteSurvival (rationalCountedNext w b) f (Sum.inr BD) =
        (rationalRejectMass w b) ^ f := by
    intro f BD
    show CostedLaw.event (runFor (rationalCountedNext w b) f (Sum.inr BD))
      (fun x => ∃ s, x.1 = Sum.inr s) = _
    rw [CostedLaw.event_congr (E' := fun x => rejectionOutcome x.1 = Sum.inr ())
        (fun x => by
          obtain ⟨c | s, k⟩ := x
          · have h : rejectionOutcome (Sum.inl c) = Sum.inr () ↔ False := by
              simp [rejectionOutcome]
            simp only
            rw [h]
            simp
          · have h : rejectionOutcome (N := N) (Sum.inr s) = Sum.inr () ↔ True := by
              simp [rejectionOutcome]
            simp only
            rw [h]
            simp),
      ← event_counted_eq_plain_pending w b f BD,
      plain_pending_mass w b hb f]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show rationalRejectionRun w b fuel
        = runFor (rationalCountedNext w b) fuel (Sum.inr (0, 0)) from rfl,
      finite_stopping_cost_tail_sum]
    exact Finset.sum_congr rfl fun k _ => hfs k (0, 0)
  · rw [expectation_congr_support (rationalRejectionRun w b fuel)
      (fun z => (rejectionBits z.1 : ℝ≥0∞)) (fun z => ((b * z.2 : ℕ) : ℝ≥0∞))
      (fun z hz => by
        change (rejectionBits z.1 : ℝ≥0∞) = ((b * z.2 : ℕ) : ℝ≥0∞)
        exact congrArg (fun n : ℕ => (n : ℝ≥0∞)) (hpaths z hz).2.1)]
    simp_rw [Nat.cast_mul]
    rw [CostedLaw.expectation_const_mul]
    show (b : ℝ≥0∞) * CostedLaw.expectedCost (rationalRejectionRun w b fuel) = _
    rw [show rationalRejectionRun w b fuel
        = runFor (rationalCountedNext w b) fuel (Sum.inr (0, 0)) from rfl,
      finite_stopping_cost_tail_sum]
    apply congrArg (fun x : ℝ≥0∞ => (b : ℝ≥0∞) * x)
    exact Finset.sum_congr rfl fun k _ => hfs k (0, 0)
  · have hF : ∀ z ∈ (runFor (rationalCountedNext w b) fuel (Sum.inr (0, 0))).support,
        (rejectionComparisons z.1 : ℝ≥0∞) = compsOf (N := N) (rejectionOutcome z.1) z.2 := by
      intro z hz
      obtain ⟨hle, hbits, hcmp, hpend, hhalt, _⟩ :=
        counted_support_invariant w b fuel (0, 0) z hz
      by_cases hp : rejectionOutcome z.1 = Sum.inr ()
      · have hnat : rejectionComparisons z.1 = N * z.2 := by simpa using hpend hp
        simpa [compsOf, hp] using congrArg (fun n : ℕ => (n : ℝ≥0∞)) hnat
      · cases hco : rejectionOutcome z.1 with
        | inl j =>
          obtain ⟨_, hc⟩ := hhalt j hco
          simpa [compsOf, hco] using congrArg (fun n : ℕ => (n : ℝ≥0∞)) hc
        | inr u =>
          have hp' : rejectionOutcome z.1 = Sum.inr () := by simpa using hco
          exact absurd hp' hp
    have hcompstrans : CostedLaw.expectation (runFor (rationalCountedNext w b) fuel
          (Sum.inr (0, 0))) (fun z => compsOf (N := N) (rejectionOutcome z.1) z.2)
        = CostedLaw.expectation (runFor (rationalRejectionNext w b) fuel (Sum.inr ()))
          (fun z => compsOf (N := N) z.1 z.2) := by
      have h := CostedLaw.expectation_map
        (p := runFor (rationalCountedNext w b) fuel (Sum.inr (0, 0)))
        (g := fun z => (rejectionOutcome z.1, z.2)) (f := fun w => compsOf (N := N) w.1 w.2)
      rw [runFor_map_outcome w b fuel (Sum.inr (0, 0)), rejectionOutcome] at h
      simp only [] at h
      exact h.symm
    rw [show rationalRejectionRun w b fuel
        = runFor (rationalCountedNext w b) fuel (Sum.inr (0, 0)) from rfl,
      expectation_congr_support (runFor (rationalCountedNext w b) fuel (Sum.inr (0, 0)))
        (fun z => (rejectionComparisons z.1 : ℝ≥0∞))
        (fun z => compsOf (N := N) (rejectionOutcome z.1) z.2)
        (fun z hz => by
          (try simp only)
          by_cases hp : rejectionOutcome z.1 = Sum.inr ()
          · have hnat : rejectionComparisons z.1 = N * z.2 := (hpaths z hz).2.2.2.1 hp
            simpa [compsOf, hp] using congrArg (fun n : ℕ => (n : ℝ≥0∞)) hnat
          · cases hco : rejectionOutcome z.1 with
            | inl j =>
              obtain ⟨_, hc⟩ := (hpaths z hz).2.2.2.2 j hco
              simpa [compsOf, hco] using congrArg (fun n : ℕ => (n : ℝ≥0∞)) hc
            | inr u =>
              have hp' : rejectionOutcome z.1 = Sum.inr () := by simpa using hco
              exact absurd hp' hp),
      hcompstrans,
      CostedLaw.expectation,
      tsum_prod_type' (F := fun z : (RandomizedExecution.Configuration Unit (Fin N)) × ℕ =>
          (runFor (rationalRejectionNext w b) fuel (Sum.inr ())) z *
            compsOf (N := N) z.1 z.2),
      tsum_sum_type' (F := fun c : RandomizedExecution.Configuration Unit (Fin N) =>
          ∑' k : ℕ, (runFor (rationalRejectionNext w b) fuel (Sum.inr ())) (c, k) *
            compsOf (N := N) c k),
      tsum_fintype (f := fun j : Fin N => ∑' k : ℕ,
        (runFor (rationalRejectionNext w b) fuel (Sum.inr ())) (Sum.inl j, k) *
          compsOf (N := N) (Sum.inl j) k)]
    simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton]
    have hper : ∀ j : Fin N, ∑' k : ℕ,
        (runFor (rationalRejectionNext w b) fuel (Sum.inr ())) (Sum.inl j, k) *
          compsOf (N := N) (Sum.inl j) k
      = ∑ k ∈ Finset.range fuel, ((w j : ℝ≥0∞)/((2^b : ℕ) : ℝ≥0∞) * ((rationalRejectMass w b) ^ k *
          ((N * k + j.val + 1 : ℕ) : ℝ≥0∞))) := by
      intro j
      let p := runFor (rationalRejectionNext w b) fuel (Sum.inr ())
      have hzero : p (Sum.inl j, 0) = 0 := by
        rw [← event_point p (Sum.inl j, 0), plain_halt_mass w b hb fuel 0 j]
        simp
      have hpoint (t : ℕ) : p (Sum.inl j, t + 1) =
          if t < fuel then (rationalRejectMass w b) ^ t *
            ((w j : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞)) else 0 := by
        rw [← event_point p (Sum.inl j, t + 1), plain_halt_mass w b hb fuel (t + 1) j]
        by_cases ht : t < fuel <;> simp [ht]
      rw [tsum_eq_zero_add' ENNReal.summable, hzero]
      simp only [zero_mul, zero_add]
      rw [tsum_eq_range_sum _ _ (by
        intro t ht
        have hnot : ¬ t < fuel := Nat.not_lt_of_ge ht
        rw [hpoint t, if_neg hnot]
        simp)]
      apply Finset.sum_congr rfl
      intro t hmem
      have ht : t < fuel := Finset.mem_range.mp hmem
      rw [hpoint t, if_pos ht]
      change ((rationalRejectMass w b) ^ t *
          ((w j : ℝ≥0∞) / ((2 ^ b : ℕ) : ℝ≥0∞))) *
          (((N * ((t + 1) - 1) + j.val + 1 : ℕ) : ℝ≥0∞)) = _
      rw [Nat.add_sub_cancel]
      ac_rfl
    have hpendpt : ∑' k : ℕ,
        (runFor (rationalRejectionNext w b) fuel (Sum.inr ())) (Sum.inr (), k) *
          compsOf (N := N) (Sum.inr ()) k
      = (rationalRejectMass w b) ^ fuel * ((N * fuel : ℕ) : ℝ≥0∞) := by
      let p := runFor (rationalRejectionNext w b) fuel (Sum.inr ())
      calc ∑' k : ℕ, p (Sum.inr (), k) * compsOf (N := N) (Sum.inr ()) k
          = ∑' k : ℕ, (if k = fuel then (rationalRejectMass w b) ^ fuel else 0) *
              compsOf (N := N) (Sum.inr ()) k := by
                apply tsum_congr
                intro k
                rw [plain_pending_point w b fuel k hb]
        _ = (rationalRejectMass w b) ^ fuel * ((N * fuel : ℕ) : ℝ≥0∞) := by
          rw [tsum_eq_single fuel (by intro k hk; simp [hk])]
          simp [compsOf]
    let q := rationalRejectMass w b
    let tails := ∑ t ∈ Finset.range fuel, q ^ t
    let weighted := ∑ t ∈ Finset.range fuel, (t : ℝ≥0∞) * q ^ t
    let accepted := ∑ j : Fin N, rationalRejectionNext w b () (Sum.inl j)
    let prefixAvg := ∑ j : Fin N,
      rationalRejectionNext w b () (Sum.inl j) * (((j.val + 1 : ℕ) : ℝ≥0∞))
    have haccepted : accepted = 1 - q := by
      have hk' := rational_rejection_kernel_normalized w b hb
      rw [next_inr_mass w b hb] at hk'
      exact ENNReal.eq_sub_of_add_eq hqtop (by simpa [accepted, q] using hk')
    have hterm (j : Fin N) (t : ℕ) :
        rationalRejectionNext w b () (Sum.inl j) *
            (q ^ t * ((N * t + j.val + 1 : ℕ) : ℝ≥0∞)) =
          (rationalRejectionNext w b () (Sum.inl j) * (N : ℝ≥0∞)) *
              ((t : ℝ≥0∞) * q ^ t) +
            (rationalRejectionNext w b () (Sum.inl j) *
              ((j.val + 1 : ℕ) : ℝ≥0∞)) * q ^ t := by
      simp only [q, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      ring
    have hacceptedSum :
        (∑ t ∈ Finset.range fuel, ∑ j : Fin N,
          rationalRejectionNext w b () (Sum.inl j) *
            (q ^ t * ((N * t + j.val + 1 : ℕ) : ℝ≥0∞))) =
          (N : ℝ≥0∞) * (1 - q) * weighted + prefixAvg * tails := by
      rw [Finset.sum_comm]
      calc ∑ j : Fin N, ∑ t ∈ Finset.range fuel,
            rationalRejectionNext w b () (Sum.inl j) *
              (q ^ t * ((N * t + j.val + 1 : ℕ) : ℝ≥0∞))
          = ∑ j : Fin N, ((rationalRejectionNext w b () (Sum.inl j) *
                (N : ℝ≥0∞)) * weighted +
              (rationalRejectionNext w b () (Sum.inl j) *
                ((j.val + 1 : ℕ) : ℝ≥0∞)) * tails) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.sum_congr rfl (fun t _ => hterm j t), Finset.sum_add_distrib,
                ← Finset.mul_sum, ← Finset.mul_sum]
        _ = (N : ℝ≥0∞) * (1 - q) * weighted + prefixAvg * tails := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
                ← Finset.sum_mul]
              simp only [prefixAvg]
              change (accepted * (N : ℝ≥0∞)) * weighted + prefixAvg * tails = _
              rw [haccepted]
              ring
    change (∑ j : Fin N, ∑' k : ℕ,
          (runFor (rationalRejectionNext w b) fuel (Sum.inr ())) (Sum.inl j, k) *
            compsOf (N := N) (Sum.inl j) k) +
        (∑' k : ℕ, (runFor (rationalRejectionNext w b) fuel (Sum.inr ()))
          (Sum.inr (), k) * compsOf (N := N) (Sum.inr ()) k) =
        rationalMeanComparisons w b * ∑ t ∈ Finset.range fuel,
          (rationalRejectMass w b) ^ t
    rw [Finset.sum_congr rfl (fun j _ => hper j), hpendpt, Finset.sum_comm]
    simp_rw [← next_inl_mass w b hb]
    calc (∑ t ∈ Finset.range fuel, ∑ j : Fin N,
          rationalRejectionNext w b () (Sum.inl j) *
            (q ^ t * ((N * t + j.val + 1 : ℕ) : ℝ≥0∞))) +
          q ^ fuel * ((N * fuel : ℕ) : ℝ≥0∞)
        = (N : ℝ≥0∞) * (1 - q) * weighted + prefixAvg * tails +
            q ^ fuel * ((N * fuel : ℕ) : ℝ≥0∞) := by
              rw [hacceptedSum]
      _ = prefixAvg * tails + (N : ℝ≥0∞) *
            ((1 - q) * weighted + (fuel : ℝ≥0∞) * q ^ fuel) := by
              simp only [Nat.cast_mul]
              ring
      _ = prefixAvg * tails + (N : ℝ≥0∞) * (q * tails) := by
              rw [tails_arith q hq1 fuel]
      _ = (prefixAvg + q * (N : ℝ≥0∞)) * tails := by ring
      _ = rationalMeanComparisons w b * tails := by
              simp only [prefixAvg, q]
              rw [← next_inr_mass w b hb, hm]
      _ = rationalMeanComparisons w b * ∑ t ∈ Finset.range fuel,
            (rationalRejectMass w b) ^ t := by rfl

  · intro z hz
    obtain ⟨hle, hbits, hcmp, hpend, hhalt⟩ := hpaths z hz
    refine ⟨?_, ?_⟩
    · rw [hbits]; exact Nat.mul_le_mul_left _ hle
    · exact hcmp.trans (Nat.mul_le_mul_left _ hle)

end FiniteExp

end Qatlib.Concepts.FairRandomBits.RationalReject
