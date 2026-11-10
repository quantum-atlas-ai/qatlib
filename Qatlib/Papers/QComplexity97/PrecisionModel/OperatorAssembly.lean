/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.NativeQuantumMachineDefs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Finset
open scoped BigOperators

namespace Qatlib.Papers.QComplexity97.PrecisionModel

open Qatlib.Concepts.QueryComplexity.DegreeMethod

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in

theorem coord_sq_le (d : ι → κ → ℂ) (ψ : ι → ℂ) (k : κ) (ε R : ℝ)
    (hcard : ((univ.filter (fun i => d i k ≠ 0)).card : ℝ) ≤ R)
    (hamp : ∀ i, ‖d i k‖ ≤ ε) :
    ‖∑ i, d i k * ψ i‖ ^ 2
      ≤ (R * ε ^ 2) * ∑ i ∈ univ.filter (fun i => d i k ≠ 0), ‖ψ i‖ ^ 2 := by
  have hR : 0 ≤ R := le_trans (by positivity) hcard
  set s : Finset ι := univ.filter (fun i => d i k ≠ 0) with hs
  have hstep1 : ‖∑ i, d i k * ψ i‖ ≤ ∑ i, ‖d i k‖ * ‖ψ i‖ := by
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    refine sum_congr rfl (fun i _ => ?_)
    rw [norm_mul]
  have hstep2 : (∑ i, ‖d i k‖ * ‖ψ i‖) = ∑ i ∈ s, ‖d i k‖ * ‖ψ i‖ := by
    trans ∑ i, (if d i k ≠ 0 then ‖d i k‖ * ‖ψ i‖ else 0)
    · refine sum_congr rfl (fun i _ => ?_)
      by_cases h : d i k = 0
      · simp [h]
      · simp [h]
    · rw [sum_filter]
  have hcs : (∑ i ∈ s, ‖d i k‖ * ‖ψ i‖) ^ 2
      ≤ (∑ i ∈ s, ‖d i k‖ ^ 2) * (∑ i ∈ s, ‖ψ i‖ ^ 2) :=
    sum_mul_sq_le_sq_mul_sq s (fun i => ‖d i k‖) (fun i => ‖ψ i‖)
  have hd2 : ∑ i ∈ s, ‖d i k‖ ^ 2 ≤ R * ε ^ 2 := by
    calc ∑ i ∈ s, ‖d i k‖ ^ 2 ≤ ∑ i ∈ s, ε ^ 2 := by
          refine sum_le_sum (fun i _ => ?_)
          exact pow_le_pow_left₀ (norm_nonneg _) (hamp i) 2
      _ = (s.card : ℝ) * ε ^ 2 := by
          simp [sum_const, nsmul_eq_mul]
      _ ≤ R * ε ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg ε)
  calc ‖∑ i, d i k * ψ i‖ ^ 2
      ≤ (∑ i, ‖d i k‖ * ‖ψ i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hstep1 2
    _ = (∑ i ∈ s, ‖d i k‖ * ‖ψ i‖) ^ 2 := by rw [hstep2]
    _ ≤ (∑ i ∈ s, ‖d i k‖ ^ 2) * (∑ i ∈ s, ‖ψ i‖ ^ 2) := hcs
    _ ≤ (R * ε ^ 2) * (∑ i ∈ s, ‖ψ i‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hd2 (sum_nonneg (fun i _ => sq_nonneg _))

omit [DecidableEq ι] [DecidableEq κ] in

theorem operator_sq_bound (d : ι → κ → ℂ) (ψ : ι → ℂ) (R ε : ℝ)
    (hR : 0 ≤ R)
    (hcard : ∀ k, ((univ.filter (fun i => d i k ≠ 0)).card : ℝ) ≤ R)
    (hamp : ∀ i k, ‖d i k‖ ≤ ε)
    (hsucc : ∀ i, ((univ.filter (fun k => d i k ≠ 0)).card : ℝ) ≤ R) :
    ∑ k, ‖∑ i, d i k * ψ i‖ ^ 2
      ≤ (R * ε) ^ 2 * ∑ i, ‖ψ i‖ ^ 2 := by
  have hA : ∑ k, ‖∑ i, d i k * ψ i‖ ^ 2
      ≤ (R * ε ^ 2) * ∑ k, ∑ i ∈ univ.filter (fun i => d i k ≠ 0), ‖ψ i‖ ^ 2 := by
    have h1 : ∑ k, ‖∑ i, d i k * ψ i‖ ^ 2
        ≤ ∑ k, (R * ε ^ 2) * ∑ i ∈ univ.filter (fun i => d i k ≠ 0), ‖ψ i‖ ^ 2 :=
      sum_le_sum (fun k _ => coord_sq_le d ψ k ε R (hcard k) (fun i => hamp i k))
    refine le_trans h1 (le_of_eq ?_)
    rw [mul_sum]
  have hswap : ∑ k, ∑ i ∈ univ.filter (fun i => d i k ≠ 0), ‖ψ i‖ ^ 2
      ≤ R * ∑ i, ‖ψ i‖ ^ 2 := by
    have h1 : ∀ k, (∑ i ∈ univ.filter (fun i => d i k ≠ 0), ‖ψ i‖ ^ 2)
        = ∑ i, if d i k ≠ 0 then ‖ψ i‖ ^ 2 else 0 := by
      intro k
      rw [sum_filter]
    simp_rw [h1]
    rw [sum_comm]
    have h2 : ∀ i, (∑ k, if d i k ≠ 0 then ‖ψ i‖ ^ 2 else 0)
        ≤ R * ‖ψ i‖ ^ 2 := by
      intro i
      have h3 : (∑ k, if d i k ≠ 0 then ‖ψ i‖ ^ 2 else 0)
          = ((univ.filter (fun k => d i k ≠ 0)).card : ℝ) * ‖ψ i‖ ^ 2 := by
        rw [← sum_filter]
        simp [sum_const, nsmul_eq_mul]
      rw [h3]
      exact mul_le_mul_of_nonneg_right (hsucc i) (sq_nonneg _)
    calc ∑ i, ∑ k, (if d i k ≠ 0 then ‖ψ i‖ ^ 2 else 0)
        ≤ ∑ i, R * ‖ψ i‖ ^ 2 := sum_le_sum (fun i _ => h2 i)
      _ = R * ∑ i, ‖ψ i‖ ^ 2 := by rw [mul_sum]
  calc ∑ k, ‖∑ i, d i k * ψ i‖ ^ 2
      ≤ (R * ε ^ 2) * ∑ k, ∑ i ∈ univ.filter (fun i => d i k ≠ 0), ‖ψ i‖ ^ 2 := hA
    _ ≤ (R * ε ^ 2) * (R * ∑ i, ‖ψ i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hswap (mul_nonneg hR (sq_nonneg ε))
    _ = (R * ε) ^ 2 * ∑ i, ‖ψ i‖ ^ 2 := by ring

omit [DecidableEq ι] [DecidableEq κ] in

theorem operator_norm_bound (d : ι → κ → ℂ) (ψ : ι → ℂ) (R ε : ℝ)
    (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hcard : ∀ k, ((univ.filter (fun i => d i k ≠ 0)).card : ℝ) ≤ R)
    (hamp : ∀ i k, ‖d i k‖ ≤ ε)
    (hsucc : ∀ i, ((univ.filter (fun k => d i k ≠ 0)).card : ℝ) ≤ R) :
    Real.sqrt (∑ k, ‖∑ i, d i k * ψ i‖ ^ 2)
      ≤ R * ε * Real.sqrt (∑ i, ‖ψ i‖ ^ 2) := by
  have h := operator_sq_bound d ψ R ε hR hcard hamp hsucc
  calc Real.sqrt (∑ k, ‖∑ i, d i k * ψ i‖ ^ 2)
      ≤ Real.sqrt ((R * ε) ^ 2 * ∑ i, ‖ψ i‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt ((R * ε) ^ 2) * Real.sqrt (∑ i, ‖ψ i‖ ^ 2) :=
        Real.sqrt_mul (sq_nonneg _) _
    _ = (R * ε) * Real.sqrt (∑ i, ‖ψ i‖ ^ 2) := by
        rw [Real.sqrt_sq (mul_nonneg hR hε)]

noncomputable def ruleAction (A : ι → κ → ℂ) (ψ : ι → ℂ) : κ → ℂ := fun k => ∑ i, A i k * ψ i

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in

theorem ruleAction_sub (A A' : ι → κ → ℂ) (ψ : ι → ℂ) :
    ruleAction A' ψ - ruleAction A ψ = ruleAction (fun i k => A' i k - A i k) ψ := by
  funext k
  simp only [ruleAction, Pi.sub_apply, sub_mul, sum_sub_distrib]

theorem closeness_operator_bound (A A' : ι → κ → ℂ) (ψ : ι → ℂ) (R ε : ℝ)
    (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hclose : ∀ i k, ‖A' i k - A i k‖ ≤ ε)
    (hcard : ∀ k, ((univ.filter (fun i => A' i k - A i k ≠ 0)).card : ℝ) ≤ R)
    (hsucc : ∀ i, ((univ.filter (fun k => A' i k - A i k ≠ 0)).card : ℝ) ≤ R) :
    Real.sqrt (∑ k, ‖(ruleAction A' ψ - ruleAction A ψ) k‖ ^ 2)
      ≤ R * ε * Real.sqrt (∑ i, ‖ψ i‖ ^ 2) := by
  rw [ruleAction_sub]
  exact operator_norm_bound (fun i k => A' i k - A i k) ψ R ε hR hε hcard hclose hsucc

variable {Q A : Type*} [Fintype Q] [Fintype A] {blank : A}

def preConfig (d : Config Q A blank) (m : Move) (q : Q) (a : A) : Config Q A blank :=
  ⟨q, d.tape.write (d.head - m.offset) a, d.head - m.offset⟩

theorem preConfig_target (c : Config Q A blank) (t : Move × Q × A) :
    preConfig (target c t.1 t.2.1 t.2.2) t.1 c.state (c.tape c.head) = c := by
  have hhead : (target c t.1 t.2.1 t.2.2).head - t.1.offset = c.head := by
    simp [target]
  have htape : (target c t.1 t.2.1 t.2.2).tape.write c.head (c.tape c.head) = c.tape := by
    simp only [target, Tape.write_write, Tape.write_read]
  apply Config.ext
  · rfl
  · simpa [preConfig, hhead] using htape
  · exact hhead

theorem pred_subset_image (d : Config Q A blank) (S : Set (Config Q A blank)) :
    {c | c ∈ S ∧ ∃ t : Move × Q × A, target c t.1 t.2.1 t.2.2 = d}
      ⊆ (fun t : Move × Q × A => preConfig d t.1 t.2.1 t.2.2) '' (Set.univ : Set (Move × Q × A)) := by
  classical
  rintro c ⟨-, t, ht⟩
  exact ⟨(t.1, c.state, c.tape c.head), Set.mem_univ _, by
    rw [← ht]; exact preConfig_target c t⟩

theorem pred_ncard_le (d : Config Q A blank) (S : Set (Config Q A blank)) :
    {c | c ∈ S ∧ ∃ t : Move × Q × A, target c t.1 t.2.1 t.2.2 = d}.ncard
      ≤ Fintype.card (Move × Q × A) := by
  classical
  have hsub := pred_subset_image (Q := Q) (A := A) d S
  have hfin : ((fun t : Move × Q × A => preConfig d t.1 t.2.1 t.2.2) ''
      (Set.univ : Set (Move × Q × A))).Finite := Set.finite_univ.image _
  calc {c | c ∈ S ∧ ∃ t : Move × Q × A, target c t.1 t.2.1 t.2.2 = d}.ncard
      ≤ ((fun t : Move × Q × A => preConfig d t.1 t.2.1 t.2.2) ''
          (Set.univ : Set (Move × Q × A))).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ (Set.univ : Set (Move × Q × A)).ncard :=
        Set.ncard_image_le (f := fun t : Move × Q × A => preConfig d t.1 t.2.1 t.2.2)
          (s := Set.univ)
    _ = Fintype.card (Move × Q × A) := by simp

theorem succ_ncard_le (c : Config Q A blank) :
    (Set.range (fun t : Move × Q × A => target c t.1 t.2.1 t.2.2)).ncard
      ≤ Fintype.card (Move × Q × A) := by
  classical
  have hrange : (Set.range (fun t : Move × Q × A => target c t.1 t.2.1 t.2.2))
      = (fun t : Move × Q × A => target c t.1 t.2.1 t.2.2) '' Set.univ := by
    ext y; simp [Set.mem_range]
  rw [hrange]
  calc ((fun t : Move × Q × A => target c t.1 t.2.1 t.2.2) '' Set.univ).ncard
      ≤ (Set.univ : Set (Move × Q × A)).ncard :=
        Set.ncard_image_le (f := fun t : Move × Q × A => target c t.1 t.2.1 t.2.2)
          (s := Set.univ)
    _ = Fintype.card (Move × Q × A) := by simp

theorem paper_threshold {Al Qs : Type*} [Fintype Al] [Fintype Qs]
    {ε : ℝ} {T : ℕ} (hAl : 0 < Fintype.card Al) (hQ : 0 < Fintype.card Qs)
    (hT : 0 < T) :
    (2 * (Fintype.card Al : ℝ) * (Fintype.card Qs : ℝ)) *
        (ε / (24 * (Fintype.card Al : ℝ) * (Fintype.card Qs : ℝ) * (T : ℝ)))
      = ε / (12 * (T : ℝ)) := by
  have hAl0 : (0 : ℝ) < (Fintype.card Al : ℝ) := by exact_mod_cast hAl
  have hQ0 : (0 : ℝ) < (Fintype.card Qs : ℝ) := by exact_mod_cast hQ
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  field_simp
  ring

theorem card_move_prod {Q A : Type*} [Fintype Q] [Fintype A] :
    Fintype.card (Move × Q × A) = 3 * Fintype.card Q * Fintype.card A := by
  rw [Fintype.card_prod, Fintype.card_prod]
  have h : Fintype.card Move = 3 := by decide
  rw [h]
  ring

theorem native_threshold {Q A : Type*} [Fintype Q] [Fintype A]
    {ε : ℝ} {T : ℕ} (hQ : 0 < Fintype.card Q) (hA : 0 < Fintype.card A)
    (hT : 0 < T) :
    (Fintype.card (Move × Q × A) : ℝ) *
        (ε / (12 * (Fintype.card (Move × Q × A) : ℝ) * (T : ℝ)))
      = ε / (12 * (T : ℝ)) := by
  have hN : (0 : ℝ) < (Fintype.card (Move × Q × A) : ℝ) := by
    have hc : Fintype.card (Move × Q × A) = 3 * Fintype.card Q * Fintype.card A :=
      card_move_prod
    rw [hc]
    have hpos : (0 : ℕ) < 3 * Fintype.card Q * Fintype.card A := by positivity
    exact_mod_cast hpos
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  field_simp

end Qatlib.Papers.QComplexity97.PrecisionModel
